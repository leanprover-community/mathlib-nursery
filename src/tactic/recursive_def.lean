
import tactic.nursery

namespace tactic

open lean.parser interactive interactive.types
open tactic.interactive (generalize cases_arg_p)
local postfix `?`:9000 := optional
open binder_info expr

meta inductive rec_pattern
| name (n : name)
| cnstr (n : name) (args : list rec_pattern)
| anon (args : list rec_pattern)

meta inductive def_term
| single (e : expr)
-- | patterns (ls : list (list rec_pattern × expr))

meta structure recursive_def :=
(name : name)
(u_names : list _root_.name)
(args : list expr)
(type : expr)
(rec_fn : expr)
(term : def_term)

meta def recursive_def.u_params (d : recursive_def) : list level :=
d.u_names.map level.param

meta def decl_ident (n : name) : lean.parser unit :=
do e ← get_env,
   updateex_env $ λ e, e.add (declaration.cnst n [ ] `(Prop) ff)
   -- lean.parser.set_env

meta def parse_arg (bi : binder_info) : lean.parser (name × binder_info × option pexpr) :=
(λ a b c, (a,b,c)) <$> ident_ <*> pure bi <*> optional (tk ":" *> texpr)

meta def parse_def_arg : lean.parser (name × binder_info × option pexpr) :=
do x ← ( brackets "{" "}" (parse_arg implicit) <|>
         brackets "(" ")" (parse_arg default) <|>
         brackets "⦃" "⦄" (parse_arg strict_implicit) <|>
         brackets "[" "]" ((λ a c, (a,inst_implicit,some c)) <$> ident_ <* tk ":" <*> texpr) <|>
         brackets "[" "]" ((λ c, (`_,inst_implicit,some c)) <$> texpr) ),
   decl_ident x.1,
   pure x

meta def mk_def_type (n : name) : list (name × binder_info × option pexpr) → option pexpr → pexpr → tactic pexpr
| [] none d :=
  do u ← mk_meta_univ,
     to_pexpr <$> mk_meta_var (sort u)
| [] (some rt) d := pure rt
| ((n,bi,t)::args) rt d :=
  do u ← mk_meta_univ,
     t ← @option.cases_on _ (λ _, tactic pexpr) t
       (to_pexpr <$> mk_meta_var (sort u))
       (pure : pexpr → tactic pexpr),
     e ← mk_def_type args rt d,
     pure $ pi n bi t e

meta def type_check_def (n : name)
  (args : list (name × binder_info × option pexpr))
  (rt : option pexpr) (d : pexpr) : tactic recursive_def :=
do g ← mk_meta_var `(Prop),
   set_goals [g],
   t ← mk_def_type n args rt d >>= to_expr,
   g ← mk_meta_var t,
   set_goals [g],
   vs ← intron' args.length,
   tgt ← target,
   v ← mk_meta_var $ tgt.imp tgt,
   set_goals [v], rec_f ← intro n,
   v' ← to_expr ``(%%d : %%tgt),
   v ← target >>= mk_meta_var,
   set_goals [v],
   v'.collect_meta_univ.enum.mmap' $ λ ⟨i,l⟩, unify_univ (level.mvar l) (level.param $ (`v).append_after i),
   vs ← vs.mmap (λ v, instantiate_mvars v >>= remove_intl_const >>= instantiate_mvars),
   v' ← instantiate_mvars v' >>= lambdas vs,
   t ← instantiate_mvars t,
   pure { name := n,
          u_names := t.collect_univ_params,
          args := vs,
          type := t,
          rec_fn := rec_f,
          term := def_term.single v' }

meta def recursive_def.parse : lean.parser recursive_def :=
do e ← tactic.get_env,
   n ← ident,
   args ← many parse_def_arg,
   rt ← optional (tk ":" *> texpr),
   decl_ident n,
   tk ":=", d ← texpr,
   trace_error (type_check_def n args rt d) <*
     lean.parser.set_env e

end tactic
