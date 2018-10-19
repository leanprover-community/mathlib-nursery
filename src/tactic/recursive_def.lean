
import tactic.nursery
import category.traversable
import category.traversable.nursery
import category.traversable.derive
namespace tactic

open lean.parser interactive interactive.types
open tactic.interactive (generalize cases_arg_p)
local postfix `?`:9000 := optional
local postfix `*`:9000 := many

meta def many1 {α : Type} (p : lean.parser α) : lean.parser (list α) :=
(::) <$> p <*> many p

local postfix `+`:9000 := many1
open binder_info expr (hiding traverse)

-- @[derive [traversable]]
meta inductive rec_pattern' (decl : Type)
-- | name (n : decl)
| cnstr (n : name) (args : list decl) (t : name) (ct : expr) : rec_pattern'
| cnstr' (n : name) (args : list (rec_pattern')) : rec_pattern'
-- | anon (args : list (rec_pattern' decl))


inductive foo
| intro : list foo → foo

-- codef map (f : α → β) : computation α → computation β
-- | (think c) := _

#check @foo.rec

#print _nest_1_1._nest_1_1.tactic.foo._mut_.sizeof
#print foo.sizeof

@[reducible]
meta def rec_pattern := rec_pattern' expr

meta inductive def_term
| single (e : expr)
| patterns (ls : list (rec_pattern × expr))

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

meta def ident_decl : lean.parser name :=
do n ← ident,
   n <$ decl_ident n

meta def ident_decl_ : lean.parser name :=
do n ← ident_,
   n <$ decl_ident n

meta def parse_arg (bi : binder_info) : lean.parser (list name × binder_info × option pexpr) :=
(λ a b c, (a,b,c)) <$> ident_decl_+ <*> pure bi <*> optional (tk ":" *> texpr)

meta def parse_def_arg : lean.parser (list name × binder_info × option pexpr) :=
( brackets "{" "}" (parse_arg implicit) <|>
         brackets "(" ")" (parse_arg default) <|>
         brackets "⦃" "⦄" (parse_arg strict_implicit) <|>
         brackets "[" "]" ((λ a c, (a,inst_implicit,some c)) <$> ident_decl_+ <* tk ":" <*> texpr) <|>
         brackets "[" "]" ((λ c, ([`_],inst_implicit,some c)) <$> texpr) )

meta def mk_def_type (n : name) : list (name × binder_info × option pexpr) → option pexpr → tactic pexpr
| [] none :=
  do u ← mk_meta_univ,
     to_pexpr <$> mk_meta_var (sort u)
| [] (some rt) := pure rt
| ((n,bi,t)::args) rt :=
  do u ← mk_meta_univ,
     t ← @option.cases_on _ (λ _, tactic pexpr) t
       (to_pexpr <$> mk_meta_var (sort u))
       (pure : pexpr → tactic pexpr),
     e ← mk_def_type args rt,
     pure $ pi n bi t e

meta def type_check_def (n : name)
  (args : list (name × binder_info × option pexpr))
  (rt : option pexpr) (d : pexpr) : tactic recursive_def :=
do g ← mk_meta_var `(Prop),
   set_goals [g],
   t ← mk_def_type n args rt >>= to_expr,
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

open traversable list

meta def new_var (n : name) : tactic expr :=
mk_local_def n `(Prop)

meta def rename_vars : expr → list name → tactic (list expr)
| (pi n binder_info.default t e) (n' :: ns) :=
  do v ← mk_local_def n' t,
     e' ← whnf (e.instantiate_var v),
     cons v <$> rename_vars e' ns
| (pi n binder_info.default t e) [] := fail "expecting more identifiers"
| (pi n bi t e) ns :=
  do v ← mk_local' n bi t,
     e' ← whnf (e.instantiate_var v),
     cons v <$> rename_vars e' ns
| e (n :: ns) := fail "too many identifiers"
| e [] := pure []

meta def types_in_pattern : rec_pattern' name → tactic rec_pattern
| (rec_pattern'.cnstr n vs t ct) :=
  do vs' ← rename_vars ct vs,
     pure (rec_pattern'.cnstr n vs' t ct)

meta def type_check_eqns (n : name)
  (args : list (name × binder_info × option pexpr))
  (rt : option pexpr) (d : list (rec_pattern' name × pexpr)) : tactic recursive_def :=
do g ← mk_meta_var `(Prop),
   set_goals [g],
   t ← mk_def_type n args rt >>= to_expr,
   g ← mk_meta_var t,
   set_goals [g],
   vs ← intron' args.length,
   tgt ← target,
   trace tgt,
   v ← mk_meta_var $ tgt.imp tgt,
   set_goals [v], rec_f ← intro n,
   trace "don't get here",
   v' ← d.mmap $ λ p : rec_pattern' name × pexpr,
     do { p' ← types_in_pattern p.1,
          let ns := to_list p,
          let e := ns.foldr (λ n b, lam n.local_pp_name binder_info.default n.local_type b) p.2,
          let t := ns.foldr (λ n b, pi n.local_pp_name binder_info.default n.local_type b) (to_pexpr tgt),
          prod.mk
            <$> traverse new_var p.1
            <*> to_expr ``(%%e : %%t) },
   v ← target >>= mk_meta_var,
   set_goals [v],
   let us := (expr.mk_app `(Prop) $ v'.map prod.snd).collect_meta_univ,
   us.enum.mmap' $ λ ⟨i,l⟩, unify_univ (level.mvar l) (level.param $ (`v).append_after i),
   vs ← vs.mmap (λ v, instantiate_mvars v >>= remove_intl_const >>= instantiate_mvars),
   v' ← v'.mmap (λ ⟨p,v⟩,
     prod.mk p <$>
     (instantiate_mvars v >>= lambdas (vs ++ to_list (p : rec_pattern)))),
   t ← instantiate_mvars t,
   pure { name := n,
          u_names := t.collect_univ_params,
          args := vs,
          type := t,
          rec_fn := rec_f,
          term := def_term.patterns v' }

meta def local_scope {α} (p : lean.parser α) : lean.parser α :=
do e ← get_env,
   p <* lean.parser.set_env e

meta def parse_lhs (n : name)
  (args : list (name × binder_info × option pexpr))
  (rt : option pexpr) : lean.parser recursive_def :=
do tk ":=", d ← texpr,
   trace_error (type_check_def n args rt d)

variable (get_ctor : name → tactic name)

meta def parse_pattern : lean.parser (rec_pattern' name) :=
do tk "(",
   c ← ident,
   args ← many ident_decl_ <* tk ")",
   t ← get_ctor c,
   ct ← (mk_const c >>= infer_type : tactic expr),
   pure $ rec_pattern'.cnstr c args t ct

meta def parse_branch (n : name)
  (args : list (name × binder_info × option pexpr))
  (rt : option pexpr) : lean.parser $ list (rec_pattern' name × pexpr) :=
many $
local_scope $
prod.mk <$> (tk "|"  *> parse_pattern get_ctor)
        <* trace "tk"
        <*  tk ":=" <*> texpr <* trace "oh?"

meta def parse_pattern_match (n : name)
  (args : list (name × binder_info × option pexpr))
  (rt : option pexpr) : lean.parser recursive_def :=
do bs ← parse_branch get_ctor n args rt,
   trace_error (type_check_eqns n args rt bs)

meta def recursive_def.parse : lean.parser recursive_def :=
do e ← tactic.get_env,
   n ← ident,
   args ← many parse_def_arg,
   let args := list.join $ args.map $ λ ⟨xs,y,z⟩, list.map (λ x, (x,y,z)) xs,
   rt ← optional (tk ":" *> texpr),
   decl_ident n,
   (parse_lhs n args rt <|> parse_pattern_match get_ctor n args rt)
    <* (lean.parser.set_env e)

end tactic
