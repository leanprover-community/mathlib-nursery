
import data.list.basic
import tactic.basic

namespace expr

meta def is_mvar : expr → bool
| (mvar _ _ _) := tt
| _            := ff

end expr

namespace tactic

meta def trace_error {α} (tac : tactic α) : tactic α :=
λ s, match tac s with
     | r@(result.success _ _) := r
     | (result.exception (some msg) pos s') := (trace (msg ()) >> result.exception (some msg) pos) s'
     | r@(result.exception none _ _) := r
     end

meta def is_type (e : expr) : tactic bool :=
do (expr.sort _) ← infer_type e | pure ff,
   pure tt

meta def list_macros : expr → list (name × list expr) | e :=
e.fold [] (λ m i s,
  match m with
  | (expr.macro m args) := (expr.macro_def_name m, args) :: s
  | _ := s end)

meta def expand_untrusted (tac : tactic unit) : tactic unit :=
do tgt ← target,
   mv  ← mk_meta_var tgt,
   gs ← get_goals,
   set_goals [mv],
   tac,
   env ← get_env,
   pr ← env.unfold_untrusted_macros <$> instantiate_mvars mv,
   set_goals gs,
   exact pr

meta def binders : expr → tactic (list expr)
| (expr.pi n bi d b) :=
  do v ← mk_local' n bi d,
     (::) v <$> binders (b.instantiate_var v)
| _ := pure []

meta def rec_args_count (t c : name) : tactic ℕ :=
do ct ← mk_const c >>= infer_type,
   (list.length ∘ list.filter (λ v : expr, v.local_type.is_app_of t)) <$> binders ct

meta def match_induct_hyp (n : name) : list expr → list expr → tactic (list $ expr × option expr)
| [] [] := pure []
| [] _ := fail "wrong number of inductive hypotheses"
| (x :: xs) [] := (::) (x,none) <$> match_induct_hyp xs []
| (x :: xs) (h :: hs) :=
do t ← infer_type x,
   if t.is_app_of n
     then (::) (x,h) <$> match_induct_hyp xs hs
     else (::) (x,none) <$> match_induct_hyp xs (h :: hs)

meta def is_recursive_type (n : name) : tactic bool :=
do e ← get_env,
   let cs := e.constructors_of n,
   rs ← cs.mmap (rec_args_count n),
   pure $ rs.any (λ r, r > 0)

meta def better_induction (e : expr) : tactic $ list (name × list (expr × option expr) × list (name × expr)) :=
do t ← infer_type e,
   let tn := t.get_app_fn.const_name,
   focus1 $
   do vs ← induction e,
      gs ← get_goals,
      vs' ← mzip_with (λ g (pat : name × list expr × list (name × expr)),
        do let ⟨n,args,σ⟩ := pat,
           set_goals [g],
           nrec ← rec_args_count tn n,
           let ⟨args,rec⟩ := args.split_at (args.length - nrec),
           args ← match_induct_hyp tn args rec,
           pure ((n,args,σ))) gs vs,
      set_goals gs,
      pure vs'

meta def extract_def' {α} (n : name) (trusted : bool) (elab_def : tactic α) : tactic α :=
do cxt ← list.map to_implicit <$> local_context,
   t ← target,
   (r,d) ← solve_aux t elab_def,
   d ← instantiate_mvars d,
   t' ← pis cxt t,
   d' ← lambdas cxt d,
   let univ := t'.collect_univ_params,
   add_decl $ declaration.defn n univ t' d' (reducibility_hints.regular 1 tt) trusted,
   r <$ (applyc n; assumption)

open expr list

meta def unpi : expr → tactic (list expr × expr)
| (pi n bi d b) :=
  do v ← mk_local' n bi d,
     prod.map (cons v) id <$> unpi (b.instantiate_var v)
| e := pure ([],e)

meta def unify_app_aux : expr → expr → list expr → tactic expr
| e (pi _ _ d b) (a :: as) :=
do t ← infer_type a,
   unify t d,
   e' ← head_beta (e a),
   b' ← whnf (b.instantiate_var a),
   unify_app_aux e' b' as
| e t (_ :: _) := fail "too many arguments"
| e _ [] := pure e

meta def unify_app (e : expr) (args : list expr) : tactic expr :=
do t ← infer_type e >>= whnf,
   unify_app_aux e t args

end tactic

namespace tactic.interactive

open lean lean.parser interactive interactive.types tactic

meta def guard_expr_eq' (t : expr) (p : parse $ tk ":=" *> texpr) : tactic unit :=
do e ← to_expr p, is_def_eq t e

/--
`guard_target t` fails if the target of the main goal is not `t`.
We use this tactic for writing tests.
-/
meta def guard_target' (p : parse texpr) : tactic unit :=
do t ← target, guard_expr_eq' t p

end tactic.interactive
