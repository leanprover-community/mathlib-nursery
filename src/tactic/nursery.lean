
namespace expr

meta def is_mvar : expr → bool
| (mvar _ _ _) := tt
| _            := ff

end expr

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
