
import tactic.basic
import category_theory.category

open category_theory
universes u v

lemma category_theory.comp_congr {C : Type*} [category.{u v} C] {x y : C} {f g : x ⟶ y}
  (Heq : f = g) :
  ∀ {z} (h : y ⟶ z), f ≫ h = g ≫ h :=
by intros; simp only [Heq]

namespace tactic.interactive

def add_prime : name → name
| (name.mk_string s n) := name.mk_string (s ++ "'") n
| n := n

open declaration tactic

@[user_attribute]
meta def reshuffled : user_attribute unit (option name) :=
{ name := `reshuffled,
  descr := "produce a companion lemma that simplifies rewriting modulo associativity",
  parser := optional lean.parser.ident,
  after_set := some $ λ n p b,
    do d ← get_decl n,
       let us := d.univ_params,
       let t := d.type,
       (vs,t') ← mk_local_pis t,
       let lmm := @expr.const tt n $ us.map level.param,
       pr ← mk_mapp ``category_theory.comp_congr [none,none,none,none,none,none,lmm.mk_app vs],
       (vs',t') ← infer_type pr >>= mk_local_pis,
       let pr' := pr.mk_app vs',
       t' ← infer_type pr',
       sl ← simp_lemmas.mk.add_simp ``category.assoc,
       (t'',eq_pr) ← simplify sl [] t',
       pr'' ← mk_eq_mp eq_pr pr',
       n' ← reshuffled.get_param n,
       let n' := n'.get_or_else (add_prime n) ,
       add_decl (thm n' us (t''.pis (vs ++ vs')) (pure $ pr''.lambdas (vs ++ vs'))),
       copy_attribute `simp n tt n',
       pure ()
}

end tactic.interactive
