
import data.equiv.basic

lemma equiv.forall_iff_forall {α β} {p : α → Prop} (f : α ≃ β) :
  (∀ x, p x) ↔ (∀ x, p $ f.symm x) :=
iff.intro
  (assume h x, h _)
  (assume h x, by { specialize h (f x), revert h, simp })
