
namespace nat

variables {x y z : ℕ}

lemma le_add_of_le_right (h : x ≤ y) :
  x ≤ y + z :=
by transitivity;
   [apply nat.le_add_right, apply nat.add_le_add_right h]

lemma le_add_of_le_left (h : x ≤ z) :
  x ≤ y + z :=
by transitivity;
   [apply nat.le_add_left, apply nat.add_le_add_left h]

end nat
