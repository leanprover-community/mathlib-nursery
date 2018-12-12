
import order.bounded_lattice

theorem abs_le_abs {α : Type*} [decidable_linear_ordered_comm_group α] {a b : α}
  (h₀ : a ≤ b) (h₁ : -a ≤ b) :
  abs a ≤ abs b :=
calc  abs a
    ≤ b : by { apply abs_le_of_le_of_neg_le; assumption }
... ≤ abs b : le_abs_self _
