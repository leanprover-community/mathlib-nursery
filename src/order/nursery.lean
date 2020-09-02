
import order.bounded_lattice
import algebra.order_functions

-- #check abs_le

-- -- #check decidable_linear_ordered_comm_group
-- theorem abs_le_abs {α : Type*}  {a b : α}
--   (h₀ : a ≤ b) (h₁ : -a ≤ b) :
--   abs a ≤ abs b :=
-- calc  abs a
--     ≤ b : by { apply abs_le_of_le_of_neg_le; assumption }
-- ... ≤ abs b : le_abs_self _
