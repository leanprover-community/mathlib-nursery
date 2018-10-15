
import order.bounded_lattice

variables {α : Type*}

namespace with_bot

@[priority 0]
instance has_lt [has_lt α] : has_lt (with_bot α) :=
{ lt := λ o₁ o₂ : option α, ∃ b ∈ o₂, ∀ a ∈ o₁, a < b }

@[simp] theorem some_lt_some' [has_lt α] {a b : α} :
  @has_lt.lt (with_bot α) _ (some a) (some b) ↔ a < b :=
by simp [(<)]

instance decidable_lt [has_lt α] [@decidable_rel α (<)] : @decidable_rel (with_bot α) (<)
| none (some x) := is_true $ by existsi [x,rfl]; rintros _ ⟨⟩
| (some x) (some y) :=
  if h : x < y
  then is_true $ by simp *
  else is_false $ by simp *
| x none := is_false $ by rintro ⟨a,⟨⟨⟩⟩⟩

end with_bot

theorem abs_le_abs {α : Type*} [decidable_linear_ordered_comm_group α] {a b : α}
  (h₀ : a ≤ b) (h₁ : -a ≤ b) :
  abs a ≤ abs b :=
calc  abs a
    ≤ b : by { apply abs_le_of_le_of_neg_le; assumption }
... ≤ abs b : le_abs_self _
