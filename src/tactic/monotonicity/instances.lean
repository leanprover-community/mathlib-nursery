
import algebra.group
import algebra.order
import tactic.monotonicity.basic

instance monoid_to_is_left_id {α : Type*} [monoid α]
: is_left_id α (*) 1 :=
⟨ monoid.one_mul ⟩

instance monoid_to_is_right_id {α : Type*} [monoid α]
: is_right_id α (*) 1 :=
⟨ monoid.mul_one ⟩

instance add_monoid_to_is_left_id {α : Type*} [add_monoid α]
: is_left_id α (+) 0 :=
⟨ add_monoid.zero_add ⟩

instance add_monoid_to_is_right_id {α : Type*} [add_monoid α]
: is_right_id α (+) 0 :=
⟨ add_monoid.add_zero ⟩

variable {α : Type*}

section monotonicity

-- @[monotonic]
-- lemma nat.add_le_add {a b c d : ℕ}
--   (h : a ≤ c)
--   (h' : b ≤ d) :
--   a + b ≤ c + d :=
-- le_trans (nat.add_le_add_right h _)
--          (nat.add_le_add_left h' _)

@[monotonic]
lemma mul_mono_nonneg {x y z : α} [ordered_semiring α]
  (h' : 0 ≤ z)
  (h : x ≤ y)
: x * z ≤ y * z :=
by apply mul_le_mul_of_nonneg_right; assumption

lemma gt_of_mul_lt_mul_neg_right {a b c : α}  [linear_ordered_ring α]
  (h : a * c < b * c) (hc : c ≤ 0) : a > b :=
have nhc : -c ≥ 0, from neg_nonneg_of_nonpos hc,
have h2 : -(b * c) < -(a * c), from neg_lt_neg h,
have h3 : b * (-c) < a * (-c), from calc
     b * (-c) = - (b * c)    : by rewrite neg_mul_eq_mul_neg
          ... < - (a * c)    : h2
          ... = a * (-c)     : by rewrite neg_mul_eq_mul_neg,
lt_of_mul_lt_mul_right h3 nhc

@[monotonic]
lemma mul_mono_nonpos {x y z : α} [linear_ordered_ring α]
  [decidable_rel ((≤) : α → α → Prop)]
  (h' : 0 ≥ z)
  (h : y ≤ x)
: x * z ≤ y * z :=
begin
  by_contradiction h'',
  revert h,
  apply not_le_of_lt,
  apply gt_of_mul_lt_mul_neg_right _ h',
  apply lt_of_not_ge h''
end

@[monotonic]
lemma nat.sub_mono_left_strict {x y z : ℕ}
  (h' : z ≤ x)
  (h : x < y)
: x - z < y - z :=
begin
  have : z ≤ y,
  { transitivity, assumption, apply le_of_lt h, },
  apply @lt_of_add_lt_add_left _ _ z,
  rw [nat.add_sub_of_le,nat.add_sub_of_le];
    solve_by_elim
end

@[monotonic]
lemma nat.sub_mono_right_strict {x y z : ℕ}
  (h' : x ≤ z)
  (h : y < x)
: z - x < z - y :=
begin
  have h'' : y ≤ z,
  { transitivity, apply le_of_lt h, assumption },
  apply @lt_of_add_lt_add_right _ _ _ x,
  rw [nat.sub_add_cancel h'],
  apply @lt_of_le_of_lt _ _ _ (z - y + y),
  rw [nat.sub_add_cancel h''],
  apply nat.add_lt_add_left h
end

@[monotonic]
lemma imp_imp_imp {a b c d : Prop}
  (h₀ : c → a) (h₁ : b → d) :
  (a → b) → (c → d) :=
assume (h₂ : a → b),
calc  c
    → a : h₀
... → b : h₂
... → d : h₁

@[monotonic]
lemma le_implies_le_of_le_of_le {a b c d : α} [preorder α]
   (h₀ : c ≤ a) (h₁ : b ≤ d) :
  a ≤ b -> c ≤ d :=
assume h₂ : a ≤ b,
calc  c
    ≤ a : h₀
... ≤ b : h₂
... ≤ d : h₁

end monotonicity

open list

instance : is_left_id (list α) has_append.append [] :=
⟨ nil_append ⟩

instance : is_right_id (list α) has_append.append [] :=
⟨ append_nil ⟩

instance : is_associative (list α) has_append.append :=
⟨ append_assoc ⟩
