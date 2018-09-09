
import tactic.monotonicity.interactive
import tactic.monotonicity.instances

import algebra.ordered_ring

import data.list.basic

open list tactic tactic.interactive

example
  (h : 3 + 6 ≤ 4 + 5)
: 1 + 3 + 2 + 6 ≤ 4 + 2 + 1 + 5 :=
begin
  ac_mono,
end

example
  (h : 3 ≤ (4 : ℤ))
  (h' : 5 ≤ (6 : ℤ))
: (1 + 3 + 2) - 6 ≤ (4 + 2 + 1 : ℤ) - 5 :=
by ac_mono

example
  (h : 3 ≤ (4 : ℤ))
  (h' : 5 ≤ (6 : ℤ))
: (1 + 3 + 2) - 6 ≤ (4 + 2 + 1 : ℤ) - 5 :=
begin
  transitivity (1 + 3 + 2 - 5 : ℤ),
  { ac_mono },
  { ac_mono },
end

example (x y z k : ℤ)
  (h : 3 ≤ (4 : ℤ))
  (h' : z ≤ y)
: (k + 3 + x) - y ≤ (k + 4 + x) - z :=
begin
  mono, -- unfold `(-)`, apply add_le_add
  { -- ⊢ k + 3 + x ≤ k + 4 + x
    mono, -- apply add_le_add, refl
    -- ⊢ k + 3 ≤ k + 4
    mono },
  { -- ⊢ -y ≤ -z
    mono /- apply neg_le_neg -/ }
end

example (x y z : ℤ)
  (h : 3 ≤ (4 : ℤ))
  (h' : z ≤ y)
: (1 + 3 + x) - y ≤ (1 + 4 + x) - z :=
begin
  transitivity (1 + 3 + x - z),
  { mono, mono },
  { mono, mono },
end

example (x y z : ℤ)
  (h : 3 ≤ (4 : ℤ))
  (h' : z ≤ y)
: (1 + 3 + x) - y ≤ (1 + 4 + x) - z :=
begin
  ac_mono, mono*
end

@[simp]
def list.le' {α : Type*} [has_le α] : list α → list α → Prop
 | (x::xs) (y::ys) := x ≤ y ∧ list.le' xs ys
 | [] [] := true
 | _ _ := false

@[simp]
instance list_has_le {α : Type*} [has_le α] : has_le (list α) :=
⟨ list.le' ⟩

lemma list.le_refl {α : Type*} [preorder α] {xs : list α}
: xs ≤ xs :=
begin
  induction xs with x xs,
  { trivial },
  { simp [has_le.le,list.le],
    split, apply le_refl, apply xs_ih }
end

-- @[trans]
lemma list.le_trans {α : Type*} [preorder α]
  {xs zs : list α} (ys : list α)
  (h  : xs ≤ ys)
  (h' : ys ≤ zs)
: xs ≤ zs :=
begin
  revert ys zs,
  induction xs with x xs
  ; intros ys zs h h'
  ; cases ys with y ys
  ; cases zs with z zs
  ; try { cases h ; cases h' ; done },
  { apply list.le_refl },
  { simp [has_le.le,list.le],
    split,
    apply le_trans h.left h'.left,
    apply xs_ih _ h.right h'.right, }
end

@[monotonic]
lemma list_le_mono_left {α : Type*} [preorder α] {xs ys zs : list α}
  (h : xs ≤ ys)
: xs ++ zs ≤ ys ++ zs :=
begin
  revert ys,
  induction xs with x xs ; intros ys h,
  { cases ys, apply list.le_refl, cases h },
  { cases ys with y ys, cases h, simp [has_le.le,list.le] at *,
    revert h, apply and.imp_right,
    apply xs_ih }
end

@[monotonic]
lemma list_le_mono_right {α : Type*} [preorder α] {xs ys zs : list α}
  (h : xs ≤ ys)
: zs ++ xs ≤ zs ++ ys :=
begin
  revert ys zs,
  induction xs with x xs ; intros ys zs h,
  { cases ys, { simp, apply list.le_refl }, cases h  },
  { cases ys with y ys, cases h, simp [has_le.le,list.le] at *,
    suffices : list.le' ((zs ++ [x]) ++ xs) ((zs ++ [y]) ++ ys),
    { refine cast _ this, simp, },
    apply list.le_trans (zs ++ [y] ++ xs),
    { apply list_le_mono_left,
      induction zs with z zs,
      { simp [has_le.le,list.le], apply h.left },
      { simp [has_le.le,list.le], split, apply le_refl,
        apply zs_ih, } },
    { apply xs_ih h.right, } }
end

lemma bar_bar'
  (h : [] ++ [3] ++ [2] ≤ [1] ++ [5] ++ [4])
: [] ++ [3] ++ [2] ++ [2] ≤ [1] ++ [5] ++ ([4] ++ [2]) :=
begin
  ac_mono,
end

lemma bar_bar''
  (h : [3] ++ [2] ++ [2] ≤ [5] ++ [4] ++ [])
: [1] ++ ([3] ++ [2]) ++ [2] ≤ [1] ++ [5] ++ ([4] ++ []) :=
begin
  ac_mono,
end

lemma bar_bar
  (h : [3] ++ [2] ≤ [5] ++ [4])
: [1] ++ [3] ++ [2] ++ [2] ≤ [1] ++ [5] ++ ([4] ++ [2]) :=
begin
  ac_mono,
end

def P (x : ℕ) := 7 ≤ x
def Q (x : ℕ) := x ≤ 7

@[monotonic]
lemma P_mono {x y : ℕ}
  (h : x ≤ y)
: P x → P y :=
by { intro h', apply le_trans h' h }

@[monotonic]
lemma Q_mono {x y : ℕ}
  (h : y ≤ x)
: Q x → Q y :=
by apply le_trans h

example (x y z : ℕ)
  (h : x ≤ y)
: P (x + z) → P (z + y) :=
begin
  ac_mono,
  ac_mono,
end

example (x y z : ℕ)
  (h : y ≤ x)
: Q (x + z) → Q (z + y) :=
begin
  ac_mono,
  ac_mono,
end

example (x y z k m n : ℤ)
  (h₀ : z ≤ 0)
  (h₁ : y ≤ x)
: (m + x + n) * z + k ≤ z * (y + n + m) + k :=
begin
  ac_mono,
  ac_mono,
  ac_mono,
end

example (x y z k m n : ℕ)
  (h₀ : z ≥ 0)
  (h₁ : x ≤ y)
: (m + x + n) * z + k ≤ z * (y + n + m) + k :=
begin
  ac_mono,
  ac_mono,
  ac_mono,
end

example (x y z k m n : ℕ)
  (h₀ : z ≥ 0)
  (h₁ : x ≤ y)
: (m + x + n) * z + k ≤ z * (y + n + m) + k :=
begin
  ac_mono,
  -- ⊢ (m + x + n) * z ≤ z * (y + n + m)
  ac_mono,
  -- ⊢ m + x + n ≤ y + n + m
  ac_mono,
end

example (x y z k m n : ℕ)
  (h₀ : z ≥ 0)
  (h₁ : x ≤ y)
: (m + x + n) * z + k ≤ z * (y + n + m) + k :=
by {  ac_mono* := h₁ }

example (x y z k m n : ℕ)
  (h₀ : z ≥ 0)
  (h₁ : m + x + n ≤ y + n + m)
: (m + x + n) * z + k ≤ z * (y + n + m) + k :=
by { ac_mono* := h₁ }

example (x y z k m n : ℕ)
  (h₀ : z ≥ 0)
  (h₁ : n + x + m ≤ y + n + m)
: (m + x + n) * z + k ≤ z * (y + n + m) + k :=
begin
  ac_mono* : m + x + n ≤ y + n + m,
  transitivity ; [ skip , apply h₁ ],
  apply le_of_eq,
  ac_refl,
end

example (x y z k m n : ℤ)
  (h₁ : x ≤ y)
: true :=
begin
  have : (m + x + n) * z + k ≤ z * (y + n + m) + k,
  { ac_mono,
    success_if_fail { ac_mono },
    admit },
  trivial
end

example (x y z k m n : ℕ)
  (h₁ : x ≤ y)
: true :=
begin
  have : (m + x + n) * z + k ≤ z * (y + n + m) + k,
  { ac_mono*,
    change 0 ≤ z, apply nat.zero_le, },
  trivial
end

example (x y z k m n : ℕ)
  (h₁ : x ≤ y)
: true :=
begin
  have : (m + x + n) * z + k ≤ z * (y + n + m) + k,
  { ac_mono,
    change (m + x + n) * z ≤ z * (y + n + m),
    admit },
  trivial,
end

example (x y z k m n i j : ℕ)
  (h₁ : x + i = y + j)
: (m + x + n + i) * z + k = z * (j + n + m + y) + k :=
begin
  ac_mono^3,
  simp [h₁],
end

example (x y z k m n i j : ℕ)
  (h₁ : x + i = y + j)
: (m + x + n + i) * z + k = z * (j + n + m + y) + k :=
begin
  ac_mono*,
  simp [h₁],
end

example (x y : ℕ)
  (h : x ≤ y)
: true :=
begin
  (do v ← mk_mvar,
      p ← to_expr ```(%%v + x ≤ y + %%v),
      assert `h' p),
  ac_mono := h,
  trivial,
  exact 1,
end

example {x y z : ℕ} : true :=
begin
  have : y + x ≤ y + z,
  { mono,
    guard_target' x ≤ z,
    admit },
  trivial
end

example {x y z : ℕ} : true :=
begin
  suffices : x + y ≤ z + y, trivial,
  mono,
  guard_target' x ≤ z,
  admit,
end

example {x y z w : ℕ} : true :=
begin
  have : x + y ≤ z + w,
  { mono,
    guard_target' x ≤ z, admit,
    guard_target' y ≤ w, admit },
  trivial
end

example {x y z w : ℕ} : true :=
begin
  have : x * y ≤ z * w,
  { mono using [0 ≤ z,0 ≤ y],
    { guard_target 0 ≤ z, admit },
    { guard_target 0 ≤ y, admit },
    guard_target' x ≤ z, admit,
    guard_target' y ≤ w, admit },
  trivial
end

example {x y z w : Prop} : true :=
begin
  have : x ∧ y → z ∧ w,
  { mono,
    guard_target' x → z, admit,
    guard_target' y → w, admit },
  trivial
end

example {x y z w : Prop} : true :=
begin
  have : x ∨ y → z ∨ w,
  { mono,
    guard_target' x → z, admit,
    guard_target' y → w, admit },
  trivial
end

example {x y z w : ℤ} : true :=
begin
  suffices : x + y < w + z, trivial,
  have : x < w, admit,
  have : y ≤ z, admit,
  mono right,
end

example {x y z w : ℤ} : true :=
begin
  suffices : x * y < w * z, trivial,
  have : x < w, admit,
  have : y ≤ z, admit,
  mono right,
  { guard_target' 0 < y, admit },
  { guard_target' 0 ≤ w, admit },
end

open tactic

example (x y : ℕ)
  (h : x ≤ y)
: true :=
begin
  (do v ← mk_mvar,
      p ← to_expr ```(%%v + x ≤ y + %%v),
      assert `h' p),
  ac_mono := h,
  trivial,
  exact 3
end
