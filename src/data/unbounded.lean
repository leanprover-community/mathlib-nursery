
import data.nat.basic
import data.stream
import order.bounded_lattice
import data.pfun

universes u

open lattice

class has_limit (α : Type u)
extends order_bot α :=
(lim : stream α → α)
(lim_bounds : ∀ xs : stream α, monotone xs → ∀ x ∈ xs, x ≤ lim xs)
(least_bounds : ∀ xs : stream α, monotone xs → ∀ y, (∀ x ∈ xs, x ≤ y) → lim xs ≤ y)

open roption

variables {α : Type u}
  (s : stream (roption α))

structure ord {p : ℕ → Prop} (h : ∃ i, p i) :=
(val : ℕ)
(is_lt : ∀ i, i < val → ¬ p i)

variables {p : ℕ → Prop} (h : ∃ i, p i)

instance : has_zero (ord h) :=
{ zero := ⟨_,0,assume i h, false.elim $ nat.not_lt_zero i h⟩ }

def r (x y : ord h) : Prop := x.val > y.val

lemma wf : well_founded (r h) :=
begin
  cases h with i h,
  suffices : r (Exists.intro _ h) = measure (λ j, i - j.val),
  { rw this, apply measure_wf },
  ext, simp [measure,inv_image,r],
  rw nat.sub_lt_sub_left_iff,
  by_contradiction,
  apply x.is_lt i _ h,
  apply lt_of_not_ge a
end

instance : has_well_founded (ord h) :=
{ r := r h,
  wf := wf h }

lemma forall_lt_succ {P : ℕ → Prop} (i : ℕ)
  (h₀ : ∀ j, j < i → P j)
  (h₁ : P i) :
  ∀ j < i.succ, P j :=
assume j h₂,
by { by_cases h₃ : j = i, subst i, exact h₁,
     apply h₀, apply lt_of_le_of_ne _ h₃, apply nat.le_of_lt_succ h₂ }

def ord.inc : Π x : ord h, ¬ p x.1 → ord h
| ⟨_,x,h⟩ h' := ⟨_,x.succ,forall_lt_succ _ h h'⟩

def find [∀ i, decidable (s i).dom] (h : ∃ (i : ℕ), (s i).dom) : ord h → α :=
well_founded.fix (wf h) $ λ x find,
if h' : (s x.val).dom
then (s x.val).get h'
else
have @r (λ (i : nat), (λ (i : nat), @roption.dom.{u} α (s i)) i) h (x.inc _ h') x,
  by { cases x, simp only [has_well_founded.r,r,ord.inc,(>),nat.lt_succ_self], },
find (x.inc _ h') this

open well_founded

lemma find_mem [∀ i, decidable (s i).dom] (h : ∃ (i : ℕ), (s i).dom) (x : ord h) :
  ∃ i, find s _ x ∈ s i :=
begin
  apply well_founded.induction (wf _) x,
  clear x,
  intros x ih,
  by_cases h' : (s x.val).dom,
  { existsi x.val, rw [find,fix_eq],
    simp [*,get_mem] },
  { specialize ih (x.inc _ h') _,
    rw [find,fix_eq], simp [*,get_mem], exact ih,
    cases x, simp [r,ord.inc], apply nat.lt_succ_self }
end

attribute [instance] classical.prop_decidable

instance roption.has_limit {α} : has_limit (roption α) :=
{ bot := none,
  le := λ x y, ∀ i ∈ x, i ∈ y,
  -- lt := _,
  le_refl := assume a i h, h,
  le_trans := assume a b c h₀ h₁ i h₂, h₁ _ $ h₀ _ h₂,
  -- lt_iff_le_not_le := _,
  le_antisymm := assume a b h₀ h₁, ext $ assume i, ⟨h₀ _,h₁ _⟩,
  bot_le := assume a i h, by cases not_mem_none _ h,
  lim := λ s, ⟨∃ i, (s i).dom,λ h, find s h 0 ⟩,
  lim_bounds := by { intros, intros a b, simp [roption.mem], split, },
  least_bounds := by { intros, intros a h,  } }
