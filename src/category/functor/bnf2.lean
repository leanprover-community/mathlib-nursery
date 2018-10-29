import category.functor.bnf data.set.basic

/-
move to option
-/

namespace option

lemma some_get {α : Type*} {x : option α} (h : is_some x) :
  some (option.get h) = x :=
by { cases x, contradiction, reflexivity }

end option

universes u v

/-
An alternative representation of BNFs.
-/

structure surj (α : Type*) (β : Type*) :=
(map : α → β)
(inv : β → α)
(is_inv : function.right_inverse inv map)

class BNF2 (F : Type u → Type v) extends functor F, is_lawful_functor F :=
(A : Type u)
(B : A → Type v)
(surj : ∀ α : Type*, surj (Σ x : A, B x → α) (F α))

/-
To map BNF to BNF2, we need some helper functions.
-/

namespace BNF

variables {F : Type u → Type v} [BNF F]
variable {α : Type u}

def in_dom (x : F α) (b : BNF.B F) : Prop :=
∃ h : (iota x b).is_some = tt, option.get h ∈ x

def in_dom_idx_aux {x : F α} {a : α} (ax : a ∈ x)
    (h : option.is_some (iota x (idx x a)) = tt) :
  option.get h = a :=
begin
  apply option.some.inj,
  have : some a = BNF.iota x (BNF.idx x a) := (idx_iota x _ ax).symm,
  rw this,
  apply option.some_get
end

def in_dom_idx {x : F α} {a : α} (ax : a ∈ x) : in_dom x (idx x a) :=
have h : option.is_some (iota x (idx x a)) = tt,
  by rw [option.mem_def.mp (idx_iota x a ax)]; reflexivity,
have h'' : option.get h ∈ x,
  by rw in_dom_idx_aux; exact ax,
exists.intro h h''

def iota' {x : F α} (b : B F) (h : in_dom x b) : α :=
have h' : (iota x b).is_some = tt, by cases h; assumption,
option.get h'

def iota'_mem {x : F α} {b : B F} (h : in_dom x b) : iota' _ h ∈ x :=
by { cases h with h₀ h₁, exact h₁ }

def iota'_eq {x : F α} {a : α} (ax : a ∈ x) :
  iota' (idx x a) (in_dom_idx ax) = a :=
by { simp [iota'], apply in_dom_idx_aux ax }

end BNF

/-
Mapping BNF to BNF2
-/

def idx' {F : Type u → Type v} [BNF F] {α : Type*} (x : F α) :
  {a // a ∈ x} → {b : BNF.B F // BNF.in_dom x b }
| ⟨a, ax⟩ := ⟨BNF.idx x a, BNF.in_dom_idx ax⟩

def iota'' {F : Type u → Type v} [BNF F] {α : Type*} (x : F α) : {b // BNF.in_dom x b} → α :=
λ u, BNF.iota' u.val u.property

lemma iota''_idx' {F : Type u → Type v} [BNF F] {α : Type*} (x : F α) :
  iota'' x ∘ idx' x = subtype.val :=
begin
  ext a, rcases a with ⟨a, ax⟩, simp [idx', iota''],
  apply BNF.iota'_eq ax
end

-- Note: this requires F : Type u → Type u

def BNF.to_BNF2 (F : Type u → Type u) [BNF F] : BNF2 F :=
{ A := Σ P : BNF.B F → Prop, F {b : BNF.B F // P b},
  B := λ Px, {b : BNF.B F // Px.fst b},
  surj := λ α,
    { map    := λ ⟨⟨P, x⟩, f⟩, f <$> x,
      inv    := λ x : F α, ⟨⟨BNF.in_dom x, idx' x <$> BNF.attach x⟩, iota'' x⟩,
      is_inv :=
        begin
          intro x, dsimp [BNF.to_BNF2._match_1],
          rw [← comp_map, iota''_idx'],
          rw [BNF.attach_map x]
        end
    } }

/-
The other direction.
-/

/-
def range {α : Type*} {β : Type*} (f : α → β) := { y : β | ∃ x : α, f x = y }

def BNF2.to_BNF (F : Type u → Type u) [bnf2 : BNF2 F] : BNF F :=
let A := BNF2.A F,
    B' := @BNF2.B F,
    surj := BNF2.surj F,
    map := λ {α}, (surj α).map,
    inv := λ {α}, (surj α).inv,
    is_inv := λ α, (surj α).inv,
    mem := λ {α} (a : α) (x : F α), a ∈ range (inv x).2 in
{ has_mem := λ α, has_mem.mk mem,
  mem_map := λ α β f b x,
    begin
      simp [(∈)], revert mem, simp [range, set.mem_sep],
      split,
      { rintros ⟨b, hb⟩,  },
    end,
  B := Σ x : A, B' x,

}

-/
