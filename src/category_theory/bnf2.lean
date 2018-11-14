
import category_theory.functor
       category_theory.products
       category_theory.ccc

universes u v u₁ v₁ u₂ v₂ u₃ v₃ w ww

namespace category_theory

-- class BNF2 (F : Type u → Type v) extends functor F, is_lawful_functor F :=
-- (A : Type u)
-- (B : A → Type v)
-- (surj : ∀ α : Type*, surj (Σ x : A, B x → α) (F α))
open CCC Monoidal

section defs
variables {C : Type u} [𝒞₀ : category.{u v} C] [𝒞₁ : Monoidal C]
          {D : Type u} [𝒞₂ : category.{u v} D] [𝒞₃ : CCC D]
include 𝒞₀ 𝒞₁ 𝒞₂ 𝒞₃

class BNF (F : C ⥤ D) :=
(A : D)
(B : D)
(embed : C ⥤ D)
[embed_monoidal : MonoidalF.{u v} embed]
(repr : ∀ α, F.obj α ⟶ A ⊗ (B ^^ embed.obj α))
(abs : ∀ α, A ⊗ (B ^^ embed.obj α) ⟶ F.obj α)
(repr_epi : ∀ α, repr α ≫ abs α = 𝟙 _ . obviously)

instance BNF.embed.MonoidalF (F : C ⥤ D) [BNF.{u v} F] : MonoidalF (BNF.embed F) :=
BNF.embed_monoidal F

end defs

section instances

variables {C₁ : Type u} [category.{u v} C₁]
          {C₂ : Type u} [category.{u v} C₂]
          {D : Type u} [category.{u v} D] [𝒞 : CCC.{u v} D]
include 𝒞
open BNF
instance curry.BNF [Monoidal.{u v} C₁] [Monoidal.{u v} C₂] (F : (C₁ × C₂) ⥤ D) [BNF.{u v} F] (x₁ : C₁) : BNF.{u v} (curry F x₁) :=
{ A := A.{u v} F,
  B := B.{u v} F,
  embed := curry (embed F) x₁,
  repr := λ x₂, BNF.repr F (x₁, x₂),
  abs := λ x₂, BNF.abs F (x₁, x₂),
  repr_epi := λ x₂, BNF.repr_epi F (x₁, x₂)
 }

instance swap.BNF [CCC.{u v} C₁] [CCC.{u v} C₂] : BNF (prod.swap C₁ C₂) :=
{ A := (I _,I _),
  B := (I _,I _),
  embed := prod.swap _ _,
  repr := λ α, (transpose (right_id _).hom ≫ (left_id _).inv , transpose (right_id _).hom ≫ (left_id _).inv),
  abs := λ α, ((left_id _).hom ≫ (right_id _).inv ≫ eval _ _,(left_id _).hom ≫ (right_id _).inv ≫ eval _ _),
  repr_epi := by { intros, tidy,
                   conv in ((left_id _).inv ≫ _) { rw [← category.assoc],  },
                   admit, admit } }

section comp
open Cartesian
variables [𝒞₀ : Monoidal.{u v} C₁] [𝒞₁ : CCC.{u v} C₂]
          (F₁ : C₁ ⥤ C₂) (F₂ : C₂ ⥤ D)
          [𝒜₀ : BNF.{u v} F₁] [𝒜₁ : BNF.{u v} F₂]

include 𝒞₀ 𝒞₁ 𝒜₀ 𝒜₁

instance comp.BNF : BNF.{u v} (F₁ ⋙ F₂) :=
{ A := A.{u v} F₂,
  B := B.{u v} F₂ ⊗ (embed F₂).obj (B.{u v} F₁),
  embed := embed F₁ ⋙ embed F₂,
  repr := λ a, F₂.map (repr F₁ a) ≫ BNF.repr F₂ _ ≫
               right _ _ (hom_map (𝟙 _) ((embed F₂).map (prj₂ C₂ _ _)) ≫
                       transpose ( (assoc _ _ _).hom ≫
                                   left _ _ (eval _ _) ≫
                                   (MonoidalF.preserves_prod _ _ _).inv ≫
                                   (embed F₂).map (eval _ _)) ),
  abs := λ a,
      right _ _ (transpose $
        transpose ((assoc _ _ _).inv ≫
        eval _ _ ≫
        𝟙 ((embed F₁ ⋙ embed F₂).obj _)) ≫ _ ≫
        (MonoidalF.preserves_prod _ _ _).inv ) ≫
      abs F₂ _ ≫ F₂.map (abs F₁ a),
  repr_epi := sorry
}
end comp

end instances

section defs
set_option pp.universes true
#check functor (Type.{u})
variables {C : Type.{u+1}}
  [𝒞 : category.{u+1 u} C]
  [Monoidal.{u+1 u} C]
include 𝒞

open BNF
inductive iW (F : (C × Type u) ⥤ Type u) [BNF F] (α : C)
| intro : A F → (B F → iW) → iW

variables (F : (C × Type u) ⥤ Type u) [BNF F]

inductive iW.eqv {α : C} : iW F α → iW F α → Prop
| intro (a : A F) (b₀ b₁ : B F → iW F α) :
  (∀ x, iW.eqv (b₀ x) (b₁ x)) →
  iW.eqv (iW.intro a b₀) (iW.intro a b₁)

instance (α : C) : setoid (iW F α) :=
{ r := iW.eqv F,
  iseqv :=
  begin
    refine ⟨_,_,_⟩,
    { intro, induction x,
      constructor, apply x_ih },
    { introv _ h, induction h,
      constructor, apply h_ih, },
    { intro x, induction x, introv h₀ h₁,
      cases h₀, cases h₁,
      constructor, intro, apply x_ih,
      apply h₀_a_1, apply h₁_a_1, }
  end }

def W (α : C) := quotient (category_theory.setoid F α)

def cata (α : C) (β : Type u) (f : F.obj (α, β) → (embed F).obj (α, β)) : iW F α → (embed F).obj (α, β)
| (iW.intro x g) := _

def ana (α : C) (β : Type u) (f : (embed F).obj (α, β) → F.obj (α, β)) : (embed F).obj (α, β) → W F α :=
sorry

end defs


namespace W

end W

namespace functor

def W

end functor

-- F a ⟶ A ⊗ [B,a]
-- Type u × Type u × Type u
end category_theory
