import category_theory.functor
import category_theory.tactics.obviously
import category_theory.isomorphism
import category_theory.products
import tactic.converter.interactive
import modal

namespace category_theory

universes u v u₁ v₁ u₂ v₂

namespace functor

@[extensionality]
lemma ext {C D} [category C] [category D] (a b : C ⥤ D)
  (h : ∀ X, a X = b X)
  (h' : ∀ {X Y} (f : X ⟶ Y), a.map f == b.map f) : a = b :=
begin
  casesm* C ⥤ D,
  have : a_obj = b_obj,
  { ext, specialize h x, dsimp at h, apply h },
  subst this, congr, ext,
  specialize h' x_2, dsimp at h',
  apply eq_of_heq h',
end

@[simp]
lemma comp_id' {C D} [category C] [category D] (a : C ⥤ D) : a ⋙ functor.id D = a :=
by { ext, refl, intros, refl, }

end functor

class Monoidal (C : Type u) [category.{u v} C] :=
(prod : (C × C) ⥤ C)
(notation x ` ⊗ `:11 y:11 := prod.obj (x,y))
(I : C)
(assoc : Π a b c, a ⊗ (b ⊗ c) ≅ (a ⊗ b) ⊗ c)
(left_id  : Π a, I ⊗ a ≅ a)
(right_id : Π a, a ⊗ I ≅ a)

notation x ` ⊗ `:11  y:11 := (Monoidal.prod _).obj (x,y)

def Monoidal.prod_map (C : Type u) [category.{u v} C] [Monoidal C] {x x' y y' : C}
  (a : x ⟶ x') (b : y ⟶ y') : x ⊗ y ⟶ x' ⊗ y' :=
(Monoidal.prod C).map (a,b)

notation x ` ⊗ `:11 y:11 := (Monoidal.prod_map _ x y)

open Monoidal

class Monoid (C : Type u) [category.{u v} C] [Monoidal.{u v} C] (M : C) :=
(unit : I _ ⟶ M)
(op : M ⊗ M ⟶ M)
(left_id  : (left_id M).hom  = (unit ⊗ 𝟙 M) ≫ op)
(right_id : (right_id M).hom = (𝟙 M ⊗ unit) ≫ op)
(assoc : (assoc M M M).hom ≫ (op ⊗ 𝟙 M) ≫ op =
         (𝟙 M ⊗ op) ≫ op)

class Comonoid (C : Type u) [category.{u v} C] [Monoidal.{u v} C] (M : C) :=
(unit : M ⟶ I _)
(op : M ⟶ M ⊗ M)
(left_id  : (left_id M).inv  = op ≫ (unit ⊗ 𝟙 M))
(right_id : (right_id M).inv = op ≫ (𝟙 M ⊗ unit))
(assoc : op ≫ (op ⊗ 𝟙 M) ≫ (assoc M M M).inv =
         op ≫ (𝟙 M ⊗ op))

def functor.tensor_prod (C : Type u₁) [category.{u₁ v₁} C] : ( (C ⥤ C) × (C ⥤ C) ) ⥤ (C ⥤ C) :=
{ obj := λ a, a.1 ⋙ a.2, map' := λ a b f, f.1 ◫ f.2 }

@[simp]
lemma functor.tensor_prod_prod (C : Type u₁) [category.{u₁ v₁} C] (x y : C ⥤ C) :
  functor.tensor_prod C (x,y) = x ⋙ y := rfl


instance functor.Monoidal_category (C : Type u₁) [category.{u₁ v₁} C] :
  Monoidal.{(max u₁ v₁) (max u₁ v₁)} (C ⥤ C) :=
{ I := functor.id C,
  prod := functor.tensor_prod C,
  left_id := functor.comp_id,
  right_id := functor.id_comp,
  assoc    := by { obviously } }

class Monad (C : Type u) [category C] (M : C ⥤ C) extends Monoid (C ⥤ C) M

class Comonad (C : Type u) [category C] (M : C ⥤ C) extends Comonoid (C ⥤ C) M

variables (C : Type u) [category C] (M : Type u ⥤ Type u) [Monad (Type u) M]

instance (M) [Monad (Type u) M] : monad M.obj :=
{ map := λ α β f x, M.map f x,
  pure := λ α x, nat_trans.app (Monoid.unit M) α x,
  bind := λ α β x f, nat_trans.app (Monoid.op M) β (M.map f x) }

instance (M) [Comonad (Type u) M] : comonad M.obj :=
{ map := λ α β, M.map,
  extract := λ α x, nat_trans.app (Comonoid.unit M) α x,
  extend := λ α β f x, M.map f (nat_trans.app (Comonoid.op M) α x) }

run_cmd mk_simp_attr `category []

@[category] lemma id_eq_unit {α : Type u} : @id α = 𝟙 α := rfl

@[category] lemma d {α β γ : Type u} (f : α ⟶ β) (g : β ⟹ γ) (x : α) :
  g (f x) = (f ≫ g) x := _

instance (M) [Monad (Type u) M] : is_lawful_monad M.obj :=
begin
  refine { bind_pure_comp_eq_map := _, .. }; intros,
  { dunfold functor.map, simp only [functor.map_id] with category, refl },
  { simp [pure,(>>=)] with category,
    type_check Monoid.unit M,
    type_check Monoid.op M,
    unfold_coes,
    have : (functor.map M f ((Monoid.unit M) α x)) = _,
    conv in (functor.map M f _) { change (Monoid.unit M ≫ functor.map M f) _ , },
    type_check Monoid.unit M,
    type_check @id (_ ⟹ _) (Monoid.op M), }
end

instance (M) [Comonad (Type u) M] : is_lawful_comonad M.obj :=
sorry

end category_theory
