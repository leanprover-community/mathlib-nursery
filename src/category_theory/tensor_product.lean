
import category_theory.category
import category_theory.products
import category_theory.types
import category_theory.tactic
import category_theory.opposites
import category_theory.functor_class

universes u v

namespace category_theory
open function (uncurry)

variables (C : Type u)

class has_prod  :=
(prod' : C → C → C)

infix ` ⊗ `:30 := has_prod.prod'

variables  [𝒞 : category.{u v} C]
include 𝒞

class has_product extends has_prod C :=
-- [prod_functor : is_functor.{v v} (uncurry prod')]
(elim_left : Π {x} (y), x ⊗ y ⟶ x)
(elim_right : Π (x) {y}, x ⊗ y ⟶ y)
(intro : Π {x y a : C}, (a ⟶ x) → (a ⟶ y) → (a ⟶ x ⊗ y))
(intro_elim_left : Π {x y a : C} (f : a ⟶ x) (g : a ⟶ y), intro f g ≫ elim_left _ = f)
(intro_elim_right : Π {x y a : C} (f : a ⟶ x) (g : a ⟶ y), intro f g ≫ elim_right _ = g)
(intro_elim_elim : Π {a x y : C} (f : a ⟶ x ⊗ y), intro (f ≫ elim_left y) (f ≫ elim_right x) = f)

open has_product
attribute [simp, reshuffled] intro_elim_left intro_elim_right

def product.map [has_product.{u v} C] : Π {x y : C × C}, (x ⟶ y) → (uncurry (⊗) x ⟶ uncurry (⊗) y)
| (x₀,x₁) (y₀,y₁) (f,g) := intro (elim_left _ ≫ f) (elim_right _ ≫ g)

@[extensionality]
lemma product_ext [has_product.{u v} C] {x y z : C} (f g : x ⟶ y ⊗ z)
  (h_l : f ≫ elim_left _ = g ≫ elim_left _)
  (h_r : f ≫ elim_right _ = g ≫ elim_right _) :
  f = g :=
by { rw [← intro_elim_elim f,h_l,h_r,intro_elim_elim], }

@[reshuffled]
lemma comp_intro [has_product.{u v} C] {w x y z : C} (f : w ⟶ x) (g : x ⟶ y) (h : x ⟶ z) :
  f ≫ intro g h = intro (f ≫ g) (f ≫ h) :=
by { apply product_ext; simp [intro_elim_left,intro_elim_right], }

instance prod_functor [has_product.{u v} C] : is_functor.{v v} (uncurry has_prod.prod' : C × C → C) :=
{ map := λ x y, product.map _,
  map_id := by { rintros ⟨x₀,x₁⟩, dsimp [product.map], ext; simp, },
  map_comp := by { rintros ⟨x₀,x₁⟩ ⟨y₀,y₁⟩ ⟨z₀,z₁⟩ ⟨f₀,f₁⟩ ⟨g₀,g₁⟩,
                    dsimp [product.map], simp only [comp_intro],
                    repeat { rw ← category.assoc },
                    simp only [intro_elim_left,intro_elim_right],  } }

def product [has_product.{u v} C] : (C × C) ⥤ C :=
is_functor.bundled $ uncurry (⊗)

omit 𝒞
class has_coprod :=
(coprod' : C → C → C)

infix ` ⨿ `:30 := has_coprod.coprod'
include 𝒞

class has_coproduct extends has_coprod C :=
(intro_left : Π {x} (y), (x ⟶ x ⨿ y))
(intro_right : Π (x) {y}, (y ⟶ x ⨿ y))
(elim : Π {x y a : C}, (x ⟶ a) → (y ⟶ a) → (x ⨿ y ⟶ a))
(intro_left_elim : Π {x y a : C} (f : x ⟶ a) (g : y ⟶ a), intro_left y ≫ elim f g = f)
(intro_right_elim : Π {x y a : C} (f : x ⟶ a) (g : y ⟶ a), intro_right x ≫ elim f g = g)
(elim_intro_intro : Π {a x y : C} (f : x ⨿ y ⟶ a), elim (intro_left _ ≫ f) (intro_right _ ≫ f) = f)

open has_coproduct

@[extensionality]
lemma coproduct_ext [has_coproduct.{u v} C] {x y z : C} (f g : x ⨿ y ⟶ z)
  (h_l : intro_left _ ≫ f = intro_left _ ≫ g)
  (h_r : intro_right _ ≫ f = intro_right _ ≫ g) :
  f = g :=
by { rw [← elim_intro_intro f,h_l,h_r,elim_intro_intro], }

@[reshuffled]
lemma comp_elim [has_coproduct.{u v} C] {w x y z : C} (f : z ⟶ w) (g : x ⟶ z) (h : y ⟶ z) :
  elim g h ≫ f = elim (g ≫ f) (h ≫ f) :=
by { apply coproduct_ext; rw ← category.assoc; simp only [intro_left_elim,intro_right_elim], }

attribute [simp, reshuffled] intro_left_elim intro_right_elim

def coproduct.map [has_coproduct.{u v} C] : Π {x y : C × C}, (x ⟶ y) → (uncurry (⨿) x ⟶ uncurry (⨿) y)
| (x₀,x₁) (y₀,y₁) (f,g) := elim (f ≫ intro_left _) (g ≫ intro_right _)

instance coprod_functor [has_coproduct.{u v} C] : is_functor.{v v} (uncurry has_coprod.coprod' : C × C → C) :=
{ map := λ x y, coproduct.map _,
  map_id := by { rintros ⟨x₀,x₁⟩, dsimp [coproduct.map], ext; simp; erw [category.comp_id], },
  map_comp := by { rintros ⟨x₀,x₁⟩ ⟨y₀,y₁⟩ ⟨z₀,z₁⟩ ⟨f₀,f₁⟩ ⟨g₀,g₁⟩,
                    dsimp [coproduct.map], simp only [comp_elim,category.assoc],
                    simp only [intro_left_elim,intro_right_elim],  } }

def coproduct [has_coproduct.{u v} C] : (C × C) ⥤ C :=
is_functor.bundled $ uncurry (⨿)

open has_coprod has_coproduct is_functor
instance [has_coproduct.{u v} C] : has_product.{u v} (Cᵒᵖ) :=
{ prod' := (coprod' : C → C → C),
  elim_left := λ x, intro_left,
  elim_right := λ x y, intro_right x,
  intro := λ x y a f g, elim f g,
  intro_elim_left := λ x y a f g, intro_left_elim f g,
  intro_elim_right := λ x y a f g, intro_right_elim f g,
  intro_elim_elim := λ x y z, elim_intro_intro }

open has_product has_prod

instance [has_product.{u v} C] : has_coproduct.{u v} (Cᵒᵖ) :=
{ coprod' := (prod' : C → C → C),
  intro_left := λ x, elim_left,
  intro_right := λ x y, elim_right x,
  elim := λ x y a f g, intro f g,
  intro_left_elim := λ x y a f g, intro_elim_left f g,
  intro_right_elim := λ x y a f g, intro_elim_right f g,
  elim_intro_intro := λ x y z, intro_elim_elim }
omit 𝒞

instance types.has_product : has_product.{u+1 u} (Type u) :=
{ prod' := (×),
  elim_left := λ x y, _root_.prod.fst,
  elim_right := λ x y, _root_.prod.snd,
  intro := λ x y z f g i, (f i,g i),
  intro_elim_left := by { intros, ext, refl },
  intro_elim_right := by { intros, ext, refl },
  intro_elim_elim := by { intros, ext; refl, } }

instance types.has_coproduct : has_coproduct.{u+1 u} (Type u) :=
{ coprod' := (⊕),
  intro_left := λ x y, sum.inl,
  intro_right := λ x y, sum.inr,
  elim := λ x y z f g i, sum.rec_on i f g,
  intro_left_elim := by { intros, ext, refl },
  intro_right_elim := by { intros, ext, refl },
  elim_intro_intro := by { intros, ext (x | y); refl } }

end category_theory
