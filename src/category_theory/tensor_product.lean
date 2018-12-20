
import category_theory.category
import category_theory.products
import category_theory.opposites
import category_theory.functor_class

universes u v

namespace category_theory
open function (uncurry)

variables (C : Type u) [𝒞 : category.{u v} C]
include 𝒞

class has_product :=
(prod' : C → C → C)
(infix ` ⊗ `:30 := prod')
[prod_functor : is_functor.{v v} (uncurry prod')]
(elim_left : Π {x} (y), x ⊗ y ⟶ x)
(elim_right : Π (x) {y}, x ⊗ y ⟶ y)
(intro : Π {x y a : C}, (a ⟶ x) → (a ⟶ y) → (a ⟶ x ⊗ y))
(intro_elim_left : Π {x y a : C} (f : a ⟶ x) (g : a ⟶ y), intro f g ≫ elim_left _ = f)
(intro_elim_right : Π {x y a : C} (f : a ⟶ x) (g : a ⟶ y), intro f g ≫ elim_right _ = g)

infix ` ⊗ `:30 := has_product.prod'

instance prod_functor [has_product.{u v} C] : is_functor.{v v} (uncurry has_product.prod'.{u v} : C × C → C) :=
has_product.prod_functor C

def product [has_product.{u v} C] : (C × C) ⥤ C :=
is_functor.bundled.{v v} (uncurry has_product.prod'.{u v} : C × C → C)

class has_coproduct :=
(coprod' : C → C → C)
(infix ` ⨿ `:30 := coprod')
[coprod_functor : is_functor.{v v} (uncurry coprod')]
(intro_left : Π {x} (y), (x ⟶ x ⨿ y))
(intro_right : Π (x) {y}, (y ⟶ x ⨿ y))
(elim : Π {x y a : C}, (x ⟶ a) → (y ⟶ a) → (x ⨿ y ⟶ a))
(intro_left_elim : Π {x y a : C} (f : x ⟶ a) (g : y ⟶ a), intro_left y ≫ elim f g = f)
(intro_right_elim : Π {x y a : C} (f : x ⟶ a) (g : y ⟶ a), intro_right x ≫ elim f g = g)

infix ` ⨿ `:30 := has_coproduct.coprod'

instance coprod_functor [has_coproduct.{u v} C] : is_functor.{v v} (uncurry has_coproduct.coprod'.{u v} : C × C → C) :=
has_coproduct.coprod_functor C

def coproduct [has_coproduct.{u v} C] : (C × C) ⥤ C :=
is_functor.bundled.{v v} (uncurry has_coproduct.coprod'.{u v} : C × C → C)

open has_coproduct is_functor
instance [has_coproduct.{u v} C] : has_product.{u v} (Cᵒᵖ) :=
{ prod' := (coprod'.{u v} : C → C → C),
  prod_functor := functor.is_functor (functor.op (coproduct C)),
  elim_left := λ x, intro_left,
  elim_right := λ x y, intro_right x,
  intro := λ x y a f g, elim f g,
  intro_elim_left := λ x y a f g, intro_left_elim f g,
  intro_elim_right := λ x y a f g, intro_right_elim f g }

open has_product

instance [has_product.{u v} C] : has_coproduct.{u v} (Cᵒᵖ) :=
{ coprod' := (prod'.{u v} : C → C → C),
  coprod_functor := functor.is_functor (functor.op (product C)),
  intro_left := λ x, elim_left,
  intro_right := λ x y, elim_right x,
  elim := λ x y a f g, intro f g,
  intro_left_elim := λ x y a f g, intro_elim_left f g,
  intro_right_elim := λ x y a f g, intro_elim_right f g }

end category_theory
