
import category_theory.category
import category_theory.monoid

universes u v

namespace category_theory

open Monoidal

class Cartesian (C : Type u) [category.{u v} C]
extends Monoidal C :=
(diagonal : Π x : C, x ⟶ x ⊗ x)
(augment : Π x : C, x ⟶ I)
(right_cancel' : Π x : C, diagonal x ≫ (𝟙 x ⊗ augment x) ≫ (right_id.{u v} x).hom = 𝟙 x )
(left_cancel' : Π x : C, diagonal x ≫ (augment x ⊗ 𝟙 x) ≫ (left_id.{u v} x).hom = 𝟙 x )

namespace Cartesian

variables (C : Type u) [category.{u v} C] [Cartesian.{u v} C]

def prj₁ (x y : C) : x ⊗ y ⟶ x :=
(𝟙 x ⊗ augment.{u v} y) ≫ (right_id x).hom

def prj₂ (x y : C) : x ⊗ y ⟶ y :=
(augment.{u v} x ⊗ 𝟙 y) ≫ (left_id y).hom

instance {x : C} : Comonoid.{u v} C x :=
{ unit := augment x,
  op := diagonal x,
  left_id :=
    begin
      generalize Hone : 𝟙 x = one,
      suffices : 𝟙 x ≫ (left_id.{u v} x).inv = diagonal.{u v} x ≫ (augment.{u v} x ⊗ one),
      { rw [← this], simp, },
      rw [← left_cancel'], simp [Hone],
    end,
  right_id :=
    begin
      generalize Hone : 𝟙 x = one,
      suffices : 𝟙 x ≫ (right_id.{u v} x).inv = diagonal x ≫ (one ⊗ augment x),
      { rw [← this], simp, },
      rw ← right_cancel', simp [Hone],
    end,
  assoc := sorry }

instance : Cartesian (Type u) :=
{ diagonal := λ X a, (a, a),
  augment := λ X a, punit.star,
  right_cancel' := by obviously,
  left_cancel'  := by obviously, }

end Cartesian

variables {C D E : Type u}
  [category.{u v} C]
  [category.{u v} D]


def curry [category.{u v} E] (h : (C × D) ⥤ E) (c : C) : D ⥤ E :=
{ obj := λ d, h.obj (c,d),
  map := λ X Y a, h.map (𝟙 c,a) }

def hom_map [category.{u v} C] (hom : (Cᵒᵖ × C) ⥤ C) {a b c d : C}
  (f : a ⟶ b) (g : c ⟶ d) : hom.obj (b,c) ⟶ hom.obj (a,d) :=
hom.map ((f,g) : ((b,c) : Cᵒᵖ × C) ⟶ (a,d))

class CCC (C : Type u) [category.{u v} C]
extends Cartesian C :=
(hom : (Cᵒᵖ × C) ⥤ C)
(i : functor.id C ≅ curry hom I)
(j : Π y : C, I ⟶ hom.obj (y,y))
(L : Π X Y Z : C, hom.obj (Y,Z) ⟶ hom.obj (hom.obj (X,Y), hom.obj (X,Z) ) )
(eval : Π X Y : C, hom.obj (X,Y) ⊗ X ⟶ Y)
(transpose : Π {X Y Z : C}, (Z ⊗ X ⟶ Y) → (Z ⟶ hom.obj (X,Y)))
(law1 : Π X Y : C,
  j Y ≫ L X Y Y = j _ . obviously)
(law2 : Π X Y : C,
  L X X Y ≫
    hom_map hom (j X) (𝟙 _) =
  i.hom.app (hom.obj (X,Y)) . obviously)
(law3 : Π Y Z : C,
  L I Y Z ≫
    hom_map hom (i.hom.app Y) (𝟙 _) =
  hom_map hom (𝟙 _) (i.hom.app Z) . obviously)
(law4 : Π X Y U V : C,
  L X U V ≫
    L (hom.obj (X,Y)) (hom.obj (X,U)) (hom.obj (X,V)) ≫
    hom_map hom (L X Y U) (𝟙 _) =
  L Y U V ≫
    hom_map hom (𝟙 _) (L X Y V) . obviously )
(law5 : Π (X Y Z : C) (f : X⊗Y ⟶ Z), (transpose f ⊗ 𝟙 _) ≫ eval Y Z = f)
(bij : Π X Y : C, function.bijective (λ f : X ⟶ Y, j X ≫ hom_map hom (𝟙 X) f ))

namespace CCC

def types.i : functor.id (Type u) ≅ curry (functor.hom (Type u)) (I (Type u)) :=
{ hom := { app := λ (X : Type u) (a : (functor.id (Type u)).obj X) (x : I (Type u)), a },
  inv := { app := λ (X : Type u) (a : (curry (functor.hom _) _).obj X), (a punit.star) } }

def types.j (y : Type u) : I (Type u) ⟶ (functor.hom (Type u)).obj (y, y) :=
λ x : punit, id

def types.L (X Y Z : Type u) :
    (functor.hom (Type u)).obj (Y, Z) ⟶
      (functor.hom (Type u)).obj ((functor.hom (Type u)).obj (X, Y), (functor.hom (Type u)).obj (X, Z)) :=
λ (f : Y → Z) (x : X → Y), (f ∘ x : X → Z)

open function

def to_exp (X Y : Type u) (f : X ⟶ Y) : I (Type u) ⟶ (functor.hom _).obj (X,Y) :=
types.j X ≫ hom_map (functor.hom (Type u)) (𝟙 X) f

def of_exp (X Y : Type u) (f : I (Type u) ⟶ (functor.hom _).obj (X,Y)) : X ⟶ Y :=
f punit.star

lemma types.bij (X Y : Type u) :
  bijective (to_exp X Y) :=
begin
  rw bijective_iff_has_inverse,
  existsi (of_exp X Y),
  split; intro, refl,
  ext a b, cases a, refl,
end

instance : CCC (Type u) :=
{ hom := functor.hom _,
  eval := λ (X Y : Type u) (a : (functor.hom (Type u)).obj (X, Y) ⊗ X), a.fst (a.snd),
  transpose := λ (X Y Z : Type u) (f : Z ⊗ X ⟶ Y), λ (z : Z) (x : X), f (z, x),
  i := types.i,
  j := types.j,
  L := types.L,
  bij := types.bij }

end CCC

end category_theory
