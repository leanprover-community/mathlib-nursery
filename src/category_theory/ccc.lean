
import category_theory.category category_theory.basic
import category_theory.monoid

universes u v u' v' u'' v''

namespace category_theory

open Monoidal

class Cartesian (C : Type u) [category.{u v} C]
extends Monoidal C :=
(diagonal : Π x : C, x ⟶ x ⊗ x)
(augment : Π x : C, x ⟶ I)
(right_cancel' : Π x : C, diagonal x ≫ (𝟙 x ⊗ augment x) ≫ (right_id.{u v} x).hom = 𝟙 x )
(left_cancel' : Π x : C, diagonal x ≫ (augment x ⊗ 𝟙 x) ≫ (left_id.{u v} x).hom = 𝟙 x )

class CartesianF
  {C₀ C₁ : Type u}
  [category.{u v} C₀]
  [category.{u v} C₁]
  [Cartesian.{u v} C₀]
  [Cartesian.{u v} C₁]
  (F : C₀ ⥤ C₁)

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

variables (C₀ : Type u)  [category.{u v} C₀]  [𝒞₀ : Cartesian C₀]
          (C₁ : Type u)  [category.{u v} C₁]  [𝒞₁ : Cartesian C₁]

include 𝒞₀ 𝒞₁

instance prod.Cartesian : Cartesian (C₀ × C₁) :=
{ diagonal := λ X, (diagonal X.fst,diagonal X.snd),
  augment := λ X, (augment X.fst,augment X.snd),
  right_cancel' := by { obviously, repeat { apply right_cancel' }, },
  left_cancel'  := by { obviously, repeat { apply left_cancel' }, } }

end Cartesian

variables
  {C : Type u}
  {D : Type u}
  {E : Type u}

section curry

variables [𝒞 : category.{u v} C] [category.{u v} D] [category.{u v} E]
include 𝒞
def curry (h : (C × D) ⥤ E) (c : C) : D ⥤ E :=
{ obj := λ d, h.obj (c,d),
  map := λ X Y a, h.map (𝟙 c,a) }

variables [Monoidal.{u v} D] [Monoidal.{u v} E]

instance curry.MonoidalF (h : (C × D) ⥤ E) (c : C) : MonoidalF (curry h c) :=
sorry

end curry

def hom_map' [category.{u v} C] (hom : (Cᵒᵖ × C) ⥤ C) {a b c d : C}
  (f : a ⟶ b) (g : c ⟶ d) : hom.obj (b,c) ⟶ hom.obj (a,d) :=
hom.map ((f,g) : ((b,c) : Cᵒᵖ × C) ⟶ (a,d))

class CCC (C : Type u) [category.{u v} C]
extends Cartesian.{u v} C :=
(hom : (Cᵒᵖ × C) ⥤ C)
(notation x ` ^^ `:12 y:12 := hom.obj (x,y))
(i : functor.id C ≅ curry hom I)
(j' : Π y : C, I ⟶ (y ^^ y))
(L' : Π X Y Z : C, (Y^^Z) ⟶ ( (X^^Y) ^^ (X^^Z) ) )
(eval' : Π X Y : C, (X^^Y) ⊗ X ⟶ Y)
(transpose' : Π {X Y Z : C}, (Z ⊗ X ⟶ Y) → (Z ⟶ (X^^Y)))
(law1' : Π X Y : C,
  j' Y ≫ L' X Y Y = j' _ . obviously)
(law2' : Π X Y : C,
  L' X X Y ≫
    hom_map' hom (j' X) (𝟙 _) =
  i.hom.app ((X ^^ Y)) . obviously)
(law3' : Π Y Z : C,
  L' I Y Z ≫
    hom_map' hom (i.hom.app Y) (𝟙 _) =
  hom_map' hom (𝟙 _) (i.hom.app Z) . obviously)
(law4' : Π X Y U V : C,
  L' X U V ≫
    L' (X ^^ Y) (X ^^ U) (X ^^ V) ≫
    hom_map' hom (L' X Y U) (𝟙 _) =
  L' Y U V ≫
    hom_map' hom (𝟙 _) (L' X Y V) . obviously )
(law5' : Π (X Y Z : C) (f : X⊗Y ⟶ Z), (transpose' f ⊗ 𝟙 _) ≫ eval' Y Z = f . obviously)
(bij : Π X Y : C, function.bijective (λ f : X ⟶ Y, j' X ≫ hom_map' hom (𝟙 X) f ))

namespace CCC
def hom_obj {C : Type u} [category.{u v} C] [CCC C] (a b : C) : C :=
(CCC.hom _).obj (a,b)

infixr ` ^^ `:12 := CCC.hom_obj

def hom_map [category.{u v} C] [CCC.{u v} C] {a b c d : C}
  (f : a ⟶ b) (g : c ⟶ d) : (b ^^ c) ⟶ (a ^^ d) :=
(CCC.hom C).map ((f,g) : ((b,c) : Cᵒᵖ × C) ⟶ (a,d))

section general

variables {C} [category.{u v} C] [𝒞 : CCC.{u v} C]
include 𝒞

def j : Π y : C, I _ ⟶ (y ^^ y) := j'

def L : Π X Y Z : C, (Y^^Z) ⟶ ( (X^^Y) ^^ (X^^Z) ) := L'
def eval : Π X Y : C, (X^^Y) ⊗ X ⟶ Y := eval'
def transpose : Π {X Y Z : C}, (Z ⊗ X ⟶ Y) → (Z ⟶ (X^^Y)) := @transpose' C _ _
lemma law1 : Π X Y : C, j Y ≫ L X Y Y = j _ := law1' C
lemma law2 : Π X Y : C,
  L X X Y ≫ hom_map (j X) (𝟙 _) =
  (i C).hom.app ((X ^^ Y)) := law2' C
lemma law3 : Π Y Z : C,
  L (I _) Y Z ≫
    hom_map ((i C).hom.app Y) (𝟙 _) =
  hom_map (𝟙 _) ((i C).hom.app Z) := law3' C
lemma law4 : Π X Y U V : C,
  L' X U V ≫
    L' (X ^^ Y) (X ^^ U) (X ^^ V) ≫
    hom_map (L' X Y U) (𝟙 _) =
  L' Y U V ≫
    hom_map (𝟙 _) (L' X Y V) := law4' C
lemma law5 : Π (X Y Z : C) (f : X⊗Y ⟶ Z), (transpose f ⊗ 𝟙 _) ≫ eval Y Z = f := law5' _

def distr (a b c : C) :
  (a ^^ (b ^^ c)) ⟶ ((a ⊗ b) ^^ c) :=
transpose $ (assoc _ _ _).hom ≫ (eval a (b^^ c) ⊗ 𝟙 _) ≫ eval _ _

def distr' (a b c : C) :
  ((a ⊗ b) ^^ c) ⟶ (a ^^ (b ^^ c)) :=
transpose $ transpose $ (assoc _ _ _).inv ≫ eval _ _

end general

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
types.j X ≫ hom_map' (functor.hom (Type u)) (𝟙 X) f

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

variables (C₀ : Type u) [category.{u v} C₀] [𝒞₀ : CCC C₀]
          (C₁ : Type u) [category.{u v} C₁] [𝒞₁ : CCC C₁]
include 𝒞₀ 𝒞₁
def prod.hom : ((C₀ × C₁)ᵒᵖ × C₀ × C₁) ⥤ (C₀ × C₁) :=
{ obj := λ f, ((CCC.hom C₀).obj (f.1.1,f.2.1),(CCC.hom C₁).obj (f.1.2,f.2.2)),
  map := λ (X Y : C₀ × C₁ᵒᵖ × C₀ × C₁) (f : X ⟶ Y),
    ((hom.{u v} C₀).map (f.1.1,f.2.1), (hom.{u v} C₁).map (f.1.2,f.2.2)) }

def prod.i : functor.id.{u v} (C₀ × C₁) ≅ curry.{u v} (prod.hom.{u v} C₀ C₁) (I.{u v} (C₀ × C₁)) :=
{ hom := { app := λ (X : C₀ × C₁), ((i.{u v} C₀).hom.app X.1, ((i C₁).hom.app X.2 )) },
  inv := { app := λ (X : C₀ × C₁), ((i.{u v} C₀).inv.app X.1, ((i C₁).inv.app X.2 )) } }

def prod.j (y : C₀ × C₁) : I.{u v} (C₀ × C₁) ⟶ (prod.hom.{u v} C₀ C₁).obj (y, y) :=
(j _,j _)

def prod.L (X Y Z : C₀ × C₁) :
 (prod.hom.{u v} C₀ C₁).obj (Y, Z) ⟶
 (prod.hom.{u v} C₀ C₁).obj ((prod.hom.{u v} C₀ C₁).obj (X, Y), (prod.hom.{u v} C₀ C₁).obj (X, Z)) :=
(L _ _ _,L _ _ _)

instance prod.CCC : CCC (C₀ × C₁) :=
{ hom := prod.hom C₀ C₁,
  i := prod.i C₀ C₁,
  j := prod.j C₀ C₁,
  L := prod.L C₀ C₁,
  eval := λ X Y, (eval _ _,eval _ _),
  transpose := λ X Y Z f, (transpose f.1,transpose f.2),
  law1 := sorry,
  law2 := sorry,
  law3 := sorry,
  law4 := sorry,
  law5 := sorry,
  bij := sorry }

end CCC

end category_theory
