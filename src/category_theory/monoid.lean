import category_theory.functor
import category_theory.terminal
import category_theory.tensor_product
import category_theory.functor_category
import category_theory.opposites
import category_theory.products
-- import category_theory.tactics.obviously
import category_theory.isomorphism
import category_theory.natural_isomorphism
import category_theory.products
import category_theory.types
-- import tactic.converter.interactive
import tactic
import category.comonad

universes u v u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄

namespace tactic.interactive

meta def product : tactic unit :=
`[ repeat { apply product_ext };
   repeat { rw ← category.assoc <|> rw comp_intro <|>
            apply has_terminal.unique <|>
            apply has_initial.unique };
   simp only [intro_elim_left,intro_elim_right,
              category.id_comp] ]

end tactic.interactive

namespace category_theory

namespace functor

@[extensionality]
lemma ext {C D} [category C] [category D] (a b : C ⥤ D)
  (h : ∀ X, a.obj X = b.obj X)
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
open function (uncurry) is_functor

section

section bimap

variables {C : Type u} [category.{u v} C]
variables (F : C → C → C) [is_functor.{v v} (uncurry F)]

def bimap {x x' y y' : C} (a : x ⟶ y) (b : x' ⟶ y') : F x x' ⟶ F y y' :=
map.{v v} (uncurry F) ((a,b) : (x,x') ⟶ (y,y'))

open has_product has_coproduct

@[simp,reshuffled]
lemma bimap_elim_left [has_product.{u v} C]
  {x x' y y' : C} (a : x ⟶ y) (b : x' ⟶ y') :
  bimap (⊗) a b ≫ elim_left _ = elim_left _ ≫ a :=
by simp only [bimap,map,product.map,intro_elim_left]

@[simp,reshuffled]
lemma bimap_elim_right [has_product.{u v} C]
  {x x' y y' : C} (a : x ⟶ y) (b : x' ⟶ y') :
  bimap (⊗) a b ≫ elim_right _ = elim_right _ ≫ b :=
by simp only [bimap,map,product.map,intro_elim_right]

@[simp,reshuffled]
lemma intro_left_bimap [has_coproduct.{u v} C]
  {x x' y y' : C} (a : x ⟶ y) (b : x' ⟶ y') :
  intro_left _ ≫ bimap (⨿) a b = a ≫ intro_left _ :=
by simp only [bimap,map,coproduct.map,intro_left_elim]

@[simp,reshuffled]
lemma intro_right_bimap [has_coproduct.{u v} C]
  {x x' y y' : C} (a : x ⟶ y) (b : x' ⟶ y') :
  intro_right _ ≫ bimap (⨿) a b = b ≫ intro_right _ :=
by simp only [bimap,map,coproduct.map,intro_right_elim]

end bimap

class Monoidal  (C : Type u) [𝒞 : category.{u v} C] :=
(prod' : C → C → C)
(infix ` ⊗ `:11 := prod')
[prod_functor : is_functor.{v v} (uncurry prod')]
(I : C)
(assoc' : Π a b c, a ⊗ (b ⊗ c) ≅ (a ⊗ b) ⊗ c)
(left_id'  : Π a, I ⊗ a ≅ a)
(right_id' : Π a, a ⊗ I ≅ a)
(infix ` × `:11 := bimap prod')
(triangle' : ∀ x y,
  (assoc' x I y).hom ≫ ((right_id' x).hom × 𝟙 y : (x ⊗ I) ⊗ y ⟶ x ⊗ y) =
  (𝟙 x × (left_id' y).hom) . obviously )
(pentagon' : ∀ w x y z,
  (assoc' w x (y ⊗ z)).hom ≫ (assoc' (w ⊗ x) y z).hom =
  (𝟙 w × (assoc' x y z).hom : w ⊗ (x ⊗ (y ⊗ z)) ⟶ w ⊗ ((x ⊗ y) ⊗ z)) ≫
  (assoc' w (x ⊗ y) z).hom ≫
  ((assoc' w x y).hom × 𝟙 z) . obviously )

end

namespace Monoidal
instance prod_is_functor {C} [category.{u v} C] [Monoidal C] :
is_functor.{v v} (uncurry Monoidal.prod' : C × C → C) :=
Monoidal.prod_functor C

infixr ` ⊗ `:51 := Monoidal.prod'
infixr ` ⊗ `:51 := bimap Monoidal.prod'

class MonoidalF
  {C₀ C₁ : Type u}
  [category.{u v} C₀]
  [category.{u v} C₁]
  [Monoidal.{u v} C₀]
  [Monoidal.{u v} C₁]
  (F : C₀ ⥤ C₁) :=
(preserves_I : F.obj (I C₀) ≅ I C₁)
(preserves_prod : Π X Y : C₀, F.obj (X ⊗ Y) ≅ F.obj X ⊗ F.obj Y)

variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞

section Monoidal
variables [Monoidal C]

def assoc (a b c : C) : a ⊗ (b ⊗ c) ≅ (a ⊗ b) ⊗ c := Monoidal.assoc'.{u v} a b c
def left_id (a : C) : I C ⊗ a ≅ a := Monoidal.left_id'.{u v} a
def right_id (a : C) : a ⊗ I C ≅ a := Monoidal.right_id'.{u v} a

@[reshuffled triangle'']
lemma triangle (x y: C) :
  (assoc x (I _) y).hom ≫ ((right_id x).hom ⊗ 𝟙 y) =
  (𝟙 x ⊗ (left_id y).hom)  :=
triangle'.{u v} _ x y

@[reshuffled pentagon'']
lemma pentagon (w x y z : C) :
  (assoc w x (y ⊗ z)).hom ≫ (assoc (w ⊗ x) y z).hom =
  (𝟙 w ⊗ (assoc x y z).hom) ≫
  (assoc w (x ⊗ y) z).hom ≫
  ((assoc w x y).hom ⊗ 𝟙 z) :=
pentagon'.{u v} _ w x y z

@[simp]
lemma prod_id {x x' : C} :
  (𝟙 x) ⊗ (𝟙 x') = 𝟙 (x ⊗ x') :=
@map_id.{v v} _ _ _ _ (uncurry Monoidal.prod') _ (x,x')

@[simp]
lemma prod_comp {x y z x' y' z' : C}
  (f : x ⟶ y) (g : y ⟶ z)
  (f' : x' ⟶ y') (g' : y' ⟶ z') :
  (f ≫ g) ⊗ (f' ≫ g') = (f ⊗ f') ≫ (g ⊗ g') :=
@map_comp.{v v} _ _ _ _ (uncurry Monoidal.prod') _ (x,x') (y,y') (z,z') (f,f') (g,g')

end Monoidal
section instances
variables (C)
open has_product has_terminal
def product_monoidal : Type u := C
-- set_option pp.universes true
instance : category (product_monoidal C) := 𝒞

instance product_monoidal.category [has_product.{u v} C] [has_terminal.{u v} C] : Monoidal (product_monoidal C) :=
suffices Monoidal C, from this,
{ prod' := (has_prod.prod' : C → C → C),
  I := (term C : C),
  left_id' := λ a,
  { hom := elim_right (term C),
    inv := intro (intro _) (𝟙 _),
    hom_inv_id' := by { ext; simp only [category.assoc,category.comp_id,category.id_comp,intro_elim_left,intro_elim_right,unique_iff,eq_self_iff_true] },
    inv_hom_id' := by { rw intro_elim_right, } },
  right_id' := λ a,
  { hom := elim_left (term C),
    inv := intro (𝟙 _) (intro _),
    hom_inv_id' := by { ext; simp only [category.assoc,category.comp_id,category.id_comp,intro_elim_left,intro_elim_right,unique_iff,eq_self_iff_true] },
    inv_hom_id' := by { rw intro_elim_left, } },
  assoc' := λ a b c,
  { hom := intro (intro (elim_left _) (elim_right _ ≫ elim_left _)) (elim_right _ ≫ elim_right _),
    inv := intro (elim_left _ ≫ elim_left _) (intro (elim_left _ ≫ elim_right _) (elim_right _)),
    hom_inv_id' := by { ext; simp only [category.assoc, category.id_comp, intro_elim_left', intro_elim_left, intro_elim_right, eq_self_iff_true] },
    inv_hom_id' := by { ext; simp only [category.assoc,category.id_comp,intro_elim_left,intro_elim_right',intro_elim_right,eq_self_iff_true] } },
  triangle' := by { intros, ext; simp only [category.comp_id,intro_elim_right,bimap_elim_right,category.assoc,intro_elim_left',intro_elim_left,bimap_elim_left] },
  pentagon' := by { intros, simp only [bimap_elim_left,comp_intro, bimap, map, product.map,intro_elim_left,intro_elim_right,intro_elim_left',intro_elim_right',category.comp_id,category.id_comp,category.assoc, eq_self_iff_true] } }

end instances

end Monoidal

section
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
(assoc : op ≫ (𝟙 M ⊗ op) ≫ (assoc M M M).hom =
         op ≫ (op ⊗ 𝟙 M))

section endofunctors

variables (C : Type u₁) [𝒞 : category.{u₁ v₁} C]
include 𝒞

def endofunctor.map : Π {x y : (C ⥤ C) × (C ⥤ C)}, (x ⟶ y) → (uncurry (⋙) x ⟶ uncurry (⋙) y)
| (x₀,x₁) (y₀,y₁) (f,g) := f ◫ g

instance : is_functor.{(max u₁ v₁) (max u₁ v₁)} (uncurry (⋙) : (C ⥤ C) × (C ⥤ C) → (C ⥤ C)) :=
{ map := λ x y, endofunctor.map C,
  map_id := by { rintro ⟨x₀,x₁⟩, dsimp [endofunctor.map,category.id,uncurry], ext, simp only [category.comp_id,nat_trans.hcomp_app,nat_trans.id_app,functor.map_id], refl },
  map_comp := by { rintro ⟨x₀,x₁⟩ ⟨y₀,y₁⟩ ⟨z₀,z₁⟩ ⟨f₀,f₁⟩ ⟨g₀,g₁⟩, simp only [endofunctor.map,(≫),nat_trans.exchange], } }

-- def hcomp {F G : C ⥤ D} {H I : D ⥤ E} (α : F ⟹ G) (β : H ⟹ I) : (F ⋙ H) ⟹ (G ⋙ I) :=
-- { app         := λ X : C, (β.app (F.obj X)) ≫ (I.map (α.app X)),

@[simp]
lemma functor.bimap_app {x x' y y' : C ⥤ C}
  (f : x ⟶ y) (g : x' ⟶ y') (a : C) :
  (bimap (⋙) f g).app a = (g.app (x.obj a) ≫ y'.map (f.app a)) :=
by { simp [bimap,nat_trans.naturality,map,endofunctor.map], }

instance functor.Monoidal_category :
  Monoidal.{(max u₁ v₁) (max u₁ v₁)} (C ⥤ C) :=
{ I := functor.id C,
  prod' := (⋙),
  right_id' := functor.comp_id,
  left_id'  := functor.id_comp,
  assoc'    := by { obviously } }

end endofunctors

instance types.Monoidal_category :
  Monoidal Type.{u} :=
product_monoidal.category (Type u)

section prod

variables (C₀ : Type u)
          (C₁ : Type u)
          -- (C₂ : Type u)
          -- (C₃ : Type u)

-- def function.assoc (a : (C₀ × C₁) × C₂) : (C₀ × (C₁ × C₂)) :=
-- (a.1.1, a.1.2, a.2)

variables
   [𝒞₀ : category.{u v} C₀]
   [𝒞₁ : category.{u v} C₁] -- [Monoidal C₁]
          -- (C₂ : Type u)
   -- [𝒞₂ : category.{u v} C₂] -- [Monoidal C₂]
   -- [𝒞₃ : category.{u v} C₃] -- [Monoidal C₂]

include 𝒞₀ 𝒞₁

section iso_prod
-- def prod.assoc : ((C₀ × C₁) × C₂) ⥤ (C₀ × (C₁ × C₂)) :=
-- { obj := λ (a : (C₀ × C₁) × C₂), (a.1.1, a.1.2, a.2),
--   map := λ (X Y : (C₀ × C₁) × C₂) f, (f.1.1, f.1.2, f.2) }

-- def prod.regroup : ((C₀ × C₁) × (C₂ × C₃)) ⥤ ((C₀ × C₂) × (C₁ × C₃)) :=
-- { obj := λ a, ((a.1.1,a.2.1),(a.1.2,a.2.2)),
--   map := λ X Y a, ((a.1.1,a.2.1),(a.1.2,a.2.2)) }

-- omit 𝒞₂ 𝒞₃
variables {C₀ C₁}
def iso.prod {x₀ y₀ : C₀} {x₁ y₁ : C₁}
  (h₀ : x₀ ≅ y₀) (h₁ : x₁ ≅ y₁) : (x₀, x₁) ≅ (y₀, y₁) :=
{ hom := (h₀.hom,h₁.hom),
  inv := (h₀.inv,h₁.inv), }

variables {x₀ y₀ : C₀} {x₁ y₁ : C₁}
  (h₀ : x₀ ≅ y₀) (h₁ : x₁ ≅ y₁)

@[simp]
lemma iso_prod_hom : (iso.prod h₀ h₁).hom = (h₀.hom,h₁.hom) := rfl

@[simp]
lemma iso_prod_inv : (iso.prod h₀ h₁).inv = (h₀.inv,h₁.inv) := rfl

end iso_prod

variables  [Monoidal.{u v} C₀] [Monoidal.{u v} C₁]

variables {C₀ C₁}

def prod.prod : C₀ × C₁ → C₀ × C₁ → C₀ × C₁
| (x₀,x₁) (y₀,y₁) := (x₀ ⊗ y₀,x₁ ⊗ y₁)

def prod.prod.map : Π {x y : (C₀ × C₁) × (C₀ × C₁)}, (x ⟶ y) → (uncurry prod.prod x ⟶ uncurry prod.prod y)
| ((x₀,x₁),x₂,x₃) ((y₀,y₁),y₂,y₃) (f,g) := (f.1 ⊗ g.1,f.2 ⊗ g.2)

instance prod.is_functor : is_functor.{v v} (uncurry $ @prod.prod C₀ C₁ _ _ _ _) :=
{ map := λ x y, prod.prod.map,
  map_id := by { intros, casesm* [_ × _,_ ⟶ _], dsimp [uncurry,prod.prod], simp only [prod.prod.map,category.id,uncurry,prod.prod,Monoidal.prod_id], },
  map_comp := by { intros, casesm* [_ × _,_ ⟶ _], simp only [prod.prod.map,(≫),Monoidal.prod_comp] } }

@[simp]
lemma bimap_prod_prod {w₀ x₀ y₀ z₀ : C₀} {w₁ x₁ y₁ z₁ : C₁}
  (f₀ : w₀ ⟶ x₀) (g₀ : y₀ ⟶ z₀)
  (f₁ : w₁ ⟶ x₁) (g₁ : y₁ ⟶ z₁) :
  (bimap prod.prod (f₀, f₁) (g₀, g₁) : prod.prod (w₀,w₁) (y₀,y₁) ⟶ prod.prod (x₀,x₁) (z₀,z₁)) =
  (bimap prod' f₀ g₀, bimap prod' f₁ g₁) := rfl

instance prod.Monoidal_category [Monoidal.{u v} C₀] [Monoidal.{u v} C₁] :
  Monoidal (C₀ × C₁) :=
{ I := (I _, I _),
  prod' := prod.prod,
  assoc' := λ ⟨a₀,a₁⟩ ⟨b₀,b₁⟩ ⟨c₀,c₁⟩, iso.prod (assoc _ _ _) (assoc _ _ _),
  left_id' := λ ⟨a₀,a₁⟩, iso.prod (left_id a₀) (left_id a₁),
  right_id' := λ ⟨a₀,a₁⟩, iso.prod (right_id a₀) (right_id a₁),
  triangle' := by { rintro ⟨ ⟩ ⟨ ⟩, simp! only [triangle,prod_comp,bimap_prod_prod,iso_prod_hom,prod_id], },
  pentagon' := by { rintro ⟨ ⟩ ⟨ ⟩ ⟨ ⟩ ⟨ ⟩, simp! only [pentagon,prod_comp,bimap_prod_prod,iso_prod_hom,prod_id], }, }

variables [Monoidal.{u v} C₀] [Monoidal.{u v} C₁]

instance prod.MonoidalF : MonoidalF (prod.swap C₀ C₁) :=
sorry

variables
          (C₂ : Type u)
          [𝒞₂ : category.{u v} C₂] -- [Monoidal C₂]
          [𝒞 : Monoidal.{u v} C₂]
include 𝒞

instance comp.MonoidalF (F : C₀ ⥤ C₁) (G : C₁ ⥤ C₂) : MonoidalF (F ⋙ G) :=
sorry

end prod
-- option ∘ (nat,_) ∘ cofix ∘ F
#check Monoidal.prod'


section opposite
open Monoidal
-- def op.prod (C) [category.{u v} C] [Monoidal.{u v} C] : (Cᵒᵖ × (Cᵒᵖ)) ⥤ (Cᵒᵖ) :=
-- { obj := λ (X : C × C), (prod' C).obj X,
--   map := λ (X Y : C × (C)) (a : Y ⟶ X), (Monoidal.prod' C).map a,
--   map_id' := sorry,
--   map_comp' := sorry }

variables (C : Type u) [𝒞 : category.{u v} C]
include 𝒞

def iso.op {x₀ y₀ : Cᵒᵖ}
  (h₀ : (id x₀ : C) ≅ (id y₀ : C)) : x₀ ≅ y₀ :=
{ hom := (h₀.inv : @category.hom (Cᵒᵖ) _ x₀ y₀),
  inv := (h₀.hom : @category.hom (Cᵒᵖ) _ y₀ x₀),
  hom_inv_id' := iso.hom_inv_id h₀,
  inv_hom_id' := iso.inv_hom_id h₀ }

section iso_op

variables {x₀ y₀ : C} (h₀ : x₀ ≅ y₀)

@[simp]
lemma iso_op_hom : (iso.op C h₀).hom = (h₀.inv) := rfl

@[simp]
lemma iso_op_inv : (iso.op C h₀).inv = (h₀.hom) := rfl

end iso_op

instance of_iso_inverse {X Y : C} (f : X ⟶ Y) [is_iso f] : is_iso.{u v} (inv f) :=
{ inv := f }

def inv_injective {X Y : C} (a b : X ⟶ Y) [is_iso.{u v} a] [is_iso.{u v} b]
  (h : inv a = inv b):
  a = b :=
begin
  suffices : a ≫ inv a = b ≫ inv a,
  { apply mono.right_cancellation a b this },
  simp, simp [h],
end

def left [Monoidal.{u v} C] {a b : C} (c : C) (f : a ⟶ b) : a⊗c ⟶ b⊗c :=
f ⊗ 𝟙 _

def right [Monoidal.{u v} C] {a b : C} (c : C) (f : a ⟶ b) : c⊗a ⟶ c⊗b :=
𝟙 _ ⊗ f

lemma inv_inj {x y : C} {f g : x ⟶ y} [is_iso f] [is_iso g]
  (h : inv f = inv g) :
  f = g :=
calc
      f
    = 𝟙 _ ≫ f         : by simp
... = (g ≫ inv g) ≫ f : by rw [is_iso.hom_inv_id]
... = g ≫ inv f ≫ f   : by rw [h,category.assoc]
... = g               : by rw [is_iso.inv_hom_id,category.comp_id]

-- def inv'
attribute [reshuffled is_iso.hom_inv_id''] is_iso.hom_inv_id
attribute [reshuffled is_iso.inv_hom_id''] is_iso.inv_hom_id

instance comp.is_iso {x y z : C} (f : x ⟶ y) (g : y ⟶ z) [is_iso f] [is_iso g] : is_iso (f ≫ g) :=
{ inv := inv g ≫ inv f,
  hom_inv_id' := by simp,
  inv_hom_id' := by simp }

lemma inv_comp {x y z : C} (f : x ⟶ y) (g : y ⟶ z) [is_iso f] [is_iso g] :
  inv (f ≫ g) = inv g ≫ inv f :=
by refl

variables [M : Monoidal.{u v} C]
include M

instance prod.is_iso {x x' y y' : C} (f : x ⟶ y) (g : x' ⟶ y') [is_iso f] [is_iso g] : is_iso (f ⊗ g) :=
{ inv := inv f ⊗ inv g,
  hom_inv_id' := by rw [← Monoidal.prod_comp,is_iso.hom_inv_id,is_iso.hom_inv_id,Monoidal.prod_id],
  inv_hom_id' := by rw [← Monoidal.prod_comp,is_iso.inv_hom_id,is_iso.inv_hom_id,Monoidal.prod_id] }

lemma inv_prod {x x' y y' : C} (f : x ⟶ y) (g : x' ⟶ y') [is_iso f] [is_iso g] :
  inv (f ⊗ g) = inv f ⊗ inv g :=
by refl

lemma inv_inv {x y : C} (f : x ≅ y) :
  inv (f.inv) = f.hom :=
by refl

lemma inv_id {x : C} :
  inv (𝟙 x) = 𝟙 x :=
by refl

-- set_option pp.all true
-- set_option pp.universes true
-- set_option pp.implicit true


#check comp.is_iso
-- #check prod.is_iso
#print instances is_iso
-- set_option class.instance_max_depth 100

instance op.Monoidal_category :
  Monoidal.{u v} (Cᵒᵖ) :=
{ prod' := (prod' : C → C → C),
  I := (I.{u v} C : C),
  prod_functor := is_functor.op (uncurry prod'),
  assoc' := λ a b c : C, iso.op _ (assoc a b c),
  left_id' := λ a : C, iso.op _ (left_id _),
  right_id' := λ a : C, iso.op _ (right_id _),
  triangle' := by { intros, dsimp [(≫)],  apply inv_inj.{u v} C ,
                    repeat {
                      apply comp.is_iso C _ _ <|>
                      apply prod.is_iso C _ _ <|>
                      apply is_iso.of_iso_inverse.{u v} _ <|>
                      apply is_iso.category_theory.is_iso },
                    erw [inv_comp,inv_inv,inv_prod.{u v},inv_prod.{u v},triangle,inv_id,inv_inv] },
  pentagon' := by { intros, dsimp [(≫)],  apply inv_inj.{u v} C ,
                    repeat {
                      apply comp.is_iso C _ _ <|>
                      apply prod.is_iso C _ _ <|>
                      apply is_iso.of_iso_inverse.{u v} _ <|>
                      apply is_iso.category_theory.is_iso },
                    repeat {
                      erw [inv_comp] <|>
                      erw [inv_prod] <|>
                      erw [inv_id]  <|>
                      erw [inv_inv] },
                    apply pentagon }, }

end opposite

@[reducible]
def Monad (C : Type u) [category C] (M : C ⥤ C) := Monoid (C ⥤ C) M
@[reducible]
def Comonad (C : Type u) [category C] (M : C ⥤ C) := Comonoid (C ⥤ C) M

section types

variables (M : Type u ⥤ Type u) [Monad (Type u) M]

instance (M) [Monad (Type u) M] : monad M.obj :=
{ map := λ α β f x, M.map f x,
  pure := λ α x, nat_trans.app (Monoid.unit M) α x,
  bind := λ α β x f, nat_trans.app (Monoid.op M) β (M.map f x) }

instance (M) [Comonad (Type u) M] : comonad M.obj :=
{ map := M.map,
  extract := λ α x, nat_trans.app (Comonoid.unit M) α x,
  extend := λ α β f x, M.map f (nat_trans.app (Comonoid.op M) α x) }

run_cmd mk_simp_attr `category []

@[category] lemma id_eq_unit {α : Type u} : @id α = 𝟙 α := rfl

variables
  (f g : Type u ⥤ Type v) (T : f ⟹ g) {α β : Type u}
  (a : α ⟶ β)
  (b : f.obj α ⟶ f.obj β)
  (c : g.obj α ⟶ g.obj β)


#check @nat_trans.naturality

-- @[category]
lemma d (x : f.obj α) :
  T.app β (f.map a x) = g.map a (T.app α x) :=
begin
  have := congr_fun (nat_trans.naturality T a) x,
  apply this,
end

@[category]
lemma cc (x : f.obj α) :
  c (T.app α x) = (T.app α ≫ c) x := rfl

@[category]
lemma cc' (x : f.obj α) :
  T.app β (b x) = (b ≫ T.app β) x := rfl

lemma d' (x : f.obj α) :
  g.map a (T.app α x) = (f.map a ≫ T.app _) x :=
begin
  have := congr_fun (nat_trans.naturality T a) x,
  apply this.symm,
end

instance (M) [Monad (Type u) M] : is_lawful_monad M.obj :=
begin
  admit
  -- refine { bind_pure_comp_eq_map := _, .. }; intros,
  -- { dunfold functor.map, simp only [functor.map_id] with category, refl },
  -- { simp only [pure,(>>=)] with category,
  --   change nat_trans.app (Monoid.op M) β ((nat_trans.app (Monoid.unit M) α ≫ M.map f) x) = _,
  --   -- type_check ((_ : M ⊗ M ⟶ M) : M ⟹ _),
  --   type_check (M.map f),
  --   type_check Monoid.op M,
  --   type_check (nat_trans.app (Monoid.op M) β),
  --   let X := nat_trans.app (Monoid.op M) β,
  --   change ((nat_trans.app (Monoid.unit M) α ≫ M.map f) ≫ X) x = _,
  --   simp [X,nat_trans.naturality,category.assoc],
  --   -- rw  cc _ _ (Monoid.unit M) (M.map f),
  --   -- type_check nat_trans.app (Monoid.op M) β,
  --   -- type_check ((nat_trans.app (Monoid.unit M) α ≫ M.map f)),
  --   -- change (nat_trans.app (Monoid.unit M) α ≫ M.map f ≫ nat_trans.app (Monoid.op M) β) x = _,
  --   -- rw cc' _ _ (Monoid.op M) (_ ≫ M.map f),
  --   -- type_check (nat_trans.app (Monoid.unit M) α ≫ M.map f),
  --   -- rw  cc' _ _ (Monoid.op M)   x,
  --   -- rw d _ M (Monoid.op M),
  --   -- type_check nat_trans.app (Monoid.op M) β _,
  --   -- type_check Monoid.unit M,
  --   -- type_check Monoid.op M,
  --   -- unfold_coes,
  --   -- have : (functor.map M f ((Monoid.unit M) α x)) = _,
  --   -- conv in (functor.map M f _) { change (Monoid.unit M ≫ functor.map M f) _ , },
  --   -- type_check Monoid.unit M,
  --   -- type_check @id (_ ⟹ _) (Monoid.op M),
  --   }
end

instance (M) [Comonad (Type u) M] : is_lawful_comonad M.obj :=
sorry

end types

section Kleisli

variables (C : Type u) [category.{u v} C] (M : C ⥤ C) [Monad C M]
include M
def Kleisli := C
open nat_trans category
#check Monoid.left_id M

instance Kleisli.category : category (Kleisli C M) :=
{ hom := λ X Y : C, X ⟶ M.obj Y,
  id := λ X : C, nat_trans.app (Monoid.unit M) X,
  comp := λ (X Y Z : C) f g, f ≫ M.map g ≫ nat_trans.app (Monoid.op M) Z,
  id_comp' := by { obviously, rw [← category.assoc,← naturality (Monoid.unit M),category.assoc],
                   let V : (M ⋙ M) ⟹ M := Monoid.op M,
                   let II : functor.id C ⟹ M := (Monoid.unit M),
                   -- let VV : M ⋙ functor.id C ⟹ M ⋙ M := hcomp (nat_trans.id M) II,
                   let VV : functor.id C ⋙ M ⟹ M ⋙ M := hcomp II (nat_trans.id M),
                   let WW := (⊟) VV V,
                   let ZZ := WW.app Y,
                   let YY := (Monoidal.I (C ⥤ C)).map f,
                   let XX := YY ≫ ZZ,
                   admit },
                   -- -- dsimp [(⟶),(⊗)] at V, ◫
                   -- change _ ≫ nat_trans.app ((⊟) ((◫) _ _) _) _ = _,
                   -- -- conv in (nat_trans.app (Monoid.unit M) (M.obj Y) ≫ nat_trans.app _ _)
                   -- -- {  },
                   -- dsimp [Monoid.unit], },
  comp_id' := sorry,
  assoc' := sorry }

end Kleisli
end
end category_theory
