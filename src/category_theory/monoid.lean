import category_theory.functor
import category_theory.functor_category
import category_theory.opposites
-- import category_theory.tactics.obviously
import category_theory.isomorphism
import category_theory.natural_isomorphism
import category_theory.products
import category_theory.types
-- import tactic.converter.interactive
import tactic
import category.comonad

universes u v u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄

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

class Monoidal (C : Type u) [category.{u v} C] :=
(prod' : (C × C) ⥤ C)
(notation x ` ⊗ `:11 y:11 := prod'.obj (x, y))
(I : C)
(assoc' : Π a b c, a ⊗ (b ⊗ c) ≅ (a ⊗ b) ⊗ c)
(left_id'  : Π a, I ⊗ a ≅ a)
(right_id' : Π a, a ⊗ I ≅ a)
(notation x ` × `:11 y:11 := prod'.map (x, y))
(triangle' : ∀ x y,
  (assoc' x I y).hom ≫ ((right_id' x).hom × 𝟙 y : (x ⊗ I) ⊗ y ⟶ x ⊗ y) =
  (𝟙 x × (left_id' y).hom) . obviously )
(pentagon' : ∀ w x y z,
  (assoc' w x (y ⊗ z)).hom ≫ (assoc' (w ⊗ x) y z).hom =
  (𝟙 w × (assoc' x y z).hom : w ⊗ (x ⊗ (y ⊗ z)) ⟶ w ⊗ ((x ⊗ y) ⊗ z)) ≫
  (assoc' w (x ⊗ y) z).hom ≫
  ((assoc' w x y).hom × 𝟙 z) . obviously )

namespace Monoidal
def prod {C : Type u} [category.{u v} C] [Monoidal C] (x y : C) := (Monoidal.prod' _).obj (x,y)

infixr ` ⊗ `:11 := Monoidal.prod

class MonoidalF
  {C₀ C₁ : Type u}
  [category.{u v} C₀]
  [category.{u v} C₁]
  [Monoidal.{u v} C₀]
  [Monoidal.{u v} C₁]
  (F : C₀ ⥤ C₁) :=
(preserves_I : F.obj (I C₀) ≅ I C₁)
(preserves_prod : Π X Y : C₀, F.obj (X ⊗ Y) ≅ F.obj X ⊗ F.obj Y)

variables {C : Type u} [category.{u v} C] [Monoidal C]

def assoc (a b c : C) : a ⊗ (b ⊗ c) ≅ (a ⊗ b) ⊗ c := Monoidal.assoc'.{u v} a b c
def left_id (a : C) : I C ⊗ a ≅ a := Monoidal.left_id'.{u v} a
def right_id (a : C) : a ⊗ I C ≅ a := Monoidal.right_id'.{u v} a

def prod_map {C : Type u} [category.{u v} C] [Monoidal C] {x x' y y' : C}
  (a : x ⟶ x') (b : y ⟶ y') : x ⊗ y ⟶ x' ⊗ y' :=
(Monoidal.prod' C).map (a,b)

infixr ` ⊗ `:11 := Monoidal.prod_map

lemma triangle (x y: C) :
  (assoc x (I _) y).hom ≫ ((right_id x).hom ⊗ 𝟙 y) =
  (𝟙 x ⊗ (left_id y).hom)  :=
triangle'.{u v} _ x y

lemma pentagon (w x y z : C) :
  (assoc w x (y ⊗ z)).hom ≫ (assoc (w ⊗ x) y z).hom =
  (𝟙 w ⊗ (assoc x y z).hom) ≫
  (assoc w (x ⊗ y) z).hom ≫
  ((assoc w x y).hom ⊗ 𝟙 z) :=
pentagon'.{u v} _ w x y z

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

def functor.tensor_prod (C : Type u₁) [category.{u₁ v₁} C] : ( (C ⥤ C) × (C ⥤ C) ) ⥤ (C ⥤ C) :=
{ obj := λ a, a.1 ⋙ a.2, map := λ a b f, f.1 ◫ f.2,
  map_comp' := sorry }

@[simp]
lemma functor.tensor_prod_prod (C : Type u₁) [category.{u₁ v₁} C] (x y : C ⥤ C) :
  (functor.tensor_prod C).obj (x,y) = x ⋙ y := rfl

@[simp]
lemma functor.tensor_prod_map (C : Type u₁) [category.{u₁ v₁} C] (f g : (C ⥤ C × C ⥤ C))
  (x : f.1 ⟹ g.1) (y : f.2 ⟹ g.2) :
  (functor.tensor_prod C).map (x,y) = (x ◫ y) := rfl

instance functor.Monoidal_category (C : Type u₁) [category.{u₁ v₁} C] :
  Monoidal.{(max u₁ v₁) (max u₁ v₁)} (C ⥤ C) :=
{ I := functor.id C,
  prod' := functor.tensor_prod C,
  right_id' := functor.comp_id,
  left_id'  := functor.id_comp,
  assoc'    := by { obviously } }

instance types.Monoidal_category :
  Monoidal Type.{u} :=
{ I := punit,
  prod' := { obj := λ x, x.1 × x.2,
             map := λ X Y f x, (f.1 x.1,f.2 x.2) },
  right_id' := λ a, { hom := λ a, a.1, inv := λ a, (a,punit.star) },
  left_id'  := λ a, { hom := λ a, a.2, inv := λ a, (punit.star,a) },
  assoc'    := λ α β γ, { hom := λ ⟨a,b,c⟩, ((a,b),c), inv := λ ⟨⟨a,b⟩,c⟩, (a,(b,c)) } }


variables (C₀ : Type u)
          (C₁ : Type u)
          (C₂ : Type u)
          (C₃ : Type u)

def function.assoc (a : (C₀ × C₁) × C₂) : (C₀ × (C₁ × C₂)) :=
(a.1.1, a.1.2, a.2)

variables
   [𝒞₀ : category.{u v} C₀]
   [𝒞₁ : category.{u v} C₁] -- [Monoidal C₁]
   [𝒞₂ : category.{u v} C₂] -- [Monoidal C₂]
   [𝒞₃ : category.{u v} C₃] -- [Monoidal C₂]

include 𝒞₀ 𝒞₁ 𝒞₂ 𝒞₃

def prod.assoc : ((C₀ × C₁) × C₂) ⥤ (C₀ × (C₁ × C₂)) :=
{ obj := λ (a : (C₀ × C₁) × C₂), (a.1.1, a.1.2, a.2),
  map := λ (X Y : (C₀ × C₁) × C₂) f, (f.1.1, f.1.2, f.2) }

def prod.regroup : ((C₀ × C₁) × (C₂ × C₃)) ⥤ ((C₀ × C₂) × (C₁ × C₃)) :=
{ obj := λ a, ((a.1.1,a.2.1),(a.1.2,a.2.2)),
  map := λ X Y a, ((a.1.1,a.2.1),(a.1.2,a.2.2)) }

omit 𝒞₂ 𝒞₃

def iso.prod {x₀ y₀ : C₀} {x₁ y₁ : C₁}
  (h₀ : x₀ ≅ y₀) (h₁ : x₁ ≅ y₁) : (x₀, x₁) ≅ (y₀, y₁) :=
{ hom := (h₀.hom,h₁.hom),
  inv := (h₀.inv,h₁.inv), }

instance prod.Monoidal_category [Monoidal.{u v} C₀] [Monoidal.{u v} C₁] :
  Monoidal (C₀ × C₁) :=
{ I := (I _, I _),
  prod' := prod.regroup _ _ _ _ ⋙ functor.prod (prod' C₀) (prod' C₁),
  assoc' := λ (X Y Z : C₀ × C₁),
    iso.prod _ _ (assoc' _ _ _) (assoc' _ _ _),
  left_id' := λ (X : C₀ × C₁),
    { hom := ((left_id' _).hom,(left_id' _).hom),
      inv := ((left_id' _).inv,(left_id' _).inv) },
  right_id' := λ (X : C₀ × C₁),
    { hom := ((right_id' _).hom,(right_id' _).hom),
      inv := ((right_id' _).inv,(right_id' _).inv) },
  triangle' := sorry,
  pentagon' := sorry }
  -- right_id' := by { intros, dsimp [functor.prod,prod.regroup],
  --                   repeat { fsplit },
  --                   apply (right_id' _).hom, apply (right_id' _).hom,
  --                   apply (right_id' _).inv, apply (right_id' _).inv,
  --                   admit, admit },
  -- left_id'  := by { intros, dsimp [functor.prod,prod.regroup],
  --                   repeat { fsplit },
  --                   apply (left_id' _).hom, apply (left_id' _).hom,
  --                   apply (left_id' _).inv, apply (left_id' _).inv,
  --                   admit, admit },
  -- assoc'    := by { admit } }

variables [Monoidal.{u v} C₀] [Monoidal.{u v} C₁]

instance prod.MonoidalF : MonoidalF (prod.swap C₀ C₁) :=
sorry

variables [𝒞 : Monoidal.{u v} C₂]
include 𝒞

instance comp.MonoidalF (F : C₀ ⥤ C₁) (G : C₁ ⥤ C₂) : MonoidalF (F ⋙ G) :=
sorry

end
-- option ∘ (nat,_) ∘ cofix ∘ F
#check Monoidal.prod'


section opposite
open Monoidal
def op.prod (C) [category.{u v} C] [Monoidal.{u v} C] : (Cᵒᵖ × (Cᵒᵖ)) ⥤ (Cᵒᵖ) :=
{ obj := λ (X : C × C), (prod' C).obj X,
  map := λ (X Y : C × (C)) (a : Y ⟶ X), (Monoidal.prod' C).map a,
  map_id' := sorry,
  map_comp' := sorry }

variables (C : Type u) [category.{u v} C]

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

instance op.Monoidal_category (C) [category.{u v} C] [Monoidal.{u v} C] :
  Monoidal.{u v} (Cᵒᵖ) :=
{ prod' := op.prod.{u v} C,
  I := (I.{u v} C : C),
  assoc' := sorry,
  left_id' := sorry,
  right_id' := sorry,
  triangle' := sorry,
  pentagon' := sorry }

end opposite

class Monad (C : Type u) [category C] (M : C ⥤ C) extends Monoid (C ⥤ C) M

class Comonad (C : Type u) [category C] (M : C ⥤ C) extends Comonoid (C ⥤ C) M

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
  id_comp' := by { obviously, rw [← assoc,← naturality (Monoid.unit M),assoc],
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

end category_theory
