import category_theory.functor
import category_theory.tactics.obviously
import category_theory.isomorphism
import category_theory.products
import category_theory.types
import tactic.converter.interactive
import tactic
import category.comonad

universes u v u₁ v₁ u₂ v₂

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
{ obj := λ a, a.1 ⋙ a.2, map := λ a b f, f.1 ◫ f.2 }

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

#check Monoidal.prod'

def op.prod (C) [category.{u v} C] [Monoidal.{u v} C] : (Cᵒᵖ × (Cᵒᵖ)) ⥤ (Cᵒᵖ) :=
{ obj := λ (X : C × C), (prod' C).obj X,
  map := λ (X Y : C × (C)) (a : Y ⟶ X), (Monoidal.prod' C).map a }

-- set_option pp.all true
#check mono.right_cancellation

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

instance op.Monoidal_category (C) [category.{u v} C] [Monoidal.{u v} C] :
  Monoidal.{u v} (Cᵒᵖ) :=
{ prod' := op.prod.{u v} C,
  I := (I.{u v} C : C),
  assoc' := sorry,
  left_id' := sorry,
  right_id' := sorry,
  triangle' := sorry,
  pentagon' := sorry }

class Monad (C : Type u) [category C] (M : C ⥤ C) extends Monoid (C ⥤ C) M

class Comonad (C : Type u) [category C] (M : C ⥤ C) extends Comonoid (C ⥤ C) M

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
  refine { bind_pure_comp_eq_map := _, .. }; intros,
  { dunfold functor.map, simp only [functor.map_id] with category, refl },
  { simp only [pure,(>>=)] with category,
    change nat_trans.app (Monoid.op M) β ((nat_trans.app (Monoid.unit M) α ≫ M.map f) x) = _,
    -- type_check ((_ : M ⊗ M ⟶ M) : M ⟹ _),
    type_check (M.map f),
    type_check Monoid.op M,
    type_check (nat_trans.app (Monoid.op M) β),
    let X := nat_trans.app (Monoid.op M) β,
    change ((nat_trans.app (Monoid.unit M) α ≫ M.map f) ≫ X) x = _,
    simp [X,nat_trans.naturality,category.assoc],
    -- rw  cc _ _ (Monoid.unit M) (M.map f),
    -- type_check nat_trans.app (Monoid.op M) β,
    -- type_check ((nat_trans.app (Monoid.unit M) α ≫ M.map f)),
    -- change (nat_trans.app (Monoid.unit M) α ≫ M.map f ≫ nat_trans.app (Monoid.op M) β) x = _,
    -- rw cc' _ _ (Monoid.op M) (_ ≫ M.map f),
    -- type_check (nat_trans.app (Monoid.unit M) α ≫ M.map f),
    -- rw  cc' _ _ (Monoid.op M)   x,
    -- rw d _ M (Monoid.op M),
    -- type_check nat_trans.app (Monoid.op M) β _,
    -- type_check Monoid.unit M,
    -- type_check Monoid.op M,
    -- unfold_coes,
    -- have : (functor.map M f ((Monoid.unit M) α x)) = _,
    -- conv in (functor.map M f _) { change (Monoid.unit M ≫ functor.map M f) _ , },
    -- type_check Monoid.unit M,
    -- type_check @id (_ ⟹ _) (Monoid.op M),
    }
end

instance (M) [Comonad (Type u) M] : is_lawful_comonad M.obj :=
sorry

end category_theory
