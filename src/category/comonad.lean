
import category_theory.types

universes u v

class comonad (w : Type u → Type v)
extends functor w :=
-- (eq : Π {α}, w α → w α → Type u)
(extract : Π {α}, w α → α)
(extend : Π {α β}, (w α → β) → w α → w β)

-- infix ` ≈ ` := comonad.eq
-- #check comonad.eq
open functor comonad

def duplicate {w} [comonad w] {α} : w α → w (w α) := extend id

class is_lawful_comonad (w : Type u → Type v) [comonad w]
extends is_lawful_functor w :=
(extend_extract : ∀ {α} (x : w α), extend extract x = x)
(extract_extend : ∀ {α β} (f : w α → β) (x : w α), extract (extend f x) = f x)
(extend_extend : ∀ {α β γ} (f : w α → β) (g : w β → γ) (x : w α),
  extend g (extend f x) = extend (g ∘ extend f) x)
(map_eq_extend : ∀ {α β} (f : α → β) (x : w α),
  map f x = extend (f ∘ extract) x)
-- (eq_refl : ∀ {a} (x : w a), x ≈ x)
-- (eq_ext : ∀ {α : MType} (x y : α), w (x ≈ y) ⟶ ↑(x = y))

-- instead of using a functor on types, use a functor on modal types

export is_lawful_comonad

attribute [functor_norm] extend_extract extract_extend extend_extend

section duplicate

variables {w : Type u → Type u}
  [comonad w]
  [is_lawful_comonad w]
variables {α β γ φ : Type u}
variables (x : w α) (f : w α → β)

lemma extract_duplicate :
  extract (duplicate x) = x :=
by simp [duplicate,map_eq_extend,(∘)] with functor_norm

lemma map_extract_duplicate :
  map extract (duplicate x) = x :=
by simp [duplicate,map_eq_extend,(∘)] with functor_norm

lemma duplicate_duplicate :
  duplicate (duplicate x) = map duplicate (duplicate x) :=
by simp [duplicate,map_eq_extend,(∘)] with functor_norm

lemma extend_eq_map_duplicate :
  extend f x = map f (duplicate x) :=
by simp [duplicate,map_eq_extend,(∘)] with functor_norm

lemma duplicate_def :
  duplicate x = extend id x := rfl

end duplicate

variables {w : Type u → Type v}
  [comonad w]
  [is_lawful_comonad w]
variables {α β γ φ : Type u}

def copipe (f : w α → β) (g : w β → γ) : (w α → γ) :=
g ∘ extend f

infix ` =>= `:55 := copipe

section laws

@[functor_norm]
def copipe_extract (f : w α → β) :
  f =>= extract = f :=
by { ext, simp only [(=>=),(∘)] with functor_norm, }

@[functor_norm]
def extract_copipe (f : w α → β) :
  extract =>= f = f :=
by { ext, simp only [(=>=),(∘)] with functor_norm, }

@[functor_norm]
def copipe_assoc (f : w α → β) (g : w β → γ) (h : w γ → φ) :
  f =>= (g =>= h) = (f =>= g) =>= h :=
by { ext, simp only [(=>=),(∘)] with functor_norm, }

end laws



namespace category_theory

open comonad

def Cokleisli (m) [comonad.{u v} m] := Type u

def Cokleisli.mk (m) [comonad.{u v} m] (α : Type u) : Cokleisli m := α

instance Cokleisli.category {m} [comonad m] [is_lawful_comonad m] : category (Cokleisli.{u v} m) :=
by refine { hom := λ α β, m α → β,
         id := λ α, (extract),
         comp := λ X Y Z f g, f =>= g,
         id_comp' := _, comp_id' := _, assoc' := _ };
   intros; simp with functor_norm

@[simp] lemma Cokleisli.id_def {m} [comonad m] [is_lawful_comonad m] (α : Cokleisli m) :
  𝟙 α = @extract m _ α := rfl

@[simp] lemma Kleisli.comp_def {m} [comonad m] [is_lawful_comonad m] (α β γ : Cokleisli m)
  (xs : α ⟶ β) (ys : β ⟶ γ) :
  xs ≫ ys = xs =>= ys := rfl

end category_theory
