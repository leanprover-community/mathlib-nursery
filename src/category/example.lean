
import category.comonad
import category_theory.category
import category_theory.monoid
import data.stream
import data.stream.basic
import tactic

universes u v

inductive slift (p : Prop) : Sort.{u}
| up (down : p) : slift

namespace stream

variables {α : Type u} {β : Type v}

def tails' (s : stream α) : stream (stream α)
| i := s.drop i
-- corec id tail (tail s)

theorem nth_tails' : ∀ (n : nat) (s : stream α), nth n (tails' s) = drop n s :=
begin
  intros, refl
end

attribute [extensionality] stream.ext

theorem drop_tails' : ∀ (n : nat) (s : stream α), drop n (tails' s) = tails' (drop n s) :=
begin
  intros, ext,
  simp [nth_tails',nth_drop],
end

lemma head_drop (s : stream α) (n : ℕ) : head (s.drop n) = s.nth n :=
by simp [head,drop,nth]

lemma drop_zero {α} (x : stream α) : drop 0 x = x := rfl

end stream

namespace category_theory

def pTime := Type.{u}
abbreviation Time := pTime.{0}

instance Time.category : category Time :=
{ hom := λ α β, stream α → stream β,
  id := λ α, @id (stream α),
  comp := λ α β γ f g, g ∘ f }

def TVar (α : Time) := (punit : Time) ⟶ α

def Henceforth : Time ⥤ Time :=
{ obj := λ α, stream α,
  map := λ X Y f, stream.map f }
open Monoidal
-- #check @Monoidal.I (Time ⥤ Time) _ _
-- #reduce Monoidal.I (Time ⥤ Time)
-- #reduce Henceforth ⟶ I (Time ⥤ Time)

local attribute [simp] stream.nth_map stream.nth_tails' stream.drop_tails' stream.map_id stream.head_drop
instance Time.comonad : Comonad Time Henceforth :=
{ unit := { app := λ X s, stream.head s },
  op := { app := λ X s, stream.tails' s },
  right_id := by { refl },
  left_id := by { dsimp [functor.tensor_prod,category_theory.Monoidal.prod_map,left_id,left_id',Henceforth,(⊟),(≫)],
                  unfold_projs, simp! [left_id',(∘),functor.tensor_prod],
                  unfold_projs, ext : 3, simp,    },
  assoc := by { dsimp [(≫),(⊟),(∘),category_theory.Monoidal.prod_map,prod',functor.tensor_prod,category_theory.Monoidal.prod,assoc,Henceforth],
                unfold_projs,
                congr, ext X s : 3, simp [(⋙),functor.tensor_prod],
                erw [iso.refl_hom], dsimp [(⋙),(𝟙)],
                unfold_projs, simp, } }

def pair {α β} (x : TVar α) (y : TVar β) : TVar (α × β) :=
(left_id (I Type)).inv ≫ (x ⊗ y)

infixr ` [⊗] `:11 := pair



end category_theory

instance : comonad stream.{u} :=
{ map := @stream.map,
  extract := λ α x, x.nth 0,
  extend := λ α β f x, x.tails'.map f,
  -- eq := λ α x y i, slift (x.nth i = y.nth i)
}

open stream

instance : is_lawful_comonad stream.{u} :=
begin
  refine { .. }; introv,
  repeat { ext, refl <|> dsimp [comonad.extend,comonad.extract] },
  { simp [nth_map,nth_tails',nth_drop] },
  { simp [nth_map,nth_tails',nth_drop,comonad.extend,comonad.extract,drop_zero], },
  { simp [nth_map,nth_tails',nth_drop,drop_map,drop_tails'], },
  { simp [(<$>),nth_drop,nth_map,nth_tails'], },
end
