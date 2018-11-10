
import category.comonad
import category_theory.category
import data.stream
import data.stream.basic
import tactic

universes u

inductive slift (p : Prop) : Sort.{u}
| up (down : p) : slift

namespace stream

variables {α : Type u}

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

lemma drop_zero {α} (x : stream α) : drop 0 x = x := rfl

end stream

namespace category_theory

def TVar := Type u

instance TVar.category : category TVar.{u} :=
{ hom := λ α β, stream α → stream β,
  id := λ α, @id (stream α),
  comp := λ α β γ f g, g ∘ f }

end category_theory

instance : comonad stream.{u} :=
{ map := @stream.map,
  extract := λ α x, x.nth 0,
  extend := λ α β f x, x.tails'.map f,
  eq := λ α x y i, slift (x.nth i = y.nth i) }

open stream

instance : is_lawful_comonad stream.{u} :=
begin
  -- constructor,
  refine { .. }; introv,
  repeat { ext, refl <|> dsimp [comonad.extend,comonad.extract] },
  { simp [nth_map,nth_tails',nth_drop] },
  { simp [nth_map,nth_tails',nth_drop,comonad.extend,comonad.extract,drop_zero], },
  { simp [nth_map,nth_tails',nth_drop,drop_map,drop_tails'], },
  { simp [(<$>),nth_drop,nth_map,nth_tails'], },
  -- { constructor, constructor, refl },
  { intro h, ext,
    replace h := h.nth n, }
end
