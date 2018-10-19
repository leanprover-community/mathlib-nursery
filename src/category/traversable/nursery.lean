
import data.list.basic
import category.traversable.instances

universes u v

def foldl (α : Type u) (β : Type v) := α → α
def foldr (α : Type u) (β : Type v) := α → α

instance {α} : applicative (foldr α) :=
{ pure := λ _ _, id,
  seq := λ _ _ f x, f ∘ x }

instance {α} : applicative (foldl α) :=
{ pure := λ _ _, id,
  seq := λ _ _ f x, x ∘ f }

instance {α} : is_lawful_applicative (foldr α) :=
by refine { .. }; intros; refl

instance {α} : is_lawful_applicative (foldl α) :=
by refine { .. }; intros; refl

def foldr.eval {α β} (x : foldr α β) : α → α := x

def foldl.eval {α β} (x : foldl α β) : α → α := x

def foldl.cons {α β} (x : α) : foldl (list α) β :=
list.cons x

def foldr.cons {α β} (x : α) : foldr (list α) β :=
list.cons x

def foldl.cons' {α} (x : α) : foldl (list α) punit :=
list.cons x

def foldl.lift {α} (x : α → α) : foldl α punit := x
def foldr.lift {α} (x : α → α) : foldr α punit := x

namespace traversable

variables {t : Type u → Type u} [traversable t]

def to_list {α} (x : t α) : list α :=
(foldl.eval (traverse foldl.cons' x) []).reverse

def foldl {α β} (f : α → β → α) (x : α) (xs : t β) : α :=
foldl.eval (traverse (foldl.lift ∘ flip f) xs) x

def foldr {α β} (f : α → β → β) (x : β) (xs : t α) : β :=
foldr.eval (traverse (foldr.lift ∘ f) xs) x

open ulift

def length {α} (xs : t α) : ℕ :=
down $ foldl (λ l _, up $ 1+down l) (up 0) xs

lemma list_foldl_eq {α β} (f : α → β → α) (x : α) (xs : list β) :
  foldl f x xs = list.foldl f x xs :=
begin
  simp [foldl,foldl.eval,traverse,foldl.lift,(∘),flip,list.foldl],
  symmetry,
  induction xs generalizing x, refl,
  simp [list.traverse,list.foldl,xs_ih,(<*>),(<$>)],
end

lemma list_foldr_eq {α β} (f : α → β → β) (x : β) (xs : list α) :
  foldr f x xs = list.foldr f x xs :=
begin
  simp [foldr,foldr.eval,traverse,foldr.lift,(∘),flip,list.foldr],
  symmetry, induction xs, refl,
  simp [list.traverse,list.foldl,xs_ih,(<*>),(<$>)],
end

end traversable

open traversable

lemma list.to_list_eq_self {α} (xs : list α) :
  to_list xs = xs :=
begin
  simp [traversable.to_list,traverse,foldl.eval],
  suffices : ∀ s, (list.traverse foldl.cons' xs s).reverse = s.reverse ++ xs,
  { rw [this], simp },
  induction xs; intros s;
  simp [list.traverse,pure,(<*>),(<$>),foldl.cons',*],
end

lemma list.length_to_list {α} (xs : list α) :
  length (to_list xs) = xs.length :=
by { rw [length,list_foldl_eq,list.to_list_eq_self,← list.foldr_reverse,← list.length_reverse],
     generalize : list.reverse xs = l,
     induction l; simp *, }
#check @traverse
instance {α : Type u} : traversable (prod.{u u} α) :=
{ map := λ β γ f (x : α × β), prod.mk x.1 $ f x.2,
  traverse := λ m _ β γ f (x : α × β), by exactI prod.mk x.1 <$> f x.2 }
