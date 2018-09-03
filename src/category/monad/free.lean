
import category.positive
import data.coinductive.tactic
import data.coinductive.eq

universes u v w

open functor positive (hiding map_eqv_rep_map)

/-- coinductive free F α :=
    | pure : α → free
    | step : f free → free
-/
def free (f : Type u → Type u) [positive f] (α : Type u) :=
cofix' (comp.{u u u} (sum α) f)

namespace free

variables {F : Type u → Type u} [positive F]

#check @cofix.corec
open functor
protected def pure {α} (x : α) : free F α :=
cofix.fold (comp.mk (sum.inl x))

def step {α} (x : F (free F α)) : free F α :=
cofix.fold (sum.inr x)

lemma child_t_pure {α} (x : α) :
  child_t (cofix.head (free.pure x : free F α)) → empty :=
by { dsimp [child_t,comp.child_t],
     generalize h : (cofix.head (free.pure x)) = k,
     simp [free.pure,cofix.fold,cofix.corec',map_eqv_rep_map] at h,
     admit }

coinductive eq {α} : free F α → free F α → Prop
| pure (x : α) : eq (free.pure x) (free.pure x)
| step (x y : F (free F α)) :
  head x = head y →
  (∀ i j, i == j → eq (child x i) (child y j)) →
  eq (step x) (step y)

lemma free_bisim {α} : cofix.is_bisimulation (@eq F _ α) :=
begin
  -- coinduction eq,
  dsimp [cofix.is_bisimulation], intros,
  apply free.eq.cases_on a,
  { intros, split, refl,
    intros, dsimp [child_t,sum.child_t,comp.child_t,free.pure,sum.child_t,cofix.roll,cofix.corec'] at i j,
    cases i, admit },
  admit
end

protected def bind_aux {α β} (g : α → free F β) : free F α ⊕ free F β → β ⊕ F (free F α ⊕ free F β)
| (sum.inl x) :=
match cofix.unfold x with
 | (sum.inl x) := map sum.inr <$> @id (β ⊕ F (free F β)) (cofix.unfold (g x))
 | (sum.inr x) := sum.inr (sum.inl <$> x)
end
| (sum.inr x) :=
match cofix.unfold x with
 | (sum.inl x) := sum.inl x
 | (sum.inr x) := sum.inr $ sum.inr <$> x
end

protected def bind {α β} (x : free F α) (g : α → free F β) : free F β :=
cofix.corec₀
  (free.bind_aux g)
  (@sum.inl _ (free F β) x)

instance : monad (free F) :=
{ pure := @free.pure F _,
  bind := @free.bind F _ }

-- instance : is_lawful_monad (free F) :=
-- begin
--   refine { .. }; intros,

-- end

end free
