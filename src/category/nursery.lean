
import tactic
import control.functor
import control.applicative

universes u v

namespace monad

@[simp]
lemma bind_pure_star {m} [monad m] [is_lawful_monad m] (x : m punit) :
  x >>= (λ (_x : punit), pure punit.star : punit → m punit) = x :=
by { transitivity,
     { apply congr_arg, ext z, cases z, refl },
     { simp } }

variables {α β γ : Type u}
variables {m : Type u → Type v} [monad m]

@[reducible]
def pipe (a : α → m β) (b : β → m γ) : α → m γ :=
λ x, a x >>= b

infixr ` >=> `:55 := pipe

@[functor_norm]
lemma map_bind_eq_bind_comp {α β γ} {m} [monad m] [is_lawful_monad m]
  (f : α → β) (cmd : m α) (g : β → m γ) :
  (f <$> cmd) >>= g = cmd >>= g ∘ f :=
by rw [← bind_pure_comp_eq_map,bind_assoc,(∘)]; simp

@[functor_norm]
lemma bind_map {α β γ} {m} [monad m] [is_lawful_monad m]
  (f : α → γ → β) (cmd : m α) (g : α → m γ) :
  cmd >>= (λ x, f x <$> g x) = do { x ← cmd, y ← g x, pure $ f x y }  :=
by congr; ext; rw [← bind_pure (g x),map_bind]; simp

@[functor_norm]
lemma bind_seq {α β γ : Type u} {m} [monad m] [is_lawful_monad m]
  (f : α → m (γ → β)) (cmd : m α) (g : α → m γ) :
  cmd >>= (λ x, f x <*> g x) = do { x ← cmd, h ← f x, y ← g x, pure $ h y }  :=
by congr; ext; simp [seq_eq_bind_map] with functor_norm

end monad

attribute [functor_norm] bind_assoc has_bind.and_then map_bind seq_left_eq seq_right_eq

namespace sum

variables {e : Type v} {α β : Type u}

protected def seq : Π (x : sum e (α → β)) (f : sum e α), sum e β
| (sum.inl e) _ := sum.inl e
| (sum.inr f) x := f <$> x

instance : applicative (sum e) :=
{ seq := @sum.seq e,
  pure := @sum.inr e }

instance : is_lawful_applicative (sum e) :=
by constructor; intros;
   casesm* _ ⊕ _; simp [(<*>),sum.seq,pure,(<$>)];
   refl

end sum
