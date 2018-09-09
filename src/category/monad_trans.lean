
import tactic

universes u v w

class is_lawful_monad_lift (m : Type u → Type v) (n : Type u → Type w) [has_monad_lift m n] [monad m] [monad n] :=
(monad_lift_pure : ∀ {α} (x : α),
  has_monad_lift.monad_lift (pure x : m α) = (pure x : n α))
(monad_lift_bind : ∀ {α β} (x : m α) (f : α → m β),
  (has_monad_lift.monad_lift $ x >>= f : n β) =
  has_monad_lift.monad_lift x >>= has_monad_lift.monad_lift ∘ f )

class is_lawful_monad_lift_t (m : Type u → Type v) (n : Type u → Type w) [has_monad_lift_t m n] [monad m] [monad n] :=
(monad_lift_pure : ∀ {α} (x : α),
  has_monad_lift_t.monad_lift (pure x : m α) = (pure x : n α))
(monad_lift_bind : ∀ {α β} (x : m α) (f : α → m β),
  (has_monad_lift_t.monad_lift $ x >>= f : n β) =
  has_monad_lift_t.monad_lift x >>= has_monad_lift_t.monad_lift ∘ f )

lemma is_lawful_monad_lift_t.monad_lift_and_then  (m : Type u → Type v) (n : Type u → Type w)
  [has_monad_lift_t m n] [monad m] [monad n] [is_lawful_monad_lift_t m n]
  {α β} (x : m α) (f : m β) :
  (has_monad_lift_t.monad_lift $ x >> f : n β) =
  has_monad_lift_t.monad_lift x >> has_monad_lift_t.monad_lift f :=
by { simp [(>>),is_lawful_monad_lift_t.monad_lift_bind n] }

export is_lawful_monad_lift_t (monad_lift_pure monad_lift_bind monad_lift_and_then)

instance has_lawful_monad_lift_t_trans (m n o) [monad m] [monad n] [monad o]
  [has_monad_lift n o] [has_monad_lift_t m n]
  [is_lawful_monad_lift n o] [is_lawful_monad_lift_t m n] : is_lawful_monad_lift_t m o :=
by constructor; intros; simp [monad_lift];
   [ simp [monad_lift_pure m n,is_lawful_monad_lift.monad_lift_pure n o],
     simp [monad_lift_bind n,is_lawful_monad_lift.monad_lift_bind o] ]

instance has_lawful_monad_lift_t_refl (m) [monad m] : is_lawful_monad_lift_t m m :=
by constructor; intros; simp [monad_lift]

class is_lawful_monad_state (σ : out_param (Type u)) (m : Type u → Type v) [monad m] [monad_state σ m] :=
(lift_pure : ∀ {α} (x : α),
  monad_state.lift (pure x : state σ α) = (pure x : m α))
(lift_bind  : ∀ {α β} (x : state σ α) (f : α → state σ β),
  (monad_state.lift $ x >>= f : m β) =
  monad_state.lift x >>= monad_state.lift ∘ f )
(lift_put : ∀ (x : σ),
  monad_state.lift (put x : state σ punit) = (put x : m punit))
(lift_get :
  monad_state.lift (get : state σ σ) = (get : m σ))
open is_lawful_monad_state

lemma is_lawful_monad_state.lift_and_then {m} [monad m] {α β σ} [monad_state σ m] [is_lawful_monad_state σ m] (x : state σ α) (f : state σ β) :
  (monad_state.lift $ x >> f : m β) =
  monad_state.lift x >> monad_state.lift f :=
by { simp [(>>),lift_bind m] }

instance (σ : (Type u)) (m : Type u → Type v) [monad m] [is_lawful_monad m] : is_lawful_monad_state σ (state_t σ m) :=
by { constructor; intros; try { refl },
     { simp [(>>=),state_t.bind,monad_state.lift,id_bind],
       congr, ext z, cases x.run z, refl }, }

instance (σ σ' : (Type u)) (m : Type u → Type v) [monad m] [is_lawful_monad m] [monad_state σ m] [is_lawful_monad_state σ m] :
  is_lawful_monad_state σ (reader_t σ' m) :=
by { constructor; intros; simp [monad_state.lift,lift_pure m,lift_bind m]; refl }

instance (σ : (Type u)) (m : Type u → Type v) [monad m] [is_lawful_monad m] : is_lawful_monad_lift m (state_t σ m) :=
by { constructor; intros; try { refl },
     all_goals
     { simp [(>>=),state_t.bind,state_t.lift,has_monad_lift.monad_lift,id_bind,bind_assoc]; refl }, }

instance (σ : (Type u)) (m : Type u → Type v) [monad m] : is_lawful_monad_lift m (reader_t σ m) :=
by { constructor; intros; refl }

-- class is_lawful_monad_reader (σ : out_param (Type u)) (m : Type u → Type v) [monad m] [monad_reader σ m] :=
-- (lift_pure {} : ∀ {α} (x : α),
--   monad_reader.lift (pure x : reader σ α) = (pure x : m α))
-- (lift_bind {} : ∀ {α β} (x : state σ α) (f : α → state σ β),
--   (monad_state.lift $ x >>= f : m β) =
--   monad_state.lift x >>= monad_state.lift ∘ f )

-- instance (σ : (Type u)) (m : Type u → Type v) [monad m] [is_lawful_monad m] : is_lawful_monad_state σ (state_t σ m) :=
-- by { constructor; intros,
--      { refl },
--      { simp [(>>=),state_t.bind,monad_state.lift,id_bind],
--        congr, ext z, cases x.run z, refl } }

-- class is_lawful_monad_state
