
import category.positive
import data.coinductive.tactic
import data.coinductive.eq
import category.traversable.derive

universes u v

codata proxy_t (i i' o o' α : Type u)
| pure {} : α → proxy_t
| write {} : o' → (o → proxy_t) → proxy_t
| read {} : i → (i' → proxy_t) → proxy_t

variables {i i' o o' α : Type u}

open positive cofix (unfold fold)

-- generate
def write.idx {x : o'} : proxy_t.child_t i i' o o' α (proxy_t.head_t.write x) → o :=
proxy_t.child_t.rec.write _ _ _ _ _ _ id

-- generate
def read.idx {x : i} : proxy_t.child_t i i' o o' α (proxy_t.head_t.read x) → i' :=
proxy_t.child_t.rec.read _ _ _ _ _ _ id

-- @[simp]
-- lemma p'' (a : α) (f : proxy_t.child_t i i' o o' α (proxy_t.head_t.pure i i' o o' α a) → cofix (proxy_t.child_t i i' o o' α)) :
--   proxy_t.child_t.rec.pure i i' o o' α a _ = f :=
-- by { admit }

-- @[simp]
-- lemma p (a : o') (f : proxy_t.child_t i i' o o' α (proxy_t.head_t.write i i' o o' α a) → cofix (proxy_t.child_t i i' o o' α)) :
--   proxy_t.child_t.rec.write i i' o o' α a (f ∘ proxy_t.child_t.write_0 i i' o o' α a) = f :=
-- by { admit }

-- @[simp]
-- lemma p' (a : i) (f : proxy_t.child_t i i' o o' α (proxy_t.head_t.read i i' o o' α a) → cofix (proxy_t.child_t i i' o o' α)) :
--   proxy_t.child_t.rec.read i i' o o' α a (f ∘ proxy_t.child_t.read_0 i i' o o' α a) = f :=
-- by { admit }

-- lemma d'' (a : α)  :
--   roll (proxy_t.f.pure a) =
--   cofix.mk (proxy_t.head_t.pure i i' o o' _ a) (proxy_t.child_t.rec.pure _ _ _ _ _ _) := sorry

-- lemma d (a : i) (f : i' → proxy_t i i' o o' α) :
--   roll (proxy_t.f.read a f) =
--   cofix.mk (proxy_t.head_t.read _ _ _ _ _ a) (proxy_t.child_t.rec.read _ _ _ _ _ _ f) := sorry

-- lemma d' (a : o') (f : o → proxy_t i i' o o' α) :
--   roll (proxy_t.f.write a f) =
--   cofix.mk (proxy_t.head_t.write _ _ _ _ _ a) (proxy_t.child_t.rec.write _ _ _ _ _ _ f) := sorry

-- lemma q'' (a : α)
--   (f : proxy_t.child_t i i' o o' α (proxy_t.head_t.pure i i' o o' α a) → cofix (proxy_t.child_t i i' o o' α)) :
--   cofix.mk (proxy_t.head_t.pure i i' o o' _ a) f =
--   fold (proxy_t.F.pure _ _ _ _ _ _ a) := sorry

-- lemma q (a : i)
--   (f : proxy_t.child_t i i' o o' α (proxy_t.head_t.read i i' o o' α a) → proxy_t i i' o o' α) :
--   cofix.mk (proxy_t.head_t.read _ _ _ _ _ a) f =
--   fold (proxy_t.F.read a $ f ∘ proxy_t.child_t.read_0 _ _ _ _ _ _ ) := sorry

-- lemma q' (a : o')
--   (f : proxy_t.child_t i i' o o' α (proxy_t.head_t.write i i' o o' α a) → proxy_t i i' o o' α) :
--   cofix.mk (proxy_t.head_t.write _ _ _ _ _ a) f =
--   fold (proxy_t.F.write a $ f ∘ proxy_t.child_t.write_0 _ _ _ _ _ _) := sorry

def X := empty

abbreviation pipe (i o) := proxy_t unit i unit o
abbreviation producer (o) := proxy_t X unit unit o
abbreviation consumer (i) := proxy_t unit i unit X
abbreviation effect := proxy_t X unit unit X

namespace proxy_t

-- generate

-- -- generate
-- lemma children_write (x : o') (g : o → proxy_t i i' o o' α)
--   (i_1 : positive.child_t (head_t.write i i' o o' α x : positive.head_t (proxy_t.F i i' o o' α))) :
--   cofix.children (write x g) i_1 = g (write.idx i_1) :=
-- by { dsimp [write,fold,to_rep], simp,
--      apply cofix.coinduction,
--      { simp [rep.map], dsimp [rep.map], admit,  },
--    admit,
--    -- dsimp [rep.map], refine child_t.cases_on i_1 _ _ ,
--    }

-- -- generate
-- lemma children_read (x : i) (g : i' → proxy_t i i' o o' α)
--   (i_1 : child_t i i' o o' α (head_t.read i i' o o' α x)) :
--   cofix.children (read x g) i_1 = g (read.idx i_1) :=
-- by { dsimp [read,fold,to_rep], simp,
--      apply cofix.coinduction,
--      { simp [rep.map], dsimp [rep.map], admit },
--    -- dsimp [rep.map], refine child_t.cases_on i_1 _ _ ,
--    admit, }

-- generate
-- lemma bisim_sound : cofix.is_bisimulation (@bisim i i' o o' α) :=
-- begin
--   dsimp [cofix.is_bisimulation], intros,
--   apply bisim.cases_on a; intros; split; try { refl }; introv,
--   all_goals { admit }
--   -- { simp [cofix.head,pure,fold,to_rep,rep.map] at j,
--   --   apply child_t.rec.pure i i' o o' _ _ j, },
--   -- { simp [cofix.head,write,fold,to_rep,rep.map] at j i_1,
--   --   rintro ⟨ ⟩ ,
--   --   apply child_t.rec.write i i' o o' _ _ _ i_1,
--   --   intros, rw [children_write,children_write],
--   --   apply a_1, },
--   -- { simp [cofix.head,read,fold,to_rep,rep.map] at j i_1,
--   --   rintro ⟨ ⟩ ,
--   --   apply child_t.rec.read i i' o o' _ _ _ i_1,
--   --   intros, rw [children_read,children_read], apply a_1 }
-- end
-- def breakup {α x} : proxy_t.f i i' o o' α x ≃ (Σ a : proxy_t.head_t i i' o o' α, proxy_t.child_t i i' o o' α a → x)

-- protected def corec : Π {α β}, (Π x (f : α → x), α → proxy_t.f i i' o o' β x) → α → proxy_t i i' o o' β
open proxy_t.F

#check @proxy_t.cases_on
#check proxy_t.F
#check i'
protected def proxy_t.corec' {β}
  (f₀ : Π X, (proxy_t i i' o o' α → X) →
    α → cofix' (F i i' o o' β) ⊕ proxy_t.F i i' o o' β X)
  (f₁ : Π X, (proxy_t i i' o o' α → X) →
    o' → (o → proxy_t i i' o o' α) →
    cofix' (F i i' o o' β) ⊕ F i i' o o' β X)
  (f₂ : Π X, (proxy_t i i' o o' α → X) →
    i → (i' → proxy_t i i' o o' α) →
    cofix' (F i i' o o' β) ⊕ F i i' o o' β X)
  : proxy_t i i' o o' α → proxy_t i i' o o' β :=
cofix.corec' $ λ X rec,
proxy_t.cases (f₀ X rec) (f₁ X rec) (f₂ X rec)

protected def bind {α β : Type u} (a : proxy_t i i' o o' α) (f : α → proxy_t i i' o o' β) : proxy_t i i' o o' β :=
proxy_t.corec'
(λ X bind a, sum.inl $ f a)
(λ X bind a b, sum.inr $ F.write a $ λ i, bind $ b i)
(λ X bind a b, sum.inr $ F.read a $ λ i, bind $ b i)
a

instance : monad (proxy_t i i' o o') :=
{ bind := @proxy_t.bind i i' o o',
  pure := @proxy_t.pure i i' o o' }

-- generate from bind def
@[simp]
protected lemma bind_eqn_1  {α β} (a : α) (f : α → proxy_t i i' o o' β) :
  pure a >>= f = f a :=
begin
  admit
end

@[simp]
protected lemma bind_eqn_2  {α β}
  (a : o') (f : o → proxy_t i i' o o' α)
  (g : α → proxy_t i i' o o' β) :
  write a f >>= g = write a (λ x, f x >>= g) := sorry

@[simp]
protected lemma bind_eqn_3  {α β}
  (a : i) (f : i' → proxy_t i i' o o' α)
  (g : α → proxy_t i i' o o' β) :
  read a f >>= g = read a (λ x, f x >>= g) := sorry

lemma bind_pure {α}
  (a : proxy_t i i' o o' α) :
  a >>= pure = a :=
begin
  bisimulation generalizing a,
  apply proxy_t.cases_on w; intros; simp,
  { right, right, left,
    existsi [a,(λ (x : o), a_1 x >>= pure),a_1],
    split, intro, refl, split; refl },
  { right, right, right, splita,
    existsi [(λ (x : i'), a_1 x >>= pure),a_1],
    split, intro, refl, split; refl }
end

lemma bind_assoc {α β γ}
  (a : proxy_t i i' o o' α) (f : α → proxy_t i i' o o' β) (g : β → proxy_t i i' o o' γ) :
  a >>= f >>= g = a >>= λ x, f x >>= g :=
begin
  bisimulation generalizing a,
  apply proxy_t.cases_on w; intros; simp,
  { right, right, left, splita,
    existsi (λ (x : o), a_1 x >>= f >>= g),
    existsi (λ (x : o), a_1 x >>= λ (x : α), f x >>= g),
    split, intro, split,
    repeat { split <|> refl } },
  { right, right, right,
    splita, existsi (λ (x : i'), a_1 x >>= f >>= g),
    existsi (λ (x : i'), a_1 x >>= λ (x : α), f x >>= g),
    split, intro, split, split; refl,
    split; refl, },
end

instance : is_lawful_monad (proxy_t i i' o o') :=
{ bind_assoc := @bind_assoc _ _ _ _,
  pure_bind  := by { intros, simp [has_pure.pure] },
  id_map := @bind_pure _ _ _ _ }

-- #check cofix.eq_of_bisim
-- #print prefix proxy_t.bisim
-- def proxy_t.bind : Π {α β}, proxy_t w α → (α → proxy_t w β) → proxy_t w β
-- | _ _ (proxy_t.fail) _ := proxy_t.fail
-- | _ _ (proxy_t.pure x)   f := f x
-- | _ _ (proxy_t.read f) g := proxy_t.read $ λ w, proxy_t.bind (f w) g
-- | _ _ (proxy_t.loop f g x₀) h := proxy_t.loop f (λ r, proxy_t.bind (g r) h) x₀

-- def proxy_t.map : Π {α β : Type u}, (α → β) → proxy_t w α → proxy_t w β
-- | _ _ _ (proxy_t.fail) := proxy_t.fail
-- | _ _ f (proxy_t.pure x) := proxy_t.pure $ f x
-- | _ _ f (proxy_t.read g) := proxy_t.read $ λ w, proxy_t.map f (g w)
-- | _ _ h (proxy_t.loop f g x₀) := proxy_t.loop f (λ r, proxy_t.map h (g r)) x₀

-- @[simp]
-- def proxy_t.loop.rest {α β γ : Type u} (f : β → w → proxy_t w (α ⊕ β)) (g : α → proxy_t w γ) : α ⊕ β → proxy_t w γ
-- | (sum.inr x) := proxy_t.loop f g x
-- | (sum.inl x) := g x

-- instance proxy_t.functor : functor.{u} (proxy_t w) :=
-- { map := @proxy_t.map _ }

-- def proxy_t.seq {α β : Type u} : Π (f : proxy_t w (α → β)) (x : proxy_t w α), proxy_t w β :=
-- λ (f : proxy_t w (α → β)) (x : proxy_t w α), proxy_t.bind f (λ f, f <$> x)

-- -- instance : applicative proxy_t :=
-- -- { to_functor := proxy_t.functor
-- -- , pure := λ α, proxy_t.pure
-- -- , seq := @proxy_t.seq }
-- open function

-- instance : is_lawful_functor.{u} (proxy_t w) :=
-- by { constructor; intros;
--      dsimp [(<$>),proxy_t.seq];
--      induction x;
--      try { refl };
--      simp [proxy_t.map,*]; ext }

-- instance : monad (proxy_t w) :=
-- { to_functor := proxy_t.functor
-- , pure := @proxy_t.pure w
-- , bind := @proxy_t.bind w }

-- instance : is_lawful_monad.{u} (proxy_t w) :=
-- { to_is_lawful_functor := by apply_instance,
--   bind_assoc := by { intros, dsimp [(>>=)],
--                      induction x; try { refl }; simp [proxy_t.bind,*], },
--   bind_pure_comp_eq_map := by { intros, dsimp [(>>=),(<$>)],
--                                 induction x; try {refl}; simp [proxy_t.bind,proxy_t.map,*], },
--   map_pure := by intros; refl,
--   pure_seq_eq_map := by { intros, dsimp [(>>=),(<$>)],
--                           induction x; try {refl}; simp [proxy_t.bind,proxy_t.map,*], },
--   pure_bind := by intros; refl }

-- def proxy_t.or_else {α} : proxy_t w α → proxy_t w α → proxy_t w α
-- | proxy_t.fail x := x
-- | x y := x

-- instance : alternative.{u} (proxy_t w) :=
-- { failure := @proxy_t.fail _,
--   orelse := @proxy_t.or_else _ }

-- def proxy_t.eval : Π {α}, list w → proxy_t w α → option α
-- | _ [] (proxy_t.pure x) := pure x
-- | _ [] _  := none
-- | α (w :: ws) (proxy_t.read f) := proxy_t.eval ws (f w)
-- | α (ww :: ws) (proxy_t.loop f g x₀) :=
--   proxy_t.eval ws $
--   f x₀ ww >>= proxy_t.loop.rest f g
-- | α (w :: ws) _ := none

-- def write_word (x : w) : put_m'.{u} w punit :=
-- put_m'.write x (λ _, put_m'.pure punit.star)

-- def read_word : proxy_t.{u} w (ulift w) :=
-- proxy_t.read (proxy_t.pure ∘ ulift.up)

-- open ulift

-- def expect_word [decidable_eq w] (x : w) : proxy_t.{u} w punit :=
-- do w' ← read_word,
--    if x = down w' then pure punit.star
--                   else failure

-- def read_write : Π {α : Type u}, proxy_t w α → put_m'.{u} w punit → option α
-- | ._ (proxy_t.pure x) (put_m'.pure _) := some x
-- | _ _ (put_m'.pure _) := none
-- | ._ (proxy_t.read f) (put_m'.write w g) := read_write (f w) (g punit.star)
-- | α (@proxy_t.loop _ α' β γ f g x₀) (put_m'.write ww h) :=
--   read_write
--     (f x₀ ww >>= proxy_t.loop.rest f g)
--     (h punit.star)
-- | _ _ (put_m'.write w g) := none

-- def read_write' : Π {α : Type u}, proxy_t w α → put_m'.{u} w punit → option (α × put_m'.{u} w punit)
-- | _ (proxy_t.read f) (put_m'.write w g) := read_write' (f w) (g punit.star)
-- | α (@proxy_t.loop _ α' β γ f g x₀) (put_m'.write ww h) :=
--   read_write'
--     (f x₀ ww >>= proxy_t.loop.rest f g)
--     (h punit.star)
-- -- | _ (proxy_t.pure x) m@(put_m'.write w g) := some (x,m)
-- | _ (proxy_t.pure x) m := some (x,m)
-- | _ _ (put_m'.pure _) := none
-- | _ (proxy_t.fail) (put_m'.write _ _) := none
-- -- | _ _ m := none

-- lemma read_read_write_write {α : Type u} (x : proxy_t w α) (m : put_m w) (i : α) :
--   read_write x m = some i ↔ read_write' x m = some (i,(pure punit.star : put_m' w _)) :=
-- begin
--   induction m generalizing x;
--   cases x; casesm* punit; simp [read_write,read_write',prod.ext_iff,pure,*],
-- end

-- def pipeline {α} (x : proxy_t w α) (y : α → put_m w) (i : α) : option α :=
-- read_write x (y i)

-- infix ` -<< `:60  := read_write
-- infix ` -<<< `:60  := read_write'
-- infix ` <-< `:60  := pipeline

-- lemma eq_star (x : punit) : x = punit.star :=
-- by cases x; refl

-- -- inductive agree : Π {α} (x : α), proxy_t α → put_m → put_m → Prop
-- -- | pure {α} (x : α) (m : put_m) : agree x (proxy_t.pure x) m m
-- -- | read_write {α} (x : α) (w : unsigned)
-- --   (f : unsigned → proxy_t α) (g : punit → put_m) (m : put_m) :
-- --   agree x (f w) (g punit.star) m →
-- --   agree x (proxy_t.read f) (put_m'.write w g) m
-- -- | loop_write {α} (x : α) {β γ} (σ₀ σ₁ : β) (w : unsigned)
-- --   (f : β → unsigned → proxy_t (γ ⊕ β)) (f' : γ → proxy_t α)
-- --   (g : punit → put_m) (m m' : put_m) :
-- --   agree (sum.inr σ₁) (f σ₀ w) (g punit.star) m' →
-- --   agree x (proxy_t.loop σ₁ f f') m' m →
-- --   agree x (proxy_t.loop σ₀ f f') (put_m'.write w g) m
-- -- | loop_exit_write {α} (x : α) {β γ} (σ₀ : β) (r : γ) (w : unsigned)
-- --   (f : β → unsigned → proxy_t (γ ⊕ β)) (f' : γ → proxy_t α)
-- --   (g : punit → put_m) (m m' : put_m) :
-- --   agree (sum.inl r) (f σ₀ w) (g punit.star) m' →
-- --   agree x (f' r) m' m →
-- --   agree x (proxy_t.loop σ₀ f f') (put_m'.write w g) m

-- -- lemma agree_spec {α} (g : proxy_t α) (m : put_m) (x : α) :
-- --   agree x g m (put_m'.pure punit.star) ↔ g -<< m = some x :=
-- -- begin
-- --   split; intro h,
-- --   { cases h,
-- --     refl, simp [read_write], }
-- -- end

-- -- lemma loop_bind {α β γ} (i : β)
-- --       (body : β → unsigned → proxy_t (α ⊕ β)) (f₀ : α → proxy_t γ) :
-- --   proxy_t.loop i body f₀ = proxy_t.read (body i) >>= _ := _

-- lemma read_write_loop_bind {α β γ φ : Type u} (i : α)
--       (body : α → w → proxy_t w (φ ⊕ α))
--       (f₀ : φ → proxy_t w β) (f₁ : β → proxy_t w γ)
--       (m : punit → put_m w) (ww : w) :
--   (proxy_t.loop body f₀ i >>= f₁) -<<< put_m'.write ww m =
--   (body i ww >>= proxy_t.loop.rest body f₀ >>= f₁) -<<< m punit.star :=
-- begin
--   rw bind_assoc,
--   simp [(>>=),proxy_t.bind,read_write'],
--   congr, ext, cases x; simp; refl,
-- end

-- -- lemma read_write_left_overs_bind {α} (i : α)
-- --       (x₀ : proxy_t α)
-- --       (x₁ x₂ : put_m) :
-- -- x₀ -<<< x₁ = some (i,x₂) →

-- lemma fail_read_write {α} (x₁ : put_m w) :
--   proxy_t.fail -<<< x₁ = @none (α × put_m w) :=
-- by cases x₁; refl

-- lemma pure_read_write {α} (x₁ : put_m w) (i : α) :
--   proxy_t.pure i -<<< x₁ = some (i, x₁) :=
-- by cases x₁; refl

-- lemma read_write_left_overs_bind {α} (f : punit → put_m' w punit) (i : α)
--       (x₀ : proxy_t w α)
--       (x₁ x₂ : put_m' w punit) :
--   x₀ -<<< x₁ = some (i,x₂) → x₀ -<<< (x₁ >>= f) = some (i,x₂ >>= f) :=
-- begin
--   induction x₁ generalizing x₀ x₂,
--   cases x₀; simp [(>>=),put_m'.bind,read_write',pure_read_write],
--   { intros, subst x₂, tauto },
--   cases x₀; simp [(>>=),put_m'.bind,read_write'],
--   { intros, substs x₂ i, split; refl },
--   { apply x₁_ih, },
--   { apply x₁_ih, },
-- end

-- lemma option_eq_forall_some {α} (x y : option α) :
--   x = y ↔ ∀ z, x = some z ↔ y = some z :=
-- begin
--   split; intro h, { rw h; intro, refl },
--   { cases y, cases x, refl,
--     symmetry, rw ← h, rw h, },
-- end

-- lemma read_write_weakening {α : Type u}
--   (x₀ x₁ : put_m w) (y₀ y₁ : proxy_t w α)
--   (h : y₀ -<<< x₀ = y₁ -<<< x₁) :
--   y₀ -<< x₀ = y₁ -<< x₁ :=
-- begin
--   rw option_eq_forall_some,
--   intro, simp [read_read_write_write,h],
-- end

-- lemma read_write_mono' {α β : Type u} (i : α)
--       (x₀ : proxy_t w α) (f₀ : α → proxy_t w β)
--       (x₁ x₂ : put_m w)
--       (h : x₀ -<<< x₁ = some (i,x₂)) :
--   (x₀ >>= f₀) -<<< x₁ = f₀ i -<<< x₂ :=
-- begin
--   -- simp [(>>=)],
--   induction x₁ generalizing x₀ f₀;
--     try { cases x₀; cases h },
--   { simp [(>>=),read_write',proxy_t.bind] },
--   { cases x₀; try { cases h },
--     simp [(>>=),read_write',proxy_t.bind] at h ⊢,
--     simp [(>>=),read_write',proxy_t.bind] at h ⊢,
--     { apply x₁_ih, assumption },
--     simp [read_write_loop_bind,x₁_ih],
--     rw [x₁_ih _ _ _ h], }
-- end

-- lemma read_write_mono {α β : Type u} {i : α}
--       {x₀ : proxy_t w α} {f₀ : α → proxy_t w β}
--       {x₁ : put_m w} {f₁ : punit → put_m w}
--       (h : x₀ -<< x₁ = some i) :
--   (x₀ >>= f₀) -<< (x₁ >>= f₁) = f₀ i -<< f₁ punit.star :=
-- begin
--   apply read_write_weakening,
--   apply read_write_mono',
--   rw [read_read_write_write] at h,
--   replace h := read_write_left_overs_bind f₁ _ _ _ _ h,
--   simp [h],
-- end

-- lemma read_write_mono_left {α β} {i : α}
--       {x₀ : proxy_t w α} {f₀ : α → proxy_t w β}
--       {x₁ : put_m w}
--       (h : x₀ -<< x₁ = some i) :
--   (x₀ >>= f₀) -<< x₁ = f₀ i -<< pure punit.star :=
-- by rw ← read_write_mono h; simp

-- @[simp]
-- lemma read_write_word {α} (x : w) (f : ulift w → proxy_t w α) (f' : punit → put_m w) :
--   (read_word >>= f) -<< (write_word x >>= f') = f ⟨x⟩ -<< f' punit.star := rfl

-- @[simp]
-- lemma read_write_word' {α} (x : w) (f : ulift w → proxy_t w α) (f' : put_m w) :
--   (read_word >>= f) -<< (write_word x >> f') = f ⟨x⟩ -<< f' := rfl

-- @[simp]
-- lemma read_write_word'' {α} (x : w) (f : ulift w → proxy_t w α) :
--   (read_word >>= f) -<< write_word x = f ⟨x⟩ -<< pure punit.star := rfl

-- @[simp]
-- lemma read_write_pure {α} (x : α) (y : punit) (f : ulift w → proxy_t w α) :
--   (pure x : proxy_t w α) -<< pure y = pure x := rfl

-- @[simp]
-- lemma read_write_loop_word {α β γ : Type u} (σ₀ : α) (x : w)
--   (f : α → w → proxy_t w (β ⊕ α)) (g : β → proxy_t w γ)
--   (f' : punit → put_m w) :
--   proxy_t.loop f g σ₀ -<< (write_word x >>= f') =
--   (f σ₀ x >>= proxy_t.loop.rest f g)
--     -<< f' punit.star := rfl

-- #check @read_write_loop_word

-- lemma eval_eval {α}
--       (x₀ : proxy_t w α) (x₁ : put_m w)  :
--   x₀.eval x₁.eval = x₀ -<< x₁ :=
-- by induction x₁ generalizing x₀; cases x₀;
--      simp! [*,read_write]; refl

-- open ulift

-- lemma proxy_t.fold_bind {α β} (x : proxy_t w α) (f : α → proxy_t w β) :
--   proxy_t.bind x f = x >>= f := rfl

-- lemma map_read_write {α β} (f : α → β) (x : proxy_t w α) (y : put_m w) :
--   (f <$> x) -<< y = f <$> (x -<< y) :=
-- begin
--   rw [← bind_pure_comp_eq_map,← bind_pure_comp_eq_map],
--   symmetry,
--   simp [(>>=)],
--   induction y generalizing x,
--   { cases x; refl },
--   { cases x; simp [read_write]; try { refl };
--     simp [proxy_t.bind,read_write,y_ih],
--     congr' 1, cases h : x_a x_a_2 y_a, refl,
--     cases a; refl,
--     dsimp [(>>=),proxy_t.bind],
--     congr, ext, simp [proxy_t.fold_bind],
--     rw bind_assoc, congr, ext z, cases z; refl,
--     simp [proxy_t.fold_bind], rw bind_assoc, congr, ext x,
--     cases x; refl, }
-- end

-- def sum_ulift (α β : Type u) : (α ⊕ β) ≃ (ulift.{v} α ⊕ ulift.{v} β) :=
-- (equiv.sum_congr equiv.ulift.symm equiv.ulift.symm)

-- -- def proxy_t.up : Π {α : Type u} {β : Type.{max u v}} (Heq : α ≃ β), proxy_t α → proxy_t β
-- -- | _ _ Heq (proxy_t.pure x) := proxy_t.pure $ Heq x
-- -- | _ _ Heq (proxy_t.fail) := proxy_t.fail
-- -- | _ _ Heq (proxy_t.read f) := proxy_t.read (λ w, proxy_t.up Heq (f w))
-- -- | _ β' Heq (@proxy_t.loop α β γ f g x) :=
-- --   proxy_t.loop
-- --     (λ a b, proxy_t.up (sum_ulift α β) (f (down.{v} a) b))
-- --     (λ w, proxy_t.up Heq (g $ down w))
-- --     (up.{v} x)

-- def proxy_t.up : Π {α : Type u} {β : Type.{max u v}} (Heq : α → β), proxy_t w α → proxy_t w β :=
-- λ α β f x, (@proxy_t.rec_on _ (λ α _, Π β, (α → β) → proxy_t w β) α x
-- (λ α β f, proxy_t.fail)
-- (λ α x β f, proxy_t.pure $ f x)
-- (λ α next proxy_t_up β f, proxy_t.read $ λ w, proxy_t_up w _ f)
-- (λ α β γ body rest x₀ proxy_t_up₀ proxy_t_up₁ β' f,
--   proxy_t.loop
--     (λ a b, proxy_t_up₀ (down a) b (ulift.{v} α ⊕ ulift.{v} β)
--                      (sum_ulift α β))
--     (λ r, proxy_t_up₁ (down r) _ f)
--     (up x₀)) β f)

-- section eqns

-- variables {α β' γ : Type u} {β : Type.{max u v}} (Heq : α → β) (x : proxy_t w α)

-- variables {i : α} {f : w → proxy_t w α}
-- variables {f' : β' → w → proxy_t w (γ ⊕ β')}
-- variables {g' : γ → proxy_t w α} {j : β'}

-- @[simp] lemma proxy_t.up.eqn_1 : proxy_t.up Heq (proxy_t.pure i : proxy_t w _) = proxy_t.pure (Heq i) := rfl
-- @[simp] lemma proxy_t.up.eqn_2 : proxy_t.up Heq (proxy_t.fail : proxy_t w α) = proxy_t.fail := rfl
-- @[simp] lemma proxy_t.up.eqn_3 : proxy_t.up Heq (proxy_t.read f) = proxy_t.read (λ w, proxy_t.up Heq (f w)) := rfl
-- @[simp] lemma proxy_t.up.eqn_4 :
--   proxy_t.up Heq (proxy_t.loop f' g' j) =
--   proxy_t.loop
--     (λ a b, proxy_t.up (sum_ulift γ β') (f' (down.{v} a) b))
--     (λ w, proxy_t.up Heq (g' $ down w))
--     (up.{v} j) := rfl

-- end eqns

-- def put_m.up {α : Type u} {β : Type v} (Heq : α → β) : put_m' w α → put_m' w β
-- | (put_m'.pure x) := put_m'.pure $ Heq x
-- | (put_m'.write w f) := put_m'.write w $ λ u, put_m.up $ f u

-- instance : liftable1 (put_m'.{u} w) (put_m'.{v} w) :=
-- { up := λ α β (eq : α ≃ β) x, put_m.up eq x
-- , down := λ α β (eq : α ≃ β) x, put_m.up eq.symm x
-- , down_up := by intros; induction x; simp [put_m.up,*]
-- , up_down := by intros; induction x; simp [put_m.up,*]  }

-- open pliftable (up')

-- lemma up_bind {α β : Type u} {β' : Type (max u v)} (x : proxy_t w α) (g : α → proxy_t w β) (f : β → β') :
--   (x >>= g).up f = x.up up.{v} >>= (λ i : ulift α, (g $ down i).up f) :=
-- begin
--   dsimp [(>>=)],
--   induction x generalizing f g; try { refl };
--     simp [proxy_t.bind,*]
-- end

-- lemma equiv_bind {m} [monad m] [is_lawful_monad m] {α α' β}
--   (Heq : α ≃ α') (x : m α) (f : α → m β) :
--   x >>= f = (Heq <$> x) >>= f ∘ Heq.symm :=
-- by simp [(∘)] with functor_norm

-- def sum.map {α α' β β'} (f : α → α') (g : β → β') : α ⊕ β → α' ⊕ β'
-- | (sum.inr x) := sum.inr $ g x
-- | (sum.inl x) := sum.inl $ f x

-- def equiv.ulift_sum {α β} : (ulift $ α ⊕ β) ≃ (ulift α ⊕ ulift β) :=
-- { to_fun := λ x, sum.map up up (down x),
--   inv_fun := λ x, up $ sum.map down down x,
--   right_inv := by intro; casesm* [_ ⊕ _,ulift _]; refl,
--   left_inv := by intro; casesm* [_ ⊕ _,ulift _]; refl }

-- lemma map_proxy_t_up {α : Type u} {β γ} (x : proxy_t w α) (f : α → β) (g : β → γ) :
--   g <$> proxy_t.up f x = proxy_t.up (g ∘ f) x :=
-- begin
--   dsimp [(<$>)],
--   induction x; simp [proxy_t.map,*]; refl,
-- end

-- lemma up_read_write {α : Type u} {α' : Type (max u v)} (x : proxy_t w α) (y : put_m w) (f : α ≃ α') :
--   x.up f -<< up' (put_m' w) y = liftable1.up option f (x -<< y) :=
-- begin
--   dsimp [up',liftable1.up],
--   induction y generalizing x f,
--   cases x; simp; refl,
--   cases x; simp [up',liftable.up',liftable1.up,read_write,put_m.up,*], refl, refl, refl,
--   rw [read_write,← y_ih,up_bind],
--     apply congr,
--     { apply congr_arg, rw equiv_bind (@equiv.ulift_sum.{u u v v v} x_α x_β) ,
--       congr,
--       { rw map_proxy_t_up, congr, ext, cases x; refl },
--       simp [(∘)], ext, cases x;
--       dsimp [equiv.ulift_sum,sum.map], refl,
--       cases x, refl, apply_instance },
--     congr,
-- end

-- lemma up_read_write' {α : Type u} {α' : Type (max u v)}
--   {x : proxy_t w α} {y : put_m w} (f : α → α') (f' : α ≃ α')
--   (h : ∀ i, f i = f' i) :
--   x.up f -<< up' (put_m' w) y = liftable1.up option f' (x -<< y) :=
-- begin
--   rw ← up_read_write, congr, ext, apply h
-- end
end proxy_t
