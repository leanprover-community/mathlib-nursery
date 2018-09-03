
import category.nursery
import category.functor
import category.traversable.equiv
import data.equiv.basic
import tactic
import data.sigma.fst
import data.coinductive.basic
import data.coinductive.eq

universes u v w

def rep {head_t : Type v} (child_t : head_t → Type v) (α : Type w) :=
(Σ x : head_t, child_t x → α)

def rep.mk {head_t : Type v} {child_t : head_t → Type v} {α : Type w}
  (x : head_t) (f : child_t x → α) : rep child_t α :=
sigma.mk x f

def rep.map {head_t : Type v} {child_t : head_t → Type v} {α β} (f : α → β) :
  rep child_t α → rep child_t β
| ⟨ x, g ⟩ := ⟨ x, f ∘ g ⟩

instance {head_t : Type v} (child_t : head_t → Type v) : functor (rep child_t) :=
{ map := @rep.map _ child_t }

instance {head_t : Type v} (child_t : head_t → Type v) : is_lawful_functor (rep child_t) :=
by constructor; intros; cases x; simp [(<$>),rep.map]

section positive

parameters (F : Type u → Type v)
           (head_t : Type v)
           (child_t : head_t → Type v)
           (to_rep : Π α, F α ≃ rep child_t α)

@[simp]
def positive.map {α β} (f : α → β) (x : F α) : F β :=
(to_rep β).symm $ f <$> to_rep α x

def positive.map_comm {α β} (f : α → β) (x : F α) :
  to_rep β (positive.map f x) = f <$> (to_rep α x) :=
by simp [positive.map]

meta def positive.prove_eqv : tactic unit :=
tactic.intros >> tactic.applyc `positive.map_comm

end positive

class positive (F : Type u → Type v)
extends functor F :=
(head_t : Type v)
(child_t : head_t → Type v)
(to_rep : Π α, F α ≃ rep child_t α)
(map := @positive.map F head_t child_t to_rep )
(map_eqv_rep_map : ∀ {α β} (f : α → β) (x : F α), to_rep β (f <$> x) = f <$> (to_rep α x) . positive.prove_eqv )
(map_const_eq : ∀ {α β : Type u}, ((<$) : α → F β → F α) = (<$>) ∘ function.const β . control_laws_tac)

export positive (head_t child_t)

def positive.rep_t (F) [positive F] := rep (@child_t F _)

def to_rep {F} [positive F] {α} : F α → rep (@child_t F _) α :=
positive.to_rep F α

def of_rep {F} [positive F] {α} : rep (@child_t F _) α → F α :=
(positive.to_rep F α).symm

@[simp]
def of_rep_to_rep (F) [positive F] {α} (x : F α) :
  of_rep (to_rep x) = x :=
by simp [to_rep,of_rep]

@[simp]
def to_rep_of_rep (F) [positive F] {α} (x : positive.rep_t F α) :
  to_rep (of_rep x) = x :=
by simp [to_rep,of_rep]

lemma map_eqv_rep_map  (F) [positive F] {α β} (f : α → β) (x : F α) :
  to_rep (f <$> x) = f <$> (to_rep x) :=
positive.map_eqv_rep_map _ _ _

open ulift function (hiding comp) functor

lemma rep_map_eqv_map {F} [positive F] {α β} (f : α → β) (x : positive.rep_t F α) :
  of_rep (f <$> x) = f <$> of_rep x :=
begin
  have := map_eqv_rep_map F f (of_rep x),
  simp at this, rw ← this, simp,
end

attribute [simp] map_eqv_rep_map

def positive.head {F} [positive F] {α} (x : F α) : head_t F :=
(to_rep x).1

def positive.idx {F α} [positive F] (x : F α) := child_t (positive.head x)

def positive.child {F α} [positive F] (x : F α) (i : positive.idx x) :=
(to_rep x).2 i

instance positive.is_lawful_functor (F : Type u → Type v) [positive F] : is_lawful_functor F :=
begin
  constructor,
  { apply positive.map_const_eq },
  { intros,
    rw [← equiv.apply_eq_iff_eq (positive.to_rep F _),positive.map_eqv_rep_map],simp },
  { intros, rw [← equiv.apply_eq_iff_eq (positive.to_rep F _)],
    simp [positive.map_eqv_rep_map,map_map], },
end

namespace sum

protected def child_t (α : Type u) : (option.{u} α) → Type u
| none := punit
| (some _) := ulift empty

@[simp]
protected def to_fun {α β} : α ⊕ β → rep (sum.child_t $ ulift.{u} α) β
| (sum.inr x) := ⟨ none, λ _, x ⟩
| (sum.inl x) := ⟨ some $ up x, empty.elim ∘ down ⟩

@[simp]
protected def inv_fun {α β} : rep (sum.child_t $ ulift.{u} α) β → α ⊕ β
| ⟨ some x, f ⟩ := sum.inl $ down x
| ⟨ none, f ⟩ := sum.inr $ f punit.star

protected def to_rep (α β) : (α ⊕ β) ≃ rep (sum.child_t $ ulift α) β :=
{ equiv . to_fun := @sum.to_fun.{u v} α β,
  inv_fun := @sum.inv_fun.{u v} α β,
  right_inv := by { intro, casesm* [ rep _ _, option _]; simp, ext ⟨ ⟨ ⟩ ⟩; refl,
                    split, simp [up_down], ext ⟨ ⟨ ⟩ ⟩, },
  left_inv  := by { intro, cases x; simp } }

instance {α : Type v} : positive (sum.{v u} α) :=
{ head_t := option (ulift α),
  child_t := sum.child_t.{max u v} (ulift.{u} α),
  to_rep := sum.to_rep α,
  map_eqv_rep_map := by { rintros _ _ _ ⟨ ⟩; simp [(<$>),sum.mapr];
                          unfold_coes; simp [sum.to_rep,rep.map] } }

end sum

namespace id

protected def child_t (x : punit) : Type u := punit

@[simp]
protected def to_fun {α} (x : id α) : rep id.child_t α :=
⟨ punit.star , λ _, x ⟩

@[simp]
protected def inv_fun {α} : rep id.child_t α → id α
| ⟨ _, f ⟩ := f punit.star

protected def to_rep (α) : id α ≃ rep id.child_t α :=
{ to_fun := id.to_fun,
  inv_fun := id.inv_fun,
  left_inv := by { intro; refl },
  right_inv := by { rintro ⟨ ⟨ ⟩ ⟩, simp, ext ⟨ ⟩, refl } }

instance : positive id :=
{ head_t := punit,
  child_t := @const _ _ punit,
  to_rep := id.to_rep,
  map_eqv_rep_map := by { intros; refl } }

end id

namespace comp

variables (F : Type v → Type v) (G : Type u → Type v)
variables [positive F] [positive G]

protected def head_t : Type* :=
Σ x : head_t F, child_t x → head_t G

protected def child_t (x : comp.head_t F G) : Type* :=
Σ (i : positive.child_t x.1), positive.child_t (x.2 i)

private def to_fun1 (α : Type u) (x : rep (@positive.child_t F _) (G α)) : rep (comp.child_t F G) α :=
⟨ ⟨ x.1, λ i, (to_rep $ x.2 i).1 ⟩ , λ ⟨a,b⟩, (to_rep $ x.2 a).2 b ⟩

protected def to_fun (α : Type u) (x : functor.comp F G α) : rep (comp.child_t F G) α :=
to_fun1 F G α (to_rep x)
-- ⟨ ⟨ (to_rep F (G α) x).1, λ i, (to_rep G α ((to_rep F (G α) x).2 i)).1 ⟩ ,
--         λ a, (to_rep G α $ (to_rep F (G α) x).2 a.1).2 a.2 ⟩

@[simp]
lemma fst_to_fun1  (α : Type u) (x : rep (@positive.child_t F _) (G α)) :
  (to_fun1 F G α x).fst = ⟨ x.1, λ i, (to_rep $ x.2 i).1 ⟩ :=
by cases x; refl

@[simp]
lemma snd_to_fun1  (α : Type u) (x : rep (@positive.child_t F _) (G α)) (a) :
  (to_fun1 F G α x).snd a = (to_rep $ x.2 a.1).2 a.2 :=
by { cases x, cases a, simp [to_fun1], refl }

def foo (α) (x : rep (@positive.child_t F _) (positive.head_t G))
    (f : comp.child_t F G x → α) (i : positive.child_t x.1) :
  rep (@positive.child_t G _) α :=
⟨x.2 i, λ j, f ⟨i,j⟩ ⟩

private def inv_fun1 (α : Type u) (x : rep (comp.child_t F G) α) : rep (@positive.child_t F _) (G α) :=
⟨ x.1.1, of_rep ∘ foo F G α _ x.2 ⟩

@[simp]
lemma fst_inv_fun1 (α : Type u) (x : rep (comp.child_t F G) α) :
  (inv_fun1 F G α x).fst = x.fst.fst :=
by rcases x with ⟨ ⟨ ⟩ ⟩; refl

@[simp]
lemma snd_inv_fun1 (α : Type u) (x : rep (comp.child_t F G) α) :
  (inv_fun1 F G α x).snd = of_rep ∘ foo F G α (x.1) x.2 :=
by rcases x with ⟨ ⟨ ⟩ ⟩; refl

-- lemma snd_to_rep_eq {α} (x : G α) (x' : rep (comp.child_t F G) α)
--   (a : positive.child_t ((to_rep G α x).fst))
--   (a' : comp.child_t F G x'.fst)
--   (y : rep (@positive.child_t G _) α)
--   (z : positive.head_t G)
--   (h : x = of_rep G α y)
--   (h' : ∀ i, x'.snd i = y.snd _) :
--   (to_rep G α x).snd a = x'.snd a' :=
-- begin
--   subst h, cases ((to_rep G α) ((of_rep G α) y)),
--   dsimp,
--   cases x', simp, dsimp at a', cases a',
--   cases h' : ((to_rep G α) x), subst x,
--   simp at h',
--  dsimp,
--   have := congr_fun (⇑(to_rep G α)) h,
-- end

protected def inv_fun (α : Type u) (x : rep (comp.child_t F G) α) : functor.comp F G α :=
@of_rep F _ (G α) (inv_fun1 F G α x)

attribute [extensionality] hfunext

lemma right_inv1 {α} : right_inverse (inv_fun1 F G α) (to_fun1 F G α) :=
begin
  intro, ext : 1,
  { simp, rcases x with ⟨ ⟨ ⟩ ⟩, simp [foo], },
  { simp, intro, apply hfunext,
    { simp, congr, ext, simp, simp, ext, simp [foo] },
    intros, simp, cases a_1, dsimp, admit },
  -- rintro ⟨ ⟨ ⟩ ⟩,
  -- dsimp [to_fun1,inv_fun1],
  -- congr' 1, refl,
  -- simp, split, refl, apply hfunext, congr,
  -- ext, simp, refl,
  -- intros, cases a, cases a', dsimp, simp,
  -- transitivity, apply congr_fun,
  -- apply eq_of_heq,
  -- apply sigma.eq_snd,
  -- generalize : ( (to_rep G α) (of_rep G α _) ) = z,
  -- dsimp [of_rep], simp,
  -- intros, simp, cases a, cases a',
  -- dsimp, simp, apply eq_of_heq,
  -- transitivity (sigma.mk (x_fst_snd a_fst) (λ (j : positive.child_t (x_fst_snd a_fst)), x_snd ⟨a_fst, j⟩)).snd a_snd,
  -- apply congr_fun,
  -- apply congr_arg,
end

protected lemma left_inv {α} : left_inverse (comp.inv_fun F G α) (comp.to_fun F G α) :=
begin
  intro, symmetry,
  simp [comp.to_fun,comp.inv_fun],
  admit
  -- { dsimp, intro, simp, ext,
  --   rw ← equiv.apply_eq_iff_eq_inverse_apply, ext, refl,
  --   intros, simp, }
end

protected lemma right_inv {α} : right_inverse (comp.inv_fun F G α) (comp.to_fun F G α) :=
begin
  intro,
  generalize h : (comp.inv_fun F G α x) = k,
  rcases x with ⟨ ⟨ ⟩ ⟩,
  simp [comp.inv_fun] at h,
  dsimp [comp.to_fun],
  admit,
--   dsimp at *, cases h, clear h,
--   simp, dsimp,
--   have : x_fst_snd = λ (i : positive.child_t x_fst_fst),
--             ((to_rep G α)
--                ((of_rep G α) ⟨x_fst_snd i, λ (j : positive.child_t (x_fst_snd i)), x_snd ⟨i, j⟩⟩)).fst,
--   { admit, },
--   cases this,

--  congr, ext, simp,
--   apply hfunext, congr, ext, simp,
--   dsimp, intros, simp,
--   have := type_eq_of_heq a_1,
--   revert a, simp,

-- simp at this,
--   rw equiv.apply_inverse_apply,

--   have := congr_arg sigma.fst h,
--   dsimp at this, congr' 2,
--   { rw this },
--   { apply hfunext, rw this,
--     subst x_fst_fst, intros, cases a_1, clear a_1, simp,

--     cases ((to_rep F (G α)) k), dsimp at *, cases h, simp },
--   { apply hfunext, congr' 1, simp [this], apply hfunext, congr, simp [this],
--     cases (to_rep F (G α)) k, cases h,
--     rw [to_fun._match_1], clear this, revert h, cases  ((to_rep F (G α)) k), simp, },
end

-- set_option pp.implicit true

protected def to_rep (α) : comp F G α ≃ rep (comp.child_t F G) α :=
{ to_fun := comp.to_fun F G α,
  inv_fun := comp.inv_fun F G α,
  left_inv := sorry,
  right_inv := by { intro, admit } }

instance : positive.{u v} (comp F G) :=
{ head_t := comp.head_t F G,
  child_t := comp.child_t F G,
  to_rep := comp.to_rep F G,
  map_eqv_rep_map := sorry }

def assoc_left {f g h} {x} : comp f (comp g h) x → comp (comp f g) h x := id

def assoc_right {f g h} {x} : comp (comp f g) h x → comp f (comp g h) x := id

end comp

def cofix' (f : Type u → Type v) [positive f] := cofix (@child_t f _)

namespace cofix

section corec'

variables {f : Type u → Type u} [positive f]

def corec₀ {X : Type u} (F : X → f X) : X → cofix' f :=
@cofix.corec _ _ _ (λ i, to_rep $ F i)

end corec'

section unroll

variables (f g : Type u → Type u) [positive f] [positive g]

def unfold_aux (i : head_t f) (F : child_t i → cofix (@child_t f _)) : f (cofix' f) :=
of_rep ⟨i,F⟩

-- set_option pp.universes true
variables {f g}

def unfold (x : cofix' f) : f (cofix'.{u u} f) :=
cofix.cases_on.{u u u+1} x (by apply unfold_aux.{u} f)

def fold (x : f (cofix' f)) : (cofix'.{u u} f) :=
cofix.mk (to_rep x).1 (to_rep x).2

lemma fold_unfold (x : cofix' f) : fold (unfold x) = x :=
begin
  apply cofix.cases_on x, intros,
  simp [unfold,unfold_aux,fold],
  rw to_rep_of_rep,
end

lemma unfold_fold (x : f $ cofix' f) : unfold (fold x) = x :=
begin
  dsimp [fold],
  cases h : to_rep x,
  simp [unfold,unfold_aux],
  rw ← h, simp,
end

open function (hiding comp)

lemma fold_inj : injective (@fold f _) :=
injective_of_left_inverse unfold_fold

lemma unfold_inj : injective (@unfold f _) :=
injective_of_left_inverse fold_unfold

def roll (x : g (cofix' (comp f g))) : cofix' (comp g f) :=
corec₀ (@comp.assoc_left g f g _ ∘ (<$>) unfold) x

def unroll (x : cofix' (comp f g)) : f (cofix' (comp g f)) :=
roll <$> comp.run (unfold x)

def head' {α} (x : f α) : head_t f := (to_rep x).1
def children' {α} (x : f α) : child_t (head' x) → α := (to_rep x).2

lemma head_fold (x : f (cofix' f)) :
  head (fold x) = head' x :=
by { dsimp [fold], cases h : to_rep x, simp [head',h], }

lemma children_fold (x : f (cofix' f)) (i : child_t (head (fold x))) :
  children (fold x) == children' x :=
by { dsimp [fold], cases h : to_rep x, simp [children,children'],
     symmetry, apply sigma.eq_snd h }

lemma children_fold' (x : f (cofix' f)) (i : child_t (head (fold x))) :
  children (fold x) i = children' x (cast (by rw head_fold) i) :=
by { dsimp [fold], cases h : to_rep x, simp [children,children'],
     symmetry,
     have := sigma.eq_snd h, simp at this,
     admit, }

end unroll

section corec'

variables {f : Type u → Type u} [positive f]

def unfold' : cofix' f ⊕ f (cofix' f) → f (cofix' f)
| (sum.inr x) := x
| (sum.inl x) := unfold x

def fold' : cofix' f ⊕ f (cofix' f) → cofix' f
| (sum.inr x) := fold x
| (sum.inl x) := x

-- lemma head_fold (x : f (cofix' f)) :
--   head (fold x) = head' x :=

def corec₁ {α : Type u} (F : Π X, (α → X) → α → f X) : α → cofix' f :=
corec₀ (F _ id)

lemma head_corec₁ {α : Type u} (F : Π X, (α → X) → α → f X) (x : α)
: head (corec₁ F x) = head' (F _ id x) :=
sorry

lemma fold_corec₁
  {α : Type u} (F : Π X, (α → X) → α → f X) (x : α)
  (h : ∀ β β' g g' y, head' (F β g y) = head' (F β' g' y)) :
  fold (F _ (corec₁ F) x) = corec₁ F x  :=
begin
  unfold corec₁ corec₀,
  symmetry, transitivity,
  rw corec_eq,
  -- unfold fold, refl,
  -- cases h' : (to_rep (F (cofix' (λ (X : Type u), f X)) (cofix.corec (λ (i : α), to_rep (F α id i))) x)),
  dsimp, congr' 1,
  { apply h },
  { ext, congr' 1, apply h,
    intros, rw corec_eq,
    admit },
end

lemma unfold_corec₁
  {α : Type u} (F : Π X, (α → X) → α → f X) (x : α)
  (h : ∀ β β' g g' y, head' (F β g y) = head' (F β' g' y)) :
  unfold (corec₁ F x) = F _ (corec₁ F) x :=
by apply fold_inj; rw [fold_corec₁ _ _ h,fold_unfold]

def corec' {α : Type u} (F : Π {X : Type u}, (α → X) → α → cofix' f ⊕ f X) (x : α) : cofix' f :=
corec₁
(λ X rec (a : cofix' f ⊕ α),
let y := a >>= F (rec ∘ sum.inr) in
match y with
| sum.inr y := y
| sum.inl y := (rec ∘ sum.inl) <$> unfold y
end )
(@sum.inr (cofix' f) _ x)

section eqns
variables
  {α : Type u}
  (F : (cofix' f) → f (cofix' f))

lemma fold_apply_corec'
  (G : Π (X), (α → X) → α → cofix' f ⊕ f X)
  (x : α)
  -- (h : ∀ β β' g g', (<$) punit.star <$> G β g x = (<$) punit.star <$> G β' g' x)
  -- (h : G _ _ x = sum.inl _)
 :
  (corec' G x) =
  fold' (G _ (corec' G) x) :=
begin
  simp [corec'],
  rw ← fold_corec₁, simp,
  cases h' : (G (cofix' (λ (X : Type u), f X))
         (corec₁
              (λ (X : Type u) (rec : cofix' f ⊕ α → X) (a : cofix' f ⊕ α),
                 corec'._match_1 X rec (a >>= G X (rec ∘ sum.inr))) ∘
            sum.inr)
         x);
  simp [fold',corec'._match_1,(∘)],
  generalize h : (λ (x : cofix' f),
            corec₁
              (λ (X : Type u) (rec : cofix' f ⊕ α → X) (a : cofix' f ⊕ α),
                 corec'._match_1 X rec (a >>= G X (λ (x : α), rec (sum.inr x))))
              (sum.inl x)) = k,
  suffices : k = id,
  { simp [this,fold_unfold], },
  subst k,
  ext,
  admit, admit
end

-- lemma fold_apply_corec''
--   (G : Π (X), (α → X) → α → cofix' f ⊕ f X)
--   (x : α)
--   (h : ∀ a, G _ _ x = sum.inr (F a)) :
--   cofix.fold (F (corec'' G x)) =
--   corec'' G x :=
-- begin
--   simp [fold],
--   cases h : (to_rep (F (corec'' G x))),
--   simp,
--   -- symmetry, transitivity,
--   simp [corec'',corec',corec_aux₁,corec_aux₀],
--   rw cofix.corec_eq,
--   -- simp [corec_aux₁._match_1],
--   congr,
--   simp [corec_aux₁._match_1],
--   cases h' : G _ id x,
--   simp [corec'._match_1,unfold],
--   revert h',
--   apply cofix.cases_on val;
--   intros; simp [unfold_aux,(<$>),rep.map,corec'._match_1],

-- end

end eqns
end corec'

end cofix
