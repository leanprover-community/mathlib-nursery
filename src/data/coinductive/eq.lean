
import data.coinductive.basic

universes u v
variables {α : Type u}
variables (β : α → Type v)

namespace cofix

open coinduction.approx

variables {β}

local prefix `♯`:0 := cast (by simp [*] <|> cc <|> solve_by_elim)

local attribute [instance, priority 0] classical.prop_decidable

lemma ext (x y : cofix β)
  (H : ∀ (ps : path β), (select x ps).dom →
                         (select y ps).dom →
                         select x ps = select y ps)
: x = y :=
begin
  cases x, cases y,
  congr, funext i,
  induction i with i,
  { cases x_approx 0, cases y_approx 0, refl },
  { apply ext_aux, apply_assumption,
    rw i_ih, apply_assumption,
    introv h₀ h₁ H',
    simp [select] at H,
    cases H',
    apply H ps ; assumption, }
end

section bisim
  variable (R : cofix β → cofix β → Prop)
  local infix ~ := R

  def is_bisimulation :=
      ∀ ⦃s₁ s₂⦄, s₁ ~ s₂ →
        head s₁ = head s₂ ∧
        (∀ i j : β (head _), i == j → children s₁ i ~ children s₂ j)

  theorem nth_of_bisim (bisim : is_bisimulation R) :
     ∀ (s₁ s₂) (ps : path β)
       (H₁ : (select s₁ ps).dom)
       (H₂ : (select s₂ ps).dom),
       s₁ ~ s₂ →
         (select s₁ ps) = (select s₂ ps) ∧
         ∀ Hi Hj i j, i == j →
                child s₁ ps Hi i ~ child s₂ ps Hj j :=
  begin
    intros _ _ _,
    revert s₁ s₂,
    induction ps,
    { introv _ _ h₀,
      have h₁ := bisim h₀,
      simp, split, cc,
      intros,
      apply h₁.2, cc, },
    { introv _ _ h₀,
      cases ps_hd with y i,
      have hd₁ : y = head s₁, { apply dom_select_cons, assumption },
      have hd₂ : y = head s₂, { apply dom_select_cons, assumption },
      split, rw [select_cons,select_cons] ; try { assumption },
      { apply (ps_ih _ _ _ _ _).1 ; clear ps_ih,
        simp [hd₁] at H₁, assumption,
        simp [hd₂] at H₂, assumption,
        simp [is_bisimulation] at bisim,
        apply (bisim h₀).2, cc, },
      intros,
      { simp [hd₁] at ⊢ H₁, simp [hd₂] at ⊢ H₂,
        apply (ps_ih _ _ _ _ _).2 ; clear ps_ih
        ; try { cc <|> assumption },
        apply (bisim h₀).2, cc, } },
  end

  theorem eq_of_bisim (bisim : is_bisimulation R) : ∀ s₁ s₂, s₁ ~ s₂ → s₁ = s₂ :=
  begin
    introv Hr, apply ext,
    introv Hs₁ Hs₂,
    have H := nth_of_bisim R bisim _ _ ps ,
    apply (H _ _ _).left ; assumption,
  end
end bisim

section coinduction

variables β

inductive rel_head : Type (max u v)
 | intro (x : α) (ch₀ ch₁ : β x → cofix β) : rel_head

def rel_branch : rel_head β → Type v
 | (rel_head.intro x _ _) := β x

structure sim_rel : Type (max u v) :=
  (rel : cofix β → cofix β → Prop)
  -- (head_rel : α → α → Prop)
  (refl : reflexive rel)
  -- (head_refl : reflexive head_rel)
  -- (head_eq : ∀ x y, rel x y → head_rel (head x) (head y))
  (backward : ∀ x (ch₀ ch₁ : β x → cofix β),
    rel (cofix.mk x ch₀) (cofix.mk x ch₁) →
    (∀ i j, i == j → rel (ch₀ i) (ch₁ j)))

instance : has_coe_to_fun (sim_rel β) :=
{ F := λ r, cofix β → cofix β → Prop
, coe := sim_rel.rel }

coinductive R : Π (s₁ s₂ : cofix β), Prop
| intro (s₁ s₂ : cofix β) :
   head s₁ = head s₂ →
   (∀ i j, i == j → R (children s₁ i) (children s₂ j)) →
   R s₁ s₂

open ulift
lemma R_is_bisimulation : is_bisimulation (R β) :=
begin
  simp [is_bisimulation],
  introv hr,
  apply R.cases_on _ hr,
  intros,
  split; assumption,
end

variables {β}

lemma coinduction (s₁ s₂ : cofix β)
  (hh : R _ s₁ s₂)
: s₁ = s₂ :=
eq_of_bisim
  (R β) (R_is_bisimulation β) _ _
  hh

end coinduction

def iterate (x : α) (f : Π x, β x → α) : cofix β :=
cofix.corec (λ x, ⟨ x, f x⟩) x

universes u' v'

def map {α' : Type u'} {β' : α' → Type v'}
  (f : α → α') (g : Π x, β' (f x) → β x)
  (x : cofix  β) : cofix β' :=
cofix.corec (λ t, ⟨ f (head t), λ k, children t (g _ k) ⟩) x

def corec_on {X : Type*} (x₀ : X) (f : X → (Σ (y : α), β y → X)) : cofix β :=
cofix.corec f x₀

theorem corec_eq {X : Type*} (f : X → (Σ (y : α), β y → X)) (x₀ : X)
: cofix.corec f x₀ = cofix.mk (f x₀).1 (λ i, cofix.corec f ((f x₀).2 i)) :=
begin
  -- cases Hf : f x₀, simp,
  rw mk_head_children (cofix.corec f x₀),
  congr, simp,
  apply function.hfunext, simp, intros, simp,
  congr, apply eq_of_heq, transitivity a,
  apply cast_heq, assumption,
end

lemma id_map {α' : Type u'} {β' : α' → Type v'} (x : cofix  β) :
  (map id (λ _, id) x : cofix β) = x :=
begin
  apply coinduction,
  coinduction cofix.R.corec_on generalizing x,
  dsimp [map], simp,
  intros, subst j, refl,
end

theorem corec_eq' {X : Type*} (f : X → α) (g : Π x : X, β (f x) → X) (x₀ : X)
: cofix.corec (λ x, ⟨f x,g x⟩) x₀ = cofix.mk (f x₀) (λ i, cofix.corec (λ x, ⟨f x,g x⟩) (g x₀ i)) :=
corec_eq _ x₀

end cofix
