import tactic.interactive logic.basic data.sigma logic.function

def rcomp {α β γ} (S : β → γ → Prop) (R : α → β → Prop) (a : α) (c : γ) :=
∃ b : β, R a b ∧ S b c

infix ` ∘ᵣ `:90 := rcomp

universes u v
class BNF (F : Type u → Type v) extends functor F, is_lawful_functor F :=
[has_mem : ∀ {α}, has_mem α (F α)]
(mem_map : ∀ {α β} (f : α → β) (b : β) (x : F α),
   b ∈ f <$> x ↔ ∃ a ∈ x, f a = b)
(attach : ∀ {α} (x : F α), F {a // a ∈ x})
(attach_map : ∀ {α} (x : F α), subtype.val <$> attach x = x)
(rel₂ : ∀ {α β}, (α → β → Prop) → F α → F β → Prop :=
  λ α β R x y,
    ∃ z : F (α × β), @prod.fst α β <$> z = x ∧ @prod.snd α β <$> z = y ∧
    ∀ (a : α) (b : β), (a, b) ∈ z → R a b)
(rel₂_iff : ∀ {α β} {R : α → β → Prop} {x y}, rel₂ R x y ↔
  ∃ z : F (α × β), @prod.fst α β <$> z = x ∧ @prod.snd α β <$> z = y ∧
  ∀ (a : α) (b : β), (a, b) ∈ z → R a b . control_laws_tac)
(rel₂_comp : ∀ {α β γ : Type u} (S : β → γ → Prop) (R : α → β → Prop)
  {x z}, (rel₂ S ∘ᵣ rel₂ R) x z → rel₂ (S ∘ᵣ R) x z)
(B : Type u)
(iota : ∀ {α}, F α → B → option α)
(idx : ∀ {α}, F α → α → B)
(idx_iota : ∀ {α} (x : F α) (a : α), a ∈ x → a ∈ iota x (idx x a))

section
variables {F : Type u → Type v} [BNF F]
attribute [instance] BNF.has_mem

theorem mem_map {α β} {f : α → β} {b : β} {x : F α} :
  b ∈ f <$> x ↔ ∃ a ∈ x, f a = b :=
BNF.mem_map f b x

def forall₂ {α β} (R : α → β → Prop) (x : F α) (y : F β) : Prop :=
BNF.rel₂ R x y

def forall₂_iff {α β} {R : α → β → Prop} {x : F α} {y : F β} :
  forall₂ R x y ↔
    ∃ z : F (α × β), @prod.fst α β <$> z = x ∧ @prod.snd α β <$> z = y ∧
    ∀ (a : α) (b : β), (a, b) ∈ z → R a b :=
BNF.rel₂_iff F

theorem map_congr {α β : Type u} {f g : α → β} {x : F α}
    (h : ∀ a ∈ x, f a = g a) : f <$> x = g <$> x :=
calc f <$> x = f <$> (subtype.val <$> BNF.attach x) : by rw BNF.attach_map
  ... = (λ x:{a//a∈ x}, f x.1) <$> BNF.attach x : (comp_map _ _ _).symm
  ... = (λ x:{a//a∈ x}, g x.1) <$> BNF.attach x : by congr; funext a; exact h _ a.2
  ... = g <$> (subtype.val <$> BNF.attach x) : (comp_map _ _ _)
  ... = g <$> x : by rw BNF.attach_map

theorem forall₂_eq {α} {a b : F α} : forall₂ (=) a b ↔ a = b :=
forall₂_iff.trans ⟨λ h, begin
  rcases h with ⟨z, rfl, rfl, h₃⟩,
  exact map_congr (λ ⟨a, b⟩ h, h₃ _ _ h),
end,
 λ h, begin
  subst h,
  refine ⟨(λ x, (x, x)) <$> a, _, _, _⟩,
  iterate 2 {
    rw ← is_lawful_functor.comp_map,
    simp [(∘)],
    rw [← show id = λ x, x, from rfl, id_map] },
  intros b c h,
  rcases mem_map.1 h with ⟨_, h, ⟨⟩⟩,
  refl
end⟩

theorem forall₂_mono {α β} {R S : α → β → Prop} (H : ∀ a b, R a b → S a b)
  {a : F α} {b : F β} (hR : forall₂ R a b) : forall₂ S a b :=
let ⟨z, h₁, h₂, h₃⟩ := forall₂_iff.1 hR in
forall₂_iff.2 ⟨z, h₁, h₂, λ a b h, H _ _ (h₃ _ _ h)⟩

theorem forall₂_swap {α β} {R : α → β → Prop}
  {x : F β} {y : F α} :
  forall₂ (function.swap R) x y ↔ forall₂ R y x :=
begin
  split; intro h;
  { rcases forall₂_iff.1 h with ⟨c, rfl, rfl, H⟩,
    refine forall₂_iff.2 ⟨prod.swap <$> c, _, _, _⟩,
    { rw ← comp_map, simp [(∘)] },
    { rw ← comp_map, simp [(∘)] },
    { refine λ a b h', H b a _,
      rcases mem_map.1 h' with ⟨⟨_, _⟩, h, ⟨⟩⟩,
      exact h } }
end

theorem forall₂_map_left {α β} (f : α → β) (x : F α) :
  forall₂ (λ b a, b = f a) (f <$> x) x :=
forall₂_iff.2 ⟨(λ a, (f a, a)) <$> x,
  by rw ← comp_map,
  by rw ← comp_map; exact id_map _,
  λ a b h, by rcases mem_map.1 h with ⟨_, h, ⟨⟩⟩; refl⟩

theorem forall₂_map_right {α β} (f : α → β) (x : F α) :
  forall₂ (λ a b, b = f a) x (f <$> x) :=
forall₂_swap.2 (forall₂_map_left _ _)

theorem map_inj {α β} {f : α → β} (hf : function.injective f)
  : @function.injective (F α) (F β) ((<$>) f)
| x y h := forall₂_eq.1 begin
  refine forall₂_mono _
    (BNF.rel₂_comp _ _ ⟨_, forall₂_swap.1 (forall₂_map_left f x),
      by rw h; exact forall₂_map_left f y⟩),
  intros a b h, rcases h with ⟨c, rfl, h⟩, exact hf h
end

theorem map_attach {α β : Type u} (f : α → β) (x : F α) :
  BNF.attach (f <$> x) = (subtype.map f (λ a h,
    mem_map.2 ⟨a, h, rfl⟩)) <$> BNF.attach x :=
map_inj subtype.val_injective begin
  rw [← comp_map, BNF.attach_map],
  transitivity, rw [← BNF.attach_map x, ← comp_map],
  congr' 1, funext a, cases a, refl
end

theorem mem_attach {α β : Type u} (f : α → β) (x : F α) : ∀ a, a ∈ BNF.attach x
| ⟨a, h⟩ := have a ∈ subtype.val <$> BNF.attach x, by rwa BNF.attach_map,
  by rcases mem_map.1 this with ⟨⟨_, _⟩, h', rfl⟩; exact h'

theorem forall₂_comp
  {α β γ} (S : β → γ → Prop) (R : α → β → Prop) :
  (forall₂ S ∘ᵣ forall₂ R : F α → F γ → Prop) = forall₂ (S ∘ᵣ R) :=
begin
  funext x z,
  simp [(∘ᵣ)],
  refine propext ⟨BNF.rel₂_comp _ _, λ h, _⟩,
  rcases forall₂_iff.1 h with ⟨y, rfl, rfl, h'⟩,
  let X := {a:α × γ // a ∈ y},
  cases classical.axiom_of_choice
    (λ x : X, h' x.1.1 x.1.2 (by simpa using x.2)) with f hf,
  dsimp at f hf,
  refine ⟨f <$> (BNF.attach y),
    forall₂_iff.2 ⟨(λ a:X, (a.1.1, f a)) <$> BNF.attach y, _, _, _⟩,
    forall₂_iff.2 ⟨(λ a:X, (f a, a.1.2)) <$> BNF.attach y, _, _, _⟩⟩,
  any_goals {
    refine eq.trans _ (congr_arg _ (BNF.attach_map y)),
    rw [← comp_map, ← comp_map] },
  any_goals { rw ← comp_map },
  any_goals {
    intros a b h,
    rcases mem_map.1 h with ⟨x, _, ⟨⟩⟩,
    simp [hf x] }
end

end

section

inductive W (B : Type u) : Type u
| nil {} : W
| fn : (B → W) → W

variables {F : Type u → Type u} [BNF F]

local notation `B` := BNF.B F
local notation `W` := W B

def Fn : W → Type u
| W.nil := ulift empty
| (W.fn f) := F (Σ b : B, Fn (f b))

def BNF.lfp (F : Type u → Type u) [BNF F] := Σ w, @Fn F _ w
local notation `μF` := BNF.lfp F

def BNF.lfp.out : μF → F μF
| ⟨W.fn f, x⟩ := (λ a:Σ b, Fn (f b), ⟨f a.1, a.2⟩) <$> x

def BNF.lfp.mk (x : F μF) : μF :=
let f (b : B) : W :=
  match BNF.iota x b with
  | none := W.nil
  | some x := x.1
  end in
⟨W.fn f, (λ a: {a // a ∈ x}, ⟨BNF.idx x a.1,
  have f (BNF.idx x a.1) = a.1.1, by exact
    congr_arg BNF.lfp.mk._match_1 (BNF.idx_iota _ _ a.2),
  by rw this; exact a.1.2⟩) <$> BNF.attach x⟩

def BNF.lfp.rec_aux {X : Type u} (G : F X → X) : ∀ w:W, Fn w → X
| (W.fn f) x := G ((λ a:Σ b : B, Fn (f b), BNF.lfp.rec_aux (f a.1) a.2) <$> x)

def BNF.lfp.rec {X : Type u} (G : F X → X) : μF → X
| ⟨w, x⟩ := BNF.lfp.rec_aux G w x

theorem BNF.lfp.rec_eq {X : Type u} (G : F X → X) (x : F μF) :
  BNF.lfp.rec G (BNF.lfp.mk x) = G (BNF.lfp.rec G <$> x) :=
begin
  simp [BNF.lfp.mk, BNF.lfp.rec, BNF.lfp.rec_aux],
  congr' 1,
  transitivity, swap, rw ← BNF.attach_map x,
  rw [← comp_map, ← comp_map],
  congr' 1,
  funext a, rcases a with ⟨⟨w, a⟩, h⟩,
  simp [(∘), BNF.lfp.rec],
  delta BNF.lfp.mk._proof_1,
  generalize : BNF.lfp.mk._proof_2 x ⟨⟨w, a⟩, h⟩ = h',
  dsimp [BNF.lfp.rec_aux] at h' ⊢,
  revert h',
  generalize : BNF.lfp.mk._match_1 (BNF.iota x (BNF.idx x ⟨w, a⟩)) = y,
  intro h', subst y, refl,
end

/-
def {l} BNF.lfp.ind_aux (X : μF → Sort l) (e : ∀ x : F μF, (∀ a ∈ x, X a) → X (BNF.lfp.mk x)) :
  ∀ (w:W) (x: Fn w), X ⟨w, x⟩
| (W.fn f) x := begin
  let y := _ <$> x,
  have : BNF.lfp.mk y = ⟨W.fn f, x⟩,
  { dsimp [BNF.lfp.mk],
    suffices : _ = f, congr', swap,
    { funext b,
      have : _ = _ := BNF.idx_iota y ⟨f b, _⟩ _, },
    { have C : ∀ {g} (h : g = f), cast (congr_arg _ h.symm) <$> x == x,
      { intros, subst g, refine heq_of_eq (id_map _) },
      refine (heq_of_eq _).trans (C this),
      rw [← BNF.attach_map x, map_attach, ← comp_map, ← comp_map],
      congr' 1, funext a, rcases a with ⟨⟨b, g⟩, ax⟩,
      dsimp [subtype.map], } },
end

def {l} BNF.lfp.ind (X : μF → Sort l) (e : ∀ x : F μF, (∀ a ∈ x, X a) → X (BNF.lfp.mk x)) :
  ∀ a, X a
| ⟨w, x⟩ := BNF.lfp.ind_aux _ e _ _

theorem {l} BNF.lfp.ind_eq (X : μF → Sort l)
  (e a) : BNF.lfp.ind X e (BNF.lfp.mk a) = e _ (λ b h, BNF.lfp.ind X e b) :=
sorry
-/

end
