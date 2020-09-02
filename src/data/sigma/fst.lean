import data.sigma.basic
import tactic.ext

namespace sigma
universes u v

section
variables {α : Type u} {β β' : α → Type v}

theorem eq_fst {s₁ s₂ : sigma β} : s₁ = s₂ → s₁.1 = s₂.1 :=
by cases s₁; cases s₂; cc

theorem eq_snd {s₁ s₂ : sigma β} : s₁ = s₂ → s₁.2 == s₂.2 :=
by cases s₁; cases s₂; cc

end

section
variables {α₁ α₂ : Type u} {β₁ : α₁ → Type v} {β₂ : α₂ → Type v}

/-- A function on `sigma`s that is functional on `fst`s (preserves equality from
argument to result). -/
def fst_functional (f : sigma β₁ → sigma β₂) : Prop :=
∀ ⦃s t : sigma β₁⦄, s.1 = t.1 → (f s).1 = (f t).1

/-- A function on `sigma`s that is injective on `fst`s (preserves equality from
result to argument). -/
def fst_injective (f : sigma β₁ → sigma β₂) : Prop :=
∀ ⦃s t : sigma β₁⦄, (f s).1 = (f t).1 → s.1 = t.1

end

/-- A function on `sigma`s bundled with its `fst`-injectivity property. -/
structure embedding {α₁ α₂ : Type u} (β₁ : α₁ → Type v) (β₂ : α₂ → Type v) :=
(to_fun  : sigma β₁ → sigma β₂)
(fst_inj : fst_injective to_fun)

infixr ` s↪ `:25 := embedding

namespace embedding
variables {α₁ α₂ : Type u} {β₁ : α₁ → Type v} {β₂ : α₂ → Type v}

instance : has_coe_to_fun (β₁ s↪ β₂) :=
⟨_, embedding.to_fun⟩

@[simp] theorem to_fun_eq_coe (f : β₁ s↪ β₂) : f.to_fun = f :=
rfl

@[simp] theorem coe_fn_mk (f : sigma β₁ → sigma β₂) (i : fst_injective f) :
  (mk f i : sigma β₁ → sigma β₂) = f :=
rfl

theorem fst_inj' : ∀ (f : β₁ s↪ β₂), fst_injective f
| ⟨_, h⟩ := h

end embedding

section map_id
variables {α : Type u} {β₁ β₂ : α → Type v}

@[simp] theorem map_id_eq_fst {s : sigma β₁} (f : ∀ a, β₁ a → β₂ a) :
  (s.map id f).1 = s.1 :=
by cases s; refl

theorem map_id_fst_functional (f : ∀ a, β₁ a → β₂ a) :
  fst_functional (map id f) :=
λ _ _, by simp only [map_id_eq_fst]; exact id

theorem map_id_fst_injective (f : ∀ a, β₁ a → β₂ a) :
  fst_injective (map id f) :=
λ _ _, by simp only [map_id_eq_fst]; exact id

/-- Construct an `embedding` with `id` on `fst`. -/
def embedding.mk₂ (f : ∀ a, β₁ a → β₂ a) : embedding β₁ β₂ :=
⟨_, map_id_fst_injective f⟩

end map_id

section
variables {α : Type u} {β : α → Type v} {R : α → α → Prop}

/-- A relation `R` on `fst` values lifted to the `sigma`. This is useful where
you might otherwise use the term `λ s₁ s₂, R s₁.1 s₂.1`. -/
def fst_rel (R : α → α → Prop) (s₁ s₂ : sigma β) : Prop :=
R s₁.1 s₂.1

@[simp] theorem fst_rel_def {s₁ s₂ : sigma β} : fst_rel R s₁ s₂ = R s₁.1 s₂.1 :=
rfl

instance fst_rel_decidable [d : decidable_rel R] : decidable_rel (@fst_rel _ β R)
| s₁ s₂ := @d s₁.1 s₂.1

theorem fst_rel.refl (h : reflexive R) : reflexive (@fst_rel _ β R) :=
λ s, h s.1

theorem fst_rel.symm (h : symmetric R) : symmetric (@fst_rel _ β R) :=
λ s₁ s₂ (p : R s₁.1 s₂.1), h p

theorem fst_rel.trans (h : transitive R) : transitive (@fst_rel _ β R) :=
λ s₁ s₂ s₃ (p : R s₁.1 s₂.1) (q : R s₂.1 s₃.1), h p q

end

section
variables {α : Type u} {β : α → Type v}

theorem fst_functional_id : fst_functional (@id (sigma β)) :=
λ s t h, h

theorem fst_injective_id : fst_injective (@id (sigma β)) :=
λ s t h, h

@[refl] protected def embedding.refl (β : α → Type v) : β s↪ β :=
⟨_, fst_injective_id⟩

@[simp] theorem embedding.refl_apply (s : sigma β) : embedding.refl β s = s :=
rfl

end

section
variables {α₁ α₂ α₃ : Type u}
variables {β₁ : α₁ → Type v} {β₂ : α₂ → Type v} {β₃ : α₃ → Type v}
variables {g : sigma β₂ → sigma β₃} {f : sigma β₁ → sigma β₂}

theorem fst_functional_comp (gf : fst_functional g) (ff : fst_functional f) :
  fst_functional (g ∘ f) :=
λ s t h, gf (ff h)

theorem fst_injective_comp (gi : fst_injective g) (fi : fst_injective f) :
  fst_injective (g ∘ f) :=
λ s t h, fi (gi h)

@[trans] protected def embedding.trans (f : β₁ s↪ β₂) (g : β₂ s↪ β₃) : β₁ s↪ β₃ :=
⟨_, fst_injective_comp g.fst_inj f.fst_inj⟩

@[simp] theorem embedding.trans_apply (f : β₁ s↪ β₂) (g : β₂ s↪ β₃) (s : sigma β₁) :
  (f.trans g) s = g (f s) :=
rfl

end

end sigma
