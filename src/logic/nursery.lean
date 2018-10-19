
lemma eq_mp_heq :
  ∀ {α β : Sort*} {a : α} {a' : β} (h₂ : a == a'), (eq.mp (type_eq_of_heq h₂) a) = a'
| α ._ a a' heq.rfl := rfl
