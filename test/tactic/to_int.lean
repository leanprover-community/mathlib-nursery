import tactic.to_int

example (a b c d : ℕ)
  (h : a + b ≥ c)
  (h₀ : a ∣ c)
  (h' : a + c + 17 ≥ d)
  (sol : a * c ≤ b + d * c) :
  a * c ≤ b + d * c :=
begin
  to_int,
    -- a : ℤ,
    -- a_nneg : a ≥ 0,
    -- b : ℤ,
    -- b_nneg : b ≥ 0,
    -- c : ℤ,
    -- c_nneg : c ≥ 0,
    -- d : ℤ,
    -- d_nneg : d ≥ 0,
    -- h : a + b ≥ c,
    -- h₀ : a ∣ c,
    -- h' : a + c + 17 ≥ d
    -- ⊢ a * c ≤ b + d * c
  guard_hyp a := ℤ,
  guard_hyp b := ℤ,
  guard_hyp c := ℤ,
  guard_hyp d := ℤ,
  guard_hyp h := a + b ≥ c,
  guard_target a * c ≤ b + d * c,
  exact sol
end
