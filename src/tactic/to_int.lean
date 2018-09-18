import data.int.basic

namespace tactic.interactive

open tactic

lemma translate_nat (P : ℤ → Sort*) (h : ∀ i : ℤ, i ≥ 0 → P i) :
  ∀ i : ℕ, P i :=
assume i,
h i (int.coe_nat_nonneg i)

run_cmd mk_simp_attr `to_int

@[to_int]
lemma coe_nat_inj {m n : ℕ} : m = n ↔ (↑m : ℤ) = ↑n := by rw int.coe_nat_inj'

@[to_int]
lemma coe_nat_le {m n : ℕ} : m ≤ n ↔ (↑m : ℤ) ≤ ↑n := by rw int.coe_nat_le

@[to_int]
lemma coe_nat_lt {m n : ℕ} : m < n ↔ (↑m : ℤ) < ↑n := by rw int.coe_nat_lt

@[to_int]
lemma coe_nat_ge {m n : ℕ} : m ≥ n ↔ (↑m : ℤ) ≥ ↑n := coe_nat_le

@[to_int]
lemma coe_nat_gt {m n : ℕ} : m > n ↔ (↑m : ℤ) > ↑n := coe_nat_lt

@[to_int]
theorem coe_nat_dvd {m n : ℕ} : m ∣ n ↔ (↑m : ℤ) ∣ ↑n := by rw int.coe_nat_dvd

@[to_int]
theorem coe_bit0 {m : ℕ} : ↑ (bit0 m) = bit0 (↑m : ℤ) := by simp [bit0]

@[to_int]
theorem coe_bit1 {m : ℕ} : ↑ (bit1 m) = bit1 (↑m : ℤ) := by simp [bit1,bit0]

attribute [to_int] int.coe_nat_mod
  int.bit_coe_nat
  int.coe_nat_add int.coe_nat_mul
  int.coe_nat_sub
  int.coe_nat_zero
  int.coe_nat_one

meta def to_int : tactic unit :=
do `[simp only with to_int at *],
   ls ← local_context,
   ls ← ls.mfilter $ λ a,
     succeeds $ infer_type a >>= is_def_eq `(nat),
   ls ← ls.mmap $ λ v,
     do { tactic.revert v <*
          do e ← target,
             ((p,l),_) ← solve_aux e $ do {
               v ← intro1,
               p ← to_expr ``(↑ %%v : int),
               tactic.generalize p,
               (expr.pi n bi b d) ← target,
               pure (p,expr.lam n bi b d) } ,
             refine ``(translate_nat %%l _),
             intro v.local_pp_name,
             target >>= head_beta >>= unsafe_change,
             tactic.intro $ mk_simple_name $ to_string v.local_pp_name ++ "_nneg" },
   ls.reverse.mmap' $ λ i,
     do intron (i - 1),
        pure ()

end tactic.interactive
