import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.ZetaValues
import Cvs.L2a.NonresonantPairSum

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The non-stationary prime pairs at one shift `k` sum to `O((1 + log k)/(c² k))`

`Σ_{m ≤ M} Σ_{m′ ≤ M′, m′ ≠ km} 1/(m m′ |km − m′|) ≤ (3/k)((1 + log k)π²/6 + 6)`, from Cvs.L2a.NonresonantPairSum over `m′`, then
`log m ≤ 2√m`, `Σ 1/m² ≤ π²/6` and `Σ m^{−3/2} ≤ 3` over `m`.
-/

namespace Cvs.L2a.NonstationaryPairsOneShift

open Finset Real

/-- `1/(m√m) ≤ 2(1/√(m−1) − 1/√m)` for `m ≥ 2`. -/
theorem inv_mul_sqrt_le {m : ℝ} (hm : 2 ≤ m) :
    1 / (m * √m) ≤ 2 * (1 / √(m - 1) - 1 / √m) := by
  have h1 : 0 < √(m - 1) := sqrt_pos.mpr (by linarith)
  have h2 : 0 < √m := sqrt_pos.mpr (by linarith)
  have hle : √(m - 1) ≤ √m := sqrt_le_sqrt (by linarith)
  have hsq1 : √(m - 1) ^ 2 = m - 1 := sq_sqrt (by linarith)
  have hsq2 : √m ^ 2 = m := sq_sqrt (by linarith)
  -- 1/√(m−1) − 1/√m = 1/(√m √(m−1)(√m + √(m−1)))
  have e : 1 / √(m - 1) - 1 / √m = 1 / (√m * √(m - 1) * (√m + √(m - 1))) := by
    field_simp; nlinarith [hsq1, hsq2]
  rw [e, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have : √m * √(m - 1) * (√m + √(m - 1)) ≤ √m * √m * (√m + √m) := by
    apply mul_le_mul (mul_le_mul_of_nonneg_left hle h2.le) (by linarith) (by positivity) (by positivity)
  nlinarith [hsq2]

theorem sum_inv_mul_sqrt_aux (M : ℕ) (hM : 1 ≤ M) :
    ∑ m ∈ Icc 1 M, 1 / ((m : ℝ) * √m) ≤ 3 - 2 / √M := by
  induction M, hM using Nat.le_induction with
  | base => simp; norm_num
  | succ M hM ih =>
    rw [sum_Icc_succ_top (by omega)]
    have hM' : (2 : ℝ) ≤ ((M + 1 : ℕ) : ℝ) := by push_cast; exact_mod_cast (by omega : 2 ≤ M + 1)
    have h := inv_mul_sqrt_le hM'
    have e : ((M + 1 : ℕ) : ℝ) - 1 = M := by push_cast; ring
    rw [e] at h
    push_cast at h ⊢
    have e2 : 2 * (1 / √(M : ℝ) - 1 / √((M : ℝ) + 1)) = 2 / √(M : ℝ) - 2 / √((M : ℝ) + 1) := by ring
    linarith

/-- **`Σ_{m=1}^{M} 1/(m√m) ≤ 3`.** -/
theorem sum_inv_mul_sqrt_le (M : ℕ) : ∑ m ∈ Icc 1 M, 1 / ((m : ℝ) * √m) ≤ 3 := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp
  · have := sum_inv_mul_sqrt_aux M hM
    have : 0 ≤ 2 / √(M : ℝ) := by positivity
    linarith

/-- **`Σ_{m=1}^{M} 1/m² ≤ π²/6`.** -/
theorem sum_inv_sq_le (M : ℕ) : ∑ m ∈ Icc 1 M, 1 / (m : ℝ) ^ 2 ≤ π ^ 2 / 6 := by
  calc ∑ m ∈ Icc 1 M, 1 / (m : ℝ) ^ 2 ≤ ∑ m ∈ range (M + 1), 1 / (m : ℝ) ^ 2 := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro m hm; simp only [mem_Icc] at hm; simp only [mem_range]; omega
        · intro _ _ _; positivity
    _ ≤ π ^ 2 / 6 := sum_le_hasSum _ (fun _ _ => by positivity) hasSum_zeta_two

/-- **The `m`-sum**: `Σ_{m=1}^{M} (1 + log(km))/m² ≤ (1 + log k)π²/6 + 6` for `k ≥ 1`. -/
theorem sum_log_le (k M : ℕ) (hk : 1 ≤ k) :
    ∑ m ∈ Icc 1 M, (1 + log ((k : ℝ) * m)) / (m : ℝ) ^ 2 ≤ (1 + log k) * (π ^ 2 / 6) + 6 := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hterm : ∀ m ∈ Icc 1 M, (1 + log ((k : ℝ) * m)) / (m : ℝ) ^ 2
      ≤ (1 + log k) * (1 / (m : ℝ) ^ 2) + 2 * (1 / ((m : ℝ) * √m)) := by
    intro m hm
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (mem_Icc.mp hm).1
    have hm0 : (0 : ℝ) < m := by linarith
    rw [log_mul hk'.ne' hm0.ne']
    have hlog : log (m : ℝ) ≤ 2 * √m := by
      have := Real.log_le_rpow_div hm0.le (by norm_num : (0 : ℝ) < 1 / 2)
      rw [← sqrt_eq_rpow] at this; linarith
    have hsq : √(m : ℝ) * √m = m := mul_self_sqrt hm0.le
    have hs : 0 < √(m : ℝ) := sqrt_pos.mpr hm0
    have e : 2 * √(m : ℝ) / (m : ℝ) ^ 2 = 2 * (1 / ((m : ℝ) * √m)) := by
      field_simp; nlinarith [hsq]
    calc (1 + (log k + log m)) / (m : ℝ) ^ 2 = (1 + log k) * (1 / (m : ℝ) ^ 2) + log m / (m : ℝ) ^ 2 := by ring
      _ ≤ (1 + log k) * (1 / (m : ℝ) ^ 2) + 2 * √(m : ℝ) / (m : ℝ) ^ 2 := by
          gcongr
      _ = _ := by rw [e]
  have hlk : 0 ≤ 1 + log (k : ℝ) := by have := log_nonneg (show (1 : ℝ) ≤ k by exact_mod_cast hk); linarith
  calc _ ≤ ∑ m ∈ Icc 1 M, ((1 + log k) * (1 / (m : ℝ) ^ 2) + 2 * (1 / ((m : ℝ) * √m))) := sum_le_sum hterm
    _ = (1 + log k) * ∑ m ∈ Icc 1 M, 1 / (m : ℝ) ^ 2 + 2 * ∑ m ∈ Icc 1 M, 1 / ((m : ℝ) * √m) := by
        rw [sum_add_distrib, ← mul_sum, ← mul_sum]
    _ ≤ (1 + log k) * (π ^ 2 / 6) + 2 * 3 :=
        add_le_add (mul_le_mul_of_nonneg_left (sum_inv_sq_le M) hlk)
          (mul_le_mul_of_nonneg_left (sum_inv_mul_sqrt_le M) (by norm_num))
    _ = (1 + log k) * (π ^ 2 / 6) + 6 := by ring

/-- **The non-stationary pairs at shift `k`**:
`Σ_{m ≤ M} Σ_{m′ ∈ [1, M′], m′ ≠ km} 1/(m m′ |km − m′|) ≤ (3/k)((1 + log k)π²/6 + 6)`. -/
theorem pairs_at_shift_le (k M M' : ℕ) (hk : 1 ≤ k) :
    ∑ m ∈ Icc 1 M, ∑ m' ∈ (Icc 1 M').erase (k * m),
        1 / ((m : ℝ) * m' * |((k * m : ℕ) : ℝ) - m'|)
      ≤ 3 / k * ((1 + log k) * (π ^ 2 / 6) + 6) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hinner : ∀ m ∈ Icc 1 M, ∑ m' ∈ (Icc 1 M').erase (k * m), 1 / ((m : ℝ) * m' * |((k * m : ℕ) : ℝ) - m'|)
      ≤ 3 / k * ((1 + log ((k : ℝ) * m)) / (m : ℝ) ^ 2) := by
    intro m hm
    have hm1 : 1 ≤ m := (mem_Icc.mp hm).1
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
    have hkm : 1 ≤ k * m := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have h := Cvs.L2a.NonresonantPairSum.nonresonant_le (k * m) M' hkm
    calc ∑ m' ∈ (Icc 1 M').erase (k * m), 1 / ((m : ℝ) * m' * |((k * m : ℕ) : ℝ) - m'|)
        = 1 / (m : ℝ) * ∑ m' ∈ (Icc 1 M').erase (k * m), 1 / ((m' : ℝ) * |((k * m : ℕ) : ℝ) - m'|) := by
          rw [mul_sum]; apply sum_congr rfl; intro m' _; field_simp
      _ ≤ 1 / (m : ℝ) * (3 * (1 + log ((k * m : ℕ) : ℝ)) / ((k * m : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = 3 / k * ((1 + log ((k : ℝ) * m)) / (m : ℝ) ^ 2) := by
          push_cast; field_simp
  calc _ ≤ ∑ m ∈ Icc 1 M, 3 / k * ((1 + log ((k : ℝ) * m)) / (m : ℝ) ^ 2) := sum_le_sum hinner
    _ = 3 / k * ∑ m ∈ Icc 1 M, (1 + log ((k : ℝ) * m)) / (m : ℝ) ^ 2 := by rw [mul_sum]
    _ ≤ 3 / k * ((1 + log k) * (π ^ 2 / 6) + 6) :=
        mul_le_mul_of_nonneg_left (sum_log_le k M hk) (by positivity)

end Cvs.L2a.NonstationaryPairsOneShift
