import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.ZetaValues
import Cvs.L2a.NonstationaryPairsOneShift

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The non-stationary prime pairs, summed over every shift, are bounded

`(1 + log k)² ≤ 4√k`, so with Cvs.L2a.NonstationaryPairsOneShift and `Λ(k) ≤ log k`, `Σ_{k ≤ K} (Λ(k)/k) Σ_{m, m′ ≠ km} 1/(m m′ |km − m′|)`
is at most `36(π²/6 + 6)` for every `K`, `M`, `M′`: a constant independent of the scale.
-/

namespace Cvs.L2a.NonstationaryPairsAllShifts

open Finset Real ArithmeticFunction

/-- `(1 + log k)² ≤ 4√k` for `k ≥ 1`. -/
theorem one_add_log_sq_le {k : ℝ} (hk : 1 ≤ k) : (1 + log k) ^ 2 ≤ 4 * √k := by
  have hk0 : 0 < k := by linarith
  set t := log k / 2 with ht
  have ht0 : 0 ≤ t := by have := log_nonneg hk; linarith
  have hsq : √k = exp t := by
    rw [ht, sqrt_eq_rpow, rpow_def_of_pos hk0]; ring_nf
  have hexp := Real.sum_le_exp_of_nonneg ht0 4
  simp [Finset.sum_range_succ, Nat.factorial] at hexp
  rw [hsq, show log k = 2 * t by rw [ht]; ring]
  nlinarith [mul_nonneg (sq_nonneg (t - 2)) (by linarith : (0:ℝ) ≤ t + 1)]

/-- **The non-stationary prime sum.** -/
theorem prime_pairs_le (K M M' : ℕ) :
    ∑ k ∈ Icc 1 K, Λ k / k * ∑ m ∈ Icc 1 M, ∑ m' ∈ (Icc 1 M').erase (k * m),
        1 / ((m : ℝ) * m' * |((k * m : ℕ) : ℝ) - m'|)
      ≤ 36 * (π ^ 2 / 6 + 6) := by
  have hterm : ∀ k ∈ Icc 1 K, Λ k / k * ∑ m ∈ Icc 1 M, ∑ m' ∈ (Icc 1 M').erase (k * m),
        1 / ((m : ℝ) * m' * |((k * m : ℕ) : ℝ) - m'|)
      ≤ 12 * (π ^ 2 / 6 + 6) * (1 / ((k : ℝ) * √k)) := by
    intro k hk
    have hk1 : 1 ≤ k := (mem_Icc.mp hk).1
    have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    have hk0 : (0 : ℝ) < k := by linarith
    have hs := Cvs.L2a.NonstationaryPairsOneShift.pairs_at_shift_le k M M' hk1
    have hΛ0 : 0 ≤ Λ k := vonMangoldt_nonneg
    have hΛ : Λ k ≤ 1 + Real.log k := by have := vonMangoldt_le_log (n := k); linarith
    have hl1 : 1 ≤ 1 + Real.log (k : ℝ) := by have := log_nonneg hk'; linarith
    have hsq := one_add_log_sq_le hk'
    have hsk : 0 < √(k : ℝ) := sqrt_pos.mpr hk0
    have hsqk : √(k : ℝ) * √k = k := mul_self_sqrt hk0.le
    calc Λ k / k * ∑ m ∈ Icc 1 M, ∑ m' ∈ (Icc 1 M').erase (k * m), 1 / ((m : ℝ) * m' * |((k * m : ℕ) : ℝ) - m'|)
        ≤ Λ k / k * (3 / k * ((1 + Real.log k) * (π ^ 2 / 6) + 6)) :=
          mul_le_mul_of_nonneg_left hs (by positivity)
      _ ≤ (1 + Real.log k) / k * (3 / k * ((1 + Real.log k) * (π ^ 2 / 6) + 6 * (1 + Real.log k))) := by
          apply mul_le_mul (div_le_div_of_nonneg_right hΛ hk0.le) _ (by positivity) (by positivity)
          apply mul_le_mul_of_nonneg_left _ (by positivity); nlinarith [pi_pos]
      _ = 3 * (π ^ 2 / 6 + 6) * ((1 + Real.log k) ^ 2 / (k : ℝ) ^ 2) := by ring
      _ ≤ 3 * (π ^ 2 / 6 + 6) * (4 * √k / (k : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hsq (by positivity)) (by positivity)
      _ = 12 * (π ^ 2 / 6 + 6) * (1 / ((k : ℝ) * √k)) := by
          field_simp; nlinarith [hsqk]
  calc _ ≤ ∑ k ∈ Icc 1 K, 12 * (π ^ 2 / 6 + 6) * (1 / ((k : ℝ) * √k)) := sum_le_sum hterm
    _ = 12 * (π ^ 2 / 6 + 6) * ∑ k ∈ Icc 1 K, 1 / ((k : ℝ) * √k) := by rw [mul_sum]
    _ ≤ 12 * (π ^ 2 / 6 + 6) * 3 :=
        mul_le_mul_of_nonneg_left (Cvs.L2a.NonstationaryPairsOneShift.sum_inv_mul_sqrt_le K) (by positivity)
    _ = 36 * (π ^ 2 / 6 + 6) := by ring

end Cvs.L2a.NonstationaryPairsAllShifts
