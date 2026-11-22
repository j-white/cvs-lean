import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.ZetaValues
import Cvs.L2a.NearResonantPairHarmonic
import Cvs.L2a.NonresonantPairSum
import Cvs.L2a.NonstationaryPairsOneShift
import Cvs.L2a.StationaryPairsWeightedTotal

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Three mode counts for the tail's own cross terms

For `s > 0`: `Σ_{6n > s} 1/n² ≤ 3√(6/s)`; for `s ≥ 1`: `Σ_{6n ≤ s} 1/n ≤ 1 + log s`; and
`Σ_m Σ_{m' ≠ m} 1/(m m' |m − m'|) ≤ 3(π²/6 + 6)`, all uniformly in the number of modes.
-/

namespace Cvs.L2a.TailCrossModeCounts

open Real Finset

/-- **The edge modes**: `Σ_{6n > s} 1/n² ≤ 3√(6/s)`. -/
theorem edge_count (M : ℕ) {s : ℝ} (hs : 0 < s) :
    ∑ n ∈ Icc 1 M, (if s < 6 * (n : ℝ) then 1 / (n : ℝ) ^ 2 else 0) ≤ 3 * √(6 / s) := by
  have hterm : ∀ n ∈ Icc 1 M, (if s < 6 * (n : ℝ) then 1 / (n : ℝ) ^ 2 else 0) ≤ √(6 / s) * (1 / ((n : ℝ) * √n)) := by
    intro n hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (mem_Icc.mp hn).1
    have hn0 : (0 : ℝ) < n := by linarith
    have hsn : 0 < √(n : ℝ) := sqrt_pos.mpr hn0
    split_ifs with h
    · have h1 : 1 / (n : ℝ) < 6 / s := by rw [div_lt_div_iff₀ hn0 hs]; linarith
      have h2 : 1 / √(n : ℝ) ≤ √(6 / s) := by
        have : 1 / √(n : ℝ) = √(1 / n) := by rw [sqrt_div' 1 hn0.le, sqrt_one]
        rw [this]; exact Real.sqrt_le_sqrt h1.le
      have hnn : √(n : ℝ) * √n = n := mul_self_sqrt hn0.le
      calc 1 / (n : ℝ) ^ 2 = 1 / √(n : ℝ) * (1 / ((n : ℝ) * √n)) := by
            field_simp; linear_combination hnn
        _ ≤ √(6 / s) * (1 / ((n : ℝ) * √n)) := mul_le_mul_of_nonneg_right h2 (by positivity)
    · positivity
  calc _ ≤ ∑ n ∈ Icc 1 M, √(6 / s) * (1 / ((n : ℝ) * √n)) := sum_le_sum hterm
    _ = √(6 / s) * ∑ n ∈ Icc 1 M, 1 / ((n : ℝ) * √n) := by rw [mul_sum]
    _ ≤ √(6 / s) * 3 := mul_le_mul_of_nonneg_left (Cvs.L2a.NonstationaryPairsOneShift.sum_inv_mul_sqrt_le M) (sqrt_nonneg _)
    _ = 3 * √(6 / s) := by ring

/-- **The strip modes**: `Σ_{6n ≤ s} 1/n ≤ 1 + log s`. -/
theorem strip_harm (M : ℕ) {s : ℝ} (hs : 1 ≤ s) :
    ∑ n ∈ Icc 1 M, (if 6 * (n : ℝ) ≤ s then 1 / (n : ℝ) else 0) ≤ 1 + log s := by
  set N := ⌊s⌋₊ with hN
  have hs0 : 0 ≤ s := by linarith
  calc ∑ n ∈ Icc 1 M, (if 6 * (n : ℝ) ≤ s then 1 / (n : ℝ) else 0)
      = ∑ n ∈ (Icc 1 M).filter (fun n : ℕ => 6 * (n : ℝ) ≤ s), 1 / (n : ℝ) := by rw [sum_filter]
    _ ≤ ∑ n ∈ Icc 1 N, 1 / (n : ℝ) := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro n hn
          rw [mem_filter, mem_Icc] at hn
          have : (n : ℝ) ≤ s := by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
                                   linarith [hn.2]
          exact mem_Icc.mpr ⟨hn.1.1, Nat.le_floor this⟩
        · intro n _ _; positivity
    _ = Cvs.L2a.NearResonantPairHarmonic.H N := Cvs.L2a.StationaryPairsWeightedTotal.sum_Icc_inv N
    _ ≤ 1 + log N := Cvs.L2a.NearResonantPairHarmonic.H_le N
    _ ≤ 1 + log s := by
        rcases Nat.eq_zero_or_pos N with h0 | hpos
        · rw [h0]; simp; exact log_nonneg hs
        · have := log_le_log (by exact_mod_cast hpos) (Nat.floor_le hs0); linarith

/-- **The non-resonant pairs of one scale**: `Σ_m Σ_{m' ≠ m} 1/(m m'|m − m'|) ≤ 3(π²/6 + 6)`. -/
theorem nonres_double (M : ℕ) :
    ∑ m ∈ Icc 1 M, ∑ m' ∈ (Icc 1 M).erase m, 1 / ((m : ℝ) * m' * |(m : ℝ) - m'|) ≤ 3 * (π ^ 2 / 6 + 6) := by
  have hterm : ∀ m ∈ Icc 1 M, ∑ m' ∈ (Icc 1 M).erase m, 1 / ((m : ℝ) * m' * |(m : ℝ) - m'|)
      ≤ 3 * ((1 + log ((1 : ℕ) * m : ℝ)) / (m : ℝ) ^ 2) := by
    intro m hm
    have hm1 : 1 ≤ m := (mem_Icc.mp hm).1
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
    have e : ∀ m' ∈ (Icc 1 M).erase m, 1 / ((m : ℝ) * m' * |(m : ℝ) - m'|) = 1 / m * (1 / ((m' : ℝ) * |(m : ℝ) - m'|)) := by
      intro m' _; field_simp
    rw [sum_congr rfl e, ← mul_sum]
    have h := Cvs.L2a.NonresonantPairSum.nonresonant_le m M hm1
    calc 1 / (m : ℝ) * ∑ m' ∈ (Icc 1 M).erase m, 1 / ((m' : ℝ) * |(m : ℝ) - m'|)
        ≤ 1 / m * (3 * (1 + log m) / m) := mul_le_mul_of_nonneg_left h (by positivity)
      _ = 3 * ((1 + log ((1 : ℕ) * m : ℝ)) / (m : ℝ) ^ 2) := by push_cast; rw [one_mul]; field_simp
  calc _ ≤ ∑ m ∈ Icc 1 M, 3 * ((1 + log ((1 : ℕ) * m : ℝ)) / (m : ℝ) ^ 2) := sum_le_sum hterm
    _ = 3 * ∑ m ∈ Icc 1 M, (1 + log ((1 : ℕ) * m : ℝ)) / (m : ℝ) ^ 2 := by rw [mul_sum]
    _ ≤ 3 * ((1 + log ((1 : ℕ) : ℝ)) * (π ^ 2 / 6) + 6) :=
        mul_le_mul_of_nonneg_left (Cvs.L2a.NonstationaryPairsOneShift.sum_log_le 1 M le_rfl) (by norm_num)
    _ = 3 * (π ^ 2 / 6 + 6) := by simp

end Cvs.L2a.TailCrossModeCounts
