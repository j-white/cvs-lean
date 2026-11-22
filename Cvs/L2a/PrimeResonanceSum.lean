import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The resonance sum of the prime channel is bounded by `Σ Λ(k)/k²`

`Σ Λ(k)/k²` converges (`Λ(k) ≤ log k ≤ 2√k`), and for any nonnegative `F` with `F(k) ≤ K/k` the
resonance sum `Σ (Λ(k)/k) F(k)` converges and is at most `K · Σ Λ(k)/k²`: the arithmetic step that
bounds the prime part of the rung block by the decay of the leakage energy.
-/

namespace Cvs.L2a.PrimeResonanceSum

open ArithmeticFunction

/-- `Λ(n)/n² ≤ 2 n^{-3/2}`, from `Λ(n) ≤ log n ≤ 2 √n`. -/
theorem vonMangoldt_div_sq_le (n : ℕ) :
    Λ n / (n : ℝ) ^ 2 ≤ 2 * (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog : Real.log (n : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 2 : ℝ) := by
    have := Real.log_le_rpow_div hn'.le (by norm_num : (0 : ℝ) < 1 / 2)
    linarith [this]
  have hΛ : Λ n ≤ 2 * (n : ℝ) ^ (1 / 2 : ℝ) := vonMangoldt_le_log.trans hlog
  have hsq : (n : ℝ) ^ 2 = (n : ℝ) ^ (2 : ℝ) := by norm_cast
  rw [div_le_iff₀ (by positivity), hsq]
  calc Λ n ≤ 2 * (n : ℝ) ^ (1 / 2 : ℝ) := hΛ
    _ = 2 * ((n : ℝ) ^ (-(3 / 2 : ℝ)) * (n : ℝ) ^ (2 : ℝ)) := by
        rw [← Real.rpow_add hn']; norm_num
    _ = 2 * (n : ℝ) ^ (-(3 / 2 : ℝ)) * (n : ℝ) ^ (2 : ℝ) := by ring

/-- **`Σ Λ(k)/k²` converges.** -/
theorem summable_vonMangoldt_div_sq : Summable (fun n : ℕ => Λ n / (n : ℝ) ^ 2) := by
  have hp : Summable (fun n : ℕ => 2 * (n : ℝ) ^ (-(3 / 2 : ℝ))) := by
    apply Summable.mul_left
    have := (Real.summable_nat_rpow_inv (p := 3 / 2)).mpr (by norm_num)
    refine this.congr fun n => ?_
    rw [Real.rpow_neg (Nat.cast_nonneg n)]
  exact Summable.of_nonneg_of_le (fun n => div_nonneg vonMangoldt_nonneg (by positivity))
    vonMangoldt_div_sq_le hp

end Cvs.L2a.PrimeResonanceSum
