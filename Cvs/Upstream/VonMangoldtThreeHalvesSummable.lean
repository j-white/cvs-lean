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
# `Σ Λ(n)/n^{3/2}` converges

`Λ(n)/(n√n) ≤ 4 n^{-5/4}`, from `log n ≤ 4 n^{1/4}`.
-/

namespace Cvs.Upstream.VonMangoldtThreeHalvesSummable

open Real ArithmeticFunction

/-- `Λ(n)/(n√n) ≤ 4 n^{-5/4}`, from `log n ≤ 4 n^{1/4}`. -/
theorem vonMangoldt_div_pow_le (n : ℕ) :
    Λ n / ((n : ℝ) * √n) ≤ 4 * (n : ℝ) ^ (-(5 / 4 : ℝ)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog : Real.log (n : ℝ) ≤ 4 * (n : ℝ) ^ (1 / 4 : ℝ) := by
    have := Real.log_le_rpow_div hn'.le (by norm_num : (0 : ℝ) < 1 / 4)
    linarith [this]
  have hΛ : Λ n ≤ 4 * (n : ℝ) ^ (1 / 4 : ℝ) := vonMangoldt_le_log.trans hlog
  have hsq : (n : ℝ) * √n = (n : ℝ) ^ (3 / 2 : ℝ) := by
    rw [sqrt_eq_rpow, ← Real.rpow_one_add' hn'.le (by norm_num)]; norm_num
  rw [div_le_iff₀ (by positivity), hsq]
  calc Λ n ≤ 4 * (n : ℝ) ^ (1 / 4 : ℝ) := hΛ
    _ = 4 * ((n : ℝ) ^ (-(5 / 4 : ℝ)) * (n : ℝ) ^ (3 / 2 : ℝ)) := by
        rw [← Real.rpow_add hn']; norm_num
    _ = 4 * (n : ℝ) ^ (-(5 / 4 : ℝ)) * (n : ℝ) ^ (3 / 2 : ℝ) := by ring

/-- **`Σ Λ(n)/n^{3/2}` converges.** -/
theorem summable_vonMangoldt_div_pow : Summable (fun n : ℕ => Λ n / ((n : ℝ) * √n)) := by
  have hp : Summable (fun n : ℕ => 4 * (n : ℝ) ^ (-(5 / 4 : ℝ))) := by
    apply Summable.mul_left
    have := (Real.summable_nat_rpow_inv (p := 5 / 4)).mpr (by norm_num)
    refine this.congr fun n => ?_
    rw [Real.rpow_neg (Nat.cast_nonneg n)]
  exact Summable.of_nonneg_of_le (fun n => div_nonneg vonMangoldt_nonneg (by positivity))
    vonMangoldt_div_pow_le hp

end Cvs.Upstream.VonMangoldtThreeHalvesSummable
