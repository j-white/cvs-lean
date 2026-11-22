import Mathlib
import Cvs.Zeta.Digamma
import Cvs.Zeta.DigammaStrip
import Cvs.Zeta.GammaRLogDeriv

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The archimedean integrand decays on the strip
-/

namespace Cvs.Detection

open Complex
open scoped Real

/-- On the strip `½ ≤ Re z ≤ 2` the log-derivative of `Γ_ℝ` is `O(log|Im z|)`. -/
theorem logDeriv_gammaR_strip_bound :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ z : ℂ, 1 / 2 ≤ z.re → z.re ≤ 2 → 2 ≤ |z.im| →
      ‖logDeriv Gammaℝ z‖ ≤ D * (1 + Real.log (2 + |z.im|)) := by
  obtain ⟨C, hC, hbd⟩ := Cvs.Zeta.exists_norm_digamma_le_strip (1 / 4) 1
  refine ⟨|Real.log π| / 2 + C / 2, by positivity, fun z h1 h2 h3 => ?_⟩
  have hre : (0 : ℝ) < z.re := by linarith
  have hne : ∀ m : ℕ, z / 2 ≠ -m := by
    intro m
    refine Cvs.Zeta.ne_neg_nat_of_re_pos ?_ m
    simp only [Complex.div_re]
    simp
    linarith
  have hhalf : ((z / 2).re) = z.re / 2 := by simp
  have himhalf : ((z / 2).im) = z.im / 2 := by simp
  have hpsi : ‖Complex.digamma (z / 2)‖ ≤ C * (1 + Real.log (2 + |(z / 2).im|)) := by
    refine hbd (z / 2) (by rw [hhalf]; linarith) (by rw [hhalf]; linarith) ?_
    rw [himhalf, abs_div]
    simp only [abs_two]
    linarith
  have hmono : Real.log (2 + |(z / 2).im|) ≤ Real.log (2 + |z.im|) := by
    refine Real.log_le_log (by positivity) ?_
    rw [himhalf, abs_div]
    simp only [abs_two]
    linarith [abs_nonneg z.im]
  have hlogpos : (0 : ℝ) ≤ Real.log (2 + |z.im|) :=
    Real.log_nonneg (by linarith [abs_nonneg z.im])
  have hlogre : ‖Complex.log ((π : ℝ) : ℂ)‖ = |Real.log π| := by
    rw [← Complex.ofReal_log Real.pi_pos.le, Complex.norm_real, Real.norm_eq_abs]
  rw [Cvs.Zeta.logDeriv_gammaR hne]
  have h1 : ‖-(Complex.log ((π : ℝ) : ℂ)) / 2 + Complex.digamma (z / 2) / 2‖
      ≤ ‖Complex.log ((π : ℝ) : ℂ)‖ / 2 + ‖Complex.digamma (z / 2)‖ / 2 := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_div, norm_div, norm_neg, Complex.norm_ofNat]
  refine h1.trans ?_
  rw [hlogre]
  nlinarith [hpsi, hmono, hlogpos, hC, abs_nonneg (Real.log π)]

end Cvs.Detection
