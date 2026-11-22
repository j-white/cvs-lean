import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Cvs.Upstream.GaussianSecondMoment
import Cvs.Upstream.PolyGaussianIntegrable

/-!
# The recursion, and `M₄`, `M₆`

`GaussianSecondMoment` did the case `n = 2` and observed that the same antiderivative works for every `n`.
-/

namespace Cvs.Moments

open MeasureTheory Filter Topology
open scoped Real

/-- The odd boundary term vanishes at `+∞`. -/
theorem tendsto_pow_gaussian {lam : ℝ} (hlam : 0 < lam) (m : ℕ) :
    Tendsto (fun y : ℝ => y ^ (2 * m + 1) * Real.exp (-lam * y ^ 2)) atTop (𝓝 0) := by
  have hb := Cvs.Moments.tendsto_gauss_half hlam
  have hc : Tendsto (fun y : ℝ =>
      (2 / lam) ^ (m + 1) * ((m + 1).factorial : ℝ)
        * Real.exp (-(lam / 2) * y ^ 2)) atTop (𝓝 0) := by
    have := hb.const_mul ((2 / lam) ^ (m + 1) * ((m + 1).factorial : ℝ))
    simpa using this
  refine squeeze_zero' ?_ ?_ hc
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with y hy
    positivity
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
    have hE : (0 : ℝ) < Real.exp (-lam * y ^ 2) := Real.exp_pos _
    have hp : y ^ (2 * m + 1) ≤ y ^ (2 * (m + 1)) := by
      refine pow_le_pow_right₀ hy ?_
      omega
    have h2 : y ^ (2 * m + 1) * Real.exp (-lam * y ^ 2)
        ≤ y ^ (2 * (m + 1)) * Real.exp (-lam * y ^ 2) :=
      mul_le_mul_of_nonneg_right hp hE.le
    have h3 := Cvs.Moments.pow_mul_exp_le hlam (m + 1) y
    have heq : Real.exp (-lam * y ^ 2 / 2) = Real.exp (-(lam / 2) * y ^ 2) := by
      congr 1; ring
    rw [heq] at h3
    linarith [h2, h3]

/-- **The recursion.** -/
theorem moment_rec {lam : ℝ} (hlam : 0 < lam) (m : ℕ) :
    (∫ y in Set.Ioi (0 : ℝ), y ^ (2 * m + 2) * Real.exp (-lam * y ^ 2))
      = ((2 * m + 1 : ℝ) / (2 * lam))
        * ∫ y in Set.Ioi (0 : ℝ), y ^ (2 * m) * Real.exp (-lam * y ^ 2) := by
  have hlne : lam ≠ 0 := ne_of_gt hlam
  set f : ℝ → ℝ :=
    fun y => -(y ^ (2 * m + 1) * Real.exp (-lam * y ^ 2)) / (2 * lam) with hf
  have hderiv : ∀ y ∈ Set.Ici (0 : ℝ), HasDerivAt f
      (y ^ (2 * m + 2) * Real.exp (-lam * y ^ 2)
        - ((2 * m + 1 : ℝ) / (2 * lam)) * (y ^ (2 * m) * Real.exp (-lam * y ^ 2))) y := by
    intro y _
    have h1 : HasDerivAt (fun t : ℝ => -lam * t ^ 2) (-lam * (2 * y)) y := by
      simpa using ((hasDerivAt_pow 2 y).const_mul (-lam))
    have h2 : HasDerivAt (fun t : ℝ => Real.exp (-lam * t ^ 2))
        (Real.exp (-lam * y ^ 2) * (-lam * (2 * y))) y := h1.exp
    have hp : HasDerivAt (fun t : ℝ => t ^ (2 * m + 1))
        (((2 * m + 1 : ℕ) : ℝ) * y ^ (2 * m)) y := by
      simpa using hasDerivAt_pow (2 * m + 1) y
    have h3 := hp.mul h2
    have h4 := (h3.neg).div_const (2 * lam)
    have hval : -(((2 * m + 1 : ℕ) : ℝ) * y ^ (2 * m) * Real.exp (-lam * y ^ 2)
          + y ^ (2 * m + 1) * (Real.exp (-lam * y ^ 2) * (-lam * (2 * y)))) / (2 * lam)
        = y ^ (2 * m + 2) * Real.exp (-lam * y ^ 2)
          - ((2 * m + 1 : ℝ) / (2 * lam)) * (y ^ (2 * m) * Real.exp (-lam * y ^ 2)) := by
      have hpow : y ^ (2 * m + 1) * y = y ^ (2 * m + 2) := by ring
      push_cast
      field_simp
      nlinarith [hpow, sq_nonneg y]
    rw [hval] at h4
    exact h4
  have hIA : Integrable (fun y : ℝ => y ^ (2 * m + 2) * Real.exp (-lam * y ^ 2)) := by
    have := Cvs.Moments.integrable_pow_mul_gaussian hlam (m + 1)
    have heq : 2 * (m + 1) = 2 * m + 2 := by omega
    rwa [heq] at this
  have hIB : Integrable (fun y : ℝ =>
      ((2 * m + 1 : ℝ) / (2 * lam)) * (y ^ (2 * m) * Real.exp (-lam * y ^ 2))) :=
    (Cvs.Moments.integrable_pow_mul_gaussian hlam m).const_mul _
  have hint : IntegrableOn (fun y : ℝ =>
      y ^ (2 * m + 2) * Real.exp (-lam * y ^ 2)
        - ((2 * m + 1 : ℝ) / (2 * lam)) * (y ^ (2 * m) * Real.exp (-lam * y ^ 2)))
      (Set.Ioi (0 : ℝ)) := (hIA.sub hIB).integrableOn
  have hlim : Tendsto f atTop (𝓝 0) := by
    have := (tendsto_pow_gaussian hlam m).neg.div_const (2 * lam)
    simpa [hf] using this
  have hkey := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hlim
  have hf0 : f 0 = 0 := by simp [hf]
  rw [hf0, sub_zero] at hkey
  rw [integral_sub hIA.integrableOn hIB.integrableOn, integral_const_mul] at hkey
  linarith [hkey]

end Cvs.Moments
