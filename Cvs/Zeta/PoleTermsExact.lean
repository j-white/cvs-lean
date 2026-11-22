import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The pole terms, exactly

Splitting `ξ'/ξ` on the surviving vertical `Re = 2` by `Cvs.Zeta.logDeriv_riemannXi_eq_zeta`
produces four pieces: two poles, the archimedean factor, and `ζ'/ζ`.
-/

noncomputable section

open Complex MeasureTheory

namespace Cvs.ZeroCounting

/-- `Re 1/(a+iy) = a/(a²+y²)`. -/
theorem re_inv_line (a y : ℝ) :
    ((1 : ℂ) / ((a : ℂ) + (y : ℂ) * I)).re = a / (a ^ 2 + y ^ 2) := by
  rw [one_div, Complex.inv_re, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  ring_nf

/-- `arctan(y/a)` is an antiderivative of `a/(a²+y²)`. -/
theorem hasDerivAt_arctan_div {a : ℝ} (ha : 0 < a) (y : ℝ) :
    HasDerivAt (fun t : ℝ => Real.arctan (t / a)) (a / (a ^ 2 + y ^ 2)) y := by
  have h1 : HasDerivAt (fun t : ℝ => t / a) (1 / a) y := by
    simpa using (hasDerivAt_id y).div_const a
  have h2 := (Real.hasDerivAt_arctan (y / a)).comp y h1
  have hane : a ≠ 0 := ne_of_gt ha
  have hd : a ^ 2 + y ^ 2 ≠ 0 := by positivity
  have key : a / (a ^ 2 + y ^ 2) = 1 / (1 + (y / a) ^ 2) * (1 / a) := by
    have hsq : (1 : ℝ) + (y / a) ^ 2 = (a ^ 2 + y ^ 2) / a ^ 2 := by field_simp
    rw [hsq]
    field_simp
  rw [key]
  exact h2

/-- The real integral, exactly. -/
theorem integral_re_inv {a : ℝ} (ha : 0 < a) (T : ℝ) :
    (∫ y in (-T)..T, a / (a ^ 2 + y ^ 2)) = 2 * Real.arctan (T / a) := by
  have hpos : ∀ y : ℝ, a ^ 2 + y ^ 2 ≠ 0 := by
    intro y; positivity
  have hcont : Continuous fun y : ℝ => a / (a ^ 2 + y ^ 2) := by
    apply Continuous.div continuous_const (by fun_prop) hpos
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y _ => hasDerivAt_arctan_div ha y) (hcont.intervalIntegrable _ _)]
  rw [neg_div, Real.arctan_neg]
  ring

/-- **`Re ∫_{-T}^{T} dy/(a+iy) = 2·arctan(T/a)`.** -/
theorem re_integral_inv_line {a : ℝ} (ha : 0 < a) (T : ℝ) :
    (∫ y in (-T)..T, (1 : ℂ) / ((a : ℂ) + (y : ℂ) * I)).re
      = 2 * Real.arctan (T / a) := by
  have hne : ∀ y : ℝ, ((a : ℂ) + (y : ℂ) * I) ≠ 0 := by
    intro y hc
    have : ((a : ℂ) + (y : ℂ) * I).re = 0 := by rw [hc]; simp
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im] at this
    simp at this
    linarith
  have hcont : Continuous fun y : ℝ => (1 : ℂ) / ((a : ℂ) + (y : ℂ) * I) := by
    apply Continuous.div continuous_const (by fun_prop) hne
  have hcomm := ContinuousLinearMap.intervalIntegral_comp_comm Complex.reCLM
    (hcont.intervalIntegrable (μ := volume) (-T) T)
  simp only [Complex.reCLM_apply] at hcomm
  rw [← hcomm]
  simp_rw [re_inv_line a]
  exact integral_re_inv ha T

/-- The two poles of `ξ'/ξ` on the line `Re s = 2`: at `s = 0` the shift is `a = 2`, at
`s = 1` it is `a = 1`. -/
theorem re_integral_poles (T : ℝ) :
    (∫ y in (-T)..T, (1 : ℂ) / (((2 : ℝ) : ℂ) + (y : ℂ) * I)).re
        + (∫ y in (-T)..T, (1 : ℂ) / (((1 : ℝ) : ℂ) + (y : ℂ) * I)).re
      = 2 * Real.arctan (T / 2) + 2 * Real.arctan T := by
  rw [re_integral_inv_line (a := 2) (by norm_num) T,
    re_integral_inv_line (a := 1) (by norm_num) T]
  norm_num

end Cvs.ZeroCounting
