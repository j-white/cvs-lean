import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The elementary Lévy integral

    ∫₀^∞ (1 − cos ωu) e^{−cu} du = ω² / (c(c² + ω²)),   c > 0

`Cvs.WeilForm.PoleFunctionalModeClosedForm`'s antiderivative pattern, on a half-line and with a decaying exponential.  This is the
one integral that turns a digamma deficit into a Lévy measure.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Real MeasureTheory Set Filter Topology

namespace Cvs.WeilForm.Archimedean.ElementaryLevyIntegral

variable {c ω : ℝ}

/-- The antiderivative of `(1 − cos ωx) e^{−cx}`. -/
def antideriv (c ω x : ℝ) : ℝ :=
  Real.exp (-(c * x))
    * (-(1 / c) + (c * Real.cos (ω * x) - ω * Real.sin (ω * x)) / (c ^ 2 + ω ^ 2))

/-- **It is one.** -/
theorem hasDerivAt_antideriv (hc : 0 < c) (ω x : ℝ) :
    HasDerivAt (antideriv c ω) ((1 - Real.cos (ω * x)) * Real.exp (-(c * x))) x := by
  have hd : (0:ℝ) < c ^ 2 + ω ^ 2 := by positivity
  have hE : HasDerivAt (fun y : ℝ => Real.exp (-(c * y))) (-c * Real.exp (-(c * x))) x := by
    have h1 : HasDerivAt (fun y : ℝ => -(c * y)) (-c) x := by
      have h0 : HasDerivAt (fun y : ℝ => -c * y) (-c * 1) x := (hasDerivAt_id x).const_mul (-c)
      simpa [neg_mul] using h0
    exact h1.exp.congr_deriv (by ring)
  have hcos : HasDerivAt (fun y : ℝ => c * Real.cos (ω * y))
      (c * (-(ω * Real.sin (ω * x)))) x :=
    ((((hasDerivAt_id x).const_mul ω).cos).congr_deriv
      (by simp only [id_eq]; ring)).const_mul c
  have hsin : HasDerivAt (fun y : ℝ => ω * Real.sin (ω * y))
      (ω * (ω * Real.cos (ω * x))) x :=
    ((((hasDerivAt_id x).const_mul ω).sin).congr_deriv
      (by simp only [id_eq]; ring)).const_mul ω
  have hP : HasDerivAt
      (fun y : ℝ => -(1 / c) + (c * Real.cos (ω * y) - ω * Real.sin (ω * y)) / (c ^ 2 + ω ^ 2))
      ((c * (-(ω * Real.sin (ω * x))) - ω * (ω * Real.cos (ω * x))) / (c ^ 2 + ω ^ 2)) x :=
    (((hcos.sub hsin).div_const (c ^ 2 + ω ^ 2)).const_add _)
  have hprod := hE.mul hP
  refine hprod.congr_deriv ?_
  have hcne : c ≠ 0 := ne_of_gt hc
  field_simp
  ring

/-- The integrand is dominated by `2 e^{−cx}`, hence integrable on the half-line. -/
theorem integrableOn (hc : 0 < c) (ω : ℝ) :
    IntegrableOn (fun x => (1 - Real.cos (ω * x)) * Real.exp (-(c * x))) (Ioi 0) := by
  have hdom : IntegrableOn (fun x : ℝ => 2 * Real.exp (-c * x)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 hc).const_mul 2
  refine Integrable.mono' hdom ?_ ?_
  · exact (Continuous.aestronglyMeasurable (by fun_prop)).restrict
  · refine Filter.Eventually.of_forall fun x => ?_
    have hcos : |1 - Real.cos (ω * x)| ≤ 2 := by
      have := Real.neg_one_le_cos (ω * x)
      have := Real.cos_le_one (ω * x)
      rw [abs_le]; constructor <;> linarith
    have hE : (0:ℝ) < Real.exp (-(c * x)) := Real.exp_pos _
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hE, show -c * x = -(c * x) by ring]
    exact mul_le_mul_of_nonneg_right hcos hE.le

/-- The antiderivative dies at infinity: a bounded factor against `e^{−cx}`. -/
theorem tendsto_antideriv (hc : 0 < c) (ω : ℝ) :
    Tendsto (antideriv c ω) atTop (𝓝 0) := by
  have hd : (0:ℝ) < c ^ 2 + ω ^ 2 := by positivity
  set M : ℝ := 1 / c + (|c| + |ω|) / (c ^ 2 + ω ^ 2) with hM
  have hbound : ∀ x, ‖antideriv c ω x‖ ≤ M * Real.exp (-(c * x)) := by
    intro x
    have hE : (0:ℝ) < Real.exp (-(c * x)) := Real.exp_pos _
    have hP : |(-(1 / c) + (c * Real.cos (ω * x) - ω * Real.sin (ω * x)) / (c ^ 2 + ω ^ 2))|
        ≤ M := by
      have h1 : |(-(1 / c) : ℝ)| = 1 / c := by
        rw [abs_neg, abs_of_pos (by positivity)]
      have hnum : |c * Real.cos (ω * x) - ω * Real.sin (ω * x)| ≤ |c| + |ω| := by
        have hcA : |c * Real.cos (ω * x)| ≤ |c| := by
          rw [abs_mul]
          nlinarith [Real.abs_cos_le_one (ω * x), abs_nonneg c, abs_nonneg (Real.cos (ω * x))]
        have hsB : |ω * Real.sin (ω * x)| ≤ |ω| := by
          rw [abs_mul]
          nlinarith [Real.abs_sin_le_one (ω * x), abs_nonneg ω, abs_nonneg (Real.sin (ω * x))]
        have htri : |c * Real.cos (ω * x) - ω * Real.sin (ω * x)|
            ≤ |c * Real.cos (ω * x)| + |ω * Real.sin (ω * x)| := by
          simpa [Real.norm_eq_abs] using
            norm_sub_le (c * Real.cos (ω * x)) (ω * Real.sin (ω * x))
        linarith
      have h2 : |(c * Real.cos (ω * x) - ω * Real.sin (ω * x)) / (c ^ 2 + ω ^ 2)|
          ≤ (|c| + |ω|) / (c ^ 2 + ω ^ 2) := by
        rw [abs_div, abs_of_pos hd]
        exact div_le_div_of_nonneg_right hnum hd.le
      have htri2 : |(-(1 / c) + (c * Real.cos (ω * x) - ω * Real.sin (ω * x)) / (c ^ 2 + ω ^ 2))|
          ≤ |(-(1 / c) : ℝ)|
            + |(c * Real.cos (ω * x) - ω * Real.sin (ω * x)) / (c ^ 2 + ω ^ 2)| := by
        simpa [Real.norm_eq_abs] using
          norm_add_le (-(1 / c) : ℝ)
            ((c * Real.cos (ω * x) - ω * Real.sin (ω * x)) / (c ^ 2 + ω ^ 2))
      rw [hM]; linarith
    rw [Real.norm_eq_abs, antideriv, abs_mul, abs_of_pos hE, mul_comm]
    exact mul_le_mul_of_nonneg_right hP hE.le
  refine squeeze_zero_norm hbound ?_
  have : Tendsto (fun x : ℝ => Real.exp (-(c * x))) atTop (𝓝 0) := by
    have hmul : Tendsto (fun x : ℝ => c * x) atTop atTop :=
      Filter.Tendsto.const_mul_atTop hc tendsto_id
    exact Real.tendsto_exp_neg_atTop_nhds_zero.comp hmul
  simpa using this.const_mul M

/-- **The Lévy integral, in closed form.** -/
theorem integral_one_sub_cos_mul_exp (hc : 0 < c) (ω : ℝ) :
    (∫ x in Ioi (0:ℝ), (1 - Real.cos (ω * x)) * Real.exp (-(c * x)))
      = ω ^ 2 / (c * (c ^ 2 + ω ^ 2)) := by
  have hd : (0:ℝ) < c ^ 2 + ω ^ 2 := by positivity
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (f := antideriv c ω) (f' := fun x => (1 - Real.cos (ω * x)) * Real.exp (-(c * x)))
    (m := 0) (a := 0)
    (fun x _ => hasDerivAt_antideriv hc ω x) (integrableOn hc ω) (tendsto_antideriv hc ω)
  rw [h, antideriv]
  have hcne : c ≠ 0 := ne_of_gt hc
  simp only [mul_zero, Real.exp_zero, Real.cos_zero, Real.sin_zero, neg_zero, one_mul,
    mul_one, mul_zero, sub_zero]
  field_simp
  ring

end Cvs.WeilForm.Archimedean.ElementaryLevyIntegral
