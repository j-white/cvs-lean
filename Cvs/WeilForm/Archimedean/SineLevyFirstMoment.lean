import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The sine Lévy integral and the first moment, in closed form

    ∫₀^∞ sin(ωx)·e^{−cx} dx = ω/(c²+ω²),    ∫₀^∞ x·e^{−cx} dx = 1/c²

The sine changes sign, so the interchange downstream is dominated not monotone, and
`|sin x| ≤ |x|` against the second integral is what makes the majorant summable.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Real MeasureTheory Set Filter Topology

namespace Cvs.WeilForm.Archimedean.SineLevyFirstMoment

variable {c ω : ℝ}

/-- The antiderivative of `sin(ωx)·e^{−cx}`. -/
def antiderivSin (c ω x : ℝ) : ℝ :=
  Real.exp (-(c * x)) * (-(c * Real.sin (ω * x) + ω * Real.cos (ω * x)) / (c ^ 2 + ω ^ 2))

/-- **It is one.** -/
theorem hasDerivAt_antiderivSin (hc : 0 < c) (ω x : ℝ) :
    HasDerivAt (antiderivSin c ω) (Real.sin (ω * x) * Real.exp (-(c * x))) x := by
  have hd : (0:ℝ) < c ^ 2 + ω ^ 2 := by positivity
  have hE : HasDerivAt (fun y : ℝ => Real.exp (-(c * y))) (-c * Real.exp (-(c * x))) x := by
    have h1 : HasDerivAt (fun y : ℝ => -(c * y)) (-c) x := by
      have h0 : HasDerivAt (fun y : ℝ => -c * y) (-c * 1) x := (hasDerivAt_id x).const_mul (-c)
      simpa [neg_mul] using h0
    exact h1.exp.congr_deriv (by ring)
  have hsin : HasDerivAt (fun y : ℝ => c * Real.sin (ω * y))
      (c * (ω * Real.cos (ω * x))) x :=
    ((((hasDerivAt_id x).const_mul ω).sin).congr_deriv
      (by simp only [id_eq]; ring)).const_mul c
  have hcos : HasDerivAt (fun y : ℝ => ω * Real.cos (ω * y))
      (ω * (-(ω * Real.sin (ω * x)))) x :=
    ((((hasDerivAt_id x).const_mul ω).cos).congr_deriv
      (by simp only [id_eq]; ring)).const_mul ω
  have hP : HasDerivAt
      (fun y : ℝ => -(c * Real.sin (ω * y) + ω * Real.cos (ω * y)) / (c ^ 2 + ω ^ 2))
      (-(c * (ω * Real.cos (ω * x)) + ω * (-(ω * Real.sin (ω * x)))) / (c ^ 2 + ω ^ 2)) x :=
    ((hsin.add hcos).neg).div_const (c ^ 2 + ω ^ 2)
  have hprod := hE.mul hP
  refine hprod.congr_deriv ?_
  have hne : (c ^ 2 + ω ^ 2) ≠ 0 := ne_of_gt hd
  field_simp
  ring

/-- The integrand is dominated by `e^{−cx}`. -/
theorem integrableOnSin (hc : 0 < c) (ω : ℝ) :
    IntegrableOn (fun x => Real.sin (ω * x) * Real.exp (-(c * x))) (Ioi 0) := by
  have hdom : IntegrableOn (fun x : ℝ => 2 * Real.exp (-c * x)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 hc).const_mul 2
  refine Integrable.mono' hdom ?_ ?_
  · exact (Continuous.aestronglyMeasurable (by fun_prop)).restrict
  · refine Filter.Eventually.of_forall fun x => ?_
    have hE : (0:ℝ) < Real.exp (-(c * x)) := Real.exp_pos _
    have hs1 : |Real.sin (ω * x)| ≤ 2 := (Real.abs_sin_le_one _).trans (by norm_num)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hE, show -c * x = -(c * x) by ring]
    exact mul_le_mul_of_nonneg_right hs1 hE.le

/-- The antiderivative dies at infinity. -/
theorem tendsto_antiderivSin (hc : 0 < c) (ω : ℝ) :
    Tendsto (antiderivSin c ω) atTop (𝓝 0) := by
  have hd : (0:ℝ) < c ^ 2 + ω ^ 2 := by positivity
  set M : ℝ := (|c| + |ω|) / (c ^ 2 + ω ^ 2) with hM
  have hbdd : ∀ x : ℝ, |antiderivSin c ω x| ≤ Real.exp (-(c * x)) * M := by
    intro x
    have hE : (0:ℝ) < Real.exp (-(c * x)) := Real.exp_pos _
    have hnum : |c * Real.sin (ω * x) + ω * Real.cos (ω * x)| ≤ |c| + |ω| := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul]
      have h1 := Real.abs_sin_le_one (ω * x)
      have h2 := Real.abs_cos_le_one (ω * x)
      nlinarith [abs_nonneg c, abs_nonneg ω]
    rw [antiderivSin, abs_mul, abs_of_pos hE, abs_div, abs_neg, abs_of_pos hd, hM]
    exact mul_le_mul_of_nonneg_left (by
      rw [div_le_div_iff_of_pos_right hd]; exact hnum) hE.le
  have hz : Tendsto (fun x : ℝ => Real.exp (-(c * x)) * M) atTop (𝓝 0) := by
    have hmul : Tendsto (fun x : ℝ => c * x) atTop atTop :=
      Filter.Tendsto.const_mul_atTop hc tendsto_id
    have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp hmul).mul_const M
    simpa using this
  exact squeeze_zero_norm (fun x => by simpa [Real.norm_eq_abs] using hbdd x) hz

/-- **The sine Lévy integral, in closed form.** -/
theorem integral_sin_mul_exp (hc : 0 < c) (ω : ℝ) :
    (∫ x in Ioi (0:ℝ), Real.sin (ω * x) * Real.exp (-(c * x)))
      = ω / (c ^ 2 + ω ^ 2) := by
  have hd : (0:ℝ) < c ^ 2 + ω ^ 2 := by positivity
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (f := antiderivSin c ω) (f' := fun x => Real.sin (ω * x) * Real.exp (-(c * x)))
    (m := 0) (a := 0)
    (fun x _ => hasDerivAt_antiderivSin hc ω x) (integrableOnSin hc ω)
    (tendsto_antiderivSin hc ω)
  rw [h, antiderivSin]
  simp only [mul_zero, Real.exp_zero, Real.cos_zero, Real.sin_zero, neg_zero, mul_one,
    mul_zero, zero_add, zero_sub]
  field_simp

/-! ### The first moment, for the summable majorant -/

/-- The antiderivative of `x·e^{−cx}`. -/
def antiderivId (c x : ℝ) : ℝ := Real.exp (-(c * x)) * (-(x / c) - 1 / c ^ 2)

theorem hasDerivAt_antiderivId (hc : 0 < c) (x : ℝ) :
    HasDerivAt (antiderivId c) (x * Real.exp (-(c * x))) x := by
  have hcne : c ≠ 0 := ne_of_gt hc
  have hE : HasDerivAt (fun y : ℝ => Real.exp (-(c * y))) (-c * Real.exp (-(c * x))) x := by
    have h1 : HasDerivAt (fun y : ℝ => -(c * y)) (-c) x := by
      have h0 : HasDerivAt (fun y : ℝ => -c * y) (-c * 1) x := (hasDerivAt_id x).const_mul (-c)
      simpa [neg_mul] using h0
    exact h1.exp.congr_deriv (by ring)
  have hP : HasDerivAt (fun y : ℝ => -(y / c) - 1 / c ^ 2) (-(1 / c)) x := by
    have h := ((hasDerivAt_id x).div_const c).neg
    simpa using h.sub_const (1 / c ^ 2)
  refine (hE.mul hP).congr_deriv ?_
  field_simp
  ring

theorem integrableOnId (hc : 0 < c) :
    IntegrableOn (fun x => x * Real.exp (-(c * x))) (Ioi 0) := by
  have hc2 : (0:ℝ) < c / 2 := by linarith
  have hdom : IntegrableOn (fun x : ℝ => (2 / c) * Real.exp (-(c / 2) * x)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 hc2).const_mul (2 / c)
  refine Integrable.mono' hdom ?_ ?_
  · exact (Continuous.aestronglyMeasurable (by fun_prop)).restrict
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun x hx => ?_)
    have hx0 : (0:ℝ) < x := hx
    have hy : (c / 2) * x ≤ Real.exp ((c / 2) * x) := by
      have := Real.add_one_le_exp ((c / 2) * x); linarith
    have hxle : x ≤ (2 / c) * Real.exp ((c / 2) * x) := by
      have hcne : c ≠ 0 := ne_of_gt hc
      have hkey : (2 / c) * Real.exp ((c / 2) * x) - x
          = (2 / c) * (Real.exp ((c / 2) * x) - (c / 2) * x) := by field_simp
      have hnn : (0:ℝ) ≤ Real.exp ((c / 2) * x) - (c / 2) * x := by linarith
      have h3 : (0:ℝ) ≤ (2 / c) * Real.exp ((c / 2) * x) - x := by
        rw [hkey]; exact mul_nonneg (by positivity) hnn
      linarith
    have hE : (0:ℝ) < Real.exp (-(c * x)) := Real.exp_pos _
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hx0, abs_of_pos hE]
    calc x * Real.exp (-(c * x))
        ≤ ((2 / c) * Real.exp ((c / 2) * x)) * Real.exp (-(c * x)) :=
          mul_le_mul_of_nonneg_right hxle hE.le
      _ = (2 / c) * Real.exp (-(c / 2) * x) := by
          rw [mul_assoc, ← Real.exp_add]; congr 2; ring

theorem tendsto_antiderivId (hc : 0 < c) : Tendsto (antiderivId c) atTop (𝓝 0) := by
  have hcne : c ≠ 0 := ne_of_gt hc
  have hmul : Tendsto (fun x : ℝ => c * x) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hc tendsto_id
  have hexp : Tendsto (fun x : ℝ => Real.exp (-(c * x))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hmul
  have hpoly : Tendsto (fun x : ℝ => Real.exp (-(c * x)) * (x / c)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun y : ℝ => y ^ 1 * Real.exp (-y)) atTop (𝓝 0) :=
      Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
    have h2 := (h1.comp hmul).div_const (c ^ 2)
    have h3 : Tendsto (fun x : ℝ => ((c * x) ^ 1 * Real.exp (-(c * x))) / c ^ 2)
        atTop (𝓝 0) := by simpa [Function.comp_def] using h2
    refine h3.congr fun x => ?_
    field_simp
  have hcomb : Tendsto (fun x : ℝ => -(Real.exp (-(c * x)) * (x / c))
      + -(Real.exp (-(c * x)) * (1 / c ^ 2))) atTop (𝓝 0) := by
    have := (hpoly.neg).add ((hexp.mul_const (1 / c ^ 2)).neg)
    simpa using this
  refine hcomb.congr fun x => ?_
  rw [antiderivId]
  ring

/-- **The first moment, in closed form.** -/
theorem integral_id_mul_exp (hc : 0 < c) :
    (∫ x in Ioi (0:ℝ), x * Real.exp (-(c * x))) = 1 / c ^ 2 := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (f := antiderivId c) (f' := fun x => x * Real.exp (-(c * x))) (m := 0) (a := 0)
    (fun x _ => hasDerivAt_antiderivId hc x) (integrableOnId hc) (tendsto_antiderivId hc)
  rw [h, antiderivId]
  have hcne : c ≠ 0 := ne_of_gt hc
  simp only [mul_zero, Real.exp_zero, one_mul, zero_div, neg_zero, zero_sub]
  ring

end Cvs.WeilForm.Archimedean.SineLevyFirstMoment
