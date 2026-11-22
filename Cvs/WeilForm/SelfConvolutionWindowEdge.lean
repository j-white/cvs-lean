import Mathlib
import Cvs.WeilForm.Archimedean.LevyDensity

/-!
# What the self-convolution cannot do near the edge of the window

For a test function supported in `(0, L]` the self-convolution vanishes off `(−L, L)`, and on the
outer half of that range the two factors draw on disjoint halves of the window, so it is at most
half of its value at the origin.
-/

set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory
open scoped ContDiff

namespace Cvs.WeilForm.SelfConvolutionWindowEdge

variable {f : ℝ → ℝ}

/-- **A Padé-type bound on the exponential.** -/
theorem exp_pade {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) : (2 - u) * Real.exp u ≤ 2 + u := by
  have h := Real.exp_bound' hu0 hu1 (n := 3) (by norm_num)
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ] at h
  norm_num at h
  nlinarith [h, hu0, hu1, pow_nonneg hu0 3, pow_nonneg hu0 4]

/-- **The archimedean density from below.**  `densityU u ≥ e^{−u/4}(1/u + 1/2) ≥ 1/u + 1/4 − u/8`. -/
theorem densityU_lower {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1) :
    1 / u + 1 / 4 - u / 8 ≤ Cvs.WeilForm.Archimedean.LevyDensity.densityU u := by
  have hep : (0:ℝ) < Real.exp u := Real.exp_pos _
  have hexp := exp_pade hu0.le hu1
  have hneg : (2 - u) / (2 + u) ≤ Real.exp (-u) := by
    rw [div_le_iff₀ (by linarith), Real.exp_neg, ← div_eq_inv_mul, le_div_iff₀ hep]
    nlinarith [hexp]
  have hden0 : (0:ℝ) < 1 - Real.exp (-u) := by
    have : Real.exp (-u) < 1 := by rw [Real.exp_lt_one_iff]; linarith
    linarith
  have hneg2 : 2 - u ≤ Real.exp (-u) * (2 + u) := by
    rw [div_le_iff₀ (by linarith)] at hneg; linarith
  have hden : 1 - Real.exp (-u) ≤ 2 * u / (2 + u) := by
    rw [le_div_iff₀ (by linarith)]
    nlinarith [hneg2]
  have he4 : 1 - u / 4 ≤ Real.exp (-(u / 4)) := by
    linarith [Real.add_one_le_exp (-(u / 4))]
  have hden2 : (1 - Real.exp (-u)) * (2 + u) ≤ 2 * u := by
    rw [le_div_iff₀ (by linarith)] at hden; linarith
  have hq : (2 + u) / (2 * u) ≤ 1 / (1 - Real.exp (-u)) := by
    rw [div_le_div_iff₀ (by positivity) hden0]
    nlinarith [hden2]
  have hkey : (1 - u / 4) * ((2 + u) / (2 * u))
      ≤ Real.exp (-(u / 4)) * (1 / (1 - Real.exp (-u))) :=
    mul_le_mul he4 hq (by positivity) (le_of_lt (Real.exp_pos _))
  have hdd : Real.exp (-(u / 4)) * (1 / (1 - Real.exp (-u)))
      = Cvs.WeilForm.Archimedean.LevyDensity.densityU u := by
    rw [Cvs.WeilForm.Archimedean.LevyDensity.densityU]; field_simp
  rw [hdd] at hkey
  have hrw : (1 - u / 4) * ((2 + u) / (2 * u)) = 1 / u + 1 / 4 - u / 8 := by
    field_simp
    ring
  linarith [hkey, hrw.le, hrw.ge]

/-- **The archimedean density's integral over a window, from below.** -/
theorem densityU_int_lower {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1) :
    Real.log b - Real.log a + (b - a) / 4 - (b ^ 2 - a ^ 2) / 16
      ≤ ∫ u in Set.Ioc a b, Cvs.WeilForm.Archimedean.LevyDensity.densityU u := by
  have hD : ContinuousOn Cvs.WeilForm.Archimedean.LevyDensity.densityU (Set.Icc a b) := by
    refine ContinuousOn.div (f := fun u : ℝ => Real.exp (-(u / 4)))
      (g := fun u : ℝ => 1 - Real.exp (-u)) (by fun_prop) (by fun_prop) fun u hu => ?_
    have hu' : (0:ℝ) < u := lt_of_lt_of_le ha hu.1
    have : Real.exp (-u) < 1 := by rw [Real.exp_lt_one_iff]; linarith
    linarith
  have hDint : IntegrableOn Cvs.WeilForm.Archimedean.LevyDensity.densityU (Set.Ioc a b) :=
    (hD.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  have hmc : ContinuousOn (fun u : ℝ => 1 / u + 1 / 4 - u / 8) (Set.Icc a b) := by
    refine ContinuousOn.sub (f := fun u : ℝ => 1 / u + 1 / 4) (g := fun u : ℝ => u / 8)
      (ContinuousOn.add (f := fun u : ℝ => 1 / u) (g := fun _ : ℝ => (1 / 4 : ℝ))
        (ContinuousOn.div (f := fun _ : ℝ => (1 : ℝ)) (g := fun u : ℝ => u) continuousOn_const
      continuousOn_id fun u hu => ?_) continuousOn_const) (by fun_prop)
    exact ne_of_gt (lt_of_lt_of_le ha hu.1)
  have hmint : IntegrableOn (fun u : ℝ => 1 / u + 1 / 4 - u / 8) (Set.Ioc a b) :=
    (hmc.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  have hmono : (∫ u in Set.Ioc a b, (1 / u + 1 / 4 - u / 8))
      ≤ ∫ u in Set.Ioc a b, Cvs.WeilForm.Archimedean.LevyDensity.densityU u :=
    setIntegral_mono_on hmint hDint measurableSet_Ioc fun u hu =>
      densityU_lower (lt_trans ha hu.1) (le_trans hu.2 hb)
  have hval : (∫ u in Set.Ioc a b, (1 / u + 1 / 4 - u / 8))
      = Real.log b - Real.log a + (b - a) / 4 - (b ^ 2 - a ^ 2) / 16 := by
    rw [← intervalIntegral.integral_of_le hab]
    have hd : ∀ x ∈ Set.uIcc a b, HasDerivAt
        (fun y : ℝ => Real.log y + y / 4 - y ^ 2 / 16) (1 / x + 1 / 4 - x / 8) x := by
      intro x hx
      have hx0 : x ≠ 0 := by
        rw [Set.uIcc_of_le hab] at hx
        exact ne_of_gt (lt_of_lt_of_le ha hx.1)
      have h1 : HasDerivAt Real.log (1 / x) x := by
        simpa [one_div] using Real.hasDerivAt_log hx0
      have h2 : HasDerivAt (fun y : ℝ => y / 4) (1 / 4 : ℝ) x := by
        simpa using (hasDerivAt_id x).div_const 4
      have h3 : HasDerivAt (fun y : ℝ => y ^ 2 / 16) (x / 8) x := by
        have := ((hasDerivAt_pow 2 x).div_const 16)
        simpa [mul_comm] using this.congr_deriv (by push_cast; ring)
      exact (h1.add h2).sub h3
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      ((hmc.mono (by rw [Set.uIcc_of_le hab])).intervalIntegrable)]
    ring
  linarith [hmono, hval.le, hval.ge]

/-- **The archimedean density is integrable past the origin.** -/
theorem densityU_integrableOn {c : ℝ} (hc : 0 < c) :
    IntegrableOn Cvs.WeilForm.Archimedean.LevyDensity.densityU (Set.Ioi c) := by
  have hd0 : (0:ℝ) < 1 - Real.exp (-c) := by
    have : Real.exp (-c) < 1 := by rw [Real.exp_lt_one_iff]; linarith
    linarith
  have hbase : IntegrableOn (fun x : ℝ => Real.exp (-(1 / 4 : ℝ) * x)) (Set.Ioi c) :=
    exp_neg_integrableOn_Ioi c (by norm_num)
  have hmaj : IntegrableOn
      (fun u : ℝ => (1 - Real.exp (-c))⁻¹ * Real.exp (-(1 / 4 : ℝ) * u)) (Set.Ioi c) :=
    hbase.const_mul _
  have hmeas : AEStronglyMeasurable Cvs.WeilForm.Archimedean.LevyDensity.densityU
      (volume.restrict (Set.Ioi c)) := by
    refine Measurable.aestronglyMeasurable ?_
    unfold Cvs.WeilForm.Archimedean.LevyDensity.densityU
    fun_prop
  refine hmaj.mono' hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu' : c < u := hu
  have hdu : (0:ℝ) < 1 - Real.exp (-u) := by
    have : Real.exp (-u) < 1 := by rw [Real.exp_lt_one_iff]; linarith
    linarith
  have hcmp : 1 - Real.exp (-c) ≤ 1 - Real.exp (-u) := by
    have : Real.exp (-u) ≤ Real.exp (-c) := Real.exp_le_exp.2 (by linarith)
    linarith
  have hpos : (0:ℝ) ≤ Cvs.WeilForm.Archimedean.LevyDensity.densityU u := by
    rw [Cvs.WeilForm.Archimedean.LevyDensity.densityU]
    positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hpos, Cvs.WeilForm.Archimedean.LevyDensity.densityU]
  rw [div_le_iff₀ hdu]
  have he : Real.exp (-(u / 4)) = Real.exp (-(1 / 4 : ℝ) * u) := by congr 1; ring
  rw [he]
  have hep : (0:ℝ) < Real.exp (-(1 / 4 : ℝ) * u) := Real.exp_pos _
  rw [inv_mul_eq_div, div_mul_eq_mul_div, le_div_iff₀ hd0]
  nlinarith [hcmp, hep]

end Cvs.WeilForm.SelfConvolutionWindowEdge
