import Mathlib
import Cvs.Zeta.CriticalParam
import Cvs.Zeta.ExplicitFormula.FirstPoleTermPositive
import Cvs.Zeta.ExplicitFormula.HorizontalSidesVanish

/-!
# The first pole term, for any admissible test
-/

namespace Cvs.Zeta.ExplicitFormula.FirstPoleContourShift

open Complex MeasureTheory Filter
open scoped Real

/-- The first pole integrand, over an arbitrary test. -/
noncomputable def poleIntegrand (h : ℂ → ℂ) (z : ℂ) : ℂ :=
  1 / z * Cvs.Zeta.ofCritical h z

theorem differentiableAt_poleIntegrand {h : ℂ → ℂ} (hd : Differentiable ℂ h) {z : ℂ}
    (hz : z ≠ 0) : DifferentiableAt ℂ (poleIntegrand h) z :=
  ((differentiableAt_const 1).div differentiableAt_id hz).mul
    ((Cvs.Zeta.differentiable_ofCritical hd) z)

theorem strip_bound {h : ℂ → ℂ} {A : ℝ}
    (hdec : ∀ z : ℂ, -1 ≤ z.re → z.re ≤ 2 → ‖Cvs.Zeta.ofCritical h z‖ ≤ A / (1 + |z.im|) ^ 3) :
    ∀ z : ℂ, 1 / 2 ≤ z.re → z.re ≤ 2 →
      ‖poleIntegrand h z‖ ≤ 2 * A / (1 + |z.im|) ^ 3 := by
  intro z h1 h2
  rw [poleIntegrand, norm_mul]
  have hstep : ‖(1 : ℂ) / z‖ * ‖Cvs.Zeta.ofCritical h z‖ ≤ 2 * (A / (1 + |z.im|) ^ 3) :=
    mul_le_mul (Cvs.Zeta.ExplicitFormula.FirstPoleTermPositive.norm_one_div_le h1) (hdec z (by linarith) h2)
      (norm_nonneg _) (by norm_num)
  refine hstep.trans (le_of_eq ?_)
  ring

theorem rect_identity {h : ℂ → ℂ} (hd : Differentiable ℂ h) (R : ℝ) :
    ((∫ x : ℝ in (1 / 2 : ℝ)..2, poleIntegrand h (x + (-R : ℝ) * I))
        - ∫ x : ℝ in (1 / 2 : ℝ)..2, poleIntegrand h (x + (R : ℝ) * I))
      + I • (∫ y : ℝ in (-R : ℝ)..R, poleIntegrand h (2 + y * I))
      - I • (∫ y : ℝ in (-R : ℝ)..R, poleIntegrand h (1 / 2 + y * I)) = 0 := by
  have hne : ∀ z : ℂ, z ∈ Set.uIcc (1 / 2 : ℝ) 2 ×ℂ Set.uIcc (-R) R → z ≠ 0 := by
    intro z hz
    have hh := hz.1
    rw [Set.uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 2)] at hh
    exact Cvs.Zeta.ExplicitFormula.FirstPoleTermPositive.ne_zero_of_half_le_re hh.1
  have hdo : DifferentiableOn ℂ (poleIntegrand h)
      (Set.uIcc (1 / 2 : ℝ) 2 ×ℂ Set.uIcc (-R) R) :=
    fun z hz => (differentiableAt_poleIntegrand hd (hne z hz)).differentiableWithinAt
  have key := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (poleIntegrand h) ((1 / 2 : ℝ) - R * I) (2 + R * I) (by simpa using hdo)
  simpa using key

theorem continuous_line {h : ℂ → ℂ} (hd : Differentiable ℂ h) {c : ℝ} (hc : 1 / 2 ≤ c) :
    Continuous (fun y : ℝ => poleIntegrand h ((c : ℂ) + y * I)) := by
  have hcont : ContinuousOn (poleIntegrand h) {z : ℂ | 1 / 2 ≤ z.re} := fun z hz =>
    ((differentiableAt_poleIntegrand hd (Cvs.Zeta.ExplicitFormula.FirstPoleTermPositive.ne_zero_of_half_le_re hz)).continuousAt).continuousWithinAt
  refine hcont.comp_continuous (by fun_prop) ?_
  intro y
  simpa using hc

theorem integrable_line {h : ℂ → ℂ} (hd : Differentiable ℂ h) {A : ℝ} (hA : 0 ≤ A)
    (hdec : ∀ z : ℂ, -1 ≤ z.re → z.re ≤ 2 → ‖Cvs.Zeta.ofCritical h z‖ ≤ A / (1 + |z.im|) ^ 3)
    {c : ℝ} (hc1 : 1 / 2 ≤ c) (hc2 : c ≤ 2) :
    Integrable (fun y : ℝ => poleIntegrand h ((c : ℂ) + y * I)) := by
  refine (integrable_inv_one_add_sq.const_mul (2 * A)).mono'
    (continuous_line hd hc1).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => ?_)
  have hre : (((c : ℂ) + y * I)).re = c := by simp
  have him : (((c : ℂ) + y * I)).im = y := by simp
  have hb := strip_bound hdec ((c : ℂ) + y * I) (by rw [hre]; exact hc1)
    (by rw [hre]; exact hc2)
  rw [him] at hb
  refine hb.trans ?_
  rw [← div_eq_mul_inv]
  gcongr
  exact Cvs.Zeta.ExplicitFormula.FirstPoleTermPositive.cube_ge y

theorem horizontal_le {h : ℂ → ℂ} {A : ℝ} (hA : 0 ≤ A)
    (hdec : ∀ z : ℂ, -1 ≤ z.re → z.re ≤ 2 → ‖Cvs.Zeta.ofCritical h z‖ ≤ A / (1 + |z.im|) ^ 3)
    {t : ℝ} (R : ℝ) (hR : 0 ≤ R) (ht : |t| = R) :
    ‖∫ x in (1 / 2 : ℝ)..2, poleIntegrand h ((x : ℂ) + (t : ℝ) * I)‖
      ≤ (1 / 2 * (2 * A)) * (3 / (1 + R) ^ 2) := by
  have hunif : ∀ x ∈ Set.uIoc (1 / 2 : ℝ) 2,
      ‖poleIntegrand h ((x : ℂ) + (t : ℝ) * I)‖ ≤ (2 * A) / 3 * (3 / (1 + R) ^ 2) := by
    intro x hx
    rw [Set.uIoc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 2)] at hx
    have hre : (((x : ℂ) + (t : ℝ) * I)).re = x := by simp
    have him : (((x : ℂ) + (t : ℝ) * I)).im = t := by simp
    have hb := strip_bound hdec ((x : ℂ) + (t : ℝ) * I) (by rw [hre]; exact le_of_lt hx.1)
      (by rw [hre]; exact hx.2)
    rw [him, ht] at hb
    refine hb.trans ?_
    rw [show (2 * A) / 3 * (3 / (1 + R) ^ 2) = (2 * A) / (1 + R) ^ 2 from by ring]
    have h3 : (1 + R) ^ 2 ≤ (1 + R) ^ 3 := by nlinarith [sq_nonneg (1 + R), hR]
    exact div_le_div_of_nonneg_left (by linarith) (by positivity) h3
  refine (intervalIntegral.norm_integral_le_of_norm_le_const hunif).trans (le_of_eq ?_)
  rw [show |(2 : ℝ) - 1 / 2| = 3 / 2 from by rw [abs_of_nonneg] <;> norm_num]
  ring

theorem horizontal_tendsto_zero {h : ℂ → ℂ} {A : ℝ} (hA : 0 ≤ A)
    (hdec : ∀ z : ℂ, -1 ≤ z.re → z.re ≤ 2 → ‖Cvs.Zeta.ofCritical h z‖ ≤ A / (1 + |z.im|) ^ 3) :
    Tendsto (fun R : ℝ => ∫ x in (1 / 2 : ℝ)..2, poleIntegrand h ((x : ℂ) + (R : ℝ) * I))
      atTop (nhds 0) := by
  have hlim : Tendsto (fun R : ℝ => (1 / 2 * (2 * A)) * (3 / (1 + R) ^ 2)) atTop (nhds 0) := by
    have hh := Cvs.Zeta.ExplicitFormula.HorizontalSidesVanish.tendsto_three_div_sq.const_mul (1 / 2 * (2 * A))
    rwa [mul_zero] at hh
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
  exact horizontal_le hA hdec R hR (abs_of_nonneg hR)

theorem horizontal_neg_tendsto_zero {h : ℂ → ℂ} {A : ℝ} (hA : 0 ≤ A)
    (hdec : ∀ z : ℂ, -1 ≤ z.re → z.re ≤ 2 → ‖Cvs.Zeta.ofCritical h z‖ ≤ A / (1 + |z.im|) ^ 3) :
    Tendsto (fun R : ℝ => ∫ x in (1 / 2 : ℝ)..2, poleIntegrand h ((x : ℂ) + (-R : ℝ) * I))
      atTop (nhds 0) := by
  have hlim : Tendsto (fun R : ℝ => (1 / 2 * (2 * A)) * (3 / (1 + R) ^ 2)) atTop (nhds 0) := by
    have hh := Cvs.Zeta.ExplicitFormula.HorizontalSidesVanish.tendsto_three_div_sq.const_mul (1 / 2 * (2 * A))
    rwa [mul_zero] at hh
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
  exact horizontal_le hA hdec R hR (by rw [abs_neg, abs_of_nonneg hR])

/-- **The contour shift for the first pole term, for any admissible test.** -/
theorem contour_shift {h : ℂ → ℂ} (hd : Differentiable ℂ h) {A : ℝ} (hA : 0 ≤ A)
    (hdec : ∀ z : ℂ, -1 ≤ z.re → z.re ≤ 2 → ‖Cvs.Zeta.ofCritical h z‖ ≤ A / (1 + |z.im|) ^ 3) :
    ∫ y : ℝ, poleIntegrand h (2 + y * I) = ∫ y : ℝ, poleIntegrand h (1 / 2 + y * I) := by
  have hbot : Tendsto (fun R : ℝ => -(R : ℝ)) atTop atBot := tendsto_neg_atTop_atBot
  have htop : Tendsto (fun R : ℝ => (R : ℝ)) atTop atTop := tendsto_id
  have hint2 : Integrable (fun y : ℝ => poleIntegrand h (2 + y * I)) := by
    have hh := integrable_line hd hA hdec (by norm_num : (1 / 2 : ℝ) ≤ 2) (le_refl 2)
    push_cast at hh
    exact hh
  have hintH : Integrable (fun y : ℝ => poleIntegrand h (1 / 2 + y * I)) := by
    have hh := integrable_line hd hA hdec (le_refl (1 / 2 : ℝ)) (by norm_num : (1 / 2 : ℝ) ≤ 2)
    push_cast at hh
    exact hh
  have hR := MeasureTheory.intervalIntegral_tendsto_integral hint2 hbot htop
  have hL := MeasureTheory.intervalIntegral_tendsto_integral hintH hbot htop
  have hid : ∀ R : ℝ,
      I • (∫ y : ℝ in (-R : ℝ)..R, poleIntegrand h (2 + y * I))
        - I • (∫ y : ℝ in (-R : ℝ)..R, poleIntegrand h (1 / 2 + y * I))
      = (∫ x : ℝ in (1 / 2 : ℝ)..2, poleIntegrand h (x + (R : ℝ) * I))
        - ∫ x : ℝ in (1 / 2 : ℝ)..2, poleIntegrand h (x + (-R : ℝ) * I) := by
    intro R
    have hh := rect_identity hd R
    linear_combination hh
  have hlim : Tendsto
      (fun R : ℝ => I • (∫ y : ℝ in (-R : ℝ)..R, poleIntegrand h (2 + y * I))
        - I • (∫ y : ℝ in (-R : ℝ)..R, poleIntegrand h (1 / 2 + y * I)))
      atTop (nhds (I • (∫ y : ℝ, poleIntegrand h (2 + y * I))
        - I • ∫ y : ℝ, poleIntegrand h (1 / 2 + y * I))) :=
    (hR.const_smul I).sub (hL.const_smul I)
  have hzero : Tendsto
      (fun R : ℝ => I • (∫ y : ℝ in (-R : ℝ)..R, poleIntegrand h (2 + y * I))
        - I • (∫ y : ℝ in (-R : ℝ)..R, poleIntegrand h (1 / 2 + y * I)))
      atTop (nhds 0) := by
    refine Tendsto.congr (fun R => (hid R).symm) ?_
    have hh := (horizontal_tendsto_zero hA hdec).sub (horizontal_neg_tendsto_zero hA hdec)
    rw [sub_zero] at hh
    exact hh
  have heq := tendsto_nhds_unique hlim hzero
  rw [smul_eq_mul, smul_eq_mul, ← mul_sub] at heq
  exact sub_eq_zero.mp ((mul_eq_zero.mp heq).resolve_left Complex.I_ne_zero)

/-- On the critical line the pole term is a Lorentzian against the density. -/
theorem re_poleIntegrand_critical {h : ℂ → ℂ} {ρ : ℝ → ℝ}
    (hrho : ∀ y : ℝ, Cvs.Zeta.ofCritical h (1 / 2 + (y : ℝ) * I) = ((ρ y : ℝ) : ℂ)) (y : ℝ) :
    (poleIntegrand h (1 / 2 + (y : ℝ) * I)).re = (1 / 2) / (1 / 4 + y ^ 2) * ρ y := by
  rw [poleIntegrand, hrho y, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Cvs.Zeta.ExplicitFormula.FirstPoleTermPositive.re_one_div_half]
  ring

end Cvs.Zeta.ExplicitFormula.FirstPoleContourShift
