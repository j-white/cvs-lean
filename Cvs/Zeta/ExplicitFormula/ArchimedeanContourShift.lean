import Mathlib
import Cvs.Zeta.CriticalParam
import Cvs.Zeta.ExplicitFormula.ArchimedeanIntegrandDecay
import Cvs.Zeta.ExplicitFormula.ArchimedeanIntegrandDiff
import Cvs.Zeta.ExplicitFormula.HorizontalSidesVanish

/-!
# The archimedean contour shift, for any admissible test
-/

namespace Cvs.Zeta.ExplicitFormula.ArchimedeanContourShift
open Cvs.Detection

open Complex MeasureTheory Filter
open scoped Real

/-- The archimedean integrand, over an arbitrary test. -/
noncomputable def archIntegrand (h : ℂ → ℂ) (z : ℂ) : ℂ :=
  logDeriv Gammaℝ z * Cvs.Zeta.ofCritical h z

theorem differentiableAt_archIntegrand {h : ℂ → ℂ} (hd : Differentiable ℂ h) {z : ℂ}
    (hz : 0 < z.re) : DifferentiableAt ℂ (archIntegrand h) z :=
  (Cvs.Detection.differentiableAt_logDeriv_gammaR hz).mul ((Cvs.Zeta.differentiable_ofCritical hd) z)

/-- The strip bound: the test's cubic decay times `ArchimedeanIntegrandDecay`'s logarithmic bound on
`logDeriv Γ_ℝ`. -/
theorem strip_bound {h : ℂ → ℂ} {A : ℝ} (hA : 0 ≤ A)
    (hdec : ∀ z : ℂ, -1 ≤ z.re → z.re ≤ 2 → ‖Cvs.Zeta.ofCritical h z‖ ≤ A / (1 + |z.im|) ^ 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, 1 / 2 ≤ z.re → z.re ≤ 2 → 2 ≤ |z.im| →
      ‖archIntegrand h z‖ ≤ C * (1 + Real.log (2 + |z.im|)) / (1 + |z.im|) ^ 3 := by
  obtain ⟨D, hD, hbd⟩ := Cvs.Detection.logDeriv_gammaR_strip_bound
  refine ⟨D * A, by positivity, fun z h1 h2 h3 => ?_⟩
  have hlog : (0 : ℝ) ≤ Real.log (2 + |z.im|) :=
    Real.log_nonneg (by linarith [abs_nonneg z.im])
  rw [archIntegrand, norm_mul]
  calc ‖logDeriv Gammaℝ z‖ * ‖Cvs.Zeta.ofCritical h z‖
      ≤ (D * (1 + Real.log (2 + |z.im|))) * (A / (1 + |z.im|) ^ 3) :=
        mul_le_mul (hbd z h1 h2 h3) (hdec z (by linarith) h2) (norm_nonneg _) (by positivity)
    _ = D * A * (1 + Real.log (2 + |z.im|)) / (1 + |z.im|) ^ 3 := by ring

/-- The rectangle identity, with the test free. -/
theorem rect_identity {h : ℂ → ℂ} (hd : Differentiable ℂ h) (R : ℝ) :
    ((∫ x : ℝ in (1 / 2 : ℝ)..2, archIntegrand h (x + (-R : ℝ) * I))
        - ∫ x : ℝ in (1 / 2 : ℝ)..2, archIntegrand h (x + (R : ℝ) * I))
      + I • (∫ y : ℝ in (-R : ℝ)..R, archIntegrand h (2 + y * I))
      - I • (∫ y : ℝ in (-R : ℝ)..R, archIntegrand h (1 / 2 + y * I)) = 0 := by
  have hre : ∀ z : ℂ, z ∈ Set.uIcc (1 / 2 : ℝ) 2 ×ℂ Set.uIcc (-R) R → 0 < z.re := by
    intro z hz
    have hh := hz.1
    rw [Set.uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 2)] at hh
    exact lt_of_lt_of_le (by norm_num) hh.1
  have hdo : DifferentiableOn ℂ (archIntegrand h)
      (Set.uIcc (1 / 2 : ℝ) 2 ×ℂ Set.uIcc (-R) R) :=
    fun z hz => (differentiableAt_archIntegrand hd (hre z hz)).differentiableWithinAt
  have key := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (archIntegrand h) ((1 / 2 : ℝ) - R * I) (2 + R * I) (by simpa using hdo)
  simpa using key

theorem continuous_line {h : ℂ → ℂ} (hd : Differentiable ℂ h) {c : ℝ} (hc : 0 < c) :
    Continuous (fun y : ℝ => archIntegrand h ((c : ℂ) + y * I)) := by
  have hcont : ContinuousOn (archIntegrand h) {z : ℂ | 0 < z.re} := fun z hz =>
    (differentiableAt_archIntegrand hd hz).continuousAt.continuousWithinAt
  refine hcont.comp_continuous (by fun_prop) ?_
  intro y
  simpa using hc

/-- Integrability on any vertical in the strip, with the test free. -/
theorem integrable_line {h : ℂ → ℂ} (hd : Differentiable ℂ h) {A : ℝ} (hA : 0 ≤ A)
    (hdec : ∀ z : ℂ, -1 ≤ z.re → z.re ≤ 2 → ‖Cvs.Zeta.ofCritical h z‖ ≤ A / (1 + |z.im|) ^ 3)
    {c : ℝ} (hc1 : 1 / 2 ≤ c) (hc2 : c ≤ 2) :
    Integrable (fun y : ℝ => archIntegrand h ((c : ℂ) + y * I)) := by
  have hc0 : (0 : ℝ) < c := by linarith
  obtain ⟨C, hC, hbd⟩ := strip_bound hA hdec
  have hcont := continuous_line hd hc0
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (-2 : ℝ)) (b := 2)).exists_bound_of_continuousOn
    hcont.continuousOn
  have hMnn : (0 : ℝ) ≤ M := le_trans (norm_nonneg _) (hM 0 (by norm_num))
  refine (integrable_inv_one_add_sq.const_mul (5 * M + 3 * C)).mono'
    hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
  have hden : (0 : ℝ) < 1 + y ^ 2 := by positivity
  by_cases hy : |y| ≤ 2
  · have h1 : ‖archIntegrand h ((c : ℂ) + y * I)‖ ≤ M :=
      hM y (by rw [Set.mem_Icc]; constructor <;> [linarith [neg_abs_le y];
        linarith [le_abs_self y]])
    have h2 : (1 : ℝ) / 5 ≤ (1 + y ^ 2)⁻¹ := by
      rw [le_inv_comm₀ (by norm_num) hden]
      nlinarith [abs_nonneg y, sq_abs y]
    nlinarith [h1, h2, hMnn, hC]
  · rw [not_le] at hy
    have hre : (((c : ℂ) + y * I)).re = c := by simp
    have him : (((c : ℂ) + y * I)).im = y := by simp
    have hb := hbd ((c : ℂ) + y * I) (by rw [hre]; exact hc1) (by rw [hre]; exact hc2)
      (by rw [him]; linarith)
    rw [him] at hb
    have hlog := Cvs.Zeta.ExplicitFormula.HorizontalSidesVanish.log_bound (abs_nonneg y)
    have hcube : (0 : ℝ) < (1 + |y|) ^ 3 := by positivity
    have hstep : ‖archIntegrand h ((c : ℂ) + y * I)‖ ≤ C * (3 / (1 + |y|) ^ 2) := by
      refine hb.trans ?_
      have hassoc : C * (1 + Real.log (2 + |y|)) / (1 + |y|) ^ 3
          = C * ((1 + Real.log (2 + |y|)) / (1 + |y|) ^ 3) := by ring
      rw [hassoc]
      exact mul_le_mul_of_nonneg_left hlog hC
    refine hstep.trans ?_
    have hsq : (1 : ℝ) + y ^ 2 ≤ (1 + |y|) ^ 2 := by nlinarith [abs_nonneg y, sq_abs y]
    have h3 : (3 : ℝ) / (1 + |y|) ^ 2 ≤ 3 / (1 + y ^ 2) :=
      div_le_div_of_nonneg_left (by norm_num) hden hsq
    have h4 : C * (3 / (1 + |y|) ^ 2) ≤ C * (3 / (1 + y ^ 2)) :=
      mul_le_mul_of_nonneg_left h3 hC
    have h5 : C * (3 / (1 + y ^ 2)) = 3 * C * (1 + y ^ 2)⁻¹ := by
      rw [div_eq_mul_inv]; ring
    have hinv : (0 : ℝ) ≤ (1 + y ^ 2)⁻¹ := by positivity
    have h6 : 3 * C * (1 + y ^ 2)⁻¹ ≤ (5 * M + 3 * C) * (1 + y ^ 2)⁻¹ := by
      nlinarith [hMnn, hinv]
    linarith [h4, h5.le, h5.ge, h6]

/-- Both horizontals, at height `±R`.  `ArchimedeanIntegrandDecay`'s bound depends on the height only
through `|Im z|`, so one lemma covers both signs. -/
theorem horizontal_le {h : ℂ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hbd : ∀ z : ℂ, 1 / 2 ≤ z.re → z.re ≤ 2 → 2 ≤ |z.im| →
      ‖archIntegrand h z‖ ≤ C * (1 + Real.log (2 + |z.im|)) / (1 + |z.im|) ^ 3)
    {t : ℝ} (R : ℝ) (hR : 2 ≤ R) (ht : |t| = R) :
    ‖∫ x in (1 / 2 : ℝ)..2, archIntegrand h ((x : ℂ) + (t : ℝ) * I)‖
      ≤ (3 / 2 * C) * (3 / (1 + R) ^ 2) := by
  have hR0 : (0 : ℝ) ≤ R := by linarith
  have hunif : ∀ x ∈ Set.uIoc (1 / 2 : ℝ) 2,
      ‖archIntegrand h ((x : ℂ) + (t : ℝ) * I)‖ ≤ C * (3 / (1 + R) ^ 2) := by
    intro x hx
    rw [Set.uIoc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 2)] at hx
    have hre : (((x : ℂ) + (t : ℝ) * I)).re = x := by simp
    have him : (((x : ℂ) + (t : ℝ) * I)).im = t := by simp
    have hb := hbd ((x : ℂ) + (t : ℝ) * I) (by rw [hre]; exact le_of_lt hx.1)
      (by rw [hre]; exact hx.2) (by rw [him, ht]; exact hR)
    rw [him, ht] at hb
    have hassoc : C * (1 + Real.log (2 + R)) / (1 + R) ^ 3
        = C * ((1 + Real.log (2 + R)) / (1 + R) ^ 3) := by ring
    rw [hassoc] at hb
    exact hb.trans (mul_le_mul_of_nonneg_left (Cvs.Zeta.ExplicitFormula.HorizontalSidesVanish.log_bound hR0) hC)
  refine (intervalIntegral.norm_integral_le_of_norm_le_const hunif).trans (le_of_eq ?_)
  rw [show |(2 : ℝ) - 1 / 2| = 3 / 2 from by rw [abs_of_nonneg] <;> norm_num]
  ring

theorem horizontal_tendsto_zero {h : ℂ → ℂ} {A : ℝ} (hA : 0 ≤ A)
    (hdec : ∀ z : ℂ, -1 ≤ z.re → z.re ≤ 2 → ‖Cvs.Zeta.ofCritical h z‖ ≤ A / (1 + |z.im|) ^ 3) :
    Tendsto (fun R : ℝ => ∫ x in (1 / 2 : ℝ)..2, archIntegrand h ((x : ℂ) + (R : ℝ) * I))
      atTop (nhds 0) := by
  obtain ⟨C, hC, hbd⟩ := strip_bound hA hdec
  have hlim : Tendsto (fun R : ℝ => (3 / 2 * C) * (3 / (1 + R) ^ 2)) atTop (nhds 0) := by
    have hh := Cvs.Zeta.ExplicitFormula.HorizontalSidesVanish.tendsto_three_div_sq.const_mul (3 / 2 * C)
    rwa [mul_zero] at hh
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with R hR
  exact horizontal_le hC hbd R hR (abs_of_nonneg (by linarith))

theorem horizontal_neg_tendsto_zero {h : ℂ → ℂ} {A : ℝ} (hA : 0 ≤ A)
    (hdec : ∀ z : ℂ, -1 ≤ z.re → z.re ≤ 2 → ‖Cvs.Zeta.ofCritical h z‖ ≤ A / (1 + |z.im|) ^ 3) :
    Tendsto (fun R : ℝ => ∫ x in (1 / 2 : ℝ)..2, archIntegrand h ((x : ℂ) + (-R : ℝ) * I))
      atTop (nhds 0) := by
  obtain ⟨C, hC, hbd⟩ := strip_bound hA hdec
  have hlim : Tendsto (fun R : ℝ => (3 / 2 * C) * (3 / (1 + R) ^ 2)) atTop (nhds 0) := by
    have hh := Cvs.Zeta.ExplicitFormula.HorizontalSidesVanish.tendsto_three_div_sq.const_mul (3 / 2 * C)
    rwa [mul_zero] at hh
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with R hR
  exact horizontal_le hC hbd R hR (by rw [abs_neg, abs_of_nonneg (by linarith)])

/-- **The archimedean contour shift, for any admissible test.** with the test as a parameter. -/
theorem contour_shift {h : ℂ → ℂ} (hd : Differentiable ℂ h) {A : ℝ} (hA : 0 ≤ A)
    (hdec : ∀ z : ℂ, -1 ≤ z.re → z.re ≤ 2 → ‖Cvs.Zeta.ofCritical h z‖ ≤ A / (1 + |z.im|) ^ 3) :
    ∫ y : ℝ, archIntegrand h (2 + y * I) = ∫ y : ℝ, archIntegrand h (1 / 2 + y * I) := by
  have hbot : Tendsto (fun R : ℝ => -(R : ℝ)) atTop atBot := tendsto_neg_atTop_atBot
  have htop : Tendsto (fun R : ℝ => (R : ℝ)) atTop atTop := tendsto_id
  have hint2 : Integrable (fun y : ℝ => archIntegrand h (2 + y * I)) := by
    have hh := integrable_line hd hA hdec (by norm_num : (1 / 2 : ℝ) ≤ 2) (le_refl 2)
    push_cast at hh
    exact hh
  have hintH : Integrable (fun y : ℝ => archIntegrand h (1 / 2 + y * I)) := by
    have hh := integrable_line hd hA hdec (le_refl (1 / 2 : ℝ)) (by norm_num : (1 / 2 : ℝ) ≤ 2)
    push_cast at hh
    exact hh
  have hR := MeasureTheory.intervalIntegral_tendsto_integral hint2 hbot htop
  have hL := MeasureTheory.intervalIntegral_tendsto_integral hintH hbot htop
  have hid : ∀ R : ℝ,
      I • (∫ y : ℝ in (-R : ℝ)..R, archIntegrand h (2 + y * I))
        - I • (∫ y : ℝ in (-R : ℝ)..R, archIntegrand h (1 / 2 + y * I))
      = (∫ x : ℝ in (1 / 2 : ℝ)..2, archIntegrand h (x + (R : ℝ) * I))
        - ∫ x : ℝ in (1 / 2 : ℝ)..2, archIntegrand h (x + (-R : ℝ) * I) := by
    intro R
    have hh := rect_identity hd R
    linear_combination hh
  have hlim : Tendsto
      (fun R : ℝ => I • (∫ y : ℝ in (-R : ℝ)..R, archIntegrand h (2 + y * I))
        - I • (∫ y : ℝ in (-R : ℝ)..R, archIntegrand h (1 / 2 + y * I)))
      atTop (nhds (I • (∫ y : ℝ, archIntegrand h (2 + y * I))
        - I • ∫ y : ℝ, archIntegrand h (1 / 2 + y * I))) :=
    (hR.const_smul I).sub (hL.const_smul I)
  have hzero : Tendsto
      (fun R : ℝ => I • (∫ y : ℝ in (-R : ℝ)..R, archIntegrand h (2 + y * I))
        - I • (∫ y : ℝ in (-R : ℝ)..R, archIntegrand h (1 / 2 + y * I)))
      atTop (nhds 0) := by
    refine Tendsto.congr (fun R => (hid R).symm) ?_
    have hh := (horizontal_tendsto_zero hA hdec).sub (horizontal_neg_tendsto_zero hA hdec)
    rw [sub_zero] at hh
    exact hh
  have heq := tendsto_nhds_unique hlim hzero
  rw [smul_eq_mul, smul_eq_mul, ← mul_sub] at heq
  exact sub_eq_zero.mp ((mul_eq_zero.mp heq).resolve_left Complex.I_ne_zero)

end Cvs.Zeta.ExplicitFormula.ArchimedeanContourShift
