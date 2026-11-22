import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The Laplace amplitude of the odd cross term is analytic with a uniform `c^{−3/4}` bound

`G_c(a, q) = ∫_{v>0} e^{−av}/(v + icq) dv` is holomorphic on `Re q > 0`, and for `0 < κ ≤ Re q − |Im q|`
it satisfies `‖G_c(a, q)‖ ≤ 2Γ(3/4)(1/(cκ))^{3/4}(1/a)^{3/4}`.
-/

noncomputable section

open Real Set MeasureTheory Filter Topology
open Complex (I)

namespace Cvs.Prolate.Hardy.OddCrossLaplaceAmplitude

/-- The Laplace amplitude `G_c(a, q) = ∫_{v>0} e^{−av}/(v + icq) dv`. -/
def lapG (c a : ℝ) (q : ℂ) : ℂ := ∫ v in Ioi (0 : ℝ), (Real.exp (-a * v) : ℂ) / ((v : ℂ) + I * c * q)

theorem im_den (c v : ℝ) (q : ℂ) : ((v : ℂ) + I * c * q).im = c * q.re := by
  simp [Complex.mul_re, Complex.mul_im]

theorem re_den (c v : ℝ) (q : ℂ) : ((v : ℂ) + I * c * q).re = v - c * q.im := by
  simp [Complex.mul_re, Complex.mul_im]; ring

theorem le_norm_den {c : ℝ} (hc : 0 ≤ c) (v : ℝ) {q : ℂ} (hq : 0 ≤ q.re) : c * q.re ≤ ‖(v : ℂ) + I * c * q‖ := by
  have := Complex.abs_im_le_norm ((v : ℂ) + I * c * q)
  rwa [im_den, abs_of_nonneg (mul_nonneg hc hq)] at this

theorem den_ne_zero {c : ℝ} (hc : 0 < c) (v : ℝ) {q : ℂ} (hq : 0 < q.re) : (v : ℂ) + I * c * q ≠ 0 := by
  intro h
  have := im_den c v q
  rw [h, Complex.zero_im] at this
  nlinarith [mul_pos hc hq]

/-- `‖v + icq‖ ≥ (v + cκ)/2` when `κ ≤ Re q − |Im q|`. -/
theorem half_le_norm_den {c : ℝ} (hc : 0 ≤ c) (v : ℝ) {κ : ℝ} {q : ℂ} (hκ : κ ≤ q.re - |q.im|) :
    (v + c * κ) / 2 ≤ ‖(v : ℂ) + I * c * q‖ := by
  have h1 := Complex.abs_im_le_norm ((v : ℂ) + I * c * q)
  have h2 := Complex.abs_re_le_norm ((v : ℂ) + I * c * q)
  rw [im_den] at h1
  rw [re_den] at h2
  have a1 := le_abs_self (c * q.re)
  have a2 := le_abs_self (v - c * q.im)
  have a3 : c * q.im ≤ c * |q.im| := mul_le_mul_of_nonneg_left (le_abs_self _) hc
  have a4 : c * κ ≤ c * q.re - c * |q.im| := by rw [← mul_sub]; exact mul_le_mul_of_nonneg_left hκ hc
  linarith

/-- `v^{1/4} m^{3/4} ≤ v + m` for `v, m ≥ 0`. -/
theorem rpow_mul_rpow_le {v m : ℝ} (hv : 0 ≤ v) (hm : 0 ≤ m) :
    v ^ (1 / 4 : ℝ) * m ^ (3 / 4 : ℝ) ≤ v + m := by
  have := Real.geom_mean_le_arith_mean2_weighted (w₁ := 1 / 4) (w₂ := 3 / 4) (by norm_num) (by norm_num) hv hm
    (by norm_num)
  linarith

theorem continuous_integrand {c : ℝ} (hc : 0 < c) (a : ℝ) {q : ℂ} (hq : 0 < q.re) :
    Continuous fun v : ℝ => (Real.exp (-a * v) : ℂ) / ((v : ℂ) + I * c * q) :=
  Continuous.div (f := fun v : ℝ => (Real.exp (-a * v) : ℂ)) (g := fun v : ℝ => (v : ℂ) + I * c * q)
    (by fun_prop) (by fun_prop) fun v => den_ne_zero hc v hq

theorem integrableOn_integrand {c a : ℝ} (hc : 0 < c) (ha : 0 < a) {q : ℂ} (hq : 0 < q.re) :
    IntegrableOn (fun v : ℝ => (Real.exp (-a * v) : ℂ) / ((v : ℂ) + I * c * q)) (Ioi 0) := by
  refine ((exp_neg_integrableOn_Ioi 0 ha).div_const (c * q.re)).mono'
    (continuous_integrand hc a hq).aestronglyMeasurable (Eventually.of_forall fun v => ?_)
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact div_le_div_of_nonneg_left (Real.exp_pos _).le (mul_pos hc hq) (le_norm_den hc.le v hq.le)

/-- **Holomorphy**: `q ↦ G_c(a, q)` is complex differentiable on `Re q > 0`. -/
theorem differentiableOn_lapG {c a : ℝ} (hc : 0 < c) (ha : 0 < a) :
    DifferentiableOn ℂ (lapG c a) {q : ℂ | 0 < q.re} := by
  intro q₀ hq₀
  have hq₀' : 0 < q₀.re := hq₀
  set r := q₀.re / 2 with hr
  have hr0 : 0 < r := by positivity
  have hball : ∀ q ∈ Metric.ball q₀ r, r ≤ q.re := by
    intro q hq
    have h1 := Complex.abs_re_le_norm (q - q₀)
    rw [Metric.mem_ball, dist_eq_norm] at hq
    rw [Complex.sub_re] at h1
    have := neg_abs_le (q.re - q₀.re)
    linarith
  set F : ℂ → ℝ → ℂ := fun q v => (Real.exp (-a * v) : ℂ) / ((v : ℂ) + I * c * q) with hF
  set F' : ℂ → ℝ → ℂ := fun q v => (Real.exp (-a * v) : ℂ) * (-(I * c * 1) / ((v : ℂ) + I * c * q) ^ 2) with hF'
  have hderiv : ∀ v : ℝ, ∀ q ∈ Metric.ball q₀ r, HasDerivAt (fun q => F q v) (F' q v) q := by
    intro v q hq
    have hne := den_ne_zero hc v (lt_of_lt_of_le hr0 (hball q hq))
    have h := ((((hasDerivAt_id q).const_mul (I * c)).const_add (v : ℂ)).inv hne).const_mul
      (Real.exp (-a * v) : ℂ)
    refine (h.congr_deriv (by simp only [hF', id])).congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
    simp only [hF, div_eq_mul_inv, id, Pi.inv_apply]
  have hmeas : ∀ q : ℂ, 0 < q.re → AEStronglyMeasurable (F q) (volume.restrict (Ioi 0)) :=
    fun q hq => (continuous_integrand hc a hq).aestronglyMeasurable
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := F) (F' := F') (x₀ := q₀) (bound := fun v => c * Real.exp (-a * v) / (c * r) ^ 2)
    (Metric.ball_mem_nhds q₀ hr0)
    (by
      filter_upwards [Metric.ball_mem_nhds q₀ hr0] with q hq
      exact hmeas q (lt_of_lt_of_le hr0 (hball q hq)))
    (integrableOn_integrand hc ha hq₀')
    (by
      have hc' : Continuous (F' q₀) := by
        simp only [hF']
        exact Continuous.mul (f := fun v : ℝ => (Real.exp (-a * v) : ℂ)) (by fun_prop)
          (Continuous.div (f := fun _ : ℝ => -(I * c * 1))
            (g := fun v : ℝ => ((v : ℂ) + I * c * q₀) ^ 2) (by fun_prop) (by fun_prop)
            fun v => pow_ne_zero 2 (den_ne_zero hc v hq₀'))
      exact hc'.aestronglyMeasurable)
    (Eventually.of_forall fun v q hq => by
      have hq' := hball q hq
      have hn := le_norm_den hc.le v (hr0.le.trans hq')
      have hcr : c * r ≤ ‖(v : ℂ) + I * c * q‖ := le_trans (mul_le_mul_of_nonneg_left hq' hc.le) hn
      simp only [hF']
      rw [norm_mul, norm_div, norm_neg, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _), mul_one, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hc]
      have hcr0 : 0 < c * r := by positivity
      have h3 : c / ‖(v : ℂ) + I * c * q‖ ^ 2 ≤ c / (c * r) ^ 2 :=
        div_le_div_of_nonneg_left hc.le (by positivity) (pow_le_pow_left₀ hcr0.le hcr 2)
      calc Real.exp (-a * v) * (c / ‖(v : ℂ) + I * c * q‖ ^ 2)
          ≤ Real.exp (-a * v) * (c / (c * r) ^ 2) := mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le
        _ = c * Real.exp (-a * v) / (c * r) ^ 2 := by ring)
    ((exp_neg_integrableOn_Ioi 0 ha).const_mul c |>.div_const _)
    (Eventually.of_forall fun v q hq => hderiv v q hq)
  exact key.2.differentiableAt.differentiableWithinAt

/-- **The uniform bound** `‖G_c(a, q)‖ ≤ 2Γ(3/4)(1/(cκ))^{3/4}(1/a)^{3/4}` for `0 < κ ≤ Re q − |Im q|`. -/
theorem norm_lapG_le {c a κ : ℝ} (hc : 0 < c) (ha : 0 < a) (hκ0 : 0 < κ) {q : ℂ} (hκ : κ ≤ q.re - |q.im|) :
    ‖lapG c a q‖ ≤ 2 * Gamma (3 / 4) * (1 / (c * κ)) ^ (3 / 4 : ℝ) * (1 / a) ^ (3 / 4 : ℝ) := by
  set m := c * κ with hm
  have hm0 : 0 < m := by positivity
  set g : ℝ → ℝ := fun v => 2 * (1 / m) ^ (3 / 4 : ℝ) * (v ^ ((3 / 4 : ℝ) - 1) * Real.exp (-(a * v))) with hg
  have hgi : ∫ v in Ioi (0 : ℝ), g v = 2 * (1 / m) ^ (3 / 4 : ℝ) * ((1 / a) ^ (3 / 4 : ℝ) * Gamma (3 / 4)) := by
    rw [integral_const_mul, Real.integral_rpow_mul_exp_neg_mul_Ioi (by norm_num) ha]
  have hgint : IntegrableOn g (Ioi 0) := by
    refine Integrable.of_integral_ne_zero ?_
    rw [hgi]
    have := Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 3 / 4)
    positivity
  have hb : ∀ᵐ v ∂(volume.restrict (Ioi (0 : ℝ))),
      ‖(Real.exp (-a * v) : ℂ) / ((v : ℂ) + I * c * q)‖ ≤ g v := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    have hv0 : 0 < v := hv
    have hd := half_le_norm_den hc.le v hκ
    have hgm := rpow_mul_rpow_le hv0.le hm0.le
    have hp : 0 < v ^ (1 / 4 : ℝ) * m ^ (3 / 4 : ℝ) := by positivity
    have hden : v ^ (1 / 4 : ℝ) * m ^ (3 / 4 : ℝ) / 2 ≤ ‖(v : ℂ) + I * c * q‖ := by linarith
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have e1 : v ^ ((3 / 4 : ℝ) - 1) * v ^ (1 / 4 : ℝ) = 1 := by
      rw [← Real.rpow_add hv0]; norm_num
    have e2 : (1 / m) ^ (3 / 4 : ℝ) * m ^ (3 / 4 : ℝ) = 1 := by
      rw [← Real.mul_rpow (by positivity) hm0.le, one_div_mul_cancel hm0.ne', Real.one_rpow]
    have hg' : g v = 2 * Real.exp (-a * v) / (v ^ (1 / 4 : ℝ) * m ^ (3 / 4 : ℝ)) := by
      simp only [hg]
      rw [eq_div_iff hp.ne', show -(a * v) = -a * v by ring]
      calc 2 * (1 / m) ^ (3 / 4 : ℝ) * (v ^ ((3 / 4 : ℝ) - 1) * Real.exp (-a * v)) *
            (v ^ (1 / 4 : ℝ) * m ^ (3 / 4 : ℝ))
          = 2 * Real.exp (-a * v) * ((v ^ ((3 / 4 : ℝ) - 1) * v ^ (1 / 4 : ℝ)) *
            ((1 / m) ^ (3 / 4 : ℝ) * m ^ (3 / 4 : ℝ))) := by ring
        _ = 2 * Real.exp (-a * v) := by rw [e1, e2]; ring
    rw [hg', div_le_div_iff₀ (lt_of_lt_of_le (by positivity) hden) hp]
    have he := Real.exp_pos (-a * v)
    nlinarith
  calc ‖lapG c a q‖ ≤ ∫ v in Ioi (0 : ℝ), g v := norm_integral_le_of_norm_le hgint hb
    _ = _ := by rw [hgi]; ring

end Cvs.Prolate.Hardy.OddCrossLaplaceAmplitude

end
