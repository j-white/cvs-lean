import Mathlib
import Cvs.Upstream.ExpSumBlaschkeProduct
import Cvs.Upstream.RightHalfPlaneCauchyHardy

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The exponential sum on `[0, T]` and the two-ended error

On `[0, T]`, `∫ |h_a|² = Re G(a) − Re G(a_T)` with `a_T = a e^{−p̄T}`, and `∫ h_a e^{−wu} = L_a(w) + err(w)`
up to the reflected end: `err(w) = −e^{−wT}L_{a_T}(w) + e^{−2wT}∫_0^T h_a e^{wu} du` is holomorphic on
`Re w > −ε` and `|err(w)| ≤ 2e^{−T Re w}(Re G(a)/(2 Re w))^{1/2}` for `Re w > 0`.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology Finset
open scoped Interval ComplexConjugate
open Cvs.Upstream.ExpSumBlaschkeProduct (lap gram)

namespace Cvs.Upstream.ExpSumTwoEndedError

set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Objects -/

/-- The exponential sum `h_a(u) = Σ a_i e^{−p̄_i u}`. -/
def expSum (p a : ι → ℂ) (u : ℝ) : ℂ := ∑ i, a i * cexp (-conj (p i) * u)

/-- The shifted coefficients `a_i e^{−p̄_i T}`. -/
def shift (p : ι → ℂ) (T : ℝ) (a : ι → ℂ) : ι → ℂ := fun i => a i * cexp (-conj (p i) * T)

/-- `∫_0^T e^{cu} du`, written as the entire function `T·dslope exp 0 (cT)`. -/
def rint (c : ℂ) (T : ℝ) : ℂ := T * dslope cexp 0 (c * T)

/-- The two-ended error `err(w) = −e^{−wT}L_{a_T}(w) + e^{−2wT}Σ a_i ∫_0^T e^{(w − p̄_i)u} du`. -/
def err (p : ι → ℂ) (T : ℝ) (a : ι → ℂ) (w : ℂ) : ℂ :=
  -(cexp (-(w * T)) * lap p (shift p T a) w) + cexp (-(2 * w * T)) * ∑ i, a i * rint (w - conj (p i)) T

/-! ### `rint` -/

theorem rint_of_ne {c : ℂ} (hc : c ≠ 0) (T : ℝ) : rint c T = (cexp (c * T) - 1) / c := by
  unfold rint
  by_cases hT : (T : ℂ) = 0
  · rw [hT]; simp
  · rw [dslope_of_ne _ (mul_ne_zero hc hT), slope_def_field, Complex.exp_zero, sub_zero]
    field_simp

/-- `∫_0^T e^{cu} du = rint c T`. -/
theorem integral_exp_eq_rint (c : ℂ) (T : ℝ) : ∫ u in (0 : ℝ)..T, cexp (c * u) = rint c T := by
  by_cases hc : c = 0
  · subst hc
    simp [rint, dslope_same]
  · rw [integral_exp_mul_complex hc, rint_of_ne hc]
    simp

/-- `c ↦ rint c T` is entire. -/
theorem differentiable_rint (T : ℝ) : Differentiable ℂ fun c => rint c T := by
  have h : DifferentiableOn ℂ (dslope cexp 0) univ :=
    (differentiableOn_dslope Filter.univ_mem).2 Complex.differentiable_exp.differentiableOn
  intro c
  exact (differentiableAt_const _).mul
    ((h.differentiableAt Filter.univ_mem).comp c (by fun_prop))

/-! ### Integrals of the exponential sum -/

theorem continuous_expSum (p a : ι → ℂ) : Continuous (expSum p a) := by
  unfold expSum; fun_prop

/-- `∫_0^T h_a(u)e^{cu} du = Σ a_i rint(c − p̄_i, T)`. -/
theorem integral_expSum_mul_exp (p a : ι → ℂ) (c : ℂ) (T : ℝ) :
    ∫ u in (0 : ℝ)..T, expSum p a u * cexp (c * u) = ∑ i, a i * rint (c - conj (p i)) T := by
  have e : (fun u : ℝ => expSum p a u * cexp (c * u))
      = fun u : ℝ => ∑ i, a i * cexp ((c - conj (p i)) * u) := by
    funext u
    unfold expSum
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_assoc, ← Complex.exp_add]
    congr 2; ring
  rw [e, intervalIntegral.integral_finsetSum fun i _ => (by fun_prop : Continuous fun u : ℝ =>
    a i * cexp ((c - conj (p i)) * u)).intervalIntegrable _ _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [intervalIntegral.integral_const_mul, integral_exp_eq_rint]

/-- **The Laplace transform on `[0, T]`**: `∫_0^T h_a e^{−wu} = L_a(w) − e^{−wT}L_{a_T}(w)`. -/
theorem integral_expSum_mul_exp_neg (p a : ι → ℂ) {w : ℂ} (hw : ∀ i, w + conj (p i) ≠ 0) (T : ℝ) :
    ∫ u in (0 : ℝ)..T, expSum p a u * cexp (-w * u)
      = lap p a w - cexp (-(w * T)) * lap p (shift p T a) w := by
  rw [integral_expSum_mul_exp, lap, lap, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hc : -w - conj (p i) ≠ 0 := by
    rw [show -w - conj (p i) = -(w + conj (p i)) by ring]; exact neg_ne_zero.2 (hw i)
  rw [rint_of_ne hc, shift]
  have h1 := hw i
  have e1 : cexp ((-w - conj (p i)) * T) = cexp (-(w * T)) * cexp (-conj (p i) * T) := by
    rw [← Complex.exp_add]; congr 1; ring
  rw [e1]
  field_simp
  ring

/-- **The norm on `[0, T]`**: `∫_0^T |h_a|² = Re G(a) − Re G(a_T)` for points in `Re > 0`. -/
theorem integral_norm_sq_expSum {p : ι → ℂ} (hp : ∀ i, 0 < (p i).re) (a : ι → ℂ) (T : ℝ) :
    ∫ u in (0 : ℝ)..T, ‖expSum p a u‖ ^ 2 = (gram p a).re - (gram p (shift p T a)).re := by
  have hconj : ∀ u : ℝ, conj (expSum p a u) = ∑ k, conj (a k) * cexp (-(p k) * u) := by
    intro u
    unfold expSum
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, ← Complex.exp_conj]
    simp
  have hpt : ∀ u : ℝ, (((‖expSum p a u‖ ^ 2 : ℝ)) : ℂ)
      = ∑ k, conj (a k) * (expSum p a u * cexp (-(p k) * u)) := by
    intro u
    rw [Complex.ofReal_pow, ← Complex.mul_conj', hconj, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hw : ∀ k i, p k + conj (p i) ≠ 0 := fun k i =>
    Cvs.Upstream.ExpSumBlaschkeProduct.add_conj_ne_zero (hp i) (hp k).le
  have hc : (((∫ u in (0 : ℝ)..T, ‖expSum p a u‖ ^ 2 : ℝ)) : ℂ)
      = gram p a - gram p (shift p T a) := by
    rw [← intervalIntegral.integral_ofReal, funext hpt,
      intervalIntegral.integral_finsetSum fun k _ => (show Continuous fun u : ℝ =>
        conj (a k) * (expSum p a u * cexp (-(p k) * u)) by
          have := continuous_expSum p a; fun_prop).intervalIntegrable _ _]
    simp_rw [intervalIntegral.integral_const_mul]
    rw [Cvs.Upstream.ExpSumBlaschkeProduct.gram, Cvs.Upstream.ExpSumBlaschkeProduct.gram, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show (-(p k)) = -(p k) from rfl, integral_expSum_mul_exp_neg p a (hw k) T, shift, map_mul,
      ← Complex.exp_conj]
    simp only [map_neg, Complex.conj_conj, map_mul, Complex.conj_ofReal]
    rw [neg_mul]
    ring
  have := congrArg Complex.re hc
  rw [Complex.ofReal_re] at this
  rw [this, Complex.sub_re]

/-! ### Bounds -/

/-- `Re G(a_T) ≤ Re G(a)` for `T ≥ 0`. -/
theorem gram_shift_re_le {p : ι → ℂ} (hp : ∀ i, 0 < (p i).re) (a : ι → ℂ) {T : ℝ} (hT : 0 ≤ T) :
    (gram p (shift p T a)).re ≤ (gram p a).re := by
  have h := intervalIntegral.integral_nonneg (μ := volume) hT fun u _ => sq_nonneg ‖expSum p a u‖
  rw [integral_norm_sq_expSum hp a T] at h
  linarith

/-- `∫_0^T |h_a|² ≤ Re G(a)`. -/
theorem integral_norm_sq_expSum_le {p : ι → ℂ} {ε : ℝ} (hε0 : 0 < ε) (hε : ∀ i, ε ≤ (p i).re)
    (a : ι → ℂ) (T : ℝ) : ∫ u in (0 : ℝ)..T, ‖expSum p a u‖ ^ 2 ≤ (gram p a).re := by
  have hp : ∀ i, 0 < (p i).re := fun i => hε0.trans_le (hε i)
  rw [integral_norm_sq_expSum hp a T]
  linarith [Cvs.Upstream.ExpSumBlaschkeProduct.gram_re_nonneg hε0 hε (shift p T a)]

/-- The error is holomorphic on `Re w > −ε`. -/
theorem differentiableOn_err {p : ι → ℂ} {ε : ℝ} (hε : ∀ i, ε ≤ (p i).re) (T : ℝ) (a : ι → ℂ) :
    DifferentiableOn ℂ (err p T a) {s | -ε < s.re} := by
  have hl := Cvs.Upstream.ExpSumBlaschkeProduct.differentiableOn_lap hε (shift p T a)
  have hr := differentiable_rint T
  intro w hw
  refine DifferentiableAt.differentiableWithinAt ?_
  have hlw : DifferentiableAt ℂ (lap p (shift p T a)) w :=
    hl.differentiableAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hw)
  unfold err
  refine ((DifferentiableAt.mul (by fun_prop) hlw).neg).add ((by fun_prop : DifferentiableAt ℂ
    (fun w : ℂ => cexp (-(2 * w * T))) w).mul (DifferentiableAt.fun_sum fun i _ => ?_))
  exact (differentiableAt_const _).mul ((hr _).comp w (by fun_prop))

/-- `∫_0^T e^{2cu} du ≤ e^{2cT}/(2c)` for `c > 0`. -/
theorem integral_exp_two_mul_le {c : ℝ} (hc : 0 < c) (T : ℝ) :
    ∫ u in (0 : ℝ)..T, Real.exp (2 * c * u) ≤ Real.exp (2 * c * T) / (2 * c) := by
  have h2 : (2 * c) ≠ 0 := by positivity
  rw [intervalIntegral.integral_comp_mul_left (fun u => Real.exp u) h2, integral_exp, mul_zero,
    Real.exp_zero, smul_eq_mul]
  rw [inv_mul_eq_div]
  exact div_le_div_of_nonneg_right (by linarith [Real.exp_pos 0]) (by positivity)

/-- **Cauchy–Schwarz on `[0, T]`** for the reflected end: `|∫_0^T h_a e^{wu}|² ≤ Re G(a) e^{2T Re w}/(2 Re w)`. -/
theorem norm_sq_integral_expSum_mul_exp_le {p : ι → ℂ} {ε : ℝ} (hε0 : 0 < ε) (hε : ∀ i, ε ≤ (p i).re)
    (a : ι → ℂ) {T : ℝ} (hT : 0 ≤ T) {w : ℂ} (hw : 0 < w.re) :
    ‖∫ u in (0 : ℝ)..T, expSum p a u * cexp (w * u)‖ ^ 2
      ≤ (gram p a).re * (Real.exp (2 * w.re * T) / (2 * w.re)) := by
  have hc1 := continuous_expSum p a
  have hc2 : Continuous fun u : ℝ => cexp (w * u) := by fun_prop
  rw [intervalIntegral.integral_of_le hT]
  have hcs := Cvs.Upstream.RightHalfPlaneCauchyHardy.norm_integral_mul_sq_le (μ := volume.restrict (Ioc 0 T)) hc1.aestronglyMeasurable
    hc2.aestronglyMeasurable
    (((hc1.norm.pow 2).integrableOn_Icc (a := 0) (b := T)).mono_set Ioc_subset_Icc_self)
    (((hc2.norm.pow 2).integrableOn_Icc (a := 0) (b := T)).mono_set Ioc_subset_Icc_self)
  refine hcs.trans ?_
  have h1 : ∫ u in Ioc 0 T, ‖expSum p a u‖ ^ 2 ≤ (gram p a).re := by
    have := integral_norm_sq_expSum_le hε0 hε a T
    rwa [intervalIntegral.integral_of_le hT] at this
  have h2 : ∫ u in Ioc 0 T, ‖cexp (w * u)‖ ^ 2 ≤ Real.exp (2 * w.re * T) / (2 * w.re) := by
    have e : (fun u : ℝ => ‖cexp (w * u)‖ ^ 2) = fun u : ℝ => Real.exp (2 * w.re * u) := by
      funext u
      rw [Complex.norm_exp, ← Real.exp_nat_mul]
      congr 1; simp; ring
    rw [e, ← intervalIntegral.integral_of_le hT]
    exact integral_exp_two_mul_le hw T
  have h0 : 0 ≤ ∫ u in Ioc 0 T, ‖cexp (w * u)‖ ^ 2 := integral_nonneg fun u => sq_nonneg _
  have hG := Cvs.Upstream.ExpSumBlaschkeProduct.gram_re_nonneg hε0 hε a
  calc (∫ u in Ioc 0 T, ‖expSum p a u‖ ^ 2) * ∫ u in Ioc 0 T, ‖cexp (w * u)‖ ^ 2
      ≤ (gram p a).re * ∫ u in Ioc 0 T, ‖cexp (w * u)‖ ^ 2 := mul_le_mul_of_nonneg_right h1 h0
    _ ≤ _ := mul_le_mul_of_nonneg_left h2 hG

/-- **The error bound**: `|err(w)| ≤ 2e^{−T Re w}(Re G(a)/(2 Re w))^{1/2}` for `Re w > 0`, `T ≥ 0`. -/
theorem norm_err_le {p : ι → ℂ} {ε : ℝ} (hε0 : 0 < ε) (hε : ∀ i, ε ≤ (p i).re) (a : ι → ℂ)
    {T : ℝ} (hT : 0 ≤ T) {w : ℂ} (hw : 0 < w.re) :
    ‖err p T a w‖ ≤ 2 * Real.exp (-(w.re * T)) * √((gram p a).re / (2 * w.re)) := by
  have hp : ∀ i, 0 < (p i).re := fun i => hε0.trans_le (hε i)
  have hG := Cvs.Upstream.ExpSumBlaschkeProduct.gram_re_nonneg hε0 hε a
  set S := √((gram p a).re / (2 * w.re)) with hS
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  -- the tail
  have hA : ‖cexp (-(w * T)) * lap p (shift p T a) w‖ ≤ Real.exp (-(w.re * T)) * S := by
    rw [norm_mul, Complex.norm_exp]
    have he : (-(w * (T : ℂ))).re = -(w.re * T) := by simp
    rw [he]
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
    have h1 := Cvs.Upstream.ExpSumBlaschkeProduct.norm_sq_lap_le hε0 hε (shift p T a) hw
    have h2 : (gram p (shift p T a)).re / (2 * w.re) ≤ (gram p a).re / (2 * w.re) :=
      div_le_div_of_nonneg_right (gram_shift_re_le hp a hT) (by positivity)
    rw [hS]
    exact Real.le_sqrt_of_sq_le (h1.trans h2)
  -- the reflected end
  have hB : ‖cexp (-(2 * w * T)) * ∑ i, a i * rint (w - conj (p i)) T‖ ≤ Real.exp (-(w.re * T)) * S := by
    rw [← integral_expSum_mul_exp, norm_mul, Complex.norm_exp]
    have he : (-(2 * w * (T : ℂ))).re = -(2 * w.re * T) := by simp
    rw [he]
    have h1 := norm_sq_integral_expSum_mul_exp_le hε0 hε a hT hw
    have h2 : ‖∫ u in (0 : ℝ)..T, expSum p a u * cexp (w * u)‖ ≤ Real.exp (w.re * T) * S := by
      refine abs_le_of_sq_le_sq' ?_ (by positivity) |>.2
      rw [mul_pow, hS, Real.sq_sqrt (by positivity), ← Real.exp_nat_mul]
      refine h1.trans_eq ?_
      push_cast
      ring_nf
    calc Real.exp (-(2 * w.re * T)) * ‖∫ u in (0 : ℝ)..T, expSum p a u * cexp (w * u)‖
        ≤ Real.exp (-(2 * w.re * T)) * (Real.exp (w.re * T) * S) :=
          mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
      _ = Real.exp (-(w.re * T)) * S := by
          rw [← mul_assoc, ← Real.exp_add]; ring_nf
  unfold err
  calc ‖-(cexp (-(w * T)) * lap p (shift p T a) w) + cexp (-(2 * w * T)) * ∑ i, a i * rint (w - conj (p i)) T‖
      ≤ ‖cexp (-(w * T)) * lap p (shift p T a) w‖ + ‖cexp (-(2 * w * T)) * ∑ i, a i * rint (w - conj (p i)) T‖ := by
        refine (norm_add_le _ _).trans ?_; rw [norm_neg]
    _ ≤ Real.exp (-(w.re * T)) * S + Real.exp (-(w.re * T)) * S := add_le_add hA hB
    _ = 2 * Real.exp (-(w.re * T)) * S := by ring

end Cvs.Upstream.ExpSumTwoEndedError

end
