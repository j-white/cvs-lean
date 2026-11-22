import Mathlib
import Cvs.Upstream.ExpSumBlaschkeProduct
import Cvs.Upstream.ExpSumContourInterpolation
import Cvs.Upstream.ExpSumTwoEndedError
import Cvs.Upstream.RightHalfPlaneCauchyHardy
import Cvs.Zeta.RectArgument

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The corrected interpolation of `H²` data

For `F` holomorphic on `Re > −ε` with `|F(s)| ≤ C/|s|` on `Re s ≥ 0`, `RightHalfPlaneCauchyHardy`'s Cauchy formula and Plancherel give
`|Σ_k ā_k F(p_k)| ≤ (∫|F(iy)|² dy)^{1/2}(Re G(a))^{1/2}/(2π)^{1/2}`, with no contour constant. With the contour bound
for the error (Cvs.Upstream.ExpSumContourInterpolation), the system `L_a + err = F` on the points has a solution with
`(1 − q)(Re G(a))^{1/2} ≤ (∫|F(iy)|²)^{1/2}/(2π)^{1/2}` (caseinf-W Theorem F (ii), (iii)).
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology Finset
open scoped Interval ComplexConjugate
open Cvs.Upstream.ExpSumBlaschkeProduct (lap gram blaschke)
open Cvs.Upstream.ExpSumTwoEndedError (err)
open Cvs.Upstream.ExpSumContourInterpolation (OnBd Inside evalMap)
open Cvs.Zeta (closedRect)

namespace Cvs.Upstream.HardyCorrectedInterpolation

set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The `H²` pairing bound**: `|Σ_k ā_k F(p_k)| ≤ (∫|F(iy)|²)^{1/2}(Re G(a))^{1/2}/(2π)^{1/2}`. -/
theorem norm_sum_conj_mul_le_h2 {p : ι → ℂ} {ε' : ℝ} (hε'0 : 0 < ε') (hε' : ∀ i, ε' ≤ (p i).re)
    (a : ι → ℂ) {F : ℂ → ℂ} {ε C R₀ : ℝ} (hε : 0 < ε) (hF : DifferentiableOn ℂ F {s | -ε < s.re})
    (hdec : ∀ s : ℂ, 0 ≤ s.re → R₀ ≤ ‖s‖ → ‖F s‖ ≤ C / ‖s‖) :
    ‖∑ k, conj (a k) * F (p k)‖
      ≤ √(∫ y : ℝ, ‖F (y * I)‖ ^ 2) * √((gram p a).re) / √(2 * Real.pi) := by
  have hp : ∀ i, 0 < (p i).re := fun i => hε'0.trans_le (hε' i)
  have hint : ∀ k, Integrable fun y : ℝ => F (y * I) / (p k - y * I) := fun k =>
    Cvs.Upstream.RightHalfPlaneCauchyHardy.integrable_div_sub_line hε hF hdec (hp k)
  have hsum : ∑ k, conj (a k) * F (p k)
      = (1 / (2 * Real.pi)) * ∫ y : ℝ, F (y * I) * conj (lap p a (y * I)) := by
    have e : (fun y : ℝ => F (y * I) * conj (lap p a (y * I)))
        = fun y : ℝ => ∑ k, conj (a k) * (F (y * I) / (p k - y * I)) := by
      funext y
      rw [Cvs.Upstream.ExpSumBlaschkeProduct.conj_lap_I, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [e, integral_finsetSum _ fun k _ => (hint k).const_mul _, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_const_mul, Cvs.Upstream.RightHalfPlaneCauchyHardy.integral_div_sub_eq hε hF hdec (hp k)]
    have := Real.pi_pos
    field_simp
  have hline : Continuous fun y : ℝ => F (y * I) := by
    refine hF.continuousOn.comp_continuous (by fun_prop) fun y => ?_
    simp only [mem_ofPred_eq, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self]
    linarith
  have hlline : Continuous fun y : ℝ => conj (lap p a (y * I)) := by
    have hl := Cvs.Upstream.ExpSumBlaschkeProduct.differentiableOn_lap hε' a
    refine Complex.continuous_conj.comp (hl.continuousOn.comp_continuous (by fun_prop) fun y => ?_)
    simp only [mem_ofPred_eq, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self]
    linarith
  have hF2 := Cvs.Upstream.RightHalfPlaneCauchyHardy.integrable_norm_sq_line hε hF hdec
  have hL2 := Cvs.Upstream.RightHalfPlaneCauchyHardy.integrable_norm_sq_line hε'0 (Cvs.Upstream.ExpSumBlaschkeProduct.differentiableOn_lap hε' a) (Cvs.Upstream.ExpSumBlaschkeProduct.lap_dec hp a)
  have hL2' : Integrable fun y : ℝ => ‖conj (lap p a (y * I))‖ ^ 2 := by
    simpa only [Complex.norm_conj] using hL2
  have hcs := Cvs.Upstream.RightHalfPlaneCauchyHardy.norm_integral_mul_sq_le hline.aestronglyMeasurable hlline.aestronglyMeasurable hF2 hL2'
  simp only [Complex.norm_conj] at hcs
  rw [Cvs.Upstream.ExpSumBlaschkeProduct.integral_norm_sq_lap hε'0 hε' a] at hcs
  have hpi := Real.pi_pos
  have hG := Cvs.Upstream.ExpSumBlaschkeProduct.gram_re_nonneg hε'0 hε' a
  have hI0 : 0 ≤ ∫ y : ℝ, ‖F (y * I)‖ ^ 2 := integral_nonneg fun y => sq_nonneg _
  rw [hsum, norm_mul]
  have hn : ‖(1 : ℂ) / (2 * Real.pi)‖ = 1 / (2 * Real.pi) := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpi]; norm_num
  rw [hn]
  have hb : ‖∫ y : ℝ, F (y * I) * conj (lap p a (y * I))‖
      ≤ √(∫ y : ℝ, ‖F (y * I)‖ ^ 2) * √(2 * Real.pi * (gram p a).re) := by
    rw [← Real.sqrt_mul hI0]
    exact Real.le_sqrt_of_sq_le hcs
  have e2 : √(2 * Real.pi * (gram p a).re) = √(2 * Real.pi) * √((gram p a).re) :=
    Real.sqrt_mul (by positivity) _
  rw [e2] at hb
  have hs : 0 < √(2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  calc 1 / (2 * Real.pi) * ‖∫ y : ℝ, F (y * I) * conj (lap p a (y * I))‖
      ≤ 1 / (2 * Real.pi) * (√(∫ y : ℝ, ‖F (y * I)‖ ^ 2) * (√(2 * Real.pi) * √((gram p a).re))) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = √(∫ y : ℝ, ‖F (y * I)‖ ^ 2) * √((gram p a).re) / √(2 * Real.pi) := by
        have h2 : √(2 * Real.pi) * √(2 * Real.pi) = 2 * Real.pi := Real.mul_self_sqrt (by positivity)
        set A := √(∫ y : ℝ, ‖F (y * I)‖ ^ 2)
        set B := √((gram p a).re)
        set S := √(2 * Real.pi)
        rw [← h2]
        field_simp

/-- The error against the coefficients: `|Σ_k ā_k err(p_k)| ≤ q Re G(a)`. -/
theorem norm_sum_err_le {p : ι → ℂ} {z w : ℂ} (hz : 0 < z.re) (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (hpin : ∀ k, Inside z w (p k)) {m : ℝ} (hm0 : 0 < m) (hm : ∀ u, OnBd z w u → m ≤ ‖blaschke p u‖)
    {T : ℝ} (hT : 0 ≤ T) (a : ι → ℂ) :
    ‖∑ k, conj (a k) * err p T a (p k)‖
      ≤ (2 * (w.re - z.re) + 2 * (w.im - z.im)) / (2 * Real.pi * m * √(2 * z.re))
        * (2 * Real.exp (-(z.re * T)) / √(2 * z.re)) * (gram p a).re := by
  have hε : ∀ i, z.re ≤ (p i).re := fun i => (hpin i).1.le
  have hG := Cvs.Upstream.ExpSumBlaschkeProduct.gram_re_nonneg hz hε a
  have hU'o : IsOpen {s : ℂ | -z.re < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hU'r : closedRect z w ⊆ {s : ℂ | -z.re < s.re} := by
    intro u hu
    have := hu.1
    rw [Set.mem_preimage, Set.uIcc_of_le hre] at this
    show -z.re < u.re
    linarith [this.1]
  have h := Cvs.Upstream.ExpSumContourInterpolation.norm_sum_conj_mul_le (a := a) hz hre him hpin hm0 hm hU'o hU'r
    (Cvs.Upstream.ExpSumTwoEndedError.differentiableOn_err hε T a) (fun u hu => Cvs.Upstream.ExpSumContourInterpolation.norm_err_le_onBd (a := a) hz hre hε hT hu)
  refine h.trans_eq ?_
  have : √((gram p a).re) * √((gram p a).re) = (gram p a).re := Real.mul_self_sqrt hG
  conv_rhs => rw [← this]
  ring

/-- **The corrected interpolation of `H²` data** (caseinf-W Theorem F (ii), (iii), by contour for the correction):
with `q < 1` there are coefficients with `L_a + err = F` at every point and
`(1 − q)(Re G(a))^{1/2} ≤ (∫|F(iy)|² dy)^{1/2}/(2π)^{1/2}`. -/
theorem exists_solution_h2 {p : ι → ℂ} (hpi : Function.Injective p) {z w : ℂ} (hz : 0 < z.re)
    (hre : z.re ≤ w.re) (him : z.im ≤ w.im) (hpin : ∀ k, Inside z w (p k)) {m : ℝ} (hm0 : 0 < m)
    (hm : ∀ u, OnBd z w u → m ≤ ‖blaschke p u‖) {T : ℝ} (hT : 0 ≤ T)
    (hq : (2 * (w.re - z.re) + 2 * (w.im - z.im)) / (2 * Real.pi * m * √(2 * z.re))
      * (2 * Real.exp (-(z.re * T)) / √(2 * z.re)) < 1)
    {F : ℂ → ℂ} {ε C R₀ : ℝ} (hε : 0 < ε) (hF : DifferentiableOn ℂ F {s | -ε < s.re})
    (hdec : ∀ s : ℂ, 0 ≤ s.re → R₀ ≤ ‖s‖ → ‖F s‖ ≤ C / ‖s‖) :
    ∃ a : ι → ℂ, (∀ k, lap p a (p k) + err p T a (p k) = F (p k))
      ∧ (1 - (2 * (w.re - z.re) + 2 * (w.im - z.im)) / (2 * Real.pi * m * √(2 * z.re))
          * (2 * Real.exp (-(z.re * T)) / √(2 * z.re))) * √((gram p a).re)
        ≤ √(∫ y : ℝ, ‖F (y * I)‖ ^ 2) / √(2 * Real.pi) := by
  set q := (2 * (w.re - z.re) + 2 * (w.im - z.im)) / (2 * Real.pi * m * √(2 * z.re))
      * (2 * Real.exp (-(z.re * T)) / √(2 * z.re)) with hqdef
  have hε' : ∀ i, z.re ≤ (p i).re := fun i => (hpin i).1.le
  have herr := norm_sum_err_le hz hre him hpin hm0 hm hT
  have hinj : Function.Injective (evalMap p T) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    have hk : ∀ k, lap p a (p k) = -err p T a (p k) := fun k => by
      have := congrFun ha k
      simp only [evalMap, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at this
      linear_combination this
    have hgram : gram p a = -∑ k, conj (a k) * err p T a (p k) := by
      rw [Cvs.Upstream.ExpSumBlaschkeProduct.gram, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hk k]; ring
    have hG := Cvs.Upstream.ExpSumBlaschkeProduct.gram_re_nonneg hz hε' a
    have h1 : (gram p a).re ≤ q * (gram p a).re := by
      have := herr a
      rw [← norm_neg, ← hgram] at this
      exact (Complex.re_le_norm _).trans this
    have h0 : (gram p a).re = 0 := by nlinarith
    exact Cvs.Upstream.ExpSumBlaschkeProduct.eq_zero_of_gram_re_eq_zero hpi hz hε' h0
  have hsurj : Function.Surjective (evalMap p T) := LinearMap.injective_iff_surjective.1 hinj
  obtain ⟨a, ha⟩ := hsurj fun k => F (p k)
  refine ⟨a, fun k => congrFun ha k, ?_⟩
  have hk : ∀ k, lap p a (p k) = F (p k) - err p T a (p k) := fun k => by
    have := congrFun ha k
    simp only [evalMap, LinearMap.coe_mk, AddHom.coe_mk] at this
    linear_combination this
  have hG := Cvs.Upstream.ExpSumBlaschkeProduct.gram_re_nonneg hz hε' a
  set S := √((gram p a).re) with hS
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hSS : S * S = (gram p a).re := Real.mul_self_sqrt hG
  have hgram : gram p a = (∑ k, conj (a k) * F (p k)) - ∑ k, conj (a k) * err p T a (p k) := by
    rw [Cvs.Upstream.ExpSumBlaschkeProduct.gram, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hk k]; ring
  have hF1 := norm_sum_conj_mul_le_h2 hz hε' a hε hF hdec
  set A := √(∫ y : ℝ, ‖F (y * I)‖ ^ 2) / √(2 * Real.pi) with hA
  have hF1' : ‖∑ k, conj (a k) * F (p k)‖ ≤ A * S := by
    refine hF1.trans_eq ?_; rw [hA]; ring
  have hnorm : ‖gram p a‖ ≤ A * S + q * (gram p a).re := by
    calc ‖gram p a‖ = ‖(∑ k, conj (a k) * F (p k)) - ∑ k, conj (a k) * err p T a (p k)‖ := by rw [hgram]
      _ ≤ _ := (norm_sub_le _ _).trans (add_le_add hF1' (herr a))
  have hbound : S * S ≤ A * S + q * (S * S) := by
    rw [hSS]; exact (Complex.re_le_norm _).trans hnorm
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  rcases hS0.lt_or_eq with hSp | hSz
  · have : S * ((1 - q) * S) ≤ S * A := by nlinarith
    exact le_of_mul_le_mul_left this hSp
  · rw [← hSz, mul_zero]; exact hA0

end Cvs.Upstream.HardyCorrectedInterpolation

end
