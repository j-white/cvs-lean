import Mathlib
import Cvs.Upstream.ExpSumBlaschkeProduct
import Cvs.Upstream.HardyCorrectedInterpolation
import Cvs.Upstream.RightHalfPlaneCauchyHardy

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The model-space kernels of the points

With `B` the Blaschke product of the points, `∫ B(iy)/|iy − μ|² dy = πB(μ)/Re μ` (Cvs.Upstream.RightHalfPlaneCauchyHardy). Pairing with the `H²`
representatives `(1 − \overline{B(λ̄)}B)/(z + λ)` and `(1 − B/B(α))/(z − α)` gives
`|Σ_k ā_k/(p_k + λ)|² ≤ Re G(a)(1 − |B(λ̄)|²)/(2 Re λ)` and `|Σ_k ā_k/(p_k − α)|² ≤ Re G(a)(|B(α)|^{−2} − 1)/(2 Re α)`
(caseinf-W Theorem C (iv), terms `I₁` and `I₃`).
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology Finset
open scoped Interval ComplexConjugate
open Cvs.Upstream.ExpSumBlaschkeProduct (lap gram blaschke bfac)

namespace Cvs.Upstream.ModelSpaceKernels

set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The Blaschke product as an analytic function -/

theorem differentiableOn_blaschke {p : ι → ℂ} {ε : ℝ} (hε : ∀ i, ε ≤ (p i).re) :
    DifferentiableOn ℂ (blaschke p) {s | -ε < s.re} := by
  intro z hz
  simp only [mem_ofPred_eq] at hz
  refine DifferentiableAt.differentiableWithinAt ?_
  unfold blaschke
  refine DifferentiableAt.fun_finsetProd fun i _ => ?_
  unfold bfac
  exact (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => z - p i) z).div (by fun_prop)
    (Cvs.Upstream.ExpSumBlaschkeProduct.add_conj_ne_zero' (by linarith [hε i]))

theorem norm_blaschke_le_one {p : ι → ℂ} (hp : ∀ i, 0 < (p i).re) {z : ℂ} (hz : 0 ≤ z.re) :
    ‖blaschke p z‖ ≤ 1 := Cvs.Upstream.ExpSumBlaschkeProduct.norm_prod_bfac_le_one hp univ hz

theorem norm_blaschke_I {p : ι → ℂ} (hp : ∀ i, 0 < (p i).re) (y : ℝ) : ‖blaschke p (y * I)‖ = 1 :=
  Cvs.Upstream.ExpSumBlaschkeProduct.norm_prod_bfac_I hp univ y

theorem blaschke_self (p : ι → ℂ) (k : ι) : blaschke p (p k) = 0 := by
  unfold blaschke
  exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp [bfac])

/-- `B(z)/(z + μ̄)` satisfies `RightHalfPlaneCauchyHardy`'s hypotheses. -/
theorem div_dec {p : ι → ℂ} (hp : ∀ i, 0 < (p i).re) (μ : ℂ) :
    ∀ s : ℂ, 0 ≤ s.re → 2 * ‖μ‖ ≤ ‖s‖ → ‖blaschke p s / (s + conj μ)‖ ≤ 2 / ‖s‖ := by
  intro s hs hR
  have h1 := Cvs.Upstream.ExpSumBlaschkeProduct.half_norm_le_norm_add_conj hR
  by_cases hs0 : ‖s‖ = 0
  · rw [hs0, div_zero]
    have hμ : ‖μ‖ = 0 := by linarith [norm_nonneg μ]
    simp [norm_eq_zero.1 hs0, norm_eq_zero.1 hμ]
  have hsp : 0 < ‖s‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hs0)
  rw [norm_div]
  calc ‖blaschke p s‖ / ‖s + conj μ‖ ≤ 1 / (‖s‖ / 2) :=
        div_le_div₀ zero_le_one (norm_blaschke_le_one hp hs) (by positivity) h1
    _ = 2 / ‖s‖ := by field_simp

/-- **The Blaschke product against a Poisson kernel**: `∫ B(iy)/((iy + μ̄)(μ − iy)) dy = 2πB(μ)/(2 Re μ)`. -/
theorem integral_blaschke_poisson {p : ι → ℂ} {ε : ℝ} (hε0 : 0 < ε) (hε : ∀ i, ε ≤ (p i).re) {μ : ℂ}
    (hμ : 0 < μ.re) :
    ∫ y : ℝ, blaschke p (y * I) / (y * I + conj μ) / (μ - y * I)
      = 2 * Real.pi * (blaschke p μ / (2 * μ.re)) := by
  have hp : ∀ i, 0 < (p i).re := fun i => hε0.trans_le (hε i)
  set ε' := min ε μ.re
  have hε' : 0 < ε' := lt_min hε0 hμ
  have hd : DifferentiableOn ℂ (fun s => blaschke p s / (s + conj μ)) {s | -ε' < s.re} := by
    intro s hs
    simp only [mem_ofPred_eq] at hs
    have h1 : -ε < s.re := by linarith [min_le_left ε μ.re]
    have h2 : -μ.re < s.re := by linarith [min_le_right ε μ.re]
    exact ((differentiableOn_blaschke hε).differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds h1)).div (by fun_prop)
      (Cvs.Upstream.ExpSumBlaschkeProduct.add_conj_ne_zero' h2) |>.differentiableWithinAt
  have h := Cvs.Upstream.RightHalfPlaneCauchyHardy.integral_div_sub_eq hε' hd (div_dec hp μ) hμ
  rw [h]
  congr 1
  have : μ + conj μ = ((2 * μ.re : ℝ) : ℂ) := by apply Complex.ext <;> simp; ring
  rw [this]; push_cast; ring

/-- `(iy + μ̄)(μ − iy) = |iy + μ̄|²`, with `|iy + μ̄|² = (Re μ)² + (y − Im μ)²`. -/
theorem poisson_eq (μ : ℂ) (y : ℝ) :
    ((y : ℂ) * I + conj μ) * (μ - y * I) = ((μ.re ^ 2 + (y - μ.im) ^ 2 : ℝ) : ℂ) := by
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.add_re, Complex.sub_re, Complex.mul_im, Complex.add_im,
      Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.conj_re,
      Complex.conj_im]
    ring
  · simp only [Complex.mul_re, Complex.add_re, Complex.sub_re, Complex.mul_im, Complex.add_im,
      Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.conj_re,
      Complex.conj_im]
    ring

theorem norm_sq_I_add_conj (μ : ℂ) (y : ℝ) : ‖(y : ℂ) * I + conj μ‖ ^ 2 = μ.re ^ 2 + (y - μ.im) ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp; ring

/-- **The kernel integral**: `∫ |1 − cB(iy)|²/|iy + μ̄|² dy = (π/Re μ)(1 + |c|² − 2 Re(cB(μ)))`. -/
theorem integral_norm_sq_one_sub_mul {p : ι → ℂ} {ε : ℝ} (hε0 : 0 < ε) (hε : ∀ i, ε ≤ (p i).re) {μ : ℂ}
    (hμ : 0 < μ.re) (c : ℂ) :
    ∫ y : ℝ, ‖1 - c * blaschke p (y * I)‖ ^ 2 / ‖(y : ℂ) * I + conj μ‖ ^ 2
      = Real.pi / μ.re * (1 + ‖c‖ ^ 2 - 2 * (c * blaschke p μ).re) := by
  have hp : ∀ i, 0 < (p i).re := fun i => hε0.trans_le (hε i)
  set B := blaschke p
  have hBc : Continuous fun y : ℝ => B (y * I) := by
    refine (differentiableOn_blaschke hε).continuousOn.comp_continuous (by fun_prop) fun y => ?_
    simp only [mem_ofPred_eq, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self]
    linarith
  have hD : ∀ y : ℝ, 0 < μ.re ^ 2 + (y - μ.im) ^ 2 := fun y => by positivity
  have hpt : ∀ y : ℝ, ‖1 - c * B (y * I)‖ ^ 2 / ‖(y : ℂ) * I + conj μ‖ ^ 2
      = (1 + ‖c‖ ^ 2) * (1 / (μ.re ^ 2 + (y - μ.im) ^ 2))
        - 2 * (c * (B (y * I) / ((y : ℂ) * I + conj μ) / (μ - y * I))).re := by
    intro y
    have hB1 := norm_blaschke_I hp y
    rw [norm_sq_I_add_conj]
    have hn : Complex.normSq (B (y * I)) = 1 := by rw [Complex.normSq_eq_norm_sq, hB1]; norm_num
    have e1 : ‖1 - c * B (y * I)‖ ^ 2 = 1 + ‖c‖ ^ 2 - 2 * (c * B (y * I)).re := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub, map_one, Complex.normSq_mul, hn, mul_one,
        Complex.normSq_eq_norm_sq, one_mul, Complex.conj_re]
    have e2 : B (y * I) / ((y : ℂ) * I + conj μ) / (μ - y * I)
        = B (y * I) / ((μ.re ^ 2 + (y - μ.im) ^ 2 : ℝ) : ℂ) := by
      rw [div_div, poisson_eq]
    have e3 : (c * (B (y * I) / ((μ.re ^ 2 + (y - μ.im) ^ 2 : ℝ) : ℂ))).re
        = (c * B (y * I)).re / (μ.re ^ 2 + (y - μ.im) ^ 2) := by
      rw [← mul_div_assoc, Complex.div_ofReal_re]
    rw [e1, e2, e3]
    field_simp
  have hi1 : Integrable fun y : ℝ => 1 / (μ.re ^ 2 + (y - μ.im) ^ 2) := Cvs.Upstream.RightHalfPlaneCauchyHardy.integrable_inv_sq_add_sq hμ μ.im
  have hi2 : Integrable fun y : ℝ => c * (B (y * I) / ((y : ℂ) * I + conj μ) / (μ - y * I)) := by
    refine (hi1.ofReal (𝕜 := ℂ)).const_mul ‖c‖ |>.mono ?_ ?_
    · refine (continuous_const.mul ?_).aestronglyMeasurable
      refine (hBc.div (by fun_prop) fun y => ?_).div (by fun_prop) fun y => ?_
      · exact Cvs.Upstream.ExpSumBlaschkeProduct.add_conj_ne_zero hμ (by simp)
      · intro h; have := congrArg Complex.re h; simp at this; linarith
    · refine Eventually.of_forall fun y => ?_
      rw [div_div, poisson_eq, norm_mul, norm_div, norm_blaschke_I hp y, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (hD y), norm_mul]
      have h2 : ‖((‖c‖ : ℝ) : ℂ)‖ = ‖c‖ := by rw [Complex.norm_real, norm_norm]
      rw [h2]
      refine le_of_eq ?_
      congr 1
      rw [RCLike.norm_ofReal, abs_of_pos (one_div_pos.2 (hD y))]
  have hi3 : Integrable fun y : ℝ => 2 * (c * (B (y * I) / ((y : ℂ) * I + conj μ) / (μ - y * I))).re :=
    (hi2.re).const_mul 2
  have hre_int : ∫ y : ℝ, (c * (B (y * I) / ((y : ℂ) * I + conj μ) / (μ - y * I))).re
      = (∫ y : ℝ, c * (B (y * I) / ((y : ℂ) * I + conj μ) / (μ - y * I))).re := integral_re hi2
  rw [integral_congr_ae (Eventually.of_forall hpt), integral_sub (hi1.const_mul _) hi3,
    integral_const_mul, integral_const_mul, Cvs.Upstream.RightHalfPlaneCauchyHardy.integral_inv_sq_add_sq hμ, hre_int,
    integral_const_mul, integral_blaschke_poisson hε0 hε hμ]
  have hre : (c * (2 * (Real.pi : ℂ) * (B μ / (2 * (μ.re : ℂ))))).re = Real.pi / μ.re * (c * B μ).re := by
    rw [show c * (2 * (Real.pi : ℂ) * (B μ / (2 * (μ.re : ℂ)))) = ((Real.pi / μ.re : ℝ) : ℂ) * (c * B μ) by
      push_cast; field_simp]
    rw [Complex.re_ofReal_mul]
  rw [hre]
  ring

/-- **The kernel term `I₁`**: `|Σ_k ā_k/(p_k + μ̄)| ≤ (Re G(a))^{1/2}((1 − |B(μ)|²)/(2 Re μ))^{1/2}`. -/
theorem norm_sum_div_add_le {p : ι → ℂ} {ε : ℝ} (hε0 : 0 < ε) (hε : ∀ i, ε ≤ (p i).re) (a : ι → ℂ)
    {μ : ℂ} (hμ : 0 < μ.re) :
    ‖∑ k, conj (a k) * (1 / (p k + conj μ))‖
      ≤ √((gram p a).re) * √((1 - ‖blaschke p μ‖ ^ 2) / (2 * μ.re)) := by
  have hp : ∀ i, 0 < (p i).re := fun i => hε0.trans_le (hε i)
  set B := blaschke p
  set c := conj (B μ)
  set F : ℂ → ℂ := fun z => (1 - c * B z) / (z + conj μ) with hF
  set ε' := min ε μ.re
  have hε' : 0 < ε' := lt_min hε0 hμ
  have hFd : DifferentiableOn ℂ F {s | -ε' < s.re} := by
    intro s hs
    simp only [mem_ofPred_eq] at hs
    have h1 : -ε < s.re := by linarith [min_le_left ε μ.re]
    have h2 : -μ.re < s.re := by linarith [min_le_right ε μ.re]
    have hB := (differentiableOn_blaschke hε).differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds h1)
    exact ((differentiableAt_const _).sub ((differentiableAt_const _).mul hB)).div (by fun_prop)
      (Cvs.Upstream.ExpSumBlaschkeProduct.add_conj_ne_zero' h2) |>.differentiableWithinAt
  have hFdec : ∀ s : ℂ, 0 ≤ s.re → 2 * ‖μ‖ ≤ ‖s‖ → ‖F s‖ ≤ (2 * (1 + ‖c‖)) / ‖s‖ := by
    intro s hs hR
    have h1 := Cvs.Upstream.ExpSumBlaschkeProduct.half_norm_le_norm_add_conj hR
    by_cases hs0 : ‖s‖ = 0
    · have hμ0 : μ = 0 := norm_eq_zero.1 (by linarith [norm_nonneg μ])
      rw [hμ0] at hμ; simp at hμ
    have hsp : 0 < ‖s‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hs0)
    have hn : ‖1 - c * B s‖ ≤ 1 + ‖c‖ := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_one, norm_mul]
      have := norm_blaschke_le_one hp hs
      nlinarith [norm_nonneg c]
    simp only [hF]
    rw [norm_div]
    calc ‖1 - c * B s‖ / ‖s + conj μ‖ ≤ (1 + ‖c‖) / (‖s‖ / 2) :=
          div_le_div₀ (by positivity) hn (by positivity) h1
      _ = 2 * (1 + ‖c‖) / ‖s‖ := by field_simp
  have hpk : ∀ k, F (p k) = 1 / (p k + conj μ) := fun k => by
    have : B (p k) = 0 := blaschke_self p k
    simp only [hF]; rw [this, mul_zero, sub_zero]
  have h := Cvs.Upstream.HardyCorrectedInterpolation.norm_sum_conj_mul_le_h2 hε0 hε a hε' hFd hFdec
  simp only [hpk] at h
  refine h.trans_eq ?_
  have hI : ∫ y : ℝ, ‖F (y * I)‖ ^ 2 = Real.pi / μ.re * (1 - ‖B μ‖ ^ 2) := by
    have e : (fun y : ℝ => ‖F (y * I)‖ ^ 2)
        = fun y : ℝ => ‖1 - c * B (y * I)‖ ^ 2 / ‖(y : ℂ) * I + conj μ‖ ^ 2 := by
      funext y; simp only [hF]; rw [norm_div, div_pow]
    rw [e, integral_norm_sq_one_sub_mul hε0 hε hμ c]
    have h1 : ‖c‖ = ‖B μ‖ := Complex.norm_conj _
    have h2 : (c * B μ).re = ‖B μ‖ ^ 2 := by
      rw [mul_comm, Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re]
    rw [h1, h2]; ring
  rw [hI]
  have hpi := Real.pi_pos
  rw [mul_comm (√((gram p a).re))]
  rw [div_eq_mul_inv, mul_comm, ← mul_assoc]
  congr 1
  rw [← Real.sqrt_inv, ← Real.sqrt_mul (by positivity)]
  · congr 1; field_simp

/-- **The kernel term `I₃`**: `|Σ_k ā_k/(p_k − α)| ≤ (Re G(a))^{1/2}((|B(α)|^{−2} − 1)/(2 Re α))^{1/2}`
for `B(α) ≠ 0`. -/
theorem norm_sum_div_sub_le {p : ι → ℂ} {ε : ℝ} (hε0 : 0 < ε) (hε : ∀ i, ε ≤ (p i).re) (a : ι → ℂ)
    {α : ℂ} (hα : 0 < α.re) (hBα : blaschke p α ≠ 0) :
    ‖∑ k, conj (a k) * (1 / (p k - α))‖
      ≤ √((gram p a).re) * √((‖blaschke p α‖⁻¹ ^ 2 - 1) / (2 * α.re)) := by
  have hp : ∀ i, 0 < (p i).re := fun i => hε0.trans_le (hε i)
  set B := blaschke p
  set e := (B α)⁻¹
  set F : ℂ → ℂ := fun z => -(dslope B α z) * e with hF
  set ε' := min ε α.re
  have hε' : 0 < ε' := lt_min hε0 hα
  have hU : IsOpen {s : ℂ | -ε' < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hBd : DifferentiableOn ℂ B {s : ℂ | -ε' < s.re} :=
    (differentiableOn_blaschke hε).mono fun s hs => by
      simp only [mem_ofPred_eq] at hs ⊢; linarith [min_le_left ε α.re]
  have hαU : α ∈ {s : ℂ | -ε' < s.re} := by
    simp only [mem_ofPred_eq]; linarith [min_le_right ε α.re]
  have hFd : DifferentiableOn ℂ F {s | -ε' < s.re} :=
    (((differentiableOn_dslope (hU.mem_nhds hαU)).2 hBd).neg).mul_const e
  have hαne : α ≠ 0 := fun h => by rw [h] at hα; simp at hα
  have hFdec : ∀ s : ℂ, 0 ≤ s.re → 2 * ‖α‖ ≤ ‖s‖ → ‖F s‖ ≤ (2 * (1 + ‖B α‖) * ‖e‖) / ‖s‖ := by
    intro s hs hR
    have hαp : 0 < ‖α‖ := norm_pos_iff.2 hαne
    have hsp : 0 < ‖s‖ := by linarith
    have hsa : s ≠ α := fun h => by rw [h] at hR; linarith
    have hden : ‖s‖ / 2 ≤ ‖s - α‖ := by have := norm_sub_norm_le s α; linarith
    have hn : ‖B s - B α‖ ≤ 1 + ‖B α‖ :=
      (norm_sub_le _ _).trans (by linarith [norm_blaschke_le_one hp hs])
    simp only [hF]
    rw [dslope_of_ne _ hsa, slope_def_field, norm_mul, norm_neg, norm_div]
    calc ‖B s - B α‖ / ‖s - α‖ * ‖e‖ ≤ (1 + ‖B α‖) / (‖s‖ / 2) * ‖e‖ :=
          mul_le_mul_of_nonneg_right (div_le_div₀ (by positivity) hn (by positivity) hden) (norm_nonneg _)
      _ = 2 * (1 + ‖B α‖) * ‖e‖ / ‖s‖ := by field_simp
  have hpk : ∀ k, F (p k) = 1 / (p k - α) := fun k => by
    have h0 : B (p k) = 0 := blaschke_self p k
    have hne : p k ≠ α := fun h => hBα (by rw [← h]; exact h0)
    simp only [hF]
    rw [dslope_of_ne _ hne, slope_def_field, h0]
    have : p k - α ≠ 0 := sub_ne_zero.2 hne
    simp only [e]
    field_simp
    ring
  have h := Cvs.Upstream.HardyCorrectedInterpolation.norm_sum_conj_mul_le_h2 hε0 hε a hε' hFd hFdec
  simp only [hpk] at h
  refine h.trans_eq ?_
  have hI : ∫ y : ℝ, ‖F (y * I)‖ ^ 2 = Real.pi / α.re * (‖B α‖⁻¹ ^ 2 - 1) := by
    have e1 : (fun y : ℝ => ‖F (y * I)‖ ^ 2)
        = fun y : ℝ => ‖1 - e * B (y * I)‖ ^ 2 / ‖(y : ℂ) * I + conj α‖ ^ 2 := by
      funext y
      have hne : (y : ℂ) * I ≠ α := fun h => by
        have := congrArg Complex.re h; simp at this; linarith
      have hn : ‖(y : ℂ) * I + conj α‖ = ‖(y : ℂ) * I - α‖ := by
        rw [← norm_neg ((y : ℂ) * I + conj α), ← Complex.norm_conj ((y : ℂ) * I - α)]
        congr 1
        simp only [map_sub, map_mul, Complex.conj_ofReal, Complex.conj_I]
        ring
      simp only [hF]
      rw [dslope_of_ne _ hne, slope_def_field, hn]
      have h3 : (y : ℂ) * I - α ≠ 0 := sub_ne_zero.2 hne
      rw [show -((B ((y : ℂ) * I) - B α) / ((y : ℂ) * I - α)) * e = (1 - e * B ((y : ℂ) * I)) / ((y : ℂ) * I - α)
        by simp only [e]; field_simp; ring]
      rw [norm_div, div_pow]
    rw [e1, integral_norm_sq_one_sub_mul hε0 hε hα e]
    have h1 : (e * B α).re = 1 := by rw [inv_mul_cancel₀ hBα, Complex.one_re]
    have h2 : ‖e‖ = ‖B α‖⁻¹ := norm_inv _
    rw [h1, h2]; ring
  rw [hI]
  have hpi := Real.pi_pos
  rw [mul_comm (√((gram p a).re))]
  rw [div_eq_mul_inv, mul_comm, ← mul_assoc]
  congr 1
  rw [← Real.sqrt_inv, ← Real.sqrt_mul (by positivity)]
  · congr 1; field_simp

end Cvs.Upstream.ModelSpaceKernels

end
