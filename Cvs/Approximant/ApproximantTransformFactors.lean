import Mathlib
import Cvs.Upstream.CauchySchwarzLine
import Cvs.WeilForm.Mollify.ComposedApproximant
import Cvs.WeilForm.Mollify.ComposedApproximantL2
import Cvs.WeilForm.Mollify.MollifiedL2
import Cvs.WeilForm.Mollify.MollifierKernel
import Cvs.WeilForm.Mollify.MollifyShiftedEnergy
import Cvs.WeilForm.SelfConvolutionTransform
import Cvs.Zeta.ExplicitFormula.HannWindowShifts
import Cvs.Zeta.ExplicitFormula.WindowTransformByParts
import Cvs.Zeta.ExplicitFormula.WindowTransformCubicDecay
import Cvs.Zeta.ExplicitFormula.WindowTransformFullLine

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The window transform of `ComposedApproximant`'s approximant factors through the transform of the test

For `η ∈ L²` vanishing off `(0, L]`, `a = dila n`, `δ = shift L n` and every `ξ ∈ ℂ`:
`W_L(pre η n)(ξ) = k̂_δ(ξ) · e^{−iδξ} · √a · W_L η(aξ)`, with `k̂_δ(ξ) = ∫ k_δ(t) e^{−itξ} dt` and
`‖k̂_δ(ξ)‖ ≤ e^{δ|Im ξ|}`; so `‖W_L η(ξ)‖ ≤ C/(1 + |Re ξ|)` on `|Im ξ| ≤ b` gives `2e^{Lb/2}C/(1 + |Re ξ|)`
for every approximant, and `‖W_L f(ξ) − W_L g(ξ)‖ ≤ e^{L|Im ξ|}√L‖f − g‖₂` gives pointwise convergence.
-/

noncomputable section

open MeasureTheory Real Set Filter Topology Complex Cvs.Upstream.L2DilationContinuity

namespace Cvs.Approximant.ApproximantTransformFactors

open Cvs.WeilForm.SelfConvolutionTransform (cf)
open Cvs.WeilForm.Mollify.ComposedApproximant (pre shifted dila shift)

/-! ### The transform as a full-line integral -/

/-- `‖e^{−isξ}‖ = e^{s Im ξ}`. -/
theorem norm_char (ξ : ℂ) (s : ℝ) : ‖Complex.exp (-((s : ℂ) * ξ) * I)‖ = Real.exp (s * ξ.im) :=
  Cvs.Detection.norm_char ξ s

/-- For `g` vanishing off `(0, L]`, `W_L g(ξ) = ∫_ℝ e^{−isξ} g(s) ds`. -/
theorem windowTransform_eq_integral {L : ℝ} (hL : 0 ≤ L) {g : ℝ → ℝ}
    (hg : ∀ s ∉ Ioc (0 : ℝ) L, g s = 0) (ξ : ℂ) :
    Cvs.Detection.windowTransform L (cf g) ξ
      = ∫ s : ℝ, Complex.exp (-((s : ℂ) * ξ) * I) * (g s : ℂ) := by
  rw [Cvs.Detection.windowTransform_eq_integral hL]
  congr 1; funext s
  by_cases hs : s ∈ Ioc (0 : ℝ) L
  · rw [Cvs.Detection.truncate_of_mem hs]; rfl
  · rw [Cvs.Detection.truncate_of_not_mem hs, hg s hs]; simp

/-- A function integrable on `[α, β]` and vanishing off it stays integrable after multiplying by the
character `e^{−isξ}`. -/
theorem integrable_char_mul {α β : ℝ} {h : ℝ → ℂ} (hh : IntegrableOn h (Icc α β))
    (hs : ∀ s ∉ Icc α β, h s = 0) (ξ : ℂ) :
    Integrable fun s : ℝ => Complex.exp (-((s : ℂ) * ξ) * I) * h s := by
  have hon := hh.continuousOn_mul (Cvs.Detection.continuous_char ξ).continuousOn isCompact_Icc
  refine (integrableOn_iff_integrable_of_support_subset ?_).1 hon
  intro s hs'
  by_contra hn
  exact hs' (by simp [hs s hn])

/-- An `L²` function vanishing off `(0, L]` is integrable on `[0, L]`. -/
theorem integrableOn_of_memLp {L : ℝ} {g : ℝ → ℝ} (hg : MemLp g 2 volume) :
    IntegrableOn g (Icc (0 : ℝ) L) := by
  have : IsFiniteMeasure (volume.restrict (Icc (0 : ℝ) L)) :=
    isFiniteMeasure_restrict.2 measure_Icc_lt_top.ne
  exact (hg.restrict (Icc (0 : ℝ) L)).integrable (by norm_num)

theorem integrable_char_mul_of_memLp {L : ℝ} {g : ℝ → ℝ} (hg : MemLp g 2 volume)
    (hgs : ∀ s ∉ Ioc (0 : ℝ) L, g s = 0) (ξ : ℂ) :
    Integrable fun s : ℝ => Complex.exp (-((s : ℂ) * ξ) * I) * (g s : ℂ) :=
  integrable_char_mul (α := 0) (β := L) (integrableOn_of_memLp hg).ofReal
    (fun s hs => by rw [hgs s fun h => hs (Ioc_subset_Icc_self h)]; simp) ξ

/-! ### The mollifier's transform -/

/-- The transform of the mollifier, `k̂_δ(ξ) = ∫ k_δ(t) e^{−itξ} dt`. -/
def kernelHat {δ : ℝ} (hδ : 0 < δ) (ξ : ℂ) : ℂ :=
  ∫ t : ℝ, Complex.exp (-((t : ℂ) * ξ) * I) * (Cvs.WeilForm.Mollify.MollifierKernel.kernel hδ t : ℂ)

theorem integrable_char_mul_kernel {δ : ℝ} (hδ : 0 < δ) (ξ : ℂ) :
    Integrable fun t : ℝ => Complex.exp (-((t : ℂ) * ξ) * I)
      * (Cvs.WeilForm.Mollify.MollifierKernel.kernel hδ t : ℂ) := by
  refine Continuous.integrable_of_hasCompactSupport
    ((Cvs.Detection.continuous_char ξ).mul
      (Complex.continuous_ofReal.comp (Cvs.WeilForm.Mollify.MollifierKernel.continuous_kernel hδ))) ?_
  exact ((Cvs.WeilForm.Mollify.MollifierKernel.hasCompactSupport_kernel hδ).comp_left
    Complex.ofReal_zero).mul_left

/-- **`‖k̂_δ(ξ)‖ ≤ e^{δ|Im ξ|}`**: the mollifier is a probability density on `[−δ, δ]`. -/
theorem norm_kernelHat_le {δ : ℝ} (hδ : 0 < δ) (ξ : ℂ) :
    ‖kernelHat hδ ξ‖ ≤ Real.exp (δ * |ξ.im|) := by
  have hb : ∀ t : ℝ, ‖Complex.exp (-((t : ℂ) * ξ) * I) * (Cvs.WeilForm.Mollify.MollifierKernel.kernel hδ t : ℂ)‖
      ≤ Real.exp (δ * |ξ.im|) * Cvs.WeilForm.Mollify.MollifierKernel.kernel hδ t := by
    intro t
    have hk := Cvs.WeilForm.Mollify.MollifierKernel.kernel_nonneg hδ t
    rw [norm_mul, norm_char, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hk]
    by_cases ht : δ < |t|
    · rw [Cvs.WeilForm.Mollify.MollifierKernel.kernel_eq_zero hδ ht]; simp
    · refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) hk
      push Not at ht
      calc t * ξ.im ≤ |t * ξ.im| := le_abs_self _
        _ = |t| * |ξ.im| := abs_mul _ _
        _ ≤ δ * |ξ.im| := mul_le_mul_of_nonneg_right ht (abs_nonneg _)
  refine (norm_integral_le_of_norm_le
    ((Cvs.WeilForm.Mollify.MollifierKernel.integrable_kernel hδ).const_mul _)
    (Eventually.of_forall hb)).trans (le_of_eq ?_)
  rw [integral_const_mul, Cvs.WeilForm.Mollify.MollifierKernel.integral_kernel, mul_one]

/-! ### The factorisation -/

/-- The transform of the dilate-and-translate: `∫ e^{−isξ} S(s) ds = e^{−iδξ} √a W_L η(aξ)`. -/
theorem integral_char_shifted {L : ℝ} (hL : 0 ≤ L) {η : ℝ → ℝ}
    (hηs : ∀ s ∉ Ioc (0 : ℝ) L, η s = 0) (n : ℕ) (ξ : ℂ) :
    ∫ s : ℝ, Complex.exp (-((s : ℂ) * ξ) * I) * (shifted L η n s : ℂ)
      = Complex.exp (-((shift L n : ℂ) * ξ) * I) * ((Real.sqrt (dila n) : ℝ) : ℂ)
        * Cvs.Detection.windowTransform L (cf η) ((dila n : ℂ) * ξ) := by
  set a := dila n with ha
  set δ := shift L n with hδ
  have ha0 : 0 < a := Cvs.WeilForm.Mollify.ComposedApproximant.dila_pos n
  have hsa : Real.sqrt a ≠ 0 := (Real.sqrt_pos.2 ha0).ne'
  rw [windowTransform_eq_integral hL hηs]
  -- translate by `δ`
  rw [← integral_add_right_eq_self _ δ]
  have h1 : ∀ u : ℝ, Complex.exp (-(((u + δ : ℝ) : ℂ) * ξ) * I) * (shifted L η n (u + δ) : ℂ)
      = Complex.exp (-((δ : ℂ) * ξ) * I) * ((Real.sqrt a)⁻¹ : ℝ)
        * (Complex.exp (-((u : ℂ) * ξ) * I) * (η (a⁻¹ * u) : ℂ)) := by
    intro u
    simp only [shifted, dilate, ← ha, ← hδ, add_neg_cancel_right, div_eq_inv_mul]
    push_cast
    rw [show -(((u : ℂ) + δ) * ξ) * I = -((δ : ℂ) * ξ) * I + -((u : ℂ) * ξ) * I by ring,
      Complex.exp_add]
    ring
  simp_rw [h1]
  rw [integral_const_mul]
  -- dilate by `a`
  have h2 := Measure.integral_comp_inv_mul_left
    (fun w : ℝ => Complex.exp (-(((a * w : ℝ) : ℂ) * ξ) * I) * (η w : ℂ)) a
  have h3 : ∀ u : ℝ, Complex.exp (-(((a * (a⁻¹ * u) : ℝ) : ℂ) * ξ) * I) * (η (a⁻¹ * u) : ℂ)
      = Complex.exp (-((u : ℂ) * ξ) * I) * (η (a⁻¹ * u) : ℂ) := by
    intro u; rw [← mul_assoc, mul_inv_cancel₀ ha0.ne', one_mul]
  simp only [h3] at h2
  rw [h2, abs_of_pos ha0]
  have h4 : ∀ w : ℝ, Complex.exp (-(((a * w : ℝ) : ℂ) * ξ) * I) * (η w : ℂ)
      = Complex.exp (-((w : ℂ) * ((a : ℂ) * ξ)) * I) * (η w : ℂ) := by
    intro w; push_cast; ring_nf
  simp_rw [h4, Complex.real_smul]
  have h5 : ((Real.sqrt a)⁻¹ : ℝ) * (a : ℂ) = ((Real.sqrt a : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul]
    congr 1
    field_simp
    rw [Real.sq_sqrt ha0.le]
  rw [← h5]
  ring

/-- **The transform of the approximant factors**:
`W_L(pre η n)(ξ) = k̂_δ(ξ) · e^{−iδξ} √a W_L η(aξ)`, `a = dila n`, `δ = shift L n`. -/
theorem windowTransform_pre {L : ℝ} (hL : 0 < L) {η : ℝ → ℝ} (hη : MemLp η 2 volume)
    (hηs : ∀ s ∉ Ioc (0 : ℝ) L, η s = 0) (n : ℕ) (ξ : ℂ) :
    Cvs.Detection.windowTransform L (cf (pre hL η n)) ξ
      = kernelHat (Cvs.WeilForm.Mollify.ComposedApproximant.shift_pos hL n) ξ
        * (Complex.exp (-((shift L n : ℂ) * ξ) * I) * ((Real.sqrt (dila n) : ℝ) : ℂ)
          * Cvs.Detection.windowTransform L (cf η) ((dila n : ℂ) * ξ)) := by
  set hδ := Cvs.WeilForm.Mollify.ComposedApproximant.shift_pos hL n
  set k := Cvs.WeilForm.Mollify.MollifierKernel.kernel hδ with hk
  set S := shifted L η n with hS
  set e : ℝ → ℂ := fun s => Complex.exp (-((s : ℂ) * ξ) * I) with he
  have hSmem : MemLp S 2 volume := Cvs.WeilForm.Mollify.ComposedApproximant.memLp_shifted hη L n
  have hSs : ∀ s ∉ Ioc (0 : ℝ) L, S s = 0 := by
    intro s hs
    refine Cvs.WeilForm.Mollify.ComposedApproximant.support_shifted hηs n s fun h => hs ⟨?_, ?_⟩
    · linarith [h.1, Cvs.WeilForm.Mollify.ComposedApproximant.shift_pos hL n]
    · have := Cvs.WeilForm.Mollify.ComposedApproximant.fit L n
      linarith [h.2, Cvs.WeilForm.Mollify.ComposedApproximant.shift_pos hL n]
  set A : ℝ → ℂ := fun u => e u * (S u : ℂ) with hA
  set B : ℝ → ℂ := fun t => e t * (k t : ℂ) with hB
  have hAi : Integrable A := integrable_char_mul_of_memLp hSmem hSs ξ
  have hBi : Integrable B := integrable_char_mul_kernel hδ ξ
  have hconv : ∀ s : ℝ, e s * (pre hL η n s : ℂ)
      = MeasureTheory.convolution B A (ContinuousLinearMap.mul ℂ ℂ) volume s := by
    intro s
    rw [MeasureTheory.convolution, pre, Cvs.WeilForm.Mollify.MollifyShiftedEnergy.conv, ← integral_complex_ofReal,
      ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [ContinuousLinearMap.mul_apply', hA, hB, he]
    rw [show -((s : ℂ) * ξ) * I = -((t : ℂ) * ξ) * I + -(((s - t : ℝ) : ℂ) * ξ) * I by
      push_cast; ring, Complex.exp_add]
    push_cast
    ring
  rw [windowTransform_eq_integral hL.le (Cvs.WeilForm.Mollify.ComposedApproximant.support_pre hL hηs n)]
  rw [integral_congr_ae (Eventually.of_forall hconv), integral_convolution (ContinuousLinearMap.mul ℂ ℂ) hBi hAi, ContinuousLinearMap.mul_apply']
  simp only [hA, hB, he]
  rw [integral_char_shifted hL.le hηs n ξ]
  rfl

/-! ### The uniform envelope -/

/-- **The envelope passes to every approximant**: if `‖W_L η(ξ)‖ ≤ C/(1 + |Re ξ|)` on `|Im ξ| ≤ b`,
then `‖W_L(pre η n)(ξ)‖ ≤ 2e^{Lb/2}C/(1 + |Re ξ|)` on the same strip, for every `n`. -/
theorem norm_windowTransform_pre_le {L : ℝ} (hL : 0 < L) {η : ℝ → ℝ} (hη : MemLp η 2 volume)
    (hηs : ∀ s ∉ Ioc (0 : ℝ) L, η s = 0) {b C : ℝ}
    (henv : ∀ ξ : ℂ, |ξ.im| ≤ b →
      ‖Cvs.Detection.windowTransform L (cf η) ξ‖ ≤ C / (1 + |ξ.re|))
    (n : ℕ) (ξ : ℂ) (hξ : |ξ.im| ≤ b) :
    ‖Cvs.Detection.windowTransform L (cf (pre hL η n)) ξ‖
      ≤ 2 * Real.exp (L * b / 2) * C / (1 + |ξ.re|) := by
  set a := dila n with ha
  set δ := shift L n with hδdef
  have ha0 : 0 < a := Cvs.WeilForm.Mollify.ComposedApproximant.dila_pos n
  have ha1 : a < 1 := Cvs.WeilForm.Mollify.ComposedApproximant.dila_lt_one n
  have ha2 : 1 / 2 ≤ a := Cvs.WeilForm.Mollify.ComposedApproximant.dila_half_le n
  have hδ0 : 0 < δ := Cvs.WeilForm.Mollify.ComposedApproximant.shift_pos hL n
  have hδL : δ ≤ L / 4 := by
    rw [hδdef, Cvs.WeilForm.Mollify.ComposedApproximant.shift, div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  have hb0 : 0 ≤ b := (abs_nonneg _).trans hξ
  have hC0 : 0 ≤ C := by
    have h := (norm_nonneg _).trans (henv ((ξ.im : ℝ) * I) (by simpa using hξ))
    exact (div_nonneg_iff.1 h).elim (fun h => h.1) fun h => absurd h.2 (by
      have : (0 : ℝ) ≤ |(((ξ.im : ℝ) : ℂ) * I).re| := abs_nonneg _
      linarith)
  have haξ : |((a : ℂ) * ξ).im| ≤ b := by
    rw [Complex.im_ofReal_mul, abs_mul, abs_of_pos ha0]
    nlinarith [abs_nonneg ξ.im]
  have hre : ((a : ℂ) * ξ).re = a * ξ.re := Complex.re_ofReal_mul a ξ
  have hW := henv _ haξ
  rw [hre, abs_mul, abs_of_pos ha0] at hW
  rw [windowTransform_pre hL hη hηs n ξ, norm_mul, norm_mul, norm_mul, norm_char,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hk := norm_kernelHat_le hδ0 ξ
  have he : Real.exp (δ * ξ.im) ≤ Real.exp (δ * |ξ.im|) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (le_abs_self _) hδ0.le)
  have hsq : Real.sqrt a ≤ 1 := Real.sqrt_le_one.mpr ha1.le
  have hexp : Real.exp (δ * |ξ.im|) * Real.exp (δ * |ξ.im|) ≤ Real.exp (L * b / 2) := by
    rw [← Real.exp_add, Real.exp_le_exp]
    nlinarith [abs_nonneg ξ.im]
  have hr0 : 0 ≤ |ξ.re| := abs_nonneg _
  have hden : C / (1 + a * |ξ.re|) ≤ 2 * C / (1 + |ξ.re|) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg hC0 hr0]
  have hWn : 0 ≤ ‖Cvs.Detection.windowTransform L (cf η) ((a : ℂ) * ξ)‖ := norm_nonneg _
  calc ‖kernelHat hδ0 ξ‖ * (Real.exp (δ * ξ.im) * Real.sqrt a
        * ‖Cvs.Detection.windowTransform L (cf η) ((a : ℂ) * ξ)‖)
      ≤ Real.exp (δ * |ξ.im|) * (Real.exp (δ * |ξ.im|) * 1 * (2 * C / (1 + |ξ.re|))) := by
        gcongr
        exact hW.trans hden
    _ ≤ Real.exp (L * b / 2) * (2 * C / (1 + |ξ.re|)) := by
        rw [mul_one, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right hexp (by positivity)
    _ = 2 * Real.exp (L * b / 2) * C / (1 + |ξ.re|) := by ring

/-! ### Pointwise convergence -/

/-- **The transform is `L²`-Lipschitz at each point**:
`‖W_L f(ξ) − W_L g(ξ)‖ ≤ e^{L|Im ξ|} √L ‖f − g‖₂` for `f, g ∈ L²` vanishing off `(0, L]`. -/
theorem norm_windowTransform_sub_le {L : ℝ} (hL : 0 ≤ L) {f g : ℝ → ℝ} (hf : MemLp f 2 volume)
    (hg : MemLp g 2 volume) (hfs : ∀ s ∉ Ioc (0 : ℝ) L, f s = 0)
    (hgs : ∀ s ∉ Ioc (0 : ℝ) L, g s = 0) (ξ : ℂ) :
    ‖Cvs.Detection.windowTransform L (cf f) ξ - Cvs.Detection.windowTransform L (cf g) ξ‖
      ≤ Real.exp (L * |ξ.im|) * (Real.sqrt L * Real.sqrt (∫ s, (f s - g s) ^ 2)) := by
  set h : ℝ → ℝ := fun s => f s - g s with hh
  have hhm : MemLp h 2 volume := hf.sub hg
  have hhs : ∀ s ∉ Ioc (0 : ℝ) L, h s = 0 := fun s hs => by simp [hh, hfs s hs, hgs s hs]
  rw [windowTransform_eq_integral hL hfs, windowTransform_eq_integral hL hgs,
    ← integral_sub (integrable_char_mul_of_memLp hf hfs ξ) (integrable_char_mul_of_memLp hg hgs ξ)]
  have hcongr : (fun s : ℝ => Complex.exp (-((s : ℂ) * ξ) * I) * (f s : ℂ)
      - Complex.exp (-((s : ℂ) * ξ) * I) * (g s : ℂ))
      = fun s : ℝ => Complex.exp (-((s : ℂ) * ξ) * I) * (h s : ℂ) := by
    funext s; simp only [hh]; push_cast; ring
  rw [hcongr]
  set ind : ℝ → ℝ := (Ioc (0 : ℝ) L).indicator 1 with hind
  have hindm : MemLp ind 2 volume :=
    (memLp_indicator_iff_restrict measurableSet_Ioc.nullMeasurableSet).2 (by
      have : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) L)) :=
        isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
      exact memLp_const 1)
  have hbd : ∀ s : ℝ, ‖Complex.exp (-((s : ℂ) * ξ) * I) * (h s : ℂ)‖
      ≤ Real.exp (L * |ξ.im|) * (|h s| * ind s) := by
    intro s
    rw [norm_mul, norm_char, Complex.norm_real, Real.norm_eq_abs]
    by_cases hs : s ∈ Ioc (0 : ℝ) L
    · rw [hind, indicator_of_mem hs, Pi.one_apply, mul_one]
      refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (abs_nonneg _)
      calc s * ξ.im ≤ s * |ξ.im| := mul_le_mul_of_nonneg_left (le_abs_self _) hs.1.le
        _ ≤ L * |ξ.im| := mul_le_mul_of_nonneg_right hs.2 (abs_nonneg _)
    · rw [hhs s hs]; simp
  have habs : MemLp (fun s => |h s|) 2 volume := hhm.abs
  have hint : Integrable fun s => |h s| * ind s := by
    have := MeasureTheory.MemLp.integrable_mul habs hindm
    exact this
  refine (norm_integral_le_of_norm_le (hint.const_mul _) (Eventually.of_forall hbd)).trans ?_
  rw [integral_const_mul]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_nonneg _)
  have hcs := Cvs.Upstream.CauchySchwarzLine.abs_integral_mul_le habs hindm
  have hind2 : ∫ s, ind s ^ 2 = L := by
    have : (fun s => ind s ^ 2) = ind := by
      funext s; by_cases hs : s ∈ Ioc (0 : ℝ) L <;> simp [hind, hs]
    rw [this, hind, integral_indicator measurableSet_Ioc]
    simp [hL]
  have hh2 : ∫ s, |h s| ^ 2 = ∫ s, (f s - g s) ^ 2 := by
    congr 1; funext s; rw [sq_abs]
  rw [hind2, hh2] at hcs
  calc ∫ s, |h s| * ind s ≤ |∫ s, |h s| * ind s| := le_abs_self _
    _ ≤ _ := by rw [mul_comm]; exact hcs

/-- **The approximants' transforms converge pointwise**: `W_L(pre η n)(ξ) → W_L η(ξ)`. -/
theorem tendsto_windowTransform_pre {L : ℝ} (hL : 0 < L) {η : ℝ → ℝ} (hη : MemLp η 2 volume)
    (hηm : Measurable η) (hηs : ∀ s ∉ Ioc (0 : ℝ) L, η s = 0) (ξ : ℂ) :
    Tendsto (fun n => Cvs.Detection.windowTransform L (cf (pre hL η n)) ξ) atTop
      (𝓝 (Cvs.Detection.windowTransform L (cf η) ξ)) := by
  have hpre : ∀ n, MemLp (pre hL η n) 2 volume := fun n =>
    Cvs.WeilForm.Mollify.MollifiedL2.memLp_conv (Cvs.WeilForm.Mollify.ComposedApproximant.memLp_shifted hη L n)
      (Cvs.WeilForm.Mollify.ComposedApproximant.measurable_shifted hηm L n)
      (Cvs.WeilForm.Mollify.MollifierKernel.continuous_kernel _) (Cvs.WeilForm.Mollify.MollifierKernel.hasCompactSupport_kernel _)
      (Cvs.WeilForm.Mollify.MollifierKernel.measurable_kernel _) (Cvs.WeilForm.Mollify.MollifierKernel.integrable_kernel _)
      (Cvs.WeilForm.Mollify.MollifierKernel.kernel_nonneg _) (Cvs.WeilForm.Mollify.MollifierKernel.integral_kernel _)
  have herr := Cvs.WeilForm.Mollify.ComposedApproximantL2.tendsto_pre_error hL hη hηm
  have hsq : Tendsto (fun n => Real.exp (L * |ξ.im|) * (Real.sqrt L
      * Real.sqrt (∫ s, (pre hL η n s - η s) ^ 2))) atTop (𝓝 0) := by
    have := ((Real.continuous_sqrt.tendsto 0).comp herr).const_mul (Real.sqrt L)
      |>.const_mul (Real.exp (L * |ξ.im|))
    simpa [Function.comp_def] using this
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun _ => norm_nonneg _)
    (fun n => norm_windowTransform_sub_le hL.le (hpre n) hη
      (Cvs.WeilForm.Mollify.ComposedApproximant.support_pre hL hηs n) hηs ξ) hsq

end Cvs.Approximant.ApproximantTransformFactors
