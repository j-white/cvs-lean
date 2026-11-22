import Mathlib
import Cvs.Finite.DividedDifferenceCommutator
import Cvs.Finite.EvenSectorZeroSide
import Cvs.Finite.OddSectorZeroSide
import Cvs.Finite.PairFormDividedDifference
import Cvs.Finite.ParitySectorDefect
import Cvs.Finite.TruncationQuadraticForm
import Cvs.Finite.TruncationZeroFreeOffAxes
import Cvs.Finite.ZeroSideGramMatrix
import Cvs.Route.ModeBoxIsometricTransfer
import Cvs.WeilForm.GaussianTestEnvelope
import Cvs.WeilForm.SelfConvolutionTransform
import Cvs.Zeta.ExplicitFormula.CompactTestAdmissibility
import Cvs.Zeta.ExplicitFormula.HannWindowShifts
import Cvs.Zeta.ExplicitFormula.PoleFactorRealPart
import Cvs.Zeta.ExplicitFormula.PrimeChannelFiniteSum
import Cvs.Zeta.GaussKernel.DivisorWeightCoordinates
import Cvs.Zeta.GaussKernel.ZetaZeroStatement
import Cvs.Zeta.ZeroSideMoments
import Cvs.Zeta.ZeroSideMomentsConverge

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# One zero in the two parity sectors: a difference of two squared pairings
For a profile `g` on the centred window, `z = x + iy`: `Re sqTransform(z) = (∫ g ue)² − (∫ g ve)²` if `g`
is even (`ue = cos xt cosh yt`, `ve = sin xt sinh yt`) and `(∫ g uo)² − (∫ g vo)²` if odd
(`uo = sin xt cosh yt`, `vo = cos xt sinh yt`). So, for every `L > 0`, `L` times `M_L`'s form on each sector
is `∑_ρ m_ρ` of these, and one such term over a nonnegative background leaves at most one negative
direction per sector.
-/

noncomputable section

open Real MeasureTheory Matrix Cvs.WeilForm.SelfConvolutionTransform

namespace Cvs.StepA.OneZeroParitySectors
open Cvs.ZeroCounting

/-! ### The centred transform -/

/-- The transform of `g` over the centred window `(−L/2, L/2)`, in the window transform's convention. -/
def ctr (L : ℝ) (g : ℝ → ℝ) (ξ : ℂ) : ℂ :=
  ∫ t in -(L / 2)..L / 2, Complex.exp (-((t : ℂ) * ξ) * Complex.I) * ((g t : ℝ) : ℂ)

/-- The window transform of the shifted profile is the phase `e^{−iξL/2}` times the centred transform. -/
theorem windowTransform_eq_ctr (L : ℝ) (g : ℝ → ℝ) (ξ : ℂ) :
    Cvs.Detection.windowTransform L (cf fun s => g (s - L / 2)) ξ
      = Complex.exp (-(((L / 2 : ℝ) : ℂ) * ξ) * Complex.I) * ctr L g ξ :=
  Cvs.WeilForm.GaussianTestEnvelope.windowTransform_shift L g ξ

/-- **The squared transform is the centred one at `±ξ`**: the phases cancel. -/
theorem sqTransform_eq_ctr (L : ℝ) (g : ℝ → ℝ) (ξ : ℂ) :
    Cvs.Detection.sqTransform L (cf fun s => g (s - L / 2)) ξ = ctr L g ξ * ctr L g (-ξ) := by
  rw [Cvs.Detection.sqTransform, windowTransform_eq_ctr, windowTransform_eq_ctr]
  have : Complex.exp (-(((L / 2 : ℝ) : ℂ) * ξ) * Complex.I)
      * Complex.exp (-(((L / 2 : ℝ) : ℂ) * -ξ) * Complex.I) = 1 := by
    rw [← Complex.exp_add, ← Complex.exp_zero]; congr 1; ring
  linear_combination (ctr L g ξ * ctr L g (-ξ)) * this

/-! ### The window pairing on continuous profiles -/

/-- The window pairing `⟨f, g⟩ = ∫_{−L/2}^{L/2} f g` on `C(ℝ, ℝ)`. -/
def winForm (L : ℝ) : LinearMap.BilinForm ℝ C(ℝ, ℝ) :=
  LinearMap.mk₂ ℝ (fun f g => ∫ t in -(L / 2)..L / 2, f t * g t)
    (fun f₁ f₂ g => by
      simp only [ContinuousMap.add_apply, add_mul]
      exact intervalIntegral.integral_add ((f₁.continuous.mul g.continuous).intervalIntegrable _ _)
        ((f₂.continuous.mul g.continuous).intervalIntegrable _ _))
    (fun c f g => by
      simp only [ContinuousMap.smul_apply, smul_eq_mul, mul_assoc]
      exact intervalIntegral.integral_const_mul c _)
    (fun f g₁ g₂ => by
      simp only [ContinuousMap.add_apply, mul_add]
      exact intervalIntegral.integral_add ((f.continuous.mul g₁.continuous).intervalIntegrable _ _)
        ((f.continuous.mul g₂.continuous).intervalIntegrable _ _))
    (fun c f g => by
      simp only [ContinuousMap.smul_apply, smul_eq_mul, mul_left_comm (f _)]
      exact intervalIntegral.integral_const_mul c _)

/-- The window pairing is the window integral of the product. -/
theorem winForm_apply (L : ℝ) (f g : C(ℝ, ℝ)) :
    winForm L f g = ∫ t in -(L / 2)..L / 2, f t * g t := rfl

/-- The window pairing is symmetric. -/
theorem winForm_isSymm (L : ℝ) : (winForm L).IsSymm :=
  ⟨fun f g => by simp only [winForm_apply, mul_comm]⟩

/-- The window pairing is positive semidefinite for `L ≥ 0`. -/
theorem winForm_self_nonneg {L : ℝ} (hL : 0 ≤ L) (f : C(ℝ, ℝ)) : 0 ≤ winForm L f f :=
  intervalIntegral.integral_nonneg (by linarith) fun t _ => mul_self_nonneg _

/-- The window pairing of a profile with itself is its square integral. -/
theorem winForm_sq (L : ℝ) (f : C(ℝ, ℝ)) :
    winForm L f f = ∫ t in -(L / 2)..L / 2, f t ^ 2 := by
  rw [winForm_apply]; simp only [sq]

/-! ### The sector weights -/

/-- Even-sector weight `cos(xt) cosh(yt)`, `z = x + iy`. -/
def ue (z : ℂ) (t : ℝ) : ℝ := cos (z.re * t) * cosh (z.im * t)

/-- Even-sector weight `sin(xt) sinh(yt)`. -/
def ve (z : ℂ) (t : ℝ) : ℝ := sin (z.re * t) * sinh (z.im * t)

/-- Odd-sector weight `sin(xt) cosh(yt)`. -/
def uo (z : ℂ) (t : ℝ) : ℝ := sin (z.re * t) * cosh (z.im * t)

/-- Odd-sector weight `cos(xt) sinh(yt)`. -/
def vo (z : ℂ) (t : ℝ) : ℝ := cos (z.re * t) * sinh (z.im * t)

/-- The sector weights are continuous. -/
@[fun_prop] theorem continuous_ue (z : ℂ) : Continuous (ue z) := by unfold ue; fun_prop
@[fun_prop] theorem continuous_ve (z : ℂ) : Continuous (ve z) := by unfold ve; fun_prop
@[fun_prop] theorem continuous_uo (z : ℂ) : Continuous (uo z) := by unfold uo; fun_prop
@[fun_prop] theorem continuous_vo (z : ℂ) : Continuous (vo z) := by unfold vo; fun_prop

/-- A real interval-integrable function stays integrable after the cast to `ℂ`. -/
theorem intervalIntegrable_ofReal {f : ℝ → ℝ} {a b : ℝ} (h : IntervalIntegrable f volume a b) :
    IntervalIntegrable (fun t => ((f t : ℝ) : ℂ)) volume a b :=
  ⟨Integrable.ofReal h.1, Integrable.ofReal h.2⟩

/-- **The centred transform in real coordinates**: with `z = x + iy`,
`ctr g z = ∫ g (ue + vo) − i ∫ g (uo + ve)`. -/
theorem ctr_eq (L : ℝ) {g : ℝ → ℝ} (hg : IntervalIntegrable g volume (-(L / 2)) (L / 2)) (z : ℂ) :
    ctr L g z = ((∫ t in -(L / 2)..L / 2, g t * (ue z t + vo z t) : ℝ) : ℂ)
      - Complex.I * ((∫ t in -(L / 2)..L / 2, g t * (uo z t + ve z t) : ℝ) : ℂ) := by
  have hpt : ∀ t : ℝ, Complex.exp (-((t : ℂ) * z) * Complex.I) * ((g t : ℝ) : ℂ)
      = ((g t * (ue z t + vo z t) : ℝ) : ℂ) - Complex.I * ((g t * (uo z t + ve z t) : ℝ) : ℂ) := by
    intro t
    have harg : -((t : ℂ) * z) * Complex.I
        = ((z.im * t : ℝ) : ℂ) + ((-(z.re * t) : ℝ) : ℂ) * Complex.I := by
      conv_lhs => rw [← Complex.re_add_im z]
      push_cast; ring_nf; rw [Complex.I_sq]; ring
    rw [harg, Complex.exp_add, ← Complex.ofReal_exp, Complex.exp_mul_I, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin, ← Real.cosh_add_sinh]
    unfold ue ve uo vo
    rw [Real.cos_neg, Real.sin_neg]
    push_cast; ring
  unfold ctr
  simp_rw [hpt]
  have i1 : IntervalIntegrable (fun t => ((g t * (ue z t + vo z t) : ℝ) : ℂ)) volume
      (-(L / 2)) (L / 2) :=
    intervalIntegrable_ofReal
      (hg.mul_continuousOn (by fun_prop : Continuous fun t => ue z t + vo z t).continuousOn)
  have i2 : IntervalIntegrable (fun t => Complex.I * ((g t * (uo z t + ve z t) : ℝ) : ℂ)) volume
      (-(L / 2)) (L / 2) :=
    (intervalIntegrable_ofReal
      (hg.mul_continuousOn (by fun_prop : Continuous fun t => uo z t + ve z t).continuousOn)).const_mul
      Complex.I
  rw [intervalIntegral.integral_sub i1 i2, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal]

/-- `ue z` is even in `t`. -/
theorem ue_neg (z : ℂ) (t : ℝ) : ue z (-t) = ue z t := by
  unfold ue; rw [mul_neg, mul_neg, Real.cos_neg, Real.cosh_neg]

/-- `ve z` is even in `t`. -/
theorem ve_neg (z : ℂ) (t : ℝ) : ve z (-t) = ve z t := by
  unfold ve; rw [mul_neg, mul_neg, Real.sin_neg, Real.sinh_neg]; ring

/-- `uo z` is odd in `t`. -/
theorem uo_neg (z : ℂ) (t : ℝ) : uo z (-t) = -uo z t := by
  unfold uo; rw [mul_neg, mul_neg, Real.sin_neg, Real.cosh_neg]; ring

/-- `vo z` is odd in `t`. -/
theorem vo_neg (z : ℂ) (t : ℝ) : vo z (-t) = -vo z t := by
  unfold vo; rw [mul_neg, mul_neg, Real.cos_neg, Real.sinh_neg]; ring

/-- `ve z` vanishes identically when `Re z = 0` or `Im z = 0`. -/
theorem ve_eq_zero {z : ℂ} (hz : z.re = 0 ∨ z.im = 0) (t : ℝ) : ve z t = 0 := by
  unfold ve
  rcases hz with h | h <;> simp [h]

/-- `vo z` vanishes identically when `Im z = 0`. -/
theorem vo_eq_zero {z : ℂ} (hz : z.im = 0) (t : ℝ) : vo z t = 0 := by
  unfold vo; simp [hz]

/-- `uo z` vanishes identically when `Re z = 0`. -/
theorem uo_eq_zero {z : ℂ} (hz : z.re = 0) (t : ℝ) : uo z t = 0 := by
  unfold uo; simp [hz]

/-- The weights at `−z`: `ue`, `ve` are unchanged and `uo`, `vo` change sign. -/
theorem weights_neg (z : ℂ) (t : ℝ) :
    ue (-z) t = ue z t ∧ ve (-z) t = ve z t ∧ uo (-z) t = -uo z t ∧ vo (-z) t = -vo z t := by
  unfold ue ve uo vo
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [Complex.neg_re, Complex.neg_im, neg_mul, Real.cos_neg, Real.cosh_neg, Real.sin_neg,
      Real.sinh_neg, mul_neg, neg_neg]

/-- The weights at `z̄`: `ue`, `uo` are unchanged and `ve`, `vo` change sign. -/
theorem weights_conj (z : ℂ) (t : ℝ) :
    ue (starRingEnd ℂ z) t = ue z t ∧ ve (starRingEnd ℂ z) t = -ve z t ∧
      uo (starRingEnd ℂ z) t = uo z t ∧ vo (starRingEnd ℂ z) t = -vo z t := by
  unfold ue ve uo vo
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [Complex.conj_re, Complex.conj_im, neg_mul, Real.cosh_neg, Real.sinh_neg, mul_neg]

/-- The integral of `g·(w₁ + w₂)` is that of `g·w₁` when `g·w₂` is odd. -/
theorem integral_add_odd (L : ℝ) {g w₁ w₂ : ℝ → ℝ}
    (hg : IntervalIntegrable g volume (-(L / 2)) (L / 2)) (h₁ : Continuous w₁) (h₂ : Continuous w₂)
    (hodd : ∀ t, g (-t) * w₂ (-t) = -(g t * w₂ t)) :
    ∫ t in -(L / 2)..L / 2, g t * (w₁ t + w₂ t) = ∫ t in -(L / 2)..L / 2, g t * w₁ t := by
  simp_rw [mul_add]
  rw [intervalIntegral.integral_add (hg.mul_continuousOn h₁.continuousOn)
    (hg.mul_continuousOn h₂.continuousOn),
    Cvs.Detection.integral_odd_eq_zero (f := fun t => g t * w₂ t) hodd (L / 2), add_zero]

/-- The integral of `g·(w₂ + w₁)` is that of `g·w₁` when `g·w₂` is odd. -/
theorem integral_odd_add (L : ℝ) {g w₁ w₂ : ℝ → ℝ}
    (hg : IntervalIntegrable g volume (-(L / 2)) (L / 2)) (h₁ : Continuous w₁) (h₂ : Continuous w₂)
    (hodd : ∀ t, g (-t) * w₂ (-t) = -(g t * w₂ t)) :
    ∫ t in -(L / 2)..L / 2, g t * (w₂ t + w₁ t) = ∫ t in -(L / 2)..L / 2, g t * w₁ t := by
  simp_rw [add_comm (w₂ _)]
  exact integral_add_odd L hg h₁ h₂ hodd

/-- **Even profile**: `ctr g z = ∫ g ue − i ∫ g ve` and `ctr g (−z) = ctr g z`. -/
theorem ctr_of_even (L : ℝ) {g : ℝ → ℝ} (hg : IntervalIntegrable g volume (-(L / 2)) (L / 2))
    (heven : ∀ t, g (-t) = g t) (z : ℂ) :
    ctr L g z = ((∫ t in -(L / 2)..L / 2, g t * ue z t : ℝ) : ℂ)
        - Complex.I * ((∫ t in -(L / 2)..L / 2, g t * ve z t : ℝ) : ℂ) ∧
      ctr L g (-z) = ctr L g z := by
  have h1 : ∀ w : ℂ, ctr L g w = ((∫ t in -(L / 2)..L / 2, g t * ue w t : ℝ) : ℂ)
      - Complex.I * ((∫ t in -(L / 2)..L / 2, g t * ve w t : ℝ) : ℂ) := by
    intro w
    rw [ctr_eq L hg w, integral_add_odd L hg (continuous_ue w) (continuous_vo w)
      (fun t => by rw [heven, vo_neg]; ring),
      integral_odd_add L hg (continuous_ve w) (continuous_uo w)
      (fun t => by rw [heven, uo_neg]; ring)]
  refine ⟨h1 z, ?_⟩
  rw [h1, h1]
  have hu : ∀ t, ue (-z) t = ue z t := fun t => (weights_neg z t).1
  have hv : ∀ t, ve (-z) t = ve z t := fun t => (weights_neg z t).2.1
  simp_rw [hu, hv]

/-- **Odd profile**: `ctr g z = ∫ g vo − i ∫ g uo` and `ctr g (−z) = −ctr g z`. -/
theorem ctr_of_odd (L : ℝ) {g : ℝ → ℝ} (hg : IntervalIntegrable g volume (-(L / 2)) (L / 2))
    (hodd : ∀ t, g (-t) = -g t) (z : ℂ) :
    ctr L g z = ((∫ t in -(L / 2)..L / 2, g t * vo z t : ℝ) : ℂ)
        - Complex.I * ((∫ t in -(L / 2)..L / 2, g t * uo z t : ℝ) : ℂ) ∧
      ctr L g (-z) = -ctr L g z := by
  have h1 : ∀ w : ℂ, ctr L g w = ((∫ t in -(L / 2)..L / 2, g t * vo w t : ℝ) : ℂ)
      - Complex.I * ((∫ t in -(L / 2)..L / 2, g t * uo w t : ℝ) : ℂ) := by
    intro w
    rw [ctr_eq L hg w,
      integral_odd_add L hg (continuous_vo w) (continuous_ue w)
      (fun t => by rw [hodd, ue_neg]; ring),
      integral_add_odd L hg (continuous_uo w) (continuous_ve w)
      (fun t => by rw [hodd, ve_neg]; ring)]
  refine ⟨h1 z, ?_⟩
  rw [h1, h1]
  have hu : ∀ t, uo (-z) t = -uo z t := fun t => (weights_neg z t).2.2.1
  have hv : ∀ t, vo (-z) t = -vo z t := fun t => (weights_neg z t).2.2.2
  simp_rw [hu, hv, mul_neg, intervalIntegral.integral_neg]
  push_cast; ring

/-! ### One zero's term in each sector -/

/-- **Even sector**: for an even profile, `Re sqTransform(z) = (∫ g ue)² − (∫ g ve)²`. -/
theorem re_sqTransform_of_even (L : ℝ) {g : ℝ → ℝ}
    (hg : IntervalIntegrable g volume (-(L / 2)) (L / 2)) (heven : ∀ t, g (-t) = g t) (z : ℂ) :
    (Cvs.Detection.sqTransform L (cf fun s => g (s - L / 2)) z).re
      = (∫ t in -(L / 2)..L / 2, g t * ue z t) ^ 2 - (∫ t in -(L / 2)..L / 2, g t * ve z t) ^ 2 := by
  obtain ⟨h1, h2⟩ := ctr_of_even L hg heven z
  rw [sqTransform_eq_ctr, h2, h1]
  simp only [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_im, Complex.I_re, Complex.I_im]
  ring

/-- **Odd sector**: for an odd profile, `Re sqTransform(z) = (∫ g uo)² − (∫ g vo)²`. -/
theorem re_sqTransform_of_odd (L : ℝ) {g : ℝ → ℝ}
    (hg : IntervalIntegrable g volume (-(L / 2)) (L / 2)) (hodd : ∀ t, g (-t) = -g t) (z : ℂ) :
    (Cvs.Detection.sqTransform L (cf fun s => g (s - L / 2)) z).re
      = (∫ t in -(L / 2)..L / 2, g t * uo z t) ^ 2 - (∫ t in -(L / 2)..L / 2, g t * vo z t) ^ 2 := by
  obtain ⟨h1, h2⟩ := ctr_of_odd L hg hodd z
  rw [sqTransform_eq_ctr, h2, h1]
  simp only [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_im, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im]
  ring

/-! ### The window form's zero terms -/

variable {ι : Type*} [Fintype ι]

/-- The cosine polynomial centred at `L/2` is even. -/
theorem cosPoly_centred_neg {L : ℝ} (hL : L ≠ 0) (mode : ι → ℤ) (xi : ι → ℝ) (t : ℝ) :
    Cvs.Finite.EvenSectorZeroSide.cosPoly L mode xi (-t + L / 2)
      = Cvs.Finite.EvenSectorZeroSide.cosPoly L mode xi (t + L / 2) := by
  unfold Cvs.Finite.EvenSectorZeroSide.cosPoly Cvs.Finite.TruncationZeroFreeOffAxes.omega
  refine Finset.sum_congr rfl fun k _ => ?_
  have hA : Real.sin (2 * π * (mode k) / L * (L / 2)) = 0 := by
    rw [show 2 * π * (mode k : ℝ) / L * (L / 2) = (mode k : ℝ) * π by field_simp]
    exact Real.sin_int_mul_pi _
  rw [show 2 * π * (mode k : ℝ) / L * (-t + L / 2)
      = 2 * π * (mode k) / L * (L / 2) - 2 * π * (mode k) / L * t by ring,
    show 2 * π * (mode k : ℝ) / L * (t + L / 2)
      = 2 * π * (mode k) / L * (L / 2) + 2 * π * (mode k) / L * t by ring,
    Real.cos_sub, Real.cos_add, hA]
  ring

/-- The sine polynomial centred at `L/2` is odd. -/
theorem sinePoly_centred_neg {L : ℝ} (hL : L ≠ 0) (mode : ι → ℤ) (o : ι → ℝ) (t : ℝ) :
    Cvs.Finite.OddSectorZeroSide.sinePoly L mode o (-t + L / 2)
      = -Cvs.Finite.OddSectorZeroSide.sinePoly L mode o (t + L / 2) := by
  unfold Cvs.Finite.OddSectorZeroSide.sinePoly Cvs.Finite.TruncationZeroFreeOffAxes.omega
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hA : Real.sin (2 * π * (mode k) / L * (L / 2)) = 0 := by
    rw [show 2 * π * (mode k : ℝ) / L * (L / 2) = (mode k : ℝ) * π by field_simp]
    exact Real.sin_int_mul_pi _
  rw [show 2 * π * (mode k : ℝ) / L * (-t + L / 2)
      = 2 * π * (mode k) / L * (L / 2) - 2 * π * (mode k) / L * t by ring,
    show 2 * π * (mode k : ℝ) / L * (t + L / 2)
      = 2 * π * (mode k) / L * (L / 2) + 2 * π * (mode k) / L * t by ring,
    Real.sin_sub, Real.sin_add, hA]
  ring

/-- A zero on the critical line has `Im z_ρ = 0`. -/
theorem zPoint_im_eq_zero {rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet} (h : (rho : ℂ).re = 1 / 2) :
    (Cvs.ZeroCounting.zPoint rho).im = 0 := by
  rw [Cvs.ZeroCounting.zPoint_im, h, sub_self, neg_zero]

/-- **The even-sector window form as squared pairings**: for even `xi` and every `L > 0`,
`L · xiᵀ M_L xi = ∑_ρ m_ρ ((∫ g ue_ρ)² − (∫ g ve_ρ)²)`, `g` the cosine polynomial centred at `L/2`. -/
theorem quadForm_even_eq_pairings [DecidableEq ι] {L : ℝ} (hL : 0 < L) {mode : ι → ℤ}
    (hinj : Function.Injective mode) {neg : ι → ι} (hinv : Function.Involutive neg)
    (hmode : ∀ i, mode (neg i) = -mode i) {xi : ι → ℝ} (hxieven : ∀ i, xi (neg i) = xi i) :
    L * (xi ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊ L mode *ᵥ xi))
      = ∑' rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet,
          (Cvs.Criterion.divisorWeight rho : ℝ)
            * ((∫ t in -(L / 2)..L / 2, Cvs.Finite.EvenSectorZeroSide.cosPoly L mode xi (t + L / 2)
                  * ue (Cvs.ZeroCounting.zPoint rho) t) ^ 2
              - (∫ t in -(L / 2)..L / 2, Cvs.Finite.EvenSectorZeroSide.cosPoly L mode xi (t + L / 2)
                  * ve (Cvs.ZeroCounting.zPoint rho) t) ^ 2) := by
  have h := Cvs.Finite.ZeroSideGramMatrix.zeroSide_eq_ddMatrix hL hinj hinv hmode hxieven 0 0
  unfold Cvs.ZeroCounting.kernelZeroSide at h
  rw [Cvs.Finite.TruncationQuadraticForm.M, ← h]
  refine tsum_congr fun rho => ?_
  have hcont : Continuous fun t => Cvs.Finite.EvenSectorZeroSide.cosPoly L mode xi (t + L / 2) := by
    unfold Cvs.Finite.EvenSectorZeroSide.cosPoly; fun_prop
  have e := re_sqTransform_of_even L
    (g := fun t => Cvs.Finite.EvenSectorZeroSide.cosPoly L mode xi (t + L / 2))
    (hcont.intervalIntegrable _ _) (cosPoly_centred_neg hL.ne' mode xi) (Cvs.ZeroCounting.zPoint rho)
  have hfun : (fun s => Cvs.Finite.EvenSectorZeroSide.cosPoly L mode xi (s - L / 2 + L / 2))
      = Cvs.Finite.EvenSectorZeroSide.cosPoly L mode xi := by
    funext s; rw [sub_add_cancel]
  simp only [hfun] at e
  rw [e]

/-- **The odd-sector window form as squared pairings**: for odd `o` and every `L > 0`,
`L · oᵀ M_L o = ∑_ρ m_ρ ((∫ g uo_ρ)² − (∫ g vo_ρ)²)`, `g` the sine polynomial centred at `L/2`. -/
theorem quadForm_odd_eq_pairings [DecidableEq ι] {L : ℝ} (hL : 0 < L) {mode : ι → ℤ}
    (hinj : Function.Injective mode) {neg : ι → ι} (hinv : Function.Involutive neg)
    (hmode : ∀ i, mode (neg i) = -mode i) {o : ι → ℝ} (hodd : ∀ i, o (neg i) = -o i) :
    L * (o ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊ L mode *ᵥ o))
      = ∑' rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet,
          (Cvs.Criterion.divisorWeight rho : ℝ)
            * ((∫ t in -(L / 2)..L / 2, Cvs.Finite.OddSectorZeroSide.sinePoly L mode o (t + L / 2)
                  * uo (Cvs.ZeroCounting.zPoint rho) t) ^ 2
              - (∫ t in -(L / 2)..L / 2, Cvs.Finite.OddSectorZeroSide.sinePoly L mode o (t + L / 2)
                  * vo (Cvs.ZeroCounting.zPoint rho) t) ^ 2) := by
  rw [Cvs.Finite.ParitySectorDefect.quadForm_odd_eq_zeroSide hL hinj hinv hmode hodd]
  refine tsum_congr fun rho => ?_
  have hcont : Continuous fun t => Cvs.Finite.OddSectorZeroSide.sinePoly L mode o (t + L / 2) := by
    unfold Cvs.Finite.OddSectorZeroSide.sinePoly; fun_prop
  have e := re_sqTransform_of_odd L
    (g := fun t => Cvs.Finite.OddSectorZeroSide.sinePoly L mode o (t + L / 2))
    (hcont.intervalIntegrable _ _) (sinePoly_centred_neg hL.ne' mode o) (Cvs.ZeroCounting.zPoint rho)
  have hfun : (fun s => Cvs.Finite.OddSectorZeroSide.sinePoly L mode o (s - L / 2 + L / 2))
      = Cvs.Finite.OddSectorZeroSide.sinePoly L mode o := by
    funext s; rw [sub_add_cancel]
  simp only [hfun] at e
  rw [e]

/-! ### At most one negative direction per sector -/

end Cvs.StepA.OneZeroParitySectors
