import Mathlib
import Cvs.Prolate.Hardy.CarrierBoundaryValues
import Cvs.Prolate.Hardy.CarrierUpperHalfPlane
import Cvs.Prolate.Hardy.HardyExtensionOperator
import Cvs.Upstream.ConfocalEllipseDeformation
import Cvs.Upstream.JordanArcIntegral

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The negative frequencies of the positive carrier on `[−3/5, 3/5]`

For `H = A e^{icx}/w` and `k = 1_{(−3/5, 3/5]}H` with `A` holomorphic on `|z| ≤ 3/5` and `|A| ≤ M` on the ellipse
`(3/5)cos θ + i(√11/10)sin θ`, every `ξ ≤ 0` has `|𝓕k(ξ)| ≤ (3/5)Mπ/(c(√11/10 − 3/10) − 2πξ√11/10)`.
-/

noncomputable section

open Real Set MeasureTheory intervalIntegral FourierTransform
open Complex (I)
open scoped Interval

namespace Cvs.Prolate.Hardy.CarrierNegativeFrequencies
open Cvs.ZeroCounting

open Cvs.Prolate.Hardy.HardyExtensionOperator (wR)
open Cvs.Prolate.Hardy.CarrierBoundaryValues (sR)

/-- `η₀ = arsinh(√11/5)`, so `cosh η₀ = 6/5` and the ellipse `cosh(η₀ + iθ)/2` has semiaxes `3/5`, `√11/10`. -/
def eta0 : ℝ := Real.arsinh (√11 / 5)

theorem sinh_eta0 : Real.sinh eta0 = √11 / 5 := Real.sinh_arsinh _

theorem cosh_eta0 : Real.cosh eta0 = 6 / 5 := by
  rw [eta0, Real.cosh_arsinh, div_pow, Real.sq_sqrt (by norm_num)]
  rw [show (1 : ℝ) + 11 / 5 ^ 2 = (6 / 5) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

theorem eta0_nonneg : 0 ≤ eta0 := Real.arsinh_nonneg_iff.2 (by positivity)

/-- The positive carrier `H(x) = A(x)e^{icx}/w(x)` on `ℝ`, `w = e^{i(c/2)S}`. -/
def carH (c : ℝ) (A : ℂ → ℂ) (x : ℝ) : ℂ := A x * Complex.exp (I * c * x) * (wR (c / 2) x)⁻¹

/-- `k = 1_{(−3/5, 3/5]} H`. -/
def kC (c : ℝ) (A : ℂ → ℂ) : ℝ → ℂ := (Ioc (-(3 / 5)) (3 / 5)).indicator (carH c A)

/-- The holomorphic integrand on the rectangle, `z = cosh ζ/2`, `S = sinh ζ/2`. -/
def Qrect (c ξ : ℝ) (A : ℂ → ℂ) (ζ : ℂ) : ℂ :=
  Complex.exp (((-2 * π * ξ : ℝ) : ℂ) * ((1 / 2 : ℂ) * Complex.cosh ζ) * I) *
    (A ((1 / 2 : ℂ) * Complex.cosh ζ) * Complex.exp (I * c * ((1 / 2 : ℂ) * Complex.cosh ζ)) *
      Complex.exp (-(I * ((c / 2 : ℝ) : ℂ) * ((1 / 2 : ℂ) * Complex.sinh ζ))))

/-- The Fourier integrand `e^{−2πixξ}H(x)`. -/
def qF (c ξ : ℝ) (A : ℂ → ℂ) (x : ℝ) : ℂ := Complex.exp (↑(-2 * π * x * ξ) * I) • carH c A x

theorem sqrt_cosh_sq {η : ℝ} (hη : 0 ≤ η) : √((1 / 2 * Real.cosh η) ^ 2 - 1 / 4) = 1 / 2 * Real.sinh η := by
  have h := Real.cosh_sq η
  rw [show (1 / 2 * Real.cosh η) ^ 2 - 1 / 4 = (1 / 2 * Real.sinh η) ^ 2 by nlinarith,
    Real.sqrt_sq (by have := Real.sinh_nonneg_iff.2 hη; positivity)]

theorem sqrt_cos_sq {y : ℝ} (hy : y ∈ Icc 0 π) : √(1 / 4 - (1 / 2 * Real.cos y) ^ 2) = 1 / 2 * Real.sin y := by
  have h := Real.sin_sq_add_cos_sq y
  rw [show 1 / 4 - (1 / 2 * Real.cos y) ^ 2 = (1 / 2 * Real.sin y) ^ 2 by nlinarith,
    Real.sqrt_sq (by have := Real.sin_nonneg_of_nonneg_of_le_pi hy.1 hy.2; positivity)]

theorem half_le_cosh (η : ℝ) : 1 / 2 ≤ |1 / 2 * Real.cosh η| := by
  rw [abs_of_pos (by positivity)]; linarith [Real.one_le_cosh η]

theorem h1 (c ξ : ℝ) (A : ℂ → ℂ) {η : ℝ} (hη : 0 ≤ η) :
    Qrect c ξ A η = qF c ξ A (1 / 2 * Real.cosh η) := by
  have hw := Cvs.Prolate.Hardy.CarrierBoundaryValues.wR_of_half_le_abs (c / 2) (half_le_cosh η)
  have hs : sR (1 / 2 * Real.cosh η) = 1 / 2 * Real.sinh η := by
    rw [Cvs.Prolate.Hardy.CarrierBoundaryValues.sR, if_pos (by positivity), sqrt_cosh_sq hη]
  unfold Qrect qF carH
  rw [hw, hs, ← Complex.exp_neg, Cvs.Upstream.ConfocalEllipseDeformation.cosh_ofReal, Cvs.Upstream.ConfocalEllipseDeformation.sinh_ofReal, smul_eq_mul]
  push_cast
  ring_nf

theorem h2 (c ξ : ℝ) (A : ℂ → ℂ) {η : ℝ} (hη : 0 ≤ η) :
    Qrect c ξ A (η + π * I) = qF c ξ A (-(1 / 2 * Real.cosh η)) := by
  have hw := Cvs.Prolate.Hardy.CarrierBoundaryValues.wR_of_half_le_abs (c / 2) (x := -(1 / 2 * Real.cosh η)) (by rw [abs_neg]; exact half_le_cosh η)
  have hs : sR (-(1 / 2 * Real.cosh η)) = -(1 / 2 * Real.sinh η) := by
    rw [Cvs.Prolate.Hardy.CarrierBoundaryValues.sR_neg, Cvs.Prolate.Hardy.CarrierBoundaryValues.sR, if_pos (by positivity), sqrt_cosh_sq hη]
  unfold Qrect qF carH
  rw [hw, hs, ← Complex.exp_neg, Complex.cosh_add_pi_mul_I, Complex.sinh_add_pi_mul_I, Cvs.Upstream.ConfocalEllipseDeformation.cosh_ofReal,
    Cvs.Upstream.ConfocalEllipseDeformation.sinh_ofReal, smul_eq_mul]
  push_cast
  ring_nf

theorem h3 (c ξ : ℝ) (A : ℂ → ℂ) {y : ℝ} (hy : y ∈ Icc 0 π) :
    Qrect c ξ A (y * I) = qF c ξ A (1 / 2 * Real.cos y) := by
  have hx : |1 / 2 * Real.cos y| ≤ 1 / 2 := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have := Real.abs_cos_le_one y
    linarith
  have hw := Cvs.Prolate.Hardy.CarrierBoundaryValues.wR_of_abs_le (c / 2) hx
  unfold Qrect qF carH
  rw [hw, sqrt_cos_sq hy, Complex.ofReal_exp, ← Complex.exp_neg, Complex.cosh_mul_I, Complex.sinh_mul_I,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin, smul_eq_mul]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring_nf

theorem norm_half_cosh_le {ζ : ℂ} (hζ : ζ ∈ [[(0 : ℝ), eta0]] ×ℂ [[(0 : ℝ), π]]) :
    ‖(1 / 2 : ℂ) * Complex.cosh ζ‖ ≤ 3 / 5 := by
  have hre : ζ.re ∈ [[(0 : ℝ), eta0]] := hζ.1
  rw [uIcc_of_le eta0_nonneg] at hre
  have e : ζ = (ζ.re : ℂ) + (ζ.im : ℂ) * I := (Complex.re_add_im ζ).symm
  have h := Cvs.Upstream.JordanArcIntegral.norm_cosh_arc_le (a := 1 / 2) (η₀ := ζ.re) (by norm_num) ζ.im
  rw [← e] at h
  have hc : Real.cosh ζ.re ≤ Real.cosh eta0 := by
    rw [Real.cosh_le_cosh, abs_of_nonneg hre.1, abs_of_nonneg eta0_nonneg]; exact hre.2
  rw [cosh_eta0] at hc
  push_cast at h
  linarith

theorem differentiableOn_Qrect (c ξ : ℝ) {A : ℂ → ℂ} (hA : ∀ z : ℂ, ‖z‖ ≤ 3 / 5 → DifferentiableAt ℂ A z) :
    DifferentiableOn ℂ (Qrect c ξ A) ([[(0 : ℝ), eta0]] ×ℂ [[(0 : ℝ), π]]) := by
  intro ζ hζ
  have hAc : DifferentiableAt ℂ (fun ζ => A ((1 / 2 : ℂ) * Complex.cosh ζ)) ζ :=
    (hA _ (norm_half_cosh_le hζ)).comp ζ (by fun_prop)
  refine DifferentiableAt.differentiableWithinAt ?_
  unfold Qrect
  refine DifferentiableAt.mul (by fun_prop) (DifferentiableAt.mul (DifferentiableAt.mul hAc (by fun_prop))
    (by fun_prop))

theorem continuousOn_qF (c ξ : ℝ) {A : ℂ → ℂ} (hA : ∀ z : ℂ, ‖z‖ ≤ 3 / 5 → DifferentiableAt ℂ A z) :
    ContinuousOn (qF c ξ A) (Icc (-(3 / 5)) (3 / 5)) := by
  have hAr : ContinuousOn (fun x : ℝ => A x) (Icc (-(3 / 5)) (3 / 5)) := by
    intro x hx
    have : ‖(x : ℂ)‖ ≤ 3 / 5 := by rw [Complex.norm_real, Real.norm_eq_abs, abs_le]; exact hx
    exact ((hA _ this).continuousAt.comp Complex.continuous_ofReal.continuousAt).continuousWithinAt
  have hw := Cvs.Prolate.Hardy.CarrierUpperHalfPlane.continuous_wR (c / 2)
  unfold qF carH
  have e1 : Continuous fun x : ℝ => Complex.exp (↑(-2 * π * x * ξ) * I) := by fun_prop
  have e2 : Continuous fun x : ℝ => Complex.exp (I * c * x) := by fun_prop
  refine ContinuousOn.smul e1.continuousOn (ContinuousOn.mul (hAr.mul e2.continuousOn) ?_)
  exact (hw.continuousOn).inv₀ fun x _ => Cvs.Prolate.Hardy.CarrierUpperHalfPlane.wR_ne_zero _ x

/-- `𝓕k(ξ) = ∫_{−3/5}^{3/5} e^{−2πixξ}H(x) dx`. -/
theorem fourier_kC (c ξ : ℝ) (A : ℂ → ℂ) : 𝓕 (kC c A) ξ = ∫ x in -(3 / 5 : ℝ)..(3 / 5), qF c ξ A x := by
  rw [Real.fourier_real_eq_integral_exp_smul, intervalIntegral.integral_of_le (by norm_num),
    ← MeasureTheory.integral_indicator measurableSet_Ioc]
  congr 1
  ext x
  unfold kC qF
  by_cases hx : x ∈ Ioc (-(3 / 5 : ℝ)) (3 / 5)
  · rw [indicator_of_mem hx, indicator_of_mem hx]
  · rw [indicator_of_notMem hx, indicator_of_notMem hx, smul_zero]

/-- **The contour form** `𝓕k(ξ) = −i∫_0^π Q(η₀ + iθ) sinh(η₀ + iθ)/2 dθ`. -/
theorem fourier_kC_eq_arc (c ξ : ℝ) {A : ℂ → ℂ} (hA : ∀ z : ℂ, ‖z‖ ≤ 3 / 5 → DifferentiableAt ℂ A z) :
    𝓕 (kC c A) ξ = -I * ∫ θ in (0 : ℝ)..π, Qrect c ξ A (eta0 + θ * I) *
      (((1 / 2 : ℝ) : ℂ) * Complex.sinh (eta0 + θ * I)) := by
  rw [fourier_kC]
  have hL : (1 / 2 : ℝ) * Real.cosh eta0 = 3 / 5 := by rw [cosh_eta0]; norm_num
  have hq : IntervalIntegrable (qF c ξ A) volume (-(1 / 2 * Real.cosh eta0)) (1 / 2 * Real.cosh eta0) := by
    rw [hL]
    exact (continuousOn_qF c ξ hA).intervalIntegrable_of_Icc (by norm_num)
  have := Cvs.Upstream.ConfocalEllipseDeformation.integral_eq_arc (a := 1 / 2) (by norm_num) eta0_nonneg (differentiableOn_Qrect c ξ hA) hq
    (fun η hη => by simpa using h1 c ξ A hη.1) (fun η hη => by simpa using h2 c ξ A hη.1)
    (fun y hy => by simpa using h3 c ξ A hy)
  rw [hL] at this
  exact this

/-- The damping rate `t = c(√11/10 − 3/10) − 2πξ√11/10` of the arc. -/
def tArc (c ξ : ℝ) : ℝ := c * (√11 / 10 - 3 / 10) - 2 * π * ξ * (√11 / 10)

theorem three_lt_sqrt_eleven : (3 : ℝ) < √11 := by
  rw [show (3 : ℝ) = √9 by rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)] ]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

theorem tArc_pos {c ξ : ℝ} (hc : 0 < c) (hξ : ξ ≤ 0) : 0 < tArc c ξ := by
  unfold tArc
  have h1 : 0 < √11 / 10 - 3 / 10 := by linarith [three_lt_sqrt_eleven]
  have h2 : 0 ≤ -(2 * π * ξ * (√11 / 10)) := by
    have : 2 * π * ξ * (√11 / 10) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by positivity) hξ) (by positivity)
    linarith
  nlinarith [mul_pos hc h1]

theorem norm_Qrect_arc (c ξ : ℝ) {A : ℂ → ℂ} {M : ℝ} (θ : ℝ)
    (hM : ‖A ((1 / 2 : ℂ) * Complex.cosh (eta0 + θ * I))‖ ≤ M) :
    ‖Qrect c ξ A (eta0 + θ * I)‖ ≤ M * Real.exp (-tArc c ξ * Real.sin θ) := by
  have hz : (1 / 2 : ℂ) * Complex.cosh (eta0 + θ * I) =
      ((3 / 5 * Real.cos θ : ℝ) : ℂ) + I * ((√11 / 10 * Real.sin θ : ℝ) : ℂ) := by
    have := Cvs.Upstream.JordanArcIntegral.cosh_arc (1 / 2) eta0 θ
    rw [cosh_eta0, sinh_eta0] at this
    push_cast at this ⊢
    linear_combination this
  have hS : (1 / 2 : ℂ) * Complex.sinh (eta0 + θ * I) =
      ((√11 / 10 * Real.cos θ : ℝ) : ℂ) + I * ((3 / 5 * Real.sin θ : ℝ) : ℂ) := by
    have := Cvs.Upstream.JordanArcIntegral.sinh_arc (1 / 2) eta0 θ
    rw [cosh_eta0, sinh_eta0] at this
    push_cast at this ⊢
    linear_combination this
  have hre : (((-2 * π * ξ : ℝ) : ℂ) * ((1 / 2 : ℂ) * Complex.cosh (eta0 + θ * I)) * I).re +
      (I * c * ((1 / 2 : ℂ) * Complex.cosh (eta0 + θ * I))).re +
      (-(I * ((c / 2 : ℝ) : ℂ) * ((1 / 2 : ℂ) * Complex.sinh (eta0 + θ * I)))).re = -tArc c ξ * Real.sin θ := by
    rw [hz, hS]
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.neg_re]
    unfold tArc
    ring
  unfold Qrect
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_exp, Complex.norm_exp, Complex.norm_exp]
  calc _ = ‖A ((1 / 2 : ℂ) * Complex.cosh (eta0 + θ * I))‖ *
        Real.exp ((((-2 * π * ξ : ℝ) : ℂ) * ((1 / 2 : ℂ) * Complex.cosh (eta0 + θ * I)) * I).re +
        (I * c * ((1 / 2 : ℂ) * Complex.cosh (eta0 + θ * I))).re +
        (-(I * ((c / 2 : ℝ) : ℂ) * ((1 / 2 : ℂ) * Complex.sinh (eta0 + θ * I)))).re) := by
          rw [Real.exp_add, Real.exp_add]; ring
    _ ≤ M * Real.exp (-tArc c ξ * Real.sin θ) := by
          rw [hre]; exact mul_le_mul_of_nonneg_right hM (Real.exp_pos _).le

/-- **The negative-frequency bound** `|𝓕k(ξ)| ≤ (3/5)Mπ/t` for `ξ ≤ 0`. -/
theorem norm_fourier_kC_le {c ξ M : ℝ} (hc : 0 < c) (hξ : ξ ≤ 0) {A : ℂ → ℂ}
    (hA : ∀ z : ℂ, ‖z‖ ≤ 3 / 5 → DifferentiableAt ℂ A z)
    (hM : ∀ θ ∈ Icc 0 π, ‖A ((1 / 2 : ℂ) * Complex.cosh (eta0 + θ * I))‖ ≤ M) :
    ‖𝓕 (kC c A) ξ‖ ≤ M * (3 / 5) * (π / tArc c ξ) := by
  rw [fourier_kC_eq_arc c ξ hA, norm_mul, norm_neg, Complex.norm_I, one_mul]
  have := Cvs.Upstream.JordanArcIntegral.norm_arc_le (a := 1 / 2) (η₀ := eta0) (M := M) (by norm_num) (tArc_pos hc hξ)
    (Q := Qrect c ξ A) (fun θ hθ => norm_Qrect_arc c ξ θ (by simpa using hM θ hθ))
  rw [cosh_eta0] at this
  convert this using 2
  norm_num

end Cvs.Prolate.Hardy.CarrierNegativeFrequencies

end
