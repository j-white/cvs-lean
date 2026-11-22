import Mathlib
import Cvs.StepA.OneZeroParitySectors

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The sector Gram data of one zero are values of the box transform
With `x = Re z`, `y = Im z`: `ue² ± ve²`, `uo² ± vo²` and `ue ve = uo vo` are `cosh 2yt`, `cos 2xt`,
`cos 2xt cosh 2yt` and `sin 2xt sinh 2yt` up to constants, and their window integrals are read off
`z · box(2z) = sin(zL)`: `∫ cos 2xt = L sinc(xL)`, `y ∫ cosh 2yt = sinh(yL)`, and `|z|² ∫ cos 2xt cosh 2yt`,
`|z|² ∫ sin 2xt sinh 2yt` in closed form.
-/

noncomputable section

open Real MeasureTheory

namespace Cvs.StepA.SectorGramBoxTransform
open Cvs.ZeroCounting

open Cvs.StepA.OneZeroParitySectors (ctr ue ve uo vo)

/-! ### Pointwise identities -/

/-- `ue² + ve² = (cosh 2yt + cos 2xt)/2`. -/
theorem ue_sq_add_ve_sq (z : ℂ) (t : ℝ) :
    ue z t ^ 2 + ve z t ^ 2 = (cosh (2 * z.im * t) + cos (2 * z.re * t)) / 2 := by
  unfold ue ve
  rw [mul_assoc (2 : ℝ) z.im t, mul_assoc (2 : ℝ) z.re t, Real.cosh_two_mul, Real.cos_two_mul]
  linear_combination (cos (z.re * t) ^ 2 - 1 / 2) * Real.cosh_sq (z.im * t)
    + sinh (z.im * t) ^ 2 * Real.sin_sq_add_cos_sq (z.re * t)

/-- `uo² + vo² = (cosh 2yt − cos 2xt)/2`. -/
theorem uo_sq_add_vo_sq (z : ℂ) (t : ℝ) :
    uo z t ^ 2 + vo z t ^ 2 = (cosh (2 * z.im * t) - cos (2 * z.re * t)) / 2 := by
  unfold uo vo
  rw [mul_assoc (2 : ℝ) z.im t, mul_assoc (2 : ℝ) z.re t, Real.cosh_two_mul, Real.cos_two_mul]
  linear_combination (sin (z.re * t) ^ 2 - 1 / 2) * Real.cosh_sq (z.im * t)
    + (sinh (z.im * t) ^ 2 + 1) * Real.sin_sq_add_cos_sq (z.re * t)

/-- `ue² − ve² = (1 + cos 2xt · cosh 2yt)/2`. -/
theorem ue_sq_sub_ve_sq (z : ℂ) (t : ℝ) :
    ue z t ^ 2 - ve z t ^ 2 = (1 + cos (2 * z.re * t) * cosh (2 * z.im * t)) / 2 := by
  unfold ue ve
  rw [mul_assoc (2 : ℝ) z.im t, mul_assoc (2 : ℝ) z.re t, Real.cosh_two_mul, Real.cos_two_mul]
  linear_combination (1 / 2 : ℝ) * Real.cosh_sq (z.im * t)
    - sinh (z.im * t) ^ 2 * Real.sin_sq_add_cos_sq (z.re * t)

/-! ### The box transform -/

/-- The transform of the box `1_{(−L/2, L/2)}`: `box L w = ∫_{−L/2}^{L/2} e^{−iwt} dt`. -/
def box (L : ℝ) (w : ℂ) : ℂ := ctr L (fun _ => 1) w

/-- **The box transform in closed form**: `w · box L w = 2 sin(wL/2)`. -/
theorem mul_box (L : ℝ) (w : ℂ) : w * box L w = 2 * Complex.sin (w * L / 2) := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp
  have hc : -w * Complex.I ≠ 0 := mul_ne_zero (neg_ne_zero.mpr hw) Complex.I_ne_zero
  have hint : box L w = ∫ t in -(L / 2)..L / 2, Complex.exp ((-w * Complex.I) * (t : ℂ)) := by
    unfold box ctr
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [Complex.ofReal_one, mul_one]
    congr 1; ring
  rw [hint, integral_exp_mul_complex hc, Complex.two_sin]
  field_simp
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring_nf

/-- **The box transform at `2z`, in real coordinates**:
`box L (2z) = ∫ cos 2xt cosh 2yt − i ∫ sin 2xt sinh 2yt`. -/
theorem box_two_mul (L : ℝ) (z : ℂ) :
    box L (2 * z) = ((∫ t in -(L / 2)..L / 2, cos (2 * z.re * t) * cosh (2 * z.im * t) : ℝ) : ℂ)
      - Complex.I * ((∫ t in -(L / 2)..L / 2, sin (2 * z.re * t) * sinh (2 * z.im * t) : ℝ) : ℂ) := by
  have h := (Cvs.StepA.OneZeroParitySectors.ctr_of_even L (g := fun _ => 1) intervalIntegrable_const
    (fun _ => rfl) (2 * z)).1
  unfold box
  rw [h]
  have hre : (2 * z).re = 2 * z.re := by simp
  have him : (2 * z).im = 2 * z.im := by simp
  simp only [ue, ve, hre, him, one_mul]

/-- **The `cos·cosh` and `sin·sinh` window integrals, exactly**: with `x = Re z`, `y = Im z`,
`x A + y B = sin xL cosh yL` and `y A − x B = cos xL sinh yL`, where `A = ∫ cos 2xt cosh 2yt` and
`B = ∫ sin 2xt sinh 2yt`. -/
theorem integral_cos_cosh_sin_sinh (L : ℝ) (z : ℂ) :
    z.re * (∫ t in -(L / 2)..L / 2, cos (2 * z.re * t) * cosh (2 * z.im * t))
        + z.im * (∫ t in -(L / 2)..L / 2, sin (2 * z.re * t) * sinh (2 * z.im * t))
        = sin (z.re * L) * cosh (z.im * L) ∧
      z.im * (∫ t in -(L / 2)..L / 2, cos (2 * z.re * t) * cosh (2 * z.im * t))
        - z.re * (∫ t in -(L / 2)..L / 2, sin (2 * z.re * t) * sinh (2 * z.im * t))
        = cos (z.re * L) * sinh (z.im * L) := by
  have h := mul_box L (2 * z)
  rw [box_two_mul] at h
  have hsin : Complex.sin (2 * z * L / 2)
      = Complex.sin (((z.re * L : ℝ) : ℂ) + ((z.im * L : ℝ) : ℂ) * Complex.I) := by
    congr 1
    conv_lhs => rw [← Complex.re_add_im z]
    push_cast; ring
  rw [hsin, Complex.sin_add_mul_I, ← Complex.ofReal_sin, ← Complex.ofReal_cosh, ← Complex.ofReal_cos,
    ← Complex.ofReal_sinh] at h
  set A := ∫ t in -(L / 2)..L / 2, cos (2 * z.re * t) * cosh (2 * z.im * t)
  set B := ∫ t in -(L / 2)..L / 2, sin (2 * z.re * t) * sinh (2 * z.im * t)
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  conv_lhs at hre => rw [← Complex.re_add_im z]
  conv_lhs at him => rw [← Complex.re_add_im z]
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re,
    Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat] at hre him
  constructor
  · linarith
  · linarith

/-- `|z|² ∫ cos 2xt cosh 2yt = x sin xL cosh yL + y cos xL sinh yL`, which is `|z|² Re(sin(zL)/z)`. -/
theorem normSq_mul_integral_cos_cosh (L : ℝ) (z : ℂ) :
    (z.re ^ 2 + z.im ^ 2) * ∫ t in -(L / 2)..L / 2, cos (2 * z.re * t) * cosh (2 * z.im * t)
      = z.re * sin (z.re * L) * cosh (z.im * L) + z.im * cos (z.re * L) * sinh (z.im * L) := by
  obtain ⟨h1, h2⟩ := integral_cos_cosh_sin_sinh L z
  linear_combination z.re * h1 + z.im * h2

/-- `|z|² ∫ sin 2xt sinh 2yt = y sin xL cosh yL − x cos xL sinh yL`, which is `−|z|² Im(sin(zL)/z)`. -/
theorem normSq_mul_integral_sin_sinh (L : ℝ) (z : ℂ) :
    (z.re ^ 2 + z.im ^ 2) * ∫ t in -(L / 2)..L / 2, sin (2 * z.re * t) * sinh (2 * z.im * t)
      = z.im * sin (z.re * L) * cosh (z.im * L) - z.re * cos (z.re * L) * sinh (z.im * L) := by
  obtain ⟨h1, h2⟩ := integral_cos_cosh_sin_sinh L z
  linear_combination z.im * h1 - z.re * h2

/-- `∫_{−L/2}^{L/2} cos 2xt dt = L sinc(xL)`. -/
theorem integral_cos_two_mul (L x : ℝ) :
    ∫ t in -(L / 2)..L / 2, cos (2 * x * t) = L * Real.sinc (x * L) := by
  have h := (integral_cos_cosh_sin_sinh L (x : ℂ)).1
  simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, Real.cosh_zero, Real.sinh_zero,
    mul_one, add_zero] at h
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  rcases eq_or_ne L 0 with rfl | hL
  · simp
  have hI : ∫ t in -(L / 2)..L / 2, cos (2 * x * t) = sin (x * L) / x := by
    rw [eq_div_iff hx]; linarith
  rw [hI, Real.sinc_of_ne_zero (mul_ne_zero hx hL)]
  field_simp

/-- `y ∫_{−L/2}^{L/2} cosh 2yt dt = sinh(yL)`. -/
theorem mul_integral_cosh_two_mul (L y : ℝ) :
    y * ∫ t in -(L / 2)..L / 2, cosh (2 * y * t) = sinh (y * L) := by
  have h := (integral_cos_cosh_sin_sinh L ((y : ℂ) * Complex.I)).2
  simpa using h

/-! ### The sector Gram data -/

/-- The window integral is additive on continuous integrands. -/
private theorem integral_add_of_continuous (L : ℝ) {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    (∫ t in -(L / 2)..L / 2, f t) + ∫ t in -(L / 2)..L / 2, g t
      = ∫ t in -(L / 2)..L / 2, (f t + g t) :=
  (intervalIntegral.integral_add (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _)).symm

/-- The window integral is subtractive on continuous integrands. -/
private theorem integral_sub_of_continuous (L : ℝ) {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    (∫ t in -(L / 2)..L / 2, f t) - ∫ t in -(L / 2)..L / 2, g t
      = ∫ t in -(L / 2)..L / 2, (f t - g t) :=
  (intervalIntegral.integral_sub (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _)).symm

/-- **Even trace**: `∫ ue² + ∫ ve² = (∫ cosh 2yt + ∫ cos 2xt)/2`. -/
theorem gram_even_add (L : ℝ) (z : ℂ) :
    (∫ t in -(L / 2)..L / 2, ue z t ^ 2) + ∫ t in -(L / 2)..L / 2, ve z t ^ 2
      = ((∫ t in -(L / 2)..L / 2, cosh (2 * z.im * t))
          + ∫ t in -(L / 2)..L / 2, cos (2 * z.re * t)) / 2 := by
  rw [integral_add_of_continuous L (by fun_prop) (by fun_prop),
    integral_add_of_continuous L (by fun_prop) (by fun_prop), ← intervalIntegral.integral_div]
  exact intervalIntegral.integral_congr fun t _ => ue_sq_add_ve_sq z t

/-- **Odd trace**: `∫ uo² + ∫ vo² = (∫ cosh 2yt − ∫ cos 2xt)/2`. -/
theorem gram_odd_add (L : ℝ) (z : ℂ) :
    (∫ t in -(L / 2)..L / 2, uo z t ^ 2) + ∫ t in -(L / 2)..L / 2, vo z t ^ 2
      = ((∫ t in -(L / 2)..L / 2, cosh (2 * z.im * t))
          - ∫ t in -(L / 2)..L / 2, cos (2 * z.re * t)) / 2 := by
  rw [integral_add_of_continuous L (by fun_prop) (by fun_prop),
    integral_sub_of_continuous L (by fun_prop) (by fun_prop), ← intervalIntegral.integral_div]
  exact intervalIntegral.integral_congr fun t _ => uo_sq_add_vo_sq z t

/-- **Even difference**: `∫ ue² − ∫ ve² = (L + ∫ cos 2xt cosh 2yt)/2`. -/
theorem gram_even_sub (L : ℝ) (z : ℂ) :
    (∫ t in -(L / 2)..L / 2, ue z t ^ 2) - ∫ t in -(L / 2)..L / 2, ve z t ^ 2
      = (L + ∫ t in -(L / 2)..L / 2, cos (2 * z.re * t) * cosh (2 * z.im * t)) / 2 := by
  rw [integral_sub_of_continuous L (by fun_prop) (by fun_prop),
    intervalIntegral.integral_congr (g := fun t => (1 + cos (2 * z.re * t) * cosh (2 * z.im * t)) / 2)
      fun t _ => ue_sq_sub_ve_sq z t,
    intervalIntegral.integral_div, intervalIntegral.integral_add intervalIntegrable_const
      ((by fun_prop : Continuous fun t => cos (2 * z.re * t) * cosh (2 * z.im * t)).intervalIntegrable
        _ _)]
  simp

end Cvs.StepA.SectorGramBoxTransform
