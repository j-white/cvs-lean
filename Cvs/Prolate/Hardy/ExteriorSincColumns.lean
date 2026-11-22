import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The exterior sinc columns and the geometry of the highpass carrier

The even part of `sin(c(x − u))/(π(x − u))` is `Re[A_u(x)e^{icx}]` with `A_u(z) = (u sin cu + iz cos cu)/(π(u² − z²))`,
and `|A_u| ≤ 1/(π(u − L))` on `|z| ≤ L < u`; `S² = z² − a²` with `Im S ≥ 0` forces `Im S ≥ Im z`; on the
confocal ellipse `Im(z − rS) = (B − rL) sin θ`; on the lips the phase `x − rS(x)` turns at `x² = a²/(1 − r²)`.
-/

noncomputable section

open Real
open Complex (I)

namespace Cvs.Prolate.Hardy.ExteriorSincColumns

/-! ### The exterior sinc columns -/

/-- **The even sinc column** `e_u(x) = (u sin(cu) cos(cx) − x cos(cu) sin(cx))/(π(u² − x²))`. -/
theorem even_sinc {c u x : ℝ} (h1 : x - u ≠ 0) (h2 : -x - u ≠ 0) :
    (sin (c * (x - u)) / (π * (x - u)) + sin (c * (-x - u)) / (π * (-x - u))) / 2 =
      (u * sin (c * u) * cos (c * x) - x * cos (c * u) * sin (c * x)) / (π * (u ^ 2 - x ^ 2)) := by
  have h3 : u ^ 2 - x ^ 2 ≠ 0 := by
    have : u ^ 2 - x ^ 2 = (x - u) * (-x - u) := by ring
    rw [this]; exact mul_ne_zero h1 h2
  have hπ := Real.pi_pos.ne'
  rw [show c * (x - u) = c * x - c * u by ring, show c * (-x - u) = -(c * x + c * u) by ring, Real.sin_neg,
    Real.sin_sub, Real.sin_add]
  field_simp
  ring

/-- The analytic amplitude `A_u(z) = (u sin(cu) + iz cos(cu))/(π(u² − z²))` of the column `e_u`. -/
def amp (c u : ℝ) (z : ℂ) : ℂ := (u * Real.sin (c * u) + I * z * Real.cos (c * u)) / (π * (u ^ 2 - z ^ 2))

/-- `e_u(x) = Re[A_u(x)e^{icx}]` on the real line. -/
theorem re_amp_mul_exp {c u x : ℝ} :
    (amp c u x * Complex.exp (I * (c * x))).re =
      (u * Real.sin (c * u) * Real.cos (c * x) - x * Real.cos (c * u) * Real.sin (c * x)) / (π * (u ^ 2 - x ^ 2)) := by
  have e : amp c u x = ((u * Real.sin (c * u) / (π * (u ^ 2 - x ^ 2)) : ℝ) : ℂ) +
      ((x * Real.cos (c * u) / (π * (u ^ 2 - x ^ 2)) : ℝ) : ℂ) * I := by
    unfold amp
    push_cast
    ring
  rw [e, show I * ((c : ℂ) * x) = ((c * x : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_mul_I]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Complex.add_im, Complex.mul_im]
  ring

/-- **Partial fractions**: `A_u(z) = ((sin cu + i cos cu)/(u − z) + (sin cu − i cos cu)/(u + z))/(2π)`. -/
theorem amp_eq {c u : ℝ} {z : ℂ} (h1 : (u : ℂ) - z ≠ 0) (h2 : (u : ℂ) + z ≠ 0) :
    amp c u z = ((Real.sin (c * u) + I * Real.cos (c * u)) / (u - z) +
      (Real.sin (c * u) - I * Real.cos (c * u)) / (u + z)) / (2 * π) := by
  have h3 : (π : ℂ) * ((u : ℂ) ^ 2 - z ^ 2) ≠ 0 := by
    refine mul_ne_zero (by exact_mod_cast Real.pi_pos.ne') ?_
    rw [show (u : ℂ) ^ 2 - z ^ 2 = (u - z) * (u + z) by ring]; exact mul_ne_zero h1 h2
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  have h4 : (u : ℂ) ^ 2 - z ^ 2 ≠ 0 := by
    rw [show (u : ℂ) ^ 2 - z ^ 2 = (u - z) * (u + z) by ring]; exact mul_ne_zero h1 h2
  unfold amp
  rw [div_add_div _ _ h1 h2, div_div, div_eq_div_iff h3 (mul_ne_zero (mul_ne_zero h1 h2) (by simp))]
  ring

theorem norm_sin_add_I_mul_cos (t : ℝ) : ‖(Real.sin t : ℂ) + I * Real.cos t‖ = 1 := by
  rw [show (Real.sin t : ℂ) + I * Real.cos t = (Real.sin t : ℂ) + (Real.cos t : ℂ) * I by ring,
    Complex.norm_add_mul_I, Real.sin_sq_add_cos_sq, Real.sqrt_one]

theorem norm_sin_sub_I_mul_cos (t : ℝ) : ‖(Real.sin t : ℂ) - I * Real.cos t‖ = 1 := by
  rw [show (Real.sin t : ℂ) - I * Real.cos t = (Real.sin t : ℂ) + ((-Real.cos t : ℝ) : ℂ) * I by push_cast; ring,
    Complex.norm_add_mul_I, neg_sq, Real.sin_sq_add_cos_sq, Real.sqrt_one]

/-- **The amplitude bound** `|A_u(z)| ≤ 1/(π(u − L))` on `|z| ≤ L < u`. -/
theorem norm_amp_le {c u L : ℝ} {z : ℂ} (hz : ‖z‖ ≤ L) (hL : L < u) : ‖amp c u z‖ ≤ 1 / (π * (u - L)) := by
  have hd1 : u - L ≤ ‖(u : ℂ) - z‖ := by
    have := norm_sub_norm_le (u : ℂ) z
    rw [Complex.norm_real, Real.norm_eq_abs] at this
    have hu : 0 ≤ u := by linarith [norm_nonneg z]
    rw [abs_of_nonneg hu] at this; linarith
  have hd2 : u - L ≤ ‖(u : ℂ) + z‖ := by
    have := norm_sub_norm_le (u : ℂ) (-z)
    rw [Complex.norm_real, Real.norm_eq_abs, norm_neg, sub_neg_eq_add] at this
    have hu : 0 ≤ u := by linarith [norm_nonneg z]
    rw [abs_of_nonneg hu] at this; linarith
  have hp : 0 < u - L := by linarith
  have h1 : (u : ℂ) - z ≠ 0 := fun h => by rw [h, norm_zero] at hd1; linarith
  have h2 : (u : ℂ) + z ≠ 0 := fun h => by rw [h, norm_zero] at hd2; linarith
  rw [amp_eq h1 h2, norm_div, show ‖(2 : ℂ) * π‖ = 2 * π by
    rw [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]]
  have hπ := Real.pi_pos
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have ht := norm_add_le ((Real.sin (c * u) + I * Real.cos (c * u)) / (u - z))
    ((Real.sin (c * u) - I * Real.cos (c * u)) / (u + z))
  rw [norm_div, norm_div, norm_sin_add_I_mul_cos, norm_sin_sub_I_mul_cos] at ht
  have e1 : 1 / ‖(u : ℂ) - z‖ ≤ 1 / (u - L) := one_div_le_one_div_of_le hp hd1
  have e2 : 1 / ‖(u : ℂ) + z‖ ≤ 1 / (u - L) := one_div_le_one_div_of_le hp hd2
  have key : ‖((Real.sin (c * u) + I * Real.cos (c * u)) / (u - z) +
      (Real.sin (c * u) - I * Real.cos (c * u)) / (u + z))‖ * (u - L) ≤ 2 := by
    have : ‖((Real.sin (c * u) + I * Real.cos (c * u)) / (u - z) +
      (Real.sin (c * u) - I * Real.cos (c * u)) / (u + z))‖ ≤ 2 / (u - L) := by
      calc _ ≤ 1 / ‖(u : ℂ) - z‖ + 1 / ‖(u : ℂ) + z‖ := ht
        _ ≤ 1 / (u - L) + 1 / (u - L) := add_le_add e1 e2
        _ = 2 / (u - L) := by ring
    rwa [le_div_iff₀ hp] at this
  nlinarith

/-! ### The carrier `w = e^{ibS}` -/

/-- **`Im S ≥ Im z`** for `S² = z² − a²` with `Im S ≥ 0`. -/
theorem im_le_im {z S : ℂ} {a : ℝ} (h : S ^ 2 = z ^ 2 - (a : ℂ) ^ 2) (hS : 0 ≤ S.im) :
    z.im ≤ S.im := by
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [sq, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
    Complex.ofReal_im] at hre him
  set p := S.re
  set q := S.im
  set x := z.re
  set y := z.im
  have hre' : p ^ 2 - q ^ 2 = x ^ 2 - y ^ 2 - a ^ 2 := by linarith
  have him' : p * q = x * y := by linarith
  have key : x ^ 2 * (y ^ 2 - q ^ 2) = q ^ 2 * (q ^ 2 - y ^ 2 - a ^ 2) := by
    linear_combination q ^ 2 * hre' - (p * q + x * y) * him'
  by_contra hlt
  push Not at hlt
  have hyq : 0 < y ^ 2 - q ^ 2 := by nlinarith
  have hL : 0 ≤ x ^ 2 * (y ^ 2 - q ^ 2) := mul_nonneg (sq_nonneg x) hyq.le
  have hR : q ^ 2 * (q ^ 2 - y ^ 2 - a ^ 2) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (sq_nonneg q) (by nlinarith [sq_nonneg a])
  have hx0 : x ^ 2 = 0 := by
    have : x ^ 2 * (y ^ 2 - q ^ 2) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact h
    · linarith
  have hq0 : q ^ 2 = 0 := by
    have h0 : q ^ 2 * (q ^ 2 - y ^ 2 - a ^ 2) = 0 := by linarith
    rcases mul_eq_zero.1 h0 with h | h
    · exact h
    · nlinarith [sq_nonneg a]
  nlinarith [sq_nonneg p, sq_nonneg a]

/-- `|e^{ibS}e^{−ibz}| ≤ 1` for `b ≥ 0`, `S² = z² − a²`, `Im S ≥ 0`. -/
theorem norm_exp_mul_exp_le {z S : ℂ} {a b : ℝ} (hb : 0 ≤ b) (h : S ^ 2 = z ^ 2 - (a : ℂ) ^ 2)
    (hS : 0 ≤ S.im) : ‖Complex.exp (I * b * S) * Complex.exp (-(I * b * z))‖ ≤ 1 := by
  rw [← Complex.exp_add, Complex.norm_exp]
  have : (I * b * S + -(I * b * z)).re = -b * (S.im - z.im) := by
    simp [Complex.mul_re, Complex.mul_im]; ring
  rw [this, Real.exp_le_one_iff]
  have := im_le_im h hS
  nlinarith

/-! ### The turning point of the lip phase -/

/-- **The lip phase turns at `x² = a²/(1 − r²)`**: for `0 < a < x` and `0 < r`, `rx/√(x² − a²) > 1` iff
`(1 − r²)x² < a²`. -/
theorem lip_turn {a r x : ℝ} (ha : 0 < a) (hx : a < x) (hr : 0 < r) :
    1 < r * x / √(x ^ 2 - a ^ 2) ↔ (1 - r ^ 2) * x ^ 2 < a ^ 2 := by
  have hpos : 0 < x ^ 2 - a ^ 2 := by nlinarith
  have hs := Real.sq_sqrt hpos.le
  have hs0 : 0 < √(x ^ 2 - a ^ 2) := Real.sqrt_pos.2 hpos
  rw [lt_div_iff₀ hs0, one_mul]
  constructor
  · intro h; nlinarith [mul_self_lt_mul_self hs0.le h]
  · intro h
    have hrx : 0 < r * x := by nlinarith
    by_contra hle
    push Not at hle
    nlinarith [mul_self_le_mul_self hrx.le hle]

/-- At `a = r = 1/2` the turning point is `ℓ = 1/√3`: `ℓ² = a²/(1 − r²) = 1/3`. -/
theorem lip_turn_half {x : ℝ} (hx : 1 / 2 < x) : 1 < 1 / 2 * x / √(x ^ 2 - (1 / 2) ^ 2) ↔ x ^ 2 < 1 / 3 := by
  rw [lip_turn (by norm_num) hx (by norm_num)]
  constructor <;> intro h <;> nlinarith

end Cvs.Prolate.Hardy.ExteriorSincColumns

end
