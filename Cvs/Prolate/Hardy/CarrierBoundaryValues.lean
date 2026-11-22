import Mathlib
import Cvs.Prolate.Hardy.HardyExtensionOperator

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The boundary values of the carrier `w = e^{ibS}` on the real line

On `I = [−½, ½]`, `S(x) = i√(¼ − x²)` and `w(x) = e^{−b√(¼ − x²)}` is real and positive; for `x ≥ ½`,
`S(x) = √(x² − ¼)`, for `x ≤ −½`, `S(x) = −√(x² − ¼)`, and there `|w(x)| = 1`.
-/

noncomputable section

open Real
open Complex (I)

namespace Cvs.Prolate.Hardy.CarrierBoundaryValues
open Cvs.ZeroCounting

open Cvs.Prolate.Hardy.HardyExtensionOperator (sS wC wR)

/-- `√(it) = √(|t|/2)(1 ± i)` with the sign of `t`, for real `t`. -/
theorem sqrt_I_mul_of_nonneg {t : ℝ} (ht : 0 ≤ t) : Complex.sqrt (I * t) = (√(t / 2) : ℂ) * (1 + I) := by
  rw [Complex.sqrt_eq_real_add_ite]
  have hn : ‖I * (t : ℂ)‖ = t := by rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_of_nonneg ht]
  have hre : (I * (t : ℂ)).re = 0 := by simp
  have him : (I * (t : ℂ)).im = t := by simp
  rw [hn, hre, him, if_pos ht]
  simp only [add_zero, sub_zero, one_mul]
  ring

theorem sqrt_I_mul_of_nonpos {t : ℝ} (ht : t ≤ 0) : Complex.sqrt (I * t) = (√(-t / 2) : ℂ) * (1 - I) := by
  rw [Complex.sqrt_eq_real_add_ite]
  have hn : ‖I * (t : ℂ)‖ = -t := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_of_nonpos ht]
  have hre : (I * (t : ℂ)).re = 0 := by simp
  have him : (I * (t : ℂ)).im = t := by simp
  rw [hn, hre, him]
  rcases ht.lt_or_eq with h | h
  · rw [if_neg (not_le.2 h)]
    simp only [add_zero, sub_zero]
    ring
  · subst h; simp

theorem sS_eq (x : ℝ) : sS x = I * Complex.sqrt (I * ((1 / 2 - x : ℝ) : ℂ)) *
    Complex.sqrt (I * ((-(1 / 2) - x : ℝ) : ℂ)) := by
  unfold sS
  congr 2 <;> push_cast <;> ring_nf

theorem sqrt_div_two_mul {p q : ℝ} (hp : 0 ≤ p) :
    (√(p / 2) : ℂ) * (√(q / 2) : ℂ) = (√(p * q) : ℂ) / 2 := by
  rw [← Complex.ofReal_mul, ← Real.sqrt_mul (by positivity)]
  have : p / 2 * (q / 2) = p * q / 4 := by ring
  rw [this, Real.sqrt_div' _ (by norm_num : (0:ℝ) ≤ 4), show (4 : ℝ) = 2 ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num)]
  push_cast; ring

/-- **On `I`**: `S(x) = i√(¼ − x²)`. -/
theorem sS_of_abs_le {x : ℝ} (hx : |x| ≤ 1 / 2) : sS x = I * (√(1 / 4 - x ^ 2) : ℂ) := by
  obtain ⟨h1, h2⟩ := abs_le.1 hx
  rw [sS_eq, sqrt_I_mul_of_nonneg (by linarith), sqrt_I_mul_of_nonpos (by linarith)]
  have e : I * ((√((1 / 2 - x) / 2) : ℂ) * (1 + I)) * ((√(-(-(1 / 2) - x) / 2) : ℂ) * (1 - I)) =
      I * ((√((1 / 2 - x) / 2) : ℂ) * (√(-(-(1 / 2) - x) / 2) : ℂ)) * ((1 + I) * (1 - I)) := by ring
  rw [e, sqrt_div_two_mul (by linarith)]
  have hI : (1 + I) * (1 - I) = 2 := by ring_nf; rw [Complex.I_sq]; ring
  rw [hI, show (1 / 2 - x) * -(-(1 / 2) - x) = 1 / 4 - x ^ 2 by ring]
  ring

/-- **Right of `I`**: `S(x) = √(x² − ¼)` for `x ≥ ½`. -/
theorem sS_of_ge {x : ℝ} (hx : 1 / 2 ≤ x) : sS x = (√(x ^ 2 - 1 / 4) : ℂ) := by
  rw [sS_eq, sqrt_I_mul_of_nonpos (by linarith), sqrt_I_mul_of_nonpos (by linarith)]
  have e : I * ((√(-(1 / 2 - x) / 2) : ℂ) * (1 - I)) * ((√(-(-(1 / 2) - x) / 2) : ℂ) * (1 - I)) =
      I * ((√(-(1 / 2 - x) / 2) : ℂ) * (√(-(-(1 / 2) - x) / 2) : ℂ)) * ((1 - I) * (1 - I)) := by ring
  rw [e, sqrt_div_two_mul (by linarith)]
  have hI : (1 - I) * (1 - I) = -2 * I := by ring_nf; rw [Complex.I_sq]; ring
  rw [hI, show -(1 / 2 - x) * -(-(1 / 2) - x) = x ^ 2 - 1 / 4 by ring]
  ring_nf; rw [Complex.I_sq]; ring

/-- **Left of `I`**: `S(x) = −√(x² − ¼)` for `x ≤ −½`. -/
theorem sS_of_le {x : ℝ} (hx : x ≤ -(1 / 2)) : sS x = -(√(x ^ 2 - 1 / 4) : ℂ) := by
  rw [sS_eq, sqrt_I_mul_of_nonneg (by linarith), sqrt_I_mul_of_nonneg (by linarith)]
  have e : I * ((√((1 / 2 - x) / 2) : ℂ) * (1 + I)) * ((√((-(1 / 2) - x) / 2) : ℂ) * (1 + I)) =
      I * ((√((1 / 2 - x) / 2) : ℂ) * (√((-(1 / 2) - x) / 2) : ℂ)) * ((1 + I) * (1 + I)) := by ring
  rw [e, sqrt_div_two_mul (by linarith)]
  have hI : (1 + I) * (1 + I) = 2 * I := by ring_nf; rw [Complex.I_sq]; ring
  rw [hI, show (1 / 2 - x) * (-(1 / 2) - x) = x ^ 2 - 1 / 4 by ring]
  ring_nf; rw [Complex.I_sq]; ring

/-- The real boundary phase `S(x) = sgn(x)√(x² − ¼)` off `I`. -/
def sR (x : ℝ) : ℝ := if 0 ≤ x then √(x ^ 2 - 1 / 4) else -√(x ^ 2 - 1 / 4)

theorem sS_of_half_le_abs {x : ℝ} (hx : 1 / 2 ≤ |x|) : sS x = (sR x : ℂ) := by
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h] at hx; rw [sS_of_ge hx, sR, if_pos h]
  · rw [abs_of_neg h] at hx; rw [sS_of_le (by linarith), sR, if_neg (not_le.2 h)]; push_cast; ring

theorem sR_neg (x : ℝ) : sR (-x) = -sR x := by
  unfold sR
  rcases lt_trichotomy x 0 with h | h | h
  · rw [if_pos (by linarith), if_neg (not_le.2 h), neg_sq, neg_neg]
  · subst h; norm_num
  · rw [if_neg (by linarith), if_pos h.le, neg_sq]

/-- **On `I`**: `w(x) = e^{−b√(¼ − x²)}`. -/
theorem wR_of_abs_le (b : ℝ) {x : ℝ} (hx : |x| ≤ 1 / 2) :
    wR b x = (Real.exp (-(b * √(1 / 4 - x ^ 2))) : ℂ) := by
  unfold wR wC
  rw [sS_of_abs_le hx, Complex.ofReal_exp]
  congr 1
  push_cast
  ring_nf
  rw [Complex.I_sq]; ring

/-- Off `I`: `w(x) = e^{ibS(x)}` with real `S(x)`. -/
theorem wR_of_half_le_abs (b : ℝ) {x : ℝ} (hx : 1 / 2 ≤ |x|) : wR b x = Complex.exp (I * (b * sR x)) := by
  unfold wR wC
  rw [sS_of_half_le_abs hx]
  ring_nf

theorem norm_wR_of_half_le_abs (b : ℝ) {x : ℝ} (hx : 1 / 2 ≤ |x|) : ‖wR b x‖ = 1 := by
  rw [wR_of_half_le_abs b hx, mul_comm, ← Complex.ofReal_mul, Complex.norm_exp_ofReal_mul_I]

theorem continuous_sR : Continuous sR := by
  unfold sR
  refine Continuous.if_le (by fun_prop) (by fun_prop) continuous_const continuous_id fun x hx => ?_
  subst hx
  norm_num

end Cvs.Prolate.Hardy.CarrierBoundaryValues

end
