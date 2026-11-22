import Mathlib
import Cvs.Prolate.Mellin.FrozenRootErrorIdentity

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Closed-form bounds for `ω`, `τ` and `|ζ|`

`|√(1 − u) − 1| ≤ |u|` for the principal root, so `|ω − m| ≤ 1/(4|m|)` with `m = s + 3/2`. Exactly,
`Re τ = Re ω (|ω|² − χ)/(2c|ω|²)` and `Im τ = Im ω (|ω|² + χ)/(2c|ω|²)`. With `√(τ²+1) = a + ib`,
`a² ≥ 1 − (Im τ)²`, and `R = Re τ (a² + (Im τ)²)/a` lies between `Re τ/|τ² + 1|^{1/2}` and `Re τ/√(1 − (Im τ)²)`
times `1 + (Re τ)²/(1 − (Im τ)²)`, according to the sign of `Re τ`.
-/

noncomputable section

open Complex

namespace Cvs.Prolate.Mellin.FrozenRootClosedBounds

open Cvs.Prolate.Mellin.FrozenRootErrorIdentity (csqrt csqrt_sq re_csqrt_nonneg omega tau zeta)

/-- **`|√(1 − u) − 1| ≤ |u|`** for the principal square root. -/
theorem norm_csqrt_one_sub_sub_le (u : ℂ) : ‖csqrt (1 - u) - 1‖ ≤ ‖u‖ := by
  have hsq := csqrt_sq (1 - u)
  have hre := re_csqrt_nonneg (1 - u)
  have hpos : 1 ≤ ‖csqrt (1 - u) + 1‖ := by
    calc (1 : ℝ) ≤ (csqrt (1 - u) + 1).re := by simp; linarith
      _ ≤ ‖csqrt (1 - u) + 1‖ := Complex.re_le_norm _
  have hprod : (csqrt (1 - u) - 1) * (csqrt (1 - u) + 1) = -u := by linear_combination hsq
  have h := congrArg norm hprod
  rw [norm_mul, norm_neg] at h
  calc ‖csqrt (1 - u) - 1‖ = ‖csqrt (1 - u) - 1‖ * 1 := (mul_one _).symm
    _ ≤ ‖csqrt (1 - u) - 1‖ * ‖csqrt (1 - u) + 1‖ := mul_le_mul_of_nonneg_left hpos (norm_nonneg _)
    _ = ‖u‖ := h

/-- **`|ω − m| ≤ 1/(4|m|)`** with `m = s + 3/2 ≠ 0`. -/
theorem norm_omega_sub_le {s : ℂ} (hm : s + 3 / 2 ≠ 0) :
    ‖omega s - (s + 3 / 2)‖ ≤ 1 / (4 * ‖s + 3 / 2‖) := by
  have hm0 : 0 < ‖s + 3 / 2‖ := norm_pos_iff.mpr hm
  have h := norm_csqrt_one_sub_sub_le (1 / (4 * (s + 3 / 2) ^ 2))
  have e : omega s - (s + 3 / 2) = (s + 3 / 2) * (csqrt (1 - 1 / (4 * (s + 3 / 2) ^ 2)) - 1) := by
    unfold omega; ring
  rw [e, norm_mul]
  calc ‖s + 3 / 2‖ * ‖csqrt (1 - 1 / (4 * (s + 3 / 2) ^ 2)) - 1‖
      ≤ ‖s + 3 / 2‖ * ‖1 / (4 * (s + 3 / 2) ^ 2)‖ := mul_le_mul_of_nonneg_left h (norm_nonneg _)
    _ = 1 / (4 * ‖s + 3 / 2‖) := by
      rw [norm_div, norm_one, norm_mul, norm_pow]
      simp only [Complex.norm_ofNat]
      field_simp

/-- **`Re τ = Re ω (|ω|² − χ)/(2c|ω|²)`.** -/
theorem re_tau {c χ : ℝ} (hc : c ≠ 0) {s : ℂ} (hω : omega s ≠ 0) :
    (tau c χ s).re = (omega s).re * (Complex.normSq (omega s) - χ) / (2 * c * Complex.normSq (omega s)) := by
  have hn : Complex.normSq (omega s) ≠ 0 := by rwa [Ne, Complex.normSq_eq_zero]
  unfold tau
  have h2c : (2 * (c : ℂ)) = ((2 * c : ℝ) : ℂ) := by push_cast; ring
  rw [h2c, Complex.div_ofReal_re, Complex.sub_re, Complex.div_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  field_simp
  ring

/-- **`Im τ = Im ω (|ω|² + χ)/(2c|ω|²)`.** -/
theorem im_tau {c χ : ℝ} (hc : c ≠ 0) {s : ℂ} (hω : omega s ≠ 0) :
    (tau c χ s).im = (omega s).im * (Complex.normSq (omega s) + χ) / (2 * c * Complex.normSq (omega s)) := by
  have hn : Complex.normSq (omega s) ≠ 0 := by rwa [Ne, Complex.normSq_eq_zero]
  unfold tau
  have h2c : (2 * (c : ℂ)) = ((2 * c : ℝ) : ℂ) := by push_cast; ring
  rw [h2c, Complex.div_ofReal_im, Complex.sub_im, Complex.div_im]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, zero_div]
  field_simp
  ring

/-- With `√(τ²+1) = a + ib`: `a² − b² = (Re τ)² − (Im τ)² + 1` and `ab = Re τ · Im τ`. -/
theorem csqrt_parts (t : ℂ) :
    (csqrt (t ^ 2 + 1)).re ^ 2 - (csqrt (t ^ 2 + 1)).im ^ 2 = t.re ^ 2 - t.im ^ 2 + 1 ∧
      (csqrt (t ^ 2 + 1)).re * (csqrt (t ^ 2 + 1)).im = t.re * t.im := by
  have hsq := csqrt_sq (t ^ 2 + 1)
  set w := csqrt (t ^ 2 + 1)
  have hre := congrArg Complex.re hsq
  have him := congrArg Complex.im hsq
  simp only [sq, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.one_re,
    Complex.one_im] at hre him
  constructor <;> nlinarith

/-- **`a² ≥ 1 − (Im τ)²`**, so `a > 0` once `|Im τ| < 1`. -/
theorem re_csqrt_sq_ge (t : ℂ) : 1 - t.im ^ 2 ≤ (csqrt (t ^ 2 + 1)).re ^ 2 := by
  have := (csqrt_parts t).1
  nlinarith [sq_nonneg (csqrt (t ^ 2 + 1)).im, sq_nonneg t.re]

theorem re_csqrt_pos {t : ℂ} (ht : t.im ^ 2 < 1) : 0 < (csqrt (t ^ 2 + 1)).re := by
  have h := re_csqrt_sq_ge t
  have h0 := re_csqrt_nonneg (t ^ 2 + 1)
  rcases h0.lt_or_eq with h0 | h0
  · exact h0
  · rw [← h0] at h; nlinarith

/-- The real part `R = a Re τ + b Im τ` of `√(τ²+1) τ̄`. -/
def Rq (t : ℂ) : ℝ := (csqrt (t ^ 2 + 1)).re * t.re + (csqrt (t ^ 2 + 1)).im * t.im

theorem Rq_eq {t : ℂ} (ht : t.im ^ 2 < 1) :
    Rq t = t.re * ((csqrt (t ^ 2 + 1)).re ^ 2 + t.im ^ 2) / (csqrt (t ^ 2 + 1)).re := by
  have ha := re_csqrt_pos ht
  have hp := (csqrt_parts t).2
  unfold Rq
  field_simp
  linear_combination t.im * hp

/-- **Lower bound for `Re τ ≥ 0`**: `R ≥ Re τ / ‖√(τ²+1)‖`. -/
theorem Rq_ge_of_nonneg {t : ℂ} (ht : t.im ^ 2 < 1) (hx : 0 ≤ t.re) :
    t.re / ‖csqrt (t ^ 2 + 1)‖ ≤ Rq t := by
  have ha := re_csqrt_pos ht
  set a := (csqrt (t ^ 2 + 1)).re
  have hn : a ≤ ‖csqrt (t ^ 2 + 1)‖ := Complex.re_le_norm _
  have hn0 : 0 < ‖csqrt (t ^ 2 + 1)‖ := ha.trans_le hn
  have h1 : 1 ≤ a ^ 2 + t.im ^ 2 := by
    have := (csqrt_parts t).1
    nlinarith [sq_nonneg (csqrt (t ^ 2 + 1)).im, sq_nonneg t.re]
  rw [Rq_eq ht, div_le_div_iff₀ hn0 ha]
  nlinarith [mul_le_mul_of_nonneg_left h1 hx, mul_le_mul_of_nonneg_left hn (mul_nonneg hx
    (by positivity : (0 : ℝ) ≤ a ^ 2 + t.im ^ 2))]

/-- **Lower bound for `Re τ ≤ 0`**: `R ≥ Re τ (1 + (Re τ)²/(1 − (Im τ)²))/√(1 − (Im τ)²)`. -/
theorem Rq_ge_of_nonpos {t : ℂ} (ht : t.im ^ 2 < 1) (hx : t.re ≤ 0) :
    t.re * (1 + t.re ^ 2 / (1 - t.im ^ 2)) / Real.sqrt (1 - t.im ^ 2) ≤ Rq t := by
  have ha := re_csqrt_pos ht
  set a := (csqrt (t ^ 2 + 1)).re
  set b := (csqrt (t ^ 2 + 1)).im
  have hy : 0 < 1 - t.im ^ 2 := by linarith
  have hs0 : 0 < Real.sqrt (1 - t.im ^ 2) := Real.sqrt_pos.mpr hy
  have ha2 : 1 - t.im ^ 2 ≤ a ^ 2 := re_csqrt_sq_ge t
  have hsa : Real.sqrt (1 - t.im ^ 2) ≤ a := by
    rw [Real.sqrt_le_left ha.le]; exact ha2
  obtain ⟨h1, h2⟩ := csqrt_parts t
  -- (a² + y²)/a = (1 + x² + b²)/a and b = xy/a
  have hb : b = t.re * t.im / a := by field_simp; linarith
  have key : (a ^ 2 + t.im ^ 2) / a ≤ (1 + t.re ^ 2 / (1 - t.im ^ 2)) / Real.sqrt (1 - t.im ^ 2) := by
    have e : (a ^ 2 + t.im ^ 2) / a = (1 + t.re ^ 2 + t.re ^ 2 * t.im ^ 2 / a ^ 2) / a := by
      have : a ^ 2 + t.im ^ 2 = 1 + t.re ^ 2 + b ^ 2 := by linarith
      rw [this, hb]; field_simp
    rw [e]
    have hnum : 1 + t.re ^ 2 + t.re ^ 2 * t.im ^ 2 / a ^ 2 ≤ 1 + t.re ^ 2 / (1 - t.im ^ 2) := by
      have : t.re ^ 2 * t.im ^ 2 / a ^ 2 ≤ t.re ^ 2 * t.im ^ 2 / (1 - t.im ^ 2) :=
        div_le_div_of_nonneg_left (by positivity) hy ha2
      have e2 : t.re ^ 2 + t.re ^ 2 * t.im ^ 2 / (1 - t.im ^ 2) = t.re ^ 2 / (1 - t.im ^ 2) := by
        field_simp; ring
      linarith
    calc (1 + t.re ^ 2 + t.re ^ 2 * t.im ^ 2 / a ^ 2) / a
        ≤ (1 + t.re ^ 2 / (1 - t.im ^ 2)) / a := div_le_div_of_nonneg_right hnum ha.le
      _ ≤ (1 + t.re ^ 2 / (1 - t.im ^ 2)) / Real.sqrt (1 - t.im ^ 2) :=
          div_le_div_of_nonneg_left (by positivity) hs0 hsa
  rw [Rq_eq ht, mul_div_assoc, mul_div_assoc]
  exact mul_le_mul_of_nonpos_left key hx

end Cvs.Prolate.Mellin.FrozenRootClosedBounds
