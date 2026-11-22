import Mathlib
import Cvs.Prolate.Mellin.FrozenRootErrorIdentity
import Cvs.Prolate.Mellin.WkbPhaseAntiderivative
import Cvs.Upstream.ComplexArsinhStrip

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The WKB phase on the imaginary axis past the turning point

For real `y ≥ 0`, `√(−y²) = iy` on the principal branch. Hence for `w ≥ 1`, `ash(iw) = arcosh w + iπ/2`, and for
`z ≥ 2c > 0`, with `w = z/(2c)`, `s = √(w² − 1)`: `S(iz) = 2ics`,
`Ĝ(iz) = −iz(arcosh w + iπ/2) + 2ics − ½(log 2c + log(1 + is))` and
`ĝ(iz) = −(arcosh w + iπ/2) − iz/(2S(S + 2c))` with `|iz/(2S(S + 2c))| = 1/(4cs)` when `s > 0`.
-/

noncomputable section

open Complex

namespace Cvs.Prolate.Mellin.WkbPhaseImaginaryAxis

open Cvs.Prolate.Mellin.FrozenRootErrorIdentity (csqrt csqrt_sq)
open Cvs.Upstream.ComplexArsinhStrip (ash)
open Cvs.Prolate.Mellin.WkbPhaseAntiderivative (Sq Gh gh)

/-- `√(−y²) = iy` for real `y ≥ 0`. -/
theorem csqrt_neg_sq {y : ℝ} (hy : 0 ≤ y) : csqrt (-((y : ℂ) ^ 2)) = I * y := by
  unfold csqrt
  apply Complex.ext
  · rw [Complex.cpow_inv_two_re]
    have h1 : ‖-((y : ℂ) ^ 2)‖ = y ^ 2 := by rw [norm_neg, norm_pow, Complex.norm_real, Real.norm_of_nonneg hy]
    have h2 : (-((y : ℂ) ^ 2)).re = -y ^ 2 := by simp [sq]
    rw [h1, h2]; simp
  · rw [Complex.cpow_inv_two_im_eq_sqrt (by simp [sq])]
    have h1 : ‖-((y : ℂ) ^ 2)‖ = y ^ 2 := by rw [norm_neg, norm_pow, Complex.norm_real, Real.norm_of_nonneg hy]
    have h2 : (-((y : ℂ) ^ 2)).re = -y ^ 2 := by simp [sq]
    rw [h1, h2, show (y ^ 2 - -y ^ 2) / 2 = y ^ 2 by ring, Real.sqrt_sq hy]
    simp

/-- **`ash(iw) = arcosh w + iπ/2`** for `w ≥ 1`. -/
theorem ash_I_mul {w : ℝ} (hw : 1 ≤ w) : ash (I * w) = (Real.arcosh w : ℂ) + I * (Real.pi / 2) := by
  have hs : 0 ≤ w ^ 2 - 1 := by nlinarith
  set s := Real.sqrt (w ^ 2 - 1)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hss : s ^ 2 = w ^ 2 - 1 := Real.sq_sqrt hs
  have hsC : (s : ℂ) ^ 2 = (w : ℂ) ^ 2 - 1 := by rw [← Complex.ofReal_pow, hss]; push_cast; ring
  have e1 : (I * (w : ℂ)) ^ 2 + 1 = -((s : ℂ) ^ 2) := by
    rw [mul_pow, I_sq, hsC]; ring
  have hpos : 0 < w + s := by linarith
  unfold ash
  rw [e1, csqrt_neg_sq hs0, show I * (w : ℂ) + I * s = ((w + s : ℝ) : ℂ) * I by push_cast; ring,
    Complex.log_ofReal_mul hpos I_ne_zero, Complex.log_I]
  unfold Real.arcosh
  ring

variable {c z : ℝ}

/-- **`S(iz) = 2ics`.** -/
theorem Sq_I_mul (hc : 0 < c) (hz : 2 * c ≤ z) :
    Sq c (I * z) = I * ((2 * c * Real.sqrt ((z / (2 * c)) ^ 2 - 1) : ℝ) : ℂ) := by
  have hw : 1 ≤ z / (2 * c) := by rw [le_div_iff₀ (by positivity)]; linarith
  have hs : 0 ≤ (z / (2 * c)) ^ 2 - 1 := by nlinarith
  set s := Real.sqrt ((z / (2 * c)) ^ 2 - 1)
  have hss : s ^ 2 = (z / (2 * c)) ^ 2 - 1 := Real.sq_sqrt hs
  have e : (I * (z : ℂ)) ^ 2 + 4 * (c : ℂ) ^ 2 = -(((2 * c * s : ℝ) : ℂ) ^ 2) := by
    rw [mul_pow, I_sq]
    have : ((2 * c * s : ℝ) : ℂ) ^ 2 = ((4 * c ^ 2 * s ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this, hss]
    have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
    push_cast; field_simp; ring
  unfold Sq
  rw [e, csqrt_neg_sq (by positivity)]

/-- **`Ĝ(iz)` in closed form.** -/
theorem Gh_I_mul (hc : 0 < c) (hz : 2 * c ≤ z) :
    Gh c (I * z) = -(I * z) * ((Real.arcosh (z / (2 * c)) : ℂ) + I * (Real.pi / 2))
      + I * ((2 * c * Real.sqrt ((z / (2 * c)) ^ 2 - 1) : ℝ) : ℂ)
      - 1 / 2 * ((Real.log (2 * c) : ℝ) + Complex.log (1 + I * Real.sqrt ((z / (2 * c)) ^ 2 - 1))) := by
  have hw : 1 ≤ z / (2 * c) := by rw [le_div_iff₀ (by positivity)]; linarith
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have ha : I * (z : ℂ) / (2 * c) = I * ((z / (2 * c) : ℝ) : ℂ) := by push_cast; ring
  have hlog : Complex.log (2 * c + I * ((2 * c * Real.sqrt ((z / (2 * c)) ^ 2 - 1) : ℝ) : ℂ))
      = (Real.log (2 * c) : ℂ) + Complex.log (1 + I * Real.sqrt ((z / (2 * c)) ^ 2 - 1)) := by
    rw [show (2 * (c : ℂ) + I * ((2 * c * Real.sqrt ((z / (2 * c)) ^ 2 - 1) : ℝ) : ℂ))
        = ((2 * c : ℝ) : ℂ) * (1 + I * Real.sqrt ((z / (2 * c)) ^ 2 - 1)) by push_cast; ring,
      Complex.log_ofReal_mul (by positivity)]
    intro h0
    have := congrArg Complex.re h0; simp at this
  unfold Gh
  rw [ha, ash_I_mul hw, Sq_I_mul hc hz, hlog]

/-- **`ĝ(iz)` in closed form.** -/
theorem gh_I_mul (hc : 0 < c) (hz : 2 * c ≤ z) :
    gh c (I * z) = -((Real.arcosh (z / (2 * c)) : ℂ) + I * (Real.pi / 2))
      - I * z / (2 * Sq c (I * z) * (Sq c (I * z) + 2 * c)) := by
  have hw : 1 ≤ z / (2 * c) := by rw [le_div_iff₀ (by positivity)]; linarith
  have ha : I * (z : ℂ) / (2 * c) = I * ((z / (2 * c) : ℝ) : ℂ) := by push_cast; ring
  unfold gh
  rw [ha, ash_I_mul hw]

/-- The correction at `iz` has norm `1/(4cs)`. -/
theorem norm_corr_I (hc : 0 < c) (hz : 2 * c < z) :
    ‖I * z / (2 * Sq c (I * z) * (Sq c (I * z) + 2 * c))‖ = 1 / (4 * c * Real.sqrt ((z / (2 * c)) ^ 2 - 1)) := by
  have hw : 1 < z / (2 * c) := by rw [lt_div_iff₀ (by positivity)]; linarith
  have hs : 0 < (z / (2 * c)) ^ 2 - 1 := by nlinarith
  set s := Real.sqrt ((z / (2 * c)) ^ 2 - 1)
  have hs0 : 0 < s := Real.sqrt_pos.mpr hs
  have hss : s ^ 2 = (z / (2 * c)) ^ 2 - 1 := Real.sq_sqrt hs.le
  have hz0 : 0 < z := by linarith
  rw [Sq_I_mul hc hz.le]
  have hnum : ‖I * (z : ℂ)‖ = z := by rw [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_of_nonneg hz0.le, one_mul]
  have ha : ‖I * ((2 * c * s : ℝ) : ℂ)‖ = 2 * c * s := by
    rw [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_of_nonneg (by positivity), one_mul]
  have hb : ‖I * ((2 * c * s : ℝ) : ℂ) + 2 * c‖ = z := by
    have hsq : ‖I * ((2 * c * s : ℝ) : ℂ) + 2 * c‖ ^ 2 = z ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp
      have : (2 * c * s) ^ 2 + (2 * c) ^ 2 = z ^ 2 := by
        rw [mul_pow, hss]; field_simp; ring
      nlinarith
    exact (pow_left_inj₀ (norm_nonneg _) hz0.le two_ne_zero).mp hsq
  rw [norm_div, hnum, norm_mul, norm_mul, Complex.norm_two, ha, hb]
  field_simp
  norm_num

end Cvs.Prolate.Mellin.WkbPhaseImaginaryAxis
