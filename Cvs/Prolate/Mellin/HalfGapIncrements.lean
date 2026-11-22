import Mathlib
import Cvs.Prolate.Mellin.CompanionRootGap
import Cvs.Prolate.Mellin.FrozenRootErrorIdentity
import Cvs.Prolate.Mellin.FrozenRootFirstDifference
import Cvs.Prolate.Mellin.FrozenRootStep
import Cvs.Prolate.Mellin.UniformRootBounds

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Increments of `√(τ²+1)` and of the half-gap `W = ω√(τ²+1)/(s+2)`

With `|Im τ| ≤ 1`: `|τ| ≤ a + 1` and `|√(τ²+1)| ≤ a + 1`. Since `√' − √ = (τ' − τ)(τ' + τ)/(√' + √)` and
`|√' + √| ≥ a + a'`, `|√(τ(s+2)²+1) − √(τ(s)²+1)| ≤ |τ' − τ|(1 + 2/(a + a'))`. With `κ = ω/(s+2)`,
`W(s+2) − W(s) = (κ' − κ)√' + κ(√' − √)`.
-/

noncomputable section

open Complex

namespace Cvs.Prolate.Mellin.HalfGapIncrements

open Cvs.Prolate.Mellin.FrozenRootErrorIdentity (csqrt csqrt_sq re_csqrt_nonneg omega tau zeta rhoStar)
open Cvs.Prolate.Mellin.UniformRootBounds (Hyp)

variable {ε c χ : ℝ} {s : ℂ}

theorem norm_le_re_csqrt_add_one {t : ℂ} (ht : t.im ^ 2 < 1) : ‖t‖ ≤ (csqrt (t ^ 2 + 1)).re + 1 := by
  have hx := Cvs.Prolate.Mellin.CompanionRootGap.abs_re_le_re_csqrt ht.le
  have ha := re_csqrt_nonneg (t ^ 2 + 1)
  have hy : |t.im| ≤ 1 := by nlinarith [abs_nonneg t.im, sq_abs t.im]
  calc ‖t‖ ≤ |t.re| + |t.im| := Complex.norm_le_abs_re_add_abs_im t
    _ ≤ _ := by linarith

theorem norm_csqrt_le {t : ℂ} (ht : t.im ^ 2 < 1) : ‖csqrt (t ^ 2 + 1)‖ ≤ (csqrt (t ^ 2 + 1)).re + 1 := by
  have hb := Cvs.Prolate.Mellin.CompanionRootGap.abs_im_csqrt_le ht
  have ha := re_csqrt_nonneg (t ^ 2 + 1)
  have hy : |t.im| ≤ 1 := by nlinarith [abs_nonneg t.im, sq_abs t.im]
  calc ‖csqrt (t ^ 2 + 1)‖ ≤ |(csqrt (t ^ 2 + 1)).re| + |(csqrt (t ^ 2 + 1)).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ ≤ _ := by rw [abs_of_nonneg ha]; linarith

theorem Hyp.im_tau_sq_lt (h : Hyp ε c χ s) : (tau c χ s).im ^ 2 < 1 := by
  have := h.abs_im_tau_le; have := h.hε
  have h1 : |(tau c χ s).im| < 1 := by linarith
  nlinarith [abs_nonneg (tau c χ s).im, sq_abs (tau c χ s).im]

/-- **The `√`-increment**: `|√' − √| ≤ |τ' − τ|(1 + 2/(a + a'))`. -/
theorem Hyp.norm_csqrt_step_le (h : Hyp ε c χ s) :
    ‖csqrt (tau c χ (s + 2) ^ 2 + 1) - csqrt (tau c χ s ^ 2 + 1)‖
      ≤ ‖tau c χ (s + 2) - tau c χ s‖
        * (1 + 2 / ((csqrt (tau c χ s ^ 2 + 1)).re + (csqrt (tau c χ (s + 2) ^ 2 + 1)).re)) := by
  have h' := Cvs.Prolate.Mellin.FrozenRootStep.Hyp.add_two h
  set t := tau c χ s
  set t' := tau c χ (s + 2)
  set w := csqrt (t ^ 2 + 1)
  set w' := csqrt (t' ^ 2 + 1)
  have ha := Cvs.Prolate.Mellin.FrozenRootFirstDifference.Hyp.a_pos h
  have ha' := Cvs.Prolate.Mellin.FrozenRootFirstDifference.Hyp.a_pos h'
  have hD : w.re + w'.re ≤ ‖w + w'‖ := by have := Complex.re_le_norm (w + w'); simpa using this
  have hDpos : 0 < w.re + w'.re := by linarith
  have hne : w + w' ≠ 0 := by intro h0; rw [h0, norm_zero] at hD; linarith
  have e : w' - w = (t' - t) * (t' + t) / (w + w') := by
    rw [eq_div_iff hne]
    have h1 := csqrt_sq (t ^ 2 + 1); have h2 := csqrt_sq (t' ^ 2 + 1)
    linear_combination h2 - h1
  rw [e, norm_div, norm_mul]
  have hn : ‖t' + t‖ ≤ w.re + w'.re + 2 := by
    have := norm_le_re_csqrt_add_one (Hyp.im_tau_sq_lt h)
    have := norm_le_re_csqrt_add_one (Hyp.im_tau_sq_lt h')
    linarith [norm_add_le t' t]
  calc ‖t' - t‖ * ‖t' + t‖ / ‖w + w'‖ ≤ ‖t' - t‖ * (w.re + w'.re + 2) / (w.re + w'.re) :=
        div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hn (norm_nonneg _)) hDpos hD
    _ = ‖t' - t‖ * (1 + 2 / (w.re + w'.re)) := by field_simp

/-- The half-gap `W = ω √(τ²+1)/(s+2)` (so `ρ* − ρ₂ = 2W`). -/
def Wg (c χ : ℝ) (s : ℂ) : ℂ := omega s * csqrt (tau c χ s ^ 2 + 1) / (s + 2)

/-- **The `W`-increment.** -/
theorem Hyp.norm_Wg_step_le (h : Hyp ε c χ s) :
    ‖Wg c χ (s + 2) - Wg c χ s‖
      ≤ ‖omega (s + 2) / (s + 2 + 2) - omega s / (s + 2)‖ * ((csqrt (tau c χ (s + 2) ^ 2 + 1)).re + 1)
        + 17 / 12 * (‖tau c χ (s + 2) - tau c χ s‖
          * (1 + 2 / ((csqrt (tau c χ s ^ 2 + 1)).re + (csqrt (tau c χ (s + 2) ^ 2 + 1)).re))) := by
  have h' := Cvs.Prolate.Mellin.FrozenRootStep.Hyp.add_two h
  have e : Wg c χ (s + 2) - Wg c χ s
      = (omega (s + 2) / (s + 2 + 2) - omega s / (s + 2)) * csqrt (tau c χ (s + 2) ^ 2 + 1)
        + omega s / (s + 2) * (csqrt (tau c χ (s + 2) ^ 2 + 1) - csqrt (tau c χ s ^ 2 + 1)) := by
    unfold Wg; ring
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_csqrt_le (Hyp.im_tau_sq_lt h')) (norm_nonneg _)
  · rw [norm_mul]
    exact mul_le_mul (Cvs.Prolate.Mellin.FrozenRootStep.norm_kappa_le h) (Hyp.norm_csqrt_step_le h) (norm_nonneg _)
      (by norm_num)

end Cvs.Prolate.Mellin.HalfGapIncrements
