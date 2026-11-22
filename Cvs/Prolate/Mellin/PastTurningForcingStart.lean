import Mathlib
import Cvs.Prolate.Mellin.ForcingComplexLogTelescope
import Cvs.Prolate.Mellin.FrozenForcingIdentities
import Cvs.Prolate.Mellin.FrozenRootErrorIdentity
import Cvs.Prolate.Mellin.PastTurningContraction
import Cvs.Prolate.Mellin.PastTurningForcingSum
import Cvs.Prolate.Mellin.PastTurningRootSizes
import Cvs.Prolate.Mellin.PastTurningStepForcing
import Cvs.Prolate.Mellin.WkbPhaseImaginaryAxis

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The forcing constant at the start of the line past the turning point

At `s₀ = ½ + iz` with `z ≥ (2 + ε)c`, `w = z/(2c)` and `s = √(w² − 1)`: `ζ(iw) = −i(w − s)`, and the exact step
`ζ(τ) − ζ(iw) = −(τ − iw)(ζ(τ) + ζ(iw))/(√(τ²+1) + is)` gives `|ρ*(s₀) − ζ(iw)| ≤ 13/(√ε c)`. With
`1 − (w − s)² = 2s(w − s)` and `w − s = e^{−arcosh w}`:
`|log p(s₀) − log(1 + r(s₀)) − (log s − arcosh w)| ≤ 82/(εc)` for `c ≥ 108/ε`.
-/

noncomputable section

open Complex

namespace Cvs.Prolate.Mellin.PastTurningForcingStart

open Cvs.Prolate.Mellin.FrozenRootErrorIdentity (csqrt csqrt_sq omega tau zeta rhoStar)
open Cvs.Prolate.Mellin.FrozenForcingIdentities (rr pp)
open Cvs.Prolate.Mellin.PastTurningContraction (Up)

variable {ε c χ z : ℝ}

/-- `ζ(iw) = −i(w − s)`. -/
theorem zeta_I {w : ℝ} (hw : 1 ≤ w) :
    csqrt ((I * (w : ℂ)) ^ 2 + 1) - I * w = -(I * ((w - Real.sqrt (w ^ 2 - 1) : ℝ) : ℂ)) := by
  have hs : 0 ≤ w ^ 2 - 1 := by nlinarith
  have hsC : ((Real.sqrt (w ^ 2 - 1) : ℝ) : ℂ) ^ 2 = (w : ℂ) ^ 2 - 1 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hs]; push_cast; ring
  have e1 : (I * (w : ℂ)) ^ 2 + 1 = -(((Real.sqrt (w ^ 2 - 1) : ℝ) : ℂ) ^ 2) := by
    rw [mul_pow, I_sq, hsC]; ring
  rw [e1, Cvs.Prolate.Mellin.WkbPhaseImaginaryAxis.csqrt_neg_sq (Real.sqrt_nonneg _)]
  push_cast; ring

/-- **`|ρ*(s₀) − ζ(iw)| ≤ 13/(√ε c)`.** -/
theorem norm_rho_sub (h : Up ε c χ ((1 / 2 : ℂ) + I * z)) :
    ‖rhoStar c χ ((1 / 2 : ℂ) + I * z) + I * (((z / (2 * c)) - Real.sqrt ((z / (2 * c)) ^ 2 - 1) : ℝ) : ℂ)‖
      ≤ 13 / (Real.sqrt ε * c) := by
  set s₀ : ℂ := (1 / 2 : ℂ) + I * z
  have hc := h.c_pos
  have hε := h.hε
  have hc64 := h.c_ge
  set w := z / (2 * c)
  have hz : (2 + ε) * c ≤ z := by have := h.him; simpa [s₀] using this
  have hw : 1 ≤ w := by
    simp only [w]; rw [le_div_iff₀ (by positivity)]; nlinarith
  set r := Real.sqrt ε
  have hr0 : 0 < r := Real.sqrt_pos.mpr hε
  have hr1 : r ≤ 1 := Real.sqrt_le_one.mpr h.hε1
  set t := tau c χ s₀
  set W := csqrt (t ^ 2 + 1)
  set W0 := csqrt ((I * (w : ℂ)) ^ 2 + 1)
  have hW0 : W0 = I * ((Real.sqrt (w ^ 2 - 1) : ℝ) : ℂ) := by
    have hs : 0 ≤ w ^ 2 - 1 := by nlinarith
    have hsC : ((Real.sqrt (w ^ 2 - 1) : ℝ) : ℂ) ^ 2 = (w : ℂ) ^ 2 - 1 := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt hs]; push_cast; ring
    have e1 : (I * (w : ℂ)) ^ 2 + 1 = -(((Real.sqrt (w ^ 2 - 1) : ℝ) : ℂ) ^ 2) := by
      rw [mul_pow, I_sq, hsC]; ring
    simp only [W0]; rw [e1, Cvs.Prolate.Mellin.WkbPhaseImaginaryAxis.csqrt_neg_sq (Real.sqrt_nonneg _)]
  -- the exact step from `iw` to `τ`
  obtain ⟨ha, hb⟩ := Cvs.Prolate.Mellin.PastTurningContraction.csqrt_parts_pos h.re_tau_pos (by linarith [h.im_tau_ge, h.hε])
  have hW0re : 0 ≤ W0.re := by rw [hW0]; simp
  have hW0im : 0 ≤ W0.im := by rw [hW0]; simp
  have hle := Cvs.Prolate.Mellin.PastTurningRootSizes.norm_le_norm_add_of_quadrant (w := W) (w' := W0) ha.le hb.le hW0re hW0im
  have hWn := Cvs.Prolate.Mellin.PastTurningRootSizes.Up.norm_w_ge h
  have ht1 : 1 ≤ ‖t‖ := by have := Cvs.Prolate.Mellin.PastTurningRootSizes.im_le_norm t; linarith [h.im_tau_ge, h.hε]
  have hWpos : r / 3 ≤ ‖W‖ := by
    refine le_trans ?_ hWn; rw [show r / 3 = r * 1 / 3 by ring]; gcongr
  have hsum : W + W0 ≠ 0 := by intro h0; rw [h0, norm_zero] at hle; linarith [hr0]
  have hstep := Cvs.Prolate.Mellin.PastTurningRootSizes.zeta_step_eq (t := I * (w : ℂ)) (t' := t) (w := W0) (w' := W)
    (csqrt_sq _) (csqrt_sq _) (by rw [add_comm]; exact hsum)
  -- sizes
  have hz1 : ‖zeta c χ s₀‖ ≤ 1 := (Cvs.Prolate.Mellin.PastTurningRootSizes.Up.norm_zeta_le h).trans
    (by rw [div_le_one (by linarith)]; exact ht1)
  have hz0 : ‖W0 - I * (w : ℂ)‖ ≤ 1 := by
    rw [zeta_I hw, norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    have hs : Real.sqrt (w ^ 2 - 1) ≤ w := by rw [Real.sqrt_le_left (by linarith)]; nlinarith
    have hs0 : 0 ≤ Real.sqrt (w ^ 2 - 1) := Real.sqrt_nonneg _
    have : w - Real.sqrt (w ^ 2 - 1) ≤ 1 := by
      have : (w - 1) ^ 2 ≤ w ^ 2 - 1 := by nlinarith
      have := Real.sqrt_le_sqrt this; rw [Real.sqrt_sq (by linarith)] at this; linarith
    rw [abs_of_nonneg (by linarith)]; exact this
  -- `|τ − iw| ≤ 2/c`
  have htw : ‖t - I * (w : ℂ)‖ ≤ 2 / c := by
    have hω := h.omega_ne
    have hd := h.norm_omega_sub
    have hm := h.norm_m_ge
    have hωn : c ≤ ‖omega s₀‖ := by
      have := norm_sub_norm_le (s₀ + 3 / 2) (omega s₀); rw [norm_sub_rev] at hd
      have hm2 : 2 * c ≤ ‖s₀ + 3 / 2‖ := Cvs.Prolate.Mellin.PastTurningStepForcing.Up.norm_m_ge h
      linarith
    have hχ0 : 0 ≤ χ := by linarith [h.hχ0]
    have hq : ‖(χ : ℂ) / omega s₀‖ ≤ 1 := by
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hχ0, div_le_one (by linarith)]; linarith [h.hχ1]
    have hωi : ‖omega s₀ - I * z‖ ≤ 17 / 8 := by
      have : omega s₀ - I * z = (omega s₀ - (s₀ + 3 / 2)) + 2 := by simp only [s₀]; ring
      rw [this]; refine (norm_add_le _ _).trans ?_; norm_num; linarith
    have e : t - I * (w : ℂ) = (omega s₀ - I * z - χ / omega s₀) / (2 * c) := by
      simp only [t, w]; unfold tau; push_cast; field_simp; ring
    rw [e, norm_div, show ‖(2 * (c : ℂ))‖ = 2 * c by
      rw [norm_mul, Complex.norm_two, Complex.norm_real, Real.norm_of_nonneg hc.le], div_le_div_iff₀ (by positivity) hc]
    have := norm_sub_le (omega s₀ - I * z) ((χ : ℂ) / omega s₀)
    nlinarith
  -- `|ζ(τ) − ζ(iw)| ≤ 12/(√ε c)`
  have hdz : ‖zeta c χ s₀ - (W0 - I * w)‖ ≤ 12 / (r * c) := by
    have e : zeta c χ s₀ - (W0 - I * w) = (W - t) - (W0 - I * w) := by simp only [W, t]; unfold zeta; rfl
    rw [e, hstep, norm_div, norm_mul, norm_neg]
    have hnum : ‖(W0 - I * (w : ℂ)) + (W - t)‖ ≤ 2 := by
      refine (norm_add_le _ _).trans ?_
      have : ‖W - t‖ ≤ 1 := by simp only [W, t]; exact hz1
      linarith
    calc ‖t - I * (w : ℂ)‖ * ‖(W0 - I * (w : ℂ)) + (W - t)‖ / ‖W0 + W‖
        ≤ 2 / c * 2 / (r / 3) := by
          rw [add_comm W0 W]
          apply div_le_div₀ (by positivity) (mul_le_mul htw hnum (norm_nonneg _) (by positivity))
            (by positivity) (hWpos.trans hle)
      _ = 12 / (r * c) := by field_simp; ring
  -- `|κ − 1| ≤ 1/c`
  have hκ : ‖omega s₀ / (s₀ + 2) - 1‖ ≤ 1 / c := by
    have hs2 : s₀ + 2 ≠ 0 := by simpa using Cvs.Prolate.Mellin.PastTurningRootSizes.Up.add_ne h 2
    have hn2 : 2 * c ≤ ‖s₀ + 2‖ := by simpa using Cvs.Prolate.Mellin.PastTurningRootSizes.Up.norm_add_ge h 2
    rw [div_sub_one hs2, norm_div, div_le_div_iff₀ (by linarith) hc]
    have : ‖omega s₀ - (s₀ + 2)‖ ≤ 5 / 8 := by
      rw [show omega s₀ - (s₀ + 2) = (omega s₀ - (s₀ + 3 / 2)) - 1 / 2 by ring]
      refine (norm_sub_le _ _).trans ?_; norm_num; linarith [h.norm_omega_sub]
    nlinarith
  have hrho : rhoStar c χ s₀ = omega s₀ / (s₀ + 2) * zeta c χ s₀ := by unfold rhoStar; ring
  have hz0' : W0 - I * (w : ℂ) = -(I * ((w - Real.sqrt (w ^ 2 - 1) : ℝ) : ℂ)) := zeta_I hw
  rw [hrho]
  have e : omega s₀ / (s₀ + 2) * zeta c χ s₀ + I * ((w - Real.sqrt (w ^ 2 - 1) : ℝ) : ℂ)
      = (omega s₀ / (s₀ + 2) - 1) * zeta c χ s₀ + (zeta c χ s₀ - (W0 - I * w)) := by rw [hz0']; ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul]
  calc ‖omega s₀ / (s₀ + 2) - 1‖ * ‖zeta c χ s₀‖ + ‖zeta c χ s₀ - (W0 - I * w)‖
      ≤ 1 / c * 1 + 12 / (r * c) := by gcongr
    _ ≤ 13 / (r * c) := by
        have h1 : 1 / c ≤ 1 / (r * c) := one_div_le_one_div_of_le (by positivity) (by nlinarith)
        have e : 13 / (r * c) = 1 / (r * c) + 12 / (r * c) := by ring
        rw [mul_one, e]; linarith

/-- `log(p₀/2) = log s − arcosh w` with `p₀ = 1 − (w − s)²`. -/
theorem log_p0 {w : ℝ} (hw : 1 < w) :
    Real.log ((1 - (w - Real.sqrt (w ^ 2 - 1)) ^ 2) / 2) = Real.log (Real.sqrt (w ^ 2 - 1)) - Real.arcosh w := by
  have hs : 0 < w ^ 2 - 1 := by nlinarith
  set q := Real.sqrt (w ^ 2 - 1)
  have hq : 0 < q := Real.sqrt_pos.mpr hs
  have hqq : q ^ 2 = w ^ 2 - 1 := Real.sq_sqrt hs.le
  have hwq : 0 < w - q := by
    have : q < w := by rw [Real.sqrt_lt' (by linarith)]; linarith
    linarith
  have hwp : 0 < w + q := by linarith
  have e : (1 - (w - q) ^ 2) / 2 = q * (w - q) := by nlinarith
  have e2 : w - q = (w + q)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left; nlinarith
  rw [e, Real.log_mul hq.ne' hwq.ne', e2, Real.log_inv]
  unfold Real.arcosh
  ring

/-- **The forcing constant at the start of the line.** -/
theorem log_pp_start (h : Up ε c χ ((1 / 2 : ℂ) + I * z)) (hcε : 108 / ε ≤ c) :
    ‖Complex.log (pp c χ ((1 / 2 : ℂ) + I * z)) - Complex.log (1 + rr ((1 / 2 : ℂ) + I * z))
      - ((Real.log (Real.sqrt ((z / (2 * c)) ^ 2 - 1)) : ℂ) - Real.arcosh (z / (2 * c)))‖ ≤ 82 / (ε * c) := by
  set s₀ : ℂ := (1 / 2 : ℂ) + I * z
  have hc := h.c_pos
  have hε := h.hε
  have hε1 := h.hε1
  set w := z / (2 * c)
  have hz : (2 + ε) * c ≤ z := by have := h.him; simpa [s₀] using this
  have hw : 1 + ε / 2 ≤ w := by simp only [w]; rw [le_div_iff₀ (by positivity)]; nlinarith
  have hw1 : 1 < w := by linarith
  set r := Real.sqrt ε
  have hr0 : 0 < r := Real.sqrt_pos.mpr hε
  have hr1 : r ≤ 1 := Real.sqrt_le_one.mpr hε1
  have hrr : r * r = ε := Real.mul_self_sqrt hε.le
  set q := Real.sqrt (w ^ 2 - 1)
  have hqq : q ^ 2 = w ^ 2 - 1 := Real.sq_sqrt (by nlinarith)
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hqw : q ≤ w := by rw [Real.sqrt_le_left (by linarith)]; nlinarith
  set p₀ : ℝ := 1 - (w - q) ^ 2
  have hwq1 : w - q ≤ 1 := by
    have : (w - 1) ^ 2 ≤ w ^ 2 - 1 := by nlinarith
    have := Real.sqrt_le_sqrt this; rw [Real.sqrt_sq (by linarith)] at this; linarith
  -- `p₀ ≥ r/2`
  have hp₀ : r / 2 ≤ p₀ := by
    have hwq : 0 < w + q := by linarith
    have e : p₀ = 2 * q / (w + q) := by
      simp only [p₀]; field_simp; nlinarith
    rw [e, le_div_iff₀ hwq]
    have hrq : r * w ≤ 2 * q := by
      have h4 : (r * w) ^ 2 ≤ (2 * q) ^ 2 := by
        rw [mul_pow, mul_pow, show r ^ 2 = ε by rw [← hrr]; ring, hqq]
        have : 1 + ε ≤ w ^ 2 := by nlinarith
        nlinarith
      exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp h4
    nlinarith
  have hp₀1 : p₀ ≤ 1 := by simp only [p₀]; nlinarith
  -- `|p − p₀| ≤ 27/(rc)`
  have hρ := norm_rho_sub h
  set ρ := rhoStar c χ s₀
  set ζ₀ : ℂ := -(I * ((w - q : ℝ) : ℂ))
  have hρζ : ‖ρ - ζ₀‖ ≤ 13 / (r * c) := by
    simp only [ζ₀, sub_neg_eq_add]; exact hρ
  have hρ1 : ‖ρ‖ ≤ 1 := by
    refine (Cvs.Prolate.Mellin.PastTurningRootSizes.Up.norm_rho_le h).trans ((Cvs.Prolate.Mellin.PastTurningRootSizes.Up.norm_zeta_le h).trans ?_)
    have ht1 : 1 ≤ ‖tau c χ s₀‖ := by
      have := Cvs.Prolate.Mellin.PastTurningRootSizes.im_le_norm (tau c χ s₀); linarith [h.im_tau_ge]
    rw [div_le_one (by linarith)]; exact ht1
  have hζ1 : ‖ζ₀‖ ≤ 1 := by
    simp only [ζ₀]; rw [norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith)]; exact hwq1
  have hζsq : 1 + ζ₀ ^ 2 = (p₀ : ℂ) := by
    simp only [ζ₀, p₀]; push_cast; ring_nf; rw [I_sq]; ring
  have hrr1 : ‖rr s₀ - 1‖ ≤ 1 / (2 * c) := by
    have hs1 : s₀ + 1 ≠ 0 := by simpa using Cvs.Prolate.Mellin.PastTurningRootSizes.Up.add_ne h 1
    have hn1 : 2 * c ≤ ‖s₀ + 1‖ := by simpa using Cvs.Prolate.Mellin.PastTurningRootSizes.Up.norm_add_ge h 1
    have e : rr s₀ - 1 = 1 / (s₀ + 1) := by unfold rr; field_simp; ring
    rw [e, norm_div, norm_one]; exact one_div_le_one_div_of_le (by positivity) hn1
  have hpp : ‖pp c χ s₀ - p₀‖ ≤ 27 / (r * c) := by
    have e : pp c χ s₀ - p₀ = (rr s₀ - 1) * ρ ^ 2 + (ρ - ζ₀) * (ρ + ζ₀) := by
      rw [← hζsq]; unfold pp; ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_pow]
    have h1 : ‖ρ‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg ρ]
    have h2 : ‖ρ + ζ₀‖ ≤ 2 := (norm_add_le _ _).trans (by linarith)
    have h3 : 1 / (2 * c) ≤ 1 / (r * c) :=
      one_div_le_one_div_of_le (by positivity) (by nlinarith [mul_le_mul_of_nonneg_right hr1 hc.le])
    calc ‖rr s₀ - 1‖ * ‖ρ‖ ^ 2 + ‖ρ - ζ₀‖ * ‖ρ + ζ₀‖ ≤ 1 / (2 * c) * 1 + 13 / (r * c) * 2 := by gcongr
      _ ≤ 1 / (r * c) + 26 / (r * c) := by
          have : 13 / (r * c) * 2 = 26 / (r * c) := by ring
          linarith
      _ = 27 / (r * c) := by ring
  -- the logarithms
  have hp₀pos : 0 < p₀ := by linarith
  have hppre : 0 < (pp c χ s₀).re := by have := Cvs.Prolate.Mellin.PastTurningForcingSum.Up.re_pp_ge h; linarith
  have hratio : ‖pp c χ s₀ / p₀ - 1‖ ≤ 54 / (ε * c) := by
    rw [div_sub_one (by exact_mod_cast hp₀pos.ne'), norm_div, Complex.norm_real, Real.norm_of_nonneg hp₀pos.le,
      div_le_iff₀ hp₀pos]
    calc ‖pp c χ s₀ - p₀‖ ≤ 27 / (r * c) := hpp
      _ = 54 / (ε * c) * (r / 2) := by rw [← hrr]; field_simp; ring
      _ ≤ 54 / (ε * c) * p₀ := by gcongr
  have hhalf : 54 / (ε * c) ≤ 1 / 2 := by
    have h108 : 108 ≤ ε * c := by rw [div_le_iff₀ hε] at hcε; linarith [mul_comm c ε]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hlp := Cvs.Prolate.Mellin.ForcingComplexLogTelescope.log_sub_log_eq hppre (by simp; exact hp₀pos) (hratio.trans hhalf)
  have hlp' : ‖Complex.log (pp c χ s₀) - Complex.log p₀‖ ≤ 81 / (ε * c) := by
    rw [hlp]; refine (Cvs.Prolate.Mellin.ForcingComplexLogTelescope.norm_log_one_add_le (hratio.trans hhalf)).trans ?_
    have : 3 / 2 * (54 / (ε * c)) = 81 / (ε * c) := by ring
    linarith
  have hre1 : 0 < (1 + rr s₀).re := Cvs.Prolate.Mellin.PastTurningForcingSum.Up.re_one_add_rr h
  have hr2 : ‖(1 + rr s₀) / 2 - 1‖ ≤ 1 / (4 * c) := by
    rw [show (1 + rr s₀) / 2 - 1 = (rr s₀ - 1) / 2 by ring, norm_div, Complex.norm_two,
      div_le_iff₀ (by norm_num)]
    calc ‖rr s₀ - 1‖ ≤ 1 / (2 * c) := hrr1
      _ = 1 / (4 * c) * 2 := by field_simp; ring
  have hr2h : 1 / (4 * c) ≤ 1 / 2 := by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith [h.c_ge]
  have hlr := Cvs.Prolate.Mellin.ForcingComplexLogTelescope.log_sub_log_eq hre1 (by norm_num : (0 : ℝ) < (2 : ℂ).re) (hr2.trans hr2h)
  have hlr' : ‖Complex.log (1 + rr s₀) - Complex.log 2‖ ≤ 3 / (8 * c) := by
    rw [hlr]; refine (Cvs.Prolate.Mellin.ForcingComplexLogTelescope.norm_log_one_add_le (hr2.trans hr2h)).trans ?_
    rw [show (3 : ℝ) / (8 * c) = 3 / 2 * (1 / (4 * c)) by ring]; exact mul_le_mul_of_nonneg_left hr2 (by norm_num)
  -- the closed form
  have hcl : Complex.log (p₀ : ℂ) - Complex.log 2 = ((Real.log q : ℝ) : ℂ) - Real.arcosh w := by
    rw [← Complex.ofReal_log hp₀pos.le, show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_log (by norm_num),
      ← Complex.ofReal_sub, ← Real.log_div hp₀pos.ne' (by norm_num)]
    simp only [p₀]; rw [log_p0 hw1]; push_cast; ring
  have e : Complex.log (pp c χ s₀) - Complex.log (1 + rr s₀) - ((Real.log q : ℂ) - Real.arcosh w)
      = (Complex.log (pp c χ s₀) - Complex.log p₀) - (Complex.log (1 + rr s₀) - Complex.log 2) := by
    rw [← hcl]; ring
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  have : 3 / (8 * c) ≤ 1 / (ε * c) := by
    have hεc : 0 < ε * c := mul_pos hε hc
    have h8c : (0:ℝ) < 8 * c := by linarith
    have hec : ε * c ≤ 1 * c := mul_le_mul_of_nonneg_right hε1 hc.le
    rw [div_le_div_iff₀ h8c hεc]; linarith
  calc ‖Complex.log (pp c χ s₀) - Complex.log p₀‖ + ‖Complex.log (1 + rr s₀) - Complex.log 2‖
      ≤ 81 / (ε * c) + 1 / (ε * c) := by linarith
    _ = 82 / (ε * c) := by ring

end Cvs.Prolate.Mellin.PastTurningForcingStart
