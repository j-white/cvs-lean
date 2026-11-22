import Mathlib
import Cvs.Prolate.Mellin.FrozenRootClosedBounds
import Cvs.Prolate.Mellin.FrozenRootErrorIdentity
import Cvs.Prolate.Mellin.PastTurningContraction
import Cvs.Prolate.Mellin.StepQuadraticRoots

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Sizes of the frozen root and its forcing past the turning point

With `m = s + 3/2` and `w = √(τ² + 1)` on the region of Cvs.Prolate.Mellin.PastTurningContraction: `|ω/(s+2)| ≤ 1`, `|ζ| ≤ 1/|τ|`, `|w|² ≥ ε|τ|²/8`,
`|τ| ≥ |m|/(3c)`, and the exact step `ζ' − ζ = −(τ' − τ)(ζ + ζ')/(w + w')` with `|w + w'| ≥ |w|`. Hence
`|ρ*(s+2) − ρ*(s)| ≤ 110c/(√ε|m|²)`, `|B| ≤ 660c²/(√ε|m|³)`, `|A(s+2) − A(s)| ≤ 1340c²/(√ε|m|³)` and `|A| ≤ 1 − √ε/4`.
-/

noncomputable section

open Complex

namespace Cvs.Prolate.Mellin.PastTurningRootSizes

open Cvs.Prolate.Mellin.FrozenRootErrorIdentity (csqrt csqrt_sq re_csqrt_nonneg omega omega_sq tau zeta rhoStar zeta_ne_zero)
open Cvs.Prolate.Mellin.FrozenRootClosedBounds (norm_omega_sub_le Rq)
open Cvs.Prolate.Mellin.PastTurningContraction (Up csqrt_parts_pos)

variable {ε c χ : ℝ} {s : ℂ}

theorem im_le_norm (z : ℂ) : z.im ≤ ‖z‖ := (le_abs_self _).trans (Complex.abs_im_le_norm z)

theorem Up.add_two (h : Up ε c χ s) : Up ε c χ (s + 2) where
  hε := h.hε
  hε1 := h.hε1
  hc := h.hc
  hχ0 := h.hχ0
  hχ1 := h.hχ1
  hre := by simp; linarith [h.hre]
  him := by simpa using h.him

theorem Up.two_c_le (h : Up ε c χ s) : 2 * c ≤ s.im := by
  have := h.hε; have := h.c_pos; nlinarith [h.him]

/-- `|s + a| ≥ 2c` for real `a`. -/
theorem Up.norm_add_ge (h : Up ε c χ s) (a : ℝ) : 2 * c ≤ ‖s + a‖ := by
  have := im_le_norm (s + a); simp at this; linarith [(Up.two_c_le h)]

theorem Up.add_ne (h : Up ε c χ s) (a : ℝ) : s + a ≠ 0 := by
  intro h0; have := (Up.norm_add_ge h) a; rw [h0, norm_zero] at this; linarith [h.c_pos]

/-- `|s + a| ≤ |s + b|` for `0 ≤ a ≤ b` on `Re s ≥ 0`. -/
theorem norm_add_mono {s : ℂ} (hs : 0 ≤ s.re) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : ‖s + a‖ ≤ ‖s + b‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply,
    Complex.normSq_apply]
  simp
  nlinarith

/-- **`|ω/(s+2)| ≤ 1`.** -/
theorem Up.norm_kappa_le (h : Up ε c χ s) : ‖omega s / (s + 2)‖ ≤ 1 := by
  have hs2 : 0 < ‖s + 2‖ := norm_pos_iff.mpr (by simpa using (Up.add_ne h) 2)
  have hsq : ‖omega s‖ ^ 2 = ‖s + 1‖ * ‖s + 2‖ := by
    rw [← norm_pow, omega_sq h.m_ne, norm_mul]
  have h12 : ‖s + 1‖ ≤ ‖s + 2‖ := by
    have := norm_add_mono (s := s) (by linarith [h.hre]) (a := 1) (b := 2) (by norm_num) (by norm_num)
    simpa using this
  rw [norm_div, div_le_one hs2]
  nlinarith [norm_nonneg (omega s)]

theorem Up.norm_rho_le (h : Up ε c χ s) : ‖rhoStar c χ s‖ ≤ ‖zeta c χ s‖ := by
  rw [show rhoStar c χ s = omega s / (s + 2) * zeta c χ s by unfold rhoStar; ring, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (Up.norm_kappa_le h)

theorem zeta_mul_add (c χ : ℝ) (s : ℂ) : zeta c χ s * (csqrt (tau c χ s ^ 2 + 1) + tau c χ s) = 1 := by
  unfold zeta
  have := csqrt_sq (tau c χ s ^ 2 + 1)
  linear_combination this

theorem normSq_add_ge_of_nonneg {w t : ℂ} (h : 0 ≤ w.re * t.re + w.im * t.im) :
    Complex.normSq w + Complex.normSq t ≤ Complex.normSq (w + t) := by
  rw [Complex.normSq_add]
  have : (w * (starRingEnd ℂ) t).re = w.re * t.re + w.im * t.im := by simp
  linarith

theorem Up.Rq_nonneg (h : Up ε c χ s) : 0 ≤ Rq (tau c χ s) := (Real.sqrt_nonneg _).trans h.Rq_ge

/-- **`|ζ|² ≤ 1/(|w|² + |τ|²)`.** -/
theorem Up.norm_zeta_sq_le (h : Up ε c χ s) :
    ‖zeta c χ s‖ ^ 2 ≤ 1 / (‖csqrt (tau c χ s ^ 2 + 1)‖ ^ 2 + ‖tau c χ s‖ ^ 2) := by
  have he := zeta_mul_add c χ s
  set w := csqrt (tau c χ s ^ 2 + 1)
  set t := tau c χ s
  have hge := normSq_add_ge_of_nonneg (w := w) (t := t) (Up.Rq_nonneg h)
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hge
  have ht : 1 ≤ ‖t‖ := by
    have := im_le_norm t; linarith [h.im_tau_ge, h.hε]
  have hpos : 0 < ‖w‖ ^ 2 + ‖t‖ ^ 2 := by positivity
  have hn : ‖zeta c χ s‖ * ‖w + t‖ = 1 := by rw [← norm_mul, he, norm_one]
  rw [le_div_iff₀ hpos]
  have : ‖zeta c χ s‖ ^ 2 * ‖w + t‖ ^ 2 = 1 := by rw [← mul_pow, hn, one_pow]
  nlinarith [sq_nonneg ‖zeta c χ s‖]

theorem Up.norm_zeta_le (h : Up ε c χ s) : ‖zeta c χ s‖ ≤ 1 / ‖tau c χ s‖ := by
  have h1 := (Up.norm_zeta_sq_le h)
  have ht : 0 < ‖tau c χ s‖ := by
    have := im_le_norm (tau c χ s); linarith [h.im_tau_ge, h.hε]
  have h2 : ‖zeta c χ s‖ ^ 2 ≤ (1 / ‖tau c χ s‖) ^ 2 := by
    refine h1.trans ?_
    rw [div_pow, one_pow]
    exact one_div_le_one_div_of_le (by positivity) (by nlinarith [norm_nonneg (csqrt (tau c χ s ^ 2 + 1))])
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h2

/-- **`|w|² ≥ ε|τ|²/8`.** -/
theorem Up.norm_w_sq_ge (h : Up ε c χ s) : ε / 8 * ‖tau c χ s‖ ^ 2 ≤ ‖csqrt (tau c χ s ^ 2 + 1)‖ ^ 2 := by
  set t := tau c χ s
  have hε := h.hε
  have hε1 := h.hε1
  have hy := h.im_tau_ge
  have hw : ‖csqrt (t ^ 2 + 1)‖ ^ 2 = ‖t ^ 2 + 1‖ := by rw [← norm_pow, csqrt_sq]
  rw [hw]
  have hf : t ^ 2 + 1 = (t - I) * (t + I) := by ring_nf; rw [I_sq]; ring
  have h1 : ε / 4 ≤ ‖t - I‖ := by
    have := im_le_norm (t - I); simp at this; linarith
  have h2 : 2 ≤ ‖t + I‖ := by
    have := im_le_norm (t + I); simp at this; linarith
  have hlow : ε / 2 ≤ ‖t ^ 2 + 1‖ := by
    rw [hf, norm_mul]; nlinarith
  have hlow2 : ‖t‖ ^ 2 - 1 ≤ ‖t ^ 2 + 1‖ := by
    have := norm_sub_norm_le (t ^ 2 + 1) (-1 : ℂ)
    rw [show t ^ 2 + 1 - -1 = t ^ 2 + 2 by ring] at this
    have h3 : ‖t ^ 2‖ ≤ ‖t ^ 2 + 1‖ + ‖(1 : ℂ)‖ := by
      have := norm_sub_le (t ^ 2 + 1) 1; rw [show t ^ 2 + 1 - 1 = t ^ 2 by ring] at this; exact this
    rw [norm_pow, norm_one] at h3; linarith
  by_cases ht : 2 ≤ ‖t‖ ^ 2
  · nlinarith
  · push Not at ht; nlinarith

theorem Up.norm_w_ge (h : Up ε c χ s) :
    Real.sqrt ε * ‖tau c χ s‖ / 3 ≤ ‖csqrt (tau c χ s ^ 2 + 1)‖ := by
  have h1 := (Up.norm_w_sq_ge h)
  have hε := h.hε
  have hs : Real.sqrt ε ^ 2 = ε := Real.sq_sqrt hε.le
  have h2 : (Real.sqrt ε * ‖tau c χ s‖ / 3) ^ 2 ≤ ‖csqrt (tau c χ s ^ 2 + 1)‖ ^ 2 := by
    rw [div_pow, mul_pow, hs]; nlinarith [sq_nonneg ‖tau c χ s‖]
  exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).mp h2

/-- **`|τ| ≥ |m|/(3c)`**. -/
theorem Up.norm_tau_ge (h : Up ε c χ s) : ‖s + 3 / 2‖ / (3 * c) ≤ ‖tau c χ s‖ := by
  have hc := h.c_pos
  have hc64 := h.c_ge
  have hω := h.omega_ne
  have hm := (Up.norm_add_ge h) (3 / 2)
  push_cast at hm
  have hd := h.norm_omega_sub
  have hωge : ‖s + 3 / 2‖ - 1 / 8 ≤ ‖omega s‖ := by
    have := norm_sub_norm_le (s + 3 / 2) (omega s); rw [norm_sub_rev] at hd; linarith
  have hωpos : 0 < ‖omega s‖ := by linarith
  have hχ0 : 0 ≤ χ := by linarith [h.hχ0]
  have hq : ‖(χ : ℂ) / omega s‖ ≤ 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hχ0, div_le_one hωpos]
    linarith [h.hχ1]
  have hnum : ‖s + 3 / 2‖ - 9 / 8 ≤ ‖omega s - χ / omega s‖ := by
    have := norm_sub_norm_le (omega s) (χ / omega s); linarith
  unfold tau
  rw [norm_div, show ‖(2 * (c : ℂ))‖ = 2 * c by
    rw [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc],
    div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- **The exact `ζ`-step.** -/
theorem zeta_step_eq {t t' w w' : ℂ} (hw : w ^ 2 = t ^ 2 + 1) (hw' : w' ^ 2 = t' ^ 2 + 1) (hs : w + w' ≠ 0) :
    (w' - t') - (w - t) = -(t' - t) * ((w - t) + (w' - t')) / (w + w') := by
  field_simp
  linear_combination hw' - hw

theorem norm_le_norm_add_of_quadrant {w w' : ℂ} (h1 : 0 ≤ w.re) (h2 : 0 ≤ w.im) (h3 : 0 ≤ w'.re)
    (h4 : 0 ≤ w'.im) : ‖w‖ ≤ ‖w + w'‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  have := normSq_add_ge_of_nonneg (w := w) (t := w') (by positivity)
  linarith [Complex.normSq_nonneg w']

/-- **The `ζ`-step bound**: `|ζ' − ζ| ≤ |τ' − τ|(|ζ| + |ζ'|)/|w|`. -/
theorem Up.norm_zeta_step_le (h : Up ε c χ s) :
    ‖zeta c χ (s + 2) - zeta c χ s‖
      ≤ ‖tau c χ (s + 2) - tau c χ s‖ * (‖zeta c χ s‖ + ‖zeta c χ (s + 2)‖)
          / ‖csqrt (tau c χ s ^ 2 + 1)‖ := by
  have h' := (Up.add_two h)
  obtain ⟨a1, b1⟩ := csqrt_parts_pos h.re_tau_pos (by linarith [h.im_tau_ge, h.hε])
  obtain ⟨a2, b2⟩ := csqrt_parts_pos h'.re_tau_pos (by linarith [h'.im_tau_ge, h'.hε])
  set w := csqrt (tau c χ s ^ 2 + 1)
  set w' := csqrt (tau c χ (s + 2) ^ 2 + 1)
  have hle := norm_le_norm_add_of_quadrant (w := w) (w' := w') a1.le b1.le a2.le b2.le
  have hwpos : 0 < ‖w‖ := by
    have := Complex.abs_re_le_norm w; rw [abs_of_pos a1] at this; linarith
  have hs : w + w' ≠ 0 := by intro h0; rw [h0, norm_zero] at hle; linarith
  have e := zeta_step_eq (t := tau c χ s) (t' := tau c χ (s + 2)) (csqrt_sq _) (csqrt_sq _) hs
  have ez : zeta c χ (s + 2) - zeta c χ s = (w' - tau c χ (s + 2)) - (w - tau c χ s) := by
    unfold zeta; rfl
  rw [ez, e, norm_div, norm_mul, norm_neg]
  have hz : ‖(w - tau c χ s) + (w' - tau c χ (s + 2))‖ ≤ ‖zeta c χ s‖ + ‖zeta c χ (s + 2)‖ := by
    have := norm_add_le (w - tau c χ s) (w' - tau c χ (s + 2)); unfold zeta at *; exact this
  calc ‖tau c χ (s + 2) - tau c χ s‖ * ‖(w - tau c χ s) + (w' - tau c χ (s + 2))‖ / ‖w + w'‖
      ≤ ‖tau c χ (s + 2) - tau c χ s‖ * (‖zeta c χ s‖ + ‖zeta c χ (s + 2)‖) / ‖w‖ := by
        apply div_le_div₀ (by positivity) (by gcongr) hwpos hle
    _ = _ := rfl

/-- **The `τ`-step**: `|τ(s+2) − τ(s)| ≤ 2/c`. -/
theorem Up.norm_tau_step_le (h : Up ε c χ s) : ‖tau c χ (s + 2) - tau c χ s‖ ≤ 2 / c := by
  have h' := (Up.add_two h)
  have hc := h.c_pos
  have hc64 := h.c_ge
  have hω := h.omega_ne
  have hω' := h'.omega_ne
  have hχ0 : 0 ≤ χ := by linarith [h.hχ0]
  have hωge : ∀ {u : ℂ}, Up ε c χ u → 2 * c - 1 / 8 ≤ ‖omega u‖ := by
    intro u hu
    have hm := (Up.norm_add_ge hu) (3 / 2); push_cast at hm
    have hd := hu.norm_omega_sub
    have := norm_sub_norm_le (u + 3 / 2) (omega u); rw [norm_sub_rev] at hd; linarith
  have hn := hωge h
  have hn' := hωge h'
  have e : tau c χ (s + 2) - tau c χ s
      = (omega (s + 2) - omega s) * (1 + (χ : ℂ) / (omega s * omega (s + 2))) / (2 * c) := by
    unfold tau
    rw [← Cvs.Prolate.Mellin.StepQuadraticRoots.tau_num_sub hω hω']
    ring
  rw [e]
  have hd : ‖omega (s + 2) - omega s‖ ≤ 9 / 4 := by
    have h1 := h.norm_omega_sub
    have h2 := h'.norm_omega_sub
    calc ‖omega (s + 2) - omega s‖
        = ‖(omega (s + 2) - (s + 2 + 3 / 2)) - (omega s - (s + 3 / 2)) + 2‖ := by ring_nf
      _ ≤ ‖omega (s + 2) - (s + 2 + 3 / 2)‖ + ‖omega s - (s + 3 / 2)‖ + ‖(2 : ℂ)‖ := by
          refine (norm_add_le _ _).trans ?_
          gcongr
          exact norm_sub_le _ _
      _ ≤ 9 / 4 := by norm_num; linarith
  have hprod : c ≤ ‖omega s‖ * ‖omega (s + 2)‖ / 64 := by nlinarith
  have hq : ‖1 + (χ : ℂ) / (omega s * omega (s + 2))‖ ≤ 1 + 1 / 64 := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_one, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hχ0]
    have hp : 0 < ‖omega s‖ * ‖omega (s + 2)‖ := by nlinarith
    have : χ / (‖omega s‖ * ‖omega (s + 2)‖) ≤ 1 / 64 := by
      rw [div_le_iff₀ hp]; nlinarith [h.hχ1]
    linarith
  rw [norm_div, norm_mul, show ‖(2 * (c : ℂ))‖ = 2 * c by
    rw [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]]
  rw [div_le_div_iff₀ (by positivity) hc]
  have := mul_le_mul hd hq (norm_nonneg _) (by norm_num)
  nlinarith

end Cvs.Prolate.Mellin.PastTurningRootSizes
