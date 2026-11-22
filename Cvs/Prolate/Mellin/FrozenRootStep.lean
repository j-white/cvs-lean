import Mathlib
import Cvs.Prolate.Mellin.CompanionRootGap
import Cvs.Prolate.Mellin.FrozenRootClosedBounds
import Cvs.Prolate.Mellin.FrozenRootErrorIdentity
import Cvs.Prolate.Mellin.FrozenRootSizeBounds
import Cvs.Prolate.Mellin.StepQuadraticRoots
import Cvs.Prolate.Mellin.UniformRootBounds

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The step of the frozen root and the shifted root gap

With `κ = ω/(s+2)`, `ρ* = κζ`: `κ(s+2) − κ(s) = (1 + δ(s+2)(s+2) − δ(s)(s+4))/((s+2)(s+4))`, `δ = ω − (s + 3/2)`;
`τ(s+2) − τ(s) = (ω' − ω)(1 + χ/(ωω'))/(2c)`; and `|ζ' − ζ| ≤ 3|τ' − τ|/(a + a')`. For `ε ≤ 1/4` this gives the
shifted gap `|ρ*(s+2) − ρ₂(s)| ≥ (3/4) Re √(τ(s)² + 1)`.
-/

noncomputable section

open Complex

namespace Cvs.Prolate.Mellin.FrozenRootStep

open Cvs.Prolate.Mellin.FrozenRootErrorIdentity (csqrt csqrt_sq re_csqrt_nonneg omega omega_sq tau zeta rhoStar)
open Cvs.Prolate.Mellin.StepQuadraticRoots (comp)
open Cvs.Prolate.Mellin.UniformRootBounds (Hyp)

variable {ε c χ : ℝ} {s : ℂ}

theorem Hyp.add_two (h : Hyp ε c χ s) : Hyp ε c χ (s + 2) where
  hε := h.hε
  hε1 := h.hε1
  hc := h.hc
  hχ0 := h.hχ0
  hχ1 := h.hχ1
  hre := by simp; linarith [h.hre]
  him := by simpa using h.him

theorem norm_kappa_le (h : Hyp ε c χ s) : ‖omega s / (s + 2)‖ ≤ 17 / 12 := by
  have hω := Cvs.Prolate.Mellin.FrozenRootSizeBounds.Hyp.norm_omega_le h
  have hs2 := Cvs.Prolate.Mellin.FrozenRootSizeBounds.Hyp.norm_s2_ge_m h
  have hm := h.norm_m_ge
  rw [norm_div, div_le_iff₀ (by linarith)]
  nlinarith

theorem rhoStar_eq_kappa (c χ : ℝ) (s : ℂ) : rhoStar c χ s = omega s / (s + 2) * zeta c χ s := by
  unfold rhoStar; ring

/-- **The `κ`-step.** -/
theorem norm_kappa_step_le (h : Hyp ε c χ s) :
    ‖omega (s + 2) / (s + 2 + 2) - omega s / (s + 2)‖
      ≤ 1 / (‖s + 2‖ * ‖s + 4‖) + 1 / 8 * (1 / ‖s + 4‖ + 1 / ‖s + 2‖) := by
  have h' := Hyp.add_two h
  have hs2 := h.s2_ne
  have hs4 : s + 4 ≠ 0 := by
    have := h'.s2_ne; rwa [show s + 2 + 2 = s + 4 by ring] at this
  have hN2 : 0 < ‖s + 2‖ := norm_pos_iff.mpr hs2
  have hN4 : 0 < ‖s + 4‖ := norm_pos_iff.mpr hs4
  set δ := omega s - (s + 3 / 2)
  set δ' := omega (s + 2) - (s + 2 + 3 / 2)
  have hδ : ‖δ‖ ≤ 1 / 8 := h.norm_omega_sub
  have hδ' : ‖δ'‖ ≤ 1 / 8 := h'.norm_omega_sub
  have e : omega (s + 2) / (s + 2 + 2) - omega s / (s + 2)
      = 1 / ((s + 2) * (s + 4)) + δ' / (s + 4) - δ / (s + 2) := by
    rw [show s + 2 + 2 = s + 4 by ring]
    simp only [δ, δ']
    field_simp
    ring
  rw [e]
  calc ‖1 / ((s + 2) * (s + 4)) + δ' / (s + 4) - δ / (s + 2)‖
      ≤ ‖1 / ((s + 2) * (s + 4))‖ + ‖δ' / (s + 4)‖ + ‖δ / (s + 2)‖ := by
        refine (norm_sub_le _ _).trans ?_
        gcongr
        exact norm_add_le _ _
    _ ≤ 1 / (‖s + 2‖ * ‖s + 4‖) + 1 / 8 * (1 / ‖s + 4‖ + 1 / ‖s + 2‖) := by
        rw [norm_div, norm_div, norm_div, norm_one, norm_mul]
        have a1 : ‖δ'‖ / ‖s + 4‖ ≤ 1 / 8 * (1 / ‖s + 4‖) := by
          rw [mul_one_div]; exact div_le_div_of_nonneg_right hδ' hN4.le
        have a2 : ‖δ‖ / ‖s + 2‖ ≤ 1 / 8 * (1 / ‖s + 2‖) := by
          rw [mul_one_div]; exact div_le_div_of_nonneg_right hδ hN2.le
        linarith

/-- **The `τ`-step**: `|τ(s+2) − τ(s)| ≤ (9/8)(1/c + 1/(‖ω‖‖ω'‖))`. -/
theorem norm_tau_step_le (h : Hyp ε c χ s) :
    ‖tau c χ (s + 2) - tau c χ s‖ ≤ 9 / 8 * (1 / c + 1 / (‖omega s‖ * ‖omega (s + 2)‖)) := by
  have h' := Hyp.add_two h
  have hc := h.c_pos
  have hω := h.omega_ne
  have hω' := h'.omega_ne
  have hn : 0 < ‖omega s‖ := norm_pos_iff.mpr hω
  have hn' : 0 < ‖omega (s + 2)‖ := norm_pos_iff.mpr hω'
  have hχ0 : 0 ≤ χ := by linarith [h.hχ0, h.c_ge]
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
  have hq : ‖1 + (χ : ℂ) / (omega s * omega (s + 2))‖ ≤ 1 + c / (‖omega s‖ * ‖omega (s + 2)‖) := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_one, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hχ0]
    gcongr
    exact h.hχ1
  rw [norm_div, norm_mul, show ‖(2 * (c : ℂ))‖ = 2 * c by
    rw [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]]
  rw [div_le_iff₀ (by positivity)]
  have := mul_le_mul hd hq (norm_nonneg _) (by norm_num)
  have e2 : 9 / 8 * (1 / c + 1 / (‖omega s‖ * ‖omega (s + 2)‖)) * (2 * c)
      = 9 / 4 * (1 + c / (‖omega s‖ * ‖omega (s + 2)‖)) := by field_simp; ring
  rw [e2]; exact this

/-- **The `ζ`-step**: `|ζ(s+2) − ζ(s)| ≤ 3|τ(s+2) − τ(s)|/(a + a')`. -/
theorem norm_zeta_step_le (h : Hyp ε c χ s) :
    ‖zeta c χ (s + 2) - zeta c χ s‖
      ≤ 3 * ‖tau c χ (s + 2) - tau c χ s‖
        / ((csqrt (tau c χ s ^ 2 + 1)).re + (csqrt (tau c χ (s + 2) ^ 2 + 1)).re) := by
  have h' := Hyp.add_two h
  have ha := h.a_sq_ge
  have ha' := h'.a_sq_ge
  have ha0 := re_csqrt_nonneg (tau c χ s ^ 2 + 1)
  have ha0' := re_csqrt_nonneg (tau c χ (s + 2) ^ 2 + 1)
  have hε := h.hε
  have hapos : 0 < (csqrt (tau c χ s ^ 2 + 1)).re + (csqrt (tau c χ (s + 2) ^ 2 + 1)).re := by
    by_contra hneg; push Not at hneg
    have : (csqrt (tau c χ s ^ 2 + 1)).re = 0 := by linarith
    rw [this] at ha; nlinarith
  have hD : csqrt (tau c χ s ^ 2 + 1) + csqrt (tau c χ (s + 2) ^ 2 + 1) ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    simp at this; linarith
  have e := Cvs.Prolate.Mellin.StepQuadraticRoots.zeta_sub (tau c χ s) (tau c χ (s + 2)) hD
  have ez : zeta c χ (s + 2) - zeta c χ s
      = -(tau c χ (s + 2) - tau c χ s) * (zeta c χ s + zeta c χ (s + 2))
          / (csqrt (tau c χ s ^ 2 + 1) + csqrt (tau c χ (s + 2) ^ 2 + 1)) := by
    unfold zeta; exact e
  rw [ez, norm_div, norm_mul, norm_neg]
  have hz : ‖zeta c χ s + zeta c χ (s + 2)‖ ≤ 3 := by
    have := Cvs.Prolate.Mellin.FrozenRootSizeBounds.Hyp.zeta_norm_le h
    have := Cvs.Prolate.Mellin.FrozenRootSizeBounds.Hyp.zeta_norm_le h'
    linarith [norm_add_le (zeta c χ s) (zeta c χ (s + 2))]
  have hre : (csqrt (tau c χ s ^ 2 + 1)).re + (csqrt (tau c χ (s + 2) ^ 2 + 1)).re
      ≤ ‖csqrt (tau c χ s ^ 2 + 1) + csqrt (tau c χ (s + 2) ^ 2 + 1)‖ := by
    have := Complex.re_le_norm (csqrt (tau c χ s ^ 2 + 1) + csqrt (tau c χ (s + 2) ^ 2 + 1))
    simpa using this
  calc ‖tau c χ (s + 2) - tau c χ s‖ * ‖zeta c χ s + zeta c χ (s + 2)‖
        / ‖csqrt (tau c χ s ^ 2 + 1) + csqrt (tau c χ (s + 2) ^ 2 + 1)‖
      ≤ ‖tau c χ (s + 2) - tau c χ s‖ * 3
        / ((csqrt (tau c χ s ^ 2 + 1)).re + (csqrt (tau c χ (s + 2) ^ 2 + 1)).re) := by
        apply div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hz (norm_nonneg _)) hapos hre
    _ = _ := by ring

/-- **The `ρ*`-step**: `|ρ*(s+2) − ρ*(s)| ≤ (17/12)|ζ' − ζ| + (3/2)|κ' − κ|`. -/
theorem norm_rho_step_le (h : Hyp ε c χ s) :
    ‖rhoStar c χ (s + 2) - rhoStar c χ s‖
      ≤ 17 / 12 * ‖zeta c χ (s + 2) - zeta c χ s‖
        + 3 / 2 * ‖omega (s + 2) / (s + 2 + 2) - omega s / (s + 2)‖ := by
  have h' := Hyp.add_two h
  rw [rhoStar_eq_kappa, rhoStar_eq_kappa]
  have e : omega (s + 2) / (s + 2 + 2) * zeta c χ (s + 2) - omega s / (s + 2) * zeta c χ s
      = omega (s + 2) / (s + 2 + 2) * (zeta c χ (s + 2) - zeta c χ s)
        + (omega (s + 2) / (s + 2 + 2) - omega s / (s + 2)) * zeta c χ s := by ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul]
  have k := norm_kappa_le h'
  have z := Cvs.Prolate.Mellin.FrozenRootSizeBounds.Hyp.zeta_norm_le h
  have i1 := mul_le_mul_of_nonneg_right k (norm_nonneg (zeta c χ (s + 2) - zeta c χ s))
  have i2 := mul_le_mul_of_nonneg_left z
    (norm_nonneg (omega (s + 2) / (s + 2 + 2) - omega s / (s + 2)))
  linarith

/-- `‖ρ* − ρ₂‖ ≥ (3/2) Re √(τ² + 1)`. -/
theorem gap_ge (h : Hyp ε c χ s) :
    3 / 2 * (csqrt (tau c χ s ^ 2 + 1)).re ≤ ‖rhoStar c χ s - comp s (rhoStar c χ s)‖ := by
  rw [Cvs.Prolate.Mellin.CompanionRootGap.rhoStar_sub_comp h.m_ne h.s2_ne h.omega_ne]
  have ha0 := re_csqrt_nonneg (tau c χ s ^ 2 + 1)
  have hre : (csqrt (tau c χ s ^ 2 + 1)).re ≤ ‖csqrt (tau c χ s ^ 2 + 1)‖ := Complex.re_le_norm _
  have hωg := h.norm_omega_ge
  have hs2 := Cvs.Prolate.Mellin.FrozenRootSizeBounds.Hyp.norm_s2_ge_m h
  have hmg := h.norm_m_ge
  have hs2' : ‖s + 2‖ ≤ ‖s + 3 / 2‖ + 1 / 2 := by
    have := norm_add_le (s + 3 / 2) (1 / 2 : ℂ)
    rw [show s + 3 / 2 + 1 / 2 = s + 2 by ring] at this
    simpa using this
  have hN : 0 < ‖s + 2‖ := by linarith
  rw [norm_div, norm_mul, norm_mul, Complex.norm_ofNat, le_div_iff₀ hN]
  nlinarith [norm_nonneg (omega s), norm_nonneg (csqrt (tau c χ s ^ 2 + 1))]

set_option maxHeartbeats 1000000 in
/-- **The shifted root gap**: for `ε ≤ 1/4`, `‖ρ*(s+2) − ρ₂(s)‖ ≥ (3/4) Re √(τ(s)² + 1)`. -/
theorem shifted_gap_ge (h : Hyp ε c χ s) (hε4 : ε ≤ 1 / 4) :
    3 / 4 * (csqrt (tau c χ s ^ 2 + 1)).re ≤ ‖rhoStar c χ (s + 2) - comp s (rhoStar c χ s)‖ := by
  have h' := Hyp.add_two h
  set a := (csqrt (tau c χ s ^ 2 + 1)).re
  set a' := (csqrt (tau c χ (s + 2) ^ 2 + 1)).re
  have ha0 : 0 ≤ a := re_csqrt_nonneg _
  have ha0' : 0 ≤ a' := re_csqrt_nonneg _
  have hg : 3 / 2 * a ≤ ‖rhoStar c χ s - comp s (rhoStar c χ s)‖ := gap_ge h
  have hstep := norm_rho_step_le h
  have hz := norm_zeta_step_le h
  have ht := norm_tau_step_le h
  have hk := norm_kappa_step_le h
  -- it suffices that the step is at most (3/4) a
  suffices hs : ‖rhoStar c χ (s + 2) - rhoStar c χ s‖ ≤ 3 / 4 * a by
    have := norm_sub_norm_le (rhoStar c χ s - comp s (rhoStar c χ s))
      (rhoStar c χ s - rhoStar c χ (s + 2))
    rw [show rhoStar c χ s - comp s (rhoStar c χ s) - (rhoStar c χ s - rhoStar c χ (s + 2))
      = rhoStar c χ (s + 2) - comp s (rhoStar c χ s) by ring] at this
    have hrev : ‖rhoStar c χ s - rhoStar c χ (s + 2)‖ = ‖rhoStar c χ (s + 2) - rhoStar c χ s‖ :=
      norm_sub_rev _ _
    linarith
  have hc := h.c_pos
  have hε := h.hε
  have hcε : 64 / ε ^ 2 ≤ c := h.hc
  have hn := norm_pos_iff.mpr h.omega_ne
  have hn' := norm_pos_iff.mpr h'.omega_ne
  have hN2 := h.norm_s2_ge
  have hN4 : 9 / 2 ≤ ‖s + 4‖ := by
    have := Complex.re_le_norm (s + 4); simp at this; linarith [h.hre]
  by_cases hz4 : |s.im| < 4 / ε
  · -- low on the line: a, a' ≥ 19/20
    have hl := h.abs_im_tau_le_low hz4
    have hl' := h'.abs_im_tau_le_low (by rw [show (s + 2).im = s.im by simp]; exact hz4)
    have hA : (19 / 20) ≤ a := by
      have := Cvs.Prolate.Mellin.FrozenRootClosedBounds.re_csqrt_sq_ge (tau c χ s)
      have : (tau c χ s).im ^ 2 ≤ (31 / 100) ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hl 2
      nlinarith
    have hA' : (19 / 20) ≤ a' := by
      have := Cvs.Prolate.Mellin.FrozenRootClosedBounds.re_csqrt_sq_ge (tau c χ (s + 2))
      have : (tau c χ (s + 2)).im ^ 2 ≤ (31 / 100) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hl' 2
      nlinarith
    have hω : 15 / 8 ≤ ‖omega s‖ := by linarith [h.norm_omega_ge, h.norm_m_ge]
    have hω' : 31 / 8 ≤ ‖omega (s + 2)‖ := by
      have h1 := h'.norm_omega_ge
      have h2 : 4 ≤ ‖s + 2 + 3 / 2‖ := by
        have := Complex.re_le_norm (s + 2 + 3 / 2); simp at this; linarith [h.hre]
      linarith
    have hc64 : 64 ≤ c := h.c_ge
    have b1 : 1 / c ≤ 1 / 64 := by rw [div_le_div_iff₀ hc (by norm_num)]; linarith
    have b2 : 1 / (‖omega s‖ * ‖omega (s + 2)‖) ≤ 64 / 465 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    have t1 : ‖tau c χ (s + 2) - tau c χ s‖ ≤ 9 / 8 * (1 / 64 + 64 / 465) := ht.trans (by linarith)
    have t2 : ‖zeta c χ (s + 2) - zeta c χ s‖ ≤ 3 * (9 / 8 * (1 / 64 + 64 / 465)) / (19 / 10) :=
      hz.trans (div_le_div₀ (by norm_num) (by linarith) (by norm_num) (by linarith))
    have b3 : 1 / (‖s + 2‖ * ‖s + 4‖) ≤ 1 / (5 / 2 * (9 / 2)) := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    have b4 : 1 / ‖s + 4‖ ≤ 2 / 9 := by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    have b5 : 1 / ‖s + 2‖ ≤ 2 / 5 := by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    have t3 : ‖omega (s + 2) / (s + 2 + 2) - omega s / (s + 2)‖
        ≤ 1 / (5 / 2 * (9 / 2)) + 1 / 8 * (2 / 9 + 2 / 5) := hk.trans (by linarith)
    have : 17 / 12 * (3 * (9 / 8 * (1 / 64 + 64 / 465)) / (19 / 10))
        + 3 / 2 * (1 / (5 / 2 * (9 / 2)) + 1 / 8 * (2 / 9 + 2 / 5)) ≤ 3 / 4 * (19 / 20) := by norm_num
    nlinarith
  · -- high on the line: a, a' ≥ √ε/2
    push Not at hz4
    set r := Real.sqrt ε
    have hr : 0 < r := Real.sqrt_pos.mpr hε
    have hr2 : r ^ 2 = ε := Real.sq_sqrt hε.le
    have hr4 : r ≤ 1 / 2 := by
      rw [show (1 / 2 : ℝ) = Real.sqrt (1 / 4) by
        rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt hε4
    have hA : r / 2 ≤ a := by
      have := h.a_sq_ge
      nlinarith
    have hA' : r / 2 ≤ a' := by
      have := h'.a_sq_ge
      nlinarith
    have hm2 : |s.im| ≤ ‖s + 3 / 2‖ := by have := Complex.abs_im_le_norm (s + 3 / 2); simpa using this
    have hm2' : |s.im| ≤ ‖s + 2 + 3 / 2‖ := by
      have := Complex.abs_im_le_norm (s + 2 + 3 / 2); simpa using this
    have h31 : 31 / (8 * ε) ≤ 4 / ε - 1 / 8 := by
      rw [div_le_iff₀ (by positivity)]
      have : (4 / ε - 1 / 8) * (8 * ε) = 32 - ε := by field_simp; ring
      rw [this]; linarith
    have hω : 31 / (8 * ε) ≤ ‖omega s‖ := by linarith [h.norm_omega_ge]
    have hω' : 31 / (8 * ε) ≤ ‖omega (s + 2)‖ := by linarith [h'.norm_omega_ge]
    have hs2 : 4 / ε ≤ ‖s + 2‖ := by
      have := Complex.abs_im_le_norm (s + 2); simp at this; linarith
    have hs4 : 4 / ε ≤ ‖s + 4‖ := by
      have := Complex.abs_im_le_norm (s + 4); simp at this; linarith
    have i1 : 1 / c ≤ ε ^ 2 / 64 := by
      rw [div_le_div_iff₀ hc (by norm_num)]
      have := (div_le_iff₀ (by positivity : (0 : ℝ) < ε ^ 2)).mp hcε
      linarith
    have i2 : 1 / (‖omega s‖ * ‖omega (s + 2)‖) ≤ (8 * ε / 31) ^ 2 := by
      have h1 : (31 / (8 * ε)) ^ 2 ≤ ‖omega s‖ * ‖omega (s + 2)‖ := by
        rw [sq]; exact mul_le_mul hω hω' (by positivity) (by positivity)
      calc 1 / (‖omega s‖ * ‖omega (s + 2)‖) ≤ 1 / (31 / (8 * ε)) ^ 2 :=
            one_div_le_one_div_of_le (by positivity) h1
        _ = (8 * ε / 31) ^ 2 := by field_simp
    have i3 : 1 / (‖s + 2‖ * ‖s + 4‖) ≤ (ε / 4) ^ 2 := by
      have h1 : (4 / ε) ^ 2 ≤ ‖s + 2‖ * ‖s + 4‖ := by
        rw [sq]; exact mul_le_mul hs2 hs4 (by positivity) (by positivity)
      calc 1 / (‖s + 2‖ * ‖s + 4‖) ≤ 1 / (4 / ε) ^ 2 := one_div_le_one_div_of_le (by positivity) h1
        _ = (ε / 4) ^ 2 := by field_simp
    have i4 : 1 / ‖s + 4‖ ≤ ε / 4 := by
      rw [div_le_iff₀ (by positivity)]
      have := mul_le_mul_of_nonneg_left hs4 (by positivity : (0 : ℝ) ≤ ε / 4)
      have e : ε / 4 * (4 / ε) = 1 := by field_simp
      linarith
    have i5 : 1 / ‖s + 2‖ ≤ ε / 4 := by
      rw [div_le_iff₀ (by positivity)]
      have := mul_le_mul_of_nonneg_left hs2 (by positivity : (0 : ℝ) ≤ ε / 4)
      have e : ε / 4 * (4 / ε) = 1 := by field_simp
      linarith
    have t1 : ‖tau c χ (s + 2) - tau c χ s‖ ≤ 9 / 8 * (ε ^ 2 / 64 + (8 * ε / 31) ^ 2) :=
      ht.trans (by linarith)
    have t2 : ‖zeta c χ (s + 2) - zeta c χ s‖ ≤ 3 * (9 / 8 * (ε ^ 2 / 64 + (8 * ε / 31) ^ 2)) / r := by
      refine hz.trans ?_
      apply div_le_div₀ (by positivity) (by linarith) hr (by linarith)
    have t3 : ‖omega (s + 2) / (s + 2 + 2) - omega s / (s + 2)‖ ≤ (ε / 4) ^ 2 + 1 / 8 * (ε / 4 + ε / 4) :=
      hk.trans (by linarith)
    -- in terms of r: ε = r², r ≤ 1/2
    rw [← hr2] at t2 t3
    have e2 : 3 * (9 / 8 * ((r ^ 2) ^ 2 / 64 + (8 * r ^ 2 / 31) ^ 2)) / r
        = 27 / 8 * (1 / 64 + 64 / 961) * r ^ 3 := by field_simp; ring
    rw [e2] at t2
    have hr3 : r ^ 3 ≤ r / 4 := by nlinarith
    have hr4' : (r ^ 2 / 4) ^ 2 + 1 / 8 * (r ^ 2 / 4 + r ^ 2 / 4) ≤ r / 16 + r / 32 := by nlinarith
    nlinarith

end Cvs.Prolate.Mellin.FrozenRootStep
