import Mathlib
import Cvs.Prolate.Mellin.ForcingSmallBound
import Cvs.Prolate.Mellin.FrozenRootClosedBounds
import Cvs.Prolate.Mellin.FrozenRootCoreBound
import Cvs.Prolate.Mellin.FrozenRootDecayOffLine
import Cvs.Prolate.Mellin.FrozenRootErrorIdentity
import Cvs.Prolate.Mellin.FrozenRootSizeBounds
import Cvs.Prolate.Mellin.FrozenRootStep
import Cvs.Prolate.Mellin.HalfGapIncrements
import Cvs.Prolate.Mellin.StepAmplification
import Cvs.Prolate.Mellin.UniformRootBounds

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Damping in the near region

For `‖s‖ ≤ 4c + 2` on the region: `‖τ‖ ≤ 23/10`, `‖√(τ²+1)‖ ≤ 43/10`, and `R = Re(√(τ²+1) τ̄) ≤ 10`. Where
`‖ω‖² ≥ 2χ`, `R ≥ Re ω/(18c)` and `|ζ|² ≤ 1/(1 + 2R) ≤ exp(−Re ω/(189c))`. With the core weight `G` and the damping
weight `D = Re ω/(189c)` (on `‖ω‖² ≥ 2χ`, else `0`): `|ζ|² ≤ exp(G − D)`.
-/

noncomputable section

open Complex

namespace Cvs.Prolate.Mellin.NearRegionDamping

open Cvs.Prolate.Mellin.FrozenRootErrorIdentity (csqrt csqrt_sq re_csqrt_nonneg omega tau zeta rhoStar)
open Cvs.Prolate.Mellin.FrozenRootClosedBounds (Rq)
open Cvs.Prolate.Mellin.UniformRootBounds (Hyp)
open Cvs.Prolate.Mellin.StepAmplification (Gw)

variable {ε c χ : ℝ} {s : ℂ}

/-- `‖τ‖ ≤ 23/10` for `‖s‖ ≤ 4c + 2`. -/
theorem Hyp.norm_tau_le_near (h : Hyp ε c χ s) (hs : ‖s‖ ≤ 4 * c + 2) : ‖tau c χ s‖ ≤ 23 / 10 := by
  have hc := h.c_pos
  have hc64 := h.c_ge
  have hω := h.omega_ne
  have hω0 : 0 < ‖omega s‖ := norm_pos_iff.mpr hω
  have hωg : 15 / 8 ≤ ‖omega s‖ := by linarith [h.norm_omega_ge, h.norm_m_ge]
  have hωl := Cvs.Prolate.Mellin.FrozenRootSizeBounds.Hyp.norm_omega_le h
  have hm : ‖s + 3 / 2‖ ≤ ‖s‖ + 3 / 2 := by
    have := norm_add_le s (3 / 2 : ℂ); norm_num at this ⊢; linarith
  have hχ0 : 0 ≤ χ := by linarith [h.hχ0]
  unfold tau
  rw [norm_div, show ‖(2 * (c : ℂ))‖ = 2 * c by
    rw [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc], div_le_iff₀ (by positivity)]
  have h1 : ‖omega s - (χ : ℂ) / omega s‖ ≤ ‖omega s‖ + χ / ‖omega s‖ := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hχ0]
  have h2 : χ / ‖omega s‖ ≤ 8 * c / 15 := by
    rw [div_le_div_iff₀ hω0 (by norm_num)]; nlinarith [h.hχ1]
  nlinarith

/-- `‖√(τ²+1)‖ ≤ 43/10` for `‖s‖ ≤ 4c + 2`. -/
theorem Hyp.norm_csqrt_le_near (h : Hyp ε c χ s) (hs : ‖s‖ ≤ 4 * c + 2) :
    ‖csqrt (tau c χ s ^ 2 + 1)‖ ≤ 43 / 10 := by
  have ht := Hyp.norm_tau_le_near h hs
  have hsq := csqrt_sq (tau c χ s ^ 2 + 1)
  have h1 : ‖csqrt (tau c χ s ^ 2 + 1)‖ ^ 2 ≤ (43 / 10) ^ 2 := by
    rw [← norm_pow, hsq]
    have := norm_add_le (tau c χ s ^ 2) 1
    rw [norm_pow, norm_one] at this
    nlinarith [norm_nonneg (tau c χ s)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by norm_num) two_ne_zero).mp h1

/-- `R ≤ 10` for `‖s‖ ≤ 4c + 2`. -/
theorem Hyp.Rq_le_near (h : Hyp ε c χ s) (hs : ‖s‖ ≤ 4 * c + 2) : Rq (tau c χ s) ≤ 10 := by
  have h1 := Hyp.norm_tau_le_near h hs
  have h2 := Hyp.norm_csqrt_le_near h hs
  have : Rq (tau c χ s) = (csqrt (tau c χ s ^ 2 + 1) * (starRingEnd ℂ) (tau c χ s)).re := by
    unfold Rq; simp [Complex.mul_re]
  rw [this]
  calc (csqrt (tau c χ s ^ 2 + 1) * (starRingEnd ℂ) (tau c χ s)).re
      ≤ ‖csqrt (tau c χ s ^ 2 + 1) * (starRingEnd ℂ) (tau c χ s)‖ := Complex.re_le_norm _
    _ = ‖csqrt (tau c χ s ^ 2 + 1)‖ * ‖tau c χ s‖ := by rw [norm_mul, Complex.norm_conj]
    _ ≤ 43 / 10 * (23 / 10) := mul_le_mul h2 h1 (norm_nonneg _) (by norm_num)
    _ ≤ 10 := by norm_num

/-- **Damping**: where `‖ω‖² ≥ 2χ` (and `‖s‖ ≤ 4c + 2`), `|ζ|² ≤ exp(−Re ω/(189c))`. -/
theorem Hyp.normSq_zeta_le_damp (h : Hyp ε c χ s) (hs : ‖s‖ ≤ 4 * c + 2) (hfar : 2 * χ ≤ ‖omega s‖ ^ 2) :
    ‖zeta c χ s‖ ^ 2 ≤ Real.exp (-((omega s).re / (189 * c))) := by
  have hc := h.c_pos
  have hτ := Cvs.Prolate.Mellin.FrozenRootDecayOffLine.Hyp.re_tau_ge_far h hfar
  have hre := Cvs.Prolate.Mellin.FrozenRootCoreBound.Hyp.re_omega_ge h
  have hreω : 0 < (omega s).re := by linarith [h.hre]
  have hτ0 : 0 ≤ (tau c χ s).re := le_trans (by positivity) hτ
  have ht : (tau c χ s).im ^ 2 < 1 := Cvs.Prolate.Mellin.HalfGapIncrements.Hyp.im_tau_sq_lt h
  have hRlo := Cvs.Prolate.Mellin.FrozenRootClosedBounds.Rq_ge_of_nonneg ht hτ0
  have hsq := Hyp.norm_csqrt_le_near h hs
  have ha := Cvs.Prolate.Mellin.FrozenRootClosedBounds.re_csqrt_pos ht
  have hn0 : 0 < ‖csqrt (tau c χ s ^ 2 + 1)‖ := lt_of_lt_of_le ha (Complex.re_le_norm _)
  set R := Rq (tau c χ s)
  have hR : (omega s).re / (18 * c) ≤ R := by
    refine le_trans ?_ hRlo
    rw [div_le_div_iff₀ (by positivity) hn0]
    have := mul_le_mul_of_nonneg_left hτ (by positivity : (0 : ℝ) ≤ 18 * c)
    have e : 18 * c * ((omega s).re / (4 * c)) = 9 / 2 * (omega s).re := by field_simp; ring
    nlinarith
  have hRu := Hyp.Rq_le_near h hs
  have hR0 : 0 ≤ R := le_trans (by positivity) hR
  rw [← Complex.normSq_eq_norm_sq, Cvs.Prolate.Mellin.FrozenRootErrorIdentity.normSq_zeta_eq]
  change Real.sqrt (4 * R ^ 2 + 1) - 2 * R ≤ _
  have hs1 : 1 ≤ Real.sqrt (4 * R ^ 2 + 1) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]; nlinarith
  have hs2 : Real.sqrt (4 * R ^ 2 + 1) ^ 2 = 4 * R ^ 2 + 1 := Real.sq_sqrt (by positivity)
  -- √ − 2R = 1/(√ + 2R) ≤ 1/(1 + 2R)
  have hp : (Real.sqrt (4 * R ^ 2 + 1) - 2 * R) * (Real.sqrt (4 * R ^ 2 + 1) + 2 * R) = 1 := by nlinarith
  have hle : Real.sqrt (4 * R ^ 2 + 1) - 2 * R ≤ 1 / (1 + 2 * R) := by
    rw [le_div_iff₀ (by positivity)]
    have hpos : 0 ≤ Real.sqrt (4 * R ^ 2 + 1) - 2 * R := by
      by_contra hn; push Not at hn; nlinarith
    nlinarith
  refine hle.trans ?_
  -- 1/(1+2R) ≤ exp(−2R/21) ≤ exp(−Re ω/(189c))
  have hlog : 2 * R / 21 ≤ Real.log (1 + 2 * R) := by
    have := Real.one_sub_inv_le_log_of_pos (show 0 < 1 + 2 * R by positivity)
    have e : 1 - (1 + 2 * R)⁻¹ = 2 * R / (1 + 2 * R) := by field_simp; ring
    rw [e] at this
    have : 2 * R / 21 ≤ 2 * R / (1 + 2 * R) := div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
    linarith
  have e : 1 / (1 + 2 * R) = Real.exp (-Real.log (1 + 2 * R)) := by
    rw [Real.exp_neg, Real.exp_log (by positivity), one_div]
  rw [e]
  apply Real.exp_le_exp.mpr
  have : (omega s).re / (189 * c) ≤ 2 * R / 21 := by
    have e2 : (omega s).re / (189 * c) = 2 * ((omega s).re / (18 * c)) / 21 := by field_simp; ring
    rw [e2]; linarith
  linarith

/-- The damping weight `D(s) = Re ω/(189c)` where `‖ω‖² ≥ 2χ`, else `0`. -/
def Dw (c χ : ℝ) (s : ℂ) : ℝ := if 2 * χ ≤ ‖omega s‖ ^ 2 then (omega s).re / (189 * c) else 0

/-- **`|ζ|² ≤ exp(G − D)`** for `‖s‖ ≤ 4c + 2`. -/
theorem Hyp.normSq_zeta_le_GD (h : Hyp ε c χ s) (hs : ‖s‖ ≤ 4 * c + 2) :
    ‖zeta c χ s‖ ^ 2 ≤ Real.exp (Gw c s - Dw c χ s) := by
  unfold Dw
  split_ifs with hfar
  · refine (Hyp.normSq_zeta_le_damp h hs hfar).trans (Real.exp_le_exp.mpr ?_)
    have := Cvs.Prolate.Mellin.StepAmplification.Gw_nonneg h; linarith
  · rw [sub_zero]; exact Cvs.Prolate.Mellin.StepAmplification.normSq_zeta_le_exp_Gw h

open Cvs.Prolate.Mellin.ForcingSmallBound (Af) in
theorem norm_Af_le_of {s₀ : ℂ} (h : Hyp ε c χ s₀) {g₀ g₁ : ℝ} (hz : ‖zeta c χ s₀‖ ^ 2 ≤ Real.exp g₀)
    (hz' : ‖zeta c χ (s₀ + 2)‖ ^ 2 ≤ Real.exp g₁) :
    ‖Af c χ s₀‖ ≤ Real.exp (1 / ((s₀.re + 1) * (s₀.re + 4)) + g₀ / 2 + g₁ / 2) := by
  have h' := Cvs.Prolate.Mellin.FrozenRootStep.Hyp.add_two h
  have hx := h.hre
  have hs1 := Cvs.Prolate.Mellin.ForcingSmallBound.Hyp.s1_ne h
  have hs4 : s₀ + 4 ≠ 0 := by
    intro h0; have := congrArg Complex.re h0; simp at this; linarith
  have hsq := Cvs.Prolate.Mellin.FrozenRootErrorIdentity.norm_A_sq (c := c) (χ := χ) h.m_ne h'.m_ne hs1 h.s2_ne hs4
  -- the rational factor
  have hr : ‖(s₀ + 2) * (s₀ + 3)‖ / ‖(s₀ + 1) * (s₀ + 4)‖ ≤ Real.exp (2 / ((s₀.re + 1) * (s₀.re + 4))) := by
    have hpos : 0 < ‖(s₀ + 1) * (s₀ + 4)‖ := norm_pos_iff.mpr (mul_ne_zero hs1 hs4)
    have hlow : (s₀.re + 1) * (s₀.re + 4) ≤ ‖(s₀ + 1) * (s₀ + 4)‖ := by
      rw [norm_mul]
      have a1 := Complex.re_le_norm (s₀ + 1); have a4 := Complex.re_le_norm (s₀ + 4)
      simp at a1 a4
      exact mul_le_mul a1 a4 (by linarith) (norm_nonneg _)
    have e : (s₀ + 2) * (s₀ + 3) = (s₀ + 1) * (s₀ + 4) + 2 := by ring
    rw [e, div_le_iff₀ hpos]
    set P := ‖(s₀ + 1) * (s₀ + 4)‖
    set D := (s₀.re + 1) * (s₀.re + 4)
    have hD : 0 < D := by positivity
    have t1 : ‖(s₀ + 1) * (s₀ + 4) + 2‖ ≤ P + 2 := by
      have := norm_add_le ((s₀ + 1) * (s₀ + 4)) (2 : ℂ)
      rw [Complex.norm_ofNat] at this; exact this
    have t2 : 1 + 2 / D ≤ Real.exp (2 / D) := by
      have := Real.add_one_le_exp (2 / D); linarith
    have t3 : P + 2 ≤ (1 + 2 / D) * P := by
      have : 2 ≤ 2 / D * P := by rw [div_mul_eq_mul_div, le_div_iff₀ hD]; nlinarith
      linarith [show (1 + 2 / D) * P = P + 2 / D * P by ring]
    nlinarith [Real.exp_pos (2 / D)]
  -- combine squares
  have hA2 : ‖Af c χ s₀‖ ^ 2 ≤ Real.exp (1 / ((s₀.re + 1) * (s₀.re + 4)) + g₀ / 2 + g₁ / 2) ^ 2 := by
    unfold Af
    rw [hsq, ← Real.exp_nat_mul]
    have e : ((2 : ℕ) : ℝ) * (1 / ((s₀.re + 1) * (s₀.re + 4)) + g₀ / 2 + g₁ / 2)
        = 2 / ((s₀.re + 1) * (s₀.re + 4)) + g₀ + g₁ := by push_cast; ring
    rw [e, Real.exp_add, Real.exp_add]
    have := mul_le_mul hz hz' (sq_nonneg _) (Real.exp_pos _).le
    calc ‖(s₀ + 2) * (s₀ + 3)‖ / ‖(s₀ + 1) * (s₀ + 4)‖ * (‖zeta c χ s₀‖ ^ 2 * ‖zeta c χ (s₀ + 2)‖ ^ 2)
        ≤ Real.exp (2 / ((s₀.re + 1) * (s₀.re + 4))) * (Real.exp (g₀) * Real.exp (g₁)) :=
          mul_le_mul hr this (by positivity) (Real.exp_pos _).le
      _ = _ := by ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (Real.exp_pos _).le two_ne_zero).mp hA2

end Cvs.Prolate.Mellin.NearRegionDamping
