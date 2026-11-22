import Mathlib
import Cvs.Prolate.Mellin.CompanionRootGap
import Cvs.Prolate.Mellin.ForcingSmallBound
import Cvs.Prolate.Mellin.FrozenRootClosedBounds
import Cvs.Prolate.Mellin.FrozenRootCoreBound
import Cvs.Prolate.Mellin.FrozenRootDecayOffLine
import Cvs.Prolate.Mellin.FrozenRootErrorIdentity
import Cvs.Prolate.Mellin.FrozenRootFirstDifference
import Cvs.Prolate.Mellin.FrozenRootStep
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
# The far region `Re s ≥ 2c`: damping and decay

For `Re s = x ≥ 2c` on the region with `ε ≤ 1/4`: `Re τ ≥ 1/2`, `a ≥ x/(4c)`, `R ≥ 1/4` so `|ζ|² ≤ 2/3`, hence
`|A| ≤ 3/4`; and `|B| ≤ 1000c²/x³`.
-/

noncomputable section

open Complex

namespace Cvs.Prolate.Mellin.FarRegionDamping

open Cvs.Prolate.Mellin.FrozenRootErrorIdentity (csqrt re_csqrt_nonneg omega tau zeta rhoStar)
open Cvs.Prolate.Mellin.FrozenRootClosedBounds (Rq)
open Cvs.Prolate.Mellin.StepQuadraticRoots (comp)
open Cvs.Prolate.Mellin.UniformRootBounds (Hyp)
open Cvs.Prolate.Mellin.ForcingSmallBound (Af Bf)

variable {ε c χ : ℝ} {s : ℂ}

theorem Hyp.far_omega (h : Hyp ε c χ s) (hx : 2 * c ≤ s.re) : 2 * χ ≤ ‖omega s‖ ^ 2 := by
  have hre := Cvs.Prolate.Mellin.FrozenRootCoreBound.Hyp.re_omega_ge h
  have h1 : (omega s).re ≤ ‖omega s‖ := Complex.re_le_norm _
  have hc := h.c_ge
  have : 2 * c ≤ ‖omega s‖ := by linarith
  nlinarith [h.hχ1]

theorem Hyp.far_re_tau (h : Hyp ε c χ s) (hx : 2 * c ≤ s.re) : s.re / (4 * c) ≤ (tau c χ s).re := by
  have hc := h.c_pos
  have h1 := Cvs.Prolate.Mellin.FrozenRootDecayOffLine.Hyp.re_tau_ge_far h (Hyp.far_omega h hx)
  have hre := Cvs.Prolate.Mellin.FrozenRootCoreBound.Hyp.re_omega_ge h
  refine le_trans ?_ h1
  exact div_le_div_of_nonneg_right (by linarith) (by positivity)

theorem Hyp.far_a_ge (h : Hyp ε c χ s) (hx : 2 * c ≤ s.re) :
    s.re / (4 * c) ≤ (csqrt (tau c χ s ^ 2 + 1)).re := by
  have h1 := Hyp.far_re_tau h hx
  have ha := Cvs.Prolate.Mellin.CompanionRootGap.abs_re_le_re_csqrt (t := tau c χ s) (by
    have := h.abs_im_tau_le; have := h.hε
    nlinarith [abs_nonneg (tau c χ s).im, sq_abs (tau c χ s).im])
  have := le_abs_self (tau c χ s).re
  linarith

theorem Hyp.far_normSq_zeta (h : Hyp ε c χ s) (hx : 2 * c ≤ s.re) : ‖zeta c χ s‖ ^ 2 ≤ 2 / 3 := by
  have hc := h.c_pos
  have h1 := Hyp.far_re_tau h hx
  have hτ : 1 / 2 ≤ (tau c χ s).re := by
    refine le_trans ?_ h1; rw [le_div_iff₀ (by positivity)]; linarith
  have ht : (tau c χ s).im ^ 2 < 1 := by
    have := h.abs_im_tau_le; have := h.hε
    have h1 : |(tau c χ s).im| < 1 := by linarith
    nlinarith [abs_nonneg (tau c χ s).im, sq_abs (tau c χ s).im]
  have ha := Cvs.Prolate.Mellin.FrozenRootClosedBounds.re_csqrt_pos ht
  have hax := Cvs.Prolate.Mellin.CompanionRootGap.abs_re_le_re_csqrt ht.le
  rw [abs_of_pos (by linarith)] at hax
  have hR : 1 / 4 ≤ Rq (tau c χ s) := by
    rw [Cvs.Prolate.Mellin.FrozenRootClosedBounds.Rq_eq ht, le_div_iff₀ ha]
    nlinarith [sq_nonneg (tau c χ s).im]
  rw [← Complex.normSq_eq_norm_sq, Cvs.Prolate.Mellin.FrozenRootErrorIdentity.normSq_zeta_eq]
  set R := Rq (tau c χ s)
  change Real.sqrt (4 * R ^ 2 + 1) - 2 * R ≤ 2 / 3
  have hs : 0 ≤ Real.sqrt (4 * R ^ 2 + 1) := Real.sqrt_nonneg _
  have hs2 : Real.sqrt (4 * R ^ 2 + 1) ^ 2 = 4 * R ^ 2 + 1 := Real.sq_sqrt (by positivity)
  have hs1 : 1 ≤ Real.sqrt (4 * R ^ 2 + 1) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]; nlinarith
  -- (√ − 2R)(√ + 2R) = 1 and √ + 2R ≥ 3/2
  have hp : (Real.sqrt (4 * R ^ 2 + 1) - 2 * R) * (Real.sqrt (4 * R ^ 2 + 1) + 2 * R) = 1 := by nlinarith
  nlinarith

/-- **Damping in the far region**: `|A| ≤ 3/4`. -/
theorem Hyp.far_norm_Af_le (h : Hyp ε c χ s) (hx : 2 * c ≤ s.re) : ‖Af c χ s‖ ≤ 3 / 4 := by
  have h' := Cvs.Prolate.Mellin.FrozenRootStep.Hyp.add_two h
  have hx' : 2 * c ≤ (s + 2).re := by simp; linarith
  have hs1 := Cvs.Prolate.Mellin.ForcingSmallBound.Hyp.s1_ne h
  have hs4 : s + 4 ≠ 0 := by intro h0; have := congrArg Complex.re h0; simp at this; linarith [h.hre]
  have hsq := Cvs.Prolate.Mellin.FrozenRootErrorIdentity.norm_A_sq (c := c) (χ := χ) h.m_ne h'.m_ne hs1 h.s2_ne hs4
  have z0 := Hyp.far_normSq_zeta h hx
  have z1 := Hyp.far_normSq_zeta h' hx'
  have hr : ‖(s + 2) * (s + 3)‖ / ‖(s + 1) * (s + 4)‖ ≤ 1 + 1 / 100 := by
    have hpos : 0 < ‖(s + 1) * (s + 4)‖ := norm_pos_iff.mpr (mul_ne_zero hs1 hs4)
    rw [div_le_iff₀ hpos]
    have e : (s + 2) * (s + 3) = (s + 1) * (s + 4) + 2 := by ring
    rw [e]
    have t1 : ‖(s + 1) * (s + 4) + 2‖ ≤ ‖(s + 1) * (s + 4)‖ + 2 := by
      have := norm_add_le ((s + 1) * (s + 4)) (2 : ℂ); rw [Complex.norm_ofNat] at this; exact this
    have hlow : (s.re + 1) * (s.re + 4) ≤ ‖(s + 1) * (s + 4)‖ := by
      rw [norm_mul]
      have a1 := Complex.re_le_norm (s + 1); have a4 := Complex.re_le_norm (s + 4)
      simp at a1 a4
      exact mul_le_mul a1 a4 (by linarith [h.hre]) (norm_nonneg _)
    have hc := h.c_ge
    nlinarith
  have : ‖Af c χ s‖ ^ 2 ≤ (3 / 4) ^ 2 := by
    unfold Af; rw [hsq]
    calc _ ≤ (1 + 1 / 100) * (2 / 3 * (2 / 3)) :=
          mul_le_mul hr (mul_le_mul z0 z1 (sq_nonneg _) (by norm_num)) (by positivity) (by norm_num)
      _ ≤ (3 / 4) ^ 2 := by norm_num
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by norm_num) two_ne_zero).mp this

/-- **Decay of the forcing in the far region**: `|B| ≤ 1000c²/x³`. -/
theorem Hyp.far_norm_Bf_le (h : Hyp ε c χ s) (hε4 : ε ≤ 1 / 4) (hx : 2 * c ≤ s.re) :
    ‖Bf c χ s‖ ≤ 1000 * c ^ 2 / s.re ^ 3 := by
  have h' := Cvs.Prolate.Mellin.FrozenRootStep.Hyp.add_two h
  have hc := h.c_pos
  have hc64 := h.c_ge
  have hx' : 2 * c ≤ (s + 2).re := by simp; linarith
  set x := s.re
  have hx0 : 0 < x := by linarith
  have ha := Hyp.far_a_ge h hx
  have hgap : 3 / 4 * (csqrt (tau c χ s ^ 2 + 1)).re ≤ ‖rhoStar c χ (s + 2) - comp s (rhoStar c χ s)‖ :=
    Cvs.Prolate.Mellin.FrozenRootStep.shifted_gap_ge h hε4
  have hρ := Cvs.Prolate.Mellin.FrozenRootDecayOffLine.Hyp.norm_rho_le_far h (Hyp.far_omega h hx)
  have hρ' := Cvs.Prolate.Mellin.FrozenRootDecayOffLine.Hyp.norm_rho_le_far h' (Hyp.far_omega h' hx')
  have hre2 : (s + 2).re = x + 2 := by simp [x]
  rw [hre2] at hρ'
  have hρ'2 : ‖rhoStar c χ (s + 2)‖ ≤ 2 := by
    refine hρ'.trans ?_; rw [div_le_iff₀ (by linarith)]; linarith
  have hsx : ‖s‖ ≤ 2 * x := by
    have hn := Complex.norm_le_abs_re_add_abs_im s
    have him := h.him; have hε := h.hε
    rw [abs_of_pos hx0] at hn
    have : |s.im| ≤ 2 * c := by nlinarith
    linarith
  -- |Q| ≤ 42
  have hQ : ‖2 * (1 - rhoStar c χ (s + 2) ^ 2) - (4 * s + 10) / c * rhoStar c χ (s + 2)‖ ≤ 42 := by
    refine (norm_sub_le _ _).trans ?_
    have q1 : ‖2 * (1 - rhoStar c χ (s + 2) ^ 2)‖ ≤ 10 := by
      rw [norm_mul, Complex.norm_ofNat]
      have := norm_sub_le (1 : ℂ) (rhoStar c χ (s + 2) ^ 2)
      rw [norm_one, norm_pow] at this
      nlinarith [norm_nonneg (rhoStar c χ (s + 2))]
    have q2 : ‖(4 * s + 10) / (c : ℂ) * rhoStar c χ (s + 2)‖ ≤ 32 := by
      rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
      have h4 : ‖4 * s + 10‖ ≤ 8 * x + 10 := by
        have := norm_add_le (4 * s) (10 : ℂ); rw [norm_mul] at this; norm_num at this; linarith
      calc ‖4 * s + 10‖ / c * ‖rhoStar c χ (s + 2)‖ ≤ (8 * x + 10) / c * (4 * c / (x + 2 + 3 / 2)) :=
            mul_le_mul (div_le_div_of_nonneg_right h4 hc.le) hρ' (norm_nonneg _) (by positivity)
        _ ≤ 32 := by
            rw [div_mul_div_comm, div_le_iff₀ (by positivity)]; nlinarith
    linarith
  -- |Δρ| ≤ 224 c/x²
  have hN2 : x ≤ ‖s + 2‖ := by have := Complex.re_le_norm (s + 2); simp at this; linarith
  have hstep : ‖rhoStar c χ (s + 2) - rhoStar c χ s‖ ≤ 224 * c / x ^ 2 := by
    rw [Cvs.Prolate.Mellin.FrozenRootFirstDifference.Hyp.rho_step_eq h hε4, norm_div, norm_mul]
    have hden : x * (3 / 4 * (x / (4 * c))) ≤ ‖s + 2‖ * ‖rhoStar c χ (s + 2) - comp s (rhoStar c χ s)‖ :=
      mul_le_mul hN2 (le_trans (by nlinarith) hgap) (by positivity) (norm_nonneg _)
    calc _ ≤ 42 / (x * (3 / 4 * (x / (4 * c)))) := div_le_div₀ (by norm_num) hQ (by positivity) hden
      _ = 224 * c / x ^ 2 := by field_simp; ring
  -- |B| = |s+2|/|s+1| |ρ| |Δρ|
  have hs21 : ‖s + 2‖ / ‖s + 1‖ ≤ 11 / 10 := by
    have hn1 : x + 1 ≤ ‖s + 1‖ := by have := Complex.re_le_norm (s + 1); simp at this; linarith
    rw [div_le_iff₀ (by linarith)]
    have t : ‖s + 2‖ ≤ ‖s + 1‖ + 1 := by
      have := norm_add_le (s + 1) (1 : ℂ); rwa [show s + 1 + 1 = s + 2 by ring, norm_one] at this
    linarith
  unfold Bf
  rw [norm_div, norm_mul, norm_mul]
  have hs10 : 0 < ‖s + 1‖ := by
    have := Complex.re_le_norm (s + 1); simp at this; linarith
  calc ‖s + 2‖ * ‖rhoStar c χ s‖ * ‖rhoStar c χ (s + 2) - rhoStar c χ s‖ / ‖s + 1‖
      = ‖s + 2‖ / ‖s + 1‖ * ‖rhoStar c χ s‖ * ‖rhoStar c χ (s + 2) - rhoStar c χ s‖ := by ring
    _ ≤ 11 / 10 * (4 * c / (x + 3 / 2)) * (224 * c / x ^ 2) := by gcongr
    _ ≤ 11 / 10 * (4 * c / x) * (224 * c / x ^ 2) := by
        gcongr
        linarith
    _ = 9856 / 10 * (c ^ 2 / x ^ 3) := by field_simp; ring
    _ ≤ 1000 * c ^ 2 / x ^ 3 := by
        rw [mul_div_assoc]
        exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)

end Cvs.Prolate.Mellin.FarRegionDamping
