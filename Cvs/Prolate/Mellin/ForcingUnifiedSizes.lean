import Mathlib
import Cvs.Prolate.Mellin.CompanionRootGap
import Cvs.Prolate.Mellin.FarRegionDamping
import Cvs.Prolate.Mellin.ForcingSmallBound
import Cvs.Prolate.Mellin.FrozenForcingIdentities
import Cvs.Prolate.Mellin.FrozenRootErrorIdentity
import Cvs.Prolate.Mellin.FrozenRootFirstDifference
import Cvs.Prolate.Mellin.FrozenRootSizeBounds
import Cvs.Prolate.Mellin.FrozenRootStep
import Cvs.Prolate.Mellin.NearRegionBetaStep
import Cvs.Prolate.Mellin.PropagationFactorSizes
import Cvs.Prolate.Mellin.UniformRootBounds

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Unified sizes of the forcing on the region

With `x = Re s`, `a = Re √(τ² + 1)`: `c·a ≥ √ε(x + 2c)/8`; hence `‖B‖ ≤ 904/(√ε(x+2c))`,
`‖ρ*(s+2) − ρ*(s)‖ ≤ 400/(√ε(x+2c))`, `‖β‖ ≤ 10848/(ε(x+2c))`; `‖p‖ ≥ √ε/24` once `‖β‖ ≤ 1/2`; `‖r‖ ≤ 5/3`,
`‖1 + r‖ ≥ 2`; and `‖ρ*(s+2)² − 1‖ ≤ 13(‖s + 3‖ + 1)/(4c)`.
-/

noncomputable section

namespace Cvs.Prolate.Mellin.ForcingUnifiedSizes

open Cvs.Prolate.Mellin.FrozenRootErrorIdentity Cvs.Prolate.Mellin.UniformRootBounds Cvs.Prolate.Mellin.ForcingSmallBound Cvs.Prolate.Mellin.NearRegionBetaStep Cvs.Prolate.Mellin.FrozenForcingIdentities

variable {ε c χ : ℝ} {s : ℂ}

theorem Hyp.ca_ge (h : Hyp ε c χ s) :
    Real.sqrt ε * (s.re + 2 * c) / 8 ≤ c * (csqrt (tau c χ s ^ 2 + 1)).re := by
  have hc := h.c_pos
  have hx := h.hre
  have hs1 : Real.sqrt ε ≤ 1 := Real.sqrt_le_one.mpr h.hε1
  have hs0 : 0 ≤ Real.sqrt ε := Real.sqrt_nonneg _
  by_cases hfar : 2 * c ≤ s.re
  · have h1 := Cvs.Prolate.Mellin.FarRegionDamping.Hyp.far_re_tau h hfar
    have h2 : |(tau c χ s).re| ≤ (csqrt (tau c χ s ^ 2 + 1)).re := by
      apply Cvs.Prolate.Mellin.CompanionRootGap.abs_re_le_re_csqrt
      have := Hyp.abs_im_tau_le h; have := h.hε
      nlinarith [abs_nonneg (tau c χ s).im, sq_abs (tau c χ s).im]
    have h3 : s.re / (4 * c) ≤ (csqrt (tau c χ s ^ 2 + 1)).re := h1.trans ((le_abs_self _).trans h2)
    have h4 : s.re / 4 ≤ c * (csqrt (tau c χ s ^ 2 + 1)).re := by
      have := mul_le_mul_of_nonneg_left h3 hc.le
      rwa [show c * (s.re / (4 * c)) = s.re / 4 by field_simp] at this
    have : Real.sqrt ε * (s.re + 2 * c) / 8 ≤ (s.re + 2 * c) / 8 := by
      have : 0 ≤ s.re + 2 * c := by linarith
      nlinarith
    linarith
  · push_neg at hfar
    have ha := Cvs.Prolate.Mellin.PropagationFactorSizes.Hyp.sqrt_eps_le_a h
    have := mul_le_mul_of_nonneg_left ha hc.le
    nlinarith

theorem Hyp.norm_Bf_le' (h : Hyp ε c χ s) (hε4 : ε ≤ 1 / 4) :
    ‖Bf c χ s‖ ≤ 904 / (Real.sqrt ε * (s.re + 2 * c)) := by
  have hB := Hyp.norm_Bf_le h hε4
  have hca := Hyp.ca_ge h
  have hs : 0 < Real.sqrt ε := Real.sqrt_pos.mpr h.hε
  have hx : 0 < s.re + 2 * c := by linarith [h.hre, h.c_pos]
  refine hB.trans ?_
  rw [div_le_div_iff₀ (by have := Cvs.Prolate.Mellin.FrozenRootFirstDifference.Hyp.a_pos h; have := h.c_pos; positivity) (by positivity)]
  nlinarith

theorem Hyp.norm_drho_le (h : Hyp ε c χ s) (hε4 : ε ≤ 1 / 4) :
    ‖rhoStar c χ (s + 2) - rhoStar c χ s‖ ≤ 400 / (Real.sqrt ε * (s.re + 2 * c)) := by
  have hB := Cvs.Prolate.Mellin.FrozenRootFirstDifference.Hyp.norm_rho_step_le h hε4
  have hca := Hyp.ca_ge h
  have hs : 0 < Real.sqrt ε := Real.sqrt_pos.mpr h.hε
  have hx : 0 < s.re + 2 * c := by linarith [h.hre, h.c_pos]
  refine hB.trans ?_
  rw [div_le_div_iff₀ (by have := Cvs.Prolate.Mellin.FrozenRootFirstDifference.Hyp.a_pos h; have := h.c_pos; positivity) (by positivity)]
  nlinarith

theorem Hyp.norm_betaf_le' (h : Hyp ε c χ s) (hε4 : ε ≤ 1 / 4) :
    ‖betaf c χ s‖ ≤ 10848 / (ε * (s.re + 2 * c)) := by
  have hB := Hyp.norm_Bf_le' h hε4
  have hA := Cvs.Prolate.Mellin.PropagationFactorSizes.Hyp.norm_one_add_Af_ge' h hε4
  have hs : 0 < Real.sqrt ε := Real.sqrt_pos.mpr h.hε
  have hsq : Real.sqrt ε ^ 2 = ε := Real.sq_sqrt h.hε.le
  have hx : 0 < s.re + 2 * c := by linarith [h.hre, h.c_pos]
  unfold betaf
  rw [norm_div, div_le_iff₀ (by linarith)]
  calc ‖Bf c χ s‖ ≤ 904 / (Real.sqrt ε * (s.re + 2 * c)) := hB
    _ = 10848 / (ε * (s.re + 2 * c)) * (Real.sqrt ε / 12) := by
        have hε0 : ε ≠ 0 := h.hε.ne'
        field_simp
        rw [hsq]; ring
    _ ≤ 10848 / (ε * (s.re + 2 * c)) * ‖1 + Af c χ s‖ := by
        gcongr; have := h.hε; positivity

theorem Hyp.norm_pp_ge (h : Hyp ε c χ s) (hε4 : ε ≤ 1 / 4) (hβ : ‖betaf c χ s‖ ≤ 1 / 2) :
    Real.sqrt ε / 24 ≤ ‖pp c χ s‖ := by
  have hA := Cvs.Prolate.Mellin.PropagationFactorSizes.Hyp.norm_one_add_Af_ge' h hε4
  have hne : 1 + Af c χ s ≠ 0 := fun h0 => by
    rw [h0, norm_zero] at hA; have := Real.sqrt_pos.mpr h.hε; linarith
  rw [← one_sub_betaf_mul hne, norm_mul]
  have : 1 / 2 ≤ ‖1 - betaf c χ s‖ := by
    have := norm_sub_norm_le (1 : ℂ) (betaf c χ s); rw [norm_one] at this; linarith
  have hs := Real.sqrt_nonneg ε
  nlinarith

theorem Hyp.norm_rr_le (h : Hyp ε c χ s) : ‖rr s‖ ≤ 5 / 3 := by
  have hs1 := Hyp.norm_s1_ge h
  unfold rr
  rw [norm_div, div_le_iff₀ (by linarith)]
  have := norm_add_le (s + 1) 1
  rw [show s + 1 + 1 = s + 2 by ring, norm_one] at this; linarith

theorem Hyp.re_rr_ge (h : Hyp ε c χ s) : 1 ≤ (rr s).re := by
  have hs1 := Hyp.s1_ne h
  have e : rr s = 1 + 1 / (s + 1) := by unfold rr; field_simp; ring
  rw [e, Complex.add_re, Complex.one_re]
  have : 0 ≤ (1 / (s + 1)).re := by
    rw [one_div, Complex.inv_re]
    apply div_nonneg _ (Complex.normSq_nonneg _)
    simp; linarith [h.hre]
  linarith

theorem Hyp.norm_one_add_rr_ge (h : Hyp ε c χ s) : 2 ≤ ‖1 + rr s‖ := by
  have := Hyp.re_rr_ge h
  have h1 := Complex.re_le_norm (1 + rr s)
  simp at h1; linarith

theorem Hyp.norm_rho_sq_sub_one_le (h : Hyp ε c χ s) :
    ‖rhoStar c χ (s + 2) ^ 2 - 1‖ ≤ 13 * (‖s + 3‖ + 1) / (4 * c) := by
  have h' := Cvs.Prolate.Mellin.FrozenRootStep.Hyp.add_two h
  have h1 := Cvs.Prolate.Mellin.FrozenRootSizeBounds.Hyp.norm_one_sub_rho_le h'
  have h2 := Cvs.Prolate.Mellin.FrozenRootSizeBounds.Hyp.norm_rho_le h'
  rw [show s + 2 + 1 = s + 3 by ring] at h1
  have hc := h.c_pos
  have e : rhoStar c χ (s + 2) ^ 2 - 1 = -(1 - rhoStar c χ (s + 2)) * (rhoStar c χ (s + 2) + 1) := by ring
  rw [e, norm_mul, norm_neg]
  have h3 : ‖rhoStar c χ (s + 2) + 1‖ ≤ 13 / 4 := by
    have := norm_add_le (rhoStar c χ (s + 2)) 1; rw [norm_one] at this; linarith
  calc ‖1 - rhoStar c χ (s + 2)‖ * ‖rhoStar c χ (s + 2) + 1‖ ≤ (‖s + 3‖ + 1) / c * (13 / 4) := by gcongr
    _ = 13 * (‖s + 3‖ + 1) / (4 * c) := by field_simp

end Cvs.Prolate.Mellin.ForcingUnifiedSizes
