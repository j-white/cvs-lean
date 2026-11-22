import Mathlib
import Cvs.Prolate.Mellin.ForcingSmallBound
import Cvs.Prolate.Mellin.FrozenRootErrorIdentity
import Cvs.Prolate.Mellin.FrozenRootSizeBounds
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
# First differences of the frozen root and of `A`

With `a(s) = Re √(τ(s)² + 1)` and `ε ≤ 1/4`: `|ρ*(s+2) − ρ*(s)| ≤ 50/(c a(s))`, from
`ρ*' − ρ* = Q_s(ρ*')/((s+2)(ρ*' − ρ₂))` with `|Q_s(ρ*')| ≤ (75/2)‖s+1‖/c` and the shifted gap. Since
`A(s+2) − A(s) = ρ*(s+2)[(s+4)/(s+3)·(ρ*(s+4) − ρ*(s)) − 2ρ*(s)/((s+1)(s+3))]`,
`|A(s+2) − A(s)| ≤ (9/4)[(9/7)(50/(c a(s)) + 50/(c a(s+2))) + (9/2)/(‖s+1‖‖s+3‖)]`.
-/

noncomputable section

open Complex

namespace Cvs.Prolate.Mellin.FrozenRootFirstDifference

open Cvs.Prolate.Mellin.FrozenRootErrorIdentity (csqrt re_csqrt_nonneg omega tau zeta rhoStar)
open Cvs.Prolate.Mellin.StepQuadraticRoots (comp Qs)
open Cvs.Prolate.Mellin.UniformRootBounds (Hyp)
open Cvs.Prolate.Mellin.ForcingSmallBound (Af Bf)

variable {ε c χ : ℝ} {s : ℂ}

/-- `a(s) > 0` on the region. -/
theorem Hyp.a_pos (h : Hyp ε c χ s) : 0 < (csqrt (tau c χ s ^ 2 + 1)).re := by
  have := h.a_sq_ge; have := h.hε; have ha0 := re_csqrt_nonneg (tau c χ s ^ 2 + 1)
  by_contra hn; push Not at hn
  have : (csqrt (tau c χ s ^ 2 + 1)).re = 0 := le_antisymm hn ha0
  nlinarith

/-- The exact step `ρ*(s+2) − ρ*(s) = Q_s(ρ*(s+2))/((s+2)(ρ*(s+2) − ρ₂(s)))`, with `q(s+2) − q(s) = (4s+10)/c`. -/
theorem Hyp.rho_step_eq (h : Hyp ε c χ s) (hε4 : ε ≤ 1 / 4) :
    rhoStar c χ (s + 2) - rhoStar c χ s
      = (2 * (1 - rhoStar c χ (s + 2) ^ 2) - (4 * s + 10) / c * rhoStar c χ (s + 2))
          / ((s + 2) * (rhoStar c χ (s + 2) - comp s (rhoStar c χ s))) := by
  have h' := Cvs.Prolate.Mellin.FrozenRootStep.Hyp.add_two h
  have hc := h.c_pos
  have hgap : 3 / 4 * (csqrt (tau c χ s ^ 2 + 1)).re ≤ ‖rhoStar c χ (s + 2) - comp s (rhoStar c χ s)‖ :=
    Cvs.Prolate.Mellin.FrozenRootStep.shifted_gap_ge h hε4
  have hgne : rhoStar c χ (s + 2) - comp s (rhoStar c χ s) ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hgap; have := Hyp.a_pos h; linarith
  have hroot := Cvs.Prolate.Mellin.FrozenRootSizeBounds.Hyp.Qs_rho h
  have hroot' := Cvs.Prolate.Mellin.FrozenRootSizeBounds.Hyp.Qs_rho h'
  have hstep := Cvs.Prolate.Mellin.StepQuadraticRoots.root_step h.s2_ne (Cvs.Prolate.Mellin.FrozenRootSizeBounds.Hyp.rho_ne h) hroot hroot' hgne
  have hq : ((s + 2 + 1) * (s + 2 + 2) - χ) / (c : ℂ) - ((s + 1) * (s + 2) - χ) / c = (4 * s + 10) / c := by
    have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
    field_simp; ring
  rw [hq] at hstep
  exact hstep

/-- `|Q_s(ρ*(s+2))| ≤ (75/2)‖s+1‖/c`. -/
theorem Hyp.norm_Q_le (h : Hyp ε c χ s) :
    ‖2 * (1 - rhoStar c χ (s + 2) ^ 2) - (4 * s + 10) / c * rhoStar c χ (s + 2)‖ ≤ 75 / 2 * ‖s + 1‖ / c := by
  have h' := Cvs.Prolate.Mellin.FrozenRootStep.Hyp.add_two h
  have hc := h.c_pos
  have hρ' := Cvs.Prolate.Mellin.FrozenRootSizeBounds.Hyp.norm_rho_le h'
  have h1ρ' := Cvs.Prolate.Mellin.FrozenRootSizeBounds.Hyp.norm_one_sub_rho_le h'
  rw [show s + 2 + 1 = s + 3 by ring] at h1ρ'
  have hs1 := Cvs.Prolate.Mellin.ForcingSmallBound.Hyp.norm_s1_ge h
  have hs3 : ‖s + 3‖ + 1 ≤ 3 * ‖s + 1‖ := by
    have := norm_add_le (s + 1) (2 : ℂ)
    rw [show s + 1 + 2 = s + 3 by ring] at this; norm_num at this; linarith
  have hs10 : ‖4 * s + 10‖ ≤ 8 * ‖s + 1‖ := by
    have := norm_add_le (4 * (s + 1)) (6 : ℂ)
    rw [show 4 * (s + 1) + 6 = 4 * s + 10 by ring, norm_mul] at this; norm_num at this; linarith
  have n1 : ‖1 - rhoStar c χ (s + 2) ^ 2‖ ≤ 13 / 4 * (3 * ‖s + 1‖ / c) := by
    have e : 1 - rhoStar c χ (s + 2) ^ 2 = (1 - rhoStar c χ (s + 2)) * (1 + rhoStar c χ (s + 2)) := by ring
    rw [e, norm_mul]
    have : ‖1 + rhoStar c χ (s + 2)‖ ≤ 13 / 4 := by
      have := norm_add_le (1 : ℂ) (rhoStar c χ (s + 2)); norm_num at this; linarith
    have hh : ‖1 - rhoStar c χ (s + 2)‖ ≤ 3 * ‖s + 1‖ / c := by
      refine h1ρ'.trans ?_; exact div_le_div_of_nonneg_right (by linarith) hc.le
    nlinarith [norm_nonneg (1 - rhoStar c χ (s + 2)), norm_nonneg (1 + rhoStar c χ (s + 2))]
  have n2 : ‖(4 * s + 10) / (c : ℂ) * rhoStar c χ (s + 2)‖ ≤ 8 * ‖s + 1‖ / c * (9 / 4) := by
    rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
    exact mul_le_mul (div_le_div_of_nonneg_right hs10 hc.le) hρ' (norm_nonneg _) (by positivity)
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, Complex.norm_ofNat]
  have e : 75 / 2 * ‖s + 1‖ / c = 2 * (13 / 4 * (3 * ‖s + 1‖ / c)) + 8 * ‖s + 1‖ / c * (9 / 4) := by ring
  rw [e]; linarith

/-- **`|ρ*(s+2) − ρ*(s)| ≤ 50/(c a)`.** -/
theorem Hyp.norm_rho_step_le (h : Hyp ε c χ s) (hε4 : ε ≤ 1 / 4) :
    ‖rhoStar c χ (s + 2) - rhoStar c χ s‖ ≤ 50 / (c * (csqrt (tau c χ s ^ 2 + 1)).re) := by
  have hc := h.c_pos
  have ha := Hyp.a_pos h
  have hgap : 3 / 4 * (csqrt (tau c χ s ^ 2 + 1)).re ≤ ‖rhoStar c χ (s + 2) - comp s (rhoStar c χ s)‖ :=
    Cvs.Prolate.Mellin.FrozenRootStep.shifted_gap_ge h hε4
  rw [Hyp.rho_step_eq h hε4, norm_div, norm_mul]
  have hQ := Hyp.norm_Q_le h
  have hs12 : ‖s + 1‖ ≤ ‖s + 2‖ := by
    rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
      Complex.normSq_apply, Complex.normSq_apply]
    simp; nlinarith [h.hre]
  have hN2 : 0 < ‖s + 2‖ := by linarith [h.norm_s2_ge]
  have hden : ‖s + 2‖ * (3 / 4 * (csqrt (tau c χ s ^ 2 + 1)).re)
      ≤ ‖s + 2‖ * ‖rhoStar c χ (s + 2) - comp s (rhoStar c χ s)‖ := mul_le_mul_of_nonneg_left hgap hN2.le
  calc _ ≤ 75 / 2 * ‖s + 1‖ / c / (‖s + 2‖ * (3 / 4 * (csqrt (tau c χ s ^ 2 + 1)).re)) :=
        div_le_div₀ (by positivity) hQ (by positivity) hden
    _ ≤ 75 / 2 * ‖s + 2‖ / c / (‖s + 2‖ * (3 / 4 * (csqrt (tau c χ s ^ 2 + 1)).re)) := by
        gcongr
    _ = 50 / (c * (csqrt (tau c χ s ^ 2 + 1)).re) := by field_simp; ring

/-- **The `A`-step identity.** -/
theorem Af_step_eq (hs1 : s + 1 ≠ 0) (hs3 : s + 3 ≠ 0) :
    Af c χ (s + 2) - Af c χ s
      = rhoStar c χ (s + 2) * ((s + 4) / (s + 3) * (rhoStar c χ (s + 2 + 2) - rhoStar c χ s)
          - 2 * rhoStar c χ s / ((s + 1) * (s + 3))) := by
  unfold Af
  rw [show s + 2 + 2 = s + 4 by ring, show s + 2 + 1 = s + 3 by ring]
  field_simp
  ring

/-- **`|A(s+2) − A(s)|`** bound. -/
theorem Hyp.norm_Af_step_le (h : Hyp ε c χ s) (hε4 : ε ≤ 1 / 4) :
    ‖Af c χ (s + 2) - Af c χ s‖
      ≤ 9 / 4 * (9 / 7 * (50 / (c * (csqrt (tau c χ s ^ 2 + 1)).re)
          + 50 / (c * (csqrt (tau c χ (s + 2) ^ 2 + 1)).re)) + 9 / 2 / (‖s + 1‖ * ‖s + 3‖)) := by
  have h' := Cvs.Prolate.Mellin.FrozenRootStep.Hyp.add_two h
  have hs1 := Cvs.Prolate.Mellin.ForcingSmallBound.Hyp.s1_ne h
  have hs3 : s + 3 ≠ 0 := by intro h0; have := congrArg Complex.re h0; simp at this; linarith [h.hre]
  rw [Af_step_eq hs1 hs3, norm_mul]
  have hρ1 := Cvs.Prolate.Mellin.FrozenRootSizeBounds.Hyp.norm_rho_le h'
  have hρ0 := Cvs.Prolate.Mellin.FrozenRootSizeBounds.Hyp.norm_rho_le h
  have d0 := Hyp.norm_rho_step_le h hε4
  have d1 := Hyp.norm_rho_step_le h' hε4
  have hN3 : 7 / 2 ≤ ‖s + 3‖ := by have := Complex.re_le_norm (s + 3); simp at this; linarith [h.hre]
  have hN1 : 3 / 2 ≤ ‖s + 1‖ := Cvs.Prolate.Mellin.ForcingSmallBound.Hyp.norm_s1_ge h
  have hq : ‖(s + 4) / (s + 3)‖ ≤ 9 / 7 := by
    rw [norm_div, div_le_iff₀ (by linarith)]
    have := norm_add_le (s + 3) (1 : ℂ); rw [show s + 3 + 1 = s + 4 by ring] at this; norm_num at this; linarith
  have hinner : ‖(s + 4) / (s + 3) * (rhoStar c χ (s + 2 + 2) - rhoStar c χ s)
      - 2 * rhoStar c χ s / ((s + 1) * (s + 3))‖
      ≤ 9 / 7 * (50 / (c * (csqrt (tau c χ s ^ 2 + 1)).re)
          + 50 / (c * (csqrt (tau c χ (s + 2) ^ 2 + 1)).re)) + 9 / 2 / (‖s + 1‖ * ‖s + 3‖) := by
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul]
      have : ‖rhoStar c χ (s + 2 + 2) - rhoStar c χ s‖
          ≤ 50 / (c * (csqrt (tau c χ s ^ 2 + 1)).re) + 50 / (c * (csqrt (tau c χ (s + 2) ^ 2 + 1)).re) := by
        have e : rhoStar c χ (s + 2 + 2) - rhoStar c χ s
            = (rhoStar c χ (s + 2 + 2) - rhoStar c χ (s + 2)) + (rhoStar c χ (s + 2) - rhoStar c χ s) := by ring
        rw [e]; exact (norm_add_le _ _).trans (by linarith)
      exact mul_le_mul hq this (norm_nonneg _) (by norm_num)
    · rw [norm_div, norm_mul, norm_mul, Complex.norm_ofNat]
      exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  exact mul_le_mul hρ1 hinner (norm_nonneg _) (by norm_num)

end Cvs.Prolate.Mellin.FrozenRootFirstDifference
