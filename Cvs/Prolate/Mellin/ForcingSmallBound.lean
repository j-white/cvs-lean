import Mathlib
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
# The forcing `B` is `O(1/c)` and `1 + A` stays away from zero

With `a = Re √(τ(s)² + 1)` and `ε ≤ 1/4`: `|B(s)| ≤ 113/(c a)` for `B = (s+2)ρ*(ρ*' − ρ*)/(s+1)`, from
`ρ*' − ρ* = Q_s(ρ*')/((s+2)(ρ*' − ρ₂))`, `|1 − ρ*'| ≤ (‖s+3‖+1)/c` and the shifted gap; and
`|1 + A| ≥ min(1/2, a/6)` for `A = (s+2)ρ*ρ*'/(s+1)`, from `1 + A = (ρ₂ − ρ*')/ρ₂`.
-/

noncomputable section

open Complex

namespace Cvs.Prolate.Mellin.ForcingSmallBound

open Cvs.Prolate.Mellin.FrozenRootErrorIdentity (csqrt re_csqrt_nonneg omega tau zeta rhoStar)
open Cvs.Prolate.Mellin.StepQuadraticRoots (comp Qs)
open Cvs.Prolate.Mellin.UniformRootBounds (Hyp)

variable {ε c χ : ℝ} {s : ℂ}

theorem Hyp.norm_s1_ge (h : Hyp ε c χ s) : 3 / 2 ≤ ‖s + 1‖ := by
  have := Complex.re_le_norm (s + 1); simp at this; linarith [h.hre]

theorem Hyp.s1_ne (h : Hyp ε c χ s) : s + 1 ≠ 0 := by
  intro h0; have := Hyp.norm_s1_ge h; rw [h0, norm_zero] at this; norm_num at this

/-- The step forcing `B(s) = (s+2)ρ*(s)(ρ*(s+2) − ρ*(s))/(s+1)`. -/
def Bf (c χ : ℝ) (s : ℂ) : ℂ := (s + 2) * rhoStar c χ s * (rhoStar c χ (s + 2) - rhoStar c χ s) / (s + 1)

/-- The propagation factor `A(s) = (s+2)ρ*(s)ρ*(s+2)/(s+1)`. -/
def Af (c χ : ℝ) (s : ℂ) : ℂ := (s + 2) * rhoStar c χ s * rhoStar c χ (s + 2) / (s + 1)

/-- **`|B| ≤ 113/(c a)`** for `ε ≤ 1/4`. -/
theorem Hyp.norm_Bf_le (h : Hyp ε c χ s) (hε4 : ε ≤ 1 / 4) :
    ‖Bf c χ s‖ ≤ 113 / (c * (csqrt (tau c χ s ^ 2 + 1)).re) := by
  have h' := Cvs.Prolate.Mellin.FrozenRootStep.Hyp.add_two h
  have hc := h.c_pos
  set a := (csqrt (tau c χ s ^ 2 + 1)).re
  have ha0 : 0 ≤ a := re_csqrt_nonneg _
  have hapos : 0 < a := by
    have := h.a_sq_ge; have := h.hε; by_contra hn; push Not at hn
    have : a = 0 := le_antisymm hn ha0; rw [this] at *; nlinarith
  have hgap : 3 / 4 * a ≤ ‖rhoStar c χ (s + 2) - comp s (rhoStar c χ s)‖ :=
    Cvs.Prolate.Mellin.FrozenRootStep.shifted_gap_ge h hε4
  have hgne : rhoStar c χ (s + 2) - comp s (rhoStar c χ s) ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hgap; nlinarith
  have hroot := Cvs.Prolate.Mellin.FrozenRootSizeBounds.Hyp.Qs_rho h
  have hroot' := Cvs.Prolate.Mellin.FrozenRootSizeBounds.Hyp.Qs_rho h'
  have hstep := Cvs.Prolate.Mellin.StepQuadraticRoots.root_step h.s2_ne (Cvs.Prolate.Mellin.FrozenRootSizeBounds.Hyp.rho_ne h) hroot hroot' hgne
  have hq : ((s + 2 + 1) * (s + 2 + 2) - χ) / (c : ℂ) - ((s + 1) * (s + 2) - χ) / c = (4 * s + 10) / c := by
    have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
    field_simp; ring
  rw [hq] at hstep
  have hB : Bf c χ s = rhoStar c χ s * (2 * (1 - rhoStar c χ (s + 2) ^ 2)
      - (4 * s + 10) / c * rhoStar c χ (s + 2)) / ((s + 1) * (rhoStar c χ (s + 2) - comp s (rhoStar c χ s))) := by
    unfold Bf
    rw [hstep]
    have := h.s2_ne
    have := Hyp.s1_ne h
    field_simp
  rw [hB]
  -- numerator bounds
  have hρ := Cvs.Prolate.Mellin.FrozenRootSizeBounds.Hyp.norm_rho_le h
  have hρ' := Cvs.Prolate.Mellin.FrozenRootSizeBounds.Hyp.norm_rho_le h'
  have h1ρ' := Cvs.Prolate.Mellin.FrozenRootSizeBounds.Hyp.norm_one_sub_rho_le h'
  rw [show s + 2 + 1 = s + 3 by ring] at h1ρ'
  have hs1 := Hyp.norm_s1_ge h
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
  have hnum : ‖2 * (1 - rhoStar c χ (s + 2) ^ 2) - (4 * s + 10) / c * rhoStar c χ (s + 2)‖
      ≤ 75 / 2 * ‖s + 1‖ / c := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, Complex.norm_ofNat]
    have e : 75 / 2 * ‖s + 1‖ / c = 2 * (13 / 4 * (3 * ‖s + 1‖ / c)) + 8 * ‖s + 1‖ / c * (9 / 4) := by ring
    rw [e]; linarith
  rw [norm_div, norm_mul, norm_mul]
  have hden : ‖s + 1‖ * (3 / 4 * a) ≤ ‖s + 1‖ * ‖rhoStar c χ (s + 2) - comp s (rhoStar c χ s)‖ :=
    mul_le_mul_of_nonneg_left hgap (norm_nonneg _)
  have hpos : 0 < ‖s + 1‖ * (3 / 4 * a) := by positivity
  calc ‖rhoStar c χ s‖ * ‖2 * (1 - rhoStar c χ (s + 2) ^ 2) - (4 * s + 10) / c * rhoStar c χ (s + 2)‖
        / (‖s + 1‖ * ‖rhoStar c χ (s + 2) - comp s (rhoStar c χ s)‖)
      ≤ 9 / 4 * (75 / 2 * ‖s + 1‖ / c) / (‖s + 1‖ * (3 / 4 * a)) :=
        div_le_div₀ (by positivity) (mul_le_mul hρ hnum (norm_nonneg _) (by norm_num)) hpos hden
    _ = 225 / 2 / (c * a) := by field_simp; ring
    _ ≤ 113 / (c * a) := by
        apply div_le_div_of_nonneg_right (by norm_num) (by positivity)

/-- **`|1 + A| ≥ min(1/2, a/6)`** for `ε ≤ 1/4`. -/
theorem Hyp.norm_one_add_Af_ge (h : Hyp ε c χ s) (hε4 : ε ≤ 1 / 4) :
    min (1 / 2) ((csqrt (tau c χ s ^ 2 + 1)).re / 6) ≤ ‖1 + Af c χ s‖ := by
  have h' := Cvs.Prolate.Mellin.FrozenRootStep.Hyp.add_two h
  set a := (csqrt (tau c χ s ^ 2 + 1)).re
  have ha0 : 0 ≤ a := re_csqrt_nonneg _
  have hgap : 3 / 4 * a ≤ ‖rhoStar c χ (s + 2) - comp s (rhoStar c χ s)‖ :=
    Cvs.Prolate.Mellin.FrozenRootStep.shifted_gap_ge h hε4
  have hρ' := Cvs.Prolate.Mellin.FrozenRootSizeBounds.Hyp.norm_rho_le h'
  have hs1 := Hyp.norm_s1_ge h
  have hs2 := h.norm_s2_ge
  have hρne := Cvs.Prolate.Mellin.FrozenRootSizeBounds.Hyp.rho_ne h
  by_cases hA : ‖Af c χ s‖ ≤ 1 / 2
  · have : 1 / 2 ≤ ‖1 + Af c χ s‖ := by
      have := norm_sub_norm_le (1 : ℂ) (-(Af c χ s))
      rw [norm_neg, sub_neg_eq_add, norm_one] at this; linarith
    exact (min_le_left _ _).trans this
  · push Not at hA
    -- then |ρ*| > |s+1|/(2|s+2| · 9/4)
    have hρlow : ‖s + 1‖ / (2 * ‖s + 2‖ * (9 / 4)) < ‖rhoStar c χ s‖ := by
      unfold Af at hA
      rw [norm_div, norm_mul, norm_mul, lt_div_iff₀ (by linarith)] at hA
      rw [div_lt_iff₀ (by positivity)]
      nlinarith [norm_nonneg (rhoStar c χ s), norm_nonneg (rhoStar c χ (s + 2))]
    have e := Cvs.Prolate.Mellin.StepQuadraticRoots.one_add_A (Hyp.s1_ne h) h.s2_ne hρne (rhoStar c χ (s + 2))
    have hcomp : ‖comp s (rhoStar c χ s)‖ = ‖s + 1‖ / (‖s + 2‖ * ‖rhoStar c χ s‖) := by
      unfold Cvs.Prolate.Mellin.StepQuadraticRoots.comp; rw [norm_div, norm_neg, norm_mul]
    have hcpos : 0 < ‖comp s (rhoStar c χ s)‖ := by rw [hcomp]; positivity
    have hcle : ‖comp s (rhoStar c χ s)‖ ≤ 9 / 2 := by
      rw [hcomp, div_le_iff₀ (by positivity)]
      rw [div_lt_iff₀ (by positivity)] at hρlow
      nlinarith
    have : a / 6 ≤ ‖1 + Af c χ s‖ := by
      unfold Af; rw [e, norm_div, le_div_iff₀ hcpos, norm_sub_rev]
      nlinarith
    exact (min_le_right _ _).trans this

end Cvs.Prolate.Mellin.ForcingSmallBound
