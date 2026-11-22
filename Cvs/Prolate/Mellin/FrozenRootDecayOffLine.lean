import Mathlib
import Cvs.Prolate.Mellin.CompanionRootGap
import Cvs.Prolate.Mellin.FrozenRootClosedBounds
import Cvs.Prolate.Mellin.FrozenRootCoreBound
import Cvs.Prolate.Mellin.FrozenRootErrorIdentity
import Cvs.Prolate.Mellin.FrozenRootSizeBounds
import Cvs.Prolate.Mellin.UniformRootBounds

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Decay of the frozen root away from the line

`ζ (√(τ²+1) + τ) = 1` gives `|ζ| ≤ 1/(a + Re τ)` when `a + Re τ > 0`, with `a = Re √(τ²+1) ≥ |Re τ|`. Outside
`‖ω‖² ≥ 2χ`, `Re τ ≥ Re ω/(4c)`, so `|ρ*| ≤ 4c/(Re s + 3/2)`.
-/

noncomputable section

open Complex

namespace Cvs.Prolate.Mellin.FrozenRootDecayOffLine

open Cvs.Prolate.Mellin.FrozenRootErrorIdentity (csqrt re_csqrt_nonneg omega tau zeta rhoStar)
open Cvs.Prolate.Mellin.FrozenRootClosedBounds (re_tau)
open Cvs.Prolate.Mellin.UniformRootBounds (Hyp)

variable {ε c χ : ℝ} {s : ℂ}

/-- `|ζ| ≤ 1/(a + Re τ)` when `a + Re τ > 0`. -/
theorem norm_zeta_le_inv (c χ : ℝ) (s : ℂ)
    (hp : 0 < (csqrt (tau c χ s ^ 2 + 1)).re + (tau c χ s).re) :
    ‖zeta c χ s‖ ≤ 1 / ((csqrt (tau c χ s ^ 2 + 1)).re + (tau c χ s).re) := by
  have h1 := Cvs.Prolate.Mellin.CompanionRootGap.zeta_mul_conj c χ s
  have hW : (csqrt (tau c χ s ^ 2 + 1)).re + (tau c χ s).re
      ≤ ‖csqrt (tau c χ s ^ 2 + 1) + tau c χ s‖ := by
    have := Complex.re_le_norm (csqrt (tau c χ s ^ 2 + 1) + tau c χ s); simpa using this
  have hn := congrArg norm h1
  rw [norm_mul, norm_one] at hn
  rw [le_div_iff₀ hp]
  calc ‖zeta c χ s‖ * ((csqrt (tau c χ s ^ 2 + 1)).re + (tau c χ s).re)
      ≤ ‖zeta c χ s‖ * ‖csqrt (tau c χ s ^ 2 + 1) + tau c χ s‖ :=
        mul_le_mul_of_nonneg_left hW (norm_nonneg _)
    _ = 1 := hn

/-- **`Re τ ≥ Re ω/(4c)` once `‖ω‖² ≥ 2χ`.** -/
theorem Hyp.re_tau_ge_far (h : Hyp ε c χ s) (hfar : 2 * χ ≤ ‖omega s‖ ^ 2) :
    (omega s).re / (4 * c) ≤ (tau c χ s).re := by
  have hc := h.c_pos
  have hω := h.omega_ne
  have hn : 0 < Complex.normSq (omega s) := Complex.normSq_pos.mpr hω
  have hre0 : 0 ≤ (omega s).re := by
    have := Cvs.Prolate.Mellin.FrozenRootCoreBound.Hyp.re_omega_ge h; linarith [h.hre]
  rw [re_tau hc.ne' hω, div_le_div_iff₀ (by positivity) (by positivity)]
  rw [← Complex.normSq_eq_norm_sq] at hfar
  have : Complex.normSq (omega s) ≤ 2 * (Complex.normSq (omega s) - χ) := by linarith
  nlinarith [mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ (omega s).re * (2 * c))]

/-- **Decay of the frozen root**: `|ρ*| ≤ 4c/(Re s + 3/2)` once `‖ω‖² ≥ 2χ`. -/
theorem Hyp.norm_rho_le_far (h : Hyp ε c χ s) (hfar : 2 * χ ≤ ‖omega s‖ ^ 2) :
    ‖rhoStar c χ s‖ ≤ 4 * c / (s.re + 3 / 2) := by
  have hc := h.c_pos
  have hre := Cvs.Prolate.Mellin.FrozenRootCoreBound.Hyp.re_omega_ge h
  have hx0 := h.hre
  have hreω : 0 < (omega s).re := by linarith
  have hτ := Hyp.re_tau_ge_far h hfar
  have hτ0 : 0 < (tau c χ s).re := lt_of_lt_of_le (by positivity) hτ
  have ha := Cvs.Prolate.Mellin.CompanionRootGap.abs_re_le_re_csqrt (t := tau c χ s) (by
    have := h.abs_im_tau_le; have := h.hε
    nlinarith [abs_nonneg (tau c χ s).im, sq_abs (tau c χ s).im])
  rw [abs_of_pos hτ0] at ha
  have hp : 0 < (csqrt (tau c χ s ^ 2 + 1)).re + (tau c χ s).re := by linarith
  have hz := norm_zeta_le_inv c χ s hp
  have hz' : ‖zeta c χ s‖ ≤ 2 * c / (omega s).re := by
    refine hz.trans ?_
    rw [div_le_div_iff₀ hp hreω]
    have : (omega s).re / (4 * c) * (4 * c) = (omega s).re := by field_simp
    nlinarith
  have hω := Cvs.Prolate.Mellin.FrozenRootSizeBounds.Hyp.norm_omega_le h
  have hs2 := Cvs.Prolate.Mellin.FrozenRootSizeBounds.Hyp.norm_s2_ge_m h
  have hm := h.norm_m_ge
  have hmre : (s + 3 / 2).re ≤ ‖s + 3 / 2‖ := Complex.re_le_norm _
  simp at hmre
  unfold rhoStar
  rw [norm_div, norm_mul, div_le_div_iff₀ (by linarith) (by linarith)]
  -- ‖ω‖ ≤ (17/12)‖s+2‖ and Re ω ≥ (15/16)(Re s + 3/2)
  have k1 : ‖omega s‖ ≤ 17 / 12 * ‖s + 2‖ := by nlinarith
  have k2 : 15 / 16 * (s.re + 3 / 2) ≤ (omega s).re := by nlinarith
  have hz'' : ‖zeta c χ s‖ ≤ 32 * c / (15 * (s.re + 3 / 2)) := by
    refine hz'.trans ?_
    rw [div_le_div_iff₀ hreω (by positivity)]; nlinarith
  calc ‖omega s‖ * ‖zeta c χ s‖ * (s.re + 3 / 2)
      ≤ 17 / 12 * ‖s + 2‖ * (32 * c / (15 * (s.re + 3 / 2))) * (s.re + 3 / 2) := by
        gcongr
    _ = 136 / 45 * c * ‖s + 2‖ := by field_simp; ring
    _ ≤ 4 * c * ‖s + 2‖ := by nlinarith [norm_nonneg (s + 2)]

end Cvs.Prolate.Mellin.FrozenRootDecayOffLine
