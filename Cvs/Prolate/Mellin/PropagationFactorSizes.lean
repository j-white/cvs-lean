import Mathlib
import Cvs.Prolate.Mellin.CompanionRootGap
import Cvs.Prolate.Mellin.FarRegionDamping
import Cvs.Prolate.Mellin.ForcingSmallBound
import Cvs.Prolate.Mellin.FrozenRootErrorIdentity
import Cvs.Prolate.Mellin.FrozenRootFirstDifference
import Cvs.Prolate.Mellin.FrozenRootSizeBounds
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
# Pointwise sizes of the propagation factor

On the region with `ε ≤ 1/4`: `‖(1 + A)⁻¹‖ ≤ 12/√ε`, `‖A‖ ≤ 135/16`,
`‖(1 + A')⁻¹ − (1 + A)⁻¹‖ ≤ (144/ε)‖A' − A‖`, `‖A(s+2) − A(s)‖ ≤ 4050/(7c√ε) + 81/(8(x+1)(x+3))`, and for `x ≥ 2c`
`‖A(s+2) − A(s)‖ ≤ 8100/(7x) + 81/(8x²)`; also `Σ_{n<N} 1/(X+2n)³ ≤ 1/X²` for `X ≥ 2`.
-/

noncomputable section

open Finset

namespace Cvs.Prolate.Mellin.PropagationFactorSizes

open Cvs.Prolate.Mellin.FrozenRootErrorIdentity Cvs.Prolate.Mellin.UniformRootBounds Cvs.Prolate.Mellin.ForcingSmallBound

variable {ε c χ : ℝ} {s : ℂ}

theorem Hyp.sqrt_eps_le_a (h : Hyp ε c χ s) : Real.sqrt ε / 2 ≤ (csqrt (tau c χ s ^ 2 + 1)).re := by
  have ha := Cvs.Prolate.Mellin.FrozenRootFirstDifference.Hyp.a_pos h
  have ha2 := Hyp.a_sq_ge h
  rw [div_le_iff₀ (by norm_num), Real.sqrt_le_left]
  · nlinarith
  · linarith

/-- `‖1 + A‖ ≥ √ε/12`. -/
theorem Hyp.norm_one_add_Af_ge' (h : Hyp ε c χ s) (hε4 : ε ≤ 1 / 4) : Real.sqrt ε / 12 ≤ ‖1 + Af c χ s‖ := by
  have hA := Hyp.norm_one_add_Af_ge h hε4
  have ha := Hyp.sqrt_eps_le_a h
  have hs1 : Real.sqrt ε ≤ 1 := Real.sqrt_le_one.mpr h.hε1
  refine le_trans ?_ hA
  apply le_min
  · linarith
  · linarith

theorem Hyp.norm_inv_one_add_Af_le (h : Hyp ε c χ s) (hε4 : ε ≤ 1 / 4) :
    ‖(1 + Af c χ s)⁻¹‖ ≤ 12 / Real.sqrt ε := by
  have h1 := Hyp.norm_one_add_Af_ge' h hε4
  have hs : 0 < Real.sqrt ε := Real.sqrt_pos.mpr h.hε
  rw [norm_inv, inv_eq_one_div, div_le_div_iff₀ (by linarith) hs]
  linarith

theorem Hyp.norm_Af_le_const (h : Hyp ε c χ s) : ‖Af c χ s‖ ≤ 135 / 16 := by
  have h' := Cvs.Prolate.Mellin.FrozenRootStep.Hyp.add_two h
  have hρ := Cvs.Prolate.Mellin.FrozenRootSizeBounds.Hyp.norm_rho_le h
  have hρ' := Cvs.Prolate.Mellin.FrozenRootSizeBounds.Hyp.norm_rho_le h'
  have hs1 := Hyp.norm_s1_ge h
  have hr : ‖s + 2‖ ≤ 5 / 3 * ‖s + 1‖ := by
    have := norm_add_le (s + 1) 1
    rw [show s + 1 + 1 = s + 2 by ring, norm_one] at this; linarith
  unfold Af
  rw [norm_div, norm_mul, norm_mul, div_le_iff₀ (by linarith)]
  calc ‖s + 2‖ * ‖rhoStar c χ s‖ * ‖rhoStar c χ (s + 2)‖ ≤ (5 / 3 * ‖s + 1‖) * (9 / 4) * (9 / 4) := by
        gcongr
    _ = 135 / 16 * ‖s + 1‖ := by ring

/-- `‖(1 + A')⁻¹ − (1 + A)⁻¹‖ ≤ (144/ε)‖A' − A‖`. -/
theorem norm_inv_sub_le {A A' : ℂ} {ε : ℝ} (hε : 0 < ε) (h1 : Real.sqrt ε / 12 ≤ ‖1 + A‖)
    (h2 : Real.sqrt ε / 12 ≤ ‖1 + A'‖) : ‖(1 + A')⁻¹ - (1 + A)⁻¹‖ ≤ 144 / ε * ‖A' - A‖ := by
  have hs : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  have n1 : 1 + A ≠ 0 := fun h0 => by rw [h0, norm_zero] at h1; linarith
  have n2 : 1 + A' ≠ 0 := fun h0 => by rw [h0, norm_zero] at h2; linarith
  have e : (1 + A')⁻¹ - (1 + A)⁻¹ = (A - A') / ((1 + A') * (1 + A)) := by field_simp; ring
  rw [e, norm_div, norm_mul, ← norm_neg (A - A'), neg_sub]
  have hp : ε / 144 ≤ ‖1 + A'‖ * ‖1 + A‖ := by
    have : Real.sqrt ε / 12 * (Real.sqrt ε / 12) ≤ ‖1 + A'‖ * ‖1 + A‖ := mul_le_mul h2 h1 (by positivity) (norm_nonneg _)
    rw [show Real.sqrt ε / 12 * (Real.sqrt ε / 12) = Real.sqrt ε ^ 2 / 144 by ring, Real.sq_sqrt hε.le] at this
    exact this
  rw [div_le_iff₀ (by linarith)]
  have := norm_nonneg (A' - A)
  calc ‖A' - A‖ = 144 / ε * ‖A' - A‖ * (ε / 144) := by field_simp
    _ ≤ 144 / ε * ‖A' - A‖ * (‖1 + A'‖ * ‖1 + A‖) := by gcongr

/-- **The `A`-step, everywhere on the region.** -/
theorem Hyp.norm_Af_step_le' (h : Hyp ε c χ s) (hε4 : ε ≤ 1 / 4) :
    ‖Af c χ (s + 2) - Af c χ s‖ ≤ 4050 / (7 * c * Real.sqrt ε) + 81 / (8 * ((s.re + 1) * (s.re + 3))) := by
  have h' := Cvs.Prolate.Mellin.FrozenRootStep.Hyp.add_two h
  have hc := h.c_pos
  have hx := h.hre
  have hs : 0 < Real.sqrt ε := Real.sqrt_pos.mpr h.hε
  have hst := Cvs.Prolate.Mellin.FrozenRootFirstDifference.Hyp.norm_Af_step_le h hε4
  have a1 := Hyp.sqrt_eps_le_a h
  have a2 := Hyp.sqrt_eps_le_a h'
  have b1 : 50 / (c * (csqrt (tau c χ s ^ 2 + 1)).re) ≤ 100 / (c * Real.sqrt ε) := by
    rw [div_le_div_iff₀ (by have := Cvs.Prolate.Mellin.FrozenRootFirstDifference.Hyp.a_pos h; positivity) (by positivity)]
    nlinarith
  have b2 : 50 / (c * (csqrt (tau c χ (s + 2) ^ 2 + 1)).re) ≤ 100 / (c * Real.sqrt ε) := by
    rw [div_le_div_iff₀ (by have := Cvs.Prolate.Mellin.FrozenRootFirstDifference.Hyp.a_pos h'; positivity) (by positivity)]
    nlinarith
  have b3 : 9 / 2 / (‖s + 1‖ * ‖s + 3‖) ≤ 9 / 2 / ((s.re + 1) * (s.re + 3)) := by
    have r1 : s.re + 1 ≤ ‖s + 1‖ := by have := Complex.re_le_norm (s + 1); simpa using this
    have r3 : s.re + 3 ≤ ‖s + 3‖ := by have := Complex.re_le_norm (s + 3); simpa using this
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    exact mul_le_mul r1 r3 (by linarith) (by linarith)
  refine hst.trans ?_
  calc 9 / 4 * (9 / 7 * (50 / (c * (csqrt (tau c χ s ^ 2 + 1)).re)
        + 50 / (c * (csqrt (tau c χ (s + 2) ^ 2 + 1)).re)) + 9 / 2 / (‖s + 1‖ * ‖s + 3‖))
      ≤ 9 / 4 * (9 / 7 * (100 / (c * Real.sqrt ε) + 100 / (c * Real.sqrt ε))
          + 9 / 2 / ((s.re + 1) * (s.re + 3))) := by gcongr
    _ = _ := by field_simp; ring

/-- **The `A`-step in the far region.** -/
theorem Hyp.norm_Af_step_le_far (h : Hyp ε c χ s) (hε4 : ε ≤ 1 / 4) (hx : 2 * c ≤ s.re) :
    ‖Af c χ (s + 2) - Af c χ s‖ ≤ 8100 / (7 * s.re) + 81 / (8 * s.re ^ 2) := by
  have h' := Cvs.Prolate.Mellin.FrozenRootStep.Hyp.add_two h
  have hc := h.c_pos
  have hx0 : 0 < s.re := by linarith
  have hst := Cvs.Prolate.Mellin.FrozenRootFirstDifference.Hyp.norm_Af_step_le h hε4
  have hfar : ∀ t : ℂ, Hyp ε c χ t → 2 * c ≤ t.re → s.re ≤ t.re →
      50 / (c * (csqrt (tau c χ t ^ 2 + 1)).re) ≤ 200 / s.re := by
    intro t ht htx hst
    have h1 := Cvs.Prolate.Mellin.FarRegionDamping.Hyp.far_re_tau ht htx
    have h2 : |(tau c χ t).re| ≤ (csqrt (tau c χ t ^ 2 + 1)).re := by
      apply Cvs.Prolate.Mellin.CompanionRootGap.abs_re_le_re_csqrt
      have := Hyp.abs_im_tau_le ht
      have := ht.hε
      nlinarith [abs_nonneg (tau c χ t).im, sq_abs (tau c χ t).im]
    have h3 : s.re / (4 * c) ≤ (csqrt (tau c χ t ^ 2 + 1)).re := by
      have : t.re / (4 * c) ≤ |(tau c χ t).re| := h1.trans (le_abs_self _)
      have : s.re / (4 * c) ≤ t.re / (4 * c) := by gcongr
      linarith
    have ha : 0 < (csqrt (tau c χ t ^ 2 + 1)).re := lt_of_lt_of_le (by positivity) h3
    rw [div_le_div_iff₀ (by positivity) hx0]
    have : c * (s.re / (4 * c)) ≤ c * (csqrt (tau c χ t ^ 2 + 1)).re := by gcongr
    rw [show c * (s.re / (4 * c)) = s.re / 4 by field_simp] at this
    linarith
  have b1 := hfar s h hx le_rfl
  have b2 := hfar (s + 2) h' (by simp; linarith) (by simp)
  have b3 : 9 / 2 / (‖s + 1‖ * ‖s + 3‖) ≤ 9 / 2 / s.re ^ 2 := by
    have r1 : s.re ≤ ‖s + 1‖ := by have := Complex.re_le_norm (s + 1); simp at this; linarith
    have r3 : s.re ≤ ‖s + 3‖ := by have := Complex.re_le_norm (s + 3); simp at this; linarith
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    rw [sq]; exact mul_le_mul r1 r3 hx0.le (by linarith)
  refine hst.trans ?_
  calc 9 / 4 * (9 / 7 * (50 / (c * (csqrt (tau c χ s ^ 2 + 1)).re)
        + 50 / (c * (csqrt (tau c χ (s + 2) ^ 2 + 1)).re)) + 9 / 2 / (‖s + 1‖ * ‖s + 3‖))
      ≤ 9 / 4 * (9 / 7 * (200 / s.re + 200 / s.re) + 9 / 2 / s.re ^ 2) := by gcongr
    _ = _ := by field_simp; ring

end Cvs.Prolate.Mellin.PropagationFactorSizes
