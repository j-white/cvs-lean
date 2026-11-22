import Mathlib
import Cvs.Prolate.Mellin.ForcingSmallBound
import Cvs.Prolate.Mellin.FrozenRootErrorIdentity
import Cvs.Prolate.Mellin.FrozenRootFirstDifference
import Cvs.Prolate.Mellin.FrozenRootSecondDifference
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
# The step of `β = B/(1 + A)` in the near region

`B(s+2) − B(s) = (s+4)/(s+3)·(ρ*(s+2)(D₁ − D₀) + D₀²) − 2ρ*(s)D₀/((s+1)(s+3))`, so in the near region
(`ε ≤ 1/16`, `Re s ≤ 2c`) `|B(s+2) − B(s)| ≤ 18000/(c ε^{3/2} ‖s+2‖) + 25000/(c² ε^{3/2})`, and with
`|1 + A| ≥ √ε/12`, `|β(s+2) − β(s)| ≤ 300000/(c ε² ‖s+2‖) + 2·10⁷/(c² ε²)`.
-/

noncomputable section

open Complex

namespace Cvs.Prolate.Mellin.NearRegionBetaStep

open Cvs.Prolate.Mellin.FrozenRootErrorIdentity (csqrt re_csqrt_nonneg omega tau zeta rhoStar)
open Cvs.Prolate.Mellin.UniformRootBounds (Hyp)
open Cvs.Prolate.Mellin.ForcingSmallBound (Af Bf)

/-- The forcing quotient `β = B/(1 + A)`. -/
def betaf (c χ : ℝ) (s : ℂ) : ℂ := Bf c χ s / (1 + Af c χ s)

variable {ε c χ : ℝ} {s : ℂ}

/-- **The `B`-step identity.** -/
theorem Bf_step_eq (hs1 : s + 1 ≠ 0) (hs3 : s + 3 ≠ 0) :
    Bf c χ (s + 2) - Bf c χ s
      = (s + 4) / (s + 3) * (rhoStar c χ (s + 2) * ((rhoStar c χ (s + 2 + 2) - rhoStar c χ (s + 2))
          - (rhoStar c χ (s + 2) - rhoStar c χ s)) + (rhoStar c χ (s + 2) - rhoStar c χ s) ^ 2)
        - 2 * rhoStar c χ s * (rhoStar c χ (s + 2) - rhoStar c χ s) / ((s + 1) * (s + 3)) := by
  unfold Bf
  rw [show s + 2 + 2 = s + 4 by ring, show s + 2 + 1 = s + 3 by ring]
  field_simp
  ring

/-- **`|B(s+2) − B(s)|` in the near region.** -/
theorem Hyp.norm_Bf_step_le (h : Hyp ε c χ s) (hε16 : ε ≤ 1 / 16) (hnear : s.re ≤ 2 * c) :
    ‖Bf c χ (s + 2) - Bf c χ s‖
      ≤ 18000 / (c * Real.sqrt ε ^ 3 * ‖s + 2‖) + 25000 / (c ^ 2 * Real.sqrt ε ^ 3) := by
  have h' := Cvs.Prolate.Mellin.FrozenRootStep.Hyp.add_two h
  have hε4 : ε ≤ 1 / 4 := by linarith
  have hc := h.c_pos
  obtain ⟨hη, hη4, hcη⟩ := Cvs.Prolate.Mellin.FrozenRootSecondDifference.Hyp.eta_facts h hε16
  set η := Real.sqrt ε
  have hs1 := Cvs.Prolate.Mellin.ForcingSmallBound.Hyp.s1_ne h
  have hs3 : s + 3 ≠ 0 := by intro h0; have := congrArg Complex.re h0; simp at this; linarith [h.hre]
  rw [Bf_step_eq hs1 hs3]
  set D₀ := rhoStar c χ (s + 2) - rhoStar c χ s
  set D₁ := rhoStar c χ (s + 2 + 2) - rhoStar c χ (s + 2)
  have hD0 : ‖D₀‖ ≤ 100 / (c * η) := Cvs.Prolate.Mellin.FrozenRootSecondDifference.Hyp.norm_step_le_eta h hε4
  have hDD : ‖D₁ - D₀‖ ≤ 5900 / (c * η ^ 3 * ‖s + 2‖) + 4000 / (c ^ 2 * η ^ 3) :=
    Cvs.Prolate.Mellin.FrozenRootSecondDifference.Hyp.norm_second_diff_le h hε16 hnear
  have hρ0 := Cvs.Prolate.Mellin.FrozenRootSizeBounds.Hyp.norm_rho_le h
  have hρ1 := Cvs.Prolate.Mellin.FrozenRootSizeBounds.Hyp.norm_rho_le h'
  have hN2 := h.norm_s2_ge
  have hN0 : 0 < ‖s + 2‖ := by linarith
  have hN3 : ‖s + 2‖ ≤ ‖s + 3‖ := by
    rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), ← Complex.normSq_eq_norm_sq,
      ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.normSq_apply]
    simp; nlinarith [h.hre]
  have hN1 : 3 / 5 * ‖s + 2‖ ≤ ‖s + 1‖ := by
    have := norm_sub_norm_le (s + 2) (1 : ℂ)
    rw [show s + 2 - 1 = s + 1 by ring, norm_one] at this; linarith
  have hq : ‖(s + 4) / (s + 3)‖ ≤ 9 / 7 := by
    have hN3' : 7 / 2 ≤ ‖s + 3‖ := by have := Complex.re_le_norm (s + 3); simp at this; linarith [h.hre]
    rw [norm_div, div_le_iff₀ (by linarith)]
    have := norm_add_le (s + 3) (1 : ℂ); rw [show s + 3 + 1 = s + 4 by ring] at this; norm_num at this; linarith
  have hD02 : ‖D₀‖ ^ 2 ≤ 10000 / (c ^ 2 * η ^ 2) := by
    have := pow_le_pow_left₀ (norm_nonneg _) hD0 2
    rw [div_pow, mul_pow] at this; linarith
  have t1 : ‖(s + 4) / (s + 3) * (rhoStar c χ (s + 2) * (D₁ - D₀) + D₀ ^ 2)‖
      ≤ 9 / 7 * (9 / 4 * (5900 / (c * η ^ 3 * ‖s + 2‖) + 4000 / (c ^ 2 * η ^ 3)) + 10000 / (c ^ 2 * η ^ 2)) := by
    rw [norm_mul]
    refine mul_le_mul hq ?_ (norm_nonneg _) (by norm_num)
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul]; exact mul_le_mul hρ1 hDD (norm_nonneg _) (by norm_num)
    · rw [norm_pow]; exact hD02
  have t2 : ‖2 * rhoStar c χ s * D₀ / ((s + 1) * (s + 3))‖ ≤ 750 / (c * η * ‖s + 2‖ ^ 2) := by
    rw [norm_div, norm_mul, norm_mul, norm_mul, Complex.norm_ofNat]
    have hden : 3 / 5 * ‖s + 2‖ ^ 2 ≤ ‖s + 1‖ * ‖s + 3‖ := by
      have := mul_le_mul hN1 hN3 hN0.le (norm_nonneg _)
      linarith [show 3 / 5 * ‖s + 2‖ * ‖s + 2‖ = 3 / 5 * ‖s + 2‖ ^ 2 by ring]
    calc 2 * ‖rhoStar c χ s‖ * ‖D₀‖ / (‖s + 1‖ * ‖s + 3‖)
        ≤ 2 * (9 / 4) * (100 / (c * η)) / (3 / 5 * ‖s + 2‖ ^ 2) :=
          div_le_div₀ (by positivity) (mul_le_mul (mul_le_mul_of_nonneg_left hρ0 (by norm_num)) hD0
            (norm_nonneg _) (by positivity)) (by positivity) hden
      _ = 750 / (c * η * ‖s + 2‖ ^ 2) := by field_simp; ring
  refine (norm_sub_le _ _).trans ?_
  have hη3 : η ^ 3 ≤ η := by nlinarith [pow_pos hη 2]
  have u1 : 10000 / (c ^ 2 * η ^ 2) ≤ 10000 / (c ^ 2 * η ^ 3) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg η] : η ^ 3 ≤ η ^ 2) (by positivity))
  have u2 : 750 / (c * η * ‖s + 2‖ ^ 2) ≤ 300 / (c * η ^ 3 * ‖s + 2‖) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : η ^ 2 ≤ 1 := by nlinarith
    have hp : 0 < c * η * ‖s + 2‖ := by positivity
    nlinarith [mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ c * η * ‖s + 2‖ * 750)]
  set X := 1 / (c * η ^ 3 * ‖s + 2‖)
  set Y := 1 / (c ^ 2 * η ^ 3)
  have hX0 : 0 ≤ X := by positivity
  have hY0 : 0 ≤ Y := by positivity
  have f1 : 5900 / (c * η ^ 3 * ‖s + 2‖) = 5900 * X := by simp only [X]; ring
  have f2 : 4000 / (c ^ 2 * η ^ 3) = 4000 * Y := by simp only [Y]; ring
  have f3 : 10000 / (c ^ 2 * η ^ 3) = 10000 * Y := by simp only [Y]; ring
  have f4 : 300 / (c * η ^ 3 * ‖s + 2‖) = 300 * X := by simp only [X]; ring
  have f5 : 18000 / (c * η ^ 3 * ‖s + 2‖) = 18000 * X := by simp only [X]; ring
  have f6 : 25000 / (c ^ 2 * η ^ 3) = 25000 * Y := by simp only [Y]; ring
  rw [f1, f2] at t1
  rw [f3] at u1
  rw [f4] at u2
  rw [f5, f6]
  nlinarith

/-- **`|β(s+2) − β(s)|` in the near region**: `≤ 300000/(c ε² ‖s+2‖) + 2·10⁷/(c² ε²)`. -/
theorem Hyp.norm_betaf_step_le (h : Hyp ε c χ s) (hε16 : ε ≤ 1 / 16) (hnear : s.re ≤ 2 * c) :
    ‖betaf c χ (s + 2) - betaf c χ s‖ ≤ 300000 / (c * ε ^ 2 * ‖s + 2‖) + 20000000 / (c ^ 2 * ε ^ 2) := by
  have h' := Cvs.Prolate.Mellin.FrozenRootStep.Hyp.add_two h
  have hε4 : ε ≤ 1 / 4 := by linarith
  have hc := h.c_pos
  obtain ⟨hη, hη4, hcη⟩ := Cvs.Prolate.Mellin.FrozenRootSecondDifference.Hyp.eta_facts h hε16
  have hη2 : Real.sqrt ε ^ 2 = ε := Real.sq_sqrt h.hε.le
  set η := Real.sqrt ε
  have hε2 : ε ^ 2 = η ^ 4 := by rw [← hη2]; ring
  rw [hε2]
  -- denominators
  have hm : ∀ {t : ℂ}, Hyp ε c χ t → η / 12 ≤ ‖1 + Af c χ t‖ := by
    intro t ht
    have h1 := Cvs.Prolate.Mellin.ForcingSmallBound.Hyp.norm_one_add_Af_ge ht hε4
    have ha : η / 2 ≤ (csqrt (tau c χ t ^ 2 + 1)).re := Cvs.Prolate.Mellin.FrozenRootSecondDifference.Hyp.a_ge_sqrt ht
    refine le_trans ?_ h1
    apply le_min (by linarith) (by linarith)
  have hm0 := hm h
  have hm1 := hm h'
  have hne0 : 1 + Af c χ s ≠ 0 := by intro h0; rw [h0, norm_zero] at hm0; linarith
  have hne1 : 1 + Af c χ (s + 2) ≠ 0 := by intro h0; rw [h0, norm_zero] at hm1; linarith
  have e : betaf c χ (s + 2) - betaf c χ s
      = (Bf c χ (s + 2) - Bf c χ s) / (1 + Af c χ (s + 2))
        - Bf c χ s * (Af c χ (s + 2) - Af c χ s) / ((1 + Af c χ s) * (1 + Af c χ (s + 2))) := by
    unfold betaf; field_simp; ring
  rw [e]
  have hB := Hyp.norm_Bf_step_le h hε16 hnear
  have hB0 : ‖Bf c χ s‖ ≤ 226 / (c * η) := by
    refine (Cvs.Prolate.Mellin.ForcingSmallBound.Hyp.norm_Bf_le h hε4).trans ?_
    have ha : η / 2 ≤ (csqrt (tau c χ s ^ 2 + 1)).re := Cvs.Prolate.Mellin.FrozenRootSecondDifference.Hyp.a_ge_sqrt h
    rw [div_le_div_iff₀ (by have := Cvs.Prolate.Mellin.FrozenRootFirstDifference.Hyp.a_pos h; positivity) (by positivity)]; nlinarith
  have hA := Cvs.Prolate.Mellin.FrozenRootFirstDifference.Hyp.norm_Af_step_le h hε4
  have a0 : η / 2 ≤ (csqrt (tau c χ s ^ 2 + 1)).re := Cvs.Prolate.Mellin.FrozenRootSecondDifference.Hyp.a_ge_sqrt h
  have a1 : η / 2 ≤ (csqrt (tau c χ (s + 2) ^ 2 + 1)).re := Cvs.Prolate.Mellin.FrozenRootSecondDifference.Hyp.a_ge_sqrt h'
  have hN2 := h.norm_s2_ge
  have hN0 : 0 < ‖s + 2‖ := by linarith
  have hN3 : ‖s + 2‖ ≤ ‖s + 3‖ := by
    rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), ← Complex.normSq_eq_norm_sq,
      ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.normSq_apply]
    simp; nlinarith [h.hre]
  have hN1 : 3 / 5 * ‖s + 2‖ ≤ ‖s + 1‖ := by
    have := norm_sub_norm_le (s + 2) (1 : ℂ)
    rw [show s + 2 - 1 = s + 1 by ring, norm_one] at this; linarith
  have hA' : ‖Af c χ (s + 2) - Af c χ s‖ ≤ 4050 / 7 / (c * η) + 135 / 8 / ‖s + 2‖ ^ 2 := by
    refine hA.trans ?_
    have u1 : 50 / (c * (csqrt (tau c χ s ^ 2 + 1)).re) ≤ 100 / (c * η) := by
      rw [div_le_div_iff₀ (by have := Cvs.Prolate.Mellin.FrozenRootFirstDifference.Hyp.a_pos h; positivity) (by positivity)]; nlinarith
    have u2 : 50 / (c * (csqrt (tau c χ (s + 2) ^ 2 + 1)).re) ≤ 100 / (c * η) := by
      rw [div_le_div_iff₀ (by have := Cvs.Prolate.Mellin.FrozenRootFirstDifference.Hyp.a_pos h'; positivity) (by positivity)]; nlinarith
    have u3 : 9 / 2 / (‖s + 1‖ * ‖s + 3‖) ≤ 15 / 2 / ‖s + 2‖ ^ 2 := by
      have hden : 3 / 5 * ‖s + 2‖ ^ 2 ≤ ‖s + 1‖ * ‖s + 3‖ := by
        have := mul_le_mul hN1 hN3 hN0.le (norm_nonneg _)
        linarith [show 3 / 5 * ‖s + 2‖ * ‖s + 2‖ = 3 / 5 * ‖s + 2‖ ^ 2 by ring]
      calc 9 / 2 / (‖s + 1‖ * ‖s + 3‖) ≤ 9 / 2 / (3 / 5 * ‖s + 2‖ ^ 2) :=
            div_le_div_of_nonneg_left (by norm_num) (by positivity) hden
        _ = 15 / 2 / ‖s + 2‖ ^ 2 := by field_simp; ring
    have e2 : 4050 / 7 / (c * η) + 135 / 8 / ‖s + 2‖ ^ 2 = 9 / 4 * (9 / 7 * (100 / (c * η) + 100 / (c * η))
        + 15 / 2 / ‖s + 2‖ ^ 2) := by ring
    rw [e2]; gcongr
  -- assemble with atoms
  have t1 : ‖(Bf c χ (s + 2) - Bf c χ s) / (1 + Af c χ (s + 2))‖
      ≤ (18000 / (c * η ^ 3 * ‖s + 2‖) + 25000 / (c ^ 2 * η ^ 3)) / (η / 12) := by
    rw [norm_div]; exact div_le_div₀ (by positivity) hB (by positivity) hm1
  have t2 : ‖Bf c χ s * (Af c χ (s + 2) - Af c χ s) / ((1 + Af c χ s) * (1 + Af c χ (s + 2)))‖
      ≤ 226 / (c * η) * (4050 / 7 / (c * η) + 135 / 8 / ‖s + 2‖ ^ 2) / (η / 12 * (η / 12)) := by
    rw [norm_div, norm_mul, norm_mul]
    exact div_le_div₀ (by positivity) (mul_le_mul hB0 hA' (norm_nonneg _) (by positivity)) (by positivity)
      (mul_le_mul hm0 hm1 (by positivity) (norm_nonneg _))
  refine (norm_sub_le _ _).trans ?_
  set X := 1 / (c * η ^ 4 * ‖s + 2‖)
  set Y := 1 / (c ^ 2 * η ^ 4)
  have hX0 : 0 ≤ X := by positivity
  have hY0 : 0 ≤ Y := by positivity
  have k1 : (18000 / (c * η ^ 3 * ‖s + 2‖) + 25000 / (c ^ 2 * η ^ 3)) / (η / 12) = 216000 * X + 300000 * Y := by
    simp only [X, Y]; field_simp; ring
  have k2 : 226 / (c * η) * (4050 / 7 / (c * η) + 135 / 8 / ‖s + 2‖ ^ 2) / (η / 12 * (η / 12))
      = 226 * 144 * (4050 / 7) * Y + 226 * 144 * (135 / 8) * (η / ‖s + 2‖) * X := by
    simp only [X, Y]; field_simp; ring
  have k3 : η / ‖s + 2‖ ≤ 1 / 10 := by
    rw [div_le_iff₀ hN0]; linarith
  rw [k1] at t1; rw [k2] at t2
  have k4 : 226 * 144 * (135 / 8) * (η / ‖s + 2‖) * X ≤ 226 * 144 * (135 / 8) * (1 / 10) * X := by
    gcongr
  have f1 : 300000 / (c * η ^ 4 * ‖s + 2‖) = 300000 * X := by simp only [X]; ring
  have f2 : 20000000 / (c ^ 2 * η ^ 4) = 20000000 * Y := by simp only [Y]; ring
  rw [f1, f2]
  nlinarith

end Cvs.Prolate.Mellin.NearRegionBetaStep
