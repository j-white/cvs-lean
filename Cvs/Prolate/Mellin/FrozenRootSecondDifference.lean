import Mathlib
import Cvs.Prolate.Mellin.CompanionRootGap
import Cvs.Prolate.Mellin.FrozenRootErrorIdentity
import Cvs.Prolate.Mellin.FrozenRootFirstDifference
import Cvs.Prolate.Mellin.FrozenRootSizeBounds
import Cvs.Prolate.Mellin.FrozenRootStep
import Cvs.Prolate.Mellin.HalfGapIncrements
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
# The second difference of the frozen root

With `D₀ = ρ*(s+2) − ρ*(s)`, `D₁ = ρ*(s+4) − ρ*(s+2)`, `F₀ = Q_s(ρ*(s+2))/(s+2)`, `F₁ = Q_{s+2}(ρ*(s+4))/(s+4)` and the
shifted gaps `G₀ = D₀ + 2W(s)`, `G₁ = D₁ + 2W(s+2)` (so that `D₀G₀ = F₀`, `D₁G₁ = F₁`):
`(D₁ − D₀)(G₁ + D₀) = (F₁ − F₀) − 2D₀(W(s+2) − W(s))`.
-/

noncomputable section

open Complex

namespace Cvs.Prolate.Mellin.FrozenRootSecondDifference

open Cvs.Prolate.Mellin.FrozenRootErrorIdentity (csqrt re_csqrt_nonneg omega tau zeta rhoStar)
open Cvs.Prolate.Mellin.StepQuadraticRoots (comp)
open Cvs.Prolate.Mellin.UniformRootBounds (Hyp)
open Cvs.Prolate.Mellin.HalfGapIncrements (Wg)

/-- **The second-difference identity** (pure algebra). -/
theorem second_diff_identity {D₀ D₁ W₀ W₁ F₀ F₁ : ℂ} (h₀ : D₀ * (D₀ + 2 * W₀) = F₀)
    (h₁ : D₁ * (D₁ + 2 * W₁) = F₁) :
    (D₁ - D₀) * (D₁ + 2 * W₁ + D₀) = (F₁ - F₀) - 2 * D₀ * (W₁ - W₀) := by
  rw [← h₀, ← h₁]; ring

variable {ε c χ : ℝ} {s : ℂ}

/-- `ρ*(s) − ρ₂(s) = 2W(s)`. -/
theorem Hyp.gap_eq_W (h : Hyp ε c χ s) : rhoStar c χ s - comp s (rhoStar c χ s) = 2 * Wg c χ s := by
  rw [Cvs.Prolate.Mellin.CompanionRootGap.rhoStar_sub_comp h.m_ne h.s2_ne h.omega_ne]; unfold Wg; ring

/-- `D₀ (D₀ + 2W₀) = F₀`. -/
theorem Hyp.step_mul_gap (h : Hyp ε c χ s) (hε4 : ε ≤ 1 / 4) :
    (rhoStar c χ (s + 2) - rhoStar c χ s) * ((rhoStar c χ (s + 2) - rhoStar c χ s) + 2 * Wg c χ s)
      = (2 * (1 - rhoStar c χ (s + 2) ^ 2) - (4 * s + 10) / c * rhoStar c χ (s + 2)) / (s + 2) := by
  have hG : (rhoStar c χ (s + 2) - rhoStar c χ s) + 2 * Wg c χ s
      = rhoStar c χ (s + 2) - comp s (rhoStar c χ s) := by
    rw [← Hyp.gap_eq_W h]; ring
  have hgap : 3 / 4 * (csqrt (tau c χ s ^ 2 + 1)).re ≤ ‖rhoStar c χ (s + 2) - comp s (rhoStar c χ s)‖ :=
    Cvs.Prolate.Mellin.FrozenRootStep.shifted_gap_ge h hε4
  have hgne : rhoStar c χ (s + 2) - comp s (rhoStar c χ s) ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hgap; have := Cvs.Prolate.Mellin.FrozenRootFirstDifference.Hyp.a_pos h; linarith
  rw [hG, Cvs.Prolate.Mellin.FrozenRootFirstDifference.Hyp.rho_step_eq h hε4]
  field_simp [h.s2_ne]

/-- **The second difference, exactly.** -/
theorem Hyp.second_diff_eq (h : Hyp ε c χ s) (hε4 : ε ≤ 1 / 4) :
    ((rhoStar c χ (s + 2 + 2) - rhoStar c χ (s + 2)) - (rhoStar c χ (s + 2) - rhoStar c χ s))
        * ((rhoStar c χ (s + 2 + 2) - rhoStar c χ (s + 2)) + 2 * Wg c χ (s + 2)
            + (rhoStar c χ (s + 2) - rhoStar c χ s))
      = ((2 * (1 - rhoStar c χ (s + 2 + 2) ^ 2) - (4 * (s + 2) + 10) / c * rhoStar c χ (s + 2 + 2)) / (s + 2 + 2)
          - (2 * (1 - rhoStar c χ (s + 2) ^ 2) - (4 * s + 10) / c * rhoStar c χ (s + 2)) / (s + 2))
        - 2 * (rhoStar c χ (s + 2) - rhoStar c χ s) * (Wg c χ (s + 2) - Wg c χ s) := by
  have h' := Cvs.Prolate.Mellin.FrozenRootStep.Hyp.add_two h
  exact second_diff_identity (Hyp.step_mul_gap h hε4) (Hyp.step_mul_gap h' hε4)

/-- `a ≥ √ε/2` on the region. -/
theorem Hyp.a_ge_sqrt (h : Hyp ε c χ s) : Real.sqrt ε / 2 ≤ (csqrt (tau c χ s ^ 2 + 1)).re := by
  have ha := h.a_sq_ge
  have ha0 := re_csqrt_nonneg (tau c χ s ^ 2 + 1)
  have hs := Real.sq_sqrt h.hε.le
  have hs0 := Real.sqrt_nonneg ε
  nlinarith [sq_nonneg ((csqrt (tau c χ s ^ 2 + 1)).re - Real.sqrt ε / 2)]

theorem Hyp.norm_le_of_near (h : Hyp ε c χ s) (hnear : s.re ≤ 2 * c) : ‖s‖ ≤ 4 * c := by
  have hn := Complex.norm_le_abs_re_add_abs_im s
  have him := h.him; have hε := h.hε; have hre := h.hre
  rw [abs_of_nonneg (by linarith)] at hn
  have : |s.im| ≤ 2 * c := by nlinarith [h.c_pos]
  linarith

/-- The near-region parameters: `η = √ε ≤ 1/4`, `c η⁴ ≥ 64`. -/
theorem Hyp.eta_facts (h : Hyp ε c χ s) (hε16 : ε ≤ 1 / 16) :
    0 < Real.sqrt ε ∧ Real.sqrt ε ≤ 1 / 4 ∧ 64 ≤ c * Real.sqrt ε ^ 4 := by
  have hη : 0 < Real.sqrt ε := Real.sqrt_pos.mpr h.hε
  have hη2 : Real.sqrt ε ^ 2 = ε := Real.sq_sqrt h.hε.le
  refine ⟨hη, ?_, ?_⟩
  · rw [show (1 / 4 : ℝ) = Real.sqrt (1 / 16) by
      rw [show (1 / 16 : ℝ) = (1 / 4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hε16
  · have := h.hc
    rw [div_le_iff₀ (by have := h.hε; positivity)] at this
    rw [show Real.sqrt ε ^ 4 = (Real.sqrt ε ^ 2) ^ 2 by ring, hη2]; linarith

/-- `|ρ*(s+2) − ρ*(s)| ≤ 100/(c η)`. -/
theorem Hyp.norm_step_le_eta (h : Hyp ε c χ s) (hε4 : ε ≤ 1 / 4) :
    ‖rhoStar c χ (s + 2) - rhoStar c χ s‖ ≤ 100 / (c * Real.sqrt ε) := by
  have hc := h.c_pos
  have hη : 0 < Real.sqrt ε := Real.sqrt_pos.mpr h.hε
  have a0 := Hyp.a_ge_sqrt h
  refine (Cvs.Prolate.Mellin.FrozenRootFirstDifference.Hyp.norm_rho_step_le h hε4).trans ?_
  rw [div_le_div_iff₀ (by have := Cvs.Prolate.Mellin.FrozenRootFirstDifference.Hyp.a_pos h; positivity) (by positivity)]
  nlinarith

theorem Hyp.norm_s2_le_s4 (h : Hyp ε c χ s) : ‖s + 2‖ ≤ ‖s + 2 + 2‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), ← Complex.normSq_eq_norm_sq,
    ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.normSq_apply]
  simp; nlinarith [h.hre]

theorem Hyp.norm_s1_le_s2 (h : Hyp ε c χ s) : ‖s + 1‖ ≤ ‖s + 2‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), ← Complex.normSq_eq_norm_sq,
    ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.normSq_apply]
  simp; nlinarith [h.hre]

/-- **The `Q`-step** in the near region: `|Q₁ − Q₀| ≤ 2618/(c η)`. -/
theorem Hyp.norm_Q_step_le (h : Hyp ε c χ s) (hε16 : ε ≤ 1 / 16) (hnear : s.re ≤ 2 * c) :
    ‖(2 * (1 - rhoStar c χ (s + 2 + 2) ^ 2) - (4 * (s + 2) + 10) / c * rhoStar c χ (s + 2 + 2))
      - (2 * (1 - rhoStar c χ (s + 2) ^ 2) - (4 * s + 10) / c * rhoStar c χ (s + 2))‖
      ≤ 2618 / (c * Real.sqrt ε) := by
  have h' := Cvs.Prolate.Mellin.FrozenRootStep.Hyp.add_two h
  have h'' := Cvs.Prolate.Mellin.FrozenRootStep.Hyp.add_two h'
  have hc := h.c_pos
  obtain ⟨hη, hη4, -⟩ := Hyp.eta_facts h hε16
  set D₁ := rhoStar c χ (s + 2 + 2) - rhoStar c χ (s + 2)
  have hD1 : ‖D₁‖ ≤ 100 / (c * Real.sqrt ε) := Hyp.norm_step_le_eta h' (by linarith)
  have hρ1 := Cvs.Prolate.Mellin.FrozenRootSizeBounds.Hyp.norm_rho_le h'
  have hρ2 := Cvs.Prolate.Mellin.FrozenRootSizeBounds.Hyp.norm_rho_le h''
  have hs := Hyp.norm_le_of_near h hnear
  have e : (2 * (1 - rhoStar c χ (s + 2 + 2) ^ 2) - (4 * (s + 2) + 10) / c * rhoStar c χ (s + 2 + 2))
      - (2 * (1 - rhoStar c χ (s + 2) ^ 2) - (4 * s + 10) / c * rhoStar c χ (s + 2))
      = -2 * D₁ * (rhoStar c χ (s + 2 + 2) + rhoStar c χ (s + 2)) - (4 * s + 10) / c * D₁
        - 8 / c * rhoStar c χ (s + 2 + 2) := by
    simp only [D₁]; ring
  rw [e]
  have h410 : ‖(4 * s + 10) / (c : ℂ)‖ ≤ 17 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc, div_le_iff₀ hc]
    have := norm_add_le (4 * s) (10 : ℂ); rw [norm_mul] at this; norm_num at this
    linarith [h.c_ge]
  have h8 : ‖(8 : ℂ) / c * rhoStar c χ (s + 2 + 2)‖ ≤ 18 / c := by
    rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc, Complex.norm_ofNat,
      div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right (by linarith) hc.le
  have t1 : ‖-2 * D₁ * (rhoStar c χ (s + 2 + 2) + rhoStar c χ (s + 2))‖ ≤ 9 * ‖D₁‖ := by
    rw [norm_mul, norm_mul, norm_neg, Complex.norm_ofNat]
    have := norm_add_le (rhoStar c χ (s + 2 + 2)) (rhoStar c χ (s + 2))
    nlinarith [norm_nonneg D₁]
  have t2 : ‖(4 * s + 10) / (c : ℂ) * D₁‖ ≤ 17 * ‖D₁‖ := by
    rw [norm_mul]; exact mul_le_mul_of_nonneg_right h410 (norm_nonneg _)
  have t3 : 18 / c ≤ 18 / (c * Real.sqrt ε) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (by nlinarith)
  calc _ ≤ ‖-2 * D₁ * (rhoStar c χ (s + 2 + 2) + rhoStar c χ (s + 2))‖ + ‖(4 * s + 10) / (c : ℂ) * D₁‖
        + ‖(8 : ℂ) / c * rhoStar c χ (s + 2 + 2)‖ := by
        refine (norm_sub_le _ _).trans ?_; gcongr; exact norm_sub_le _ _
    _ ≤ 26 * (100 / (c * Real.sqrt ε)) + 18 / (c * Real.sqrt ε) := by linarith
    _ = 2618 / (c * Real.sqrt ε) := by ring

/-- **The `F`-step** in the near region: `|F₁ − F₀| ≤ 2700/(c η ‖s+2‖)`. -/
theorem Hyp.norm_F_step_le (h : Hyp ε c χ s) (hε16 : ε ≤ 1 / 16) (hnear : s.re ≤ 2 * c) :
    ‖(2 * (1 - rhoStar c χ (s + 2 + 2) ^ 2) - (4 * (s + 2) + 10) / c * rhoStar c χ (s + 2 + 2)) / (s + 2 + 2)
      - (2 * (1 - rhoStar c χ (s + 2) ^ 2) - (4 * s + 10) / c * rhoStar c χ (s + 2)) / (s + 2)‖
      ≤ 2700 / (c * Real.sqrt ε * ‖s + 2‖) := by
  have h' := Cvs.Prolate.Mellin.FrozenRootStep.Hyp.add_two h
  have hc := h.c_pos
  obtain ⟨hη, hη4, -⟩ := Hyp.eta_facts h hε16
  have hQd := Hyp.norm_Q_step_le h hε16 hnear
  have hQ0 := Cvs.Prolate.Mellin.FrozenRootFirstDifference.Hyp.norm_Q_le h
  set Q₀ := 2 * (1 - rhoStar c χ (s + 2) ^ 2) - (4 * s + 10) / c * rhoStar c χ (s + 2)
  set Q₁ := 2 * (1 - rhoStar c χ (s + 2 + 2) ^ 2) - (4 * (s + 2) + 10) / c * rhoStar c χ (s + 2 + 2)
  have hs2ne := h.s2_ne
  have hs4ne : s + 2 + 2 ≠ 0 := h'.s2_ne
  have hN2 : 0 < ‖s + 2‖ := by linarith [h.norm_s2_ge]
  have hs4 := Hyp.norm_s2_le_s4 h
  have hs1 := Hyp.norm_s1_le_s2 h
  have e : Q₁ / (s + 2 + 2) - Q₀ / (s + 2) = (Q₁ - Q₀) / (s + 2 + 2) - 2 * Q₀ / ((s + 2) * (s + 2 + 2)) := by
    field_simp; ring
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_div, norm_div, norm_mul, norm_mul, Complex.norm_ofNat]
  have u1 : ‖Q₁ - Q₀‖ / ‖s + 2 + 2‖ ≤ 2618 / (c * Real.sqrt ε) / ‖s + 2‖ :=
    div_le_div₀ (by positivity) hQd hN2 hs4
  have u2 : 2 * ‖Q₀‖ / (‖s + 2‖ * ‖s + 2 + 2‖) ≤ 75 / c / ‖s + 2‖ := by
    have hQ0' : 2 * ‖Q₀‖ ≤ 75 / c * ‖s + 2‖ := by
      have := mul_le_mul_of_nonneg_left hQ0 (by norm_num : (0 : ℝ) ≤ 2)
      have h3 : 2 * (75 / 2 * ‖s + 1‖ / c) ≤ 75 / c * ‖s + 2‖ := by
        rw [show 2 * (75 / 2 * ‖s + 1‖ / c) = 75 / c * ‖s + 1‖ by ring]
        exact mul_le_mul_of_nonneg_left hs1 (by positivity)
      linarith
    rw [div_le_div_iff₀ (by positivity) hN2]
    have h4 : ‖s + 2‖ ≤ ‖s + 2 + 2‖ := hs4
    calc 2 * ‖Q₀‖ * ‖s + 2‖ ≤ 75 / c * ‖s + 2‖ * ‖s + 2‖ := mul_le_mul_of_nonneg_right hQ0' hN2.le
      _ ≤ 75 / c * (‖s + 2‖ * ‖s + 2 + 2‖) := by
          rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h4 hN2.le) (by positivity)
  have u3 : 75 / c / ‖s + 2‖ ≤ 82 / (c * Real.sqrt ε) / ‖s + 2‖ := by
    apply div_le_div_of_nonneg_right _ hN2.le
    rw [div_le_div_iff₀ hc (by positivity)]; nlinarith
  calc _ ≤ 2618 / (c * Real.sqrt ε) / ‖s + 2‖ + 82 / (c * Real.sqrt ε) / ‖s + 2‖ := by linarith
    _ = 2700 / (c * Real.sqrt ε * ‖s + 2‖) := by field_simp; ring

/-- `a(s) ≤ ‖τ‖ + 1` and `‖τ‖ ≤ (‖ω‖ + χ/‖ω‖)/(2c)`. -/
theorem Hyp.a_le_two_point_three (h : Hyp ε c χ s) (hs : ‖s‖ ≤ 4 * c + 2) :
    (csqrt (tau c χ s ^ 2 + 1)).re ≤ 33 / 10 := by
  have hc := h.c_pos
  have hc64 := h.c_ge
  have hω := h.omega_ne
  have hω0 : 0 < ‖omega s‖ := norm_pos_iff.mpr hω
  have hωg : 15 / 8 ≤ ‖omega s‖ := by linarith [h.norm_omega_ge, h.norm_m_ge]
  have hωl := Cvs.Prolate.Mellin.FrozenRootSizeBounds.Hyp.norm_omega_le h
  have hm : ‖s + 3 / 2‖ ≤ ‖s‖ + 3 / 2 := by
    have := norm_add_le s (3 / 2 : ℂ); norm_num at this ⊢; linarith
  have hχ0 : 0 ≤ χ := by linarith [h.hχ0]
  have ht : ‖tau c χ s‖ ≤ 23 / 10 := by
    unfold Cvs.Prolate.Mellin.FrozenRootErrorIdentity.tau
    rw [norm_div, show ‖(2 * (c : ℂ))‖ = 2 * c by
      rw [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc], div_le_iff₀ (by positivity)]
    have h1 : ‖omega s - (χ : ℂ) / omega s‖ ≤ ‖omega s‖ + χ / ‖omega s‖ := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hχ0]
    have h2 : χ / ‖omega s‖ ≤ 8 * c / 15 := by
      rw [div_le_div_iff₀ hω0 (by norm_num)]; nlinarith [h.hχ1]
    nlinarith
  have ha := re_le_norm_csqrt (tau c χ s)
  have hn : ‖csqrt (tau c χ s ^ 2 + 1)‖ ≤ ‖tau c χ s‖ + 1 := by
    have hsq := Cvs.Prolate.Mellin.FrozenRootErrorIdentity.csqrt_sq (tau c χ s ^ 2 + 1)
    have h1 : ‖csqrt (tau c χ s ^ 2 + 1)‖ ^ 2 ≤ (‖tau c χ s‖ + 1) ^ 2 := by
      rw [← norm_pow, hsq]
      have := norm_add_le (tau c χ s ^ 2) 1
      rw [norm_pow, norm_one] at this
      nlinarith [norm_nonneg (tau c χ s)]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h1
  linarith
where re_le_norm_csqrt (t : ℂ) : (csqrt (t ^ 2 + 1)).re ≤ ‖csqrt (t ^ 2 + 1)‖ := Complex.re_le_norm _

/-- **The `W`-step** in the near region: `|W₁ − W₀| ≤ 4/(η‖s+2‖) + 5/(cη)`. -/
theorem Hyp.norm_W_step_near (h : Hyp ε c χ s) (hε16 : ε ≤ 1 / 16) (hnear : s.re ≤ 2 * c) :
    ‖Wg c χ (s + 2) - Wg c χ s‖ ≤ 4 / (Real.sqrt ε * ‖s + 2‖) + 5 / (c * Real.sqrt ε) := by
  have h' := Cvs.Prolate.Mellin.FrozenRootStep.Hyp.add_two h
  have hc := h.c_pos
  obtain ⟨hη, hη4, -⟩ := Hyp.eta_facts h hε16
  have hW := Cvs.Prolate.Mellin.HalfGapIncrements.Hyp.norm_Wg_step_le h
  have hk := Cvs.Prolate.Mellin.FrozenRootStep.norm_kappa_step_le h
  have ht := Cvs.Prolate.Mellin.FrozenRootStep.norm_tau_step_le h
  have hN2 := h.norm_s2_ge
  have hN4 : 9 / 2 ≤ ‖s + 4‖ := by have := Complex.re_le_norm (s + 4); simp at this; linarith [h.hre]
  have hs := Hyp.norm_le_of_near h hnear
  have ha1 : (csqrt (tau c χ (s + 2) ^ 2 + 1)).re ≤ 33 / 10 := by
    apply Hyp.a_le_two_point_three h'
    have := norm_add_le s (2 : ℂ); norm_num at this; linarith
  have a0 := Hyp.a_ge_sqrt h
  have a1 := Hyp.a_ge_sqrt h'
  have hk' : ‖omega (s + 2) / (s + 2 + 2) - omega s / (s + 2)‖ ≤ 17 / 36 / ‖s + 2‖ := by
    refine hk.trans ?_
    have e1 : 1 / (‖s + 2‖ * ‖s + 4‖) ≤ 2 / 9 / ‖s + 2‖ := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    have e2 : 1 / ‖s + 4‖ ≤ 1 / ‖s + 2‖ := by
      apply one_div_le_one_div_of_le (by linarith)
      have := Hyp.norm_s2_le_s4 h; rwa [show s + 2 + 2 = s + 4 by ring] at this
    have e3 : 17 / 36 / ‖s + 2‖ = 2 / 9 / ‖s + 2‖ + 1 / 8 * (1 / ‖s + 2‖ + 1 / ‖s + 2‖) := by ring
    rw [e3]; linarith
  have hωω : 1 / (‖omega s‖ * ‖omega (s + 2)‖) ≤ 32 / 45 / ‖s + 2‖ := by
    have hω0 : 3 / 4 * ‖s + 2‖ ≤ ‖omega s‖ := by
      have := h.norm_omega_ge
      have := norm_add_le (s + 3 / 2) (1 / 2 : ℂ)
      rw [show s + 3 / 2 + 1 / 2 = s + 2 by ring] at this; norm_num at this
      linarith
    have hω1 : 15 / 8 ≤ ‖omega (s + 2)‖ := by linarith [h'.norm_omega_ge, h'.norm_m_ge]
    rw [div_le_div_iff₀ (by have := norm_pos_iff.mpr h.omega_ne; have := norm_pos_iff.mpr h'.omega_ne; positivity)
      (by positivity)]
    nlinarith
  have ht' : ‖tau c χ (s + 2) - tau c χ s‖ ≤ 9 / 8 * (1 / c + 32 / 45 / ‖s + 2‖) := by
    refine ht.trans ?_; gcongr
  have hfac : 1 + 2 / ((csqrt (tau c χ s ^ 2 + 1)).re + (csqrt (tau c χ (s + 2) ^ 2 + 1)).re)
      ≤ 3 / Real.sqrt ε := by
    have : 2 / ((csqrt (tau c χ s ^ 2 + 1)).re + (csqrt (tau c χ (s + 2) ^ 2 + 1)).re) ≤ 2 / Real.sqrt ε :=
      div_le_div_of_nonneg_left (by norm_num) hη (by linarith)
    have : 1 ≤ 1 / Real.sqrt ε := by rw [le_div_iff₀ hη]; linarith
    have e : 3 / Real.sqrt ε = 1 / Real.sqrt ε + 2 / Real.sqrt ε := by ring
    linarith
  calc ‖Wg c χ (s + 2) - Wg c χ s‖
      ≤ 17 / 36 / ‖s + 2‖ * (33 / 10 + 1) + 17 / 12 * (9 / 8 * (1 / c + 32 / 45 / ‖s + 2‖) * (3 / Real.sqrt ε)) := by
        refine hW.trans ?_
        have hpos : 0 ≤ 1 + 2 / ((csqrt (tau c χ s ^ 2 + 1)).re + (csqrt (tau c χ (s + 2) ^ 2 + 1)).re) := by
          have := Cvs.Prolate.Mellin.FrozenRootFirstDifference.Hyp.a_pos h; have := Cvs.Prolate.Mellin.FrozenRootFirstDifference.Hyp.a_pos h'; positivity
        have hpa : 0 ≤ (csqrt (tau c χ (s + 2) ^ 2 + 1)).re + 1 := by
          have := re_csqrt_nonneg (tau c χ (s + 2) ^ 2 + 1); linarith
        gcongr
    _ ≤ 4 / (Real.sqrt ε * ‖s + 2‖) + 5 / (c * Real.sqrt ε) := by
        have hN0 : 0 < ‖s + 2‖ := by linarith
        have e : 17 / 36 / ‖s + 2‖ * (33 / 10 + 1) + 17 / 12 * (9 / 8 * (1 / c + 32 / 45 / ‖s + 2‖) * (3 / Real.sqrt ε))
            = 731 / 360 / ‖s + 2‖ + 153 / 32 / (c * Real.sqrt ε) + 17 / 5 / (Real.sqrt ε * ‖s + 2‖) := by
          field_simp; ring
        rw [e]
        have f1 : 731 / 360 / ‖s + 2‖ ≤ 6 / 10 / (Real.sqrt ε * ‖s + 2‖) := by
          rw [div_le_div_iff₀ hN0 (by positivity)]; nlinarith
        have f2 : 153 / 32 / (c * Real.sqrt ε) ≤ 5 / (c * Real.sqrt ε) :=
          div_le_div_of_nonneg_right (by norm_num) (by positivity)
        have f3 : 6 / 10 / (Real.sqrt ε * ‖s + 2‖) + 17 / 5 / (Real.sqrt ε * ‖s + 2‖) = 4 / (Real.sqrt ε * ‖s + 2‖) := by
          ring
        linarith

/-- **The second difference in the near region**: `|D₁ − D₀| ≤ 5900/(c η³ ‖s+2‖) + 4000/(c² η³)`, `η = √ε`. -/
theorem Hyp.norm_second_diff_le (h : Hyp ε c χ s) (hε16 : ε ≤ 1 / 16) (hnear : s.re ≤ 2 * c) :
    ‖(rhoStar c χ (s + 2 + 2) - rhoStar c χ (s + 2)) - (rhoStar c χ (s + 2) - rhoStar c χ s)‖
      ≤ 5900 / (c * Real.sqrt ε ^ 3 * ‖s + 2‖) + 4000 / (c ^ 2 * Real.sqrt ε ^ 3) := by
  have h' := Cvs.Prolate.Mellin.FrozenRootStep.Hyp.add_two h
  have hε4 : ε ≤ 1 / 4 := by linarith
  have hc := h.c_pos
  obtain ⟨hη, hη4, hcη⟩ := Hyp.eta_facts h hε16
  set η := Real.sqrt ε
  set D₀ := rhoStar c χ (s + 2) - rhoStar c χ s
  set D₁ := rhoStar c χ (s + 2 + 2) - rhoStar c χ (s + 2)
  have hD0 : ‖D₀‖ ≤ 100 / (c * η) := Hyp.norm_step_le_eta h hε4
  have hsmall : 100 / (c * η) ≤ η / 10 := by
    have hη2 : η ^ 2 ≤ 1 / 16 := by nlinarith
    have h1024 : 1024 ≤ c * η ^ 2 := by
      have : c * η ^ 4 ≤ c * η ^ 2 * (1 / 16) := by
        rw [show c * η ^ 4 = c * η ^ 2 * η ^ 2 by ring]
        exact mul_le_mul_of_nonneg_left hη2 (by positivity)
      linarith
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have a1 : η / 2 ≤ (csqrt (tau c χ (s + 2) ^ 2 + 1)).re := Hyp.a_ge_sqrt h'
  have hG1 : 3 / 4 * (csqrt (tau c χ (s + 2) ^ 2 + 1)).re ≤ ‖D₁ + 2 * Wg c χ (s + 2)‖ := by
    have := Cvs.Prolate.Mellin.FrozenRootStep.shifted_gap_ge h' hε4
    have e : D₁ + 2 * Wg c χ (s + 2) = rhoStar c χ (s + 2 + 2) - comp (s + 2) (rhoStar c χ (s + 2)) := by
      rw [← Hyp.gap_eq_W h']; simp only [D₁]; ring
    rwa [e]
  have hden : η / 4 ≤ ‖D₁ + 2 * Wg c χ (s + 2) + D₀‖ := by
    have := norm_sub_norm_le (D₁ + 2 * Wg c χ (s + 2)) (-D₀)
    rw [norm_neg, sub_neg_eq_add] at this
    linarith
  have hid := Hyp.second_diff_eq h hε4
  have hF := Hyp.norm_F_step_le h hε16 hnear
  have hWs := Hyp.norm_W_step_near h hε16 hnear
  have hN0 : 0 < ‖s + 2‖ := by linarith [h.norm_s2_ge]
  have hR : ‖(D₁ - D₀) * (D₁ + 2 * Wg c χ (s + 2) + D₀)‖
      ≤ 2700 / (c * η * ‖s + 2‖) + 2 * (100 / (c * η)) * (4 / (η * ‖s + 2‖) + 5 / (c * η)) := by
    rw [hid]
    refine (norm_sub_le _ _).trans (add_le_add hF ?_)
    rw [norm_mul, norm_mul, Complex.norm_ofNat]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hD0 (by norm_num)) hWs (norm_nonneg _) (by positivity)
  rw [norm_mul] at hR
  have hmain : ‖D₁ - D₀‖ * (η / 4) ≤ 2700 / (c * η * ‖s + 2‖) + 2 * (100 / (c * η)) * (4 / (η * ‖s + 2‖) + 5 / (c * η)) :=
    (mul_le_mul_of_nonneg_left hden (norm_nonneg _)).trans hR
  have hfinal : 2700 / (c * η * ‖s + 2‖) + 2 * (100 / (c * η)) * (4 / (η * ‖s + 2‖) + 5 / (c * η))
      ≤ (5900 / (c * η ^ 3 * ‖s + 2‖) + 4000 / (c ^ 2 * η ^ 3)) * (η / 4) := by
    have e1 : 2 * (100 / (c * η)) * (4 / (η * ‖s + 2‖) + 5 / (c * η))
        = 800 / (c * η ^ 2 * ‖s + 2‖) + 1000 / (c ^ 2 * η ^ 2) := by field_simp; ring
    have e2 : (5900 / (c * η ^ 3 * ‖s + 2‖) + 4000 / (c ^ 2 * η ^ 3)) * (η / 4)
        = 1475 / (c * η ^ 2 * ‖s + 2‖) + 1000 / (c ^ 2 * η ^ 2) := by field_simp; ring
    rw [e1, e2]
    have : 2700 / (c * η * ‖s + 2‖) ≤ 675 / (c * η ^ 2 * ‖s + 2‖) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hp : 0 < c * η * ‖s + 2‖ := by positivity
      have := mul_le_mul_of_nonneg_right hη4 hp.le
      have e : c * η ^ 2 * ‖s + 2‖ = η * (c * η * ‖s + 2‖) := by ring
      rw [e]; nlinarith
    have e3 : 675 / (c * η ^ 2 * ‖s + 2‖) + 800 / (c * η ^ 2 * ‖s + 2‖) = 1475 / (c * η ^ 2 * ‖s + 2‖) := by ring
    linarith
  have := hmain.trans hfinal
  exact le_of_mul_le_mul_right this (by positivity)

end Cvs.Prolate.Mellin.FrozenRootSecondDifference
