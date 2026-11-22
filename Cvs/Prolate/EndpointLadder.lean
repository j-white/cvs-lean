import Mathlib
import Cvs.Prolate.EvenAngularPeak
import Cvs.Prolate.LadderRatioClosedForm
import Cvs.Prolate.LiouvilleGreen.FarSideTurningPoint
import Cvs.Prolate.LiouvilleGreen.RiccatiWkbExponent
import Cvs.Prolate.LiouvilleGreen.WkbEndpointLower
import Cvs.Prolate.LiouvilleGreen.WkbRiccatiBarrier

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The endpoint ladder

For even `L²`-normalised angular solutions at `χ_a ≤ χ_b` with `a = 2√χ_b/c ≤ 1/2`, and `ψ g_a = μ_a g_a`, `μ_a > 0`:
`g_b(1)² ≥ (B² μ_a²/4) R^{(χ_b − χ_a)/c} g_a(1)²`, `R = (2c + K₀)/(2ca + K₀)` (Cvs.Prolate.LadderRatioClosedForm), `B = e^{−K·2s₀/p(2s₀)}` the
loss from the peak of `g_b` to `a` (Cvs.Prolate.EvenAngularPeak, Cvs.Prolate.LiouvilleGreen.WkbEndpointLower), `√2/μ_a` the amplitude of `g_a` (Cvs.Prolate.LiouvilleGreen.WkbEndpointAmplitude).
-/

noncomputable section

open Real Set Cvs.L2a.AngularProlateTailPositive

namespace Cvs.Prolate.EndpointLadder

open Cvs.Prolate.LiouvilleGreen.WkbRiccatiBarrier (pp)
open Cvs.Prolate.LiouvilleGreen.RiccatiWkbExponent (U)
open Cvs.Prolate.LiouvilleGreen.FarSideTurningPoint (sm)
open Cvs.Prolate.LiouvilleGreen.WkbEndpointLower (Kl)
open Cvs.Prolate.LadderRatioClosedForm (kap)

/-- The ladder's starting point `a = 2√χ/c`. -/
def aS (c χ : ℝ) : ℝ := 2 * √χ / c

/-- The loss from the peak to `2s₀`: `B = e^{−K·2s₀/p(2s₀)}`, `K = Kl(c, χ, s₀)`, `s₀ = √χ/c`. -/
def startB (c χ : ℝ) : ℝ := exp (-(Kl c χ (√χ / c) * (√χ / c + √χ / c) / pp (√χ / c + √χ / c)))

/-- The ladder base `R = (2c + K₀)/(2ca + K₀)`, `K₀ = 2/a + κ`, at `a = 2√χ/c`. -/
def ladR (c χ : ℝ) : ℝ :=
  (2 * c + (2 / aS c χ + kap c χ (aS c χ))) / (2 * c * aS c χ + (2 / aS c χ + kap c χ (aS c χ)))

theorem startB_pos (c χ : ℝ) : 0 < startB c χ := exp_pos _

theorem ladR_pos {c χ : ℝ} (hc : 0 < c) (hχ : 0 < χ) : 0 < ladR c χ := by
  have ha : 0 < aS c χ := by unfold aS; positivity
  have hk : 0 < kap c χ (aS c χ) := by unfold kap; positivity
  unfold ladR; positivity

/-- `s_m ≥ 1/2`. -/
theorem half_le_sm {c χ : ℝ} (hc : 0 < c) (hχ : 0 < χ) : 1 / 2 ≤ sm c χ := by
  have h := Cvs.Prolate.LiouvilleGreen.FarSideTurningPoint.sm_sq hc hχ
  have : (1 / 2 : ℝ) ^ 2 ≤ sm c χ ^ 2 := by
    rw [h, le_div_iff₀ (by positivity)]; nlinarith
  exact (pow_le_pow_iff_left₀ (by norm_num) (Cvs.Prolate.LiouvilleGreen.FarSideTurningPoint.sm_pos hc hχ).le two_ne_zero).1 this

/-- `U ≥ 0` where `g > 0` and `g g′ ≤ 0`, `s² ≤ 1`. -/
theorem U_nonneg {g g₁ : ℝ → ℝ} {s : ℝ} (hg : 0 < g s) (hgg : g s * g₁ s ≤ 0) (hs : s ^ 2 ≤ 1) :
    0 ≤ U g g₁ s := by
  have h1 : g₁ s ≤ 0 := by
    by_contra h; push Not at h; nlinarith [mul_pos hg h]
  unfold U
  exact div_nonneg (neg_nonneg.2 (mul_nonpos_of_nonneg_of_nonpos (by linarith) h1)) hg.le

/-- **The peak, made positive**: an even normalised angular solution with `g(1) ≠ 0` has a sign `ε` and a point
`m ∈ [0, s₀]` maximising `g²` on `[0, 1]` with `(εg(m))² ≥ 1/2`, `εg > 0` and `(εg)(εg′) ≤ 0` on `[m, 1]`. -/
theorem exists_pos_peak {g g₁ g₂ : ℝ → ℝ} {c χ : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) (hnorm : ∫ s in (-1 : ℝ)..1, g s ^ 2 = 1)
    (hc : 0 < c) (hχ : 0 < χ) (hχc : χ < c ^ 2) (hg1 : g 1 ≠ 0) :
    ∃ ε : ℝ, ε ^ 2 = 1 ∧ ∃ m ∈ Icc (0 : ℝ) (√χ / c), 1 / 2 ≤ (ε * g m) ^ 2 ∧
      (∀ s ∈ Icc m 1, 0 < ε * g s) ∧ (∀ s ∈ Icc m 1, (ε * g s) * (ε * g₁ s) ≤ 0) ∧
      ∀ s ∈ Icc (0 : ℝ) 1, (ε * g s) ^ 2 ≤ (ε * g m) ^ 2 := by
  obtain ⟨m, hm, hm2, hsign, hmono, hmax⟩ := Cvs.Prolate.EvenAngularPeak.exists_peak hg hg₁ hang heven hnorm hc hχ hχc hg1
  rcases lt_or_gt_of_ne (show g m ≠ 0 by intro h; rw [h] at hm2; norm_num at hm2) with hneg | hpos
  · refine ⟨-1, by norm_num, m, hm, by nlinarith, fun s hs => ?_, fun s hs => ?_, fun s hs => ?_⟩
    · have := hsign s hs; nlinarith
    · have := hmono s hs; nlinarith
    · have := hmax s hs; nlinarith
  · refine ⟨1, by norm_num, m, hm, by nlinarith, fun s hs => ?_, fun s hs => ?_, fun s hs => ?_⟩
    · have := hsign s hs; nlinarith
    · have := hmono s hs; nlinarith
    · have := hmax s hs; nlinarith

end Cvs.Prolate.EndpointLadder
