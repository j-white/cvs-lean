import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.Prolate.Envelope.PointwiseEnergyEnvelopes
import Cvs.Prolate.Gram.OffDiagonalFromTails
import Cvs.Prolate.Gram.RungGramFloorAtInfinity
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyLower
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.RungAveragedTailIntegrated
import Cvs.Prolate.RungOrthogonalityAtInfinity

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The rungs' pairings on `[1, b]` from the averaged tail

For a rung beyond `b ≥ 2` with `W = w(b)` and energy growth `Γ = (1 + W/2)/(1 − W/2)·e^{W/(2−W)}`, Cvs.Prolate.RungAveragedTailIntegrated gives
`∫_b^tψ² ≤ T̄ = (G/(4c))log((b+1)/(b−1))(1 + κ_W) + G/(c²(b² − 1))` with `G = E(b)Γ` (when `E(b) = 0` the rung vanishes
beyond `b`); with `RungOrthogonalityAtInfinity`'s Wronskian bound at infinity, Cvs.Prolate.Gram.OffDiagonalFromTails gives `|∫₁ᵇψᵢψⱼ| ≤ √(T̄ᵢT̄ⱼ)` for distinct rungs.
-/

namespace Cvs.L2a.RungPairingsAveragedTail

open Real Set intervalIntegral MeasureTheory Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyLower Cvs.Prolate.Envelope.PointwiseEnergyEnvelopes Cvs.L2a.AngularProlateTailPositive Cvs.Prolate.RungOrthogonalityAtInfinity Cvs.Prolate.Gram.RungGramFloorAtInfinity Cvs.Prolate.Gram.OffDiagonalFromTails Cvs.Prolate.RungAveragedTailIntegrated

/-- The rung's energy growth factor beyond `b`. -/
noncomputable def growth (c χ b : ℝ) : ℝ :=
  (1 + wP c χ b / 2) / (1 - wP c χ b / 2) * exp (wP c χ b / (2 - wP c χ b))

/-- The averaged tail bound of a rung beyond `b`. -/
noncomputable def avgTail (c χ : ℝ) (g : ℝ → ℝ) (b : ℝ) : ℝ :=
  energy (aP c χ) (psi c g) (rungU c g) b * growth c χ b / (4 * c) * log ((b + 1) / (b - 1))
      * (1 + wP c χ b / 2 * (1 + wP c χ b / 2) / (1 - wP c χ b / 2))
    + energy (aP c χ) (psi c g) (rungU c g) b * growth c χ b / (c ^ 2 * (b ^ 2 - 1))

theorem growth_pos {c χ b : ℝ} (hW : wP c χ b < 2) (hW0 : 0 ≤ wP c χ b) : 0 < growth c χ b := by
  unfold growth
  have : 0 < 1 - wP c χ b / 2 := by linarith
  positivity

/-- **The averaged tail of a rung**: `∫_b^tψ² ≤ T̄` for every `t ≥ b`. -/
theorem tail_le_avgTail {g g₁ g₂ : ℝ → ℝ} {c χ b t : ℝ} (hc : 1 ≤ c) (hb : 2 ≤ b) (hbt : b ≤ t)
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hχ0 : 0 ≤ χ) (hχc : χ < c ^ 2) :
    ∫ ξ in b..t, psi c g ξ ^ 2 ≤ avgTail c χ g b := by
  obtain ⟨hψu, huu, hcψ, _⟩ := rung_system hg hg₁ hg₂c hang
  have hc0 : 0 < c := by linarith
  have hc2 : 0 < c ^ 2 := by positivity
  have hb1 : 1 < b := by linarith
  have hW := wP_lt_two hb hc hχ0 hχc
  have hW0 : 0 ≤ wP c χ b := (wP_pos hb1 hc2 hχc).le
  set E := energy (aP c χ) (psi c g) (rungU c g) with hEd
  have hψ' : ∀ ξ ∈ Icc b t, HasDerivAt (psi c g) (rungU c g ξ / pP ξ) ξ := fun ξ hξ =>
    hψu ξ (lt_of_lt_of_le hb1 hξ.1)
  have hu' : ∀ ξ ∈ Icc b t, HasDerivAt (rungU c g) (-(qP c χ ξ * psi c g ξ)) ξ := fun ξ _ => huu ξ
  have hEb0 : 0 ≤ E b := by
    have := aP_pos hb1 hc2 hχc
    simp only [hEd]; unfold energy; positivity
  have hG : ∀ ξ ∈ Icc b t, E ξ ≤ E b * growth c χ b := fun ξ hξ => by
    have := prolate_energy_le hb1 hξ.1 hc2 hχ0 hχc (fun r hr => hψ' r ⟨hr.1, hr.2.trans hξ.2⟩)
      (fun r hr => hu' r ⟨hr.1, hr.2.trans hξ.2⟩) hW
    have e : E b * growth c χ b = energy (aP c χ) (psi c g) (rungU c g) b * (1 + wP c χ b / 2)
        / (1 - wP c χ b / 2) * exp (wP c χ b / (2 - wP c χ b)) := by
      simp only [hEd]; unfold growth; ring
    rw [e]; exact this
  have hlog : 0 ≤ log ((b + 1) / (b - 1)) := by
    apply log_nonneg; rw [le_div_iff₀ (by linarith)]; linarith
  rcases eq_or_lt_of_le hEb0 with h0 | hpos
  · -- the rung vanishes beyond `b`
    have hzero : ∀ ξ ∈ Icc b t, psi c g ξ ^ 2 = 0 := fun ξ hξ => by
      have hEξ : E ξ ≤ 0 := by have := hG ξ hξ; rw [← h0] at this; simpa using this
      have ha := aP_pos (lt_of_lt_of_le hb1 hξ.1) hc2 hχc
      have h1 := sq_le_energy_div (ψ := psi c g) (u := rungU c g) ha
      have h2 : E ξ / aP c χ ξ ≤ 0 := div_nonpos_of_nonpos_of_nonneg hEξ ha.le
      have := sq_nonneg (psi c g ξ)
      simp only [hEd] at h2; linarith
    have hint : ∫ ξ in b..t, psi c g ξ ^ 2 = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun ξ hξ => by
        rw [uIcc_of_le hbt] at hξ; exact hzero ξ hξ]
      simp
    rw [hint]
    unfold avgTail; rw [← hEd, ← h0]; simp
  · -- positive energy throughout `[b, t]`
    have hEpos : ∀ ξ ∈ Icc b t, 0 < E ξ := fun ξ hξ => by
      have hge := prolate_energy_ge hb1 hξ.1 hc2 hχ0 hχc (fun r hr => hψ' r ⟨hr.1, hr.2.trans hξ.2⟩)
        (fun r hr => hu' r ⟨hr.1, hr.2.trans hξ.2⟩) hW
      have : 0 < E b * (1 - wP c χ b / 2) / (1 + wP c χ b / 2) * exp (-(wP c χ b / (2 - wP c χ b))) := by
        have : 0 < 1 - wP c χ b / 2 := by linarith
        positivity
      simp only [hEd] at hge this ⊢; linarith
    have h := tail_mass_le_avg (G := E b * growth c χ b) (W := wP c χ b) hc0 hχ0 hχc hb1 hbt hψ' hu' hEpos hG
      le_rfl hW
    unfold avgTail
    simp only [hEd] at h ⊢
    linarith

theorem avgTail_nonneg {g : ℝ → ℝ} {c χ b : ℝ} (hc : 1 ≤ c) (hb : 2 ≤ b) (hχ0 : 0 ≤ χ) (hχc : χ < c ^ 2) :
    0 ≤ avgTail c χ g b := by
  have hc0 : 0 < c := by linarith
  have hc2 : 0 < c ^ 2 := by positivity
  have hb1 : 1 < b := by linarith
  have hW := wP_lt_two hb hc hχ0 hχc
  have hW0 : 0 ≤ wP c χ b := (wP_pos hb1 hc2 hχc).le
  have hE : 0 ≤ energy (aP c χ) (psi c g) (rungU c g) b := by
    have := aP_pos hb1 hc2 hχc; unfold energy; positivity
  have hΓ := growth_pos hW hW0
  have hlog : 0 ≤ log ((b + 1) / (b - 1)) := by
    apply log_nonneg; rw [le_div_iff₀ (by linarith)]; linarith
  have h1 : 0 < 1 - wP c χ b / 2 := by linarith
  have hb2 : 0 < b ^ 2 - 1 := by nlinarith
  unfold avgTail
  positivity

/-- **The rungs' pairings on `[1, b]`**: `|∫₁ᵇψᵢψⱼ| ≤ √(T̄ᵢT̄ⱼ)` for distinct angular eigenvalues. -/
theorem rung_pair_le {gi gi₁ gi₂ gj gj₁ gj₂ : ℝ → ℝ} {c χi χj b : ℝ} (hc : 1 ≤ c) (hb : 2 ≤ b)
    (hgi : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt gi (gi₁ s) s)
    (hgi₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt gi₁ (gi₂ s) s) (hgi₂c : ContinuousOn gi₂ (uIcc (-1) 1))
    (hangi : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * gi₂ s - 2 * s * gi₁ s - c ^ 2 * s ^ 2 * gi s + χi * gi s = 0)
    (hgj : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt gj (gj₁ s) s)
    (hgj₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt gj₁ (gj₂ s) s) (hgj₂c : ContinuousOn gj₂ (uIcc (-1) 1))
    (hangj : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * gj₂ s - 2 * s * gj₁ s - c ^ 2 * s ^ 2 * gj s + χj * gj s = 0)
    (hχi0 : 0 ≤ χi) (hχic : χi < c ^ 2) (hχj0 : 0 ≤ χj) (hχjc : χj < c ^ 2) (hχ : χi ≠ χj) :
    |∫ ξ in (1 : ℝ)..b, psi c gi ξ * psi c gj ξ| ≤ √(avgTail c χi gi b * avgTail c χj gj b) := by
  have hc0 : 0 < c := by linarith
  have hb1 : (1 : ℝ) ≤ b := by linarith
  obtain ⟨_, _, hci, _⟩ := rung_system hgi hgi₁ hgi₂c hangi
  obtain ⟨_, _, hcj, _⟩ := rung_system hgj hgj₁ hgj₂c hangj
  refine abs_integral_le_tails (K := wronskianConst c gi gi₁ gi₂ gj gj₁ gj₂ / |χi - χj|) hb1 hci.continuousOn
    hcj.continuousOn (fun t hbt => ?_) (fun t hbt => tail_le_avgTail hc hb hbt hgi hgi₁ hgi₂c hangi hχi0 hχic)
    (fun t hbt => tail_le_avgTail hc hb hbt hgj hgj₁ hgj₂c hangj hχj0 hχjc)
  rw [div_div]
  exact integral_psi_mul_le hgi hgi₁ hgi₂c hangi hgj hgj₁ hgj₂c hangj hc0 hχ (hb1.trans hbt)

end Cvs.L2a.RungPairingsAveragedTail
