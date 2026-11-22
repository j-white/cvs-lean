import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.FrameFloorMirror
import Cvs.L2a.MirrorFloor
import Cvs.L2a.PositionTruncatedTail
import Cvs.Prolate.AngularEdgeValueNonzero
import Cvs.Prolate.CorrectedEnergyAntitone
import Cvs.Prolate.Gram.RungGramFloorAtInfinity
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.RungConnectionIdentity
import Cvs.Prolate.RungEdgeCorrectedEnergy
import Cvs.Prolate.RungMirrorIdentity
import Cvs.Prolate.RungOrthogonalityAtInfinity
import Cvs.Upstream.CosineTransformHalfLine

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The concentration half of `H_τ`

For a rung with `c ≥ 80`, `χ ≥ 0`, `c² − χ ≥ 5c`: `E ≤ (11/10)ψ(1)²` beyond `ξ₀ = 1 + 1/(2(c² − χ))` (Cvs.Prolate.CorrectedEnergyAntitone, Cvs.Prolate.RungEdgeCorrectedEnergy), so
`(g(1) + g(−1))² ≤ (11/10) c ψ(1)²` by `RungConnectionIdentity`'s limit; for `g` even and `≢ 0` (Cvs.Prolate.AngularEdgeValueNonzero) this gives `λ = (c/2π)μ² ≥ 20/(11π)`
and, when `ψ(1)g(1) > 0`, `1 − ε_τ ≤ τ = μ√(c/2π) ≤ 1` (Cvs.Prolate.RungMirrorIdentity) with `ε_τ = 1 − √(20/(11π))`. With it `FrameFloorMirror`'s
`FF_mirror_lt_nine` holds on spans of such rungs with `β = η + ε_τ`.
-/

noncomputable section

open MeasureTheory Set Real Filter Topology Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.AngularProlateTailPositive Cvs.Prolate.Gram.RungGramFloorAtInfinity Cvs.L2a.PositionTruncatedTail Cvs.Upstream.CosineTransformHalfLine
open Cvs.L2a.MirrorFloor (muBeta)

namespace Cvs.L2a.MirrorConcentrationHalf

/-- The concentration defect `ε_τ = 1 − √(20/(11π))`. -/
def epsTau : ℝ := 1 - √(20 / (11 * π))

/-- `0 ≤ ε_τ`. -/
theorem epsTau_nonneg : 0 ≤ epsTau := by
  have h : 20 / (11 * π) ≤ 1 := by
    rw [div_le_one (by positivity)]; nlinarith [Real.pi_gt_three]
  have := Real.sqrt_le_one.mpr h
  unfold epsTau; linarith

/-- `ε_τ < 0.24`. -/
theorem epsTau_lt : epsTau < 0.24 := by
  have h : (0.76 : ℝ) ^ 2 < 20 / (11 * π) := by
    rw [lt_div_iff₀ (by positivity)]; nlinarith [Real.pi_lt_d4]
  have := (Real.lt_sqrt (by norm_num)).mpr h
  unfold epsTau; linarith

/-- **The rung energy is at most `(11/10)ψ(1)²` beyond `ξ₀ = 1 + 1/(2(c² − χ))`**, for `c ≥ 80`, `χ ≥ 0`,
`c² − χ ≥ 5c`. -/
theorem energy_le_far {g g₁ g₂ : ℝ → ℝ} {c χ : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hc : 80 ≤ c) (hχ0 : 0 ≤ χ) (hD : 5 * c ≤ c ^ 2 - χ) {ξ : ℝ}
    (hξ : 1 + 1 / (2 * (c ^ 2 - χ)) ≤ ξ) :
    energy (aP c χ) (psi c g) (rungU c g) ξ ≤ 11 / 10 * psi c g 1 ^ 2 := by
  set ξ₀ := 1 + 1 / (2 * (c ^ 2 - χ)) with hξ₀
  have hc0 : 0 < c := by linarith
  have hc2 : 0 < c ^ 2 := by positivity
  have hDpos : 0 < c ^ 2 - χ := by nlinarith
  have hχc : χ < c ^ 2 := by linarith
  have h1 : 1 < ξ₀ := by
    have : 0 < 1 / (2 * (c ^ 2 - χ)) := by positivity
    linarith
  obtain ⟨hW, hN⟩ := Cvs.Prolate.CorrectedEnergyAntitone.eeb_constant hc hχ0 hD hξ₀
  obtain ⟨hψ, hu, -, -⟩ := rung_system hg hg₁ hg₂c hang
  have hE := Cvs.Prolate.CorrectedEnergyAntitone.prolate_energy_le_corrected h1 hξ hc2 hχ0 hχc
    (fun t ht => hψ t (lt_of_lt_of_le h1 ht.1)) (fun t _ => hu t) (by linarith)
  have hH := Cvs.Prolate.RungEdgeCorrectedEnergy.edge_corrected_energy_le hc0 hχ0 hχc hg hg₁ hg₂c hang h1
  have hden : 0 < 1 - wP c χ ξ₀ / 2 := by linarith
  calc energy (aP c χ) (psi c g) (rungU c g) ξ
      ≤ (energy (aP c χ) (psi c g) (rungU c g) ξ₀ + wP c χ ξ₀ * (psi c g ξ₀ * rungU c g ξ₀))
          / (1 - wP c χ ξ₀ / 2) := hE
    _ ≤ psi c g 1 ^ 2 * ((1 + 2 * c ^ 2 * ξ₀ * (ξ₀ - 1) / (c ^ 2 - χ)) * aP c χ ξ₀
          - wP c χ ξ₀ * (ξ₀ - 1) * qP c χ ξ₀) / (1 - wP c χ ξ₀ / 2) :=
        div_le_div_of_nonneg_right hH hden.le
    _ = psi c g 1 ^ 2 * (((1 + 2 * c ^ 2 * ξ₀ * (ξ₀ - 1) / (c ^ 2 - χ)) * aP c χ ξ₀
          - wP c χ ξ₀ * (ξ₀ - 1) * qP c χ ξ₀) / (1 - wP c χ ξ₀ / 2)) := mul_div_assoc _ _ _
    _ ≤ psi c g 1 ^ 2 * (11 / 10) := mul_le_mul_of_nonneg_left hN (sq_nonneg _)
    _ = 11 / 10 * psi c g 1 ^ 2 := mul_comm _ _

/-- **The amplitude is concentrated at the edge**: for a rung with `c ≥ 80`, `χ ≥ 0`, `c² − χ ≥ 5c`,
`(g(1) + g(−1))² ≤ (11/10) c ψ(1)²`. -/
theorem ampl_sq_le {g g₁ g₂ : ℝ → ℝ} {c χ : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hc : 80 ≤ c) (hχ0 : 0 ≤ χ) (hD : 5 * c ≤ c ^ 2 - χ) :
    (g 1 + g (-1)) ^ 2 ≤ 11 / 10 * c * psi c g 1 ^ 2 := by
  have hc0 : 0 < c := by linarith
  have hχc : χ < c ^ 2 := by nlinarith
  have hlim := Cvs.Prolate.RungConnectionIdentity.tendsto_energy hg hg₁ hg₂c hc0 hχ0 hχc
  have hle : Cvs.Prolate.RungOrthogonalityAtInfinity.ampl g ^ 2 / c ≤ 11 / 10 * psi c g 1 ^ 2 :=
    le_of_tendsto hlim ((eventually_ge_atTop (1 + 1 / (2 * (c ^ 2 - χ)))).mono
      fun ξ hξ => energy_le_far hg hg₁ hg₂c hang hc hχ0 hD hξ)
  rw [div_le_iff₀ hc0] at hle
  unfold Cvs.Prolate.RungOrthogonalityAtInfinity.ampl at hle
  linarith

/-- **The concentration half of `H_τ`**: for an even rung `g ≢ 0` with `psi c g = μ g` on `[−1, 1]`, `c ≥ 80`,
`χ ≥ 0`, `c² − χ ≥ 5c`: `(g(1) + g(−1))² ≤ (11/10) c ψ(1)²`, `λ = (c/2π)μ² ≥ 20/(11π)`, and if `ψ(1)g(1) > 0` then
`1 − ε_τ ≤ μ√(c/2π) ≤ 1`. -/
theorem htau_concentration {g g₁ g₂ : ℝ → ℝ} {c χ μ : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hc : 80 ≤ c) (hχ0 : 0 ≤ χ) (hD : 5 * c ≤ c ^ 2 - χ)
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) (hg0 : ∃ s ∈ Icc (-1 : ℝ) 1, g s ≠ 0)
    (hμ : ∀ s ∈ Icc (-1 : ℝ) 1, psi c g s = μ * g s) :
    (g 1 + g (-1)) ^ 2 ≤ 11 / 10 * c * psi c g 1 ^ 2 ∧ 20 / (11 * π) ≤ c / (2 * π) * μ ^ 2
      ∧ (0 < psi c g 1 * g 1 → 1 - epsTau ≤ μ * √(c / (2 * π)) ∧ μ * √(c / (2 * π)) ≤ 1) := by
  have hc0 : 0 < c := by linarith
  have h1 : (1 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, le_rfl⟩
  have hA := ampl_sq_le hg hg₁ hg₂c hang hc hχ0 hD
  obtain ⟨s₀, hs₀, hgs₀⟩ := hg0
  have hg1 : g 1 ≠ 0 := Cvs.Prolate.AngularEdgeValueNonzero.edge_ne_zero hg hg₁ hang hs₀ hgs₀
  have hAeq : g 1 + g (-1) = 2 * g 1 := by rw [heven 1 h1]; ring
  have hApos : 0 < (g 1 + g (-1)) ^ 2 := by
    rw [hAeq]; have := pow_pos (abs_pos.mpr hg1) 2
    rw [sq_abs] at this; nlinarith
  have hP : 0 < psi c g 1 ^ 2 := by
    by_contra h
    have : psi c g 1 ^ 2 = 0 := le_antisymm (not_lt.mp h) (sq_nonneg _)
    rw [this] at hA; linarith
  have hconn := Cvs.Prolate.RungConnectionIdentity.connection_identity hc0.ne' heven hμ
  unfold Cvs.Prolate.RungOrthogonalityAtInfinity.ampl at hconn
  have hA' : (g 1 + g (-1)) ^ 2 / c ≤ 11 / 10 * psi c g 1 ^ 2 := by
    rw [div_le_iff₀ hc0]; linarith
  have hlam0 : 0 ≤ c / (2 * π) * μ ^ 2 := by positivity
  have hlam : 20 / (11 * π) ≤ c / (2 * π) * μ ^ 2 := by
    have h2 : 2 / π * psi c g 1 ^ 2 ≤ c / (2 * π) * μ ^ 2 * (11 / 10 * psi c g 1 ^ 2) := by
      rw [← hconn]; exact mul_le_mul_of_nonneg_left hA' hlam0
    have h3 : 2 / π ≤ c / (2 * π) * μ ^ 2 * (11 / 10) := by
      have := (mul_le_mul_iff_left₀ hP).mp (by linarith : 2 / π * psi c g 1 ^ 2
        ≤ c / (2 * π) * μ ^ 2 * (11 / 10) * psi c g 1 ^ 2)
      exact this
    rw [div_le_iff₀ (by positivity)]
    have : 2 / π * π = 2 := div_mul_cancel₀ _ Real.pi_ne_zero
    nlinarith [Real.pi_pos]
  refine ⟨hA, hlam, fun hsign => ⟨?_, ?_⟩⟩
  · have hμpos : 0 < μ := by
      rw [hμ 1 h1] at hsign
      by_contra h
      have : μ * g 1 * g 1 ≤ 0 := by
        rw [mul_assoc]; exact mul_nonpos_of_nonpos_of_nonneg (not_lt.mp h) (mul_self_nonneg _)
      linarith
    have hτ0 : 0 ≤ μ * √(c / (2 * π)) := by positivity
    have hτ2 : (μ * √(c / (2 * π))) ^ 2 = c / (2 * π) * μ ^ 2 := by
      rw [mul_pow, sq_sqrt (by positivity)]; ring
    have : √(20 / (11 * π)) ≤ μ * √(c / (2 * π)) := (Real.sqrt_le_left hτ0).mpr (by rw [hτ2]; exact hlam)
    unfold epsTau; linarith
  · have hgc : ContinuousOn g (Icc (-1 : ℝ) 1) := fun s hs =>
      (hg s (by rw [uIcc_of_le (by norm_num)]; exact hs)).continuousAt.continuousWithinAt
    exact (le_abs_self _).trans
      (Cvs.Prolate.RungMirrorIdentity.abs_tau_le_one hc0 hgc heven hμ ⟨s₀, hs₀, hgs₀⟩)

/-- **`H_τ` from the sign**: for an even rung `g ≢ 0` with `psi c g = μ g`, `c ≥ 80`, `χ ≥ 0`, `c² − χ ≥ 5c` and
`ψ(1)g(1) > 0`, `1 − ε_τ ≤ μ√(c/2π)`. -/
theorem tau_ge_of_sign {g g₁ g₂ : ℝ → ℝ} {c χ μ : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hc : 80 ≤ c) (hχ0 : 0 ≤ χ) (hD : 5 * c ≤ c ^ 2 - χ)
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) (hg0 : ∃ s ∈ Icc (-1 : ℝ) 1, g s ≠ 0)
    (hμ : ∀ s ∈ Icc (-1 : ℝ) 1, psi c g s = μ * g s) (hsign : 0 < psi c g 1 * g 1) :
    1 - epsTau ≤ μ * √(c / (2 * π)) :=
  ((htau_concentration hg hg₁ hg₂c hang hc hχ0 hD heven hg0 hμ).2.2 hsign).1

/-- **The mirror floor below `9` from concentration**: `FrameFloorMirror`'s `FF_mirror_lt_nine` with `ε = ε_τ`, for a span of even
rungs `gᵢ ≢ 0` with `c ≥ 80`, `χᵢ ≥ 0`, `c² − χᵢ ≥ 5c` and `ψᵢ(1)gᵢ(1) > 0`. -/
theorem FF_mirror_concentrated {ι : Type*} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ μ : ι → ℝ}
    (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hσ : ∀ i, 5 * c ≤ c ^ 2 - χ i) (hχ : Function.Injective χ)
    (heven : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, g i (-s) = g i s) (hg0 : ∀ i, ∃ s ∈ Icc (-1 : ℝ) 1, g i s ≠ 0)
    (hμ : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, psi c (g i) s = μ i * g i s)
    (hsign : ∀ i, 0 < psi c (g i) 1 * g i 1)
    {w : ℝ → ℝ} (hwm : Measurable w) (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∀ x, w x ≤ 1)
    {X : ℝ} (hX : 1 ≤ X) (hX9 : X < 9) (hwX : ∀ x, X ≤ x → w x = 1)
    {η : ℝ} (hη0 : 0 ≤ η)
    (hη : ∫ y in Ioi 1, ‖(w y : ℂ) * calK c ((Ioi 1).indicator fun x =>
        ((w x * ∑ i, a i * psi c (g i) x : ℝ) : ℂ)) y‖ ^ 2
      ≤ η ^ 2 * ∫ ξ in Ioi 1, (∑ i, a i * psi c (g i) ξ) ^ 2)
    (hβ : η + epsTau < 1) :
    muBeta (η + epsTau) / 16.31 * ∑ i, a i ^ 2 * (∫ ξ in (1 : ℝ)..X, psi c (g i) ξ ^ 2)
      ≤ ∫ θ in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X θ ^ 2 :=
  Cvs.L2a.FrameFloorMirror.FF_mirror_lt_nine a hg hg₁ hg₂c hang (by linarith) hχ heven hμ epsTau_nonneg
    (fun i => tau_ge_of_sign (hg i) (hg₁ i) (hg₂c i) (hang i) hc (hχ0 i) (hσ i) (heven i) (hg0 i) (hμ i)
      (hsign i))
    hwm hw0 hw1 hX hX9 hwX hη0 hη hβ

end Cvs.L2a.MirrorConcentrationHalf
