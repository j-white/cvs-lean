import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.FullTailConvergence
import Cvs.L2a.L1FullTailWinfBound
import Cvs.L2a.PositionTailAdmissible
import Cvs.L2a.PositionTruncatedTail
import Cvs.L2a.SpectralMassLevelLeak
import Cvs.L2a.TailLogScaleTest
import Cvs.Prolate.EdgeLayerDerivativeMass
import Cvs.Prolate.Envelope.FarRadialDerivative
import Cvs.Prolate.Gram.RungGramFloorAtInfinity
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.LiouvilleGreen.SoninFunction
import Cvs.Prolate.SincTopIsRung
import Cvs.Prolate.SlepianCommutingRelation
import Cvs.Prolate.TruncatedTailAboveOrbit
import Cvs.Prolate.TruncatedTailEdgeIntegral
import Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous
import Cvs.WeilForm.SelfConvolutionTransform

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The high spectral mass of a low prolate rung's truncated tail

For an angular prolate rung with `c ≥ 100` and `0 ≤ χ ≤ (2/5)c²`, for every `k > 1`,
`∫_{θ>1} F_k² − specMass F_k (2ck) ≤ Khigh(c)·ψ(1)²·k^{-1/2}`, where `F_k = posTail ψ k`.
-/

noncomputable section

open Real Set MeasureTheory
open scoped FourierTransform

namespace Cvs.L2a.LowRungHighSpectralMass

open Cvs.L2a.AngularProlateTailPositive (psi)
open Cvs.Prolate.SlepianCommutingRelation (kint)
open Cvs.L2a.PositionTruncatedTail (posTail)
open Cvs.L2a.SpectralMassLevelLeak (specMass)

/-- The high-mass constant at unit edge value. -/
def Khigh (c : ℝ) : ℝ :=
  ((6 + 4 * (4 * (2 ^ (-(3/4) : ℝ) * √(96 * exp 1 * c)))) ^ 2 + 74 ^ 2 * (48 * exp 1 / c) * 25) / c

/-- **The high mass of a truncated tail**: `∫_{θ>1} F_k² − specMass F_k (2ck) ≤ Khigh(c)·ψ(1)²·k^{-1/2}`. -/
theorem highMass_le {g g₁ g₂ : ℝ → ℝ} {c χ : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hc : 100 ≤ c) (hχ0 : 0 ≤ χ) (hχ : χ ≤ 2 / 5 * c ^ 2) {k : ℝ} (hk : 1 < k) :
    (∫ θ in Ioi 1, posTail (psi c g) k θ ^ 2) - specMass (posTail (psi c g) k) (k * (2 * c))
      ≤ Khigh c * psi c g 1 ^ 2 * k ^ (-(1 / 2) : ℝ) := by
  have hc0 : 0 < c := by linarith
  have hk0 : 0 < k := by linarith
  have hχc : χ < c ^ 2 := by nlinarith
  have hgc : ContinuousOn g (uIcc (-1) 1) := fun s hs => (hg s hs).continuousAt.continuousWithinAt
  obtain ⟨hψs, hvs, hode⟩ := Cvs.L2a.AngularProlateTailPositive.psi_system hg hg₁ hg₂c hang
  obtain ⟨hψ, hu, hψc, -⟩ := Cvs.Prolate.Gram.RungGramFloorAtInfinity.rung_system hg hg₁ hg₂c hang
  set ψ := psi c g with hψdef
  set a := |ψ 1| with ha
  set a₁ := 4 * (2 ^ (-(3/4) : ℝ) * √(96 * exp 1 * c)) with ha₁
  set e := √(48 * exp 1 / c) with he
  have ha₁0 : 0 ≤ a₁ := by positivity
  have he2 : e ^ 2 = 48 * exp 1 / c := Real.sq_sqrt (by positivity)
  have ha2 : a ^ 2 = ψ 1 ^ 2 := sq_abs _
  have hP₀ : ∀ θ ∈ Icc (1 : ℝ) 2, |ψ θ| ≤ a := fun θ hθ => by
    have hs : ψ θ ^ 2 ≤ ψ 1 ^ 2 :=
      Cvs.Prolate.LiouvilleGreen.SoninFunction.prolate_sq_le_edge (ξ₁ := 2) hχc hθ (fun r _ => hψs r) (fun r _ => hvs r)
        (fun r _ => hode r)
    simpa using sq_le_sq.mp hs
  have hA₁ : ∫ θ in (1 : ℝ)..2, |kint g (fun ξ s => -(c * s * sin (c * ξ * s))) θ| ≤ a * a₁ := by
    have h := Cvs.Prolate.EdgeLayerDerivativeMass.integral_abs_deriv_le hg hg₁ hg₂c hang hc hχ0 hχ
    calc _ ≤ _ := h
      _ = a * a₁ := by rw [ha, ha₁]; ring
  have hψ₁ := fun ξ (_ : ξ ∈ Icc (1 : ℝ) 2) => Cvs.Prolate.SincTopIsRung.hasDerivAt_psi (c := c) hgc ξ
  have hψ₁c : ContinuousOn (kint g (fun ξ s => -(c * s * sin (c * ξ * s)))) (Icc 1 2) :=
    fun ξ _ => (Cvs.Prolate.SincTopIsRung.hasDerivAt_psi₁ (c := c) hgc ξ).continuousAt.continuousWithinAt
  have hE : ∀ ξ ∈ Icc 2 k, Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact.energy (Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval.aP c χ) ψ
      (Cvs.Prolate.Gram.RungGramFloorAtInfinity.rungU c g) ξ ≤ 48 * exp 1 * ψ 1 ^ 2 := fun ξ hξ =>
    Cvs.Prolate.Envelope.FarRadialDerivative.energy_far_le hg hg₁ hg₂c hang hc hχ0 hχ hξ.1
  -- the amplitude
  set A := a * (6 + 4 * a₁) + 74 * (a * e) * (1 + Real.log k) with hAd
  have hsq : √(48 * exp 1 * ψ 1 ^ 2 / c) = a * e := by
    have h0 : a = √(a ^ 2) := (Real.sqrt_sq (abs_nonneg _)).symm
    rw [he, h0, ← Real.sqrt_mul (sq_nonneg _), ha2]
    congr 1; ring
  have hfour : ∀ t, k * (2 * c) ≤ |t| →
      ‖𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf (Cvs.L2a.TailLogScaleTest.logScale (posTail ψ k))) (t / (2 * π))‖ ≤ A / |t| := by
    intro t ht
    have h2' : (2 * c * k) ^ 2 ≤ t ^ 2 := by
      rw [← sq_abs t]; exact pow_le_pow_left₀ (by positivity) (by linarith) 2
    have h := Cvs.Prolate.TruncatedTailEdgeIntegral.norm_fourier_posTail_le_hi' (Ebar := 48 * exp 1 * ψ 1 ^ 2) (P₀ := a)
      (A₁ := a * a₁) (t := t) (by linarith) hχ0 hχc.le hk.le (by nlinarith [sq_nonneg (c * k)]) hψc.continuousOn
      (fun ξ hξ => hψ ξ (by linarith [hξ.1])) (fun ξ _ => hu ξ) hE hψ₁ hψ₁c hP₀ hA₁
    refine h.trans (le_of_eq ?_)
    rw [hsq, hAd]; ring
  obtain ⟨h2, h1, -⟩ := Cvs.L2a.PositionTailAdmissible.admissible_posTail hk.le
    (Cvs.L2a.FullTailConvergence.contDiff_psi hgc c).contDiffOn
  have hmain := Cvs.Prolate.TruncatedTailAboveOrbit.highMass_le (fun θ hθ => Cvs.L2a.PositionTruncatedTail.posTail_zero _ k hθ) h2 h1
    (by positivity) hfour
  refine hmain.trans ?_
  -- `A²/(2ck) ≤ Khigh·a²·k^{-1/2}`
  have hL := Cvs.L2a.L1FullTailWinfBound.one_add_log_sq_le hk.le
  have hsk : k ^ (1 / 2 : ℝ) * k ^ (1 / 2 : ℝ) = k := by
    rw [← rpow_add hk0]; norm_num
  have hs1 : 1 ≤ k ^ (1 / 2 : ℝ) := one_le_rpow hk.le (by norm_num)
  have hA2 : A ^ 2 ≤ 2 * (a * (6 + 4 * a₁)) ^ 2 + 2 * (74 * (a * e) * (1 + Real.log k)) ^ 2 := by
    nlinarith [sq_nonneg (a * (6 + 4 * a₁) - 74 * (a * e) * (1 + Real.log k))]
  have hA2' : A ^ 2 ≤ 2 * a ^ 2 * ((6 + 4 * a₁) ^ 2 + 74 ^ 2 * e ^ 2 * 25 * k ^ (1 / 2 : ℝ)) := by
    refine hA2.trans ?_
    have : (74 * (a * e) * (1 + Real.log k)) ^ 2 ≤ 74 ^ 2 * a ^ 2 * e ^ 2 * (25 * k ^ (1 / 2 : ℝ)) := by
      rw [show (74 * (a * e) * (1 + Real.log k)) ^ 2 = 74 ^ 2 * a ^ 2 * e ^ 2 * (1 + Real.log k) ^ 2 by ring]
      exact mul_le_mul_of_nonneg_left hL (by positivity)
    nlinarith
  have hkey : (6 + 4 * a₁) ^ 2 + 74 ^ 2 * e ^ 2 * 25 * k ^ (1 / 2 : ℝ)
      ≤ ((6 + 4 * a₁) ^ 2 + 74 ^ 2 * e ^ 2 * 25) * k ^ (1 / 2 : ℝ) := by
    nlinarith [sq_nonneg (6 + 4 * a₁)]
  rw [Khigh, ← ha₁, ← he2, ← ha2, div_le_iff₀ (by positivity)]
  calc A ^ 2 ≤ 2 * a ^ 2 * ((6 + 4 * a₁) ^ 2 + 74 ^ 2 * e ^ 2 * 25 * k ^ (1 / 2 : ℝ)) := hA2'
    _ ≤ 2 * a ^ 2 * (((6 + 4 * a₁) ^ 2 + 74 ^ 2 * e ^ 2 * 25) * k ^ (1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = ((6 + 4 * a₁) ^ 2 + 74 ^ 2 * e ^ 2 * 25) / c * a ^ 2 * k ^ (-(1 / 2) : ℝ) * (k * (2 * c)) := by
        have hS0 : 0 < k ^ (1 / 2 : ℝ) := by linarith
        rw [show k ^ (-(1 / 2) : ℝ) = 1 / k ^ (1 / 2 : ℝ) by rw [rpow_neg hk0.le, inv_eq_one_div]]
        generalize k ^ (1 / 2 : ℝ) = S at hS0 hsk ⊢
        rw [← hsk]
        field_simp

end Cvs.L2a.LowRungHighSpectralMass
