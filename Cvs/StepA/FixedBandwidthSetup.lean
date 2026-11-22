import Mathlib
import Cvs.StepA.DepthToZero
import Cvs.StepA.Edge.BandTopGap
import Cvs.StepA.Edge.EdgeDiscriminant
import Cvs.StepA.Edge.EdgePositivity
import Cvs.StepA.Edge.FiniteTopDiscriminant
import Cvs.StepA.Edge.FiniteTopGap
import Cvs.StepA.Edge.TopSetCriterion
import Cvs.StepA.OddBottomGapCriterion
import Cvs.StepA.OddTrialErrorBudget
import Cvs.StepA.StepAAlongBandwidth
import Cvs.StepA.StepACountDischarged
import Cvs.StepA.StepACriterion
import Cvs.Zeta.GaussKernel.ZetaZeroStatement
import Cvs.Zeta.ZeroSideMoments

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Step (a) along every fixed bandwidth as an RH criterion

Along the mode count `band Ω L = ⌈ΩL/2π⌉₊`, an edge-positive finite top set refutes step (a) at every
large bandwidth (Cvs.StepA.Edge.BandTopGap), and every finite family is edge positive (`EdgePositivity`). So RH holds iff step (a)
holds along every fixed bandwidth and `DepthToZero` holds, given odd bottom eigenpairs below every
ordinate along each bandwidth `Ω ≥ 6.24` under RH.
-/

noncomputable section

open Real Filter Topology

namespace Cvs.StepA.FixedBandwidthSetup
open Cvs.ZeroCounting

open Cvs.Zeta.GaussKernel.AdmissibleKernel (nonTrivialZeroSet)
open Cvs.StepA.OddBottomGapCriterion (OddBottomBelow)
open Cvs.StepA.Edge.FiniteTopGap (FiniteTop)
open Cvs.StepA.Edge.FiniteTopDiscriminant (EdgePositive)
open Cvs.StepA.Edge.TopSetCriterion (TopSet BandTopGap)
open Cvs.StepA.StepAAlongBandwidth (StepAAlong)

/-- The fixed-bandwidth mode count `⌈ΩL/2π⌉₊`. -/
abbrev band (Ω : ℝ) : ℝ → ℕ := fun L => ⌈Ω * L / (2 * π)⌉₊

/-- Odd bottom eigenpairs below every ordinate along `band Ω`, at all large integer scales. -/
def FixBelow (Ω : ℝ) : Prop :=
  ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x → 0 < Real.log x → OddBottomBelow (Real.log x) (band Ω (Real.log x))

/-- Under RH, `FixBelow Ω` for every bandwidth `Ω ≥ 6.24`. -/
def HFixAbove : Prop := RiemannHypothesis → ∀ Ω : ℝ, 6.24 ≤ Ω → FixBelow Ω

/-- Off RH, some top set has a band top gap at some positive bandwidth. -/
def EBand : Prop :=
  ¬ RiemannHypothesis → ∃ Ω : ℝ, 0 < Ω ∧
    ∃ (S : Set nonTrivialZeroSet) (δ : ℝ), TopSet S δ ∧ BandTopGap S δ Ω

/-- Under RH, `FixBelow Ω` gives step (a) along `band Ω`. -/
theorem stepAAlong_of_fixBelow (hRH : RiemannHypothesis) {Ω : ℝ} (h : FixBelow Ω) :
    ∃ x₀ : ℕ, StepAAlong (band Ω) x₀ := by
  obtain ⟨x₀, hx₀⟩ := h
  exact ⟨x₀, fun x hx hlx =>
    Cvs.StepA.StepACountDischarged.oddAbove_of_RH_of_oddBottomBelow hRH hlx (hx₀ x hx hlx)⟩

/-- Under RH and `HFixAbove`, step (a) holds along every positive fixed bandwidth. -/
theorem stepAAlong_of_RH (hH : HFixAbove) (hRH : RiemannHypothesis) {Ω : ℝ} (hΩ : 0 < Ω) :
    ∃ x₀ : ℕ, StepAAlong (band Ω) x₀ := by
  rcases lt_or_ge Ω 6.24 with h | h
  · exact Cvs.StepA.StepAAlongBandwidth.exists_stepAAlong_of_RH hRH hΩ.le h
      (fun ρ => (Cvs.StepA.StepACriterion.lt_abs_im ρ).le)
  · exact stepAAlong_of_fixBelow hRH (hH hRH Ω h)

/-- Every finite top set is edge positive. -/
theorem edgePositive_of_finiteTop {S : Finset nonTrivialZeroSet} {δ : ℝ} (hS : FiniteTop S δ) :
    EdgePositive S δ :=
  Cvs.StepA.Edge.FiniteTopDiscriminant.edgePositive_of_edgePositiveFamilies
    Cvs.StepA.Edge.PlanarBoxLemma.edgePositiveFamilies hS

/-- A finite top set off RH gives `EBand`. -/
theorem eBand_of_finiteTop
    (hT : ¬ RiemannHypothesis → ∃ (S : Finset nonTrivialZeroSet) (δ : ℝ), FiniteTop S δ) :
    EBand := fun h => by
  obtain ⟨S, δ, hS⟩ := hT h
  obtain ⟨L₀, hpos⟩ := edgePositive_of_finiteTop hS
  obtain ⟨Ω, hm⟩ := (Cvs.StepA.Edge.BandTopGap.eventually_headMargin_of_finiteTop hS hpos).exists
  exact ⟨Ω, hm.2.2.1, S, δ, hm.1, Cvs.StepA.Edge.BandTopGap.bandTopGap_of_margin hm⟩

/-- **RH iff step (a) along every positive fixed bandwidth**, given `HFixAbove` and `EBand`. -/
theorem riemannHypothesis_iff_forall_of_eBand (hH : HFixAbove) (hE : EBand) :
    RiemannHypothesis ↔ ∀ Ω : ℝ, 0 < Ω → ∃ x₀ : ℕ, StepAAlong (band Ω) x₀ := by
  refine ⟨fun hRH Ω hΩ => stepAAlong_of_RH hH hRH hΩ, fun hA => ?_⟩
  by_contra hRH
  obtain ⟨Ω, hΩ, S, δ, hS, hG⟩ := hE hRH
  obtain ⟨x₀, hx₀⟩ := hA Ω hΩ
  exact Cvs.StepA.StepAAlongBandwidth.not_stepAAlong_of_bandTopGap hS hΩ hG x₀ hx₀

/-- **RH iff step (a) along every positive fixed bandwidth**, given a finite top set off RH and
`HFixAbove`. -/
theorem riemannHypothesis_iff_forall_of_finiteTop
    (hT : ¬ RiemannHypothesis → ∃ (S : Finset nonTrivialZeroSet) (δ : ℝ), FiniteTop S δ)
    (hH : HFixAbove) :
    RiemannHypothesis ↔ ∀ Ω : ℝ, 0 < Ω → ∃ x₀ : ℕ, StepAAlong (band Ω) x₀ :=
  riemannHypothesis_iff_forall_of_eBand hH (eBand_of_finiteTop hT)

/-- **RH iff step (a) along every positive fixed bandwidth and `DepthToZero`**, given
`HFixAbove`. -/
theorem riemannHypothesis_iff_forall_and_depthToZero (hH : HFixAbove) :
    RiemannHypothesis ↔
      (∀ Ω : ℝ, 0 < Ω → ∃ x₀ : ℕ, StepAAlong (band Ω) x₀) ∧ Cvs.StepA.DepthToZero.DepthToZero := by
  refine ⟨fun hRH => ⟨fun Ω hΩ => stepAAlong_of_RH hH hRH hΩ,
    Cvs.StepA.DepthToZero.depthToZero_of_RH hRH⟩, fun ⟨hA, hD⟩ => ?_⟩
  exact (riemannHypothesis_iff_forall_of_finiteTop
    (Cvs.StepA.DepthToZero.exists_finiteTop_of_depthToZero hD) hH).mpr hA

end Cvs.StepA.FixedBandwidthSetup
