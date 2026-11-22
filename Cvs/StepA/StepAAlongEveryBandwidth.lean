import Mathlib
import Cvs.StepA.DepthToZero
import Cvs.StepA.FixedBandwidthSetup
import Cvs.StepA.LatticeCondition
import Cvs.StepA.LatticeEventually
import Cvs.StepA.OddBottomFromLattice
import Cvs.StepA.OddBottomGapCriterion
import Cvs.StepA.StepAAlongBandwidth

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Step (a) along every fixed bandwidth is an RH criterion

Under RH, `LAT(L, ⌈ΩL/2π⌉)` holds for all large `L` and gives an odd bottom eigenpair below every
ordinate, so `Cvs.StepA.FixedBandwidthSetup.HFixAbove` holds. Hence RH holds iff step (a) holds along every positive fixed
bandwidth and `DepthToZero` holds.
-/

noncomputable section

open Real Filter Topology

namespace Cvs.Finite.OddDisplacementPencil
open Cvs.ZeroCounting

open Cvs.StepA.StepAAlongBandwidth (StepAAlong)

/-- **Under RH, every positive fixed bandwidth has odd bottom eigenpairs below every ordinate at
all large integer scales.** -/
theorem fixBelow_of_RH (hRH : RiemannHypothesis) {Ω : ℝ} (hΩ : 0 < Ω) :
    Cvs.StepA.FixedBandwidthSetup.FixBelow Ω := by
  have hlog : Tendsto (fun x : ℕ => Real.log x) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp (hlog.eventually (eventually_LAT hΩ))
  exact ⟨x₀, fun x hx hlx => oddBottomBelow_of_LAT hRH hlx (hx₀ x hx)⟩

/-- **`HFixAbove` holds.** -/
theorem hFixAbove : Cvs.StepA.FixedBandwidthSetup.HFixAbove := fun hRH _ hΩ =>
  fixBelow_of_RH hRH (by linarith)

/-- **RH iff step (a) along every positive fixed bandwidth `⌈ΩL/2π⌉` at all large integer scales,
and `DepthToZero`.** -/
theorem riemannHypothesis_iff_forall_stepAAlong_and_depthToZero :
    RiemannHypothesis ↔
      (∀ Ω : ℝ, 0 < Ω → ∃ x₀ : ℕ, StepAAlong (Cvs.StepA.FixedBandwidthSetup.band Ω) x₀) ∧
        Cvs.StepA.DepthToZero.DepthToZero :=
  Cvs.StepA.FixedBandwidthSetup.riemannHypothesis_iff_forall_and_depthToZero hFixAbove

end Cvs.Finite.OddDisplacementPencil
