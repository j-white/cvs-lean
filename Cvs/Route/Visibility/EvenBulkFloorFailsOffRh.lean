import Mathlib
import Cvs.Route.EvenWindowBulkCoupling
import Cvs.Route.Visibility.ExtPairingRatesSubpoly
import Cvs.Route.Visibility.ShareBesselFromExtPairing
import Cvs.StepA.Edge.CorrectedPairingUSums
import Cvs.StepA.Edge.DeepJointShare
import Cvs.StepA.Edge.FiniteTopCorrectedClosing
import Cvs.StepA.Edge.FiniteTopGap
import Cvs.StepA.Edge.FiniteTopIffFiniteBand
import Cvs.Zeta.GaussKernel.ZeroChain
import Cvs.Zeta.GaussKernel.ZetaZeroStatement

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# `hV` on route SEP: the eventual failure of the zero even bulk floor off RH

Off RH, either a finite top set exists (`TopAttained`) or `NoTop` holds (Cvs.StepA.Edge.FiniteTopIffFiniteBand). On a finite top set, M1 and M2 give
the exterior pairing and Bessel rates (Cvs.Route.Visibility.ExtPairingRatesSubpoly), hence `ShareBessel` (Cvs.Route.Visibility.ShareBesselFromExtPairing) and `PerpRates` (Cvs.StepA.Edge.CorrectedPairingUSums), and Cvs.StepA.Edge.FiniteTopCorrectedClosing closes
at all large `x`. On `NoTop`, the joint rates give `DeepJointShare` (Cvs.StepA.Edge.DeepJointShare), which closes at all large `x`. With route
SEP's inputs this is `hV`, in the `EvenBulkFloor` form and in `EvenBulkVisibility`'s visibility form, without the even floor.
-/

noncomputable section

open Real Filter
open Cvs.Zeta.GaussKernel.AdmissibleKernel (nonTrivialZeroSet)
open Cvs.StepA.Edge.FiniteTopGap (FiniteTop)
open Cvs.Route.Visibility.ExtPairingRatesSubpoly (M2Rate M1Rate)
open Cvs.Route.L1FloorFromBulkD0 (Dom)
open Cvs.Route.WindowPositivityBulkCoupling (Qx)
open Cvs.L2a.EvenSectorReflectionBound (R1)
open Cvs.WeilForm.ReflectionEvenPositivityRH (Ev)
open scoped InnerProductSpace

namespace Cvs.Route.Visibility.EvenBulkFloorFailsOffRh
open Cvs.ZeroCounting

/-- **A finite top set with M1 and M2 closes eventually**: the zero even bulk floor fails at all large `x`. -/
theorem eventually_not_evenBulkFloor_of_m1_m2 {S : Finset nonTrivialZeroSet} {δ : ℝ} (hS : FiniteTop S δ)
    (h : ∃ K Bess : ℕ → ℝ, M2Rate S δ K ∧ M1Rate δ Bess) :
    ∀ᶠ x : ℕ in atTop, ¬ Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x 0 := by
  obtain ⟨σ, hσ⟩ := hS.2.1
  obtain ⟨K, Bess, hK, hB⟩ := h
  exact Cvs.StepA.Edge.FiniteTopCorrectedClosing.eventually_not_evenBulkFloor_of_perpRates hS hσ (Cvs.StepA.Edge.CorrectedPairingUSums.perpRates_of_shareBessel hS hσ
    (Cvs.Route.Visibility.ShareBesselFromExtPairing.shareBessel_of_extPairing hS hσ (Cvs.Route.Visibility.ExtPairingRatesSubpoly.extPairingRate_of_m2Rate hK)
      (Cvs.Route.Visibility.ExtPairingRatesSubpoly.r1BesselRate_of_m1Rate hK hB)))

/-- **`NoTop` with the joint rates closes eventually**: the zero even bulk floor fails at all large `x`. -/
theorem eventually_not_evenBulkFloor_of_jointRates
    (hJ : ∃ σ : nonTrivialZeroSet, Cvs.GaussKernel.del σ ≠ 0 ∧
      ∃ (D : ℕ → Finset nonTrivialZeroSet) (r η : ℝ) (K : ℕ → ℝ), η < r ∧ Cvs.StepA.Edge.DeepJointShare.FreeShare σ D r
        ∧ Cvs.Route.Visibility.ShareBesselFromExtPairing.ExtPairingRate {σ} |Cvs.GaussKernel.del σ| K ∧ Cvs.StepA.Edge.DeepJointShare.AngleBound D η ∧ Cvs.StepA.Edge.DeepJointShare.ShallowRate σ D) :
    ∀ᶠ x : ℕ in atTop, ¬ Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x 0 := by
  obtain ⟨σ, hσ, D, r, η, K, hηr, hr, hK, hθ, hSh⟩ := hJ
  exact Cvs.StepA.Edge.DeepJointShare.eventually_not_evenBulkFloor_of_joint hσ (Cvs.StepA.Edge.DeepJointShare.deepJointShare_of_rates hr
    (Cvs.StepA.Edge.DeepJointShare.pairingRate_of_extPairingRate_offLine hσ (Finset.mem_singleton_self σ) hK) hθ hηr) hSh

/-- **`hV` from M1 and M2 on every finite top set and the joint rates in `NoTop`**. -/
theorem hV_of_m1_m2_of_jointRates
    (h : ∀ (S : Finset nonTrivialZeroSet) (δ : ℝ), FiniteTop S δ →
      ∃ K Bess : ℕ → ℝ, M2Rate S δ K ∧ M1Rate δ Bess)
    (hJ : Cvs.StepA.Edge.FiniteTopIffFiniteBand.NoTop → ∃ σ : nonTrivialZeroSet, Cvs.GaussKernel.del σ ≠ 0 ∧
      ∃ (D : ℕ → Finset nonTrivialZeroSet) (r η : ℝ) (K : ℕ → ℝ), η < r ∧ Cvs.StepA.Edge.DeepJointShare.FreeShare σ D r
        ∧ Cvs.Route.Visibility.ShareBesselFromExtPairing.ExtPairingRate {σ} |Cvs.GaussKernel.del σ| K ∧ Cvs.StepA.Edge.DeepJointShare.AngleBound D η ∧ Cvs.StepA.Edge.DeepJointShare.ShallowRate σ D) :
    ¬ RiemannHypothesis → ∀ᶠ x : ℕ in atTop, ¬ Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x 0 := fun hRH => by
  by_cases hT : Cvs.StepA.Edge.FiniteTopIffFiniteBand.TopAttained
  · obtain ⟨S, δ, hS⟩ := hT hRH
    exact eventually_not_evenBulkFloor_of_m1_m2 hS (h S δ hS)
  · exact eventually_not_evenBulkFloor_of_jointRates (hJ (Cvs.StepA.Edge.FiniteTopIffFiniteBand.not_topAttained_iff.mp hT))

end Cvs.Route.Visibility.EvenBulkFloorFailsOffRh

end
