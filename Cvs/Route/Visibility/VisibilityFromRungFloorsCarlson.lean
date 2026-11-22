import Mathlib
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.Approximant.SpineSubspace
import Cvs.Prolate.Gram.DeepRemainderCellFloors
import Cvs.Prolate.Gram.TunnellingFloorSumPlunge
import Cvs.Prolate.Gram.TwoCutLayerBound
import Cvs.Route.EvenWindowBulkCoupling
import Cvs.Route.Visibility.AliasRemainderCentreBound
import Cvs.Route.Visibility.AliasRemainderOffDiagonal
import Cvs.Route.Visibility.AliasTailThroughWindow
import Cvs.Route.Visibility.CaseFiniteCellFloorRates
import Cvs.Route.Visibility.CaseFiniteFromWindowChain
import Cvs.Route.Visibility.CellFloorFromConditionB
import Cvs.Route.Visibility.EvenBulkFloorFailsOffRh
import Cvs.Route.Visibility.ExtPairingRatesSubpoly
import Cvs.Route.Visibility.ExteriorTransformPointBound
import Cvs.Route.Visibility.LayerFloorDeepRemainderB
import Cvs.Route.Visibility.LogTailRateCellFloor
import Cvs.Route.Visibility.MOnePrimeTopDepth
import Cvs.Route.Visibility.PerRungBoxBound
import Cvs.Route.Visibility.RungXBoxExplicit
import Cvs.Route.Visibility.SummableBesselDisc
import Cvs.Route.Visibility.WindowBesselDiscBound
import Cvs.Route.Visibility.WindowChainCellFloors
import Cvs.StepA.Edge.CaseInfinityJointRates
import Cvs.StepA.Edge.DbarTransplantHolds
import Cvs.StepA.Edge.FiniteTopGap
import Cvs.StepA.Edge.FiniteTopIffFiniteBand
import Cvs.StepA.Edge.FreeInterpHolds
import Cvs.StepA.Edge.LemmaCFromCarlson
import Cvs.Zeta.GaussKernel.ZeroChain
import Cvs.Zeta.GaussKernel.ZetaZeroStatement
import Cvs.Zeta.ZeroCounting.ZeroDensityBlueprint

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# HV from the per-rung floors, the window inputs and Carlson

The wave-12 reductions composed: (EF′) from the three cell floors (Cvs.Prolate.Gram.DeepRemainderCellFloors), AL-R at `W̃ = 57/60` from the centre and
off-diagonal bounds (Cvs.Route.Visibility.AliasRemainderOffDiagonal), the tunnelling sum from its four inputs (Cvs.Prolate.Gram.TunnellingFloorSumPlunge), the box bound from the per-rung lemma
(Cvs.Route.Visibility.RungXBoxExplicit), (M1′) at `Θ' = ½` from the window log regularity (Cvs.Route.Visibility.WindowBesselDiscBound), Lemma C from Carlson (Cvs.StepA.Edge.LemmaCFromCarlson), and the transplant
and point interpolation (Cvs.StepA.Edge.DbarTransplantHolds, Cvs.StepA.Edge.FreeInterpHolds) give hV from (WF₂) or (WF′).
-/

noncomputable section
open Real Filter
open Cvs.ZeroCounting
open Cvs.StepA.Edge.CaseInfinityJointRates (M1Prime topDepth DbarTransplant FreeInterp LemmaC)
open Cvs.Route.L1FloorFromBulkD0 (Dom)
open Cvs.Route.WindowPositivityBulkCoupling (Qx)
open Cvs.L2a.EvenSectorReflectionBound (R1)
open Cvs.WeilForm.ReflectionEvenPositivityRH (Ev)
open scoped InnerProductSpace

namespace Cvs.Route.Visibility.VisibilityFromRungFloorsCarlson
open Cvs.ZeroCounting

/-- hV from the cell floors alone plus the non-floor inputs (`EvenBulkFloorFailsOffRh`'s proof with the floor as hypothesis). -/
theorem hV_of_cellFloor {η₀ : ℝ} (hη₀ : η₀ < 1)
    (hδ : ∀ᶠ x : ℕ in atTop, Cvs.Route.Visibility.CaseFiniteCellFloorRates.IsCellFloor x (Cvs.Route.Visibility.WindowChainCellFloors.cellFloor x η₀))
    {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1 / 2) (hTun : Cvs.Route.Visibility.CaseFiniteFromWindowChain.ExtTunnelSum η) (hP : Cvs.Route.Visibility.LogTailRateCellFloor.LogTailProfile η)
    (hBox : Cvs.Route.Visibility.PerRungBoxBound.RungBox 1)
    (hM : topDepth = 1 / 2 → M1Prime 1) (hD : DbarTransplant) (hI : FreeInterp) (hC : LemmaC) :
    ¬ RiemannHypothesis → ∀ᶠ x : ℕ in atTop, ¬ Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x 0 := by
  obtain ⟨A, hA, hB⟩ := Cvs.Route.Visibility.SummableBesselDisc.exists_besselDiscS
  have hm : (1 : ℝ) ≤ 1 := le_rfl
  have hT : ∀ δ' : ℝ, 0 < δ' → δ' < 1 / 2 →
      Cvs.Route.Visibility.CaseFiniteCellFloorRates.LogTailRate (1 / 2 - (δ' + (1 / 2 - δ') / 2)) (1 / 2 + (δ' + (1 / 2 - δ') / 2)) :=
    fun δ' h0 h1 => Cvs.Route.Visibility.LogTailRateCellFloor.logTailRate_of_profile hη₀ hδ hTun hP (by linarith) (by linarith)
  obtain ⟨F, ν, hBx, hs⟩ := Cvs.Route.Visibility.PerRungBoxBound.rungBox_cellFloor hη₀ hBox
  have hEx : ∀ δ' : ℝ, 0 < δ' → δ' < 1 / 2 →
      Cvs.Route.Visibility.CaseFiniteCellFloorRates.ExtFloorSum (fun x => Cvs.Route.Visibility.WindowChainCellFloors.cellFloor x η₀) (1 / 2 + (δ' + (1 / 2 - δ') / 2)) :=
    fun δ' _ h1 => Cvs.Route.Visibility.CaseFiniteFromWindowChain.extFloorSum_of_tunnel (by linarith) hη0 hη1 hη₀ hTun
  have hh := Cvs.Route.Visibility.CaseFiniteCellFloorRates.caseF_h_of_floor hδ (fun S _ _ => Cvs.Route.Visibility.PerRungBoxBound.xFloorSum_of_box hm hBx hs S) hEx hT hA
    (Cvs.Route.Visibility.PerRungBoxBound.besselDisc_of_besselDiscS hB)
  have hSEP := Cvs.Route.Visibility.PerRungBoxBound.sepData_of_floor_box hδ hBx hs
  refine Cvs.Route.Visibility.EvenBulkFloorFailsOffRh.hV_of_m1_m2_of_jointRates hh fun hN => ?_
  have hM' : M1Prime 1 := by
    rcases lt_or_eq_of_le (Cvs.StepA.Edge.CaseInfinityJointRates.topDepth_le_half hN.1) with hlt | heq
    · have h0 := Cvs.StepA.Edge.CaseInfinityJointRates.topDepth_pos hN.1
      obtain ⟨μ, hμ, hμ0, hμs⟩ := hEx topDepth h0 hlt
      have hσ : 1 / 2 + (topDepth + (1 / 2 - topDepth) / 2) < 1 := by linarith
      exact Cvs.Route.Visibility.PerRungBoxBound.m1Prime_of_besselDiscS hA hB hN.1 hlt (Cvs.Route.Visibility.CaseFiniteCellFloorRates.psiRate_of_extRate hσ
        (Cvs.Route.Visibility.CaseFiniteCellFloorRates.extRate_of_floorSum hσ hδ hμ hμ0 hμs) (hT topDepth h0 hlt)) (by linarith)
    · exact hM heq
  exact Cvs.StepA.Edge.CaseInfinityJointRates.jointRates_of_caseInf (by linarith) hSEP hM' hD hI hC hN

/-- The wave-12 composition: every discharge substituted, (WF₂) in place of (WF′). -/
theorem hV_wave12 {T₀ C₁ η ν : ℝ} (hT₀ : T₀ < 1) (hW : Cvs.Prolate.Gram.TwoCutLayerBound.WFtwo (57 / 60) T₀)
    (hDp : Cvs.Prolate.Gram.DeepRemainderCellFloors.DeepCellFloor) (hBd : Cvs.Prolate.Gram.DeepRemainderCellFloors.BandCellFloor) (hTp : Cvs.Prolate.Gram.DeepRemainderCellFloors.TopPlungeFloor)
    (hZ : Cvs.Route.Visibility.AliasRemainderCentreBound.ZBound) (hO : Cvs.Route.Visibility.AliasTailThroughWindow.OffDiag C₁)
    (hK : Cvs.Prolate.Gram.TunnellingFloorSumPlunge.KRDCount) (hP : Cvs.Prolate.Gram.TunnellingFloorSumPlunge.PlungeLaw) (hCP : Cvs.Prolate.Gram.TunnellingFloorSumPlunge.CPbFloor) (hBF : Cvs.Prolate.Gram.TunnellingFloorSumPlunge.BandFloor)
    (hη0 : 0 < η) (hη1 : η < 1 / 2) (hLP : Cvs.Route.Visibility.LogTailRateCellFloor.LogTailProfile η)
    (hX : Cvs.Route.Visibility.RungXBoxExplicit.RungLemmaX) (hν : ν < 1) (hWR : Cvs.Route.Visibility.MOnePrimeTopDepth.WinLogReg ν)
    (hCarl : Cvs.Zeta.ZeroCounting.ZeroDensityBlueprint.CarlsonBound) :
    ¬ RiemannHypothesis → ∀ᶠ x : ℕ in atTop, ¬ Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x 0 := by
  have hE := Cvs.Prolate.Gram.DeepRemainderCellFloors.efprime_of_cellFloors hDp hBd hTp hT₀
  have hR := Cvs.Route.Visibility.AliasRemainderOffDiagonal.alr_of_offDiag hZ hO
  have hTun := Cvs.Prolate.Gram.TunnellingFloorSumPlunge.extTunnelSum_of_floors hK hP hCP hBF hη0.le
  obtain ⟨η₀, -, hη₀, hδ⟩ := Cvs.Route.Visibility.CellFloorFromConditionB.isCellFloor_of_condB (Cvs.Prolate.Gram.TwoCutLayerBound.condB_of_wfTwo_ef hW hE) hR
  exact hV_of_cellFloor hη₀ hδ hη0 hη1 hTun hLP (Cvs.Route.Visibility.RungXBoxExplicit.rungBox_one_of_lemmaX ⟨η, hη0, hη1, hTun⟩ hX)
    (Cvs.Route.Visibility.WindowBesselDiscBound.m1PrimeHalf_of_winLogReg hWR hν) Cvs.StepA.Edge.DbarTransplantHolds.dbarTransplant Cvs.StepA.Edge.FreeInterpHolds.freeInterp
    (Cvs.StepA.Edge.LemmaCFromCarlson.lemmaC_of_carlson hCarl)

end Cvs.Route.Visibility.VisibilityFromRungFloorsCarlson

end
