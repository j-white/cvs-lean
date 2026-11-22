import Mathlib
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
import Cvs.Route.Visibility.LayerFloorDeepRemainderB
import Cvs.Route.Visibility.LogTailRateCellFloor
import Cvs.Route.Visibility.RungXBoxExplicit
import Cvs.Route.Visibility.VisibilityFromRungFloorsCarlson
import Cvs.Route.Visibility.WindowBesselDiscBound
import Cvs.Route.Visibility.WindowChainCellFloors
import Cvs.Route.Visibility.WindowLogEnergyCellFloor
import Cvs.StepA.Edge.DbarTransplantHolds
import Cvs.StepA.Edge.FreeInterpHolds
import Cvs.StepA.Edge.LemmaCFromCarlson
import Cvs.Zeta.ZeroCounting.ZeroDensityBlueprint

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# HV with the per-rung window log-tail law in place of the window log regularity

The wave-12 composition of Cvs.Route.Visibility.VisibilityFromRungFloorsCarlson with `WinLogReg 0` supplied by Cvs.Route.Visibility.WindowLogEnergyCellFloor from the route's own cell floor, the
tunnelling floor sum at the window exponent `η' ≥ 0` (Cvs.Prolate.Gram.TunnellingFloorSumPlunge) and `WinTailProfile η'`.
-/

noncomputable section
open Real Filter
open Cvs.ZeroCounting
open Cvs.Route.L1FloorFromBulkD0 (Dom)
open Cvs.Route.WindowPositivityBulkCoupling (Qx)
open Cvs.L2a.EvenSectorReflectionBound (R1)
open Cvs.WeilForm.ReflectionEvenPositivityRH (Ev)
open scoped InnerProductSpace

namespace Cvs.Route.Visibility.VisibilityWindowLogTail
open Cvs.ZeroCounting

/-- **hV from the per-rung window log-tail law**: `hV_wave12` with `WinTailProfile η'`, `0 ≤ η'`, in place of
`WinLogReg ν`. -/
theorem hV_wave13 {T₀ C₁ η η' : ℝ} (hT₀ : T₀ < 1) (hW : Cvs.Prolate.Gram.TwoCutLayerBound.WFtwo (57 / 60) T₀)
    (hDp : Cvs.Prolate.Gram.DeepRemainderCellFloors.DeepCellFloor) (hBd : Cvs.Prolate.Gram.DeepRemainderCellFloors.BandCellFloor) (hTp : Cvs.Prolate.Gram.DeepRemainderCellFloors.TopPlungeFloor)
    (hZ : Cvs.Route.Visibility.AliasRemainderCentreBound.ZBound) (hO : Cvs.Route.Visibility.AliasTailThroughWindow.OffDiag C₁)
    (hK : Cvs.Prolate.Gram.TunnellingFloorSumPlunge.KRDCount) (hP : Cvs.Prolate.Gram.TunnellingFloorSumPlunge.PlungeLaw) (hCP : Cvs.Prolate.Gram.TunnellingFloorSumPlunge.CPbFloor) (hBF : Cvs.Prolate.Gram.TunnellingFloorSumPlunge.BandFloor)
    (hη0 : 0 < η) (hη1 : η < 1 / 2) (hLP : Cvs.Route.Visibility.LogTailRateCellFloor.LogTailProfile η)
    (hX : Cvs.Route.Visibility.RungXBoxExplicit.RungLemmaX) (hη' : 0 ≤ η') (hWT : Cvs.Route.Visibility.WindowLogEnergyCellFloor.WinTailProfile η')
    (hCarl : Cvs.Zeta.ZeroCounting.ZeroDensityBlueprint.CarlsonBound) :
    ¬ RiemannHypothesis → ∀ᶠ x : ℕ in atTop, ¬ Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x 0 := by
  have hE := Cvs.Prolate.Gram.DeepRemainderCellFloors.efprime_of_cellFloors hDp hBd hTp hT₀
  have hR := Cvs.Route.Visibility.AliasRemainderOffDiagonal.alr_of_offDiag hZ hO
  have hTun := Cvs.Prolate.Gram.TunnellingFloorSumPlunge.extTunnelSum_of_floors hK hP hCP hBF hη0.le
  have hTun' := Cvs.Prolate.Gram.TunnellingFloorSumPlunge.extTunnelSum_of_floors hK hP hCP hBF hη'
  obtain ⟨η₀, -, hη₀, hδ⟩ := Cvs.Route.Visibility.CellFloorFromConditionB.isCellFloor_of_condB (Cvs.Prolate.Gram.TwoCutLayerBound.condB_of_wfTwo_ef hW hE) hR
  exact Cvs.Route.Visibility.VisibilityFromRungFloorsCarlson.hV_of_cellFloor hη₀ hδ hη0 hη1 hTun hLP (Cvs.Route.Visibility.RungXBoxExplicit.rungBox_one_of_lemmaX ⟨η, hη0, hη1, hTun⟩ hX)
    (Cvs.Route.Visibility.WindowBesselDiscBound.m1PrimeHalf_of_winLogReg (Cvs.Route.Visibility.WindowLogEnergyCellFloor.winLogReg_of_profile hη₀ hδ hTun' hWT) one_pos)
    Cvs.StepA.Edge.DbarTransplantHolds.dbarTransplant Cvs.StepA.Edge.FreeInterpHolds.freeInterp (Cvs.StepA.Edge.LemmaCFromCarlson.lemmaC_of_carlson hCarl)

end Cvs.Route.Visibility.VisibilityWindowLogTail

end
