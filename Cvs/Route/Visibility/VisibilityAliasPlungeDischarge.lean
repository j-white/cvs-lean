import Mathlib
import Cvs.Prolate.Gram.DeepRemainderCellFloors
import Cvs.Prolate.Gram.PlungeLawBandCellFloor
import Cvs.Prolate.Gram.TunnellingFloorSumPlunge
import Cvs.Prolate.Gram.TwoCutLayerBound
import Cvs.Prolate.Mellin.RungExteriorBoxBound
import Cvs.Prolate.TopPlungeFloor
import Cvs.Route.EvenWindowBulkCoupling
import Cvs.Route.Visibility.AliasOffDiagonalIncoherence
import Cvs.Route.Visibility.MOnePrimeTopDepth
import Cvs.Route.Visibility.PerRungLogTailLaw
import Cvs.Route.Visibility.SpineCentreTermBound
import Cvs.Route.Visibility.VisibilityFromRungFloorsCarlson
import Cvs.Route.Visibility.VisibilityWindowLogTail
import Cvs.Route.Visibility.WindowChainCellFloors
import Cvs.Route.Visibility.WindowLogEnergyCellFloor
import Cvs.Zeta.ZeroCounting.ZeroDensityBlueprint

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# HV after wave 13

Every wave-13 discharge substituted into `Cvs.Route.Visibility.VisibilityFromRungFloorsCarlson.hV_wave12` and `Cvs.Route.Visibility.VisibilityWindowLogTail.hV_wave13`: ZBound (Cvs.Route.Visibility.SpineCentreTermBound), OffDiag (Cvs.Route.Visibility.AliasOffDiagonalIncoherence),
TopPlungeFloor (Cvs.Prolate.TopPlungeFloor), PlungeLaw, CPbFloor and BandCellFloor (Cvs.Prolate.Gram.PlungeLawBandCellFloor), LogTailProfile at `η = ¼` (Cvs.Route.Visibility.PerRungLogTailLaw) and
RungLemmaX (Cvs.Prolate.Mellin.RungExteriorBoxBound). The window input is the disjunction of WinLogReg and WinTailProfile.
-/

noncomputable section
open Real Filter
open Cvs.ZeroCounting
open Cvs.Route.L1FloorFromBulkD0 (Dom)
open Cvs.Route.WindowPositivityBulkCoupling (Qx)
open Cvs.L2a.EvenSectorReflectionBound (R1)
open Cvs.WeilForm.ReflectionEvenPositivityRH (Ev)
open scoped InnerProductSpace

namespace Cvs.Route.Visibility.VisibilityAliasPlungeDischarge
open Cvs.ZeroCounting

/-- AL-R at `W̃ = 57/60` with the closed-form constant `offC`, unconditionally. -/
theorem alr : Cvs.Route.Visibility.WindowChainCellFloors.ALR (57 / 60) Cvs.Route.Visibility.AliasOffDiagonalIncoherence.offC := Cvs.Route.Visibility.AliasOffDiagonalIncoherence.alr_of_zBound Cvs.Route.Visibility.SpineCentreTermBound.zBound

/-- hV from (WF₂), the deep cell floor, the band floor, KRD, a window input and Carlson. -/
theorem hV_wave13 {T₀ : ℝ} (hT₀ : T₀ < 1) (hW : Cvs.Prolate.Gram.TwoCutLayerBound.WFtwo (57 / 60) T₀)
    (hDp : Cvs.Prolate.Gram.DeepRemainderCellFloors.DeepCellFloor) (hBF : Cvs.Prolate.Gram.TunnellingFloorSumPlunge.BandFloor) (hK : Cvs.Prolate.Gram.TunnellingFloorSumPlunge.KRDCount)
    (hWin : (∃ ν < 1, Cvs.Route.Visibility.MOnePrimeTopDepth.WinLogReg ν) ∨ ∃ η' ≥ 0, Cvs.Route.Visibility.WindowLogEnergyCellFloor.WinTailProfile η')
    (hCarl : Cvs.Zeta.ZeroCounting.ZeroDensityBlueprint.CarlsonBound) :
    ¬ RiemannHypothesis → ∀ᶠ x : ℕ in atTop, ¬ Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x 0 := by
  have hη0 : (0 : ℝ) < 1 / 4 := by norm_num
  have hη1 : (1 / 4 : ℝ) < 1 / 2 := by norm_num
  rcases hWin with ⟨ν, hν, hWR⟩ | ⟨η', hη', hWT⟩
  · exact Cvs.Route.Visibility.VisibilityFromRungFloorsCarlson.hV_wave12 hT₀ hW hDp (Cvs.Prolate.Gram.PlungeLawBandCellFloor.bandCellFloor_of_bandFloor hBF hDp) Cvs.Prolate.TopPlungeFloor.topPlungeFloor
      Cvs.Route.Visibility.SpineCentreTermBound.zBound Cvs.Route.Visibility.AliasOffDiagonalIncoherence.offDiag hK Cvs.Prolate.Gram.PlungeLawBandCellFloor.plungeLaw (Cvs.Prolate.Gram.PlungeLawBandCellFloor.cPbFloor_of_deep hDp) hBF hη0 hη1
      (Cvs.Route.Visibility.PerRungLogTailLaw.logTailProfile hη0 hη1) Cvs.Prolate.Mellin.RungExteriorBoxBound.rungLemmaX hν hWR hCarl
  · exact Cvs.Route.Visibility.VisibilityWindowLogTail.hV_wave13 hT₀ hW hDp (Cvs.Prolate.Gram.PlungeLawBandCellFloor.bandCellFloor_of_bandFloor hBF hDp) Cvs.Prolate.TopPlungeFloor.topPlungeFloor
      Cvs.Route.Visibility.SpineCentreTermBound.zBound Cvs.Route.Visibility.AliasOffDiagonalIncoherence.offDiag hK Cvs.Prolate.Gram.PlungeLawBandCellFloor.plungeLaw (Cvs.Prolate.Gram.PlungeLawBandCellFloor.cPbFloor_of_deep hDp) hBF hη0 hη1
      (Cvs.Route.Visibility.PerRungLogTailLaw.logTailProfile hη0 hη1) Cvs.Prolate.Mellin.RungExteriorBoxBound.rungLemmaX hη' hWT hCarl

end Cvs.Route.Visibility.VisibilityAliasPlungeDischarge

end
