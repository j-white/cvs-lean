import Mathlib
import Cvs.Approximant.SpineSubspace
import Cvs.Route.Visibility.CaseFiniteCellFloorRates
import Cvs.Route.Visibility.LayerFloorDeepRemainderB
import Cvs.Route.Visibility.WindowChainCellFloors
import Cvs.Upstream.CoefficientFloorLinearBound

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Route SEP from (B): the window floor enters only through `limsup C₀·c_E^C < 2`

The cell floors of Cvs.Route.Visibility.WindowChainCellFloors and Cvs.Route.Visibility.CaseFiniteFromWindowChain use (WF′) and (EF′) only through (B). So route SEP holds with (B) in their place,
and in particular with (WF₂) ∧ (EF′), or with the half-band pair inequality, a bulk far loss and a plunge floor.
-/

noncomputable section

open Real Filter Finset
open Cvs.Zeta.GaussKernel.AdmissibleKernel (nonTrivialZeroSet)
open Cvs.Route.Visibility.CaseFiniteCellFloorRates (LogTailRate)

namespace Cvs.Route.Visibility.CellFloorFromConditionB
open Cvs.ZeroCounting

/-- **The window chain from (B)**: (B) and AL-R give `η₀ ∈ (0, 1)` and, eventually, the cell floors. -/
theorem isCellFloor_of_condB {Wt C₁ : ℝ} (hB : Cvs.Route.Visibility.LayerFloorDeepRemainderB.CondB Wt C₁) (hR : Cvs.Route.Visibility.WindowChainCellFloors.ALR Wt C₁) :
    ∃ η₀, 0 < η₀ ∧ η₀ < 1 ∧ ∀ᶠ x : ℕ in atTop, Cvs.Route.Visibility.CaseFiniteCellFloorRates.IsCellFloor x (Cvs.Route.Visibility.WindowChainCellFloors.cellFloor x η₀) := by
  obtain ⟨η₀, h0, h1, hAL⟩ := Cvs.Route.Visibility.WindowChainCellFloors.al_of_condB hB hR
  refine ⟨η₀, h0, h1, ?_⟩
  filter_upwards [Cvs.Route.Visibility.WindowChainCellFloors.cellFloor_le_of_al h0 h1 hAL, Cvs.Route.Visibility.LayerFloorDeepRemainderB.eventually_scale] with x h hx
  exact ⟨Cvs.Route.Visibility.WindowChainCellFloors.cellFloor_pos hx h1, h⟩

end Cvs.Route.Visibility.CellFloorFromConditionB

end
