import Mathlib
import Cvs.Prolate.Mellin.WeakRightEdgeLaw
import Cvs.Prolate.Mellin.WeakRightEdgeWindowInput
import Cvs.Route.Visibility.MOnePrimeTopDepth
import Cvs.Route.Visibility.WindowLogEnergyCellFloor

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# HV from Landau's transition law, the band floor and Carlson

The window input is `WeakRightEdgeLaw`'s weak right-edge law (Cvs.Prolate.Mellin.WeakRightEdgeWindowInput) and the tunnelling sum is `TunnellingFloorSumBand`'s, which with `VisibilityHardyModule`'s
`CEBound (57/60)` gives hV from Landau, the band floor `σ'_j ≥ x^{−ε}` and Carlson; `PosQ0At 1` gives the band floor.
-/

noncomputable section

open Real Filter

namespace Cvs.Route.Visibility.VisibilityLandauBandCarlson
open Cvs.ZeroCounting

/-- **The window input** `(∃ ν < 1, WinLogReg ν) ∨ ∃ η' ≥ 0, WinTailProfile η'`. -/
theorem winInput : (∃ ν < 1, Cvs.Route.Visibility.MOnePrimeTopDepth.WinLogReg ν) ∨ ∃ η' ≥ 0, Cvs.Route.Visibility.WindowLogEnergyCellFloor.WinTailProfile η' :=
  Cvs.Prolate.Mellin.WeakRightEdgeWindowInput.winInput_of_weakEdgeLaw Cvs.Prolate.Mellin.WeakRightEdgeLaw.weakEdgeLaw

end Cvs.Route.Visibility.VisibilityLandauBandCarlson

end
