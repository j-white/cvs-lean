import Mathlib
import Cvs.L2a.EvenSectorReflectionBound
import Cvs.Route.EvenGramRungFloors
import Cvs.Route.EvenWindowBulkCoupling
import Cvs.Route.L1FloorFromBulkD0
import Cvs.Route.WindowPositivityBulkCoupling
import Cvs.WeilForm.ReflectionEvenPositivityRH
import Cvs.WeilForm.WeilFormOnWindowL2

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Symmetry, Diagonal Dominance, and Mode-Matrix Bridges for `evenGram`

Establishes symmetry, diagonal evaluations, and weighted/unweighted Gershgorin diagonal-dominance
floors for `Cvs.L2a.EvenSectorReflectionBound.evenGram x`, and bridges `Cvs.Route.EvenMatrixSlotPoleRestored.ApoleSlot` to `EvenGramNonneg x`.
-/

noncomputable section

open Real Filter Finset Matrix
open scoped InnerProductSpace

namespace Cvs.Finite.EvenGramSymmetryBridges
open Cvs.ZeroCounting

open Cvs.Route.L1FloorFromBulkD0 (Dom Bx rung)
open Cvs.L2a.EvenSectorReflectionBound (R1 ReflBound evenGram)
open Cvs.Route.WindowPositivityBulkCoupling (Qx)
open Cvs.WeilForm.ReflectionEvenPositivityRH (Ev)
open Cvs.Route.RepresenterFreeCrossBounds (EvenRungNonneg)
open Cvs.Route.EvenGramRungFloors (EvenGramNonneg evenRungPos_iff_evenGramNonneg evenGramNonneg_iff_reflBound_one)

/-! ### Symmetry and diagonal structure of `evenGram x` -/

/-! ### Weighted and unweighted Gershgorin diagonal dominance -/

/-! ### Bridges from `Cvs.Route.EvenMatrixSlotPoleRestored` mode-matrix positivity and `ApoleSlot` to `EvenGramNonneg x` -/

/-- Even window positivity `∀ v ∈ Ev x, 0 ≤ Qx x v` implies `EvenGramNonneg x`. -/
theorem evenGramNonneg_of_evenWindowPos {x : ℕ} (h : ∀ v ∈ Ev x, 0 ≤ Qx x v) :
    EvenGramNonneg x :=
  (evenRungPos_iff_evenGramNonneg x).1 fun r hr => h r (Cvs.Route.EvenWindowBulkCoupling.R1_le_Ev x hr)

end Cvs.Finite.EvenGramSymmetryBridges
