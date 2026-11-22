import Mathlib
import Cvs.Finite.PairPoleChannelClosed
import Cvs.Finite.WindowMatrixSymbolKernel
import Cvs.Route.PoleMatChannelStrip
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded

/-!
# Midpoint-Reflection Folding of Boundary Strips onto `[0, L − t]`

Folds the even-sector boundary strips `[t/2, L/2]` into midpoint-symmetric and
midpoint-antisymmetric profile energies on `[0, L − t]`.
-/

set_option maxHeartbeats 800000
set_option autoImplicit false

noncomputable section

namespace Cvs.Route.BoundaryStripFolding
open Cvs.ZeroCounting

open scoped Matrix
open Real MeasureTheory
open Cvs.Finite.SymmetricModeSet
open Cvs.Route.EvenMatrixSlotPoleRestored
open Cvs.Route.PoleMatDefiniteSign
open Cvs.Route.PoleMatChannelStrip

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### `L`-periodicity and midpoint reflection of `evenProfile` -/

/-! ### Midpoint-symmetric and midpoint-antisymmetric profile components on `[0, L − t]` -/

omit [DecidableEq ι] in
/-- **The midpoint-symmetric part of `evenProfile` on `[0, L − t]`**:
`Φ^+_{ξ,t}(s) = (Φ_ξ(s) + Φ_ξ(L − t − s)) / 2`. -/
def evenProfileSym (L t : ℝ) (mode : ι → ℤ) (ξ : ι → ℝ) (s : ℝ) : ℝ :=
  (evenProfile L mode ξ s + evenProfile L mode ξ (L - t - s)) / 2

/-! ### Folding the boundary strip `[-L/2, -t/2] ∪ [t/2, L/2]` onto `[0, (L − t)/2]` and `[0, L − t]` -/

/-! ### Prime-summed interval representations of `sinStripQ`, `cosStripQ`, and strip excess -/

/-! ### Archimedean-plus-pole form, autoconvolution identity, and weighted strip-excess reduction -/

omit [DecidableEq ι] in
/-- **The archimedean-plus-pole quadratic form**:
`archPoleQ L mode ξ = ∑_i ξ_i² archSymbol(ω_i) + (2 poleFactor L / L) (∑_i ξ_i uu(1/2, ω_i))²`. -/
def archPoleQ (L : ℝ) (mode : ι → ℤ) (ξ : ι → ℝ) : ℝ :=
  (∑ i, ξ i ^ 2 * Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol (2 * π * mode i / L))
    + 2 * Cvs.Finite.PairPoleChannelClosed.poleFactor L / L * (∑ i, ξ i * Cvs.Finite.WindowMatrixSymbolKernel.uu (1 / 2) (2 * π * mode i / L)) ^ 2

omit [DecidableEq ι] in
/-- `posChannelQ` equals `archPoleQ` plus `sinStripQ`. -/
theorem posChannelQ_eq_archPoleQ_add_sinStripQ (P R : ℕ) (L : ℝ) (mode : ι → ℤ) (ξ : ι → ℝ) :
    posChannelQ P R L mode ξ = archPoleQ L mode ξ + sinStripQ P R L mode ξ := by
  rfl

end Cvs.Route.BoundaryStripFolding
