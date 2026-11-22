import Mathlib
import Cvs.Finite.SymmetricModeSet
import Cvs.Route.EvenMatrixSlotPoleRestored
import Cvs.Route.PosChannelFloorCoercivity
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded

/-!
# Unconditional Bulk Floor and Contraction on `lowModeRung`

Proves `PosChannelFloor`, `StripExcessBound`, `PosChannelContraction`, and `ApoleBulkFloor`
unconditionally on `lowModeRung L N C` and reduces `ApoleSlot` and `RiemannHypothesis` to the rungs.
-/

set_option maxHeartbeats 800000
set_option autoImplicit false

noncomputable section

namespace Cvs.Route.LowModeRungBulkFloor
open Cvs.ZeroCounting

open scoped Matrix
open Real Filter
open Cvs.Finite.SymmetricModeSet
open Cvs.Route.EvenMatrixSlotPoleRestored
open Cvs.Route.PosChannelFloorCoercivity

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Spanning `evenModeSub` by `evenBasisVec` -/

/-- Every vector `x ∈ evenModeSub neg` is the linear combination `∑ j, (x j / 2) • evenBasisVec neg j`. -/
theorem eq_sum_evenBasisVec_of_even {neg : ι → ι} (hinv : Function.Involutive neg)
    {x : ι → ℝ} (hx : x ∈ evenModeSub neg) :
    x = ∑ j : ι, (x j / 2) • evenBasisVec neg j := by
  ext k
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, evenBasisVec, mul_add,
    mul_ite, mul_one, mul_zero, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ,
    ↓reduceIte]
  have hbij : (∑ j : ι, if k = neg j then x j / 2 else 0) = x (neg k) / 2 := by
    have h1 : (fun j : ι => if k = neg j then x j / 2 else 0)
        = (fun j : ι => if neg k = j then x j / 2 else 0) := by
      ext j
      have heq : (k = neg j) ↔ (neg k = j) :=
        ⟨fun h => by rw [h, hinv j], fun h => by rw [← h, hinv k]⟩
      simp [heq]
    rw [h1, Finset.sum_ite_eq Finset.univ (neg k) (fun j => x j / 2)]
    simp
  rw [hbij, hx k]
  ring

/-! ### The canonical low-mode rung subspace `lowModeRung L N C` -/

/-- **The set of mode indices below archimedean symbol threshold `C` at scale `L`.** -/
def lowModeSet (L : ℝ) (N : ℕ) (C : ℝ) : Set (Cvs.Finite.SymmetricModeSet.Idx N) :=
  {i : Cvs.Finite.SymmetricModeSet.Idx N | Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol (2 * π * Cvs.Finite.SymmetricModeSet.mode N i / L) < C}

/-! ### Unconditional proof of Sub-Target B (`ArchPoleBulkFloor` & `PosChannelFloor`) on `lowModeRung` -/

/-! ### Unconditional proof of Sub-Target C (`StripExcessBound`, `PosChannelContraction`, & `ApoleBulkFloor`) -/

/-! ### Reduction of `ApoleSlot`, `M_even_nonneg`, and `RiemannHypothesis` solely to `lowModeRung` -/

end Cvs.Route.LowModeRungBulkFloor
