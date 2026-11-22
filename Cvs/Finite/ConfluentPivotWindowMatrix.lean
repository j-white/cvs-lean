import Mathlib
import Cvs.Finite.DiagonalCutSymbol
import Cvs.Finite.DisplacementIdentity
import Cvs.Finite.DividedDifferenceCommutator
import Cvs.Finite.OddEigenvectorResolvent
import Cvs.Finite.PairFormDividedDifference
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationQuadraticForm
import Cvs.Finite.TruncationZeroFreeOffAxes
import Cvs.StepA.OddAboveDisplacement
import Cvs.Upstream.GeneralizedSchurStep
import Cvs.Upstream.SchurSylvesterDisplacement

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The confluent pivot law on the CvS window matrix

The CvS window matrix `Cvs.Finite.TruncationQuadraticForm.M` at the nodes `ω_i` carries Hermite data in the sense of Cvs.Upstream.GeneralizedSchurStep: `G_i = (1, −b_i)`,
`J = [[0, 1], [−1, 0]]`, `G′_i = (0, −(b̂′(ω_i) + Pair(cosCut L ω_i)))` with `b̂(ω) = −Pair(sinCut L ω)/L` (Cvs.Finite.DiagonalCutSymbol), so
`(ω_i − ω_j)M_ij = G_iJG_jᵀ` and `M_ii = G′_iJG_iᵀ`. Along every in-place elimination order of distinct nodes each
pivot of `M` is the confluent value `G′_MJG_Mᵀ` of the current data.
-/

noncomputable section

open Matrix Real

namespace Cvs.Finite.ConfluentPivotWindowMatrix
open Cvs.ZeroCounting

open Cvs.Finite.SymmetricModeSet (Idx mode negI)
open Cvs.Finite.OddEigenvectorResolvent (om)
open Cvs.Upstream.GeneralizedSchurStep (HermiteOn iterMat iterGen iterDer)

/-- The natural extension `b̂(ω) = −Pair(sinCut L ω)/L` of the window values `b`. -/
def bExt (Pt R : ℕ) (L : ℝ) (ω : ℝ) : ℝ := -(Cvs.Finite.PairFormDividedDifference.Pair Pt R (Cvs.Finite.DiagonalCutSymbol.sinCut L ω)) / L

/-- The window generator rows `G_i = (1, −b_i)`. -/
def winGen (Pt R : ℕ) (L : ℝ) (N : ℕ) : Idx N → Fin 2 → ℝ :=
  fun i => ![1, -Cvs.Finite.PairFormDividedDifference.bval Pt R L (mode N i)]

/-- The window derivative rows `G′_i = (0, −(b̂′(ω_i) + Pair(cosCut L ω_i)))`. -/
def winDer (Pt R : ℕ) (L : ℝ) (N : ℕ) : Idx N → Fin 2 → ℝ :=
  fun i => ![0, -(deriv (bExt Pt R L) (om L N i)
    + Cvs.Finite.PairFormDividedDifference.Pair Pt R (Cvs.Finite.DiagonalCutSymbol.cosCut L (om L N i)))]

/-- The window generator samples the natural extension: `b_i = b̂(ω_i)`. -/
theorem bval_eq_bExt (Pt R : ℕ) (L : ℝ) (N : ℕ) (i : Idx N) :
    Cvs.Finite.PairFormDividedDifference.bval Pt R L (mode N i) = bExt Pt R L (om L N i) :=
  Cvs.Finite.DiagonalCutSymbol.bval_eq Pt R L (mode N i)

/-- **The window diagonal is the natural confluent value plus the cut symbol**:
`M_ii = b̂′(ω_i) + Pair(cosCut L ω_i)`. -/
theorem window_diag_eq {L : ℝ} (hL : 0 < L) (Pt R N : ℕ) (i : Idx N) :
    Cvs.Finite.TruncationQuadraticForm.M Pt R L (mode N) i i
      = deriv (bExt Pt R L) (om L N i)
        + Cvs.Finite.PairFormDividedDifference.Pair Pt R (Cvs.Finite.DiagonalCutSymbol.cosCut L (om L N i)) := by
  have h := (Cvs.Finite.DiagonalCutSymbol.hasDerivAt_bval Pt R hL (mode N i)).deriv
  have hom : om L N i = 2 * π * (mode N i : ℝ) / L := rfl
  rw [hom, show bExt Pt R L = fun ω => -(Cvs.Finite.PairFormDividedDifference.Pair Pt R (Cvs.Finite.DiagonalCutSymbol.sinCut L ω)) / L
    from rfl, h]
  simp [Cvs.Finite.TruncationQuadraticForm.M]

/-- **The CvS window matrix carries Hermite data** on all nodes: `(ω_i − ω_j)M_ij = G_iJG_jᵀ`, `M` symmetric, and
`M_ii = G′_iJG_iᵀ` for `G = winGen`, `G′ = winDer`, `J = [[0, 1], [−1, 0]]`. -/
theorem window_hermite {L : ℝ} (hL : 0 < L) (Pt R N : ℕ) :
    HermiteOn Set.univ (Cvs.Finite.TruncationQuadraticForm.M Pt R L (mode N)) (om L N) (winGen Pt R L N) (winDer Pt R L N)
      (Cvs.Upstream.SchurSylvesterDisplacement.J2 ℝ) := by
  refine ⟨fun i _ j _ => ?_, fun i _ j _ => Cvs.Finite.TruncationQuadraticForm.M_symm hL Pt R
    (Cvs.Finite.SymmetricModeSet.mode_injective N) i j, fun i _ => ?_⟩
  · rw [Cvs.StepA.OddAboveDisplacement.displacement_M hL Pt R N i j]
    simp [winGen, Cvs.Upstream.SchurSylvesterDisplacement.J2, dotProduct, mulVec, Fin.sum_univ_two]
  · rw [window_diag_eq hL Pt R N i]
    simp [winGen, winDer, Cvs.Upstream.SchurSylvesterDisplacement.J2, dotProduct, mulVec, Fin.sum_univ_two]

/-- The window nodes are distinct. -/
theorem om_injective {L : ℝ} (hL : 0 < L) (N : ℕ) : Function.Injective (om L N) :=
  Cvs.Finite.DisplacementIdentity.omega_injective hL (Cvs.Finite.SymmetricModeSet.mode_injective N)

/-- **The confluent pivot law on the CvS window matrix**: for every order `a 0, …, a M` of distinct window nodes,
the `M`-th in-place pivot of `M = Cvs.Finite.TruncationQuadraticForm.M` is `G′_M(a_M) J G_M(a_M)ᵀ` for the window Hermite data carried along the
chain. -/
theorem window_pivot_eq_hermite {L : ℝ} (hL : 0 < L) (Pt R N : ℕ) {a : ℕ → Idx N} (M : ℕ)
    (hinj : Set.InjOn a (Set.Iic M)) :
    iterMat (Cvs.Finite.TruncationQuadraticForm.M Pt R L (mode N)) a M (a M) (a M)
      = iterDer (Cvs.Finite.TruncationQuadraticForm.M Pt R L (mode N)) (om L N) (Cvs.Upstream.SchurSylvesterDisplacement.J2 ℝ) (winGen Pt R L N)
          (winDer Pt R L N) a M (a M)
        ⬝ᵥ (Cvs.Upstream.SchurSylvesterDisplacement.J2 ℝ *ᵥ iterGen (Cvs.Finite.TruncationQuadraticForm.M Pt R L (mode N)) (winGen Pt R L N) a M (a M)) :=
  Cvs.Upstream.GeneralizedSchurStep.pivot_eq_hermite (window_hermite hL Pt R N) ((om_injective hL N).injOn) M
    (fun _ _ => Set.mem_univ _) hinj

end Cvs.Finite.ConfluentPivotWindowMatrix
