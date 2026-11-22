import Mathlib
import Cvs.Approximant.D0FloorEvenRungShare
import Cvs.Approximant.SpineClassNotOdd
import Cvs.Approximant.SpineSubspace
import Cvs.L2a.EvenRungBlockOneLowEigen
import Cvs.L2a.EvenSectorReflectionBound
import Cvs.Route.L1FloorFromBulkD0
import Cvs.StepA.LowEigenvalueCountSpine
import Cvs.WeilForm.BulkSchurIdentity
import Cvs.WeilForm.CouplingGramTopEigen
import Cvs.WeilForm.EvenOddSplitForm
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.WeilFormOnWindowL2

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The even norm Gram matrix is positive definite, and the second even eigenvalue

`aᵀ(evenNormGram x)a = ‖e_a‖²` and `a ↦ e_a` is injective (Cvs.Approximant.SpineClassNotOdd), so `evenNormGram x` is positive definite at
`80 ≤ 2πx` and `S = (evenNormGram x)^{−1/2}` has `Sᵀ(evenNormGram x)S = 1`. With it `EvenRungBlockOneLowEigen`'s bound reads
`κ_E(x, δ)(1 − λ₈) ≤ λ₁(Sᵀ(evenGram x)S)` (ascending, from `0`) past `c₀W`, from the reflection bound at level `2`.
-/

noncomputable section

open Real Matrix
open scoped MatrixOrder

namespace Cvs.L2a.EvenNormGramPosDef
open Cvs.ZeroCounting

open Cvs.Prolate.EvenRungsByIndex (lamR)
open Cvs.L2a.WindowChainInputsProlate (c0W)
open Cvs.L2a.EvenSectorReflectionBound (evenGram kappaE ReflBound)
open Cvs.L2a.EvenRungBlockOneLowEigen (evenNormGram)

/-- The pulled-back inner product is symmetric. -/
theorem evenNormForm_isSymm (x : ℕ) : (Cvs.L2a.EvenRungBlockOneLowEigen.evenNormForm x).IsSymm :=
  ⟨fun a b => by
    simp only [Cvs.L2a.EvenRungBlockOneLowEigen.evenNormForm, LinearMap.compl₁₂_apply, innerₗ_apply_apply]
    exact real_inner_comm _ _⟩

/-- `evenNormGram x` is symmetric. -/
theorem evenNormGram_isHermitian (x : ℕ) : (evenNormGram x).IsHermitian :=
  Cvs.WeilForm.BulkSchurIdentity.gram_isHermitian (evenNormForm_isSymm x) _

/-- **The even norm Gram matrix is positive definite** at `80 ≤ 2πx`. -/
theorem evenNormGram_posDef {x : ℕ} (hx : 80 ≤ 2 * π * x) : (evenNormGram x).PosDef := by
  refine PosDef.of_dotProduct_mulVec_pos (evenNormGram_isHermitian x) fun a ha => ?_
  rw [star_trivial, Cvs.L2a.EvenRungBlockOneLowEigen.quad_evenNormGram]
  have hne : Cvs.WeilForm.EvenOddSplitForm.evenPart (Real.log_natCast_nonneg x) (Cvs.Approximant.SpineSubspace.spineMap x a) ≠ 0 :=
    fun h => ha (Cvs.Approximant.SpineClassNotOdd.eq_zero_of_evenPart_eq_zero hx h)
  positivity

/-- The whitening matrix `S = (evenNormGram x)^{−1/2}`. -/
def whiten (x : ℕ) : Matrix (Cvs.Approximant.SpineSubspace.SF x) (Cvs.Approximant.SpineSubspace.SF x) ℝ := CFC.sqrt (evenNormGram x)⁻¹

/-- **`Sᵀ(evenNormGram x)S = 1`** at `80 ≤ 2πx`. -/
theorem whiten_spec {x : ℕ} (hx : 80 ≤ 2 * π * x) : (whiten x)ᵀ * evenNormGram x * whiten x = 1 :=
  Cvs.WeilForm.CouplingGramTopEigen.invSqrt_whitens (evenNormGram_posDef hx)

/-- `Sᵀ(evenGram x)S` is symmetric. -/
theorem whitened_isHermitian (x : ℕ) : ((whiten x)ᵀ * evenGram x * whiten x).IsHermitian :=
  Cvs.WeilForm.CouplingGramTopEigen.isHermitian_whitened (Cvs.StepA.LowEigenvalueCountSpine.evenGram_isHermitian x) _

end Cvs.L2a.EvenNormGramPosDef
