import Mathlib
import Cvs.Approximant.D0FloorEvenRungShare
import Cvs.Approximant.SpineCoefficientMatrix
import Cvs.Approximant.SpineSubspace
import Cvs.Route.L1FloorFromBulkD0
import Cvs.WeilForm.BulkSchurIdentity
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
# The even rung block has at most one generalised eigenvalue below `κ_E(1 − λ₈)`

`evenNormGram x = (⟪rung i, rung j⟫)ᵢⱼ` is the Gram matrix of the even rungs, `aᵀ(evenNormGram x)a = ‖e_a‖²`. The
coefficients vanishing on `j < 2` have codimension `≤ 1` and their even parts lie in `D₀`, so `EvenSectorReflectionBound`'s `D₀` floor
gives `n₋(evenGram x − d·evenNormGram x) ≤ 1`, `d = κ_E(x, δ)(1 − λ₈)`, and `d ≤ λ₁(PᵀTP)` (ascending, from `0`)
for every `P` with `Pᵀ(evenNormGram x)P = 1`.
-/

noncomputable section

open Real Matrix Module
open scoped InnerProductSpace

namespace Cvs.L2a.EvenRungBlockOneLowEigen

open Cvs.Prolate.EvenRungsByIndex (lamR)
open Cvs.L2a.WindowChainInputsProlate (c0W)
open Cvs.Route.L1FloorFromBulkD0 (Dom rung)

/-! ### The even norm Gram matrix -/

/-- The inner product pulled back along `a ↦ e_a`, the even part of the spine class of `a`. -/
def evenNormForm (x : ℕ) : LinearMap.BilinForm ℝ (Cvs.Approximant.SpineSubspace.SF x → ℝ) :=
  (innerₗ (Dom x)).compl₁₂ ((Cvs.Approximant.D0FloorEvenRungShare.evenPartL (Real.log_natCast_nonneg x)).comp (Cvs.Approximant.SpineSubspace.spineMap x))
    ((Cvs.Approximant.D0FloorEvenRungShare.evenPartL (Real.log_natCast_nonneg x)).comp (Cvs.Approximant.SpineSubspace.spineMap x))

/-- The Gram matrix of the even rungs. -/
def evenNormGram (x : ℕ) : Matrix (Cvs.Approximant.SpineSubspace.SF x) (Cvs.Approximant.SpineSubspace.SF x) ℝ :=
  Cvs.WeilForm.BulkSchurIdentity.gram (evenNormForm x) fun j => Pi.single j 1

/-- `aᵀ(evenNormGram x)a = ‖e_a‖²`. -/
theorem quad_evenNormGram (x : ℕ) (a : Cvs.Approximant.SpineSubspace.SF x → ℝ) :
    a ⬝ᵥ (evenNormGram x *ᵥ a)
      = ‖Cvs.WeilForm.EvenOddSplitForm.evenPart (Real.log_natCast_nonneg x) (Cvs.Approximant.SpineSubspace.spineMap x a)‖ ^ 2 := by
  rw [evenNormGram, ← Cvs.WeilForm.BulkSchurIdentity.apply_sum_sum, Cvs.Approximant.SpineCoefficientMatrix.sum_single, evenNormForm, LinearMap.compl₁₂_apply,
    innerₗ_apply_apply, real_inner_self_eq_norm_sq]
  rfl

/-! ### The coefficients of `D₀` -/

/-! ### The floor and the count -/

end Cvs.L2a.EvenRungBlockOneLowEigen
