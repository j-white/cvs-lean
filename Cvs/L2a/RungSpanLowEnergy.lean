import Mathlib
import Cvs.Approximant.SpineCoefficientMatrix
import Cvs.Approximant.SpineSubspace
import Cvs.Route.L1FloorFromBulkD0
import Cvs.WeilForm.BulkSchurIdentity
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
# The rung span is a low-energy subspace of dimension `x − 1`, given a window nondegeneracy constant

`normGram x` is the Gram matrix of the spine classes, `aᵀ(normGram x)a = ‖spineMap x a‖²`. If
`Σᵢ bᵢ²(1 − λ_{kᵢ}) ≤ Γ‖spineMap x a‖²` on `SF x`, an earlier result gives `Q ≤ ε₁‖·‖²` on `R_F`,
`ε₁ = L1U(x)·frameU(x)·(π/c)·Γ`; so `R_F` has dimension `x − 1` with `Q ≤ ε₁‖·‖²` there, and
`n₋(spineGram x − ε′·normGram x) = x − 1` for every `ε′ > ε₁`.
-/

noncomputable section

open MeasureTheory Set Real Matrix Module Cvs.Prolate.EvenRungsByIndex

namespace Cvs.L2a.RungSpanLowEnergy

open Cvs.L2a.ProlateFamilySpine (kOf bOf)
open Cvs.L2a.WindowChainInputsProlate (c0W)
open Cvs.Approximant.SpineSubspace (SF spineMap RF)

/-! ### The norm Gram matrix -/

/-- The inner product pulled back along the spine map. -/
def normForm (x : ℕ) : LinearMap.BilinForm ℝ (SF x → ℝ) :=
  (innerₗ (Cvs.Route.L1FloorFromBulkD0.Dom x)).compl₁₂ (spineMap x) (spineMap x)

/-- The Gram matrix of the spine classes, `(⟪spineMap x eᵢ, spineMap x eⱼ⟫)ᵢⱼ`. -/
def normGram (x : ℕ) : Matrix (SF x) (SF x) ℝ :=
  Cvs.WeilForm.BulkSchurIdentity.gram (normForm x) fun j => Pi.single j 1

/-- `aᵀ(normGram x)a = ‖spineMap x a‖²`. -/
theorem quad_normGram (x : ℕ) (a : SF x → ℝ) : a ⬝ᵥ (normGram x *ᵥ a) = ‖spineMap x a‖ ^ 2 := by
  rw [normGram, ← Cvs.WeilForm.BulkSchurIdentity.apply_sum_sum, Cvs.Approximant.SpineCoefficientMatrix.sum_single, normForm, LinearMap.compl₁₂_apply, innerₗ_apply_apply,
    real_inner_self_eq_norm_sq]

/-! ### The weights `1 − λ` -/

/-! ### The low-energy subspace -/

end Cvs.L2a.RungSpanLowEnergy
