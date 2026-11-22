import Mathlib
import Cvs.StepA.NegativeIndexQuadruples
import Cvs.StepA.OneZeroParitySectors
import Cvs.Zeta.GaussKernel.ZetaZeroStatement
import Cvs.Zeta.ZeroCounting.CarlsonCountBridge
import Cvs.Zeta.ZeroSideMoments

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Each parity sector of the window form has at most one negative direction per quadruple
On `L·M_L`'s sector forms `∑_ρ m_ρ ((∫ g u_ρ)² − (∫ g v_ρ)²)` the functional `ℓ_ρ : xi ↦ ∫ g v_ρ` is
linear in the coefficient vector, vanishes for zeros on the line, and equals `±ℓ_σ` across the
quadruple `σ, σ̄, 1 − σ, 1 − σ̄`. So for every `L > 0`, every subspace of even (odd) coefficient vectors
on which the form is negative definite has dimension at most the number of off-line quadruples.
-/

noncomputable section

open Real Matrix Module Cvs.WeilForm.SelfConvolutionTransform

namespace Cvs.StepA.ParitySectorNegativeIndex
open Cvs.ZeroCounting

open Cvs.Finite.TruncationZeroFreeOffAxes (omega)
open Cvs.StepA.OneZeroParitySectors (ue ve uo vo continuous_ve continuous_vo)
open Cvs.StepA.NegativeIndexQuadruples (InQuad zPoint_oneSubZ zPoint_conjZ)

variable {ι : Type*} [Fintype ι]

/-! ### The off-line functionals -/

/-- Across a quadruple, `ve` at `z_ρ` is `±ve` at `z_σ`. -/
theorem ve_quad {rho σ : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet} (hq : InQuad rho σ) :
    (∀ t, ve (Cvs.ZeroCounting.zPoint rho) t = ve (Cvs.ZeroCounting.zPoint σ) t) ∨
      ∀ t, ve (Cvs.ZeroCounting.zPoint rho) t = -ve (Cvs.ZeroCounting.zPoint σ) t := by
  rcases hq with rfl | rfl | rfl | rfl
  · exact Or.inl fun t => rfl
  · refine Or.inr fun t => ?_
    rw [zPoint_conjZ, (Cvs.StepA.OneZeroParitySectors.weights_neg _ t).2.1,
      (Cvs.StepA.OneZeroParitySectors.weights_conj _ t).2.1]
  · exact Or.inl fun t => by rw [zPoint_oneSubZ, (Cvs.StepA.OneZeroParitySectors.weights_neg _ t).2.1]
  · refine Or.inr fun t => ?_
    rw [zPoint_oneSubZ, zPoint_conjZ, neg_neg, (Cvs.StepA.OneZeroParitySectors.weights_conj _ t).2.1]

/-! ### Nonnegativity on the common kernel -/

/-! ### The inertia bounds -/

end Cvs.StepA.ParitySectorNegativeIndex
