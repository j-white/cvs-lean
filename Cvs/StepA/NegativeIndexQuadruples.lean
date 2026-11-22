import Mathlib
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
# The window form's negative index is at most the number of off-line quadruples
On `Cvs.Finite.UniversalFunctionPairing`'s zero side `xiᵀ M xi = L ∑_ρ m_ρ ((Re G)² − (Im G)²)(L z_ρ)` the functional
`xi ↦ Im G(L z_ρ)` is linear and equals `± Im G(L z_σ)` across the quadruple `σ, σ̄, 1 − σ, 1 − σ̄`.
Every subspace of even coefficient vectors on which the form is negative definite has dimension at
most the dimension of the span of the off-line functionals, at most the number of quadruples.
-/

noncomputable section

open Real Matrix Module

namespace Cvs.StepA.NegativeIndexQuadruples
open Cvs.ZeroCounting

variable {ι : Type*} [Fintype ι]

theorem zPoint_oneSubZ (σ : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet) :
    Cvs.ZeroCounting.zPoint (Cvs.GaussKernel.oneSubZ σ) = -Cvs.ZeroCounting.zPoint σ := by
  unfold Cvs.ZeroCounting.zPoint Cvs.GaussKernel.oneSubZ
  ring

theorem zPoint_conjZ (σ : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet) :
    Cvs.ZeroCounting.zPoint (Cvs.GaussKernel.conjZ σ)
      = -starRingEnd ℂ (Cvs.ZeroCounting.zPoint σ) := by
  unfold Cvs.ZeroCounting.zPoint Cvs.GaussKernel.conjZ
  simp only [map_mul, map_neg, Complex.conj_I, map_sub, map_div₀, map_one, map_ofNat]
  ring

/-- `ρ` lies in the quadruple `{σ, σ̄, 1 − σ, 1 − σ̄}`. -/
def InQuad (rho σ : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet) : Prop :=
  rho = σ ∨ rho = Cvs.GaussKernel.conjZ σ ∨ rho = Cvs.GaussKernel.oneSubZ σ
    ∨ rho = Cvs.GaussKernel.oneSubZ (Cvs.GaussKernel.conjZ σ)

end Cvs.StepA.NegativeIndexQuadruples
