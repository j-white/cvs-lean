import Mathlib
import Cvs.WeilForm.MellinZeroSum
import Cvs.Zeta.GaussKernel.RiemannHypothesisTarget
import Cvs.Zeta.GaussKernel.ZeroChain
import Cvs.Zeta.GaussKernel.ZeroInductionIsRH
import Cvs.Zeta.GaussKernel.ZetaZeroStatement

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The coupling as an angle between images in `ℓ²` over the zeros

For `B(a, b) = ⟪Sa, Sb⟫`, the coupling `B(r,w)² ≤ (1−δ)B(r,r)B(w,w)` on `R × W` is
`⟪a,b⟫² ≤ (1−δ)‖a‖²‖b‖²` on `S(R) × S(W)`, and for `δ ≤ 1` it is `|cos ∠(a, b)| ≤ √(1−δ)`.
When every zero has real part `½`, `Q(w_v, w_u) = ⟪Z(v), Z(u)⟫` in `ℓ²(zeros, ℂ)` with the real inner product,
`Z(v)_ρ = √m_ρ M[v](ρ)`, so the coupling of spine vectors against tame classes of `R_Fᗮ` is that angle bound.
-/

noncomputable section

open Real Complex ComplexConjugate InnerProductGeometry
open scoped InnerProductSpace

namespace Cvs.WeilForm.CouplingAngle
open Cvs.ZeroCounting

/-! ### The abstract angle form -/

section Abstract

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

end Abstract

section Orth

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

end Orth

/-! ### The zero vector of a tame test on the line -/

open Cvs.L2a.WindowFormTailLimit (Tame)
open Cvs.WeilForm.ThetaSpaceParseval (mellinR)
open Cvs.WeilForm.MellinZeroSum (Z zeroTerm)

/-- RH puts every zero on the line. -/
theorem re_eq_half_of_rh (hRH : RiemannHypothesis) (rho : Z) : (rho : ℂ).re = 1 / 2 := by
  have h := Cvs.Zeta.GaussKernel.AdmissibleKernel.riemannHypothesis_iff.mpr hRH
  have := Cvs.Criterion.del_eq_zero_of_riemannHypothesis h rho
  unfold Cvs.GaussKernel.del at this
  linarith

/-! ### The coupling of spine vectors against tame classes -/

end Cvs.WeilForm.CouplingAngle
