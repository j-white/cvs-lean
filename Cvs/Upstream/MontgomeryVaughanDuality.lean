import Mathlib
import Cvs.Upstream.HermitianPosPart

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# MV step 4 — spectral reduction: `eigen_bound` ⇒ `MVDiag 13` ⇒ `∃ C, MVHilbert C`

With `k_{rs} := √δ_r √δ_s/(λ_r − λ_s)` (0 on the diagonal; real antisymmetric) the matrix
`M := i·K` is Hermitian.  Every eigen-pair `(ν, v)` of `M` (unit `v`, from Mathlib's
`Matrix.IsHermitian.eigenvectorBasis`) satisfies the eigen-relation of `eigen_bound` with `μ := −ν`,
so `|ν| ≤ 13` for all eigenvalues (step 3).  Expanding in the eigenbasis
(`y* M y = Σ_i ν_i |(U*y)_i|²`, `Σ_i |(U*y)_i|² = Σ_i |y_i|²`) gives `|y* M y| ≤ 13 ‖y‖²`;
substituting `y_r := x_r/√δ_r` lands exactly on `MVDiag 13` (the literature / diagonal form of the
Montgomery–Vaughan weighted Hilbert inequality, Cvs.Zeta.Base/MV.lean), and polarization
`exists_MVHilbert_of_diag` yields the bilinear H-MV of `Hypotheses.lean`.
-/

noncomputable section

open Finset Complex Matrix Unitary
open scoped BigOperators ComplexConjugate

namespace Cvs.Zeta.Base
namespace MV

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The normalized kernel `k_{rs} = √δ_r √δ_s/(freq r − freq s)`, `0` on the diagonal. -/
def kfun (freq δ : ι → ℝ) (r s : ι) : ℝ :=
  if r = s then 0 else Real.sqrt (δ r) * Real.sqrt (δ s) / (freq r - freq s)

omit [Fintype ι] in
lemma kfun_antisymm (freq δ : ι → ℝ) (r s : ι) : kfun freq δ s r = -kfun freq δ r s := by
  unfold kfun
  by_cases h : r = s
  · subst h; simp
  · rw [if_neg (Ne.symm h), if_neg h, ← neg_div_neg_eq, neg_sub]; ring

/-- `M := i·K`, a Hermitian complex matrix. -/
def Mmat (freq δ : ι → ℝ) : Matrix ι ι ℂ := fun r s => (kfun freq δ r s : ℂ) * Complex.I

omit [Fintype ι] in
lemma Mmat_isHermitian (freq δ : ι → ℝ) : (Mmat freq δ).IsHermitian := by
  refine Matrix.IsHermitian.ext fun r s => ?_
  simp only [Mmat, star_mul', Complex.star_def, Complex.conj_ofReal, Complex.conj_I,
    kfun_antisymm freq δ r s]
  push_cast
  ring

omit [DecidableEq ι] in
/-- `star v ⬝ᵥ v = Σ ‖v_i‖²` (as a complex number). -/
lemma star_dotProduct_self (v : ι → ℂ) : star v ⬝ᵥ v = ((∑ i, ‖v i‖ ^ 2 : ℝ) : ℂ) := by
  simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.conj_mul']
  push_cast
  rfl

/-- Spectral expansion of the Hermitian form, complex-valued:
`x* A x = Σ_i ν_i ‖(U* x)_i‖²` with `U` the eigenvector unitary. -/
lemma star_dotProduct_mulVec_eq {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (x : ι → ℂ) :
    star x ⬝ᵥ (A *ᵥ x)
      = ((∑ i, hA.eigenvalues i *
          ‖(star (hA.eigenvectorUnitary : Matrix ι ι ℂ) *ᵥ x) i‖ ^ 2 : ℝ) : ℂ) := by
  set U : Matrix ι ι ℂ := ↑hA.eigenvectorUnitary
  set c := star U *ᵥ x with hc_def
  have hsc : star x ᵥ* U = star c := by
    rw [hc_def, star_mulVec, show (star U)ᴴ = U from conjTranspose_conjTranspose U]
  conv_lhs => rw [← RHLinalg.specMap_id hA]
  unfold RHLinalg.specMap
  rw [conjStarAlgAut_apply, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    dotProduct_mulVec (star x) U, hsc, ← hc_def]
  simp only [id, dotProduct, mulVec_diagonal, Pi.star_apply, Complex.star_def]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Complex.conj_mul', mul_left_comm]
  rfl

/-- `Σ ‖(U* x)_i‖² = Σ ‖x_i‖²` for the eigenvector unitary `U`. -/
lemma sum_norm_sq_unitary {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (x : ι → ℂ) :
    ∑ i, ‖(star (hA.eigenvectorUnitary : Matrix ι ι ℂ) *ᵥ x) i‖ ^ 2 = ∑ i, ‖x i‖ ^ 2 := by
  set U : Matrix ι ι ℂ := ↑hA.eigenvectorUnitary
  set c := star U *ᵥ x with hc_def
  have hsc : star x ᵥ* U = star c := by
    rw [hc_def, star_mulVec, show (star U)ᴴ = U from conjTranspose_conjTranspose U]
  have h : star c ⬝ᵥ c = star x ⬝ᵥ x := by
    have hU : U * star U = 1 := Unitary.mul_star_self_of_mem hA.eigenvectorUnitary.2
    rw [← hsc, hc_def, ← dotProduct_mulVec, Matrix.mulVec_mulVec, hU, Matrix.one_mulVec]
  rw [star_dotProduct_self, star_dotProduct_self] at h
  exact_mod_cast h

end MV
end Cvs.Zeta.Base

end
