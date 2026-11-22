import Mathlib

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The Schur floor onto an index set: block form, variational form, weighted-sieve form

For `M ≻ 0` and `T = {j | p j}`, `S_T = ((M⁻¹)_{TT})⁻¹ = M_TT − M_TF M_FF⁻¹ M_FT`; `v_TᵀS_Tv_T` is the least `aᵀMa`
over `a` with `a_T = v`, and over a Gram matrix it is `dist²(Σ_T v_t u_t, span u_F)`. Hence `f` is a floor of `S_T`
iff `f P_T ≤ M`, iff `uᵀ(M⁻¹)_{TT}u ≤ |u|²/f`, iff `f ≤ λ_min(S_T)`; with `M = 1 − G` this is the weighted
large-sieve form `G ≤ P_F + (1 − f)P_T`, and every floor of `S_T` is a floor of `M_TT`.
-/

noncomputable section

open Matrix
open scoped MatrixOrder

namespace Cvs.Upstream.SchurFloorIndexSet


variable {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → Prop) [DecidablePred p]

/-! ### The Schur complement onto an index set and its block form -/

/-- The Schur complement of `M` onto `T = {j | p j}`, written `((M⁻¹)_{TT})⁻¹`. -/
def schurOn (M : Matrix ι ι ℝ) : Matrix {j // p j} {j // p j} ℝ := (M⁻¹.toBlock p p)⁻¹

variable {p}

/-! ### The variational form -/

/-! ### The floor as `λ_min` -/

/-! ### The distance form on a Gram matrix -/

section Gram

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

end Gram

end Cvs.Upstream.SchurFloorIndexSet
