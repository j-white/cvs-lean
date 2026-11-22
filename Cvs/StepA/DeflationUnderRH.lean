import Mathlib
import Cvs.Finite.EvenSectorZeroSide
import Cvs.Finite.OddDivisionPolynomial
import Cvs.Finite.OddEigenvectorResolvent
import Cvs.Finite.ParitySectorDefect
import Cvs.Finite.SymmetricModeSet
import Cvs.StepA.ZeroSideIdentitiesRH
import Cvs.WeilForm.SelfConvolutionTransform
import Cvs.Zeta.ExplicitFormula.HannWindowShifts
import Cvs.Zeta.GaussKernel.ZetaZeroStatement

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Deflation under RH, and the deflated root configuration

Under RH, for `deg p < N − 1` vanishing at `γ²` for every zero ordinate with `γ² < Λ`, the odd vector
`v = vecOf p` has `Λ·vᵀMv ≤ (W²v)ᵀMv`. Replacing the roots `r_0, …, r_k` of a root list by
`a_0, …, a_{k−1}` (`a` monotone) gives a list that still dominates `a` when `r_i ≥ a_i` for `i > k`.
-/

noncomputable section

open Matrix Real Polynomial

namespace Cvs.Finite.OddDisplacementPencil
open Cvs.ZeroCounting
open Cvs.Zeta.GaussKernel.AdmissibleKernel (nonTrivialZeroSet)
open Cvs.Finite.SymmetricModeSet (Idx mode negI)
open Cvs.Finite.OddEigenvectorResolvent (xdiv om)
open Cvs.Finite.ParitySectorDefect (MX)

variable {L : ℝ} {N : ℕ}

/-- **Deflation under RH**: for `deg p < N − 1` with `p(γ_ρ²) = 0` at every zero with `γ_ρ² < Λ`,
`Λ·vᵀMv ≤ (W²v)ᵀMv` for `v = vecOf p`. -/
theorem mul_dot_le_of_eval_eq_zero (hRH : RiemannHypothesis) (hL : 0 < L) {p : ℝ[X]}
    (hp : p.degree < (N - 1 : ℕ)) {Λ : ℝ}
    (hvan : ∀ ρ : nonTrivialZeroSet, (ρ : ℂ).im ^ 2 < Λ → p.eval ((ρ : ℂ).im ^ 2) = 0) :
    Λ * (vecOf L N p ⬝ᵥ (MX L N *ᵥ vecOf L N p))
      ≤ (fun i => om L N i ^ 2 * vecOf L N p i) ⬝ᵥ (MX L N *ᵥ vecOf L N p) := by
  have hpN : p.degree < N := lt_of_lt_of_le hp (by exact_mod_cast Nat.sub_le N 1)
  refine mul_dotProduct_le_of_vanish hRH hL (vecOf_negI p) (om_dotProduct_vecOf_eq_zero hp)
    fun ρ hρ => ?_
  unfold Wdiv
  rw [xdiv_vecOf hL.ne' hpN]
  exact windowTransform_xOf_eq_zero hL hpN (hvan ρ hρ)

-- H_fix Step 3 (the roots of `g*` are `γ_1², …, γ_{k*−1}²` and `r_i`, `i > k*`)
/-- **The deflated product**: `∏_{i<k}(X − a_i)·∏_{k<i<n}(X − r_i) = ∏_{i<n−1}(X − r'_i)` with
`r'_i = a_i` for `i < k` and `r'_i = r_{i+1}` for `i ≥ k`. -/
theorem deflate_prod {a r : ℕ → ℝ} {k n : ℕ} (hk : k < n) :
    (∏ i ∈ Finset.range k, (X - C (a i))) * ∏ i ∈ Finset.Ioo k n, (X - C (r i))
      = ∏ i ∈ Finset.range (n - 1), (X - C (if i < k then a i else r (i + 1))) := by
  rw [← Finset.prod_range_mul_prod_Ico _ (show k ≤ n - 1 by omega)]
  congr 1
  · exact Finset.prod_congr rfl fun i hi => by rw [if_pos (Finset.mem_range.mp hi)]
  · rw [Finset.prod_congr (s₂ := Finset.Ico k (n - 1)) (g := fun i => X - C (r (i + 1))) rfl
        fun i hi => by rw [if_neg (not_lt.mpr (Finset.mem_Ico.mp hi).1)],
      Finset.prod_Ico_add' (fun i => X - C (r i)) k (n - 1) 1, Nat.sub_add_cancel (by omega),
      Finset.Ico_add_one_left_eq_Ioo]

/-- The deflated list dominates a monotone `a` when `r_i ≥ a_i` for `k < i < n`. -/
theorem deflate_dominates {a r : ℕ → ℝ} (ha : Monotone a) {k n : ℕ}
    (hr : ∀ i, k < i → i < n → a i ≤ r i) :
    ∀ i < n - 1, a i ≤ if i < k then a i else r (i + 1) := by
  intro i hi
  split_ifs with hik
  · exact le_rfl
  · exact (ha (Nat.le_succ i)).trans (hr (i + 1) (by omega) (by omega))

end Cvs.Finite.OddDisplacementPencil
