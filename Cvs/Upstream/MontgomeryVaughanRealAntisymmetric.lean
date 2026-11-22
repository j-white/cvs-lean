import Mathlib

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Montgomery–Vaughan for real vectors and the antisymmetric kernel

From `Cvs.Zeta.Base.MV.mvDiag_thirteen`: for distinct real `λ_r`, admissible gaps `δ_r`, real `x, z` and `s > 0`,
`|Σ_{r≠t} x_r z_t/(λ_r − λ_t)| ≤ (13/2)(s² Σ x_r²/δ_r + Σ z_r²/δ_r/s²)`, by applying the diagonal form to
`y = s x + i z/s`: the symmetric parts cancel against the antisymmetric kernel and the rest is `−2i` times the form.
-/

noncomputable section

namespace Cvs.Upstream.MontgomeryVaughanRealAntisymmetric

open Finset Complex
open scoped ComplexConjugate

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The antisymmetric kernel `T_{rt} = 1/(λ_r − λ_t)` off the diagonal. -/
def T (freq : ι → ℝ) (r t : ι) : ℂ := if r = t then 0 else 1 / ((freq r - freq t : ℝ) : ℂ)

omit [Fintype ι] in
theorem T_swap (freq : ι → ℝ) (r t : ι) : T freq t r = -T freq r t := by
  unfold T
  by_cases h : r = t
  · subst h; simp
  · rw [if_neg (Ne.symm h), if_neg h]
    have e : ((freq t - freq r : ℝ) : ℂ) = -((freq r - freq t : ℝ) : ℂ) := by push_cast; ring
    rw [e, one_div, one_div, inv_neg]

/-- **A symmetric weight against the antisymmetric kernel sums to zero.** -/
theorem sum_sym_T (freq : ι → ℝ) (f : ι → ι → ℂ) (hf : ∀ r t, f r t = f t r) :
    ∑ r, ∑ t, f r t * T freq r t = 0 := by
  have h : ∑ r, ∑ t, f r t * T freq r t = -∑ r, ∑ t, f r t * T freq r t := by
    conv_lhs => rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro r _
    rw [← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro t _
    rw [T_swap, hf]; ring
  have h2 : (2 : ℂ) * ∑ r, ∑ t, f r t * T freq r t = 0 := by rw [two_mul]; nth_rewrite 2 [h]; ring
  simpa using h2

end Cvs.Upstream.MontgomeryVaughanRealAntisymmetric
