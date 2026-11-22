import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Cvs.Finite.DividedDifferenceCommutator
import Cvs.Finite.EigenvectorFormRealSpectrum
import Cvs.Finite.SelfAdjointRealSpectrum

/-!
# A spectral gap gives the kernel line, and the real spectrum

A gap below the second eigenvalue pins the kernel of `Q` to the line through `ξ`, which is
the hypothesis `finmain` needs; positive semidefiniteness comes with it.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Matrix Cvs.Finite.DividedDifferenceCommutator Cvs.Finite.SelfAdjointRealSpectrum Cvs.Finite.EigenvectorFormRealSpectrum

namespace Cvs.Finite.SpectralGapKernelLine

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- **The kernel is exactly the line through `ξ`.** -/
theorem eq_smul_of_mulVec_eq_zero {Q : Matrix ι ι ℝ} {xi : ι → ℝ} {gap : ℝ} (hgap : 0 < gap)
    (hbound : ∀ v : ι → ℝ, v ⬝ᵥ xi = 0 → gap * (v ⬝ᵥ v) ≤ v ⬝ᵥ (Q *ᵥ v))
    (hxi : Q *ᵥ xi = 0) (hnorm : xi ⬝ᵥ xi = 1)
    {u : ι → ℝ} (hu : Q *ᵥ u = 0) : u = (u ⬝ᵥ xi) • xi := by
  set c : ℝ := u ⬝ᵥ xi with hc
  set w : ι → ℝ := u - c • xi with hw
  have hwxi : w ⬝ᵥ xi = 0 := by
    rw [hw, sub_dotProduct, smul_dotProduct, hnorm, smul_eq_mul, mul_one, ← hc, sub_self]
  have hQw : Q *ᵥ w = 0 := by
    rw [hw, Matrix.mulVec_sub, Matrix.mulVec_smul, hu, hxi, smul_zero, sub_zero]
  have h0 : w ⬝ᵥ (Q *ᵥ w) = 0 := by rw [hQw, dotProduct_zero]
  have hb := hbound w hwxi
  rw [h0] at hb
  have hnn : 0 ≤ w ⬝ᵥ w := by
    rw [dotProduct]; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hww : w ⬝ᵥ w = 0 := le_antisymm (by nlinarith [hb, hgap, hnn]) hnn
  have hw0 : w = 0 := dotProduct_self_eq_zero.mp hww
  rw [hw, sub_eq_zero] at hw0
  exact hw0

omit [DecidableEq ι] in
/-- **`hkerline`, discharged.**  The form of the hypothesis `Dprime_real_spectrum` consumes. -/
theorem kerline_of_gap {Q : Matrix ι ι ℝ} {xi : ι → ℝ} {gap : ℝ} (hgap : 0 < gap)
    (hbound : ∀ v : ι → ℝ, v ⬝ᵥ xi = 0 → gap * (v ⬝ᵥ v) ≤ v ⬝ᵥ (Q *ᵥ v))
    (hxi : Q *ᵥ xi = 0) (hnorm : xi ⬝ᵥ xi = 1) :
    ∀ v : ι → ℝ, Q *ᵥ v = 0 → ∃ c : ℝ, v = c • xi :=
  fun v hv => ⟨v ⬝ᵥ xi, eq_smul_of_mulVec_eq_zero hgap hbound hxi hnorm hv⟩

omit [DecidableEq ι] in
/-- **Positive semidefiniteness, also from the gap.**  Splitting off the `ξ`-component, the
form is `0` plus something `≥ gap·‖·‖² ≥ 0`. -/
theorem posSemidef_of_gap {Q : Matrix ι ι ℝ} {xi : ι → ℝ} {gap : ℝ} (hgap : 0 < gap)
    (hQsymm : Q.IsSymm)
    (hbound : ∀ v : ι → ℝ, v ⬝ᵥ xi = 0 → gap * (v ⬝ᵥ v) ≤ v ⬝ᵥ (Q *ᵥ v))
    (hxi : Q *ᵥ xi = 0) (hnorm : xi ⬝ᵥ xi = 1) :
    ∀ v : ι → ℝ, 0 ≤ v ⬝ᵥ (Q *ᵥ v) := by
  intro v
  obtain ⟨c, w, hwxi, hveq⟩ : ∃ (c : ℝ) (w : ι → ℝ), w ⬝ᵥ xi = 0 ∧ v = w + c • xi :=
    ⟨v ⬝ᵥ xi, v - (v ⬝ᵥ xi) • xi,
      by rw [sub_dotProduct, smul_dotProduct, hnorm, smul_eq_mul, mul_one, sub_self],
      by abel⟩
  subst hveq
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, hxi, smul_zero, add_zero, add_dotProduct,
    smul_dotProduct]
  have hxw : xi ⬝ᵥ (Q *ᵥ w) = 0 := by
    rw [dotProduct_mulVec_comm hQsymm xi w, hxi, dotProduct_zero]
  rw [hxw, smul_eq_mul, mul_zero, add_zero]
  have hb := hbound w hwxi
  have hnn : 0 ≤ w ⬝ᵥ w := by
    rw [dotProduct]; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  nlinarith [hb, hgap, hnn]

/-! ### Simplicity of the truncation's bottom, elementarily -/

omit [DecidableEq ι] in
-- CvS get this from the min-max theorem; it is elementary.  A two-dimensional eigenspace
-- would meet the hyperplane `⟂ ξ`, and there the gap forces `lam + del ≤ lamN`.
/-- **Any two ground vectors of the truncation are proportional**, in the explicit form
`(v·ξ)u = (u·ξ)v` — what "the eigenspace is a line" says without mentioning dimension. -/
theorem ker_dependent_of_gap {Q : Matrix ι ι ℝ} {xi : ι → ℝ} {lam del lamN : ℝ}
    (hgap : ∀ w : ι → ℝ, w ⬝ᵥ xi = 0 → (lam + del) * (w ⬝ᵥ w) ≤ w ⬝ᵥ (Q *ᵥ w))
    (hlt : lamN < lam + del)
    {u v : ι → ℝ} (hu : Q *ᵥ u = lamN • u) (hv : Q *ᵥ v = lamN • v) :
    (v ⬝ᵥ xi) • u - (u ⬝ᵥ xi) • v = 0 := by
  set w : ι → ℝ := (v ⬝ᵥ xi) • u - (u ⬝ᵥ xi) • v with hw
  have hwxi : w ⬝ᵥ xi = 0 := by
    rw [hw, sub_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul]
    ring
  have hQw : Q *ᵥ w = lamN • w := by
    rw [hw, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, hu, hv, smul_sub,
      smul_comm, smul_comm lamN (u ⬝ᵥ xi) v]
  have hform : w ⬝ᵥ (Q *ᵥ w) = lamN * (w ⬝ᵥ w) := by
    rw [hQw, dotProduct_smul, smul_eq_mul]
  have hb := hgap w hwxi
  rw [hform] at hb
  have hnn : 0 ≤ w ⬝ᵥ w := by
    rw [dotProduct]; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hww : w ⬝ᵥ w = 0 := le_antisymm (by nlinarith [hb, hlt, hnn]) hnn
  exact dotProduct_self_eq_zero.mp hww

/-! ### `finmain`(i) with the auxiliary hypotheses discharged -/

variable {a b pos : ι → ℝ} {neg : ι → ι} {xi : ι → ℝ}

/-- **Theorem `finmain`(i), driven only by CvS's own hypotheses.**  Positive semidefiniteness
and the one-dimensional kernel are no longer assumed: both follow from the variational form of
"the bottom eigenvalue is simple and isolated". -/
theorem Dprime_real_spectrum_of_gap {gap : ℝ}
    (hposinj : Function.Injective pos) (hinv : Function.Involutive neg)
    (hb : ∀ i, b (neg i) = -b i) (hxieven : ∀ i, xi (neg i) = xi i)
    (hgap : 0 < gap)
    (hbound : ∀ v : ι → ℝ, v ⬝ᵥ xi = 0 → gap * (v ⬝ᵥ v) ≤ v ⬝ᵥ (ddMatrix a b pos *ᵥ v))
    (hQxi : ddMatrix a b pos *ᵥ xi = 0)
    (hunit : xi ⬝ᵥ xi = 1)
    (hnorm : ∑ i, xi i = 1)
    {al be : ℝ} (hbe : be ≠ 0) {x y : ι → ℝ}
    (hx : Dprime pos xi *ᵥ x = al • x - be • y)
    (hy : Dprime pos xi *ᵥ y = be • x + al • y) :
    x = 0 ∧ y = 0 :=
  Dprime_real_spectrum hposinj hinv hb hxieven
    (posSemidef_of_gap hgap ddMatrix_isSymm hbound hQxi hunit)
    hQxi hnorm (kerline_of_gap hgap hbound hQxi hunit) hbe hx hy

end Cvs.Finite.SpectralGapKernelLine
