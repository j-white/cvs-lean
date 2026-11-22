import Mathlib
import Cvs.Finite.CosineModeOverlap
import Cvs.Finite.DividedDifferenceCommutator
import Cvs.Finite.LevyChannelDoubleSum
import Cvs.Finite.LevyKernelIncrement
import Cvs.Finite.ModeSumPairValues
import Cvs.Finite.OddSectorSineSums
import Cvs.Finite.PairFormDividedDifference
import Cvs.Finite.TruncationZeroFreeOffAxes
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.LevyDensity
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.Zeta.PrimePowerSideTruncated
import Cvs.Zeta.WeilPositivityStatement

/-!
# The CvS quadratic form on every real vector

The matrix commutes with the involution, so the cross term between even and odd parts vanishes:
`L · v ⬝ (M v) = weilForm (modeSum (even part)) + weilForm (sineSum (odd part))`, and likewise for
the norms. Positivity of the window form on all window functions is thus `M − λ ≥ 0` on `ℝ^ι`.
-/

noncomputable section

open Real MeasureTheory Set Cvs.Zeta.Explicit.Weil Matrix

namespace Cvs.Finite.TruncationQuadraticForm

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The CvS matrix** at scale `L`, truncation `P R`, on the mode set `mode`. -/
def M (P R : ℕ) (L : ℝ) (mode : ι → ℤ) : Matrix ι ι ℝ :=
  Cvs.Finite.DividedDifferenceCommutator.ddMatrix (fun k => Cvs.Finite.PairFormDividedDifference.aval P R L (mode k))
    (fun k => Cvs.Finite.PairFormDividedDifference.bval P R L (mode k)) (Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode)

theorem M_apply {L : ℝ} (hL : 0 < L) (P R : ℕ) {mode : ι → ℤ} (hinj : Function.Injective mode)
    (i j : ι) : M P R L mode i j = Cvs.Finite.ModeSumPairValues.pairQ P R L (mode i) (mode j) / 2 :=
  Cvs.Finite.PairFormDividedDifference.ddMatrix_eq hL P R hinj i j

/-- The pair value is invariant under negating both modes. -/
theorem pairQ_neg_neg (P R : ℕ) (L : ℝ) (m n : ℤ) :
    Cvs.Finite.ModeSumPairValues.pairQ P R L (-m) (-n) = Cvs.Finite.ModeSumPairValues.pairQ P R L m n := by
  have hKc : Cvs.Finite.LevyKernelIncrement.Kc L (-m) (-n) = Cvs.Finite.LevyKernelIncrement.Kc L m n := by
    funext v; unfold Cvs.Finite.LevyKernelIncrement.Kc; rw [Cvs.Finite.OddSectorSineSums.K_neg_neg]
  unfold Cvs.Finite.ModeSumPairValues.pairQ Cvs.Finite.ModeSumPairValues.polePair Cvs.Finite.LevyChannelDoubleSum.levyPair
    Cvs.Finite.ModeSumPairValues.primePair
  rw [hKc, Cvs.Finite.OddSectorSineSums.K_neg_neg]

/-- The pair value is symmetric. -/
theorem pairQ_symm {L : ℝ} (hL : 0 < L) (P R : ℕ) (m n : ℤ) :
    Cvs.Finite.ModeSumPairValues.pairQ P R L m n = Cvs.Finite.ModeSumPairValues.pairQ P R L n m := by
  by_cases hmn : m = n
  · subst hmn; rfl
  · have h1 := Cvs.Finite.PairFormDividedDifference.pairQ_off hL P R hmn
    have h2 := Cvs.Finite.PairFormDividedDifference.pairQ_off hL P R (Ne.symm hmn)
    have hden : 2 * π * m / L - 2 * π * n / L ≠ 0 := by
      have : (m : ℝ) - n ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hmn)
      have hπ : π ≠ 0 := Real.pi_ne_zero
      have hL0 : L ≠ 0 := hL.ne'
      rw [show 2 * π * m / L - 2 * π * n / L = 2 * π * ((m : ℝ) - n) / L by ring]
      exact div_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hπ) this) hL0
    have hden' : 2 * π * n / L - 2 * π * m / L = -(2 * π * m / L - 2 * π * n / L) := by ring
    rw [hden'] at h2
    have : Cvs.Finite.ModeSumPairValues.pairQ P R L m n / 2 = Cvs.Finite.ModeSumPairValues.pairQ P R L n m / 2 := by
      rw [h1, h2, div_neg]; ring
    linarith

/-- **The CvS matrix commutes with the involution.** -/
theorem M_neg_neg {L : ℝ} (hL : 0 < L) (P R : ℕ) {mode : ι → ℤ} (hinj : Function.Injective mode)
    {neg : ι → ι} (hmode : ∀ i, mode (neg i) = -mode i) (i j : ι) :
    M P R L mode (neg i) (neg j) = M P R L mode i j := by
  rw [M_apply hL P R hinj, M_apply hL P R hinj, hmode, hmode, pairQ_neg_neg]

/-- **The CvS matrix is symmetric.** -/
theorem M_symm {L : ℝ} (hL : 0 < L) (P R : ℕ) {mode : ι → ℤ} (hinj : Function.Injective mode)
    (i j : ι) : M P R L mode i j = M P R L mode j i := by
  rw [M_apply hL P R hinj, M_apply hL P R hinj, pairQ_symm hL]

/-! ### Even and odd parts -/

/-- The even part of a vector under the involution. -/
def evenPart (neg : ι → ι) (v : ι → ℝ) : ι → ℝ := fun i => (v i + v (neg i)) / 2

/-- The odd part of a vector under the involution. -/
def oddPart (neg : ι → ι) (v : ι → ℝ) : ι → ℝ := fun i => (v i - v (neg i)) / 2

omit [Fintype ι] [DecidableEq ι] in
theorem evenPart_even {neg : ι → ι} (hinv : Function.Involutive neg) (v : ι → ℝ) (i : ι) :
    evenPart neg v (neg i) = evenPart neg v i := by
  simp only [evenPart, hinv i]; ring

omit [Fintype ι] [DecidableEq ι] in
theorem oddPart_odd {neg : ι → ι} (hinv : Function.Involutive neg) (v : ι → ℝ) (i : ι) :
    oddPart neg v (neg i) = -oddPart neg v i := by
  simp only [oddPart, hinv i]; ring

omit [Fintype ι] [DecidableEq ι] in
theorem evenPart_add_oddPart (neg : ι → ι) (v : ι → ℝ) : evenPart neg v + oddPart neg v = v := by
  funext i; simp only [Pi.add_apply, evenPart, oddPart]; ring

omit [DecidableEq ι] in
/-- **A matrix commuting with the involution pairs even against odd to zero.** -/
theorem dotProduct_mulVec_eq_zero {A : Matrix ι ι ℝ} {neg : ι → ι} (hinv : Function.Involutive neg)
    (hA : ∀ i j, A (neg i) (neg j) = A i j) {e o : ι → ℝ} (he : ∀ i, e (neg i) = e i)
    (ho : ∀ i, o (neg i) = -o i) : e ⬝ᵥ (A *ᵥ o) = 0 := by
  have hexp : e ⬝ᵥ (A *ᵥ o) = ∑ i, e i * ∑ j, A i j * o j := by
    simp only [dotProduct, Matrix.mulVec]
  have houter := Equiv.sum_comp (Function.Involutive.toPerm neg hinv)
    (fun i => e i * ∑ j, A i j * o j)
  simp only [Function.Involutive.coe_toPerm] at houter
  have hinner : ∀ i, ∑ j, A (neg i) (neg j) * o (neg j) = ∑ j, A (neg i) j * o j := by
    intro i
    have := Equiv.sum_comp (Function.Involutive.toPerm neg hinv) (fun j => A (neg i) j * o j)
    simpa only [Function.Involutive.coe_toPerm] using this
  have key : e ⬝ᵥ (A *ᵥ o) = -(e ⬝ᵥ (A *ᵥ o)) := by
    calc e ⬝ᵥ (A *ᵥ o) = ∑ i, e i * ∑ j, A i j * o j := hexp
      _ = ∑ i, e (neg i) * ∑ j, A (neg i) j * o j := houter.symm
      _ = ∑ i, e (neg i) * ∑ j, A (neg i) (neg j) * o (neg j) := by simp only [hinner]
      _ = ∑ i, e i * ∑ j, A i j * (-o j) := by simp only [he, hA, ho]
      _ = -(∑ i, e i * ∑ j, A i j * o j) := by
          simp only [mul_neg, Finset.sum_neg_distrib]
      _ = -(e ⬝ᵥ (A *ᵥ o)) := by rw [hexp]
  linarith

omit [DecidableEq ι] in
/-- **The quadratic form splits into its even and odd parts.** -/
theorem dotProduct_mulVec_split {A : Matrix ι ι ℝ} (hsymm : ∀ i j, A i j = A j i)
    {neg : ι → ι} (hinv : Function.Involutive neg)
    (hA : ∀ i j, A (neg i) (neg j) = A i j) (v : ι → ℝ) :
    v ⬝ᵥ (A *ᵥ v) = evenPart neg v ⬝ᵥ (A *ᵥ evenPart neg v)
      + oddPart neg v ⬝ᵥ (A *ᵥ oddPart neg v) := by
  have hcross := dotProduct_mulVec_eq_zero hinv hA (evenPart_even hinv v) (oddPart_odd hinv v)
  have hcross' : oddPart neg v ⬝ᵥ (A *ᵥ evenPart neg v) = 0 := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
    have : Aᵀ = A := by ext i j; exact hsymm j i
    rw [this, dotProduct_comm]
    exact hcross
  conv_lhs => rw [← evenPart_add_oddPart neg v]
  rw [Matrix.mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct, hcross, hcross']
  ring

theorem dotProduct_split {neg : ι → ι} (hinv : Function.Involutive neg) (v : ι → ℝ) :
    v ⬝ᵥ v = evenPart neg v ⬝ᵥ evenPart neg v + oddPart neg v ⬝ᵥ oddPart neg v := by
  have h := dotProduct_mulVec_split (A := (1 : Matrix ι ι ℝ))
    (fun i j => by simp [Matrix.one_apply, eq_comm]) hinv
    (fun i j => by simp [Matrix.one_apply, hinv.injective.eq_iff]) v
  simpa using h

/-! ### The form on every vector -/

/-- **`L` times the CvS quadratic form is the Weil form on the cosine and sine sums.** -/
theorem quadForm_eq_weil {L : ℝ} (hL : 0 < L) (P R : ℕ) {mode : ι → ℤ}
    (hinj : Function.Injective mode) {neg : ι → ι} (hinv : Function.Involutive neg)
    (hmode : ∀ i, mode (neg i) = -mode i) (v : ι → ℝ) :
    L * (v ⬝ᵥ (M P R L mode *ᵥ v))
      = Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L mode (evenPart neg v))
        + Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R
            (Cvs.Finite.OddSectorSineSums.sineSum L mode (oddPart neg v)) := by
  rw [dotProduct_mulVec_split (M_symm hL P R hinj) hinv (M_neg_neg hL P R hinj hmode) v, mul_add,
    Cvs.Finite.PairFormDividedDifference.weilForm_modeSum_eq_ddMatrix hL P R hinj hinv hmode (evenPart_even hinv v),
    Cvs.Finite.OddSectorSineSums.weilForm_sineSum_eq_ddMatrix hL P R hinj hinv hmode (oddPart_odd hinv v)]
  rfl

/-- **`L` times the coefficient norm is the squared norm of the cosine and sine sums.** -/
theorem dot_eq_norm {L : ℝ} (hL : 0 < L) {mode : ι → ℤ}
    (hinj : Function.Injective mode) {neg : ι → ι} (hinv : Function.Involutive neg)
    (hmode : ∀ i, mode (neg i) = -mode i) (v : ι → ℝ) :
    L * (v ⬝ᵥ v)
      = selfConvolution (Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L mode (evenPart neg v)) 0
        + selfConvolution (Cvs.Finite.OddSectorSineSums.sineSum L mode (oddPart neg v)) 0 := by
  rw [dotProduct_split hinv v, mul_add,
    Cvs.Finite.PairFormDividedDifference.selfConvolution_modeSum_zero hL hinj hinv hmode (evenPart_even hinv v),
    Cvs.Finite.OddSectorSineSums.selfConvolution_sineSum_zero hL hinj hinv hmode (oddPart_odd hinv v)]

end Cvs.Finite.TruncationQuadraticForm
