import Mathlib
import Cvs.Approximant.ConnesCoefficientsNonvanishing
import Cvs.Approximant.ConnesEndpointGeometry
import Cvs.Approximant.ConnesLowModeGeometry
import Cvs.Approximant.ConnesVectorRealScale
import Cvs.Approximant.ThreeModeMassShiftFilters
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.UniversalFunctionPairing
import Cvs.Finite.WindowCosineBessel
import Cvs.Limit.OffAxesLimit

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The actual two-filter wedge has a positive Hermitian numerator

The two Connes-perpendicular cosine filters have an exact rational wedge.
Its coefficient matrix is positive when the actual first ratio is negative and second positive.
-/

noncomputable section
set_option maxHeartbeats 1000000
open Real Matrix Finset Filter
open scoped Topology ComplexConjugate
namespace Cvs.Approximant.TwoFilterWedgeNumerator
open Cvs.ZeroCounting
open Cvs.Finite.SymmetricModeSet (Idx mode negI)

/-- The coefficient of the mixed squared-frequency term. -/
def leading (r s : ℝ) : ℝ := 3+s-4*r

/-- The coefficient of either single squared-frequency term. -/
def middle (a r s : ℝ) : ℝ := -4*(s-r)*a

/-- The constant coefficient of the two-filter wedge numerator. -/
def constant (a r s : ℝ) : ℝ := 4*(4*s-r)*a^2

/-- The real two-by-two coefficient matrix of the rational wedge numerator. -/
def coefficientMatrix (a r s : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![leading r s, middle a r s; middle a r s, constant a r s]

/-- The symmetric two-variable numerator of the actual cosine-filter wedge. -/
def numerator (a r s : ℝ) (z w : ℂ) : ℂ :=
  (leading r s : ℂ)*z*w+(middle a r s : ℂ)*(z+w)+(constant a r s : ℂ)

/-- The common three-frequency denominator. -/
def denominator (a : ℝ) (z : ℂ) : ℂ :=
  (-z)*((a : ℂ)-z)*(4*(a : ℂ)-z)

/-- The rational filter of the first cosine minus its actual normal ratio. -/
def filterU (a r : ℝ) (z : ℂ) : ℂ := (r : ℂ)/z+1/((a : ℂ)-z)

/-- The rational filter of the second cosine minus its actual normal ratio. -/
def filterV (a s : ℝ) (z : ℂ) : ℂ := (s : ℂ)/z+1/(4*(a : ℂ)-z)

/-- The numerator's coefficient determinant is an explicit product polynomial. -/
theorem coefficient_det (a r s : ℝ) :
    (coefficientMatrix a r s).det=12*a^2*(s*(4-3*r)-r) := by
  simp only [coefficientMatrix, Matrix.det_fin_two_of, leading, middle, constant]
  ring

private theorem coefficient_product (a r s : ℝ) :
    leading r s*constant a r s-(middle a r s)^2=12*a^2*(s*(4-3*r)-r) := by
  unfold leading middle constant
  ring

/-- Negative first ratio and positive second ratio make the leading coefficient positive. -/
theorem leading_pos {r s : ℝ} (hr : r < 0) (hs : 0 < s) : 0 < leading r s := by
  unfold leading
  linarith

/-- The exact coefficient determinant is positive at every positive squared frequency. -/
theorem coefficient_det_pos {a r s : ℝ} (ha : 0 < a) (hr : r < 0) (hs : 0 < s) :
    0 < (coefficientMatrix a r s).det := by
  rw [coefficient_det]
  have h4 : 0 < 4-3*r := by linarith
  have hp : 0 < s*(4-3*r)-r := by have h := mul_pos hs h4; linarith
  positivity

private theorem quadratic_pos {a r s : ℝ} (ha : 0 < a) (hr : r < 0) (hs : 0 < s)
    (x y : ℝ) (hxy : x ≠ 0 ∨ y ≠ 0) :
    0 < leading r s*x^2+2*middle a r s*x*y+constant a r s*y^2 := by
  have hA := leading_pos hr hs
  have hD : 0 < leading r s*constant a r s-(middle a r s)^2 := by
    rw [coefficient_product]
    simpa only [coefficient_det] using coefficient_det_pos ha hr hs
  have he : leading r s*(leading r s*x^2+2*middle a r s*x*y+constant a r s*y^2)=
      (leading r s*x+middle a r s*y)^2+
        (leading r s*constant a r s-(middle a r s)^2)*y^2 := by ring
  by_cases hy : y=0
  · have hx : x ≠ 0 := by simpa [hy] using hxy
    simpa [hy] using mul_pos hA (sq_pos_of_ne_zero hx)
  · have hp := mul_pos hD (sq_pos_of_ne_zero hy)
    have hn := sq_nonneg (leading r s*x+middle a r s*y)
    exact pos_of_mul_pos_left (by nlinarith [he]) hA.le

/-- The actual numerator coefficient matrix is positive definite under the two ratio signs. -/
theorem coefficientMatrix_posDef {a r s : ℝ} (ha : 0 < a) (hr : r < 0) (hs : 0 < s) :
    (coefficientMatrix a r s).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext i j
    fin_cases i  <;> fin_cases j  <;> simp [coefficientMatrix]
  · intro x hx
    have hxy : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
      by_cases hx0 : x 0=0
      · right
        intro hx1
        apply hx
        funext i
        fin_cases i  <;> simp [hx0, hx1]
      · exact Or.inl hx0
    have hp := quadratic_pos ha hr hs (x 0) (x 1) hxy
    simp [dotProduct, mulVec, Fin.sum_univ_two, coefficientMatrix]
    nlinarith [hp]

/-- On conjugate arguments the numerator is its real quadratic expression. -/
theorem numerator_conj_eq (a r s : ℝ) (z : ℂ) :
    numerator a r s z (conj z)=
      ((leading r s*(z.re^2+z.im^2)+2*middle a r s*z.re+constant a r s : ℝ) : ℂ) := by
  apply Complex.ext  <;> simp [numerator, pow_two, Complex.mul_re, Complex.mul_im]  <;> ring

/-- The Hermitian numerator is strictly positive on every conjugate pair. -/
theorem numerator_conj_re_pos {a r s : ℝ} (ha : 0 < a) (hr : r < 0) (hs : 0 < s) (z : ℂ) :
    0 < (numerator a r s z (conj z)).re := by
  rw [numerator_conj_eq, Complex.ofReal_re]
  have hp := quadratic_pos ha hr hs z.re 1 (Or.inr one_ne_zero)
  have hA := leading_pos hr hs
  nlinarith [sq_nonneg z.im]

/-- The positive Hermitian numerator cannot vanish on a conjugate pair. -/
theorem numerator_conj_ne_zero {a r s : ℝ} (ha : 0 < a) (hr : r < 0) (hs : 0 < s) (z : ℂ) :
    numerator a r s z (conj z) ≠ 0 := by
  intro h
  have hp := numerator_conj_re_pos ha hr hs z
  rw [h, Complex.zero_re] at hp
  exact lt_irrefl 0 hp

private theorem denominator_factors {a : ℝ} {z : ℂ} (hz : denominator a z ≠ 0) :
    z ≠ 0 ∧ (a : ℂ)-z ≠ 0 ∧ 4*(a : ℂ)-z ≠ 0 := by
  have h := mul_ne_zero_iff.mp hz
  have h' := mul_ne_zero_iff.mp h.1
  exact ⟨neg_ne_zero.mp h'.1, h'.2, h.2⟩

/-- The actual induction-basis rational wedge has its exact two-variable numerator. -/
theorem rational_wedge (a r s : ℝ) (z w : ℂ)
    (hz : denominator a z ≠ 0) (hw : denominator a w ≠ 0) :
    filterU a r z*filterV a s w-filterV a s z*filterU a r w=
      (a : ℂ)*(z-w)*numerator a r s z w/(denominator a z*denominator a w) := by
  obtain ⟨hz0,hz1,hz2⟩ := denominator_factors hz
  obtain ⟨hw0,hw1,hw2⟩ := denominator_factors hw
  have hz2' : (a : ℂ)*4-z ≠ 0 := by simpa only [mul_comm] using hz2
  have hw2' : (a : ℂ)*4-w ≠ 0 := by simpa only [mul_comm] using hw2
  unfold filterU filterV numerator denominator leading middle constant
  push_cast
  field_simp [hz0,hz1,hz2,hz2',hw0,hw1,hw2,hw2']
  ring

private theorem denominator_ne_zero_of_im {a : ℝ} {z : ℂ} (hz : z.im ≠ 0) :
    denominator a z ≠ 0 := by
  have hz0 : z ≠ 0 := by intro h; exact hz (by simp [h])
  have hn (b : ℝ) : (b : ℂ)-z ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.ofReal_im, Complex.zero_im] at hi
    exact hz (by linarith)
  unfold denominator
  exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hz0) (hn a))
    (by simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat] using hn (4*a))

/-- The Hermitian numerator is an exact sum of three squared complex distances. -/
theorem numerator_conj_eq_squares (a r s : ℝ) (z : ℂ) :
    numerator a r s z (conj z)=
      ((3*Complex.normSq z-4*r*Complex.normSq ((a : ℂ)-z)+
        s*Complex.normSq (4*(a : ℂ)-z) : ℝ) : ℂ) := by
  rw [numerator_conj_eq]
  congr 1
  simp [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, leading, middle, constant]
  ring

/-- Nonpositive first ratio and nonnegative second ratio give strict Hermitian positivity away from zero. -/
theorem numerator_conj_re_pos_of_ne_zero {a r s : ℝ} (hr : r ≤ 0) (hs : 0 ≤ s)
    {z : ℂ} (hz : z ≠ 0) : 0 < (numerator a r s z (conj z)).re := by
  rw [numerator_conj_eq_squares, Complex.ofReal_re]
  have hp : 0 < Complex.normSq z := Complex.normSq_pos.mpr hz
  have h1 : 0 ≤ -4*r*Complex.normSq ((a : ℂ)-z) :=
    mul_nonneg (by linarith) (Complex.normSq_nonneg _)
  have h2 : 0 ≤ s*Complex.normSq (4*(a : ℂ)-z) :=
    mul_nonneg hs (Complex.normSq_nonneg _)
  linarith

/-- The two actual rational filters are real-independent at every nonreal squared frequency. -/
theorem rational_wedge_conj_ne_zero {a r s : ℝ} (ha : a ≠ 0) (hr : r ≤ 0) (hs : 0 ≤ s)
    {z : ℂ} (hz : z.im ≠ 0) :
    filterU a r z*filterV a s (conj z)-filterV a s z*filterU a r (conj z) ≠ 0 := by
  have hz' : (conj z).im ≠ 0 := by simpa using hz
  rw [rational_wedge _ _ _ _ _ (denominator_ne_zero_of_im hz)
    (denominator_ne_zero_of_im hz')]
  have hd : z-conj z ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.conj_im, Complex.zero_im] at hi
    exact hz (by linarith)
  have hz0 : z ≠ 0 := by intro h; exact hz (by simp [h])
  have hJ : numerator a r s z (conj z) ≠ 0 := by
    intro h
    have hp := numerator_conj_re_pos_of_ne_zero hr hs hz0 (a := a)
    rw [h, Complex.zero_re] at hp
    exact lt_irrefl 0 hp
  exact div_ne_zero
    (mul_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr ha) hd) hJ)
    (mul_ne_zero (denominator_ne_zero_of_im hz) (denominator_ne_zero_of_im hz'))

/-- The first signed cosine profile has the first rational filter at squared frequency. -/
theorem S_profileU {N : ℕ} (hN : 2 ≤ N) (L r : ℝ) (z : ℂ) :
    Cvs.Finite.UniversalFunctionPairing.S L (mode N) (Cvs.Approximant.ThreeModeMassShiftFilters.profileCoeffs N (-r) 1 0) z=
      filterU ((Cvs.Approximant.ConnesEndpointGeometry.frequency L 1)^2) r (z^2) := by
  rw [Cvs.Approximant.ThreeModeMassShiftFilters.S_profileCoeffs hN]
  simp [filterU, Complex.ofReal_pow]

/-- The second signed cosine profile has the second rational filter at squared frequency. -/
theorem S_profileV {N : ℕ} (hN : 2 ≤ N) (L s : ℝ) (z : ℂ) :
    Cvs.Finite.UniversalFunctionPairing.S L (mode N) (Cvs.Approximant.ThreeModeMassShiftFilters.profileCoeffs N (-s) 0 1) z=
      filterV ((Cvs.Approximant.ConnesEndpointGeometry.frequency L 1)^2) s (z^2) := by
  rw [Cvs.Approximant.ThreeModeMassShiftFilters.S_profileCoeffs hN]
  simp [filterV, Complex.ofReal_pow]

/-- The centered two-cosine rational evaluations have nonzero off-axis wedge under the ratio signs. -/
theorem S_profiles_wedge_ne_zero {L : ℝ} (hL : 0 < L) {N : ℕ} (hN : 2 ≤ N)
    {r s : ℝ} (hr : r ≤ 0) (hs : 0 ≤ s) {z : ℂ} (hz : z∈Cvs.Limit.OffAxesLimit.offAxes) :
    Cvs.Finite.UniversalFunctionPairing.S L (mode N) (Cvs.Approximant.ThreeModeMassShiftFilters.profileCoeffs N (-r) 1 0) z*
      Cvs.Finite.UniversalFunctionPairing.S L (mode N) (Cvs.Approximant.ThreeModeMassShiftFilters.profileCoeffs N (-s) 0 1) (conj z)-
    Cvs.Finite.UniversalFunctionPairing.S L (mode N) (Cvs.Approximant.ThreeModeMassShiftFilters.profileCoeffs N (-s) 0 1) z*
      Cvs.Finite.UniversalFunctionPairing.S L (mode N) (Cvs.Approximant.ThreeModeMassShiftFilters.profileCoeffs N (-r) 1 0) (conj z) ≠ 0 := by
  rw [S_profileU hN, S_profileV hN, S_profileV hN, S_profileU hN]
  have hz2 : (z^2).im ≠ 0 := fun h => Cvs.Limit.OffAxesLimit.notMem_offAxes_of_sq_im h hz
  simpa only [map_pow] using rational_wedge_conj_ne_zero
    (sq_pos_of_pos (Cvs.Approximant.ConnesEndpointGeometry.frequency_pos hL (by norm_num : 0 < 1))).ne' hr hs hz2

/-- The unsigned cosine coefficient ratios of the actual Connes profile. -/
def ratio (x : ℝ) (n : ℕ) : ℝ := Cvs.Approximant.ConnesLowModeGeometry.coef x n/(2*Cvs.Approximant.ConnesLowModeGeometry.coef x 0)

/-- The actual first-ratio cosine profile is perpendicular to the actual Connes normal. -/
theorem profileU_connes_orthogonal (x : ℝ) {N : ℕ} (hN : 2 ≤ N)
    (h0 : Cvs.Approximant.ConnesLowModeGeometry.coef x 0 ≠ 0) :
    Cvs.Approximant.ThreeModeMassShiftFilters.profileCoeffs N (-ratio x 1) 1 0 ⬝ᵥ Cvs.Approximant.ConnesVectorRealScale.connesCoef x N=0 := by
  rw [Cvs.Approximant.ThreeModeMassShiftFilters.profileCoeffs, Cvs.Approximant.ConnesEndpointGeometry.threeMode_pair hN, Cvs.Approximant.ConnesCoefficientsNonvanishing.connesCoef_none,
    Cvs.Approximant.ConnesLowModeGeometry.connesCoef_first x (by omega), Cvs.Approximant.ConnesLowModeGeometry.connesCoef_first x (by omega)]
  simp only [zero_div, zero_mul, add_zero]
  change -(Cvs.Approximant.ConnesLowModeGeometry.coef x 1/(2*Cvs.Approximant.ConnesLowModeGeometry.coef x 0))*Cvs.Approximant.ConnesLowModeGeometry.coef x 0+
    (1/2)*(Cvs.Approximant.ConnesLowModeGeometry.coef x 1/2+Cvs.Approximant.ConnesLowModeGeometry.coef x 1/2)=0
  field_simp
  ring

/-- The actual second-ratio cosine profile is perpendicular to the actual Connes normal. -/
theorem profileV_connes_orthogonal (x : ℝ) {N : ℕ} (hN : 2 ≤ N)
    (h0 : Cvs.Approximant.ConnesLowModeGeometry.coef x 0 ≠ 0) :
    Cvs.Approximant.ThreeModeMassShiftFilters.profileCoeffs N (-ratio x 2) 0 1 ⬝ᵥ Cvs.Approximant.ConnesVectorRealScale.connesCoef x N=0 := by
  rw [Cvs.Approximant.ThreeModeMassShiftFilters.profileCoeffs, Cvs.Approximant.ConnesEndpointGeometry.threeMode_pair hN, Cvs.Approximant.ConnesCoefficientsNonvanishing.connesCoef_none,
    Cvs.Approximant.ConnesEndpointGeometry.connesCoef_second x hN true, Cvs.Approximant.ConnesEndpointGeometry.connesCoef_second x hN false]
  simp only [zero_div, zero_mul, add_zero]
  change -(Cvs.Approximant.ConnesLowModeGeometry.coef x 2/(2*Cvs.Approximant.ConnesLowModeGeometry.coef x 0))*Cvs.Approximant.ConnesLowModeGeometry.coef x 0+
    (1/2)*(Cvs.Approximant.ConnesLowModeGeometry.coef x 2/2+Cvs.Approximant.ConnesLowModeGeometry.coef x 2/2)=0
  field_simp
  ring

/-- The actual-ratio cosine filters have nonzero off-axis wedge at the two ratio signs. -/
theorem actual_S_wedge_ne_zero {x : ℝ} (hx : 1 < x) {N : ℕ} (hN : 2 ≤ N)
    (hr : ratio x 1 ≤ 0) (hs : 0 ≤ ratio x 2) {z : ℂ} (hz : z∈Cvs.Limit.OffAxesLimit.offAxes) :
    Cvs.Finite.UniversalFunctionPairing.S (log x) (mode N) (Cvs.Approximant.ThreeModeMassShiftFilters.profileCoeffs N (-ratio x 1) 1 0) z*
      Cvs.Finite.UniversalFunctionPairing.S (log x) (mode N) (Cvs.Approximant.ThreeModeMassShiftFilters.profileCoeffs N (-ratio x 2) 0 1) (conj z)-
    Cvs.Finite.UniversalFunctionPairing.S (log x) (mode N) (Cvs.Approximant.ThreeModeMassShiftFilters.profileCoeffs N (-ratio x 2) 0 1) z*
      Cvs.Finite.UniversalFunctionPairing.S (log x) (mode N) (Cvs.Approximant.ThreeModeMassShiftFilters.profileCoeffs N (-ratio x 1) 1 0) (conj z) ≠ 0 :=
  S_profiles_wedge_ne_zero (log_pos hx) hN hr hs hz

end Cvs.Approximant.TwoFilterWedgeNumerator
