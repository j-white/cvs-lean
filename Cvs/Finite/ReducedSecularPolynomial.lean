import Mathlib
import Cvs.Finite.SecularRealRooted
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationQuadraticForm
import Cvs.Finite.TruncationZeroFreeOffAxes
import Cvs.Finite.UniversalFunctionPairing
import Cvs.Limit.OffAxesLimit
import Cvs.Limit.SpineWithoutSimplicity
import Cvs.Upstream.FourierLaplace
import Cvs.WeilForm.SelfConvolutionTransform

/-!
# Step (b) on the reduced secular polynomial
For an even vector on `Idx N` the secular sum is `S(z) = secPoly(z²)/(−z²·∏_j (q_j − z²))`, where `secPoly` is a
polynomial of degree `N` over the reflection pairs (`S_mul_eq_secPoly`). The ground state's `secPoly(z²)` is zero-free
off the axes (`secPoly_ground_ne_zero`), so step (b) can be asked of these polynomials instead of the transforms
(`riemannHypothesis_of_secPoly`); `secPoly(0) = x₀·∏ q_j`.
-/

noncomputable section

open Real Matrix Filter Topology

namespace Cvs.Finite.ReducedSecularPolynomial
open Cvs.ZeroCounting

open Cvs.Finite.SymmetricModeSet

/-- The squared frequency of the pair `j`. -/
def qf (L : ℝ) (N : ℕ) (j : Fin N) : ℂ := ((2 * π * ((j : ℕ) + 1 : ℝ) / L : ℝ) : ℂ) ^ 2

/-- **The reduced secular polynomial** `x₀ ∏_j (q_j − w) + ∑_j (x_j⁺ + x_j⁻)(−w) ∏_{j' ≠ j} (q_{j'} − w)`. -/
def secPoly (L : ℝ) (N : ℕ) (xi : Idx N → ℝ) (w : ℂ) : ℂ :=
  (xi none : ℂ) * ∏ j, (qf L N j - w)
    + ∑ j, ((xi (some (j, true)) + xi (some (j, false)) : ℝ) : ℂ) * (-w)
        * ∏ j' ∈ Finset.univ.erase j, (qf L N j' - w)

theorem secPoly_zero (L : ℝ) (N : ℕ) (xi : Idx N → ℝ) :
    secPoly L N xi 0 = (xi none : ℂ) * ∏ j, qf L N j := by
  simp [secPoly]

/-- **The secular sum times its denominator is the reduced polynomial.** -/
theorem S_mul_eq_secPoly {L : ℝ} (N : ℕ) (xi : Idx N → ℝ) {ξ : ℂ} (h0 : ξ ^ 2 ≠ 0)
    (hq : ∀ j, qf L N j - ξ ^ 2 ≠ 0) :
    Cvs.Finite.UniversalFunctionPairing.S L (mode N) xi ξ * (-ξ ^ 2 * ∏ j, (qf L N j - ξ ^ 2))
      = secPoly L N xi (ξ ^ 2) := by
  have hnone : (((2 * π * (mode N none : ℝ) / L : ℝ) : ℂ)) ^ 2 = 0 := by simp [mode]
  have ht : ∀ j : Fin N, (((2 * π * (mode N (some (j, true)) : ℝ) / L : ℝ) : ℂ)) ^ 2 = qf L N j := by
    intro j; simp only [mode, ite_true, qf]; push_cast; ring
  have hf : ∀ j : Fin N, (((2 * π * (mode N (some (j, false)) : ℝ) / L : ℝ) : ℂ)) ^ 2 = qf L N j := by
    intro j; simp only [mode, Bool.false_eq_true, ite_false, qf]; push_cast; ring
  unfold Cvs.Finite.UniversalFunctionPairing.S secPoly
  rw [Fintype.sum_option]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, hnone, ht, hf]
  rw [add_mul, Finset.sum_mul]
  refine congrArg₂ (· + ·) ?_ ?_
  · field_simp
    ring
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.mul_prod_erase Finset.univ (fun j => qf L N j - ξ ^ 2) (Finset.mem_univ j)]
    have hqj := hq j
    field_simp
    push_cast
    ring

/-- **The ground state's reduced secular polynomial is zero-free off the axes.** -/
theorem secPoly_ground_ne_zero {L : ℝ} (hL : 0 < L) (P R N : ℕ) {z : ℂ}
    (hz : z ∈ Cvs.Limit.OffAxesLimit.offAxes) :
    secPoly L N (Cvs.Limit.SpineWithoutSimplicity.ground P R L hL N) (z ^ 2) ≠ 0 := by
  obtain ⟨hge, -, -, -, hzf⟩ := Cvs.Limit.SpineWithoutSimplicity.ground_spec P R hL N
  have hz0 : ∀ i, ((Cvs.Finite.TruncationZeroFreeOffAxes.omega L (mode N) i : ℝ) : ℂ) + z ≠ 0 := by
    intro i hc; exact hz.2 (by simpa using congrArg Complex.im hc)
  have hFL := hzf z hz
  rw [Cvs.Finite.SecularRealRooted.fourierLaplace_eq_S hL (negI_involutive N) (mode_negI N) hge hz0] at hFL
  have hS : Cvs.Finite.UniversalFunctionPairing.S L (mode N) (Cvs.Limit.SpineWithoutSimplicity.ground P R L hL N) z ≠ 0 :=
    fun h => hFL (by rw [h, mul_zero])
  have hw : (z ^ 2).im ≠ 0 := by
    rw [sq, Complex.mul_im]
    have : z.re * z.im + z.im * z.re = 2 * (z.re * z.im) := by ring
    rw [this]
    exact mul_ne_zero two_ne_zero (mul_ne_zero hz.1 hz.2)
  have h0 : z ^ 2 ≠ 0 := fun h => hw (by rw [h, Complex.zero_im])
  have hq : ∀ j, qf L N j - z ^ 2 ≠ 0 := by
    intro j h
    apply hw
    have h' := congrArg Complex.im h
    unfold qf at h'
    rw [Complex.sub_im, ← Complex.ofReal_pow, Complex.ofReal_im, zero_sub, Complex.zero_im, neg_eq_zero] at h'
    exact h'
  rw [← S_mul_eq_secPoly N _ h0 hq]
  exact mul_ne_zero hS (mul_ne_zero (neg_ne_zero.mpr h0) (Finset.prod_ne_zero_iff.mpr fun j _ => hq j))

end Cvs.Finite.ReducedSecularPolynomial
