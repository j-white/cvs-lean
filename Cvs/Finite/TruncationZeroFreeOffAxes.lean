import Mathlib
import Cvs.Finite.DividedDifferenceCommutator
import Cvs.Finite.SecularRootsReal
import Cvs.Finite.ShiftedDiagonalSimplicity
import Cvs.Limit.OffAxesLimit
import Cvs.Upstream.FourierLaplace
import Cvs.WeilForm.SelfConvolutionTransform

/-!
# A divided-difference truncation's transform is zero-free off the axes

The mode sum's transform factors as a prefactor vanishing only at real `z` times the secular
sum `∑ⱼ ξⱼ/(ωⱼ + z)`, so off the axes its zeros are the secular roots, and `an earlier result` forces those
real when the matrix is of `ddMatrix` form.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Matrix Real Cvs.Finite.DividedDifferenceCommutator Cvs.Limit.OffAxesLimit

namespace Cvs.Finite.TruncationZeroFreeOffAxes

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The mode frequency `ω = 2πn/L`. -/
def omega (L : ℝ) (mode : ι → ℤ) : ι → ℝ := fun i => 2 * π * (mode i) / L

/-- The truncation's ground state, as a function on the window. -/
def modeSum (L : ℝ) (mode : ι → ℤ) (xi : ι → ℝ) : ℝ → ℝ :=
  fun y => if y ∈ Set.Ioc (0 : ℝ) L then ∑ i, xi i * Real.cos (omega L mode i * y) else 0

/-- The frequency flips sign under the index involution. -/
theorem omega_neg {L : ℝ} {mode : ι → ℤ} {neg : ι → ι} (hmode : ∀ i, mode (neg i) = -mode i)
    (i : ι) : omega L mode (neg i) = -(omega L mode i) := by
  simp only [omega, hmode i]
  push_cast
  ring

/-- **The cosine sum is the two-sided exponential sum**, the sines cancelling in pairs. -/
theorem modeSum_eq_exp_sum {L : ℝ} {mode : ι → ℤ} {neg : ι → ι}
    (hinv : Function.Involutive neg) (hmode : ∀ i, mode (neg i) = -mode i)
    {xi : ι → ℝ} (hxieven : ∀ i, xi (neg i) = xi i) (t : ℝ) :
    ((∑ i, xi i * Real.cos (omega L mode i * t) : ℝ) : ℂ)
      = ∑ i, (xi i : ℂ) * Complex.exp (Complex.I * ((omega L mode i : ℝ) : ℂ) * (t : ℂ)) := by
  have hsin : ∑ i, Real.sin (omega L mode i * t) * xi i = 0 :=
    Cvs.Finite.DividedDifferenceCommutator.sum_odd_even hinv
      (fun i => by rw [omega_neg hmode i]; simp [neg_mul, Real.sin_neg]) hxieven
  have hexp : ∀ i : ι, Complex.exp (Complex.I * ((omega L mode i : ℝ) : ℂ) * (t : ℂ))
      = (Real.cos (omega L mode i * t) : ℂ) + Complex.I * (Real.sin (omega L mode i * t) : ℂ) := by
    intro i
    have h : Complex.I * ((omega L mode i : ℝ) : ℂ) * (t : ℂ)
        = ((omega L mode i * t : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [h, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]; ring
  simp only [hexp, mul_add, Finset.sum_add_distrib, Complex.ofReal_sum, Complex.ofReal_mul]
  have hzero : ∑ i, (xi i : ℂ) * (Complex.I * (Real.sin (omega L mode i * t) : ℂ)) = 0 := by
    have h2 : ∑ i, (xi i : ℂ) * (Complex.I * (Real.sin (omega L mode i * t) : ℂ))
        = Complex.I * ((∑ i, Real.sin (omega L mode i * t) * xi i : ℝ) : ℂ) := by
      rw [Complex.ofReal_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by push_cast; ring
    rw [h2, hsin]; simp
  rw [hzero, add_zero]

/-- **`exp(I ω L) = 1`** — the frequency times the window is an integer multiple of `2π`. -/
theorem exp_omega_mul {L : ℝ} (hL : L ≠ 0) (mode : ι → ℤ) (i : ι) :
    Complex.exp (Complex.I * ((omega L mode i : ℝ) : ℂ) * (L : ℂ)) = 1 := by
  have h : Complex.I * ((omega L mode i : ℝ) : ℂ) * (L : ℂ)
      = ((mode i : ℤ) : ℂ) * (2 * (π : ℂ) * Complex.I) := by
    simp only [omega]
    have hLC : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL
    push_cast
    field_simp
  rw [h, Complex.exp_int_mul_two_pi_mul_I]

/-- **The transform factors through the secular sum**, with a prefactor that vanishes only
at real `z`. -/
theorem fourierLaplace_modeSum {L : ℝ} (hL : 0 < L) {mode : ι → ℤ} {neg : ι → ι}
    (hinv : Function.Involutive neg) (hmode : ∀ i, mode (neg i) = -mode i)
    {xi : ι → ℝ} (hxieven : ∀ i, xi (neg i) = xi i) (z : ℂ)
    (hz : ∀ i, ((omega L mode i : ℝ) : ℂ) + z ≠ 0) :
    FourierLaplace.fourierLaplace (Cvs.WeilForm.SelfConvolutionTransform.cf (modeSum L mode xi)) z
      = ((Complex.exp (Complex.I * z * (L : ℂ)) - 1) / Complex.I)
        * ∑ i, (xi i : ℂ) / (((omega L mode i : ℝ) : ℂ) + z) := by
  have hInd : ∀ t : ℝ, Cvs.WeilForm.SelfConvolutionTransform.cf (modeSum L mode xi) t
        * Complex.exp (Complex.I * z * (t : ℂ))
      = Set.indicator (Set.Ioc (0 : ℝ) L)
          (fun t : ℝ => (∑ i, (xi i : ℂ)
              * Complex.exp (Complex.I * (((omega L mode i : ℝ) : ℂ) + z) * (t : ℂ))) ) t := by
    intro t
    by_cases ht : t ∈ Set.Ioc (0 : ℝ) L
    · rw [Set.indicator_of_mem ht]
      simp only [Cvs.WeilForm.SelfConvolutionTransform.cf, modeSum, if_pos ht]
      rw [modeSum_eq_exp_sum hinv hmode hxieven t, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_assoc, ← Complex.exp_add]
      ring_nf
    · rw [Set.indicator_of_notMem ht]
      simp only [Cvs.WeilForm.SelfConvolutionTransform.cf, modeSum, if_neg ht]
      simp
  rw [FourierLaplace.fourierLaplace]
  simp only [hInd]
  rw [MeasureTheory.integral_indicator measurableSet_Ioc,
    ← intervalIntegral.integral_of_le hL.le]
  have hint : ∀ i : ι, IntervalIntegrable
      (fun t : ℝ => (xi i : ℂ)
        * Complex.exp (Complex.I * (((omega L mode i : ℝ) : ℂ) + z) * (t : ℂ)))
      MeasureTheory.volume 0 L := fun i =>
    (continuous_const.mul (Complex.continuous_exp.comp
      (continuous_const.mul Complex.continuous_ofReal))).intervalIntegrable 0 L
  rw [intervalIntegral.integral_finsetSum (fun i _ => hint i)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hc : Complex.I * (((omega L mode i : ℝ) : ℂ) + z) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero (hz i)
  rw [intervalIntegral.integral_const_mul, integral_exp_mul_complex hc]
  have hsplit : Complex.exp (Complex.I * (((omega L mode i : ℝ) : ℂ) + z) * (L : ℂ))
      = Complex.exp (Complex.I * z * (L : ℂ)) := by
    rw [show Complex.I * (((omega L mode i : ℝ) : ℂ) + z) * (L : ℂ)
        = Complex.I * ((omega L mode i : ℝ) : ℂ) * (L : ℂ) + Complex.I * z * (L : ℂ) by ring,
      Complex.exp_add, exp_omega_mul (ne_of_gt hL) mode i, one_mul]
  rw [hsplit]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  field_simp

/-- **So the transform is zero-free off the axes**, for a `ddMatrix` whose shifted bottom is a
simple eigenvalue. -/
theorem zeroFree_offAxes {L : ℝ} (hL : 0 < L) {a b pos : ι → ℝ} {mode : ι → ℤ} {neg : ι → ι}
    {lam : ℝ} {xi : ι → ℝ}
    (hposinj : Function.Injective pos) (hinv : Function.Involutive neg)
    (hmode : ∀ i, mode (neg i) = -mode i) (hb : ∀ i, b (neg i) = -b i)
    (hxieven : ∀ i, xi (neg i) = xi i)
    (hpos : ∀ i, pos i = omega L mode i)
    (hQpsd : ∀ v : ι → ℝ, 0 ≤ v ⬝ᵥ (ddMatrix (Cvs.Finite.ShiftedDiagonalSimplicity.shiftDiag a lam) b pos *ᵥ v))
    (hQxi : ddMatrix (Cvs.Finite.ShiftedDiagonalSimplicity.shiftDiag a lam) b pos *ᵥ xi = 0)
    (hnorm : ∑ i, xi i = 1)
    (hkerline : ∀ v : ι → ℝ, ddMatrix a b pos *ᵥ v = lam • v → ∃ c : ℝ, v = c • xi)
    (hne : ∃ j, xi j * pos j ≠ 0) :
    ∀ z ∈ offAxes,
      FourierLaplace.fourierLaplace (Cvs.WeilForm.SelfConvolutionTransform.cf (modeSum L mode xi)) z ≠ 0 := by
  intro z hz hzero
  obtain ⟨hre, him⟩ := hz
  have hne0 : ∀ i, ((omega L mode i : ℝ) : ℂ) + z ≠ 0 := by
    intro i hc
    exact him (by simpa using congrArg Complex.im hc)
  rw [fourierLaplace_modeSum hL hinv hmode hxieven z hne0] at hzero
  have hpre : Complex.exp (Complex.I * z * (L : ℂ)) - 1 ≠ 0 := by
    intro hc
    have h1 : Complex.exp (Complex.I * z * (L : ℂ)) = 1 := sub_eq_zero.mp hc
    have h2 : Real.exp ((Complex.I * z * (L : ℂ)).re) = 1 := by
      rw [← Complex.norm_exp, h1, norm_one]
    have h3 : (Complex.I * z * (L : ℂ)).re = 0 := by
      have he : Real.exp ((Complex.I * z * (L : ℂ)).re) = Real.exp 0 := by
        rw [h2, Real.exp_zero]
      exact Real.exp_injective he
    have h4 : -(z.im * L) = 0 := by
      simpa [Complex.mul_re, Complex.mul_im] using h3
    exact him (by
      have : z.im * L = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · exact h
      · exact absurd h (ne_of_gt hL))
  have hsecular : ∑ i, (xi i : ℂ) / (((omega L mode i : ℝ) : ℂ) + z) = 0 := by
    rcases mul_eq_zero.mp hzero with h | h
    · exact absurd (div_eq_zero_iff.mp h |>.resolve_right Complex.I_ne_zero) hpre
    · exact h
  have hs : ∀ j, ((pos j : ℝ) : ℂ) ≠ -z := by
    intro j hc
    exact him (by simpa using congrArg Complex.im hc)
  have hsum : ∑ j, (xi j : ℂ) / (((pos j : ℝ) : ℂ) - (-z)) = 0 := by
    rw [← hsecular]
    exact Finset.sum_congr rfl fun i _ => by rw [hpos i]; ring_nf
  have hroot := Cvs.Finite.SecularRootsReal.root_im_eq_zero hposinj hinv hb hxieven hQpsd hQxi hnorm
    ((Cvs.Finite.ShiftedDiagonalSimplicity.kerline_shift_iff a b pos lam xi).mpr hkerline) hne hsum
  exact him (by simpa using hroot)

end Cvs.Finite.TruncationZeroFreeOffAxes
