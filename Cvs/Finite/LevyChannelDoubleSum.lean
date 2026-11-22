import Mathlib
import Cvs.Finite.CosineModeOverlap
import Cvs.Finite.KernelLipschitzOrigin
import Cvs.Finite.LevyKernelIncrement
import Cvs.Finite.TruncationZeroFreeOffAxes
import Cvs.WeilForm.Archimedean.LevyDensity
import Cvs.Zeta.WeilPositivityStatement

/-!
# The Lévy channel of the Weil form on a mode sum is a double sum over the cut kernel

`∫₀^∞ densityU(u)(g(0) − g(u/2)) du = (L/2) ∑ᵢ∑ⱼ xiᵢ xiⱼ ∫₀^∞ densityU(u)(K(0) − Kc(u/2)) du` for
`g` the self-convolution of the mode sum, by the closed forms of `Cvs.Finite.CosineModeOverlap`/`Cvs.Finite.KernelLipschitzOrigin` and the termwise
integrability of `Cvs.Finite.LevyKernelIncrement`.
-/

noncomputable section

open Real MeasureTheory Set Cvs.Zeta.Explicit.Weil

namespace Cvs.Finite.LevyChannelDoubleSum

/-- The self-convolution of a mode sum on the whole half-line, through the cut kernel. -/
theorem selfConvolution_modeSum_Kc {ι : Type*} [Fintype ι] [DecidableEq ι] {L : ℝ} (hL : 0 < L)
    (mode : ι → ℤ) {neg : ι → ι} (hinv : Function.Involutive neg)
    (hmode : ∀ i, mode (neg i) = -mode i) {xi : ι → ℝ} (hxieven : ∀ i, xi (neg i) = xi i)
    {v : ℝ} (hv0 : 0 ≤ v) :
    selfConvolution (Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L mode xi) v
      = L / 2 * ∑ i, ∑ j, xi i * xi j * Cvs.Finite.LevyKernelIncrement.Kc L (mode i) (mode j) v := by
  by_cases hv : v ≤ L
  · rw [Cvs.Finite.CosineModeOverlap.selfConvolution_modeSum hL mode hinv hmode hxieven hv0 hv]
    simp only [Cvs.Finite.LevyKernelIncrement.Kc_of_le hv]
  · rw [Cvs.Finite.KernelLipschitzOrigin.selfConvolution_modeSum_eq_zero mode xi (not_le.mp hv).le]
    simp only [Cvs.Finite.LevyKernelIncrement.Kc_of_gt (not_le.mp hv), mul_zero, Finset.sum_const_zero]

/-- The Lévy integrand for a single pair, named. -/
def levyPair (L : ℝ) (m n : ℤ) : ℝ :=
  ∫ u in Ioi (0:ℝ), Cvs.WeilForm.Archimedean.LevyDensity.densityU u
    * (Cvs.Finite.CosineModeOverlap.K L m n 0 - Cvs.Finite.LevyKernelIncrement.Kc L m n (u / 2))

/-- **The Lévy channel of any function whose self-convolution is the kernel double sum.** -/
theorem levy_of_rep {ι : Type*} [Fintype ι] {L : ℝ} (hL : 0 < L) (mode : ι → ℤ) (c : ι → ℝ)
    {f : ℝ → ℝ} (hg : ∀ v, 0 ≤ v → selfConvolution f v
      = L / 2 * ∑ i, ∑ j, c i * c j * Cvs.Finite.LevyKernelIncrement.Kc L (mode i) (mode j) v) :
    (∫ u in Ioi (0:ℝ), Cvs.WeilForm.Archimedean.LevyDensity.densityU u
        * (selfConvolution f 0 - selfConvolution f (u / 2)))
      = L / 2 * ∑ i, ∑ j, c i * c j * levyPair L (mode i) (mode j) := by
  have hpt : ∀ u ∈ Ioi (0:ℝ), Cvs.WeilForm.Archimedean.LevyDensity.densityU u
        * (selfConvolution f 0 - selfConvolution f (u / 2))
      = ∑ i, ∑ j, L / 2 * (c i * c j) * (Cvs.WeilForm.Archimedean.LevyDensity.densityU u
          * (Cvs.Finite.CosineModeOverlap.K L (mode i) (mode j) 0
            - Cvs.Finite.LevyKernelIncrement.Kc L (mode i) (mode j) (u / 2))) := by
    intro u hu
    have hu0 : (0:ℝ) < u := hu
    rw [hg 0 (le_refl 0), hg (u / 2) (by linarith)]
    simp only [Cvs.Finite.LevyKernelIncrement.Kc_of_le hL.le, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpt]
  have hint : ∀ i j : ι, IntegrableOn (fun u => L / 2 * (c i * c j)
      * (Cvs.WeilForm.Archimedean.LevyDensity.densityU u * (Cvs.Finite.CosineModeOverlap.K L (mode i) (mode j) 0
        - Cvs.Finite.LevyKernelIncrement.Kc L (mode i) (mode j) (u / 2)))) (Ioi 0) volume :=
    fun i j => (Cvs.Finite.LevyKernelIncrement.integrableOn_densityU_mul_K_sub hL _ _).const_mul _
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => hint i j]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, levyPair]
  ring

end Cvs.Finite.LevyChannelDoubleSum
