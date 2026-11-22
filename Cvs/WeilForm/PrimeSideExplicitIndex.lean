import Mathlib
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.LevyDensity
import Cvs.WeilForm.AutocorrSelfConvolution
import Cvs.WeilForm.PrimeIndexSetsAgree
import Cvs.WeilForm.PrimePowerIndexed
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.WeilForm.WindowTruncatesPrimes
import Cvs.Zeta.PrimePowerSideTruncated
import Cvs.Zeta.WeilPositivityStatement

/-!
# The window form's prime side, in the explicit formula's index

    primePowerSideTruncated P R (selfConvolution (indicator (Ioc 0 L) f))
      = ∑_{n < ⌈exp L⌉₊} Λ n · n^{−1/2} · (g (log n) + g (−log n))

for `exp L ≤ P` and `L ≤ R·log 2`, by `Cvs.WeilForm.PrimePowerIndexed`'s reindexing and `Cvs.WeilForm.PrimeIndexSetsAgree`'s index agreement.
-/

set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Set Real Cvs.Zeta.Explicit.Weil

namespace Cvs.WeilForm.PrimeSideExplicitIndex

open Cvs.WeilForm.WindowTruncatesPrimes

/-- **The prime side, cut where the explicit formula cuts it.** -/
theorem primeSide_eq_range {L : ℝ} (hL : 0 ≤ L) {P R : ℕ}
    (hP : Real.exp L ≤ P) (hR : L ≤ R * Real.log 2) (f : ℝ → ℝ) :
    primePowerSideTruncated P R (selfConvolution (Set.indicator (Set.Ioc 0 L) f))
      = ∑ n ∈ Finset.range ⌈Real.exp L⌉₊,
          (ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(1/2) : ℝ))
            * (selfConvolution (Set.indicator (Set.Ioc 0 L) f) (Real.log n)
              + selfConvolution (Set.indicator (Set.Ioc 0 L) f) (-(Real.log n))) := by
  classical
  rw [Cvs.WeilForm.PrimePowerIndexed.primePowerSideTruncated_eq_image]
  have hfilter : (∑ k ∈ Cvs.WeilForm.PrimePowerIndexed.primePowIndex P R,
        (ArithmeticFunction.vonMangoldt k * (k : ℝ) ^ (-(1/2) : ℝ))
          * (selfConvolution (Set.indicator (Set.Ioc 0 L) f) (Real.log k)
            + selfConvolution (Set.indicator (Set.Ioc 0 L) f) (-(Real.log k))))
      = ∑ k ∈ windowIndex P R L,
          (ArithmeticFunction.vonMangoldt k * (k : ℝ) ^ (-(1/2) : ℝ))
            * (selfConvolution (Set.indicator (Set.Ioc 0 L) f) (Real.log k)
              + selfConvolution (Set.indicator (Set.Ioc 0 L) f) (-(Real.log k))) := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro k hk hkf
    have hgt : L < Real.log k := by
      by_contra hc
      exact hkf (Finset.mem_filter.mpr ⟨hk, not_lt.mp hc⟩)
    have habs : |Real.log k| = Real.log k := abs_of_nonneg (le_trans hL hgt.le)
    have h1 : selfConvolution (Set.indicator (Set.Ioc 0 L) f) (Real.log k) = 0 :=
      Cvs.WeilForm.AutocorrSelfConvolution.selfConvolution_indicator_eq_zero L f (by rw [habs]; exact hgt.le)
    have h2 : selfConvolution (Set.indicator (Set.Ioc 0 L) f) (-(Real.log k)) = 0 :=
      Cvs.WeilForm.AutocorrSelfConvolution.selfConvolution_indicator_eq_zero L f
        (by rw [abs_neg, habs]; exact hgt.le)
    rw [h1, h2]
    ring
  rw [hfilter, Cvs.WeilForm.PrimeIndexSetsAgree.sum_windowIndex_eq_range hL hP hR f]

/-- **The form, with its prime side in the explicit formula's index.**  Pole, archimedean
bracket, and a sum over `n < ⌈exp L⌉₊`. -/
theorem weilForm_eq_range {L : ℝ} (hL : 0 ≤ L) {P R : ℕ}
    (hP : Real.exp L ≤ P) (hR : L ≤ R * Real.log 2) (f : ℝ → ℝ) :
    Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (Set.indicator (Set.Ioc 0 L) f)
      = 2 * (∫ x : ℝ, Set.indicator (Set.Ioc 0 L) f x * Real.exp (x / 2))
          * (∫ x : ℝ, Set.indicator (Set.Ioc 0 L) f x * Real.exp (-(x / 2)))
        + (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0
              * selfConvolution (Set.indicator (Set.Ioc 0 L) f) 0
            + ∫ u in Ioi (0:ℝ), Cvs.WeilForm.Archimedean.LevyDensity.densityU u
                * (selfConvolution (Set.indicator (Set.Ioc 0 L) f) 0
                  - selfConvolution (Set.indicator (Set.Ioc 0 L) f) (u / 2)))
        - ∑ n ∈ Finset.range ⌈Real.exp L⌉₊,
            (ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(1/2) : ℝ))
              * (selfConvolution (Set.indicator (Set.Ioc 0 L) f) (Real.log n)
                + selfConvolution (Set.indicator (Set.Ioc 0 L) f) (-(Real.log n))) := by
  rw [Cvs.WeilForm.SelfConvolutionFunctional.weilForm_eq, primeSide_eq_range hL hP hR f]

end Cvs.WeilForm.PrimeSideExplicitIndex
