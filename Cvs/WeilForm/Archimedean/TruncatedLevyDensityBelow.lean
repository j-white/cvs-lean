import Mathlib
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.LevyDensity
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.WeilForm.SelfConvolutionMaximum
import Cvs.Zeta.PrimePowerSideTruncated
import Cvs.Zeta.WeilPositivityStatement

/-!
# Truncating the Lévy density bounds the archimedean channel below

    ∑_{k<N} e^{−(¼+k)u} ≤ densityU u,   so the truncated energy never exceeds the true one

Each dropped term is a nonnegative multiple of a nonnegative shift deficit, so a positivity
statement proved for a truncation transfers to the full archimedean channel.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Real MeasureTheory Set Cvs.Zeta.Explicit.Weil

namespace Cvs.WeilForm.Archimedean.TruncatedLevyDensityBelow

/-- The Lévy density truncated to its first `N` exponential terms. -/
def densityTrunc (N : ℕ) (u : ℝ) : ℝ :=
  ∑ k ∈ Finset.range N, Real.exp (-((1 / 4 + (k : ℝ)) * u))

theorem densityTrunc_nonneg (N : ℕ) (u : ℝ) : 0 ≤ densityTrunc N u :=
  Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le

/-- **The truncation never exceeds the density.**  `Cvs.WeilForm.Archimedean.LevyDensity` sums the same nonnegative family. -/
theorem densityTrunc_le (N : ℕ) {u : ℝ} (hu : 0 < u) :
    densityTrunc N u ≤ Cvs.WeilForm.Archimedean.LevyDensity.densityU u := by
  have hs := Cvs.WeilForm.Archimedean.LevyDensity.hasSum_exp u hu
  have hsum : Summable fun k : ℕ => Real.exp (-((1 / 4 + (k : ℝ)) * u)) := hs.summable
  have hnn : ∀ k : ℕ, 0 ≤ Real.exp (-((1 / 4 + (k : ℝ)) * u)) := fun _ => (Real.exp_pos _).le
  have := hsum.sum_le_tsum (Finset.range N) (fun k _ => hnn k)
  rwa [hs.tsum_eq] at this

/-- **The truncated Lévy energy is a lower bound for the true one.** -/
theorem levy_trunc_le (N : ℕ) {f : ℝ → ℝ}
    (hsq : Integrable fun s => (f s) ^ 2)
    (hcross : ∀ u : ℝ, Integrable fun s => f s * f (s + u))
    (hint₁ : IntegrableOn (fun u => densityTrunc N u
      * (selfConvolution f 0 - selfConvolution f (u / 2))) (Ioi 0))
    (hint₂ : IntegrableOn (fun u => Cvs.WeilForm.Archimedean.LevyDensity.densityU u
      * (selfConvolution f 0 - selfConvolution f (u / 2))) (Ioi 0)) :
    (∫ u in Ioi (0:ℝ), densityTrunc N u
        * (selfConvolution f 0 - selfConvolution f (u / 2)))
      ≤ ∫ u in Ioi (0:ℝ), Cvs.WeilForm.Archimedean.LevyDensity.densityU u
        * (selfConvolution f 0 - selfConvolution f (u / 2)) := by
  refine setIntegral_mono_on hint₁ hint₂ measurableSet_Ioi fun u hu => ?_
  have hu' : 0 < u := hu
  have hdef : 0 ≤ selfConvolution f 0 - selfConvolution f (u / 2) := by
    have := Cvs.WeilForm.SelfConvolutionMaximum.selfConvolution_le (u / 2) hsq (hcross (u / 2))
    linarith
  exact mul_le_mul_of_nonneg_right (densityTrunc_le N hu') hdef

/-- **The window form, bounded below with `N` Lévy terms retained.**  Keeping a finite part of
the density instead of discarding all of it. -/
theorem weilForm_ge_trunc (N P R : ℕ) {f : ℝ → ℝ}
    (hsq : Integrable fun s => (f s) ^ 2)
    (hcross : ∀ u : ℝ, Integrable fun s => f s * f (s + u))
    (hint₁ : IntegrableOn (fun u => densityTrunc N u
      * (selfConvolution f 0 - selfConvolution f (u / 2))) (Ioi 0))
    (hint₂ : IntegrableOn (fun u => Cvs.WeilForm.Archimedean.LevyDensity.densityU u
      * (selfConvolution f 0 - selfConvolution f (u / 2))) (Ioi 0)) :
    2 * (∫ x : ℝ, f x * Real.exp (x / 2)) * (∫ x : ℝ, f x * Real.exp (-(x / 2)))
        + (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 * selfConvolution f 0
          + ∫ u in Ioi (0:ℝ), densityTrunc N u
              * (selfConvolution f 0 - selfConvolution f (u / 2)))
        - primePowerSideTruncated P R (selfConvolution f)
      ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R f := by
  rw [Cvs.WeilForm.SelfConvolutionFunctional.weilForm_eq]
  linarith [levy_trunc_le N hsq hcross hint₁ hint₂]

end Cvs.WeilForm.Archimedean.TruncatedLevyDensityBelow
