import Mathlib
import Cvs.WeilForm.Archimedean.LevyDensity
import Cvs.WeilForm.Archimedean.LevyIntegrandNonneg
import Cvs.WeilForm.Archimedean.LevyTruncationExhausts
import Cvs.WeilForm.Archimedean.TruncatedArchContinuous
import Cvs.Zeta.WeilPositivityStatement

/-!
# The arch channel is lower semicontinuous along L² convergence

    archFull f − ε ≤ archFull (F n)   eventually

`archFull` is the supremum of the continuous `archTrunc δ`, so it clears any level its
truncations clear.
-/

set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Set Filter Cvs.Zeta.Explicit.Weil

namespace Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous

/-- The Lévy integrand of a test function. -/
def levy (f : ℝ → ℝ) : ℝ → ℝ := fun u =>
  Cvs.WeilForm.Archimedean.LevyDensity.densityU u * (selfConvolution f 0 - selfConvolution f (u / 2))

/-- **Lower semicontinuity of the archimedean channel.** -/
theorem archFull_le_eventually {f : ℝ → ℝ} {F : ℕ → ℝ → ℝ} {C ε : ℝ}
    (hf : MemLp f 2 (volume : Measure ℝ))
    (hfc : AEStronglyMeasurable (selfConvolution f) (volume : Measure ℝ))
    (hint : IntegrableOn (levy f) (Set.Ioi 0) (volume : Measure ℝ))
    (hF : ∀ n, MemLp (F n) 2 (volume : Measure ℝ))
    (hFc : ∀ n, AEStronglyMeasurable (selfConvolution (F n)) (volume : Measure ℝ))
    (hFint : ∀ n, IntegrableOn (levy (F n)) (Set.Ioi 0) (volume : Measure ℝ))
    (hconv : Tendsto (fun n => ∫ x : ℝ, (F n x - f x) ^ 2) atTop (nhds 0))
    (hbdd : ∀ n, (∫ x : ℝ, F n x ^ 2) ≤ C) (hε : 0 < ε) :
    ∀ᶠ n in atTop, Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull f - ε
      ≤ Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull (F n) := by
  -- a cut that recovers all but ε/2 of the integral
  obtain ⟨δ, hδ, hcut⟩ :=
    Cvs.WeilForm.Archimedean.LevyTruncationExhausts.exists_archTrunc_close hint (by linarith : (0:ℝ) < ε / 2)
  set D : ℝ := ∫ u in Set.Ioi δ, Cvs.WeilForm.Archimedean.LevyDensity.densityU u with hD
  have hDnn : 0 ≤ D := by
    rw [hD]
    exact setIntegral_nonneg measurableSet_Ioi fun u hu =>
      (Cvs.WeilForm.Archimedean.LevyDensity.densityU_pos (lt_trans hδ hu)).le
  set E : ℝ := Real.sqrt (∫ x : ℝ, f x ^ 2) with hE
  set B : ℝ := Real.sqrt C + E with hB
  set M : ℝ := 2 * B * D with hM
  -- the cross term goes to zero
  set s : ℕ → ℝ := fun n => Real.sqrt (∫ x : ℝ, (F n x - f x) ^ 2) with hs
  have hstend : Tendsto s atTop (nhds 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp hconv
    simpa [hs, Real.sqrt_zero, Function.comp_def] using this
  have hsnn : ∀ n, 0 ≤ s n := fun n => Real.sqrt_nonneg _
  have hMtend : Tendsto (fun n => s n * M) atTop (nhds 0) := by
    have := hstend.mul_const M
    simpa using this
  have hev : ∀ᶠ n in atTop, s n * M < ε / 2 :=
    hMtend.eventually_lt_const (by linarith : (0:ℝ) < ε / 2)
  filter_upwards [hev] with n hn
  -- the truncated channels are close
  have hb := Cvs.WeilForm.Archimedean.TruncatedArchContinuous.abs_archTrunc_sub_le hδ (hF n) hf (hFc n) hfc
  have hEn : Real.sqrt (∫ x : ℝ, F n x ^ 2) ≤ Real.sqrt C := Real.sqrt_le_sqrt (hbdd n)
  have hfac : 2 * (s n * (Real.sqrt (∫ x : ℝ, F n x ^ 2) + E)) * D ≤ s n * M := by
    have h1 : Real.sqrt (∫ x : ℝ, F n x ^ 2) + E ≤ B := by rw [hB]; linarith
    have h2 : s n * (Real.sqrt (∫ x : ℝ, F n x ^ 2) + E) ≤ s n * B :=
      mul_le_mul_of_nonneg_left h1 (hsnn n)
    rw [hM]
    nlinarith [hsnn n, hDnn]
  have hclose : |Cvs.WeilForm.Archimedean.TruncatedArchContinuous.archTrunc δ (F n)
      - Cvs.WeilForm.Archimedean.TruncatedArchContinuous.archTrunc δ f| ≤ s n * M := le_trans hb hfac
  have hlow : Cvs.WeilForm.Archimedean.TruncatedArchContinuous.archTrunc δ f - s n * M
      ≤ Cvs.WeilForm.Archimedean.TruncatedArchContinuous.archTrunc δ (F n) := by
    have := abs_le.mp hclose
    linarith [this.1]
  -- and the truncation of `F n` is below its full integral
  have hup : Cvs.WeilForm.Archimedean.TruncatedArchContinuous.archTrunc δ (F n)
      ≤ Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull (F n) :=
    Cvs.WeilForm.Archimedean.LevyIntegrandNonneg.archTrunc_le_archFull hδ (hF n) (hFint n)
  linarith

end Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous
