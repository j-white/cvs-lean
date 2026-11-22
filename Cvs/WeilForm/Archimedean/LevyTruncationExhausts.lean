import Mathlib
import Cvs.WeilForm.Archimedean.LevyDensity
import Cvs.WeilForm.Archimedean.TruncatedArchContinuous
import Cvs.Zeta.WeilPositivityStatement

/-!
# The truncation exhausts the Lévy integral

    ∀ ε > 0, ∃ δ > 0,  archFull f − ε ≤ archTrunc δ f

so `archFull` is the supremum of the continuous functionals `archTrunc δ`, and lower
semicontinuity follows without a limit theorem.
-/

set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Set Filter Cvs.Zeta.Explicit.Weil

namespace Cvs.WeilForm.Archimedean.LevyTruncationExhausts

/-- The Lévy integral as `Cvs.WeilForm.SelfConvolutionFunctional`'s Weil form writes it. -/
def archFull (f : ℝ → ℝ) : ℝ :=
  ∫ u in Set.Ioi (0:ℝ), Cvs.WeilForm.Archimedean.LevyDensity.densityU u
      * (selfConvolution f 0 - selfConvolution f (u / 2))

/-- **The head of the Lévy integral is negligible.** -/
theorem tendsto_head_zero {f : ℝ → ℝ}
    (hint : IntegrableOn (fun u : ℝ => Cvs.WeilForm.Archimedean.LevyDensity.densityU u
      * (selfConvolution f 0 - selfConvolution f (u / 2))) (Set.Ioi 0) (volume : Measure ℝ)) :
    Tendsto (fun n : ℕ => ∫ u in Set.Ioc (0:ℝ) (1 / (n + 1)),
      Cvs.WeilForm.Archimedean.LevyDensity.densityU u
        * (selfConvolution f 0 - selfConvolution f (u / 2))) atTop (nhds 0) := by
  set F : ℝ → ℝ := fun u : ℝ => Cvs.WeilForm.Archimedean.LevyDensity.densityU u
      * (selfConvolution f 0 - selfConvolution f (u / 2)) with hF
  set s : ℕ → Set ℝ := fun n => Set.Ioc (0:ℝ) (1 / (n + 1)) with hs
  have hsm : ∀ n, MeasurableSet (s n) := fun n => measurableSet_Ioc
  have hanti : Antitone s := by
    intro m n hmn u hu
    have h1 : (0:ℝ) < u := hu.1
    have h2 : u ≤ 1 / (n + 1) := hu.2
    have hmono : (1:ℝ) / (n + 1) ≤ 1 / (m + 1) := by
      apply one_div_le_one_div_of_le
      · positivity
      · exact_mod_cast Nat.succ_le_succ hmn
    exact ⟨h1, le_trans h2 hmono⟩
  have hs0 : IntegrableOn F (s 0) (volume : Measure ℝ) :=
    hint.mono_set (fun u hu => hu.1)
  have hempty : (⋂ n, s n) = (∅ : Set ℝ) := by
    refine Set.eq_empty_iff_forall_notMem.mpr fun u hu => ?_
    simp only [Set.mem_iInter, hs, Set.mem_Ioc] at hu
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (hu 0).1
    exact absurd (hu n).2 (not_le.mpr hn)
  have := hanti.tendsto_setIntegral hsm hs0
  rwa [hempty, MeasureTheory.setIntegral_empty] at this

/-- **The truncation exhausts the integral.** -/
theorem exists_archTrunc_close {f : ℝ → ℝ}
    (hint : IntegrableOn (fun u : ℝ => Cvs.WeilForm.Archimedean.LevyDensity.densityU u
      * (selfConvolution f 0 - selfConvolution f (u / 2))) (Set.Ioi 0) (volume : Measure ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ archFull f - ε ≤ Cvs.WeilForm.Archimedean.TruncatedArchContinuous.archTrunc δ f := by
  set F : ℝ → ℝ := fun u : ℝ => Cvs.WeilForm.Archimedean.LevyDensity.densityU u
      * (selfConvolution f 0 - selfConvolution f (u / 2)) with hF
  have htend := tendsto_head_zero hint
  have hev := (Metric.tendsto_atTop.mp htend) ε hε
  obtain ⟨N, hN⟩ := hev
  have hNspec := hN N le_rfl
  refine ⟨1 / (N + 1), by positivity, ?_⟩
  -- split `Ioi 0` at the cut
  have hpos : (0:ℝ) < 1 / ((N:ℝ) + 1) := by positivity
  have hδ : (0:ℝ) ≤ 1 / (N + 1) := hpos.le
  have hsplit : archFull f
      = (∫ u in Set.Ioc (0:ℝ) (1 / (N + 1)), F u)
        + Cvs.WeilForm.Archimedean.TruncatedArchContinuous.archTrunc (1 / (N + 1)) f := by
    rw [archFull, Cvs.WeilForm.Archimedean.TruncatedArchContinuous.archTrunc, ← hF,
      ← MeasureTheory.setIntegral_union (Set.Ioc_disjoint_Ioi (le_refl (1 / ((N:ℝ) + 1)))) measurableSet_Ioi
        (hint.mono_set (fun u hu => hu.1)) (hint.mono_set (fun u hu => lt_trans hpos hu)),
      Set.Ioc_union_Ioi_eq_Ioi hδ]
  rw [hsplit]
  have habs : |∫ u in Set.Ioc (0:ℝ) (1 / (N + 1)), F u| < ε := by
    rwa [Real.dist_eq, sub_zero] at hNspec
  have hle : ∫ u in Set.Ioc (0:ℝ) (1 / (N + 1)), F u ≤ ε := le_of_lt (lt_of_abs_lt habs)
  linarith

end Cvs.WeilForm.Archimedean.LevyTruncationExhausts
