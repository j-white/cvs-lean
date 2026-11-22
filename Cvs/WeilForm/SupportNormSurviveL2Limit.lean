import Mathlib
import Cvs.Upstream.CauchySchwarzLine
import Cvs.WeilForm.EvennessSurvivesL2Limit

/-!
# The support and the norm survive an L² limit

    F n supported in `(0, L]`,  F n → g in L²   ⟹   g is supported there almost everywhere
    ‖F n‖ = 1                                    ⟹   ‖g‖ = 1

the two closed conditions of the constraint set.
-/

set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Real Filter Set

namespace Cvs.WeilForm.SupportNormSurviveL2Limit

/-- **The support is closed under `L²` limits.** -/
theorem support_of_tendsto {L : ℝ} {F : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    (hFs : ∀ n, ∀ s ∉ Set.Ioc (0:ℝ) L, F n s = 0)
    (hF : ∀ n, MemLp (F n) 2 (volume : Measure ℝ)) (hg : MemLp g 2 (volume : Measure ℝ))
    (h : Tendsto (fun n => ∫ x : ℝ, (F n x - g x) ^ 2) atTop (nhds 0)) :
    (∫ x in (Set.Ioc (0:ℝ) L)ᶜ, g x ^ 2) = 0 := by
  have hnn : 0 ≤ ∫ x in (Set.Ioc (0:ℝ) L)ᶜ, g x ^ 2 :=
    setIntegral_nonneg (measurableSet_Ioc.compl) fun x _ => sq_nonneg _
  refine le_antisymm ?_ hnn
  refine ge_of_tendsto h ?_
  filter_upwards with n
  have hle : (∫ x in (Set.Ioc (0:ℝ) L)ᶜ, g x ^ 2)
      ≤ ∫ x in (Set.Ioc (0:ℝ) L)ᶜ, (F n x - g x) ^ 2 := by
    refine setIntegral_mono_on ?_ ?_ measurableSet_Ioc.compl fun x hx => ?_
    · exact ((hg.integrable_sq).integrableOn)
    · exact (((hF n).sub hg).integrable_sq).integrableOn
    · rw [hFs n x hx]
      simp
  refine le_trans hle ?_
  refine setIntegral_le_integral (((hF n).sub hg).integrable_sq) ?_
  exact Filter.Eventually.of_forall fun x => sq_nonneg _

/-- **The norm is closed under `L²` limits.** -/
theorem norm_of_tendsto {F : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    (hF : ∀ n, MemLp (F n) 2 (volume : Measure ℝ)) (hg : MemLp g 2 (volume : Measure ℝ))
    (hnorm : ∀ n, (∫ x : ℝ, F n x ^ 2) = 1)
    (h : Tendsto (fun n => ∫ x : ℝ, (F n x - g x) ^ 2) atTop (nhds 0)) :
    (∫ x : ℝ, g x ^ 2) = 1 := by
  -- the classes converge, and the norm is continuous
  have hlim := Cvs.WeilForm.EvennessSurvivesL2Limit.tendsto_toLp hF hg h
  have hnormlim : Tendsto (fun n => ‖(hF n).toLp (F n)‖) atTop (nhds ‖hg.toLp g‖) :=
    (continuous_norm.tendsto _).comp hlim
  have hone : ∀ n, ‖(hF n).toLp (F n)‖ = 1 := by
    intro n
    have h2 : ‖(hF n).toLp (F n)‖ ^ 2 = 1 := by
      rw [Cvs.Upstream.CauchySchwarzLine.norm_toLp_sq_real (hF n)]; exact hnorm n
    nlinarith [norm_nonneg ((hF n).toLp (F n)), h2]
  have hone' : Tendsto (fun n => ‖(hF n).toLp (F n)‖) atTop (nhds 1) := by
    simp only [hone]
    exact tendsto_const_nhds
  have : ‖hg.toLp g‖ = 1 := tendsto_nhds_unique hnormlim hone'
  have hsq : ‖hg.toLp g‖ ^ 2 = ∫ x : ℝ, g x ^ 2 :=
    Cvs.Upstream.CauchySchwarzLine.norm_toLp_sq_real hg
  rw [this] at hsq
  simpa using hsq.symm

end Cvs.WeilForm.SupportNormSurviveL2Limit
