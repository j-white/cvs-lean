import Mathlib
import Cvs.WeilForm.Archimedean.ArchEnergySpectral
import Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous
import Cvs.WeilForm.Archimedean.HatLevyDeficit
import Cvs.WeilForm.Archimedean.LevyDensity
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.HatFunctionWindow
import Cvs.WeilForm.InfimumAttainedSphere
import Cvs.WeilForm.SelfConvolutionContinuous
import Cvs.WeilForm.SelfConvolutionWindowEdge
import Cvs.WeilForm.TruncatedArchDomain
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowRepresentative
import Cvs.Zeta.WeilPositivityStatement

/-!
# The hat lies in the form domain, so the Weil form attains its infimum on the sphere

    `hatW L ∈ formDomain`   and   `∃ η, ‖η‖ = 1, weilQW η = inf {weilQW φ | ‖φ‖ = 1}`

for `0 < L`: the hat's Lévy integrand is bounded on `(0, 1]` and dominated by `2g(0)·densityU`
on `(1, ∞)`.
-/

noncomputable section

open MeasureTheory Set Cvs.Zeta.Explicit.Weil

namespace Cvs.WeilForm.HatInFormDomain

/-- **The hat's Lévy integrand is integrable on `(0, ∞)`.** -/
theorem integrableOn_levy_hat {L : ℝ} (hL : 0 < L) :
    IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (Cvs.WeilForm.WindowRepresentative.rep (Cvs.WeilForm.HatFunctionWindow.hatW L)))
      (Ioi 0) (volume : Measure ℝ) := by
  set φ := Cvs.WeilForm.HatFunctionWindow.hatW L with hφ
  have hmeas : AEStronglyMeasurable (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (Cvs.WeilForm.WindowRepresentative.rep φ))
      (volume.restrict (Ioi 0)) :=
    Cvs.WeilForm.TruncatedArchDomain.aestronglyMeasurable_levy
      (Cvs.WeilForm.SelfConvolutionContinuous.continuous_selfConvolution
        (Cvs.WeilForm.WindowRepresentative.memLp_rep φ)).aestronglyMeasurable
  have hnn : ∀ u, 0 < u → 0 ≤ Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (Cvs.WeilForm.WindowRepresentative.rep φ) u := fun u hu =>
    Cvs.WeilForm.Archimedean.ArchEnergySpectral.levy_nonneg (Cvs.WeilForm.WindowRepresentative.integrable_sq_rep φ)
      (Cvs.WeilForm.WindowRepresentative.integrable_cross_rep φ) hu
  -- on `(0, 1]`: bounded by a constant
  have h1 : IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (Cvs.WeilForm.WindowRepresentative.rep φ)) (Ioc 0 1) volume := by
    refine Integrable.mono' (g := fun _ : ℝ => (L + 1) / 4)
      ((continuous_const.integrableOn_Icc (a := (0:ℝ)) (b := 1)).mono_set Ioc_subset_Icc_self) (hmeas.mono_measure (Measure.restrict_mono Ioc_subset_Ioi_self le_rfl)) ?_
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun u hu => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hnn u hu.1)]
    show Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (Cvs.WeilForm.WindowRepresentative.rep φ) u ≤ (L + 1) / 4
    unfold Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy
    rw [Cvs.WeilForm.Archimedean.HatLevyDeficit.selfConvolution_rep_hatW, Cvs.WeilForm.Archimedean.HatLevyDeficit.selfConvolution_rep_hatW]
    have hdef := Cvs.WeilForm.Archimedean.HatLevyDeficit.deficit_hat_le hL.le (show (0:ℝ) ≤ u / 2 by linarith [hu.1])
    have hdens := Cvs.WeilForm.Archimedean.HatLevyDeficit.densityU_le_two_div hu.1 hu.2
    have hdpos := Cvs.WeilForm.Archimedean.LevyDensity.densityU_pos hu.1
    have hdefnn : 0 ≤ selfConvolution (Cvs.WeilForm.HatFunctionWindow.hat L) 0
        - selfConvolution (Cvs.WeilForm.HatFunctionWindow.hat L) (u / 2) := by
      have := hnn u hu.1
      unfold Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy at this
      rw [Cvs.WeilForm.Archimedean.HatLevyDeficit.selfConvolution_rep_hatW,
        Cvs.WeilForm.Archimedean.HatLevyDeficit.selfConvolution_rep_hatW] at this
      exact nonneg_of_mul_nonneg_right this hdpos
    calc Cvs.WeilForm.Archimedean.LevyDensity.densityU u * (selfConvolution (Cvs.WeilForm.HatFunctionWindow.hat L) 0
          - selfConvolution (Cvs.WeilForm.HatFunctionWindow.hat L) (u / 2))
        ≤ (2 / u) * ((u / 2) ^ 2 * (L + u / 2) / 2) :=
          mul_le_mul hdens hdef hdefnn (div_pos two_pos hu.1).le
      _ = u * (L + u / 2) / 4 := by field_simp; ring
      _ ≤ (L + 1) / 4 := by
          have := hu.1; have := hu.2
          nlinarith
  -- on `(1, ∞)`: dominated by `2 g(0) · densityU`
  have h2 : IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (Cvs.WeilForm.WindowRepresentative.rep φ)) (Ioi 1) volume := by
    refine Integrable.mono' ((Cvs.WeilForm.SelfConvolutionWindowEdge.densityU_integrableOn one_pos).const_mul
      (2 * selfConvolution (Cvs.WeilForm.WindowRepresentative.rep φ) 0))
      (hmeas.mono_measure (Measure.restrict_mono (Ioi_subset_Ioi zero_le_one) le_rfl)) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun u hu => ?_)
    have hu0 : (0:ℝ) < u := lt_trans zero_lt_one hu
    rw [Real.norm_eq_abs, abs_of_nonneg (hnn u hu0)]
    show Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (Cvs.WeilForm.WindowRepresentative.rep φ) u
      ≤ 2 * selfConvolution (Cvs.WeilForm.WindowRepresentative.rep φ) 0 * Cvs.WeilForm.Archimedean.LevyDensity.densityU u
    unfold Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (Cvs.WeilForm.Archimedean.HatLevyDeficit.deficit_le_two φ (u / 2))
      (Cvs.WeilForm.Archimedean.LevyDensity.densityU_pos hu0).le
  exact (h1.union h2).mono_set Ioi_subset_Ioc_union_Ioi

/-- **The hat, as an element of the form domain.** -/
def hatD {L : ℝ} (hL : 0 < L) : Cvs.WeilForm.FormDomain.formDomain hL.le :=
  ⟨Cvs.WeilForm.HatFunctionWindow.hatW L, integrableOn_levy_hat hL⟩

theorem hatD_ne_zero {L : ℝ} (hL : 0 < L) : hatD hL ≠ 0 := fun h =>
  Cvs.WeilForm.HatFunctionWindow.hatW_ne_zero hL (congrArg Subtype.val h)

/-- **The form domain has a nonzero class.** -/
theorem exists_ne_zero {L : ℝ} (hL : 0 < L) :
    ∃ φ : Cvs.WeilForm.FormDomain.formDomain hL.le, φ ≠ 0 := ⟨hatD hL, hatD_ne_zero hL⟩

/-- **The Weil form attains its infimum on the unit sphere of the form domain.** -/
theorem exists_min {L : ℝ} (hL : 0 < L) (P R : ℕ) :
    ∃ η ∈ Cvs.WeilForm.InfimumAttainedSphere.sphere hL.le,
      Cvs.WeilForm.InfimumAttainedSphere.Q hL.le P R η
        = sInf (Cvs.WeilForm.InfimumAttainedSphere.Q hL.le P R '' Cvs.WeilForm.InfimumAttainedSphere.sphere hL.le) :=
  Cvs.WeilForm.InfimumAttainedSphere.exists_min hL.le P R (exists_ne_zero hL)

end Cvs.WeilForm.HatInFormDomain
