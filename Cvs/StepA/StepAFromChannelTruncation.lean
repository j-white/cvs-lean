import Mathlib
import Cvs.StepA.StepAFromTwoGaps
import Cvs.StepA.StepAPredicate
import Cvs.WeilForm.Archimedean.ArchEnergySpectral
import Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous
import Cvs.WeilForm.Archimedean.LevyDensity
import Cvs.WeilForm.Archimedean.TruncatedLevyDensityBelow
import Cvs.WeilForm.BottomAttained
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.InfimumAttainedSphere
import Cvs.WeilForm.SelfConvolutionContinuous
import Cvs.WeilForm.SimplicityCriterionWindow
import Cvs.WeilForm.TruncatedFormL2Below
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowReflectionSymmetry
import Cvs.WeilForm.WindowRepresentative
import Cvs.Zeta.WeilPositivityStatement

/-!
# Step (a) from the channel truncation and a trial function

    `weilQWTrunc N P R ≤ weilQW P R` on the form domain, so the two gaps of step (a) may be
    stated for the channel truncation, against a bottom bounded above by a trial function.
-/

noncomputable section

open MeasureTheory Set Cvs.Zeta.Explicit.Weil

namespace Cvs.StepA.StepAFromChannelTruncation

/-- **The truncated Lévy integrand is integrable on the domain**, dominated by the full one. -/
theorem integrableOn_trunc {L : ℝ} (hL : 0 ≤ L) (N : ℕ) (φ : Cvs.WeilForm.FormDomain.formDomain hL) :
    IntegrableOn (fun u => Cvs.WeilForm.Archimedean.TruncatedLevyDensityBelow.densityTrunc N u *
      (selfConvolution (Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)) 0
        - selfConvolution (Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)) (u / 2)))
      (Ioi 0) (volume : Measure ℝ) := by
  have hdom := Cvs.WeilForm.FormDomain.hdom_of_mem φ
  have hcont : Continuous fun u => Cvs.WeilForm.Archimedean.TruncatedLevyDensityBelow.densityTrunc N u *
      (selfConvolution (Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)) 0
        - selfConvolution (Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)) (u / 2)) := by
    have h1 : Continuous (Cvs.WeilForm.Archimedean.TruncatedLevyDensityBelow.densityTrunc N) := by
      unfold Cvs.WeilForm.Archimedean.TruncatedLevyDensityBelow.densityTrunc
      exact continuous_finsetSum _ fun k _ => by fun_prop
    have h2 := Cvs.WeilForm.SelfConvolutionContinuous.continuous_selfConvolution
      (Cvs.WeilForm.WindowRepresentative.memLp_rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L))
    exact h1.mul (continuous_const.sub (h2.comp (continuous_id.div_const 2)))
  refine Integrable.mono' hdom hcont.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun u hu => ?_)
  have hlevy := Cvs.WeilForm.Archimedean.ArchEnergySpectral.levy_nonneg (Cvs.WeilForm.WindowRepresentative.integrable_sq_rep
    (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)) (Cvs.WeilForm.WindowRepresentative.integrable_cross_rep _) hu
  have hdpos := Cvs.WeilForm.Archimedean.LevyDensity.densityU_pos hu
  have hd : 0 ≤ selfConvolution (Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)) 0
      - selfConvolution (Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)) (u / 2) := by
    unfold Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy at hlevy
    exact (mul_nonneg_iff_of_pos_left hdpos).mp hlevy
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Cvs.WeilForm.Archimedean.TruncatedLevyDensityBelow.densityTrunc_nonneg N u) hd)]
  show Cvs.WeilForm.Archimedean.TruncatedLevyDensityBelow.densityTrunc N u * _ ≤ Cvs.WeilForm.Archimedean.LevyDensity.densityU u * _
  exact mul_le_mul_of_nonneg_right (Cvs.WeilForm.Archimedean.TruncatedLevyDensityBelow.densityTrunc_le N hu) hd

/-- **The channel truncation lies beneath the form**, on the domain. -/
theorem weilQWTrunc_le {L : ℝ} (hL : 0 ≤ L) (N P R : ℕ) (φ : Cvs.WeilForm.FormDomain.formDomain hL) :
    Cvs.WeilForm.SimplicityCriterionWindow.weilQWTrunc N P R (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)
      ≤ Cvs.WeilForm.WindowRepresentative.weilQW P R (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) :=
  Cvs.WeilForm.TruncatedFormL2Below.weilQTrunc_le N P R (Cvs.WeilForm.WindowRepresentative.ae_eq_rep _)
    (Cvs.WeilForm.WindowRepresentative.integrable_sq_rep _) (Cvs.WeilForm.WindowRepresentative.integrable_cross_rep _)
    (integrableOn_trunc hL N φ) (Cvs.WeilForm.FormDomain.hdom_of_mem φ)

/-- **Step (a) from the two gaps of the channel truncation.** -/
theorem stepA_of_trunc_gaps {L : ℝ} (hL : 0 < L) (P R N : ℕ)
    (hodd : ∀ o : Cvs.WeilForm.FormDomain.formDomain hL.le,
      Cvs.WeilForm.WindowReflectionSymmetry.reflD hL.le o = -o → o ≠ 0 →
      Cvs.WeilForm.BottomAttained.lam hL P R * ‖o‖ ^ 2 < Cvs.WeilForm.InfimumAttainedSphere.Q hL.le P R o)
    {mu2 : ℝ} (hgap : Cvs.WeilForm.BottomAttained.lam hL P R < mu2)
    (hplane : ∀ V : Submodule ℝ (Cvs.WeilForm.FormDomain.formDomain hL.le),
      Module.finrank ℝ V = 2 → V ≤ Cvs.StepA.StepAFromTwoGaps.evenSub hL.le →
      ∃ v ∈ V, v ≠ 0 ∧ mu2 * ‖v‖ ^ 2 ≤ Cvs.WeilForm.SimplicityCriterionWindow.weilQWTrunc N P R
        (v : Cvs.WeilForm.WeilFormOnWindowL2.window L)) :
    ∃ η : Cvs.WeilForm.FormDomain.formDomain hL.le,
      Cvs.StepA.StepAPredicate.StepA
        (fun v : Cvs.WeilForm.FormDomain.formDomain hL.le =>
          Cvs.WeilForm.WindowRepresentative.weilQW P R (v : Cvs.WeilForm.WeilFormOnWindowL2.window L))
        (Cvs.WeilForm.WindowReflectionSymmetry.reflD hL.le) (Cvs.WeilForm.BottomAttained.lam hL P R) η :=
  Cvs.StepA.StepAFromTwoGaps.stepA_of_gaps hL P R hodd
    ⟨fun v => Cvs.WeilForm.SimplicityCriterionWindow.weilQWTrunc N P R (v : Cvs.WeilForm.WeilFormOnWindowL2.window L), mu2, hgap,
      fun v _ => weilQWTrunc_le hL.le N P R v, hplane⟩

/-- **Step (a) from a trial function and the truncation's two gaps.**  The trial bounds the bottom
from above by `β`; the odd sector and the even planes are compared against `β`. -/
theorem stepA_of_trial {L : ℝ} (hL : 0 < L) (P R N : ℕ)
    {w : Cvs.WeilForm.FormDomain.formDomain hL.le} (hw : w ≠ 0) {β : ℝ}
    (hβ : Cvs.WeilForm.InfimumAttainedSphere.Q hL.le P R w ≤ β * ‖w‖ ^ 2)
    (hoddT : ∀ o : Cvs.WeilForm.FormDomain.formDomain hL.le,
      Cvs.WeilForm.WindowReflectionSymmetry.reflD hL.le o = -o → o ≠ 0 →
      β * ‖o‖ ^ 2 < Cvs.WeilForm.SimplicityCriterionWindow.weilQWTrunc N P R (o : Cvs.WeilForm.WeilFormOnWindowL2.window L))
    {mu2 : ℝ} (hgap : β < mu2)
    (hplane : ∀ V : Submodule ℝ (Cvs.WeilForm.FormDomain.formDomain hL.le),
      Module.finrank ℝ V = 2 → V ≤ Cvs.StepA.StepAFromTwoGaps.evenSub hL.le →
      ∃ v ∈ V, v ≠ 0 ∧ mu2 * ‖v‖ ^ 2 ≤ Cvs.WeilForm.SimplicityCriterionWindow.weilQWTrunc N P R
        (v : Cvs.WeilForm.WeilFormOnWindowL2.window L)) :
    ∃ η : Cvs.WeilForm.FormDomain.formDomain hL.le,
      Cvs.StepA.StepAPredicate.StepA
        (fun v : Cvs.WeilForm.FormDomain.formDomain hL.le =>
          Cvs.WeilForm.WindowRepresentative.weilQW P R (v : Cvs.WeilForm.WeilFormOnWindowL2.window L))
        (Cvs.WeilForm.WindowReflectionSymmetry.reflD hL.le) (Cvs.WeilForm.BottomAttained.lam hL P R) η := by
  -- the trial bounds the bottom
  have hlam : Cvs.WeilForm.BottomAttained.lam hL P R ≤ β := by
    have h1 := Cvs.WeilForm.BottomAttained.bottom hL P R w
    have hn : ‖w‖ ≠ 0 := by simpa using hw
    have hpos : 0 < ‖w‖ ^ 2 := by positivity
    have : Cvs.WeilForm.BottomAttained.lam hL P R * ‖w‖ ^ 2 ≤ β * ‖w‖ ^ 2 := h1.trans hβ
    exact le_of_mul_le_mul_right this hpos
  refine stepA_of_trunc_gaps hL P R N ?_ (lt_of_le_of_lt hlam hgap) hplane
  intro o ho ho0
  calc Cvs.WeilForm.BottomAttained.lam hL P R * ‖o‖ ^ 2 ≤ β * ‖o‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hlam (sq_nonneg _)
    _ < Cvs.WeilForm.SimplicityCriterionWindow.weilQWTrunc N P R (o : Cvs.WeilForm.WeilFormOnWindowL2.window L) := hoddT o ho ho0
    _ ≤ Cvs.WeilForm.InfimumAttainedSphere.Q hL.le P R o := weilQWTrunc_le hL.le N P R o

end Cvs.StepA.StepAFromChannelTruncation
