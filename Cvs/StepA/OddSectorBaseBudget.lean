import Mathlib
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.OffWindowDefect
import Cvs.WeilForm.Archimedean.TruncatedLevyDensityBelow
import Cvs.WeilForm.Archimedean.TruncatedSymbolConstant
import Cvs.WeilForm.ChannelFunctionalL2
import Cvs.WeilForm.OddCapTransfer
import Cvs.WeilForm.OddPoleTermBound
import Cvs.WeilForm.PrimeSideVanishesLogTwo
import Cvs.WeilForm.SimplicityCriterionWindow
import Cvs.WeilForm.TruncatedArchCappedBudget
import Cvs.WeilForm.TruncatedArchChannelSum
import Cvs.WeilForm.TruncatedFormL2Below
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowReflectionSymmetry
import Cvs.WeilForm.WindowRepresentative
import Cvs.Zeta.PrimePowerSideTruncated
import Cvs.Zeta.WeilPositivityStatement

/-!
# The odd sector of the truncated Weil form clears the base-case budget

At `L = log 2`, `P = 2`, `R = 1`, an odd class has its truncated Weil form bounded below by the
constant minus the capped channels minus the pole, and with the `100`-channel budget this clears
`15/1000`, which is the `hoddT` input of step (a).
-/

noncomputable section

open MeasureTheory Set Real Cvs.Zeta.Explicit.Weil

namespace Cvs.StepA.OddSectorBaseBudget

/-- **The truncated form is the truncation functional on the canonical representative.** -/
theorem weilQWTrunc_rep {L : ℝ} (N P R : ℕ) (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) :
    Cvs.WeilForm.SimplicityCriterionWindow.weilQWTrunc N P R φ
      = Cvs.WeilForm.TruncatedFormL2Below.weilFormTrunc N P R (Cvs.WeilForm.WindowRepresentative.rep φ) := by
  unfold Cvs.WeilForm.SimplicityCriterionWindow.weilQWTrunc Cvs.WeilForm.TruncatedFormL2Below.weilQTrunc
  exact Cvs.WeilForm.TruncatedFormL2Below.weilFormTrunc_congr_ae N P R (Cvs.WeilForm.WindowRepresentative.ae_eq_rep φ)

/-- **The self-convolution at zero is the squared norm**, on the representative. -/
theorem selfConvolution_rep_zero {L : ℝ} (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) :
    selfConvolution (Cvs.WeilForm.WindowRepresentative.rep φ) 0 = ‖φ‖ ^ 2 := by
  rw [Cvs.WeilForm.TruncatedArchCappedBudget.selfConvolution_zero_eq, ← Cvs.WeilForm.OddCapTransfer.sq_norm_eq_integral_rep]

/-- **The odd sector, bounded below by the channel budget and the pole.**  Given per-channel caps
on the resolvent functionals, the truncated Weil form at `x = 2` sits above the constant minus the
caps minus the pole coefficient. -/
theorem odd_lower_of_caps (N : ℕ) {o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)}
    (hodd : Cvs.WeilForm.WindowReflectionSymmetry.reflW o = -o) {lam : ℕ → ℝ}
    (hcaps : ∀ k ∈ Finset.range N,
      Cvs.WeilForm.ChannelFunctionalL2.chanInt (Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx k) (Cvs.WeilForm.WindowRepresentative.rep o)
        ≤ lam k * ‖o‖ ^ 2) :
    (Cvs.WeilForm.Archimedean.TruncatedSymbolConstant.truncConst N - (∑ k ∈ Finset.range N, lam k)
        - (Real.exp (Real.log 2 / 2) - Real.exp (-(Real.log 2 / 2)) - Real.log 2)) * ‖o‖ ^ 2
      ≤ Cvs.WeilForm.SimplicityCriterionWindow.weilQWTrunc N 2 1 o := by
  set g := Cvs.WeilForm.WindowRepresentative.rep o with hg
  set W2 := ‖o‖ ^ 2 with hW2
  have hS0 : selfConvolution g 0 = W2 := selfConvolution_rep_zero o
  -- decompose the form
  rw [weilQWTrunc_rep, Cvs.WeilForm.TruncatedFormL2Below.weilFormTrunc]
  -- prime side vanishes
  rw [Cvs.WeilForm.PrimeSideVanishesLogTwo.primeSide_eq_zero o]
  -- arch + Lévy is the channel sum
  rw [Cvs.WeilForm.TruncatedArchChannelSum.archLevy_eq_channelSum o N]
  -- the rank-1 term is 2·A·B, bounded below by the pole
  have hpole : -(Real.exp (Real.log 2 / 2) - Real.exp (-(Real.log 2 / 2)) - Real.log 2) * W2
      ≤ 2 * Cvs.WeilForm.OddPoleTermBound.A o * Cvs.WeilForm.OddPoleTermBound.B o :=
    Cvs.WeilForm.OddPoleTermBound.pole_ge (by positivity) hodd
  have hrank : 2 * (∫ x : ℝ, g x * Real.exp (x / 2)) * (∫ x : ℝ, g x * Real.exp (-(x / 2)))
      = 2 * Cvs.WeilForm.OddPoleTermBound.A o * Cvs.WeilForm.OddPoleTermBound.B o := rfl
  -- the channel sum is capped
  have hsum : ∑ k ∈ Finset.range N,
      Cvs.WeilForm.ChannelFunctionalL2.chanInt (Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx k) g
        ≤ ∑ k ∈ Finset.range N, lam k * W2 := Finset.sum_le_sum hcaps
  have hsum' : (∑ k ∈ Finset.range N, lam k * W2) = (∑ k ∈ Finset.range N, lam k) * W2 := by
    rw [Finset.sum_mul]
  rw [hS0, hrank]
  rw [sub_zero]
  nlinarith [hpole, hsum, hsum'.le, hsum'.ge]

end Cvs.StepA.OddSectorBaseBudget
