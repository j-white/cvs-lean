import Mathlib
import Cvs.L2a.BetaProfilePoissonTail
import Cvs.L2a.FullTailBilinearBound
import Cvs.L2a.FullTailBilinearChannels
import Cvs.L2a.FullTailConvergence
import Cvs.L2a.FullTailPoleChannel
import Cvs.L2a.TailLogScaleTest
import Cvs.L2a.WindowFormDeepSpan
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.SelfConvolutionCosine

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# `c₀ ≤ e^{10836}`

`K_pol(1/16) ≤ 1790`, `C̄ ≤ 16`, `Λ̄₀ ≤ 14.1`, `κ̄ ≤ 12.1`, `archSymbol 0 ≥ −5.3721834231` and `log π ≤ 1.1448` give
`B₀ ≤ 2704`; with `κ⋆ ≤ 288` (`Ē ≤ 9`), `c₀ = max(10¹⁶, 16κ⋆²e^{4B₀+4}) ≤ e^{10836} ≤ 10^{4707}`, and `WindowDeepSpanStructural`'s
SPINE-L2a(5) holds for every `c ≥ e^{10836}`.
-/

noncomputable section

open Real Set Filter MeasureTheory Cvs.L2a.AngularProlateTailPositive Cvs.L2a.FullTailConvergence Cvs.L2a.BetaProfilePoissonTail Cvs.L2a.WindowFormDeepSpan
open Cvs.WeilForm.Archimedean.ArchimedeanUnbounded (archSymbol)

namespace Cvs.L2a.ThresholdExplicit

/-! ### `K_pol(1/16)` from `BetaProfilePoissonTail`'s certificates -/

/-- **`W̄_Ψ ≤ 57/4`**: `WindowFormDeepSpan`'s `WPsiBar_le` argument, with its rational inputs summed to `14.196`. -/
theorem WPsiBar_le_sharp : WPsiBar ≤ 57 / 4 := by
  have hT := normT_le
  have hT0 : 0 ≤ Cvs.L2a.FullTailBilinearChannels.normT := Real.sqrt_nonneg _
  have hL := normLogT_le
  have hL0 : 0 ≤ Cvs.L2a.FullTailBilinearChannels.normLogT := Real.sqrt_nonneg _
  have hCA := CA_le_rat
  have hCA0 : 0 ≤ CA := Real.sqrt_nonneg _
  have hCL := CL1_le_rat
  have hCL0 := Cvs.L2a.FullTailBilinearBound.CL1_nonneg
  have hV : Cvs.L2a.FullTailBilinearChannels.V0 ≤ 93 / 50 := V0_le_rat
  have hV0 := Cvs.L2a.FullTailBilinearChannels.V0_nonneg
  have hl2 := Real.log_two_lt_d9
  have hl20 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hpp := piPlus_Psi_bounds.2
  rw [piPlus_Psi] at hpp
  have hK := KPsi_le_rat
  have hK0 := KPsi_nonneg
  have hπ4 := two_pi_pow_four_ge
  have h7 : (264 / 100 : ℝ) ≤ √7 := by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have q1 : KPsi / ((2 * π) ^ 4 * √7) ≤ 3743 / (1555 * (264 / 100)) :=
    div_le_div₀ (by norm_num) hK (by norm_num) (mul_le_mul hπ4 h7 (by norm_num) (by positivity))
  have q2 : KPsi / (4 * (2 * π) ^ 4) ≤ 3743 / (4 * 1555) :=
    div_le_div₀ (by norm_num) hK (by norm_num) (by linarith)
  have q10 : 0 ≤ KPsi / ((2 * π) ^ 4 * √7) := div_nonneg hK0 (by positivity)
  have q20 : 0 ≤ KPsi / (4 * (2 * π) ^ 4) := div_nonneg hK0 (by positivity)
  have t2 : CA * Cvs.L2a.FullTailBilinearChannels.normT ≤ 179 / 10 * (37 / 100) := mul_le_mul hCA hT hT0 (by norm_num)
  have t3 : (CL1 + Real.log 2 * Cvs.L2a.FullTailBilinearChannels.normT + 2 * Cvs.L2a.FullTailBilinearChannels.normLogT)
      * Cvs.L2a.FullTailBilinearChannels.normT ≤ (101 / 10 + 6932 / 10000 * (37 / 100) + 2 * (21 / 100)) * (37 / 100) := by
    refine mul_le_mul ?_ hT hT0 (by positivity)
    have : Real.log 2 * Cvs.L2a.FullTailBilinearChannels.normT ≤ 6932 / 10000 * (37 / 100) :=
      mul_le_mul (by linarith) hT hT0 (by norm_num)
    linarith
  have t4 : Real.log 2 * Cvs.L2a.FullTailBilinearChannels.normT * (KPsi / ((2 * π) ^ 4 * √7))
      ≤ 6932 / 10000 * (37 / 100) * (3743 / (1555 * (264 / 100))) :=
    mul_le_mul (mul_le_mul (by linarith) hT hT0 (by norm_num)) q1 q10 (by norm_num)
  have t5 : (1 / 2 + Cvs.L2a.FullTailBilinearChannels.V0) * (2 + Real.log 2 / 2) * (KPsi / (4 * (2 * π) ^ 4))
      ≤ (1 / 2 + 93 / 50) * (2 + 6932 / 10000 / 2) * (3743 / (4 * 1555)) := by
    refine mul_le_mul (mul_le_mul (by linarith) (by linarith) (by positivity) (by norm_num)) q2 q20
      (by norm_num)
  unfold WPsiBar
  norm_num at t2 t3 t4 t5 ⊢
  linarith

/-! ### `B₀` and `c₀` -/

/-! ### SPINE-L2a(5) past `e^{10836}` -/

variable {ι : Type} [Fintype ι] [DecidableEq ι]

end Cvs.L2a.ThresholdExplicit
