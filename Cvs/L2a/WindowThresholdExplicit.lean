import Mathlib
import Cvs.L2a.BetaProfilePoissonTail
import Cvs.L2a.FullTailBilinearBound
import Cvs.L2a.FullTailBilinearChannels
import Cvs.L2a.FullTailConvergence
import Cvs.L2a.FullTailPoleChannel
import Cvs.L2a.ThresholdExplicit
import Cvs.L2a.WindowChainFromInputs
import Cvs.L2a.WindowFormDeepSpan

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# `c₀^W ≤ e^{34300}`

At `λ_min = ½` and `κ_F = 1/38`, `ε̄² = 304` and `w̄₁ = A₁ + Ā₂√38 ≤ 66.34` give `K_pol(½, 1/38) ≤ 6650`; with
`B₀^F ≤ 1916` (Cvs.L2a.FullSpanThreshold) this is `B₀^W ≤ 8568`, so `e^{1360} ≤ c₀^W ≤ e^{34300}`.
-/

noncomputable section

open Real Cvs.L2a.BetaProfilePoissonTail Cvs.L2a.WindowFormDeepSpan

namespace Cvs.L2a.WindowThresholdExplicit

open Cvs.L2a.WindowChainFromInputs (epsBarL KpolL epsBarL_nonneg)

/-- **`A₁ ≤ 28.79`**: `BetaProfilePoissonTail`'s rational bounds on `Π₊(Ψ)`, `‖T⁺‖`, `C_A`, `C_L1`. -/
theorem A1_le : Cvs.L2a.FullTailBilinearBound.A1 ≤ 2879 / 100 := by
  have hT := normT_le
  have hT0 : 0 ≤ Cvs.L2a.FullTailBilinearChannels.normT := Real.sqrt_nonneg _
  have hL := normLogT_le
  have hCA := CA_le_rat
  have hCL := CL1_le_rat
  have hl2 := Real.log_two_lt_d9
  have hpp := piPlus_Psi_bounds.2
  rw [piPlus_Psi] at hpp
  have hLT : Real.log 2 * Cvs.L2a.FullTailBilinearChannels.normT ≤ 6932 / 10000 * (37 / 100) :=
    mul_le_mul (by linarith) hT hT0 (by norm_num)
  unfold Cvs.L2a.FullTailBilinearBound.A1; norm_num at hLT ⊢; linarith

/-- **`Ā₂ ≤ 6.09`**: `BetaProfilePoissonTail`'s rational bounds with `V₀ ≤ 93/50` and `1/√5 ≤ 0.4473`. -/
theorem A2bar_le : Cvs.L2a.FullTailBilinearBound.A2bar ≤ 609 / 100 := by
  have hT := normT_le
  have hT0 : 0 ≤ Cvs.L2a.FullTailBilinearChannels.normT := Real.sqrt_nonneg _
  have hL := normLogT_le
  have hCA := CA_le_rat
  have hCL := CL1_le_rat
  have hV : Cvs.L2a.FullTailBilinearChannels.V0 ≤ 93 / 50 := V0_le_rat
  have hl2 := Real.log_two_lt_d9
  have h5 : 1 / √5 ≤ 4473 / 10000 := by
    rw [div_le_iff₀ (Real.sqrt_pos.2 (by norm_num))]
    have : (22357 / 10000 : ℝ) ≤ √5 := by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
    nlinarith
  have hLT : Real.log 2 * Cvs.L2a.FullTailBilinearChannels.normT ≤ 6932 / 10000 * (37 / 100) :=
    mul_le_mul (by linarith) hT hT0 (by norm_num)
  have hVl : (1 / 2 + Cvs.L2a.FullTailBilinearChannels.V0) * (2 + Real.log 2 / 2)
      ≤ (1 / 2 + 93 / 50) * (2 + 6932 / 10000 / 2) :=
    mul_le_mul (by linarith) (by linarith) (by linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)])
      (by linarith [Cvs.L2a.FullTailBilinearChannels.V0_nonneg])
  unfold Cvs.L2a.FullTailBilinearBound.A2bar; norm_num at hLT hVl h5 ⊢; linarith

/-- `ε̄(½, 1/38)² = 304`. -/
theorem epsBarL_half_sq : epsBarL (1 / 2) (1 / 38) ^ 2 = 304 := by
  unfold epsBarL
  rw [div_pow, Real.sq_sqrt (by norm_num)]
  norm_num

/-- `ε̄(½, 1/38) ≤ 17.437`. -/
theorem epsBarL_half_le : epsBarL (1 / 2) (1 / 38) ≤ 17437 / 1000 := by
  have h0 := epsBarL_nonneg (1 / 2) (1 / 38)
  nlinarith [epsBarL_half_sq]

/-- `w̄₁(1/38) = A₁ + Ā₂/√(1/38) ≤ 28.79 + 6.09/0.1622`. -/
theorem w1Bar_38_le : w1Bar (1 / 38) ≤ 2879 / 100 + 609 / 100 / (1622 / 10000) := by
  have hs : (1622 / 10000 : ℝ) ≤ √(1 / 38) := by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hA2 := A2bar_le
  have hA20 := A2bar_nonneg
  unfold w1Bar
  have : Cvs.L2a.FullTailBilinearBound.A2bar / √(1 / 38) ≤ 609 / 100 / (1622 / 10000) :=
    div_le_div₀ (by norm_num) hA2 (by norm_num) hs
  linarith [A1_le]

/-- **`K_pol(½, 1/38) ≤ 6650`**: `2w̄₁ε̄ + W̄_Ψε̄²` with `ε̄² = 304` and `W̄_Ψ ≤ 57/4` (Cvs.L2a.ThresholdExplicit). -/
theorem KpolL_half_le : KpolL (1 / 2) (1 / 38) ≤ 6650 := by
  have he := epsBarL_half_le
  have he0 := epsBarL_nonneg (1 / 2) (1 / 38)
  have hw := w1Bar_38_le
  have hw0 := w1Bar_nonneg (1 / 38)
  have hW := Cvs.L2a.ThresholdExplicit.WPsiBar_le_sharp
  unfold KpolL
  rw [epsBarL_half_sq]
  have h1 : w1Bar (1 / 38) * epsBarL (1 / 2) (1 / 38)
      ≤ (2879 / 100 + 609 / 100 / (1622 / 10000)) * (17437 / 1000) := mul_le_mul hw he he0 (by positivity)
  norm_num at h1 ⊢
  nlinarith

end Cvs.L2a.WindowThresholdExplicit
