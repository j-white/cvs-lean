import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.BetaProfilePoissonTail
import Cvs.L2a.CutKernelRemainder
import Cvs.L2a.FarFarConstantClosedForm
import Cvs.L2a.FrameFloorIntegerM
import Cvs.L2a.FullTailBilinearBound
import Cvs.L2a.FullTailBilinearChannels
import Cvs.L2a.FullTailConvergence
import Cvs.L2a.FullTailDeepSpan
import Cvs.L2a.FullTailDeepSpanClosed
import Cvs.L2a.FullTailFloorLimit
import Cvs.L2a.FullTailPolarisation
import Cvs.L2a.FullTailPoleChannel
import Cvs.L2a.FullTailWeilFormLimit
import Cvs.L2a.KappaUniformInX
import Cvs.L2a.LocalResidualBound
import Cvs.L2a.LocalisedConstants
import Cvs.L2a.LowConstantUniform
import Cvs.L2a.MiddlePartQStep
import Cvs.L2a.PerLevelFarLeak
import Cvs.L2a.PolarParameterBessel
import Cvs.L2a.PositionTruncatedTail
import Cvs.L2a.RampCutSumsUniform
import Cvs.L2a.SecondModeShells
import Cvs.L2a.SpanPlungeBound
import Cvs.L2a.TailLogScaleTest
import Cvs.L2a.WindowFormTailLimit
import Cvs.Prolate.AngularBesselInequality
import Cvs.Prolate.EdgeCentreSign
import Cvs.Prolate.Mellin.FarPartLevelBound
import Cvs.Prolate.RegularSolutionEdge
import Cvs.Prolate.SlepianEvenOrdering
import Cvs.StepA.DirichletCosineTrial
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.SymbolIncrementQuadratic
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.Xi.EImageWindowPoisson

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# SPINE-L2a(5): the window form on the deep span

`QW(k_G) = W_∞(Φ) − 2εW_∞(Φ, Ψ) + ε²W_∞(Ψ)` (Cvs.L2a.WindowFormTailLimit), with `b̄N ≤ W_∞(Φ)` (Cvs.L2a.FullTailDeepSpanClosed), E2 (Cvs.L2a.FullTailBilinearBound), E3 (Cvs.L2a.PolarParameterBessel) and
`|W_∞(Ψ)| ≤ W̄_Ψ ≤ 15`, gives `QW(k_G) ≥ b′N`, `b′ = b̄ − K_pol(κ_F)`; the floor, `AngularBesselInequality`'s masses, ORD (Cvs.Prolate.SlepianEvenOrdering) and
`EImageWindowPoisson`'s window norm turn this into `QW(k_G) ≥ c₂(1 − Λ)‖k_G‖²`. For `c ≥ c₀ = max(10¹⁶, 16κ⋆²e^{4B₀+4})`, `b′ ≥ 1`.
-/

noncomputable section

open Real Set Filter MeasureTheory Cvs.L2a.AngularProlateTailPositive Cvs.L2a.FullTailConvergence Cvs.L2a.BetaProfilePoissonTail
open Cvs.WeilForm.Archimedean.ArchimedeanUnbounded (archSymbol)

namespace Cvs.L2a.WindowFormDeepSpan

/-! ### The polar constants -/

/-- `ε̄(κ) = 2/√(κ(993/1000)²)`, E3's bound on the polar parameter under the floor `κ`. -/
def epsBar (κ : ℝ) : ℝ := 2 / √(κ * (993 / 1000) ^ 2)

/-- `w̄₁(κ) = A₁ + Ā₂/√κ`, E2's bound on `w₁` under the floor `κ`. -/
def w1Bar (κ : ℝ) : ℝ := Cvs.L2a.FullTailBilinearBound.A1 + Cvs.L2a.FullTailBilinearBound.A2bar / √κ

/-- `W̄_Ψ = 2(59/630)Π₊(Ψ) + C_A‖T⁺‖ + (C_L1 + log 2‖T⁺‖ + 2‖log θ T⁺‖)‖T⁺‖ + log 2‖T⁺‖K_Ψ/((2π)⁴√7)
+ (½ + V₀)(2 + ½log 2)K_Ψ/(4(2π)⁴)`, with `Π₊(Ψ) = 49/48 − ½log 2π`. -/
def WPsiBar : ℝ :=
  2 * (59 / 630) * (49 / 48 - Real.log (2 * π) / 2) + CA * Cvs.L2a.FullTailBilinearChannels.normT
    + (CL1 + Real.log 2 * Cvs.L2a.FullTailBilinearChannels.normT + 2 * Cvs.L2a.FullTailBilinearChannels.normLogT)
      * Cvs.L2a.FullTailBilinearChannels.normT
    + Real.log 2 * Cvs.L2a.FullTailBilinearChannels.normT * (KPsi / ((2 * π) ^ 4 * √7))
    + (1 / 2 + Cvs.L2a.FullTailBilinearChannels.V0) * (2 + Real.log 2 / 2) * (KPsi / (4 * (2 * π) ^ 4))

/-- The polar correction `K_pol(κ) = 2w̄₁(κ)ε̄(κ) + W̄_Ψ ε̄(κ)²`. -/
def Kpol (κ : ℝ) : ℝ := 2 * w1Bar κ * epsBar κ + WPsiBar * epsBar κ ^ 2

/-! ### `|W_∞(Ψ)| ≤ W̄_Ψ` -/

/-- `|Ψ(ξ)|² ≤ (K_Ψ/(2π)⁴)²/ξ⁸` for `ξ > 0`. -/
theorem Psi_sq_le {ξ : ℝ} (hξ : 0 < ξ) : Psi ξ ^ 2 ≤ (KPsi / (2 * π) ^ 4) ^ 2 * (1 / ξ ^ 8) := by
  have h := abs_Psi_le hξ.ne'
  have h0 : 0 ≤ KPsi / (2 * π * ξ) ^ 4 := div_nonneg KPsi_nonneg (by positivity)
  calc Psi ξ ^ 2 = |Psi ξ| ^ 2 := (sq_abs _).symm
    _ ≤ (KPsi / (2 * π * ξ) ^ 4) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
    _ = (KPsi / (2 * π) ^ 4) ^ 2 * (1 / ξ ^ 8) := by field_simp

/-- `Ψ² ∈ L¹(1, ∞)`. -/
theorem integrableOn_Psi_sq : IntegrableOn (fun ξ => Psi ξ ^ 2) (Ioi 1) := by
  refine Integrable.mono' ((integrableOn_inv_pow (n := 8) (by norm_num)).const_mul
    ((KPsi / (2 * π) ^ 4) ^ 2)) (Cvs.L2a.FullTailBilinearChannels.continuous_Psi.pow 2).aestronglyMeasurable ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi fun ξ hξ => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact Psi_sq_le (lt_trans one_pos hξ)

/-- `‖Ψ‖_{L²(1,∞)} ≤ K_Ψ/((2π)⁴√7)`. -/
theorem sqrt_integral_Psi_sq_le : √(∫ ξ in Ioi 1, Psi ξ ^ 2) ≤ KPsi / ((2 * π) ^ 4 * √7) := by
  have hK : 0 ≤ KPsi / (2 * π) ^ 4 := div_nonneg KPsi_nonneg (by positivity)
  have hI : ∫ ξ in Ioi 1, Psi ξ ^ 2 ≤ (KPsi / (2 * π) ^ 4) ^ 2 * (1 / 7) := by
    calc ∫ ξ in Ioi 1, Psi ξ ^ 2 ≤ ∫ ξ in Ioi (1 : ℝ), (KPsi / (2 * π) ^ 4) ^ 2 * (1 / ξ ^ 8) :=
          setIntegral_mono_on integrableOn_Psi_sq
            ((integrableOn_inv_pow (n := 8) (by norm_num)).const_mul _) measurableSet_Ioi
            fun ξ hξ => Psi_sq_le (lt_trans one_pos hξ)
      _ = (KPsi / (2 * π) ^ 4) ^ 2 * (1 / 7) := by
          rw [integral_const_mul, integral_inv_pow (n := 8) (by norm_num)]; norm_num
  have h7 : (0 : ℝ) < √7 := Real.sqrt_pos.2 (by norm_num)
  have e : (KPsi / (2 * π) ^ 4) ^ 2 * (1 / 7) = (KPsi / ((2 * π) ^ 4 * √7)) ^ 2 := by
    have h7' : √7 ^ 2 = 7 := Real.sq_sqrt (by norm_num)
    rw [show (KPsi / ((2 * π) ^ 4 * √7)) ^ 2 = KPsi ^ 2 / (((2 * π) ^ 4) ^ 2 * √7 ^ 2) by
      rw [div_pow, mul_pow], h7']; ring
  rw [e] at hI
  exact (Real.sqrt_le_sqrt hI).trans (le_of_eq (Real.sqrt_sq (div_nonneg KPsi_nonneg (by positivity))))

/-- **TI for `Ψ`**: `|∫_y^Y Ψ| ≤ (K_Ψ/(4(2π)⁴))/y` for `2 ≤ y ≤ Y`. -/
theorem abs_integral_Psi_le {y Y : ℝ} (hy : 2 ≤ y) (hyY : y ≤ Y) :
    |∫ ξ in y..Y, Psi ξ| ≤ KPsi / (4 * (2 * π) ^ 4) / y := by
  have hy0 : 0 < y := by linarith
  set C := KPsi / (2 * π) ^ 4 with hC
  have hC0 : 0 ≤ C := div_nonneg KPsi_nonneg (by positivity)
  have hpt : ∀ ξ ∈ Icc y Y, |Psi ξ| ≤ C / y ^ 2 * (1 / ξ ^ 2) := by
    intro ξ hξ
    have hξ0 : 0 < ξ := lt_of_lt_of_le hy0 hξ.1
    have h := abs_Psi_le hξ0.ne'
    have e : KPsi / (2 * π * ξ) ^ 4 = C * (1 / ξ ^ 2 * (1 / ξ ^ 2)) := by rw [hC]; field_simp
    rw [e] at h
    have hyξ : 1 / ξ ^ 2 ≤ 1 / y ^ 2 :=
      one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hy0.le hξ.1 2)
    refine h.trans ((mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hyξ (by positivity)) hC0).trans
      (le_of_eq (by ring)))
  have hcont : ContinuousOn (fun ξ : ℝ => C / y ^ 2 * (1 / ξ ^ 2)) (uIcc y Y) := by
    refine continuousOn_const.mul (continuousOn_const.div (continuousOn_pow 2) fun ξ hξ => ?_)
    rw [uIcc_of_le hyY] at hξ
    exact pow_ne_zero 2 (lt_of_lt_of_le hy0 hξ.1).ne'
  calc |∫ ξ in y..Y, Psi ξ| ≤ ∫ ξ in y..Y, |Psi ξ| := intervalIntegral.abs_integral_le_integral_abs hyY
    _ ≤ ∫ ξ in y..Y, C / y ^ 2 * (1 / ξ ^ 2) :=
        intervalIntegral.integral_mono_on hyY
          (Cvs.L2a.FullTailBilinearChannels.continuous_Psi.abs.intervalIntegrable _ _) (hcont.intervalIntegrable) hpt
    _ = C / y ^ 2 * (1 / y - 1 / Y) := by
        rw [intervalIntegral.integral_const_mul, integral_inv_sq_interval hy0 hyY]
    _ ≤ C / y ^ 2 * (1 / y) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have : 0 ≤ 1 / Y := by have : 0 < Y := by linarith
                               positivity
        linarith
    _ ≤ KPsi / (4 * (2 * π) ^ 4) / y := by
        have e : KPsi / (4 * (2 * π) ^ 4) / y = C / (4 * y) := by rw [hC]; field_simp
        rw [e, div_mul_div_comm, mul_one, ← pow_succ]
        have h4 : (4 : ℝ) ≤ y ^ 2 := by nlinarith
        have h3 : 4 * y ≤ y ^ (2 + 1) := by rw [pow_succ]; nlinarith
        exact div_le_div_of_nonneg_left hC0 (by positivity) h3

/-- **`|W_∞(Ψ)| ≤ W̄_Ψ`**: the pole channel is `2Π₊(Ψ)Π₋(Ψ)` exactly, the arch and prime channels are `FullTailBilinearChannels`'s at
`Φ = Ψ`, with `‖Ψ‖_{L²(1,∞)} ≤ K_Ψ/((2π)⁴√7)` and TI constant `K_Ψ/(4(2π)⁴)`. -/
theorem abs_Winf_Psi_le : |Cvs.L2a.FullTailWeilFormLimit.Winf Psi| ≤ WPsiBar := by
  rw [← Cvs.L2a.FullTailPolarisation.WinfBil_self]
  have hpole : Cvs.L2a.FullTailPolarisation.poleBil Psi Psi
      = 2 * (59 / 630) * (49 / 48 - Real.log (2 * π) / 2) := by
    unfold Cvs.L2a.FullTailPolarisation.poleBil; rw [piMinus_Psi, piPlus_Psi]; ring
  have hpole0 : 0 ≤ 2 * (59 / 630) * (49 / 48 - Real.log (2 * π) / 2) := by
    have := piPlus_Psi_bounds.1; rw [piPlus_Psi] at this; linarith
  have harch : |Cvs.L2a.FullTailPolarisation.archBil Psi Psi| ≤ CA * Cvs.L2a.FullTailBilinearChannels.normT :=
    Cvs.L2a.FullTailBilinearChannels.abs_archBil_Psi_le hasDerivAt_beta_on hasDerivAt_beta1_on continuousOn_beta2 le_rfl
  have hK0 : 0 ≤ KPsi / (4 * (2 * π) ^ 4) := div_nonneg KPsi_nonneg (by positivity)
  have hprime : |Cvs.L2a.FullTailPolarisation.primeBil Psi Psi|
      ≤ (CL1 + Real.log 2 * Cvs.L2a.FullTailBilinearChannels.normT + 2 * Cvs.L2a.FullTailBilinearChannels.normLogT)
          * Cvs.L2a.FullTailBilinearChannels.normT
        + Real.log 2 * Cvs.L2a.FullTailBilinearChannels.normT * √(∫ ξ in Ioi 1, Psi ξ ^ 2)
        + (1 / 2 + Cvs.L2a.FullTailBilinearChannels.V0) * (2 + Real.log 2 / 2) * (KPsi / (4 * (2 * π) ^ 4)) :=
    Cvs.L2a.FullTailBilinearChannels.abs_primeBil_Psi_le hasDerivAt_beta_on hasDerivAt_beta1_on continuousOn_beta2
      (by positivity) integrableOn_Psi_sq fun y Y hy hyY => abs_integral_Psi_le hy hyY
  have hL : 0 ≤ Real.log 2 * Cvs.L2a.FullTailBilinearChannels.normT :=
    mul_nonneg (Real.log_nonneg (by norm_num)) (Real.sqrt_nonneg _)
  have hs := mul_le_mul_of_nonneg_left sqrt_integral_Psi_sq_le hL
  unfold Cvs.L2a.FullTailPolarisation.WinfBil WPsiBar
  rw [hpole]
  have h1 := abs_le.1 harch
  have h2 := abs_le.1 hprime
  rw [abs_le]
  constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]

theorem WPsiBar_nonneg : 0 ≤ WPsiBar := (abs_nonneg _).trans abs_Winf_Psi_le

/-! ### Rational bounds -/

theorem normT_le : Cvs.L2a.FullTailBilinearChannels.normT ≤ 37 / 100 := by
  unfold Cvs.L2a.FullTailBilinearChannels.normT
  rw [Real.sqrt_le_left (by norm_num)]; linarith [integral_fullTail_Psi_sq_le_rat]

theorem normLogT_le : Cvs.L2a.FullTailBilinearChannels.normLogT ≤ 21 / 100 := by
  unfold Cvs.L2a.FullTailBilinearChannels.normLogT
  rw [Real.sqrt_le_left (by norm_num)]; linarith [integral_log_fullTail_Psi_sq_le_rat]

theorem KPsi_le_rat : KPsi ≤ 3743 := by
  have h := KPsi_le
  have : √8847360 ≤ 2975 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  linarith

theorem two_pi_pow_four_ge : (1555 : ℝ) ≤ (2 * π) ^ 4 := by
  have h : (628 / 100 : ℝ) ≤ 2 * π := by linarith [Real.pi_gt_d2]
  calc (1555 : ℝ) ≤ (628 / 100) ^ 4 := by norm_num
    _ ≤ (2 * π) ^ 4 := pow_le_pow_left₀ (by norm_num) h 4

theorem A2bar_nonneg : 0 ≤ Cvs.L2a.FullTailBilinearBound.A2bar :=
  (Cvs.L2a.FullTailBilinearBound.A2_nonneg (J := 0) (by norm_num : (0 : ℝ) < 80)).trans
    (Cvs.L2a.FullTailBilinearBound.A2_le_A2bar le_rfl (by norm_num))

theorem epsBar_nonneg (κ : ℝ) : 0 ≤ epsBar κ := div_nonneg (by norm_num) (Real.sqrt_nonneg _)

theorem w1Bar_nonneg (κ : ℝ) : 0 ≤ w1Bar κ :=
  add_nonneg Cvs.L2a.FullTailBilinearBound.A1_nonneg (div_nonneg A2bar_nonneg (Real.sqrt_nonneg _))

theorem epsBar_anti {κ κ' : ℝ} (hκ : 0 < κ) (h : κ ≤ κ') : epsBar κ' ≤ epsBar κ :=
  div_le_div_of_nonneg_left (by norm_num) (Real.sqrt_pos.2 (by positivity))
    (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right h (by norm_num)))

theorem w1Bar_anti {κ κ' : ℝ} (hκ : 0 < κ) (h : κ ≤ κ') : w1Bar κ' ≤ w1Bar κ :=
  add_le_add le_rfl (div_le_div_of_nonneg_left A2bar_nonneg (Real.sqrt_pos.2 hκ) (Real.sqrt_le_sqrt h))

/-- `K_pol` decreases in the floor. -/
theorem Kpol_anti {κ κ' : ℝ} (hκ : 0 < κ) (h : κ ≤ κ') : Kpol κ' ≤ Kpol κ := by
  have he := epsBar_anti hκ h
  have hw := w1Bar_anti hκ h
  have he0 := epsBar_nonneg κ'
  have hw0 := w1Bar_nonneg κ'
  unfold Kpol
  have h1 : w1Bar κ' * epsBar κ' ≤ w1Bar κ * epsBar κ := mul_le_mul hw he he0 (w1Bar_nonneg κ)
  have h2 : epsBar κ' ^ 2 ≤ epsBar κ ^ 2 := pow_le_pow_left₀ he0 he 2
  nlinarith [WPsiBar_nonneg]

/-! ### JA's floor is at least `1/16` -/

/-- `κ_F` on the deep span: `kappaF 10¹⁶ c J (7/100)`. -/
def kapF (c J : ℝ) : ℝ := Cvs.L2a.FrameFloorIntegerM.kappaF (10 ^ 16) c J (7 / 100)

/-- **`A ≥ 7/100`** for `c ≥ 10¹⁶`, `J ≤ c/4 + 1`: the quantitative form of `FrameFloorIntegerM`'s `aJA_pos`. -/
theorem aJA_ge {c J : ℝ} (hc : 10 ^ 16 ≤ c) (hJ0 : 0 ≤ J) (hJ : J ≤ c / 4 + 1) :
    7 / 100 ≤ Cvs.L2a.FrameFloorIntegerM.aJA (10 ^ 16) c J (7 / 100) := by
  have hJc : J ≤ c := by linarith
  have h1 := Cvs.L2a.SpanPlungeBound.epsTauFlat_five_le
  have h2 := Cvs.L2a.LocalisedConstants.eta_le_c0 hc
  have h3 := Cvs.L2a.LocalisedConstants.rOne_le_c0 hc
  have h4 := Cvs.L2a.LocalisedConstants.rStrip_le_c0 hc
  have h5 := Cvs.L2a.LocalisedConstants.Rbar_le
  have h6 := Cvs.L2a.FrameFloorIntegerM.gammaD_le hc hJ0 hJc
  have h7 := Cvs.L2a.FrameFloorIntegerM.gammaE1_le hc hJc
  unfold Cvs.L2a.FrameFloorIntegerM.aJA
  norm_num at h2 h3 h6 h7 ⊢
  linarith

/-- **`κ_F ≥ 1/16`** for `c ≥ 10¹⁶`, `J ≤ c/4 + 1`: `A ≥ 7/100 ≥ 1/16 + ε/2` with `ε ≤ 7/1000`. -/
theorem kapF_ge {c J : ℝ} (hc : 10 ^ 16 ≤ c) (hJ0 : 0 ≤ J) (hJ : J ≤ c / 4 + 1) : 1 / 16 ≤ kapF c J := by
  have hA := aJA_ge hc hJ0 hJ
  have hε := Cvs.L2a.SpanPlungeBound.epsTauFlat_five_le
  have hε0 := Cvs.L2a.SpanPlungeBound.epsTauFlat_nonneg 5
  unfold kapF Cvs.L2a.FrameFloorIntegerM.kappaF
  set A := Cvs.L2a.FrameFloorIntegerM.aJA (10 ^ 16) c J (7 / 100)
  set ε := Cvs.L2a.SpanPlungeBound.epsTauFlat 5
  have hs : 1 / 4 + ε ≤ √(A + ε ^ 2) := Real.le_sqrt_of_sq_le (by nlinarith)
  have h4 : 1 / 4 ≤ √(A + ε ^ 2) - ε := by linarith
  nlinarith

/-! ### The polar algebra -/

/-- **The polar lower bound**: `b̄N ≤ W`, `|x| ≤ e√N`, `|B| ≤ w√N`, `|W_Ψ| ≤ W̄` give
`(b̄ − (2we + W̄e²))N ≤ W − 2xB + x²W_Ψ`. -/
theorem polar_lower {W B WΨ x bb e w WB N : ℝ} (hN : 0 ≤ N) (hW : bb * N ≤ W) (hx : |x| ≤ e * √N)
    (hB : |B| ≤ w * √N) (hΨ : |WΨ| ≤ WB) (he : 0 ≤ e) :
    (bb - (2 * w * e + WB * e ^ 2)) * N ≤ W - 2 * x * B + x ^ 2 * WΨ := by
  have hsN : √N * √N = N := Real.mul_self_sqrt hN
  have hxB : x * B ≤ e * w * N := by
    calc x * B ≤ |x * B| := le_abs_self _
      _ = |x| * |B| := abs_mul _ _
      _ ≤ (e * √N) * (w * √N) := mul_le_mul hx hB (abs_nonneg _) (by positivity)
      _ = e * w * (√N * √N) := by ring
      _ = e * w * N := by rw [hsN]
  have hx2 : x ^ 2 ≤ e ^ 2 * N := by
    calc x ^ 2 = |x| ^ 2 := (sq_abs x).symm
      _ ≤ (e * √N) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hx 2
      _ = e ^ 2 * N := by rw [mul_pow, Real.sq_sqrt hN]
  have hWB0 : 0 ≤ WB := (abs_nonneg _).trans hΨ
  have h1 : -(x ^ 2 * WB) ≤ x ^ 2 * WΨ := by
    have := (abs_le.1 hΨ).1
    nlinarith [sq_nonneg x]
  have h2 : x ^ 2 * WB ≤ e ^ 2 * N * WB := mul_le_mul_of_nonneg_right hx2 hWB0
  nlinarith

/-! ### SPINE-L2a(5) under the margin `b′ ≥ 0` -/

/-- `b′ = b̄ − K_pol(κ_F)`, `κ_F = kapF c J`. -/
def bPrime (c κ J : ℝ) : ℝ := Cvs.L2a.FullTailDeepSpan.bBar c κ J (kapF c J) - Kpol (kapF c J)

/-- `H_x = harmonic ⌊1/a⌋`, `a = 2π/c`: `EImageWindowPoisson`'s window-norm constant `‖k_G‖² ≤ (H_x/2)‖G‖²`. -/
def Hx (c : ℝ) : ℝ := ((harmonic ⌊1 / (2 * π / c)⌋₊ : ℚ) : ℝ)

/-- **`c₂ = 2πb′κ_F/(cH_x(1 + 2c/(πλ₀)))`**. -/
def c2 (c κ J lam0 : ℝ) : ℝ := 2 * π * bPrime c κ J * kapF c J / (c * Hx c * (1 + 2 * c / (π * lam0)))

theorem Hx_pos {c : ℝ} (hc : 2 * π ≤ c) : 0 < Hx c := by
  unfold Hx
  have h1 : (1 : ℝ) ≤ 1 / (2 * π / c) := by
    rw [one_div_div, le_div_iff₀ (by positivity)]; linarith
  exact Rat.cast_pos.2 (harmonic_pos (Nat.floor_pos.2 h1).ne')

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **SPINE-L2a(5) under the margin**: on the deep span (even normalised angular solutions at distinct even-index
levels, `c ≥ 10¹⁶`, `σ² ≥ 5c`, `J ≤ c/4 + 1`, ground `i₀`), for a pole-free `G = Σ bᵢhᵢ` with E1's prime limit,
`b′ ≥ 0` and `λᵢ ≤ Λ` off `i₀`: `c₂(1 − Λ)‖k_G‖² ≤ QW(k_G)`. -/
theorem L2a_window_margin (i₀ : ι) {h h₁ h₂ : ι → ℝ → ℝ} {c κ Λ : ℝ} {χ μ : ι → ℝ} (b : ι → ℝ) {P R : ℕ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (h i) (h₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (h₁ i) (h₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (h₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * h₂ i s - 2 * s * h₁ i s - c ^ 2 * s ^ 2 * h i s + χ i * h i s = 0)
    (hc : 10 ^ 16 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hσ : ∀ i, 5 * c ≤ c ^ 2 - χ i) (hχi : Function.Injective χ)
    (heven : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, h i (-s) = h i s) (hnorm : ∀ i, ∫ s in (-1 : ℝ)..1, h i s ^ 2 = 1)
    (hμ : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, psi c (h i) s = μ i * h i s)
    (hground : (Cvs.Prolate.EdgeCentreSign.evenSpec (Cvs.Prolate.RegularSolutionEdge.sqC c) ∩ Iio (χ i₀)).ncard = 0)
    (hidx : ∀ i, Even (Cvs.Prolate.EdgeCentreSign.evenSpec (Cvs.Prolate.RegularSolutionEdge.sqC c) ∩ Iio (χ i)).ncard)
    (hJ : (Fintype.card ι : ℝ) ≤ c / 4 + 1) (hκ1 : 1 ≤ κ) (hT : 2 ≤ Cvs.L2a.FullTailDeepSpan.TL c κ)
    (hΛ : ∀ i, i ≠ i₀ → (μ i * √(c / (2 * π))) ^ 2 ≤ Λ)
    (hpole : ∑ i, b i * ∫ s in (-1 : ℝ)..1, h i s = 0)
    (hP : 1 / (2 * π / c) ≤ P) (hR : Real.log (1 / (2 * π / c)) ≤ R * Real.log 2)
    (hE1 : Cvs.L2a.WindowFormTailLimit.PrimeTailLimit c
      (Cvs.L2a.WindowFormTailLimit.regProfile c fun s => ∑ i, b i * h i s))
    (hb : 0 ≤ bPrime c κ (Fintype.card ι)) :
    c2 c κ (Fintype.card ι) ((μ i₀ * √(c / (2 * π))) ^ 2) * (1 - Λ)
        * ∫ θ, Cvs.Xi.EImageWindowPoisson.window (2 * π / c) (fun s => ∑ i, b i * h i s) θ ^ 2
      ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (Cvs.L2a.TailLogScaleTest.logScale
          (Cvs.Xi.EImageWindowPoisson.window (2 * π / c) fun s => ∑ i, b i * h i s)) := by
  set J : ℝ := (Fintype.card ι : ℝ) with hJd
  set κF := kapF c J with hκFd
  set G : ℝ → ℝ := fun s => ∑ i, b i * h i s with hGd
  set Φ : ℝ → ℝ := fun ξ => ∑ i, b i * psi c (h i) ξ with hΦd
  set N := ∫ θ in Ioi 1, fullTail Φ θ ^ 2 with hNd
  set lam0 := (μ i₀ * √(c / (2 * π))) ^ 2 with hlam0
  have hc0 : 0 < c := lt_of_lt_of_le (by norm_num) hc
  have hc80 : (80 : ℝ) ≤ c := le_trans (by norm_num) hc
  have hc2π : 2 * π ≤ c := by linarith [Real.pi_lt_four]
  have hχc : ∀ i, χ i < c ^ 2 := fun i => by have := hσ i; nlinarith
  have hg0 : ∀ i, ∃ s ∈ Icc (-1 : ℝ) 1, h i s ≠ 0 := fun i => Cvs.L2a.PolarParameterBessel.exists_ne_zero_of_norm (hnorm i)
  have hcont : ∀ i, ContinuousOn (h i) (uIcc (-1) 1) := fun i s hs =>
    (hg i s hs).continuousAt.continuousWithinAt
  have hcontI : ∀ i, ContinuousOn (h i) (Icc (-1) 1) := fun i => by
    simpa [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hcont i
  have hmass : ∀ i, 0 < ∫ t in (1 : ℝ)..3, psi c (h i) t ^ 2 :=
    Cvs.Prolate.AngularBesselInequality.hM_of_angular hg hg₁ hg₂c hang heven hg0 hc0 hχ0 (by norm_num)
  -- the floor at infinity
  obtain ⟨hκF, hJA⟩ := Cvs.L2a.FrameFloorIntegerM.JA_integer_floor b hg hg₁ hg₂c hang hc hχ0 hσ hχi heven hg0 hμ
    hidx hJ (Cvs.L2a.SecondModeShells.shellM2_star b hg hg₁ hg₂c hang hc hχ0 hσ hχi hmass)
    (fun M hM => Cvs.L2a.LocalResidualBound.resLoc_le hc (Nat.cast_nonneg _) hJ hM) (by norm_num)
  have hFF : ∃ᶠ X in atTop, κF * ∑ i, b i ^ 2 * (∫ ξ in (1 : ℝ)..X, psi c (h i) ξ ^ 2)
      ≤ ∫ θ in Ioi 1, Cvs.L2a.PositionTruncatedTail.posTail Φ X θ ^ 2 := by
    refine frequently_atTop.2 fun X₀ => ⟨((max 3 ⌈X₀⌉₊ : ℕ) : ℝ), ?_, ?_⟩
    · exact (Nat.le_ceil X₀).trans (by exact_mod_cast le_max_right 3 ⌈X₀⌉₊)
    · have h3 : 3 ≤ max 3 ⌈X₀⌉₊ := le_max_left _ _
      have h1 : (1 : ℝ) < ((max 3 ⌈X₀⌉₊ : ℕ) : ℝ) := by exact_mod_cast (show 1 < max 3 ⌈X₀⌉₊ by omega)
      exact hJA _ h3 (Cvs.Prolate.AngularBesselInequality.hM_of_angular hg hg₁ hg₂c hang heven hg0 hc0 hχ0 h1)
  have hfloor : κF * ∑ i, b i ^ 2 * (∫ ξ in Ioi 1, psi c (h i) ξ ^ 2) ≤ N :=
    Cvs.L2a.FullTailFloorLimit.floor_limit b hg hg₁ hg₂c hc0 hFF
  have hN0 : 0 ≤ N := setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _
  -- the four inputs
  have hW := (Cvs.L2a.FullTailDeepSpanClosed.L2a_fulltail_span_closed b hg hg₁ hg₂c hang hc hχ0 hσ hχi heven hg0 hμ
    hidx hJ hκ1 hT hmass).2.2
  have hWB := Cvs.L2a.FullTailBilinearBound.polar_bil_le_of_floor b hg hg₁ hg₂c hang hc80 hχ0 hχc hχi hκF hfloor
  have hA2 := Cvs.L2a.FullTailBilinearBound.A2_le_A2bar hc80 hJ
  have hWB' : |Cvs.L2a.FullTailPolarisation.WinfBil Φ Psi| ≤ w1Bar κF * √N := by
    refine hWB.trans (mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _))
    unfold w1Bar
    exact add_le_add le_rfl (div_le_div_of_nonneg_right hA2 (Real.sqrt_nonneg _))
  have hlam := Cvs.L2a.PolarParameterBessel.lam_ge_deep hg hg₁ hg₂c hang hc80 hσ heven hg0 hμ hidx
  have hε := Cvs.L2a.PolarParameterBessel.polar_eps_le_of_floor i₀ b hc0 hg hg₁ hg₂c hang heven hnorm hχi hμ
    hground hidx (by norm_num) (fun i _ => hlam i) hpole hκF hfloor
  have hx : |2 * π / c * G 0| ≤ epsBar κF * √N := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π / c)]; exact hε
  -- the identity of Cvs.L2a.WindowFormTailLimit
  have hG : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G (∑ i, b i * h₁ i s) s :=
    Cvs.L2a.FullTailBilinearChannels.hasDerivAt_span b hg
  have hG₁ := Cvs.L2a.FullTailBilinearChannels.hasDerivAt_span b hg₁
  have hG₂c : ContinuousOn (fun s => ∑ i, b i * h₂ i s) (uIcc (-1) 1) :=
    continuousOn_finsetSum _ fun i _ => continuousOn_const.mul (hg₂c i)
  have hGeven : ∀ s ∈ Icc (-1 : ℝ) 1, G (-s) = G s := fun s hs =>
    Finset.sum_congr rfl fun i _ => by rw [heven i s hs]
  have hGi : ∫ s in (-1 : ℝ)..1, G s = 0 := by
    show ∫ s in (-1 : ℝ)..1, ∑ i, b i * h i s = 0
    rw [intervalIntegral.integral_finsetSum (f := fun i s => b i * h i s) fun i _ =>
      (ContinuousOn.mul continuousOn_const (hcont i)).intervalIntegrable]
    simp_rw [intervalIntegral.integral_const_mul]; exact hpole
  have hQW := Cvs.L2a.WindowFormTailLimit.window_eq_polar hc2π hG hG₁ hG₂c hGeven hGi hP hR hE1
  rw [← Cvs.L2a.FullTailBilinearChannels.span_eq_psi b hg] at hQW
  have hcore : bPrime c κ J * N ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R
      (Cvs.L2a.TailLogScaleTest.logScale (Cvs.Xi.EImageWindowPoisson.window (2 * π / c) G)) := by
    rw [hQW]
    have := polar_lower hN0 hW hx hWB' abs_Winf_Psi_le (epsBar_nonneg _)
    unfold bPrime Kpol; exact this
  have hQW0 : 0 ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R
      (Cvs.L2a.TailLogScaleTest.logScale (Cvs.Xi.EImageWindowPoisson.window (2 * π / c) G)) :=
    (mul_nonneg hb hN0).trans hcore
  -- the masses and the window norm
  set S := ∑ i ∈ Finset.univ.erase i₀, b i ^ 2 with hSd
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hM : ∀ i, ∫ ξ in Ioi 1, psi c (h i) ξ ^ 2 = π / c * (1 - (μ i * √(c / (2 * π))) ^ 2) := fun i =>
    Cvs.Prolate.AngularBesselInequality.mass_eq hc0 (hcontI i) (heven i) (hμ i) (hnorm i)
  have hPS : π / c * (1 - Λ) * S ≤ ∑ i, b i ^ 2 * ∫ ξ in Ioi 1, psi c (h i) ξ ^ 2 := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀), hSd, Finset.mul_sum]
    have h0 : 0 ≤ b i₀ ^ 2 * ∫ ξ in Ioi 1, psi c (h i₀) ξ ^ 2 :=
      mul_nonneg (sq_nonneg _) (setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _)
    have hsum : ∑ i ∈ Finset.univ.erase i₀, π / c * (1 - Λ) * b i ^ 2
        ≤ ∑ i ∈ Finset.univ.erase i₀, b i ^ 2 * ∫ ξ in Ioi 1, psi c (h i) ξ ^ 2 :=
      Finset.sum_le_sum fun i hi => by
        rw [hM i]
        have hl := hΛ i (Finset.ne_of_mem_erase hi)
        have hπc : 0 < π / c := by positivity
        nlinarith [mul_nonneg (mul_nonneg (sq_nonneg (b i)) hπc.le) (sub_nonneg.2 hl)]
    linarith
  have horth := Cvs.Prolate.AngularBesselInequality.orthonormal_of_angular Finset.univ hg hg₁ hang hχi.injOn
    (fun i _ => hnorm i)
  have hGsq : ∫ s in (-1 : ℝ)..1, G s ^ 2 = ∑ i, b i ^ 2 := by
    have hii : ∀ i j, ContinuousOn (fun s => b i * b j * (h i s * h j s)) (uIcc (-1) 1) := fun i j =>
      continuousOn_const.mul ((hcont i).mul (hcont j))
    calc ∫ s in (-1 : ℝ)..1, G s ^ 2 = ∫ s in (-1 : ℝ)..1, ∑ i, ∑ j, b i * b j * (h i s * h j s) := by
          congr 1; funext s; simp only [hGd, sq, Finset.sum_mul_sum]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      _ = ∑ i, ∑ j, b i * b j * ∫ s in (-1 : ℝ)..1, h i s * h j s := by
          rw [intervalIntegral.integral_finsetSum fun i _ =>
            (continuousOn_finsetSum _ fun j _ => hii i j).intervalIntegrable]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [intervalIntegral.integral_finsetSum fun j _ => (hii i j).intervalIntegrable]
          exact Finset.sum_congr rfl fun j _ => intervalIntegral.integral_const_mul _ _
      _ = ∑ i, b i ^ 2 := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_congr rfl fun j _ => by rw [horth i (Finset.mem_univ i) j (Finset.mem_univ j)]]
          simp [sq]
  -- the ground coefficient
  set I : ι → ℝ := fun i => ∫ s in (-1 : ℝ)..1, h i s with hId
  have hI0 : I i₀ ≠ 0 := by
    have e : I i₀ = μ i₀ * h i₀ 0 := Cvs.Prolate.AngularBesselInequality.integral_eq_mu_mul (hμ i₀)
    have hμ0 := Cvs.Prolate.SlepianEvenOrdering.mu_pos_of_even_index hc0 (hg i₀) (hg₁ i₀) (hg₂c i₀) (hang i₀) (heven i₀)
      (hg0 i₀) (hμ i₀) (hidx i₀)
    have hh0 := Cvs.Prolate.AngularBesselInequality.half_le_ground_sq (hg i₀) (hg₁ i₀) (hang i₀) (heven i₀) hground
      (hnorm i₀)
    have : h i₀ 0 ≠ 0 := fun h0 => by rw [h0] at hh0; norm_num at hh0
    rw [e]; exact mul_ne_zero hμ0.ne' this
  have hb0 : b i₀ = -∑ i ∈ Finset.univ.erase i₀, b i * (I i / I i₀) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)] at hpole
    have e : ∑ i ∈ Finset.univ.erase i₀, b i * (I i / I i₀)
        = (∑ i ∈ Finset.univ.erase i₀, b i * I i) / I i₀ := by
      rw [Finset.sum_div]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [e, show ∑ i ∈ Finset.univ.erase i₀, b i * I i = -(b i₀ * I i₀) by simp only [hId]; linarith]
    field_simp
  have halpha := Cvs.Xi.EImageWindowPoisson.sum_alpha_sq_le (Finset.univ.erase i₀) h (fun i _ => hcont i)
    (fun i hi j hj => horth i (Finset.mem_univ i) j (Finset.mem_univ j)) hc0 (hg i₀) (hg₁ i₀) (hang i₀)
    (heven i₀) hground (hnorm i₀) (hμ i₀)
  have hq0 : 0 ≤ 2 * c / (π * lam0) := by positivity
  have hb0sq : b i₀ ^ 2 ≤ 2 * c / (π * lam0) * S := by
    rw [hb0, neg_sq]
    refine (Finset.sum_mul_sq_le_sq_mul_sq _ _ _).trans ?_
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right halpha hS0
  have hGS : ∫ s in (-1 : ℝ)..1, G s ^ 2 ≤ (1 + 2 * c / (π * lam0)) * S := by
    have e : ∑ i, b i ^ 2 = b i₀ ^ 2 + S := (Finset.add_sum_erase _ _ (Finset.mem_univ i₀)).symm
    rw [hGsq, e]; linarith [hb0sq]
  have hGc : ContinuousOn G (Icc (-1) 1) :=
    continuousOn_finsetSum _ fun i _ => continuousOn_const.mul (hcontI i)
  have hk := Cvs.Xi.EImageWindowPoisson.integral_window_sq_le_half (by positivity : (0 : ℝ) < 2 * π / c) hGc hGeven
  have hH := Hx_pos hc2π
  set q := 2 * c / (π * lam0) with hqd
  have hk' : ∫ θ, Cvs.Xi.EImageWindowPoisson.window (2 * π / c) G θ ^ 2 ≤ Hx c / 2 * ((1 + q) * S) :=
    hk.trans (mul_le_mul_of_nonneg_left hGS (by unfold Hx at hH; positivity))
  have hk0 : 0 ≤ ∫ θ, Cvs.Xi.EImageWindowPoisson.window (2 * π / c) G θ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hc20 : 0 ≤ c2 c κ J lam0 := by
    unfold c2
    exact div_nonneg (mul_nonneg (mul_nonneg (by positivity) hb) hκF.le)
      (mul_nonneg (mul_nonneg hc0.le hH.le) (by linarith))
  rcases le_or_gt Λ 1 with hΛ1 | hΛ1
  · calc c2 c κ J lam0 * (1 - Λ) * ∫ θ, Cvs.Xi.EImageWindowPoisson.window (2 * π / c) G θ ^ 2
        ≤ c2 c κ J lam0 * (1 - Λ) * (Hx c / 2 * ((1 + q) * S)) :=
          mul_le_mul_of_nonneg_left hk' (mul_nonneg hc20 (sub_nonneg.2 hΛ1))
      _ = bPrime c κ J * κF * (π / c * (1 - Λ) * S) := by
          have h1q : 1 + q ≠ 0 := by linarith
          unfold c2; rw [← hqd, ← hκFd]; field_simp
      _ ≤ bPrime c κ J * κF * ∑ i, b i ^ 2 * ∫ ξ in Ioi 1, psi c (h i) ξ ^ 2 :=
          mul_le_mul_of_nonneg_left hPS (mul_nonneg hb hκF.le)
      _ ≤ bPrime c κ J * N := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hfloor hb
      _ ≤ _ := hcore
  · have : c2 c κ J lam0 * (1 - Λ) * ∫ θ, Cvs.Xi.EImageWindowPoisson.window (2 * π / c) G θ ^ 2 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hc20 (by linarith)) hk0
    linarith

/-! ### The explicit threshold `c₀` -/

/-- `κ⋆ = max(2, 32Ē)`, so that `Ē/(κ⋆κ_F) ≤ ½` once `κ_F ≥ 1/16`. -/
def kapStar : ℝ := max 2 (32 * Cvs.L2a.LowConstantUniform.Ebar)

/-- `B₀ = 57/4 + ½log π − ½a(0) + 58 + log 2 + 4√(24C̄²/π) + (126/5)(Λ̄₀ + κ̄) + K_pol(1/16)`,
`C̄ = Cbar 80 r̄_F`: the constant with `b′ ≥ ½log(T/2) − B₀`. -/
def B0 : ℝ :=
  57 / 4 + Real.log π / 2 - archSymbol 0 / 2 + 58 + Real.log 2
    + 4 * √(24 * Cvs.Prolate.Mellin.FarPartLevelBound.Cbar 80 Cvs.L2a.LowConstantUniform.rBarF ^ 2 / π)
    + 126 / 5 * (Cvs.L2a.RampCutSumsUniform.LambdaBar0 + Cvs.L2a.KappaUniformInX.kappaBar) + Kpol (1 / 16)

/-- **The threshold** `c₀ = max(10¹⁶, 16κ⋆²e^{4B₀+4})`. -/
def c0 : ℝ := max (10 ^ 16) (16 * kapStar ^ 2 * exp (4 * B0 + 4))

theorem Kpol_nonneg (κ : ℝ) : 0 ≤ Kpol κ := by
  unfold Kpol
  have := w1Bar_nonneg κ; have := epsBar_nonneg κ; have := WPsiBar_nonneg
  positivity

theorem B0_nonneg : 0 ≤ B0 := by
  have ha := Cvs.StepA.DirichletCosineTrial.archSymbol_zero_upper
  have hπ : 0 ≤ Real.log π := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hL := Cvs.L2a.RampCutSumsUniform.LambdaBar0_nonneg
  have hk := Cvs.L2a.KappaUniformInX.kappaBar_nonneg
  have hK := Kpol_nonneg (1 / 16)
  have hs := Real.sqrt_nonneg (24 * Cvs.Prolate.Mellin.FarPartLevelBound.Cbar 80 Cvs.L2a.LowConstantUniform.rBarF ^ 2 / π)
  unfold B0
  nlinarith

/-- **The bracket against `T`**: for `κ ≥ max(2, 32Ē)`, `c ≥ 10¹⁶`, `0 ≤ J ≤ c/4 + 1` and `T = TL c κ ≥ 2`,
`½log(T/2) − B₀ ≤ b′`. -/
theorem bPrime_ge_log {c κ J : ℝ} (hc : 10 ^ 16 ≤ c) (hκ2 : 2 ≤ κ) (hκE : 32 * Cvs.L2a.LowConstantUniform.Ebar ≤ κ)
    (hJ0 : 0 ≤ J) (hJ : J ≤ c / 4 + 1) (hT : 2 ≤ Cvs.L2a.FullTailDeepSpan.TL c κ) :
    Real.log (Cvs.L2a.FullTailDeepSpan.TL c κ / 2) / 2 - B0 ≤ bPrime c κ J := by
  set T := Cvs.L2a.FullTailDeepSpan.TL c κ with hTd
  set κF := kapF c J with hκFd
  have hc0 : 0 < c := lt_of_lt_of_le (by norm_num) hc
  have hc80 : (80 : ℝ) ≤ c := le_trans (by norm_num) hc
  have hκF := kapF_ge hc hJ0 hJ
  have hκF0 : 0 < κF := lt_of_lt_of_le (by norm_num) hκF
  have hlogc : Real.log 80 ≤ Real.log c := Real.log_le_log (by norm_num) hc80
  have hlog80 : 0 ≤ Real.log 80 := Real.log_nonneg (by norm_num)
  have hK0 : 1 ≤ κ * (1 + Real.log c) := by nlinarith
  have hTc : T ≤ c := div_le_self hc0.le hK0
  have hT0 : 0 < T := by linarith
  -- the arch terms
  have f1 := Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol_ge hT
  have f2 : 57 / T ≤ 57 / 2 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hT
  have f2' : 114 / T ≤ 57 := by
    have := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 114) (by norm_num) hT; linarith
  have f3 := Cvs.WeilForm.Archimedean.SymbolIncrementQuadratic.archSymbol_sub_nonneg T
  have hE0 : 0 ≤ Cvs.L2a.LowConstantUniform.Ebar := by unfold Cvs.L2a.LowConstantUniform.Ebar; positivity
  have f4 : Cvs.L2a.LowConstantUniform.Ebar / (κ * κF) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have f5 := mul_le_mul_of_nonneg_left f4 f3
  -- the loc term
  set Cb := Cvs.Prolate.Mellin.FarPartLevelBound.Cbar 80 Cvs.L2a.LowConstantUniform.rBarF
  have hr : Cvs.L2a.FullTailDeepSpan.rL c κ ≤ Cvs.L2a.LowConstantUniform.rBarF := by
    have e : Cvs.L2a.FullTailDeepSpan.rL c κ = 1 / (κ * (1 + Real.log c)) ^ 2 + 1 / (16 * c ^ 2) := by
      unfold Cvs.L2a.FullTailDeepSpan.rL Cvs.L2a.FullTailDeepSpan.TL; field_simp
    rw [e]; unfold Cvs.L2a.LowConstantUniform.rBarF
    have h1 : 1 / (κ * (1 + Real.log c)) ^ 2 ≤ 1 / (4 * (1 + Real.log 80) ^ 2) := by
      refine one_div_le_one_div_of_le (by positivity) ?_
      have : 2 * (1 + Real.log 80) ≤ κ * (1 + Real.log c) := by nlinarith
      nlinarith
    have h2 : 1 / (16 * c ^ 2) ≤ 1 / (16 * 80 ^ 2) :=
      one_div_le_one_div_of_le (by positivity) (by nlinarith)
    linarith
  obtain ⟨hC0, hC⟩ := Cvs.L2a.LowConstantUniform.Cbar_le hc80 hr
  have hA : Cvs.L2a.PerLevelFarLeak.ALoc J c (Cvs.L2a.FullTailDeepSpan.rL c κ) T κF ≤ 48 * Cb ^ 2 / π := by
    unfold Cvs.L2a.PerLevelFarLeak.ALoc
    have hCC : Cvs.Prolate.Mellin.FarPartLevelBound.Cbar c (Cvs.L2a.FullTailDeepSpan.rL c κ) ^ 2 ≤ Cb ^ 2 :=
      pow_le_pow_left₀ hC0 hC 2
    have hnum : 6 * J * Cvs.Prolate.Mellin.FarPartLevelBound.Cbar c (Cvs.L2a.FullTailDeepSpan.rL c κ) ^ 2 * T
        ≤ 6 * (c / 2) * Cb ^ 2 * c := by
      have s1 : 6 * J ≤ 6 * (c / 2) := by linarith
      have s2 : 6 * J * Cvs.Prolate.Mellin.FarPartLevelBound.Cbar c (Cvs.L2a.FullTailDeepSpan.rL c κ) ^ 2 ≤ 6 * (c / 2) * Cb ^ 2 :=
        mul_le_mul s1 hCC (sq_nonneg _) (by positivity)
      exact mul_le_mul s2 hTc hT0.le (by positivity)
    have hden : π * c ^ 2 * (1 / 16) ≤ π * c ^ 2 * κF := mul_le_mul_of_nonneg_left hκF (by positivity)
    calc 6 * J * Cvs.Prolate.Mellin.FarPartLevelBound.Cbar c (Cvs.L2a.FullTailDeepSpan.rL c κ) ^ 2 * T / (π * c ^ 2 * κF)
        ≤ 6 * (c / 2) * Cb ^ 2 * c / (π * c ^ 2 * (1 / 16)) :=
          div_le_div₀ (by positivity) hnum (by positivity) hden
      _ = 48 * Cb ^ 2 / π := by field_simp; ring
  have f6 : √(Cvs.L2a.PerLevelFarLeak.ALoc J c (Cvs.L2a.FullTailDeepSpan.rL c κ) T κF / 2) ≤ √(24 * Cb ^ 2 / π) :=
    Real.sqrt_le_sqrt (by have := div_le_div_of_nonneg_right hA (by norm_num : (0 : ℝ) ≤ 2); linarith [this,
      show 48 * Cb ^ 2 / π / 2 = 24 * Cb ^ 2 / π by ring])
  -- the NS and tail terms
  set L := Cvs.L2a.RampCutSumsUniform.LambdaBar0 + Cvs.L2a.KappaUniformInX.kappaBar
  have hL0 : 0 ≤ L := add_nonneg Cvs.L2a.RampCutSumsUniform.LambdaBar0_nonneg Cvs.L2a.KappaUniformInX.kappaBar_nonneg
  have f7 : 63 / 40 * L / κF ≤ 126 / 5 * L := by
    rw [div_le_iff₀ hκF0]; nlinarith
  have f8 : 49 * (c / 4 + 1) / (2 * c ^ 2 * κF) ≤ 1 := by
    rw [div_le_one (by positivity)]; nlinarith
  have f9 := Kpol_anti (by norm_num : (0 : ℝ) < 1 / 16) hκF
  unfold bPrime Cvs.L2a.FullTailDeepSpan.bBar
  rw [← hTd, ← hκFd]
  unfold B0
  nlinarith

/-- **`b′ ≥ 1` past `c₀`**: for `c ≥ c₀` and `0 ≤ J ≤ c/4 + 1`, `T = TL c κ⋆ ≥ 2` and `b′(c, κ⋆, J) ≥ 1`;
`T ≥ √c/(2κ⋆) ≥ 2e^{2B₀+2}` from `1 + log c ≤ 2√c`. -/
theorem bPrime_ge_one {c J : ℝ} (hc : c0 ≤ c) (hJ0 : 0 ≤ J) (hJ : J ≤ c / 4 + 1) :
    2 ≤ Cvs.L2a.FullTailDeepSpan.TL c kapStar ∧ 1 ≤ bPrime c kapStar J := by
  have hc16 : (10 : ℝ) ^ 16 ≤ c := le_trans (le_max_left _ _) hc
  have hcB : 16 * kapStar ^ 2 * exp (4 * B0 + 4) ≤ c := le_trans (le_max_right _ _) hc
  have hc0 : 0 < c := lt_of_lt_of_le (by norm_num) hc16
  have hκ2 : 2 ≤ kapStar := le_max_left _ _
  have hκ0 : 0 < kapStar := by linarith
  have hsc := Real.sqrt_pos.2 hc0
  -- `1 + log c ≤ 2√c`
  have hlog : 1 + Real.log c ≤ 2 * √c := by
    have h1 := Real.log_le_sub_one_of_pos hsc
    rw [Real.log_sqrt hc0.le] at h1
    linarith
  have hlogc : 0 ≤ Real.log c := Real.log_nonneg (by linarith)
  have hTge : √c / (2 * kapStar) ≤ Cvs.L2a.FullTailDeepSpan.TL c kapStar := by
    unfold Cvs.L2a.FullTailDeepSpan.TL
    have e : √c / (2 * kapStar) = c / (kapStar * (2 * √c)) := by
      rw [show c = √c * √c from (Real.mul_self_sqrt hc0.le).symm]
      rw [Real.sqrt_mul_self hsc.le]; field_simp
    rw [e]
    exact div_le_div_of_nonneg_left hc0.le (by positivity) (mul_le_mul_of_nonneg_left hlog hκ0.le)
  have hE := exp_pos (2 * B0 + 2)
  have hsq : 4 * kapStar * exp (2 * B0 + 2) ≤ √c := by
    have e : 16 * kapStar ^ 2 * exp (4 * B0 + 4) = (4 * kapStar * exp (2 * B0 + 2)) ^ 2 := by
      rw [mul_pow, ← Real.exp_nat_mul]; push_cast; ring_nf
    rw [e] at hcB
    calc 4 * kapStar * exp (2 * B0 + 2) = √((4 * kapStar * exp (2 * B0 + 2)) ^ 2) :=
          (Real.sqrt_sq (by positivity)).symm
      _ ≤ √c := Real.sqrt_le_sqrt hcB
  have hT2 : 2 * exp (2 * B0 + 2) ≤ Cvs.L2a.FullTailDeepSpan.TL c kapStar := by
    refine le_trans ?_ hTge
    rw [le_div_iff₀ (by positivity)]; nlinarith
  have hE1 : 1 ≤ exp (2 * B0 + 2) := Real.one_le_exp (by linarith [B0_nonneg])
  have hT : 2 ≤ Cvs.L2a.FullTailDeepSpan.TL c kapStar := by linarith
  refine ⟨hT, ?_⟩
  have hb := bPrime_ge_log hc16 hκ2 (le_max_right _ _) hJ0 hJ hT
  have hl : 2 * B0 + 2 ≤ Real.log (Cvs.L2a.FullTailDeepSpan.TL c kapStar / 2) := by
    rw [Real.le_log_iff_exp_le (by linarith)]; linarith
  linarith

/-! ### SPINE-L2a(5) past `c₀`, on `D₀` and on `R_D` -/

/-- Levels are ordered by their even counts: for `y` in a set `S` with `1 ≤ m = #(S ∩ (−∞, x)) ≤ #(S ∩ (−∞, y))`,
`x ≤ y`. -/
theorem le_of_ncard_le {S : Set ℝ} {x y : ℝ} {m : ℕ} (hm : 1 ≤ m) (hx : (S ∩ Iio x).ncard = m) (hy : y ∈ S)
    (hle : m ≤ (S ∩ Iio y).ncard) : x ≤ y := by
  by_contra hlt
  push Not at hlt
  have hfin : (S ∩ Iio x).Finite := Set.finite_of_ncard_ne_zero (by omega)
  have hss : S ∩ Iio y ⊂ S ∩ Iio x := by
    refine ⟨fun z hz => ⟨hz.1, lt_trans hz.2 hlt⟩, fun h => ?_⟩
    exact lt_irrefl y (h ⟨hy, hlt⟩).2
  have := Set.ncard_lt_ncard hss hfin
  omega

/-- **SPINE-L2a(5) past `c₀`**: on the deep span with ground `i₀`, every other rung at even count `≥ m ≥ 1`, and a
reference rung `g` at even count `m` (`λ_m = (μ_g√(c/2π))²`): for `c ≥ c₀`, a pole-free `G = Σ bᵢhᵢ` with E1's prime
limit has `(π/(8cH_x(1 + 2c/(πλ₀))))(1 − λ_m)‖k_G‖² ≤ QW(k_G)`. -/
theorem L2a_window_deep (i₀ : ι) {h h₁ h₂ : ι → ℝ → ℝ} {g g₁ g₂ : ℝ → ℝ} {c χg μg : ℝ} {χ μ : ι → ℝ}
    (b : ι → ℝ) {m : ℕ} {P R : ℕ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (h i) (h₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (h₁ i) (h₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (h₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * h₂ i s - 2 * s * h₁ i s - c ^ 2 * s ^ 2 * h i s + χ i * h i s = 0)
    (hc : c0 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hσ : ∀ i, 5 * c ≤ c ^ 2 - χ i) (hχi : Function.Injective χ)
    (heven : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, h i (-s) = h i s) (hnorm : ∀ i, ∫ s in (-1 : ℝ)..1, h i s ^ 2 = 1)
    (hμ : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, psi c (h i) s = μ i * h i s)
    (hground : (Cvs.Prolate.EdgeCentreSign.evenSpec (Cvs.Prolate.RegularSolutionEdge.sqC c) ∩ Iio (χ i₀)).ncard = 0)
    (hidx : ∀ i, Even (Cvs.Prolate.EdgeCentreSign.evenSpec (Cvs.Prolate.RegularSolutionEdge.sqC c) ∩ Iio (χ i)).ncard)
    (hJ : (Fintype.card ι : ℝ) ≤ c / 4 + 1)
    (hm : 1 ≤ m) (hcount : ∀ i, i ≠ i₀ →
      m ≤ (Cvs.Prolate.EdgeCentreSign.evenSpec (Cvs.Prolate.RegularSolutionEdge.sqC c) ∩ Iio (χ i)).ncard)
    (hgd : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hgd₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hgd₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hgang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χg * g s = 0)
    (hgeven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) (hgnorm : ∫ s in (-1 : ℝ)..1, g s ^ 2 = 1)
    (hgμ : ∀ s ∈ Icc (-1 : ℝ) 1, psi c g s = μg * g s)
    (hgcount : (Cvs.Prolate.EdgeCentreSign.evenSpec (Cvs.Prolate.RegularSolutionEdge.sqC c) ∩ Iio χg).ncard = m)
    (hpole : ∑ i, b i * ∫ s in (-1 : ℝ)..1, h i s = 0)
    (hP : 1 / (2 * π / c) ≤ P) (hR : Real.log (1 / (2 * π / c)) ≤ R * Real.log 2)
    (hE1 : Cvs.L2a.WindowFormTailLimit.PrimeTailLimit c
      (Cvs.L2a.WindowFormTailLimit.regProfile c fun s => ∑ i, b i * h i s)) :
    π / (8 * c * Hx c * (1 + 2 * c / (π * (μ i₀ * √(c / (2 * π))) ^ 2))) * (1 - (μg * √(c / (2 * π))) ^ 2)
        * ∫ θ, Cvs.Xi.EImageWindowPoisson.window (2 * π / c) (fun s => ∑ i, b i * h i s) θ ^ 2
      ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (Cvs.L2a.TailLogScaleTest.logScale
          (Cvs.Xi.EImageWindowPoisson.window (2 * π / c) fun s => ∑ i, b i * h i s)) := by
  have hc16 : (10 : ℝ) ^ 16 ≤ c := le_trans (le_max_left _ _) hc
  have hc0 : 0 < c := lt_of_lt_of_le (by norm_num) hc16
  have hc2π : 2 * π ≤ c := by linarith [Real.pi_lt_four]
  obtain ⟨hT, hb1⟩ := bPrime_ge_one hc (Nat.cast_nonneg _) hJ
  have hg0 : ∀ i, ∃ s ∈ Icc (-1 : ℝ) 1, h i s ≠ 0 := fun i => Cvs.L2a.PolarParameterBessel.exists_ne_zero_of_norm (hnorm i)
  have hgg0 := Cvs.L2a.PolarParameterBessel.exists_ne_zero_of_norm hgnorm
  have hΛ : ∀ i, i ≠ i₀ → (μ i * √(c / (2 * π))) ^ 2 ≤ (μg * √(c / (2 * π))) ^ 2 := fun i hi => by
    have hmem := Cvs.Prolate.EdgeCentreSign.mem_evenSpec_of_angular (hg i) (hg₁ i) (hang i) (heven i) (hg0 i)
    have hle := le_of_ncard_le hm hgcount hmem (hcount i hi)
    exact Cvs.Prolate.SlepianEvenOrdering.lam_le_of_chi_le hc0 hgd hgd₁ hgd₂c hgang hgeven hgg0 (hg i) (hg₁ i) (hg₂c i)
      (hang i) (heven i) (hg0 i) hgμ (hμ i) hle
  have hmain := L2a_window_margin i₀ b hg hg₁ hg₂c hang hc16 hχ0 hσ hχi heven hnorm hμ hground hidx hJ
    (show (1 : ℝ) ≤ kapStar from le_trans (by norm_num) (le_max_left 2 _)) hT hΛ hpole hP hR hE1 (by linarith)
  -- `λ_m ≤ 1` from the nonnegative mass
  have hgc : ContinuousOn g (Icc (-1) 1) := by
    have : ContinuousOn g (uIcc (-1) 1) := fun s hs => (hgd s hs).continuousAt.continuousWithinAt
    simpa [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using this
  have hMg := Cvs.Prolate.AngularBesselInequality.mass_eq hc0 hgc hgeven hgμ hgnorm
  have hMg0 : 0 ≤ ∫ ξ in Ioi 1, psi c g ξ ^ 2 := setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _
  have hlam1 : 0 ≤ 1 - (μg * √(c / (2 * π))) ^ 2 := by
    rw [hMg] at hMg0
    exact nonneg_of_mul_nonneg_right (by linarith) (by positivity : (0 : ℝ) < π / c)
  have hk0 : 0 ≤ ∫ θ, Cvs.Xi.EImageWindowPoisson.window (2 * π / c) (fun s => ∑ i, b i * h i s) θ ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  have hH := Hx_pos hc2π
  have hq0 : 0 ≤ 2 * c / (π * (μ i₀ * √(c / (2 * π))) ^ 2) := by positivity
  have hκF := kapF_ge hc16 (Nat.cast_nonneg _) hJ
  have hc2 : π / (8 * c * Hx c * (1 + 2 * c / (π * (μ i₀ * √(c / (2 * π))) ^ 2)))
      ≤ c2 c kapStar (Fintype.card ι) ((μ i₀ * √(c / (2 * π))) ^ 2) := by
    unfold c2
    rw [show π / (8 * c * Hx c * (1 + 2 * c / (π * (μ i₀ * √(c / (2 * π))) ^ 2)))
        = 2 * π * 1 * (1 / 16) / (c * Hx c * (1 + 2 * c / (π * (μ i₀ * √(c / (2 * π))) ^ 2))) by
      field_simp; ring]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    exact mul_le_mul (mul_le_mul_of_nonneg_left hb1 (by positivity)) hκF (by norm_num) (by positivity)
  exact le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc2 hlam1) hk0) hmain

end Cvs.L2a.WindowFormDeepSpan
