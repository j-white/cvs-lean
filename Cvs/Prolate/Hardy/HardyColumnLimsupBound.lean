import Mathlib
import Cvs.Prolate.Gram.CentralResolventTrace
import Cvs.Prolate.Hardy.AveragedColumnEnergy
import Cvs.Prolate.Hardy.CarrierNegativeFreqRate
import Cvs.Prolate.Hardy.ColumnAmplitudeBound
import Cvs.Prolate.Hardy.ColumnTwoCarrierWave
import Cvs.Prolate.Hardy.ColumnWaveErrorBound
import Cvs.Prolate.Hardy.ColumnWaveSquareIntegral
import Cvs.Prolate.Hardy.ExtensionTraceColumnIntegral
import Cvs.Prolate.Hardy.ExteriorWeightAverages
import Cvs.Prolate.Hardy.HardyExtensionOperator
import Cvs.Prolate.Hardy.LipPhaseDecay
import Cvs.Prolate.Hardy.TwoCarrierAveragedEnergy
import Cvs.Prolate.Hardy.TwoCarrierWaveExplicit

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The column bound (16): `limsup_c S_J(c) ≤ S_∞(1/√3)` for the Hardy extension `J_c`

`‖J_cQe_u‖² ≤ (1 + η)‖V_u‖² + (1 + 1/η)(2g_uE_c)²`, integrated in `u > 1`, with `2∫‖V_u‖² → S_∞(ℓ)` and
`E_c → 3√(2t)` for the cuts `α = ½ + t`, `x₀ = ℓ − t`, `x₁ = ℓ + t`; so for every `ε > 0`, eventually
`S_J(c) ≤ S_∞(1/√3) + ε`, hence `≤ S_∞(3/5) + ε`.
-/

noncomputable section

open Real Set MeasureTheory Filter Topology

namespace Cvs.Prolate.Hardy.HardyColumnLimsupBound
open Cvs.ZeroCounting

open Cvs.Prolate.Hardy.ExtensionTraceColumnIntegral (L2R colA extS)
open Cvs.Prolate.Hardy.HardyExtensionOperator (hardyJ)
open Cvs.Prolate.Hardy.ColumnTwoCarrierWave (waveV)
open Cvs.Prolate.Hardy.ColumnAmplitudeBound (gU)
open Cvs.Prolate.Hardy.ColumnWaveErrorBound (ell errC)
open Cvs.Prolate.Hardy.AveragedColumnEnergy (avgEnergy)

theorem young {a b η : ℝ} (hη : 0 < η) : (a + b) ^ 2 ≤ (1 + η) * a ^ 2 + (1 + 1 / η) * b ^ 2 := by
  have h : 0 ≤ (η * a - b) ^ 2 := sq_nonneg _
  have : (1 + η) * a ^ 2 + (1 + 1 / η) * b ^ 2 - (a + b) ^ 2 = (η * a - b) ^ 2 / η := by
    field_simp; ring
  have : 0 ≤ (η * a - b) ^ 2 / η := div_nonneg h hη.le
  linarith

theorem integrableOn_gU_sq : IntegrableOn (fun u => gU u ^ 2) (Ioi 1) := by
  have := (Cvs.Prolate.Hardy.ExteriorWeightAverages.integrableOn_inv_sub_sq (a := 3 / 5) (by norm_num)).const_mul (1 / π ^ 2)
  refine IntegrableOn.congr_fun this (fun u _ => ?_) measurableSet_Ioi
  unfold gU; field_simp

theorem integral_gU_sq : ∫ u in Ioi 1, gU u ^ 2 = 5 / (2 * π ^ 2) := by
  have h := Cvs.Prolate.Hardy.ExteriorWeightAverages.integral_inv_sub_sq (a := 3 / 5) (by norm_num)
  rw [show ∫ u in Ioi 1, gU u ^ 2 = ∫ u in Ioi 1, 1 / π ^ 2 * (1 / (u - 3 / 5) ^ 2) from
    setIntegral_congr_fun measurableSet_Ioi fun u _ => by unfold gU; field_simp, integral_const_mul, h]
  field_simp; norm_num

theorem integrableOn_norm_waveV_sq {c : ℝ} (hc : 0 ≤ c) :
    IntegrableOn (fun u => ‖waveV c u ell‖ ^ 2) (Ioi 1) := by
  have h := (Cvs.Prolate.Hardy.ColumnWaveSquareIntegral.integrable_vfun_sq c).integral_prod_left
  refine Integrable.congr h ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact (Cvs.Prolate.Hardy.TwoCarrierWaveExplicit.norm_waveV_sq hc hu).symm

/-- **The integrated Young bound**:
`S_J(c) ≤ 2((1 + η)∫_{u>1}‖V_u‖² + (1 + 1/η)·4E_c²·5/(2π²))`. -/
theorem extS_le {c α x₀ x₁ η : ℝ} (hc : 0 < c) (hη : 0 < η) (hα : 1 / 2 < α) (h1 : α ≤ x₀)
    (h2 : x₀ < ell) (h3 : ell < x₁) (h4 : x₁ ≤ 3 / 5) :
    extS c (hardyJ c) ≤ 2 * ((1 + η) * ∫ u in Ioi 1, ‖waveV c u ell‖ ^ 2) +
      2 * ((1 + 1 / η) * (4 * errC c α x₀ x₁ ^ 2) * (5 / (2 * π ^ 2))) := by
  unfold extS
  have hint : IntegrableOn (fun u => (1 + η) * ‖waveV c u ell‖ ^ 2 +
      (1 + 1 / η) * (4 * errC c α x₀ x₁ ^ 2) * gU u ^ 2) (Ioi 1) :=
    ((integrableOn_norm_waveV_sq hc.le).const_mul _).add (integrableOn_gU_sq.const_mul _)
  have hle : ∫ u in Ioi 1, ‖hardyJ c (colA c u)‖ ^ 2 ≤ ∫ u in Ioi 1, ((1 + η) * ‖waveV c u ell‖ ^ 2 +
      (1 + 1 / η) * (4 * errC c α x₀ x₁ ^ 2) * gU u ^ 2) := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => sq_nonneg _) hint ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hE := Cvs.Prolate.Hardy.ColumnWaveErrorBound.norm_col_err_le hc hu hα h1 h2 h3 h4
    have htri : ‖hardyJ c (colA c u)‖ ≤ ‖waveV c u ell‖ + 2 * (gU u * errC c α x₀ x₁) := by
      have := norm_le_insert' (hardyJ c (colA c u)) (waveV c u ell)
      linarith [norm_sub_rev (hardyJ c (colA c u)) (waveV c u ell)]
    have hs : ‖hardyJ c (colA c u)‖ ^ 2 ≤ (‖waveV c u ell‖ + 2 * (gU u * errC c α x₀ x₁)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) htri 2
    refine hs.trans ((young hη).trans (le_of_eq ?_))
    ring
  rw [integral_add ((integrableOn_norm_waveV_sq hc.le).const_mul _) (integrableOn_gU_sq.const_mul _),
    integral_const_mul, integral_const_mul, integral_gU_sq] at hle
  linarith

theorem tendsto_sqrt_inv {k : ℝ} (hk : 0 < k) : Tendsto (fun c : ℝ => √(1 / (c * k))) atTop (𝓝 0) := by
  have h : Tendsto (fun c : ℝ => 1 / (c * k)) atTop (𝓝 0) := by
    have := (tendsto_id.atTop_mul_const hk).inv_tendsto_atTop
    exact this.congr fun c => by simp [div_eq_mul_inv]
  have h2 := (Real.continuous_sqrt.tendsto 0).comp h
  rw [Real.sqrt_zero] at h2
  exact h2

/-- `E_c → √(2(α − ½)) + √(2(ℓ − x₀)) + √(2(x₁ − ℓ))`. -/
theorem tendsto_errC {α x₀ x₁ : ℝ} (hα : 1 / 2 < α) (h1 : α ≤ x₀) (h2 : x₀ < ell) (h3 : ell < x₁) :
    Tendsto (fun c => errC c α x₀ x₁) atTop
      (𝓝 (√(2 * (α - 1 / 2)) + √(2 * (ell - x₀)) + √(2 * (x₁ - ell)))) := by
  have k0 : 0 < (√11 / 10 - 3 / 10) * (2 * π * (√11 / 10)) :=
    mul_pos Cvs.Prolate.Hardy.CarrierNegativeFreqRate.delta0_pos (by positivity)
  have k1 : 0 < Cvs.Prolate.Hardy.LipPhaseDecay.lipD x₁ * (2 * π) := mul_pos (Cvs.Prolate.Hardy.ColumnWaveErrorBound.lipD_pos h3) (by positivity)
  have k2 : 0 < -Cvs.Prolate.Hardy.LipPhaseDecay.lipD x₀ * (2 * π) :=
    mul_pos (by linarith [Cvs.Prolate.Hardy.ColumnWaveErrorBound.lipD_neg (hα.trans_le h1) h2]) (by positivity)
  have t0 := tendsto_sqrt_inv k0
  have t1 := tendsto_sqrt_inv k1
  have t2 := tendsto_sqrt_inv k2
  have := (((t0.const_mul (3 / 5 * π)).add ((t1.const_mul (Cvs.Prolate.Hardy.ColumnWaveErrorBound.kap x₁ (3 / 5) (Cvs.Prolate.Hardy.LipPhaseDecay.lipD x₁))).const_mul 2)).add
    ((t2.const_mul (Cvs.Prolate.Hardy.ColumnWaveErrorBound.kap α x₀ (-Cvs.Prolate.Hardy.LipPhaseDecay.lipD x₀))).const_mul 2)).add
      (tendsto_const_nhds (x := √(2 * (α - 1 / 2)) + √(2 * (ell - x₀)) + √(2 * (x₁ - ell))))
  simp only [mul_zero, add_zero, zero_add] at this
  refine this.congr fun c => ?_
  unfold errC
  simp only [mul_assoc]

theorem ell_lt_three_fifths : ell < 3 / 5 := by
  unfold Cvs.Prolate.Hardy.ColumnWaveErrorBound.ell
  rw [div_lt_iff₀ (by positivity)]
  have : (5 / 3 : ℝ) < √3 := by
    rw [show (5 / 3 : ℝ) = √((5 / 3) ^ 2) by rw [Real.sqrt_sq (by norm_num)] ]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

theorem avgEnergy_ell_nonneg : 0 ≤ avgEnergy ell := by
  rw [← Cvs.Prolate.Hardy.TwoCarrierAveragedEnergy.two_limL]
  have h := Cvs.Prolate.Hardy.TwoCarrierAveragedEnergy.tendsto_integral_waveV
  have : 0 ≤ Cvs.Prolate.Hardy.TwoCarrierAveragedEnergy.limL := ge_of_tendsto h (Filter.Eventually.of_forall fun c =>
    setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _)
  linarith

/-- **The column bound (16)**: for every `ε > 0`, eventually in `c`, `S_J(c) ≤ S_∞(1/√3) + ε`. -/
theorem extS_hardyJ_le {ε : ℝ} (hε : 0 < ε) : ∀ᶠ c : ℝ in atTop, extS c (hardyJ c) ≤ avgEnergy ell + ε := by
  have hA := avgEnergy_ell_nonneg
  set η := ε / (4 * (avgEnergy ell + 1)) with hηdef
  have hη : 0 < η := by positivity
  set Kη := (1 + 1 / η) * (20 / π ^ 2) * 18 with hK
  have hK0 : 0 < Kη := by positivity
  have hl := Cvs.Prolate.Hardy.ColumnWaveErrorBound.half_lt_ell
  have hl3 := ell_lt_three_fifths
  set t := min (min ((ell - 1 / 2) / 2) (3 / 5 - ell)) (ε / (4 * Kη)) with htdef
  have ht0 : 0 < t := lt_min (lt_min (by linarith) (by linarith)) (by positivity)
  have ht1 : t ≤ (ell - 1 / 2) / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have ht2 : t ≤ 3 / 5 - ell := (min_le_left _ _).trans (min_le_right _ _)
  have ht3 : t ≤ ε / (4 * Kη) := min_le_right _ _
  have hα : 1 / 2 < 1 / 2 + t := by linarith
  have h1 : 1 / 2 + t ≤ ell - t := by linarith
  have h2 : ell - t < ell := by linarith
  have h3 : ell < ell + t := by linarith
  have h4 : ell + t ≤ 3 / 5 := by linarith
  -- the limit of the right-hand side
  have hV := Cvs.Prolate.Hardy.TwoCarrierAveragedEnergy.tendsto_integral_waveV
  have hE := tendsto_errC hα h1 h2 h3
  set T := √(2 * (1 / 2 + t - 1 / 2)) + √(2 * (ell - (ell - t))) + √(2 * (ell + t - ell))
  have hT : T ^ 2 = 18 * t := by
    have e : T = 3 * √(2 * t) := by
      simp only [T]; rw [show 1 / 2 + t - 1 / 2 = t by ring, show ell - (ell - t) = t by ring,
        show ell + t - ell = t by ring]; ring
    rw [e, mul_pow, Real.sq_sqrt (by linarith)]; ring
  have hR : Tendsto (fun c => 2 * ((1 + η) * ∫ u in Ioi 1, ‖waveV c u ell‖ ^ 2) +
      2 * ((1 + 1 / η) * (4 * errC c (1 / 2 + t) (ell - t) (ell + t) ^ 2) * (5 / (2 * π ^ 2)))) atTop
      (𝓝 (2 * ((1 + η) * Cvs.Prolate.Hardy.TwoCarrierAveragedEnergy.limL) + 2 * ((1 + 1 / η) * (4 * T ^ 2) * (5 / (2 * π ^ 2))))) :=
    ((hV.const_mul (1 + η)).const_mul 2).add
      (((((hE.pow 2).const_mul 4).const_mul (1 + 1 / η)).mul_const (5 / (2 * π ^ 2))).const_mul 2)
  have hlt : 2 * ((1 + η) * Cvs.Prolate.Hardy.TwoCarrierAveragedEnergy.limL) + 2 * ((1 + 1 / η) * (4 * T ^ 2) * (5 / (2 * π ^ 2))) <
      avgEnergy ell + ε := by
    have e1 : 2 * ((1 + η) * Cvs.Prolate.Hardy.TwoCarrierAveragedEnergy.limL) = (1 + η) * avgEnergy ell := by rw [← Cvs.Prolate.Hardy.TwoCarrierAveragedEnergy.two_limL]; ring
    have e2 : 2 * ((1 + 1 / η) * (4 * T ^ 2) * (5 / (2 * π ^ 2))) = Kη * t := by
      rw [hT, hK]; field_simp; ring
    rw [e1, e2]
    have hηA : η * avgEnergy ell < ε / 2 := by
      rw [hηdef]
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith
    have hKt : Kη * t ≤ ε / 4 := by
      have := mul_le_mul_of_nonneg_left ht3 hK0.le
      rwa [mul_div_assoc', mul_comm Kη ε, mul_div_mul_comm, div_self hK0.ne', mul_one] at this
    nlinarith
  filter_upwards [hR.eventually (gt_mem_nhds hlt), eventually_gt_atTop 0] with c hc hc0
  exact (extS_le hc0 hη hα h1 h2 h3 h4).trans hc.le

/-- **The column bound along `c = 2πx`**, at the turning point `ℓ = 1/√3`. -/
theorem extS_hardyJ_le_nat {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℕ in atTop, extS (2 * π * x) (hardyJ (2 * π * x)) ≤ avgEnergy (1 / √3) + ε := by
  have h := extS_hardyJ_le hε
  have hc : Tendsto (fun x : ℕ => 2 * π * (x : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity)
  exact hc.eventually h

end Cvs.Prolate.Hardy.HardyColumnLimsupBound

end
