import Mathlib
import Cvs.Prolate.Hardy.AveragedColumnEnergy
import Cvs.Prolate.Hardy.CarrierBoundaryValues
import Cvs.Prolate.Hardy.ColumnTwoCarrierWave
import Cvs.Prolate.Hardy.ColumnWaveErrorBound
import Cvs.Prolate.Hardy.ColumnWaveSquareIntegral
import Cvs.Prolate.Hardy.CosineSynthesisPlancherel
import Cvs.Prolate.Hardy.ExtensionTraceColumnIntegral
import Cvs.Prolate.Hardy.ExteriorWeightAverages
import Cvs.Prolate.Hardy.LipCrossPhases
import Cvs.Prolate.Hardy.LipSymmetricPieces
import Cvs.Prolate.Hardy.OscillatingPartVanishes
import Cvs.Prolate.Hardy.SpectrumCosineHighpass
import Cvs.Prolate.Hardy.TwoCarrierWaveExplicit
import Cvs.Upstream.RiemannLebesgueNonStationary

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The two-carrier wave has the averaged energy `S_∞(ℓ)`, `ℓ = 1/√3`

On `I` the averaged part of `G_c` is `(P + Q)/4 + (P − Q)cos(2cx)/4`; on the lips it is `(P + Q)/2` plus the four
cross phases `2x`, `2(x − S)`, `S`, `2x − S`; the Riemann–Lebesgue lemmas give
`2∫_{u>1}‖V_u‖² → 2(∫_I ρ + 2∫_{½<|x|<ℓ} ρ) = S_∞(ℓ)`.
-/

noncomputable section

open Real Set MeasureTheory Filter Topology

namespace Cvs.Prolate.Hardy.TwoCarrierAveragedEnergy
open Cvs.ZeroCounting

open Cvs.Prolate.Hardy.CosineSynthesisPlancherel (cI)
open Cvs.Prolate.Hardy.CarrierBoundaryValues (sR)
open Cvs.Prolate.Hardy.LipSymmetricPieces (symS)
open Cvs.Prolate.Hardy.ColumnTwoCarrierWave (waveV)
open Cvs.Prolate.Hardy.ColumnWaveErrorBound (ell)
open Cvs.Prolate.Hardy.LipCrossPhases (phase)
open Cvs.Prolate.Hardy.ExteriorWeightAverages (pP qQ)
open Cvs.Prolate.Hardy.ColumnWaveSquareIntegral (xX yY)
open Cvs.Prolate.Hardy.OscillatingPartVanishes (mainF errF iOm)

/-- The averaged part on `I`. -/
def m1 (c x : ℝ) : ℝ := (Real.cos (c * x) ^ 2 * pP x + Real.sin (c * x) ^ 2 * qQ x) / 2

/-- The averaged part on the lips. -/
def m2 (c x : ℝ) : ℝ := ((Real.cos (c * x) - Real.cos (c * (x - sR x))) ^ 2 * pP x +
  (Real.sin (c * x) - Real.sin (c * (x - sR x))) ^ 2 * qQ x) / 2

theorem mainF_eq (c : ℝ) {x : ℝ} (hx : x ≠ -(1 / 2)) :
    mainF c x = cI.indicator (m1 c) x + (symS (1 / 2) ell).indicator (m2 c) x := by
  unfold mainF xX yY
  by_cases h1 : x ∈ cI
  · have h2 : x ∉ symS (1 / 2) ell := fun h => Cvs.Prolate.Hardy.TwoCarrierWaveExplicit.mem_symS_not_cI h hx h1
    simp only [indicator_of_mem h1, indicator_of_notMem h2, add_zero, m1]
  · by_cases h2 : x ∈ symS (1 / 2) ell
    · simp only [indicator_of_mem h2, indicator_of_notMem h1, zero_add, m2]
    · simp only [indicator_of_notMem h1, indicator_of_notMem h2, add_zero]; simp

theorem m1_eq (c x : ℝ) : m1 c x = (pP x + qQ x) / 4 + (pP x - qQ x) / 4 * Real.cos (2 * c * x) := by
  unfold m1
  have h1 : Real.cos (c * x) ^ 2 = (1 + Real.cos (2 * c * x)) / 2 := by
    rw [show 2 * c * x = 2 * (c * x) by ring, Real.cos_two_mul]; ring
  have h2 : Real.sin (c * x) ^ 2 = (1 - Real.cos (2 * c * x)) / 2 := by
    rw [show 2 * c * x = 2 * (c * x) by ring, Real.cos_two_mul, ← Real.sin_sq_add_cos_sq (c * x)]; ring
  rw [h1, h2]; ring

theorem m2_eq (c x : ℝ) : m2 c x = (pP x + qQ x) / 2 + (pP x - qQ x) / 4 * Real.cos (c * phase 0 x) +
    (pP x - qQ x) / 4 * Real.cos (c * phase 1 x) - (pP x + qQ x) / 2 * Real.cos (c * phase 2 x) -
    (pP x - qQ x) / 2 * Real.cos (c * phase 3 x) := by
  unfold m2
  simp only [phase]
  set a := c * x
  set b := c * (x - sR x)
  have e0 : c * (2 * x) = 2 * a := by simp only [a]; ring
  have e1 : c * (2 * (x - sR x)) = 2 * b := by simp only [b]; ring
  have e2 : c * sR x = a - b := by simp only [a, b]; ring
  have e3 : c * (2 * x - sR x) = a + b := by simp only [a, b]; ring
  rw [e0, e1, e2, e3, Real.cos_two_mul, Real.cos_two_mul, Real.cos_sub, Real.cos_add]
  have ha : Real.sin a ^ 2 = 1 - Real.cos a ^ 2 := by linarith [Real.sin_sq_add_cos_sq a]
  have hb : Real.sin b ^ 2 = 1 - Real.cos b ^ 2 := by linarith [Real.sin_sq_add_cos_sq b]
  rw [show (Real.sin a - Real.sin b) ^ 2 = Real.sin a ^ 2 + Real.sin b ^ 2 - 2 * Real.sin a * Real.sin b by ring,
    ha, hb]
  ring

theorem integrableOn_K {s : Set ℝ} (hs : ∀ x ∈ s, |x| ≤ ell) (hsm : MeasurableSet s) {g : ℝ → ℝ}
    (hg : AEStronglyMeasurable g volume) (hb : ∀ x, |x| ≤ ell → |g x| ≤ 2 * iOm) {k : ℝ → ℝ}
    (hk : Continuous k) (hk1 : ∀ x, |k x| ≤ 1) : IntegrableOn (fun x => g x * k x) s := by
  have hK : volume s ≠ ⊤ := by
    refine ne_top_of_le_ne_top (measure_Icc_lt_top (a := -ell) (b := ell)).ne (measure_mono fun x hx => ?_)
    exact abs_le.1 (hs x hx)
  refine (integrableOn_const (C := 2 * iOm) hK).mono' (hg.mul hk.aestronglyMeasurable).restrict ?_
  filter_upwards [ae_restrict_mem hsm] with x hx
  rw [Real.norm_eq_abs, abs_mul]
  have h1 := hb x (hs x hx)
  have h2 := hk1 x
  have : 0 ≤ 2 * iOm := (abs_nonneg _).trans h1
  nlinarith [abs_nonneg (g x), abs_nonneg (k x)]

theorem pPqQ_bound (a b : ℝ) (ha : |a| ≤ 1) (hb : |b| ≤ 1) {x : ℝ} (hx : |x| ≤ ell) :
    |a * pP x + b * qQ x| ≤ 2 * iOm := by
  have h1 := Cvs.Prolate.Hardy.OscillatingPartVanishes.abs_pP_le hx
  have h2 := Cvs.Prolate.Hardy.OscillatingPartVanishes.abs_qQ_le hx
  calc |a * pP x + b * qQ x| ≤ |a| * |pP x| + |b| * |qQ x| := by
        rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ 1 * iOm + 1 * iOm := by
        have := abs_nonneg (pP x)
        have := abs_nonneg (qQ x)
        have := abs_nonneg a
        have := abs_nonneg b
        nlinarith
    _ = 2 * iOm := by ring

theorem aesm_comb (a b : ℝ) : AEStronglyMeasurable (fun x => a * pP x + b * qQ x) volume :=
  ((Cvs.Prolate.Hardy.OscillatingPartVanishes.sm_pP.const_mul a).add (Cvs.Prolate.Hardy.OscillatingPartVanishes.sm_qQ.const_mul b)).aestronglyMeasurable

theorem cI_abs {x : ℝ} (hx : x ∈ cI) : |x| ≤ ell := Cvs.Prolate.Hardy.ColumnWaveSquareIntegral.cI_subset hx

theorem symS_abs {x : ℝ} (hx : x ∈ symS (1 / 2) ell) : |x| ≤ ell := Cvs.Prolate.Hardy.ColumnWaveSquareIntegral.symS_subset hx

theorem int_on (s : Set ℝ) (hs : ∀ x ∈ s, |x| ≤ ell) (hsm : MeasurableSet s) (a b : ℝ) (ha : |a| ≤ 1)
    (hb : |b| ≤ 1) {k : ℝ → ℝ} (hk : Continuous k) (hk1 : ∀ x, |k x| ≤ 1) :
    IntegrableOn (fun x => (a * pP x + b * qQ x) * k x) s :=
  integrableOn_K hs hsm (aesm_comb a b) (fun _ hx => pPqQ_bound a b ha hb hx) hk hk1

theorem abs_quarter : |(1 / 4 : ℝ)| ≤ 1 := by norm_num [abs_of_pos]
theorem abs_neg_quarter : |(-(1 / 4) : ℝ)| ≤ 1 := by norm_num [abs_of_pos]
theorem abs_half : |(1 / 2 : ℝ)| ≤ 1 := by norm_num [abs_of_pos]
theorem abs_neg_half : |(-(1 / 2) : ℝ)| ≤ 1 := by norm_num [abs_of_pos]

theorem cont_phase (c : ℝ) (j : Fin 4) : Continuous fun x => Real.cos (c * phase j x) := by
  have := Cvs.Prolate.Hardy.CarrierBoundaryValues.continuous_sR
  fin_cases j <;> simp only [phase] <;> fun_prop

/-- The limit `L = ∫_I (P + Q)/4 + ∫_{lips} (P + Q)/2`. -/
def limL : ℝ := (∫ x in cI, (pP x + qQ x) / 4) + ∫ x in symS (1 / 2) ell, (pP x + qQ x) / 2

theorem tendsto_cI : Tendsto (fun c => ∫ x in cI, m1 c x) atTop (𝓝 (∫ x in cI, (pP x + qQ x) / 4)) := by
  have hI1 : IntegrableOn (fun x => (pP x + qQ x) / 4) cI := by
    have := int_on cI (fun x hx => cI_abs hx) measurableSet_Icc (1 / 4) (1 / 4) abs_quarter abs_quarter
      (k := fun _ => 1) continuous_const (fun _ => by simp)
    refine this.congr_fun (fun x _ => by ring) measurableSet_Icc
  have hI2 : IntegrableOn (fun x => (pP x - qQ x) / 4) cI := by
    have := int_on cI (fun x hx => cI_abs hx) measurableSet_Icc (1 / 4) (-(1 / 4)) abs_quarter abs_neg_quarter
      (k := fun _ => 1) continuous_const (fun _ => by simp)
    refine this.congr_fun (fun x _ => by ring) measurableSet_Icc
  have hosc := (Cvs.Upstream.RiemannLebesgueNonStationary.tendsto_integral_mul_cos ((integrable_indicator_iff measurableSet_Icc).2 hI2)).comp
    (tendsto_id.const_mul_atTop (show (0 : ℝ) < 2 by norm_num))
  have hint : ∀ c : ℝ, ∫ x in cI, m1 c x =
      (∫ x in cI, (pP x + qQ x) / 4) + ∫ x, cI.indicator (fun x => (pP x - qQ x) / 4) x * Real.cos ((2 * c) * x) := by
    intro c
    have hI3 : IntegrableOn (fun x => (pP x - qQ x) / 4 * Real.cos (2 * c * x)) cI := by
      have := int_on cI (fun x hx => cI_abs hx) measurableSet_Icc (1 / 4) (-(1 / 4)) abs_quarter abs_neg_quarter
        (k := fun x => Real.cos (2 * c * x)) (by fun_prop) (fun _ => abs_cos_le_one _)
      refine this.congr_fun (fun x _ => by ring) measurableSet_Icc
    rw [setIntegral_congr_fun measurableSet_Icc (fun x _ => m1_eq c x), integral_add hI1 hI3]
    congr 1
    rw [← integral_indicator measurableSet_Icc]
    congr 1; ext x
    by_cases hx : x ∈ cI
    · rw [indicator_of_mem hx, indicator_of_mem hx]
    · rw [indicator_of_notMem hx, indicator_of_notMem hx, zero_mul]
  simp_rw [hint]
  have h2 : Tendsto (fun c : ℝ => (∫ x in cI, (pP x + qQ x) / 4) +
      ∫ x, cI.indicator (fun x => (pP x - qQ x) / 4) x * Real.cos ((2 * c) * x)) atTop
      (𝓝 ((∫ x in cI, (pP x + qQ x) / 4) + 0)) := tendsto_const_nhds.add hosc
  rw [add_zero] at h2
  exact h2

theorem tendsto_lips :
    Tendsto (fun c => ∫ x in symS (1 / 2) ell, m2 c x) atTop
      (𝓝 (∫ x in symS (1 / 2) ell, (pP x + qQ x) / 2)) := by
  set S := symS (1 / 2) ell
  have hSm : MeasurableSet S := Cvs.Prolate.Hardy.LipSymmetricPieces.measurableSet_symS _ _
  have hSa : ∀ x ∈ S, |x| ≤ ell := fun x hx => symS_abs hx
  have gP : IntegrableOn (fun x => (pP x + qQ x) / 2) S := by
    have := int_on S hSa hSm (1 / 2) (1 / 2) abs_half abs_half (k := fun _ => 1) continuous_const (fun _ => by simp)
    exact this.congr_fun (fun x _ => by ring) hSm
  have gM4 : IntegrableOn (fun x => (pP x - qQ x) / 4) S := by
    have := int_on S hSa hSm (1 / 4) (-(1 / 4)) abs_quarter abs_neg_quarter (k := fun _ => 1) continuous_const
      (fun _ => by simp)
    exact this.congr_fun (fun x _ => by ring) hSm
  have gM2 : IntegrableOn (fun x => (pP x - qQ x) / 2) S := by
    have := int_on S hSa hSm (1 / 2) (-(1 / 2)) abs_half abs_neg_half (k := fun _ => 1) continuous_const
      (fun _ => by simp)
    exact this.congr_fun (fun x _ => by ring) hSm
  have io : ∀ (c : ℝ) (j : Fin 4) (a b : ℝ), |a| ≤ 1 → |b| ≤ 1 →
      IntegrableOn (fun x => (a * pP x + b * qQ x) * Real.cos (c * phase j x)) S :=
    fun c j a b ha hb => int_on S hSa hSm a b ha hb (cont_phase c j) (fun _ => abs_cos_le_one _)
  have hint : ∀ c : ℝ, ∫ x in S, m2 c x = (∫ x in S, (pP x + qQ x) / 2) +
      (∫ x in S, (pP x - qQ x) / 4 * Real.cos (c * phase 0 x)) +
      (∫ x in S, (pP x - qQ x) / 4 * Real.cos (c * phase 1 x)) -
      (∫ x in S, (pP x + qQ x) / 2 * Real.cos (c * phase 2 x)) -
      (∫ x in S, (pP x - qQ x) / 2 * Real.cos (c * phase 3 x)) := by
    intro c
    have i0 := (io c 0 (1 / 4) (-(1 / 4)) abs_quarter abs_neg_quarter).congr_fun
      (g := fun x => (pP x - qQ x) / 4 * Real.cos (c * phase 0 x)) (fun x _ => by ring) hSm
    have i1 := (io c 1 (1 / 4) (-(1 / 4)) abs_quarter abs_neg_quarter).congr_fun
      (g := fun x => (pP x - qQ x) / 4 * Real.cos (c * phase 1 x)) (fun x _ => by ring) hSm
    have i2 := (io c 2 (1 / 2) (1 / 2) abs_half abs_half).congr_fun
      (g := fun x => (pP x + qQ x) / 2 * Real.cos (c * phase 2 x)) (fun x _ => by ring) hSm
    have i3 := (io c 3 (1 / 2) (-(1 / 2)) abs_half abs_neg_half).congr_fun
      (g := fun x => (pP x - qQ x) / 2 * Real.cos (c * phase 3 x)) (fun x _ => by ring) hSm
    rw [setIntegral_congr_fun hSm (fun x _ => m2_eq c x), integral_sub ?h1 i3,
      integral_sub ?h2 i2, integral_add ?h3 i1, integral_add gP i0]
    case h1 => exact ((gP.add i0).add i1).sub i2
    case h2 => exact (gP.add i0).add i1
    case h3 => exact gP.add i0
  have l0 := (Cvs.Prolate.Hardy.LipCrossPhases.tendsto_lips 0 gM4).1
  have l1 := (Cvs.Prolate.Hardy.LipCrossPhases.tendsto_lips 1 gM4).1
  have l2 := (Cvs.Prolate.Hardy.LipCrossPhases.tendsto_lips 2 gP).1
  have l3 := (Cvs.Prolate.Hardy.LipCrossPhases.tendsto_lips 3 gM2).1
  simp_rw [hint]
  have h := ((((tendsto_const_nhds (x := ∫ x in S, (pP x + qQ x) / 2)).add l0).add l1).sub l2).sub l3
  simp only [add_zero, sub_zero] at h
  exact h

theorem integrableOn_m1 (c : ℝ) : IntegrableOn (m1 c) cI := by
  have := int_on cI (fun x hx => cI_abs hx) measurableSet_Icc (1 / 4) (1 / 4) abs_quarter abs_quarter
    (k := fun _ => 1) continuous_const (fun _ => by simp)
  have h2 := int_on cI (fun x hx => cI_abs hx) measurableSet_Icc (1 / 4) (-(1 / 4)) abs_quarter
    abs_neg_quarter (k := fun x => Real.cos (2 * c * x)) (by fun_prop) (fun _ => abs_cos_le_one _)
  exact (this.add h2).congr_fun (fun x _ => by simp only [Pi.add_apply]; rw [m1_eq]; ring) measurableSet_Icc

theorem integrableOn_m2 (c : ℝ) : IntegrableOn (m2 c) (symS (1 / 2) ell) := by
  have hSm : MeasurableSet (symS (1 / 2) ell) := Cvs.Prolate.Hardy.LipSymmetricPieces.measurableSet_symS _ _
  have hSa : ∀ x ∈ symS (1 / 2) ell, |x| ≤ ell := fun x hx => symS_abs hx
  have g0 := int_on _ hSa hSm (1 / 2) (1 / 2) abs_half abs_half (k := fun _ => 1) continuous_const
    (fun _ => by simp)
  have g1 := int_on _ hSa hSm (1 / 4) (-(1 / 4)) abs_quarter abs_neg_quarter (cont_phase c 0)
    (fun _ => abs_cos_le_one _)
  have g2 := int_on _ hSa hSm (1 / 4) (-(1 / 4)) abs_quarter abs_neg_quarter (cont_phase c 1)
    (fun _ => abs_cos_le_one _)
  have g3 := int_on _ hSa hSm (1 / 2) (1 / 2) abs_half abs_half (cont_phase c 2)
    (fun _ => abs_cos_le_one _)
  have g4 := int_on _ hSa hSm (1 / 2) (-(1 / 2)) abs_half abs_neg_half (cont_phase c 3)
    (fun _ => abs_cos_le_one _)
  exact ((((g0.add g1).add g2).sub g3).sub g4).congr_fun
    (fun x _ => by simp only [Pi.add_apply, Pi.sub_apply]; rw [m2_eq]; ring) hSm

theorem mainF_ae (c : ℝ) : (fun x => mainF c x) =ᵐ[volume]
    fun x => cI.indicator (m1 c) x + (symS (1 / 2) ell).indicator (m2 c) x := by
  filter_upwards [Cvs.Prolate.Hardy.SpectrumCosineHighpass.ae_ne (-(1 / 2))] with x hx using mainF_eq c hx

theorem integrable_mainF (c : ℝ) : Integrable (mainF c) :=
  (((integrable_indicator_iff measurableSet_Icc).2 (integrableOn_m1 c)).add
    ((integrable_indicator_iff (Cvs.Prolate.Hardy.LipSymmetricPieces.measurableSet_symS _ _)).2 (integrableOn_m2 c))).congr (mainF_ae c).symm

theorem integrable_errF (c : ℝ) : Integrable (errF c) := by
  have hbound : Integrable (fun x => 27 / 2 * iOm * (Icc (-ell) ell).indicator (fun _ => (1 : ℝ)) x) :=
    ((integrable_indicator_iff measurableSet_Icc).2
      (integrableOn_const (C := (1 : ℝ)) (s := Icc (-ell) ell) (μ := volume) measure_Icc_lt_top.ne)).const_mul _
  refine hbound.mono' ?_ (Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs]; exact Cvs.Prolate.Hardy.OscillatingPartVanishes.abs_errF_le c x)
  unfold errF
  have hX := Cvs.Prolate.Hardy.ColumnWaveSquareIntegral.measurable_xX c
  have hY := Cvs.Prolate.Hardy.ColumnWaveSquareIntegral.measurable_yY c
  exact (((((hX.pow_const 2).neg.mul (Cvs.Prolate.Hardy.OscillatingPartVanishes.sm_iA c).measurable).add
    ((hY.pow_const 2).mul (Cvs.Prolate.Hardy.OscillatingPartVanishes.sm_iB c).measurable)).sub
      ((hX.mul hY).mul (Cvs.Prolate.Hardy.OscillatingPartVanishes.sm_iD c).measurable)).div_const 2).aestronglyMeasurable

theorem tendsto_integral_mainF : Tendsto (fun c => ∫ x, mainF c x) atTop (𝓝 limL) := by
  have hm : ∀ c : ℝ, ∫ x, mainF c x = (∫ x in cI, m1 c x) + ∫ x in symS (1 / 2) ell, m2 c x := by
    intro c
    have hSm : MeasurableSet (symS (1 / 2) ell) := Cvs.Prolate.Hardy.LipSymmetricPieces.measurableSet_symS _ _
    rw [integral_congr_ae (mainF_ae c)]
    rw [integral_add ((integrable_indicator_iff measurableSet_Icc).2 (integrableOn_m1 c))
      ((integrable_indicator_iff hSm).2 (integrableOn_m2 c)), integral_indicator measurableSet_Icc,
      integral_indicator hSm]
  simp_rw [hm]
  exact tendsto_cI.add tendsto_lips

/-- **The two-carrier limit**: `∫_{u>1}‖V_u‖² → L`. -/
theorem tendsto_integral_waveV :
    Tendsto (fun c => ∫ u in Ioi 1, ‖waveV c u ell‖ ^ 2) atTop (𝓝 limL) := by
  have h := tendsto_integral_mainF.add Cvs.Prolate.Hardy.OscillatingPartVanishes.tendsto_integral_errF
  rw [add_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with c hc
  rw [Cvs.Prolate.Hardy.ColumnWaveSquareIntegral.integral_norm_waveV_sq hc, ← integral_add (integrable_mainF c) (integrable_errF c)]
  rfl

/-- `2L = S_∞(ℓ)`. -/
theorem two_limL : 2 * limL = Cvs.Prolate.Hardy.AveragedColumnEnergy.avgEnergy ell := by
  have hl := Cvs.Prolate.Hardy.ColumnWaveErrorBound.half_lt_ell
  have hl1 := Cvs.Prolate.Hardy.ExteriorWeightAverages.ell_lt_one
  have hrho : ∀ {s : Set ℝ}, (∀ x ∈ s, |x| ≤ ell) → ∀ k : ℝ, ∀ x ∈ s, (pP x + qQ x) / k = 4 / k *
      Cvs.Prolate.Hardy.AveragedColumnEnergy.colDensity x := fun hs k x hx => by rw [Cvs.Prolate.Hardy.ExteriorWeightAverages.pP_add_qQ (hs x hx)]; ring
  unfold limL Cvs.Prolate.Hardy.AveragedColumnEnergy.avgEnergy
  rw [setIntegral_congr_fun measurableSet_Icc (hrho (fun x hx => cI_abs hx) 4),
    setIntegral_congr_fun (Cvs.Prolate.Hardy.LipSymmetricPieces.measurableSet_symS _ _) (hrho (fun x hx => symS_abs hx) 2),
    integral_const_mul, integral_const_mul]
  have hcont : ContinuousOn Cvs.Prolate.Hardy.AveragedColumnEnergy.colDensity (Icc (-ell) ell) := by
    have : ∀ x ∈ Icc (-ell) ell, Cvs.Prolate.Hardy.AveragedColumnEnergy.colDensity x = 1 / (4 * π ^ 2) * (1 / (1 - x ^ 2)) := fun x hx =>
      Cvs.Prolate.Hardy.AveragedColumnEnergy.colDensity_eq (by rw [abs_lt]; constructor <;> linarith [hx.1, hx.2])
    refine ContinuousOn.congr ?_ this
    have hd : ContinuousOn (fun x : ℝ => 1 - x ^ 2) (Icc (-ell) ell) := by fun_prop
    refine continuousOn_const.mul (continuousOn_const.div₀ hd fun x hx => ?_)
    have : x ^ 2 < 1 := by nlinarith [hx.1, hx.2]
    exact (by linarith : (0:ℝ) < 1 - x ^ 2).ne'
  have hint : ∀ a b : ℝ, -ell ≤ a → b ≤ ell → IntegrableOn Cvs.Prolate.Hardy.AveragedColumnEnergy.colDensity (Ioc a b) := fun a b ha hb =>
    ((hcont.mono (Icc_subset_Icc ha hb)).integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  have e1 : ∫ x in cI, Cvs.Prolate.Hardy.AveragedColumnEnergy.colDensity x = ∫ x in (-(1 / 2) : ℝ)..(1 / 2), Cvs.Prolate.Hardy.AveragedColumnEnergy.colDensity x := by
    rw [intervalIntegral.integral_of_le (by norm_num)]
    exact setIntegral_congr_set (Ioc_ae_eq_Icc.symm.trans (by
      rw [show (-1 / 2 : ℝ) = -(1 / 2) by norm_num]))
  have e2 : ∫ x in symS (1 / 2) ell, Cvs.Prolate.Hardy.AveragedColumnEnergy.colDensity x =
      (∫ x in (1 / 2 : ℝ)..ell, Cvs.Prolate.Hardy.AveragedColumnEnergy.colDensity x) + ∫ x in -ell..(-(1 / 2)), Cvs.Prolate.Hardy.AveragedColumnEnergy.colDensity x := by
    rw [intervalIntegral.integral_of_le hl.le, intervalIntegral.integral_of_le (by linarith)]
    unfold Cvs.Prolate.Hardy.LipSymmetricPieces.symS
    exact setIntegral_union (Cvs.Prolate.Hardy.LipSymmetricPieces.disjoint_sides (by norm_num)) measurableSet_Ioc (hint _ _ (by linarith) le_rfl)
      (hint _ _ le_rfl (by linarith))
  rw [e1, e2]
  ring

end Cvs.Prolate.Hardy.TwoCarrierAveragedEnergy

end
