import Mathlib
import Cvs.Prolate.EdgeCentreSign
import Cvs.Prolate.LiouvilleGreen.AdiabaticStretchBounds
import Cvs.Prolate.LiouvilleGreen.CoulombLayerExplicit
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.LiouvilleGreen.RegularSolutionNodeLaw
import Cvs.Prolate.RegularSolutionEdge
import Cvs.Prolate.TopRungDepthBound

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The Airy layer below the Coulomb zone: `∫_{t₂}^1 y² ≤ C_A G(t₂)/c` at `q(t₂) = cX`

For `σ < c²`, `b = (c² − σ)/c` and `t₂ < t* = √(σ/c²)` with `q(t₂) = cX`: `f = pqy² + U²` decreases on `[t₂, t*]`,
so `U² ≤ a₂G₂` and `|y| ≤ Y₁ = √(G₂/a₂)(1 + R)`, `R = (t* − t₂)a₂c/b`; beyond `t*`, `y ≥ 1` decreases and
`∫_{t*}^1 (c²t² − σ)y² ≤ y(t*)U(t*)`, so with `8 ≤ X ≤ b`, `X³ ≤ K₃b` the layer costs `(2(1 + R₀)² + (1 + R₀)/4)G₂/c`.
-/

noncomputable section

open Real Set Filter Topology MeasureTheory intervalIntegral
open Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval (pP)
open Cvs.Prolate.RegularSolutionEdge (regSol regU regV sqC continuousOn_regSol hasDerivAt_regSol hasDerivAt_regU pP_mul_regV regSol_one)
open Cvs.Prolate.TopRungDepthBound (af qf wf af_pos af_sq sqC_apply)
open Cvs.Prolate.LiouvilleGreen.AdiabaticStretchBounds (energyAt qf_eq sq_le_energyAt_div LayerBound)
open Cvs.Prolate.LiouvilleGreen.CoulombLayerExplicit (soninF soninG hasDerivAt_soninF regU_one)

namespace Cvs.Prolate.LiouvilleGreen.AiryLayerBelowCoulomb

variable {c σ : ℝ}

/-- `f = a·G` wherever `t² < 1` and `q(t) > 0`. -/
theorem soninF_eq_mul {t : ℝ} (hc : c ≠ 0) (ht : t ^ 2 < 1) (hq : 0 < qf c ((c ^ 2 - σ) / c) t) :
    soninF c σ t = af c ((c ^ 2 - σ) / c) t * energyAt c σ t := by
  have ha := af_pos ht hq
  have ha2 := af_sq ht hq
  rw [qf_eq hc] at ha2
  have hE : energyAt c σ t = af c ((c ^ 2 - σ) / c) t * regSol (sqC c) σ t ^ 2 +
      regU (sqC c) σ t ^ 2 / af c ((c ^ 2 - σ) / c) t := rfl
  rw [hE]; unfold soninF
  rw [mul_add, ← mul_assoc, ← sq, ha2, mul_div_cancel₀ _ ha.ne']

/-- Beyond the turning point `t* = √(σ/c²)` (`0 < σ`): `y ≥ 1`. -/
theorem one_le_forbidden (hc : 0 < c) {t : ℝ} (ht : t ∈ Icc √(σ / c ^ 2) 1) : 1 ≤ regSol (sqC c) σ t := by
  have h := Cvs.Prolate.LiouvilleGreen.RegularSolutionNodeLaw.one_le_regSol (c := c) (τ := σ / c ^ 2) t ht
  rwa [show c ^ 2 * (σ / c ^ 2) = σ by field_simp] at h

/-- Beyond the turning point: `U ≥ 0`. -/
theorem regU_nonneg_forbidden (hc : 0 < c) (hσ0 : 0 < σ) {t : ℝ} (ht : t ∈ Icc √(σ / c ^ 2) 1) :
    0 ≤ regU (sqC c) σ t := by
  have hc2 : 0 < c ^ 2 := by positivity
  have hts2 : √(σ / c ^ 2) ^ 2 = σ / c ^ 2 := Real.sq_sqrt (div_pos hσ0 hc2).le
  have hts0 := Real.sqrt_nonneg (σ / c ^ 2)
  unfold regU
  rw [intervalIntegral.integral_symm, neg_neg]
  refine intervalIntegral.integral_nonneg ht.2 fun s hs => ?_
  rw [sqC_apply]
  have h1 : σ ≤ c ^ 2 * s ^ 2 := by
    have : σ / c ^ 2 ≤ s ^ 2 := by rw [← hts2]; nlinarith [hs.1, ht.1]
    rwa [div_le_iff₀ hc2, mul_comm] at this
  exact mul_nonneg (by linarith) (by linarith [one_le_forbidden hc ⟨ht.1.trans hs.1, hs.2⟩])

/-- Beyond the turning point: `y` decreases. -/
theorem antitoneOn_forbidden (hc : 0 < c) (hσ0 : 0 < σ) :
    AntitoneOn (regSol (sqC c) σ) (Icc √(σ / c ^ 2) 1) := by
  have hts0 := Real.sqrt_nonneg (σ / c ^ 2)
  refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := regV (sqC c) σ) (convex_Icc _ 1)
    ((continuousOn_regSol (sqC c) σ).mono fun x hx => show (-1 : ℝ) < x by linarith [hx.1])
    (fun x hx => ?_) (fun x hx => ?_)
  · rw [interior_Icc] at hx
    exact (hasDerivAt_regSol (sqC c) σ (by linarith [hx.1])).hasDerivWithinAt
  · rw [interior_Icc] at hx
    have hx1 : -1 < x := by linarith [hx.1]
    have hpv := pP_mul_regV (sqC c) σ hx1
    unfold pP at hpv
    have hp : x ^ 2 - 1 < 0 := by nlinarith [hx.1, hx.2]
    have hU := regU_nonneg_forbidden hc hσ0 ⟨hx.1.le, hx.2.le⟩
    nlinarith

theorem continuousAt_regV {t : ℝ} (ht : -1 < t) : ContinuousAt (regV (sqC c) σ) t := by
  rcases eq_or_ne t 1 with h | h
  · rw [h]; exact (Cvs.Prolate.RegularSolutionEdge.hasDerivAt_regV_one (sqC c) σ (Cvs.Prolate.EdgeCentreSign.hasDerivAt_sqC c 1)).continuousAt
  · exact (Cvs.Prolate.RegularSolutionEdge.hasDerivAt_regV_of_ne (sqC c) σ ht h).continuousAt

/-- **The forbidden virial**: `∫_{t*}^1 (c²t² − σ)y² ≤ y(t*)U(t*)`. -/
theorem integral_forbidden_le (hc : 0 < c) (hσ0 : 0 < σ) (hσ : σ < c ^ 2) :
    ∫ t in √(σ / c ^ 2)..1, (c ^ 2 * t ^ 2 - σ) * regSol (sqC c) σ t ^ 2 ≤
      regSol (sqC c) σ √(σ / c ^ 2) * regU (sqC c) σ √(σ / c ^ 2) := by
  set ts := √(σ / c ^ 2)
  have hc2 : 0 < c ^ 2 := by positivity
  have hts1 : ts ≤ 1 := by
    rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt (by rw [div_le_one hc2]; linarith)
  have hts0 : 0 ≤ ts := Real.sqrt_nonneg _
  set F' : ℝ → ℝ := fun t => regV (sqC c) σ t * regU (sqC c) σ t + (σ - c ^ 2 * t ^ 2) * regSol (sqC c) σ t ^ 2
  have hd : ∀ t ∈ uIcc ts 1, HasDerivAt (fun t => regSol (sqC c) σ t * regU (sqC c) σ t) (F' t) t := by
    intro t ht
    rw [uIcc_of_le hts1] at ht
    have ht1 : -1 < t := by linarith [ht.1]
    refine ((hasDerivAt_regSol (sqC c) σ ht1).mul (hasDerivAt_regU (sqC c) σ ht1)).congr_deriv ?_
    simp only [F', sqC_apply]; ring
  have hcF : ContinuousOn F' (uIcc ts 1) := by
    rw [uIcc_of_le hts1]
    have h1 : ∀ t ∈ Icc ts 1, (-1 : ℝ) < t := fun t ht => by linarith [ht.1]
    have hy : ContinuousOn (regSol (sqC c) σ) (Icc ts 1) := (continuousOn_regSol (sqC c) σ).mono h1
    have hU : ContinuousOn (regU (sqC c) σ) (Icc ts 1) := fun t ht =>
      (hasDerivAt_regU (sqC c) σ (h1 t ht)).continuousAt.continuousWithinAt
    have hV : ContinuousOn (regV (sqC c) σ) (Icc ts 1) := fun t ht =>
      (continuousAt_regV (h1 t ht)).continuousWithinAt
    exact (hV.mul hU).add ((by fun_prop : Continuous fun t : ℝ => σ - c ^ 2 * t ^ 2).continuousOn.mul (hy.pow 2))
  have hFTC := integral_eq_sub_of_hasDerivAt hd hcF.intervalIntegrable
  rw [regU_one, mul_zero, zero_sub] at hFTC
  have hσ0' : 0 < σ := hσ0
  have hpt : ∀ t ∈ Icc ts 1, (c ^ 2 * t ^ 2 - σ) * regSol (sqC c) σ t ^ 2 ≤ -F' t := by
    intro t ht
    have hU := regU_nonneg_forbidden hc hσ0 ht
    have hVU : regV (sqC c) σ t * regU (sqC c) σ t ≤ 0 := by
      rcases eq_or_lt_of_le ht.2 with h | h
      · rw [h, regU_one, mul_zero]
      · have hpv := pP_mul_regV (sqC c) σ (show (-1 : ℝ) < t by linarith [ht.1])
        unfold pP at hpv
        have hp : t ^ 2 - 1 < 0 := by nlinarith [ht.1]
        have hV : regV (sqC c) σ t ≤ 0 := by nlinarith
        exact mul_nonpos_of_nonpos_of_nonneg hV hU
    simp only [F']; linarith
  have hyc : ContinuousOn (fun t => (c ^ 2 * t ^ 2 - σ) * regSol (sqC c) σ t ^ 2) (Icc ts 1) :=
    (by fun_prop : Continuous fun t : ℝ => c ^ 2 * t ^ 2 - σ).continuousOn.mul
      (((continuousOn_regSol (sqC c) σ).mono fun t (ht : t ∈ Icc ts 1) => show (-1 : ℝ) < t by linarith [ht.1]).pow 2)
  have hyi : IntervalIntegrable (fun t => (c ^ 2 * t ^ 2 - σ) * regSol (sqC c) σ t ^ 2) volume ts 1 := by
    rw [← uIcc_of_le hts1] at hyc; exact hyc.intervalIntegrable
  have hmono := integral_mono_on hts1 hyi (hcF.intervalIntegrable (μ := volume)).neg hpt
  simp only [Pi.neg_apply, intervalIntegral.integral_neg] at hmono
  rw [hFTC] at hmono
  linarith

/-- **The flux bounds `U` on the allowed side**: for `σ < c²`, `½ ≤ t₂ ≤ t ≤ t* = √(σ/c²)` and `q(t₂) > 0`,
`U(t)² ≤ f(t₂)`. -/
theorem regU_sq_le_soninF (hc : 0 < c) (hσ0 : 0 < σ) (hσ : σ < c ^ 2) {t₂ t : ℝ} (h2 : 1 / 2 ≤ t₂)
    (ht : t ∈ Icc t₂ √(σ / c ^ 2)) : regU (sqC c) σ t ^ 2 ≤ soninF c σ t₂ := by
  set ts := √(σ / c ^ 2)
  have hc2 : 0 < c ^ 2 := by positivity
  have hts2 : ts ^ 2 = σ / c ^ 2 := Real.sq_sqrt (div_pos hσ0 hc2).le
  have hts1 : ts ≤ 1 := by
    rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt (by rw [div_le_one hc2]; linarith)
  have hσts : σ = c ^ 2 * ts ^ 2 := by rw [hts2]; field_simp
  have hanti : AntitoneOn (soninF c σ) (Icc t₂ ts) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := fun x => -(soninG c σ x * regSol (sqC c) σ x ^ 2))
      (convex_Icc t₂ ts)
      (fun x hx => (hasDerivAt_soninF (c := c) (σ := σ) (by linarith [hx.1])).continuousAt.continuousWithinAt)
      (fun x hx => ?_) (fun x hx => ?_)
    · rw [interior_Icc] at hx
      exact (hasDerivAt_soninF (by linarith [hx.1])).hasDerivWithinAt
    · rw [interior_Icc] at hx
      have hx0 : 0 ≤ x := by linarith [hx.1]
      have : x ^ 2 ≤ ts ^ 2 := by nlinarith [hx.2]
      have hg : 0 ≤ soninG c σ x := by
        unfold soninG
        have : 0 ≤ σ + c ^ 2 - 2 * c ^ 2 * x ^ 2 := by nlinarith
        positivity
      have := mul_nonneg hg (sq_nonneg (regSol (sqC c) σ x))
      linarith
  have h1 := hanti ⟨le_rfl, ht.1.trans ht.2⟩ ht ht.1
  have h0 : 0 ≤ (1 - t ^ 2) * (σ - c ^ 2 * t ^ 2) * regSol (sqC c) σ t ^ 2 := by
    have : t ^ 2 ≤ ts ^ 2 := by nlinarith [ht.1, ht.2]
    have : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
    have : 0 ≤ σ - c ^ 2 * t ^ 2 := by nlinarith
    have : 0 ≤ 1 - t ^ 2 := by linarith
    positivity
  unfold soninF at h1 ⊢
  linarith

/-- **The sup on the allowed side**: `|y(t)| ≤ √(G₂/a₂) + (t − t₂)√f(t₂)/(1 − σ/c²)` on `[t₂, t*]`. -/
theorem abs_regSol_le_allowed (hc : 0 < c) (hσ0 : 0 < σ) (hσ : σ < c ^ 2) {t₂ t : ℝ} (h2 : 1 / 2 ≤ t₂)
    (hq2 : 0 < qf c ((c ^ 2 - σ) / c) t₂) (h21 : t₂ ^ 2 < 1) (ht : t ∈ Icc t₂ √(σ / c ^ 2)) :
    |regSol (sqC c) σ t| ≤ √(energyAt c σ t₂ / af c ((c ^ 2 - σ) / c) t₂) +
      (t - t₂) * √(soninF c σ t₂) / (1 - σ / c ^ 2) := by
  set ts := √(σ / c ^ 2)
  have hc2 : 0 < c ^ 2 := by positivity
  have hts2 : ts ^ 2 = σ / c ^ 2 := Real.sq_sqrt (div_pos hσ0 hc2).le
  have hps : 0 < 1 - σ / c ^ 2 := by rw [sub_pos, div_lt_one hc2]; exact hσ
  have ha := af_pos h21 hq2
  have hy2 : |regSol (sqC c) σ t₂| ≤ √(energyAt c σ t₂ / af c ((c ^ 2 - σ) / c) t₂) :=
    Real.abs_le_sqrt (sq_le_energyAt_div ha)
  have hderiv : ∀ x ∈ Icc t₂ t, HasDerivWithinAt (regSol (sqC c) σ) (regV (sqC c) σ x) (Icc t₂ t) x :=
    fun x hx => (hasDerivAt_regSol (sqC c) σ (by linarith [hx.1])).hasDerivWithinAt
  have hbound : ∀ x ∈ Ico t₂ t, ‖regV (sqC c) σ x‖ ≤ √(soninF c σ t₂) / (1 - σ / c ^ 2) := by
    intro x hx
    have hxI : x ∈ Icc t₂ ts := ⟨hx.1, hx.2.le.trans ht.2⟩
    have hx0 : 0 ≤ x := by linarith [hx.1]
    have hxs : x ^ 2 ≤ σ / c ^ 2 := by rw [← hts2]; nlinarith [hxI.2]
    have hp : 1 - σ / c ^ 2 ≤ 1 - x ^ 2 := by linarith
    have hp0 : 0 < 1 - x ^ 2 := lt_of_lt_of_le hps hp
    have hpv := pP_mul_regV (sqC c) σ (show (-1 : ℝ) < x by linarith)
    unfold pP at hpv
    have hV : regV (sqC c) σ x = -regU (sqC c) σ x / (1 - x ^ 2) := by field_simp; linarith
    have hU : |regU (sqC c) σ x| ≤ √(soninF c σ t₂) :=
      Real.abs_le_sqrt (regU_sq_le_soninF hc hσ0 hσ h2 hxI)
    rw [Real.norm_eq_abs, hV, abs_div, abs_neg, abs_of_pos hp0]
    calc |regU (sqC c) σ x| / (1 - x ^ 2) ≤ √(soninF c σ t₂) / (1 - x ^ 2) :=
          div_le_div_of_nonneg_right hU hp0.le
      _ ≤ √(soninF c σ t₂) / (1 - σ / c ^ 2) := div_le_div_of_nonneg_left (Real.sqrt_nonneg _) hps hp
  have h := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound t ⟨ht.1, le_rfl⟩
  rw [Real.norm_eq_abs] at h
  have := abs_sub_abs_le_abs_sub (regSol (sqC c) σ t) (regSol (sqC c) σ t₂)
  have e : √(soninF c σ t₂) / (1 - σ / c ^ 2) * (t - t₂) = (t - t₂) * √(soninF c σ t₂) / (1 - σ / c ^ 2) := by
    ring
  linarith

/-- The Airy-layer constant `C_A(K₃) = 2(1 + √(2K₃))² + (1 + √(2K₃))/4`. -/
def airyConst (K₃ : ℝ) : ℝ := 2 * (1 + √(2 * K₃)) ^ 2 + (1 + √(2 * K₃)) / 4

set_option maxHeartbeats 4000000 in
/-- **The Airy layer**: for `σ < c²`, `b = (c² − σ)/c` and `X` with `8 ≤ X ≤ b`, `16(b + X) ≤ X³ ≤ K₃b` and
`c²/4 < σ − cX`, the point `t₂ = √((σ − cX)/c²)` has `|w(t₂)| ≤ 3/8` and `∫_{t₂}^1 y² ≤ C_A(K₃)G(t₂)/c`. -/
theorem airy_layer (hc : 0 < c) (hσ : σ < c ^ 2) {X K₃ : ℝ} (hX8 : 8 ≤ X) (hXb : X ≤ (c ^ 2 - σ) / c)
    (hXw : 16 * ((c ^ 2 - σ) / c + X) ≤ X ^ 3) (hK : X ^ 3 ≤ K₃ * ((c ^ 2 - σ) / c))
    (h2 : c ^ 2 / 4 < σ - c * X) :
    |wf c ((c ^ 2 - σ) / c) √((σ - c * X) / c ^ 2)| ≤ 3 / 8 ∧
      LayerBound c σ √((σ - c * X) / c ^ 2) (airyConst K₃ / c) := by
  set b := (c ^ 2 - σ) / c with hb
  set t₂ := √((σ - c * X) / c ^ 2)
  set ts := √(σ / c ^ 2)
  set y := regSol (sqC c) σ
  have hc2 : 0 < c ^ 2 := by positivity
  have hX0 : 0 < X := by linarith
  have hσ0 : 0 < σ := by nlinarith
  have hb0 : 0 < b := by rw [hb]; apply div_pos _ hc; linarith
  have hbc : c * b = c ^ 2 - σ := by rw [hb]; field_simp
  have ht22 : t₂ ^ 2 = (σ - c * X) / c ^ 2 := Real.sq_sqrt (div_pos (by linarith) hc2).le
  have hts2 : ts ^ 2 = σ / c ^ 2 := Real.sq_sqrt (div_pos hσ0 hc2).le
  have ht20 : 0 ≤ t₂ := Real.sqrt_nonneg _
  have hts0 : 0 ≤ ts := Real.sqrt_nonneg _
  have ht2h : 1 / 2 < t₂ := by
    have : (1 / 2 : ℝ) ^ 2 < t₂ ^ 2 := by rw [ht22, lt_div_iff₀ hc2]; linarith
    nlinarith
  have ht2s : t₂ < ts := by
    have : t₂ ^ 2 < ts ^ 2 := by rw [ht22, hts2]; exact div_lt_div_of_pos_right (by nlinarith) hc2
    nlinarith
  have hts1 : ts < 1 := by
    have : ts ^ 2 < 1 := by rw [hts2, div_lt_one hc2]; exact hσ
    nlinarith
  -- the data at `t₂`
  have hq2 : qf c b t₂ = c * X := by rw [hb, qf_eq hc.ne', ht22]; field_simp; ring
  have hq2p : 0 < qf c b t₂ := by rw [hq2]; positivity
  have h21 : t₂ ^ 2 < 1 := by nlinarith
  have hp2 : 1 - t₂ ^ 2 = (b + X) / c := by rw [ht22]; field_simp; linarith [hbc]
  have ha := af_pos h21 hq2p
  have ha2 : af c b t₂ ^ 2 = (b + X) * X := by
    rw [af_sq h21 hq2p, hp2, hq2]; field_simp
  set a := af c b t₂
  set G := energyAt c σ t₂
  have haX : X ≤ a := by
    have : X ^ 2 ≤ a ^ 2 := by rw [ha2]; nlinarith
    exact (pow_le_pow_iff_left₀ hX0.le ha.le two_ne_zero).mp this
  -- `|w(t₂)| ≤ ½`
  have hw : |wf c b t₂| ≤ 3 / 8 := by
    have hw0 : wf c b t₂ ≤ 0 := Cvs.Prolate.TopRungDepthBound.wf_nonpos ht20 h21 hq2p
    have hwe : wf c b t₂ = -(t₂ / a + c ^ 2 * t₂ * (1 - t₂ ^ 2) / (a * qf c b t₂)) := rfl
    rw [abs_of_nonpos hw0, hwe, neg_neg]
    have hp0 : 0 < 1 - t₂ ^ 2 := by linarith
    have h1 : t₂ / a ≤ 1 / 8 := by rw [div_le_div_iff₀ ha (by norm_num)]; nlinarith
    have h2' : c ^ 2 * t₂ * (1 - t₂ ^ 2) / (a * qf c b t₂) ≤ 1 / 4 := by
      rw [div_le_div_iff₀ (mul_pos ha hq2p) (by norm_num)]
      have hsq : (4 * (c ^ 2 * (1 - t₂ ^ 2))) ^ 2 ≤ (a * qf c b t₂) ^ 2 := by
        rw [mul_pow a (qf c b t₂) 2, ha2, hq2, hp2]
        have e1 : (4 * (c ^ 2 * ((b + X) / c))) ^ 2 = 16 * c ^ 2 * (b + X) ^ 2 := by field_simp; ring
        rw [e1]
        have : 16 * c ^ 2 * (b + X) ^ 2 ≤ (b + X) * (X * (16 * (b + X))) * c ^ 2 := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_left hXw (by positivity : (0 : ℝ) ≤ (b + X) * c ^ 2)]
      have h3 : 4 * (c ^ 2 * (1 - t₂ ^ 2)) ≤ a * qf c b t₂ :=
        (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp hsq
      have h4 : c ^ 2 * t₂ * (1 - t₂ ^ 2) ≤ c ^ 2 * (1 - t₂ ^ 2) := by
        have : t₂ ≤ 1 := by linarith
        nlinarith [mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ c ^ 2 * (1 - t₂ ^ 2))]
      linarith
    linarith
  refine ⟨hw, ?_⟩
  -- the gap `d = t* − t₂`
  set d := ts - t₂
  have hd0 : 0 < d := by simp only [d]; linarith
  have hdd : d * (ts + t₂) = X / c := by
    have : ts ^ 2 - t₂ ^ 2 = X / c := by rw [hts2, ht22]; field_simp; ring
    rw [← this]; simp only [d]; ring
  have hdX : d ≤ X / c := by rw [← hdd]; exact le_mul_of_one_le_right hd0.le (by linarith)
  have hdX' : X / c ≤ 2 * d := by rw [← hdd]; nlinarith
  -- `Y₁ = √(G/a)(1 + R)`
  have hfG : soninF c σ t₂ = a * G := soninF_eq_mul hc.ne' h21 hq2p
  have hG0 : 0 ≤ G := by
    have : 0 ≤ soninF c σ t₂ := by
      unfold soninF
      have : 0 ≤ (1 - t₂ ^ 2) * (σ - c ^ 2 * t₂ ^ 2) := by
        have h' : σ - c ^ 2 * t₂ ^ 2 = c * X := by rw [ht22]; field_simp; ring
        rw [h']; have : 0 ≤ 1 - t₂ ^ 2 := by linarith
        positivity
      positivity
    rw [hfG] at this; exact nonneg_of_mul_nonneg_right (by linarith) ha
  set s := √(G / a)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = G / a := Real.sq_sqrt (div_nonneg hG0 ha.le)
  have hsf : √(soninF c σ t₂) = a * s := by
    rw [hfG, show a * G = (a * s) ^ 2 by rw [mul_pow, hs2]; field_simp]
    exact Real.sqrt_sq (by positivity)
  have hps : 1 - σ / c ^ 2 = b / c := by rw [hb]; field_simp
  set R := d * a * c / b
  have hR0 : 0 ≤ R := by positivity
  have hRK : R ≤ √(2 * K₃) := by
    apply Real.le_sqrt_of_sq_le
    have h1 : R ≤ X * a / b := by
      simp only [R]; rw [div_le_div_iff₀ hb0 hb0]
      have := mul_le_mul_of_nonneg_right hdX (by positivity : (0 : ℝ) ≤ a * c)
      have e : X / c * (a * c) = X * a := by field_simp
      nlinarith
    have h2' : (X * a / b) ^ 2 ≤ 2 * K₃ := by
      rw [div_pow, mul_pow, ha2, div_le_iff₀ (by positivity)]
      have : X ^ 2 * ((b + X) * X) ≤ X ^ 3 * (2 * b) := by nlinarith
      nlinarith
    nlinarith
  have hY : ∀ t ∈ Icc t₂ ts, |y t| ≤ s * (1 + R) := by
    intro t ht
    have h := abs_regSol_le_allowed hc hσ0 hσ ht2h.le hq2p h21 ht
    rw [hsf, hps] at h
    have h3 : (t - t₂) * (a * s) / (b / c) ≤ s * R := by
      have : t - t₂ ≤ d := by simp only [d]; linarith [ht.2]
      rw [div_le_iff₀ (by positivity)]
      simp only [R]
      have e : s * (d * a * c / b) * (b / c) = d * (a * s) := by field_simp
      rw [e]
      exact mul_le_mul_of_nonneg_right this (by positivity)
    linarith
  -- the forbidden side
  have hyts : 1 ≤ y ts := one_le_forbidden hc ⟨le_rfl, hts1.le⟩
  have hYf : ∀ t ∈ Icc ts 1, |y t| ≤ s * (1 + R) := by
    intro t ht
    have h1 := one_le_forbidden hc ht
    have h2'' := antitoneOn_forbidden hc hσ0 ⟨le_rfl, hts1.le⟩ ht ht.1
    rw [abs_of_pos (by linarith)]
    have := hY ts ⟨ht2s.le, le_rfl⟩
    rw [abs_of_pos (by linarith)] at this
    linarith
  -- the integral
  set M := s * (1 + R)
  have hM0 : 0 ≤ M := by positivity
  have hsq : ∀ u v : ℝ, -1 < u → u ≤ v → (∀ t ∈ Icc u v, |y t| ≤ M) →
      ∫ t in u..v, y t ^ 2 ≤ (v - u) * M ^ 2 := by
    intro u v hu huv hb
    have hb' : ∀ t ∈ uIoc u v, ‖y t ^ 2‖ ≤ M ^ 2 := by
      intro t ht
      rw [uIoc_of_le huv] at ht
      rw [Real.norm_eq_abs, abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hb t ⟨ht.1.le, ht.2⟩) 2
    have h := norm_integral_le_of_norm_le_const hb'
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ v - u)] at h
    have := le_abs_self (∫ t in u..v, y t ^ 2)
    rw [Real.norm_eq_abs] at h
    linarith
  have hyi : ∀ u v : ℝ, -1 < u → -1 < v → IntervalIntegrable (fun t => y t ^ 2) volume u v := by
    intro u v hu hv
    exact (((continuousOn_regSol (sqC c) σ).mono fun t (ht : t ∈ uIcc u v) =>
      show (-1 : ℝ) < t from lt_of_lt_of_le (lt_min hu hv) ht.1).pow 2).intervalIntegrable
  have hI1 := hsq t₂ ts (by linarith) ht2s.le hY
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (hyi t₂ ts (by linarith) (by linarith))
    (hyi ts 1 (by linarith) (by norm_num))
  -- `U(t*) ≤ a s`
  have hU0 := regU_nonneg_forbidden hc hσ0 (σ := σ) (t := ts) ⟨le_rfl, hts1.le⟩
  have hUs : regU (sqC c) σ ts ≤ a * s := by
    rw [← hsf]; exact Real.le_sqrt_of_sq_le (regU_sq_le_soninF hc hσ0 hσ ht2h.le ⟨ht2s.le, le_rfl⟩)
  have hyts' : y ts ≤ M := by have := hY ts ⟨ht2s.le, le_rfl⟩; rwa [abs_of_pos (by linarith)] at this
  have hI2 : ∫ t in ts..1, y t ^ 2 ≤ d * M ^ 2 + M * (a * s) / (c ^ 2 * d) := by
    rcases le_or_gt 1 (ts + d) with h | h
    · have := hsq ts 1 (by linarith) hts1.le hYf
      have h3 : (1 - ts) * M ^ 2 ≤ d * M ^ 2 := mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
      have h4 : 0 ≤ M * (a * s) / (c ^ 2 * d) := by positivity
      linarith
    · set t₃ := ts + d
      have hs3 := intervalIntegral.integral_add_adjacent_intervals (hyi ts t₃ (by linarith) (by linarith))
        (hyi t₃ 1 (by linarith) (by norm_num))
      have hA := hsq ts t₃ (by linarith) (by linarith) fun t ht => hYf t ⟨ht.1, by linarith [ht.2]⟩
      have hvir := integral_forbidden_le hc hσ0 hσ
      have hqi : ∀ u v : ℝ, -1 < u → -1 < v →
          IntervalIntegrable (fun t => (c ^ 2 * t ^ 2 - σ) * y t ^ 2) volume u v := by
        intro u v hu hv
        exact ((by fun_prop : Continuous fun t : ℝ => c ^ 2 * t ^ 2 - σ).continuousOn.mul
          (((continuousOn_regSol (sqC c) σ).mono fun t (ht : t ∈ uIcc u v) =>
            show (-1 : ℝ) < t from lt_of_lt_of_le (lt_min hu hv) ht.1).pow 2)).intervalIntegrable
      have hq3 := intervalIntegral.integral_add_adjacent_intervals (hqi ts t₃ (by linarith) (by linarith))
        (hqi t₃ 1 (by linarith) (by norm_num))
      have hq0 : 0 ≤ ∫ t in ts..t₃, (c ^ 2 * t ^ 2 - σ) * y t ^ 2 := by
        refine intervalIntegral.integral_nonneg (by linarith) fun t ht => mul_nonneg ?_ (sq_nonneg _)
        have : ts ^ 2 ≤ t ^ 2 := by nlinarith [ht.1]
        rw [hts2] at this
        have := mul_le_mul_of_nonneg_left this hc2.le
        rw [mul_div_cancel₀ _ hc2.ne'] at this
        linarith
      have hB : c ^ 2 * d * ∫ t in t₃..1, y t ^ 2 ≤ ∫ t in t₃..1, (c ^ 2 * t ^ 2 - σ) * y t ^ 2 := by
        rw [← intervalIntegral.integral_const_mul]
        refine intervalIntegral.integral_mono_on h.le ((hyi t₃ 1 (by linarith) (by norm_num)).const_mul _)
          (hqi t₃ 1 (by linarith) (by norm_num)) fun t ht => ?_
        have h5 : c ^ 2 * d ≤ c ^ 2 * t ^ 2 - σ := by
          have h8 : (ts + d) ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ (by positivity) ht.1 2
          have h9 : 2 * ts * d + d ^ 2 ≤ t ^ 2 - ts ^ 2 := by nlinarith only [h8]
          have hts' : 1 / 2 ≤ ts := by linarith only [ht2h, ht2s]
          have h6 : d ≤ 2 * ts * d + d ^ 2 := by nlinarith only [hd0, hts']
          have h7 : σ = c ^ 2 * ts ^ 2 := by rw [hts2]; field_simp
          have h10 := mul_le_mul_of_nonneg_left (h6.trans h9) hc2.le
          rw [mul_sub] at h10
          rw [h7]; linarith only [h10]
        exact mul_le_mul_of_nonneg_right h5 (sq_nonneg _)
      have hC : ∫ t in t₃..1, y t ^ 2 ≤ M * (a * s) / (c ^ 2 * d) := by
        rw [le_div_iff₀ (by positivity), mul_comm]
        have : y ts * regU (sqC c) σ ts ≤ M * (a * s) :=
          mul_le_mul hyts' hUs hU0 hM0
        linarith only [hB, hvir, hq3, hq0, this]
      linarith only [hs3, hA, hC]
  -- the constants
  unfold LayerBound
  have hdc : d * M ^ 2 ≤ (1 + R) ^ 2 * G / c := by
    have e : d * M ^ 2 = d / a * G * (1 + R) ^ 2 := by
      simp only [M]; rw [mul_pow, hs2]; field_simp
    rw [e]
    have : d / a ≤ 1 / c := by
      rw [div_le_div_iff₀ ha hc]; have := mul_le_mul_of_nonneg_left hdX hc.le
      rw [mul_div_cancel₀ _ hc.ne'] at this; linarith
    have := mul_le_mul_of_nonneg_right this (by positivity : (0 : ℝ) ≤ G * (1 + R) ^ 2)
    calc d / a * G * (1 + R) ^ 2 = d / a * (G * (1 + R) ^ 2) := by ring
      _ ≤ 1 / c * (G * (1 + R) ^ 2) := this
      _ = (1 + R) ^ 2 * G / c := by ring
  have hdc2 : M * (a * s) / (c ^ 2 * d) ≤ (1 + R) * G / (4 * c) := by
    have e : M * (a * s) = (1 + R) * G := by
      simp only [M]; rw [show s * (1 + R) * (a * s) = a * s ^ 2 * (1 + R) by ring, hs2]; field_simp
    rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
    have : 4 * c ≤ c ^ 2 * d := by
      have := mul_le_mul_of_nonneg_left hdX' (by positivity : (0 : ℝ) ≤ c ^ 2 / 2)
      have e2 : c ^ 2 / 2 * (X / c) = c * X / 2 := by field_simp
      nlinarith
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have hfin : (2 * (1 + R) ^ 2 + (1 + R) / 4) ≤ airyConst K₃ := by
    unfold airyConst
    have : 1 + R ≤ 1 + √(2 * K₃) := by linarith
    have h1 : (1 + R) ^ 2 ≤ (1 + √(2 * K₃)) ^ 2 := pow_le_pow_left₀ (by positivity) this 2
    linarith
  have hG' : 0 ≤ G / c := by positivity
  calc ∫ t in t₂..1, y t ^ 2 = (∫ t in t₂..ts, y t ^ 2) + ∫ t in ts..1, y t ^ 2 := hsplit.symm
    _ ≤ (ts - t₂) * M ^ 2 + (d * M ^ 2 + M * (a * s) / (c ^ 2 * d)) := add_le_add hI1 hI2
    _ ≤ (1 + R) ^ 2 * G / c + ((1 + R) ^ 2 * G / c + (1 + R) * G / (4 * c)) := by
        have : (ts - t₂) * M ^ 2 = d * M ^ 2 := rfl
        linarith
    _ = (2 * (1 + R) ^ 2 + (1 + R) / 4) * (G / c) := by field_simp; ring
    _ ≤ airyConst K₃ * (G / c) := mul_le_mul_of_nonneg_right hfin hG'
    _ = airyConst K₃ / c * energyAt c σ t₂ := by ring

end Cvs.Prolate.LiouvilleGreen.AiryLayerBelowCoulomb

end
