import Mathlib
import Cvs.Prolate.Mellin.GroundRatioStepErrors
import Cvs.Prolate.Mellin.NearRegionBootstrap
import Cvs.Prolate.Mellin.NearRegionForcingSize

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The bootstrap conditions hold for large `c`, and `E₁ → 0`

For fixed `ε > 0`, `c^{7/8} Λ₁(ε, c) → 0` as `c → ∞`; hence `(40/9)Λ₁ΓT ≤ 1` and `2ΓΛ₁ ≤ 1/10` eventually, and the
step-error budget `E₁(ε, c) → 0`.
-/

noncomputable section

open Filter Topology

namespace Cvs.Prolate.Mellin.BootstrapLargeBandwidth

open Cvs.Prolate.Mellin.NearRegionForcingSize Cvs.Prolate.Mellin.NearRegionBootstrap Cvs.Prolate.Mellin.GroundRatioStepErrors

variable {ε : ℝ}

/-- `c^{7/8} Λ₁`. -/
def uΛ (ε c : ℝ) : ℝ := c ^ (7 / 8 : ℝ) * Λc ε c

theorem tendsto_log_mul_rpow : Tendsto (fun c : ℝ => Real.log c * c ^ (-(1 / 8 : ℝ))) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_atTop (r := 1 / 8) (by norm_num)).tendsto_div_nhds_zero
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with c hc
  rw [Real.rpow_neg hc.le, div_eq_mul_inv]

theorem tendsto_uΛ (hε : 0 < ε) : Tendsto (uΛ ε) atTop (𝓝 0) := by
  have e : ∀ᶠ c : ℝ in atTop, (5424 / ε + 750 + 300000 / ε ^ 2 * (2 / 5) + 20000000 / ε ^ 2) * c ^ (-(1 / 8 : ℝ))
      + 300000 / ε ^ 2 * (1 / 2) * (Real.log c * c ^ (-(1 / 8 : ℝ)))
      + 20000000 / ε ^ 2 * (c ^ (-(1 / 8 : ℝ)) * c⁻¹) = uΛ ε c := by
    filter_upwards [eventually_gt_atTop 0] with c hc
    have h78 : c ^ (7 / 8 : ℝ) = c * c ^ (-(1 / 8 : ℝ)) := by
      rw [← Real.rpow_one_add' hc.le (by norm_num)]; norm_num
    unfold uΛ Λc DS
    rw [h78]
    field_simp
    ring
  refine Tendsto.congr' e ?_
  have t1 := tendsto_rpow_neg_atTop (y := 1 / 8) (by norm_num)
  have t2 := tendsto_log_mul_rpow
  have t3 := t1.mul tendsto_inv_atTop_zero
  have := ((t1.const_mul (5424 / ε + 750 + 300000 / ε ^ 2 * (2 / 5) + 20000000 / ε ^ 2)).add
    (t2.const_mul (300000 / ε ^ 2 * (1 / 2)))).add (t3.const_mul (20000000 / ε ^ 2))
  simpa using this

theorem Γc_eq {c : ℝ} (hc : 0 < c) : Γc c = Real.exp (17 / 15) * c ^ (3 / 8 : ℝ) := by
  unfold Γc; rw [Real.rpow_def_of_pos hc, ← Real.exp_add]; ring_nf

theorem NV_eq {c : ℝ} (hc : 0 < c) : NV ε c = 2 * Real.exp (17 / 15) * c ^ (-(1 / 2 : ℝ)) * uΛ ε c := by
  unfold NV uΛ; rw [Γc_eq hc]
  have : c ^ (3 / 8 : ℝ) = c ^ (-(1 / 2 : ℝ)) * c ^ (7 / 8 : ℝ) := by
    rw [← Real.rpow_add hc]; norm_num
  rw [this]; ring

theorem tendsto_NV (hε : 0 < ε) : Tendsto (NV ε) atTop (𝓝 0) := by
  have t1 := tendsto_rpow_neg_atTop (y := 1 / 2) (by norm_num)
  have := (t1.const_mul (2 * Real.exp (17 / 15))).mul (tendsto_uΛ hε)
  simp only [mul_zero] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with c hc
  rw [NV_eq hc]

theorem tendsto_sq_NV (hε : 0 < ε) : Tendsto (fun c => (c + 2) * NV ε c ^ 2) atTop (𝓝 0) := by
  have e : ∀ᶠ c : ℝ in atTop, (1 + 2 * c⁻¹) * (2 * Real.exp (17 / 15) * uΛ ε c) ^ 2 = (c + 2) * NV ε c ^ 2 := by
    filter_upwards [eventually_gt_atTop 0] with c hc
    rw [NV_eq hc]
    have h : (c ^ (-(1 / 2 : ℝ))) ^ 2 = c⁻¹ := by
      rw [sq, ← Real.rpow_add hc]; norm_num; exact Real.rpow_neg_one c
    have e2 : (2 * Real.exp (17 / 15) * c ^ (-(1 / 2 : ℝ)) * uΛ ε c) ^ 2
        = (2 * Real.exp (17 / 15)) ^ 2 * uΛ ε c ^ 2 * (c ^ (-(1 / 2 : ℝ))) ^ 2 := by ring
    rw [e2, h]
    field_simp
  refine Tendsto.congr' e ?_
  have t := ((tendsto_const_nhds (x := (1 : ℝ))).add (tendsto_inv_atTop_zero.const_mul 2)).mul
    (((tendsto_uΛ hε).const_mul (2 * Real.exp (17 / 15))).pow 2)
  simpa using t

theorem Tc_le {c : ℝ} (hc : 1 ≤ c) : Tc c ≤ 137 * Real.sqrt c := by
  have hc0 : 0 < c := by linarith
  have hs : 1 ≤ Real.sqrt c := Real.one_le_sqrt.mpr hc
  have h2 : Real.sqrt (2 * c) = Real.sqrt 2 * Real.sqrt c := by rw [Real.sqrt_mul (by norm_num)]
  have hs2 : Real.sqrt 2 ≤ 3 / 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hs2' : 7 / 5 ≤ Real.sqrt 2 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  unfold Tc
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ Real.sqrt (2 * c) / 2 by positivity)
  have h3 : 189 * c / Real.sqrt (2 * c) = 189 / Real.sqrt 2 * Real.sqrt c := by
    rw [h2]; field_simp; rw [Real.sq_sqrt hc0.le]
  rw [h3, h2]
  have h4 : 189 / Real.sqrt 2 ≤ 135 := by rw [div_le_iff₀ (by positivity)]; linarith
  rw [h2] at hceil
  have : (189 / Real.sqrt 2) * Real.sqrt c ≤ 135 * Real.sqrt c := by gcongr
  nlinarith

theorem tendsto_hs1 (hε : 0 < ε) : Tendsto (fun c => 40 / 9 * Λc ε c * Γc c * Tc c) atTop (𝓝 0) := by
  have hb : Tendsto (fun c => 40 / 9 * 137 * Real.exp (17 / 15) * uΛ ε c) atTop (𝓝 0) := by
    simpa using (tendsto_uΛ hε).const_mul (40 / 9 * 137 * Real.exp (17 / 15))
  refine squeeze_zero' ?_ ?_ hb
  · filter_upwards [eventually_ge_atTop 1] with c hc
    have hc0 : 0 < c := by linarith
    have hΓ : 0 ≤ Γc c := (Real.exp_pos _).le
    have hT : 0 ≤ Tc c := by unfold Tc; positivity
    have hΛ : 0 ≤ Λc ε c := by
      unfold Λc DS
      have := Real.log_nonneg hc
      positivity
    positivity
  · filter_upwards [eventually_ge_atTop 1] with c hc
    have hc0 : 0 < c := by linarith
    have hΛ0 : 0 ≤ Λc ε c := by
      unfold Λc DS
      have := Real.log_nonneg hc
      positivity
    rw [Γc_eq hc0]
    have hT := Tc_le hc
    have hsq : c ^ (3 / 8 : ℝ) * Real.sqrt c = c ^ (7 / 8 : ℝ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hc0]; norm_num
    unfold uΛ
    calc 40 / 9 * Λc ε c * (Real.exp (17 / 15) * c ^ (3 / 8 : ℝ)) * Tc c
        ≤ 40 / 9 * Λc ε c * (Real.exp (17 / 15) * c ^ (3 / 8 : ℝ)) * (137 * Real.sqrt c) := by
          gcongr
      _ = 40 / 9 * 137 * Real.exp (17 / 15) * (c ^ (3 / 8 : ℝ) * Real.sqrt c * Λc ε c) := by ring
      _ = _ := by rw [hsq]

/-- **The bootstrap conditions hold for large `c`.** -/
theorem eventually_conditions (hε : 0 < ε) :
    ∀ᶠ c : ℝ in atTop, 40 / 9 * Λc ε c * Γc c * Tc c ≤ 1 ∧ 2 * Γc c * Λc ε c ≤ 1 / 10 := by
  have h1 := (tendsto_hs1 hε).eventually (ge_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  have h2 := (tendsto_NV hε).eventually (ge_mem_nhds (show (0 : ℝ) < 1 / 10 by norm_num))
  filter_upwards [h1, h2] with c a b
  exact ⟨a, b⟩

/-- **`E₁ → 0`.** -/
theorem tendsto_E1 (hε : 0 < ε) : Tendsto (E1 ε) atTop (𝓝 0) := by
  have hN := tendsto_NV hε
  have hS := tendsto_sq_NV hε
  have hi := tendsto_inv_atTop_zero (𝕜 := ℝ)
  have e : ∀ᶠ c : ℝ in atTop,
      (225 / (2 * Real.sqrt ε) + 1) * ((c + 2) * NV ε c ^ 2 + 1125000 * c⁻¹) + (1 + 12 / Real.sqrt ε) * NV ε c
        + (144 / ε * NV ε c * ((1 + c⁻¹) * (4050 / (7 * Real.sqrt ε)) + 27 / 8)
          + 216000 / ε * (8100 / 14 * c⁻¹ + 81 / 32 * c⁻¹ ^ 2)) = E1 ε c := by
    filter_upwards [eventually_gt_atTop 0] with c hc
    unfold E1 DV
    field_simp
  refine Tendsto.congr' e ?_
  have t := (((hS.add (hi.const_mul 1125000)).const_mul (225 / (2 * Real.sqrt ε) + 1)).add
    (hN.const_mul (1 + 12 / Real.sqrt ε))).add
    (((hN.const_mul (144 / ε)).mul
      (((tendsto_const_nhds (x := (1 : ℝ))).add hi).mul_const (4050 / (7 * Real.sqrt ε)) |>.add_const (27 / 8))).add
      (((hi.const_mul (8100 / 14)).add ((hi.pow 2).const_mul (81 / 32))).const_mul (216000 / ε)))
  simpa using t

end Cvs.Prolate.Mellin.BootstrapLargeBandwidth
