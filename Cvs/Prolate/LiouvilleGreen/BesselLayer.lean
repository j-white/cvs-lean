import Mathlib
import Cvs.Prolate.LiouvilleGreen.AdiabaticStretchBounds
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
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
# The Bessel layer: `AdiabaticStretchBounds`'s `BesselLayer c σ` for `c ≥ 1`, and `|w(t₃)| ≤ 11/10`

With `D = σ − c² ≥ 16c`, `s₃ = 1/(2D)`, `t₃ = 1 − s₃` and `Y = max_{[t₃, 1]} |y|`: `|U(t)| ≤ Y q(t₃)(1 − t)`, so
`|y − 1| ≤ εY` with `ε = q(t₃)s₃/(2 − s₃) ≤ 257/1008`, hence `Y(1 − 2ε) ≤ |y(t₃)|` and `∫_{t₃}^1 y² ≤ 4.35 s₃ G/a`.
-/

noncomputable section

open Real Set Filter Topology MeasureTheory intervalIntegral
open Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval (pP)
open Cvs.Prolate.RegularSolutionEdge (regSol regU regV sqC continuousOn_regSol hasDerivAt_regSol hasDerivAt_regU pP_mul_regV regSol_one)
open Cvs.Prolate.TopRungDepthBound (af qf wf af_pos af_sq sqC_apply)
open Cvs.Prolate.LiouvilleGreen.AdiabaticStretchBounds (energyAt sq_le_energyAt_div qf_eq LayerBound BesselLayer)

namespace Cvs.Prolate.LiouvilleGreen.BesselLayer

variable {c σ : ℝ}

/-- `regU = −∫_t^1 q y` bounded by the sup: `|U(t)| ≤ Y q(t₃)(1 − t)` on `[t₃, 1]` when `σ ≥ c²` and `0 ≤ t₃`. -/
theorem abs_regU_le {t₃ t Y : ℝ} (ht₃ : 0 ≤ t₃) (hσ : c ^ 2 ≤ σ) (ht : t ∈ Icc t₃ 1)
    (hY : ∀ s ∈ Icc t₃ 1, |regSol (sqC c) σ s| ≤ Y) :
    |regU (sqC c) σ t| ≤ Y * (σ - c ^ 2 * t₃ ^ 2) * (1 - t) := by
  unfold regU
  rw [abs_neg]
  have hb : ∀ s ∈ uIoc (1 : ℝ) t, ‖(sqC c s - σ) * regSol (sqC c) σ s‖ ≤ Y * (σ - c ^ 2 * t₃ ^ 2) := by
    intro s hs
    rw [uIoc_of_ge ht.2] at hs
    have hs0 : t₃ ≤ s := ht.1.trans hs.1.le
    have hs1 : s ≤ 1 := hs.2
    have hsI : s ∈ Icc t₃ 1 := ⟨hs0, hs1⟩
    rw [Real.norm_eq_abs, abs_mul, sqC_apply]
    have h1 : |c ^ 2 * s ^ 2 - σ| ≤ σ - c ^ 2 * t₃ ^ 2 := by
      have hs2 : s ^ 2 ≤ 1 := by nlinarith
      have hst : t₃ ^ 2 ≤ s ^ 2 := by nlinarith
      rw [abs_of_nonpos (by nlinarith [sq_nonneg c])]
      nlinarith [sq_nonneg c]
    have hY0 : 0 ≤ Y := (abs_nonneg _).trans (hY s hsI)
    calc |c ^ 2 * s ^ 2 - σ| * |regSol (sqC c) σ s| ≤ (σ - c ^ 2 * t₃ ^ 2) * Y :=
          mul_le_mul h1 (hY s hsI) (abs_nonneg _) ((abs_nonneg _).trans h1)
      _ = Y * (σ - c ^ 2 * t₃ ^ 2) := by ring
  have h := norm_integral_le_of_norm_le_const hb
  rw [Real.norm_eq_abs, abs_of_nonpos (by linarith [ht.2] : t - 1 ≤ 0)] at h
  linarith

/-- **The Bessel-layer sup bound**: with `ε = q(t₃)(1 − t₃)/(1 + t₃)`, `|y(t) − 1| ≤ εY` on `[t₃, 1]`. -/
theorem abs_regSol_sub_one_le {t₃ t Y : ℝ} (ht₃ : 0 ≤ t₃) (ht₃1 : t₃ ≤ 1) (hσ : c ^ 2 ≤ σ) (ht : t ∈ Icc t₃ 1)
    (hY : ∀ s ∈ Icc t₃ 1, |regSol (sqC c) σ s| ≤ Y) :
    |regSol (sqC c) σ t - 1| ≤ (σ - c ^ 2 * t₃ ^ 2) * (1 - t₃) / (1 + t₃) * Y := by
  set q₃ := σ - c ^ 2 * t₃ ^ 2
  have ht2 : t₃ ^ 2 ≤ 1 := by nlinarith
  have hq₃ : 0 ≤ q₃ := by nlinarith [mul_le_mul_of_nonneg_left ht2 (sq_nonneg c)]
  have hY0 : 0 ≤ Y := (abs_nonneg _).trans (hY t ht)
  have hderiv : ∀ x ∈ Icc t 1, HasDerivWithinAt (regSol (sqC c) σ) (regV (sqC c) σ x) (Icc t 1) x :=
    fun x hx => (hasDerivAt_regSol (sqC c) σ (by linarith [ht.1, hx.1])).hasDerivWithinAt
  have hbound : ∀ x ∈ Ico t 1, ‖regV (sqC c) σ x‖ ≤ Y * q₃ / (1 + t₃) := by
    intro x hx
    have hxI : x ∈ Icc t₃ 1 := ⟨ht.1.trans hx.1, hx.2.le⟩
    have hx1 : x < 1 := hx.2
    have hxp : 0 < 1 - x ^ 2 := by nlinarith [ht.1, hx.1]
    have hpv := pP_mul_regV (sqC c) σ (show (-1 : ℝ) < x by linarith [ht.1, hx.1])
    unfold pP at hpv
    have hv : regV (sqC c) σ x = -regU (sqC c) σ x / (1 - x ^ 2) := by
      field_simp; linarith
    rw [Real.norm_eq_abs, hv, abs_div, abs_neg, abs_of_pos hxp, div_le_div_iff₀ hxp (by linarith)]
    have hU := abs_regU_le ht₃ hσ hxI hY
    have e : 1 - x ^ 2 = (1 - x) * (1 + x) := by ring
    rw [e]
    have h1x : 0 ≤ 1 - x := by linarith
    have hxt : 1 + t₃ ≤ 1 + x := by linarith [hxI.1]
    calc |regU (sqC c) σ x| * (1 + t₃) ≤ Y * q₃ * (1 - x) * (1 + t₃) :=
          mul_le_mul_of_nonneg_right hU (by linarith)
      _ ≤ Y * q₃ * (1 - x) * (1 + x) := by
          apply mul_le_mul_of_nonneg_left hxt; positivity
      _ = Y * q₃ * ((1 - x) * (1 + x)) := by ring
  have h := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound 1 ⟨ht.2, le_rfl⟩
  rw [regSol_one, Real.norm_eq_abs, abs_sub_comm] at h
  calc |regSol (sqC c) σ t - 1| ≤ Y * q₃ / (1 + t₃) * (1 - t) := h
    _ ≤ Y * q₃ / (1 + t₃) * (1 - t₃) := by
        apply mul_le_mul_of_nonneg_left (by linarith [ht.1]); positivity
    _ = q₃ * (1 - t₃) / (1 + t₃) * Y := by ring

/-- **Lemma 3.7(a) (the Bessel layer)**: for `c ≥ 1`, `AdiabaticStretchBounds`'s `BesselLayer c σ` holds. -/
theorem besselLayer (hc : 1 ≤ c) : BesselLayer c σ := by
  intro hβ
  set D := σ - c ^ 2 with hD_def
  have hc0 : 0 < c := by linarith
  have hD : 16 * c ≤ D := by
    have := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * c)).mp hβ; linarith
  have hDpos : 0 < D := by linarith
  set s₃ := 1 / (2 * D) with hs₃
  set t₃ := 1 - s₃ with ht₃
  set K := (c ^ 2 - σ) / c
  have hs₃pos : 0 < s₃ := div_pos one_pos (by linarith)
  have hcs : c * s₃ ≤ 1 / 32 := by
    rw [hs₃, mul_one_div, div_le_iff₀ (by positivity)]; linarith
  have hs₃le : s₃ ≤ 1 / 32 := by nlinarith
  have hDs : D * s₃ = 1 / 2 := by rw [hs₃]; field_simp
  have ht₃0 : 0 ≤ t₃ := by linarith
  have ht₃1 : t₃ ≤ 1 := by linarith
  have hσ : c ^ 2 ≤ σ := by linarith
  -- the sup
  have hcont : ContinuousOn (fun s => |regSol (sqC c) σ s|) (Icc t₃ 1) :=
    ((continuousOn_regSol (sqC c) σ).mono fun s hs => show (-1 : ℝ) < s by linarith [hs.1]).abs
  obtain ⟨tm, htm, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr ht₃1) hcont
  set Y := |regSol (sqC c) σ tm|
  have hY : ∀ s ∈ Icc t₃ 1, |regSol (sqC c) σ s| ≤ Y := fun s hs => hmax hs
  have hY0 : 0 ≤ Y := abs_nonneg _
  set q₃ := σ - c ^ 2 * t₃ ^ 2 with hq₃
  set ε := q₃ * (1 - t₃) / (1 + t₃) with hε
  have hE : ε ≤ 257 / 1008 := by
    have e1 : q₃ * s₃ = 1 / 2 + c ^ 2 * s₃ ^ 2 * (2 - s₃) := by
      rw [hq₃, ht₃]; linear_combination hDs
    have e2 : c ^ 2 * s₃ ^ 2 ≤ 1 / 1024 := by
      calc c ^ 2 * s₃ ^ 2 = (c * s₃) * (c * s₃) := by ring
        _ ≤ (1 / 32) * (1 / 32) := mul_le_mul hcs hcs (by positivity) (by norm_num)
        _ = 1 / 1024 := by norm_num
    have e4 : c ^ 2 * s₃ ^ 2 * (2 - s₃) ≤ 1 / 1024 * 2 :=
      mul_le_mul e2 (by linarith) (by linarith) (by norm_num)
    have e3 : q₃ * s₃ ≤ 257 / 512 := by linarith
    rw [hε, show 1 - t₃ = s₃ by ring, show 1 + t₃ = 2 - s₃ by ring, div_le_iff₀ (by linarith)]
    linarith
  have hε0 : 0 ≤ ε := by
    have ht2 : t₃ ^ 2 ≤ 1 := by nlinarith
    have : 0 ≤ q₃ := by nlinarith [mul_le_mul_of_nonneg_left ht2 (sq_nonneg c)]
    rw [hε]; apply div_nonneg (mul_nonneg this (by linarith)) (by linarith)
  have hdev := fun t (ht : t ∈ Icc t₃ 1) => abs_regSol_sub_one_le ht₃0 ht₃1 hσ ht hY
  -- `Y(1 − 2ε) ≤ |y(t₃)|`
  have hYm : Y ≤ 1 + ε * Y := by
    have := hdev tm htm
    have := abs_sub_abs_le_abs_sub (regSol (sqC c) σ tm) 1
    rw [abs_one] at this; linarith
  have hY3 : Y * (1 - 2 * ε) ≤ |regSol (sqC c) σ t₃| := by
    have h := hdev t₃ ⟨le_rfl, ht₃1⟩
    have := abs_sub_abs_le_abs_sub 1 (regSol (sqC c) σ t₃)
    rw [abs_one, abs_sub_comm] at this
    nlinarith
  have hY2 : Y ^ 2 ≤ 435 / 100 * regSol (sqC c) σ t₃ ^ 2 := by
    have h12 : 494 / 1008 ≤ 1 - 2 * ε := by linarith
    have hsq : (Y * (1 - 2 * ε)) ^ 2 ≤ regSol (sqC c) σ t₃ ^ 2 := by
      rw [← sq_abs (regSol (sqC c) σ t₃)]
      exact pow_le_pow_left₀ (mul_nonneg hY0 (by linarith)) hY3 2
    have : Y ^ 2 * (494 / 1008) ^ 2 ≤ (Y * (1 - 2 * ε)) ^ 2 := by
      rw [mul_pow]; exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) h12 2) (sq_nonneg _)
    nlinarith [sq_nonneg Y]
  -- the integral
  have hint : ∫ s in t₃..1, regSol (sqC c) σ s ^ 2 ≤ s₃ * Y ^ 2 := by
    have hb : ∀ s ∈ uIoc t₃ 1, ‖regSol (sqC c) σ s ^ 2‖ ≤ Y ^ 2 := by
      intro s hs
      rw [uIoc_of_le ht₃1] at hs
      rw [Real.norm_eq_abs, abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hY s ⟨hs.1.le, hs.2⟩) 2
    have h := norm_integral_le_of_norm_le_const hb
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - t₃), show 1 - t₃ = s₃ by ring] at h
    have := le_abs_self (∫ s in t₃..1, regSol (sqC c) σ s ^ 2)
    rw [Real.norm_eq_abs] at h
    linarith
  -- `y(t₃)² ≤ G/a`
  have ht₃s : t₃ ^ 2 < 1 := by nlinarith
  have hq : 0 < qf c K t₃ := by rw [qf_eq hc0.ne']; nlinarith
  have ha := af_pos ht₃s hq
  have hyG := sq_le_energyAt_div (c := c) (σ := σ) (t := t₃) ha
  unfold LayerBound
  calc ∫ s in t₃..1, regSol (sqC c) σ s ^ 2 ≤ s₃ * Y ^ 2 := hint
    _ ≤ s₃ * (435 / 100 * regSol (sqC c) σ t₃ ^ 2) := mul_le_mul_of_nonneg_left hY2 hs₃pos.le
    _ ≤ s₃ * (435 / 100 * (energyAt c σ t₃ / af c K t₃)) := by gcongr
    _ = 435 / 100 * s₃ / af c K t₃ * energyAt c σ t₃ := by ring

/-- **Lemma 3.7(b) (the rate at the layer edge)**: for `c ≥ 1` and `σ − c² ≥ 16c`, `|w(t₃)| ≤ 11/10`. -/
theorem abs_wf_le (hc : 1 ≤ c) (hβ : 8 ≤ (σ - c ^ 2) / (2 * c)) :
    |wf c ((c ^ 2 - σ) / c) (1 - 1 / (2 * (σ - c ^ 2)))| ≤ 11 / 10 := by
  set D := σ - c ^ 2 with hD_def
  have hc0 : 0 < c := by linarith
  have hD : 16 * c ≤ D := by
    have := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * c)).mp hβ; linarith
  have hDpos : 0 < D := by linarith
  set s₃ := 1 / (2 * D) with hs₃
  set t₃ := 1 - s₃ with ht₃
  set K := (c ^ 2 - σ) / c
  have hs₃pos : 0 < s₃ := div_pos one_pos (by linarith)
  have hcs : c * s₃ ≤ 1 / 32 := by
    rw [hs₃, mul_one_div, div_le_iff₀ (by positivity)]; linarith
  have hs₃le : s₃ ≤ 1 / 32 := by nlinarith
  have hDs : D * s₃ = 1 / 2 := by rw [hs₃]; field_simp
  have ht₃s : t₃ ^ 2 < 1 := by nlinarith
  set q := qf c K t₃ with hqdef
  have hqe : q = D + c ^ 2 * s₃ * (2 - s₃) := by rw [hqdef, qf_eq hc0.ne', ht₃]; ring
  have hqD : D ≤ q := by rw [hqe]; nlinarith [sq_nonneg c]
  have hq : 0 < q := by linarith
  set p := 1 - t₃ ^ 2 with hp
  have hpe : p = s₃ * (2 - s₃) := by rw [hp, ht₃]; ring
  have ha := af_pos ht₃s hq
  have ha2 : af c K t₃ ^ 2 = p * q := af_sq ht₃s hq
  set a := af c K t₃
  have hp0 : 0 ≤ p := by rw [hpe]; nlinarith
  have hpq : 63 / 64 ≤ p * q := by
    have h1 : s₃ * (2 - s₃) * D ≤ s₃ * (2 - s₃) * q := mul_le_mul_of_nonneg_left hqD (by nlinarith)
    have h2 : s₃ * (2 - s₃) * D = (2 - s₃) / 2 := by linear_combination (2 - s₃) * hDs
    rw [hpe]; linarith
  have ha99 : 99 / 100 ≤ a := by
    have h : (99 / 100 : ℝ) ^ 2 ≤ a ^ 2 := by rw [ha2]; linarith
    exact (pow_le_pow_iff_left₀ (by norm_num) ha.le two_ne_zero).mp h
  have hw0 : wf c K t₃ ≤ 0 := Cvs.Prolate.TopRungDepthBound.wf_nonpos (by linarith) ht₃s hq
  have hw : wf c K t₃ = -(t₃ / a + c ^ 2 * t₃ * p / (a * q)) := rfl
  rw [abs_of_nonpos hw0, hw, neg_neg]
  have h1 : t₃ / a ≤ 100 / 99 := by
    rw [div_le_div_iff₀ ha (by norm_num)]; linarith
  have hp2 : p ≤ 2 * s₃ := by rw [hpe]; nlinarith
  have hc2 : c ^ 2 * s₃ ^ 2 ≤ 1 / 1024 := by
    calc c ^ 2 * s₃ ^ 2 = (c * s₃) * (c * s₃) := by ring
      _ ≤ (1 / 32) * (1 / 32) := mul_le_mul hcs hcs (by positivity) (by norm_num)
      _ = 1 / 1024 := by norm_num
  have e1 : c ^ 2 * t₃ * p ≤ c ^ 2 * (2 * s₃) := by
    have h3 : t₃ * p ≤ 1 * (2 * s₃) := mul_le_mul (by linarith) hp2 hp0 (by norm_num)
    have := mul_le_mul_of_nonneg_left h3 (sq_nonneg c)
    linarith
  have e2 : 99 / 100 * D ≤ a * q := mul_le_mul ha99 hqD hDpos.le ha.le
  have e5 : c ^ 2 * (2 * s₃) = 4 * (c ^ 2 * s₃ ^ 2) * D := by linear_combination (-4 * c ^ 2 * s₃) * hDs
  have h2 : c ^ 2 * t₃ * p / (a * q) ≤ 400 / (99 * 1024) := by
    rw [div_le_div_iff₀ (mul_pos ha hq) (by norm_num)]
    have e3 : c ^ 2 * (2 * s₃) * (99 * 1024) ≤ 400 * (99 / 100 * D) := by
      rw [e5]; nlinarith
    nlinarith
  linarith

end Cvs.Prolate.LiouvilleGreen.BesselLayer

end
