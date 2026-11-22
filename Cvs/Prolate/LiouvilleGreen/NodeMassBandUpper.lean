import Mathlib
import Cvs.Prolate.Gram.BandCellMassFloor
import Cvs.Prolate.LiouvilleGreen.AdiabaticStretchBounds
import Cvs.Prolate.LiouvilleGreen.AiryLayerBelowCoulomb
import Cvs.Prolate.LiouvilleGreen.BesselLayer
import Cvs.Prolate.LiouvilleGreen.CoulombLayerExplicit
import Cvs.Prolate.LiouvilleGreen.NodeMassAboveCoulomb
import Cvs.Prolate.LiouvilleGreen.PruferAngleRobinRate
import Cvs.Prolate.LiouvilleGreen.RateStrictlyDecreasing
import Cvs.Prolate.LiouvilleGreen.StretchClosedForms
import Cvs.Prolate.TopRungDepthBound

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# `N/G₀` is at most a multiple of `(1 + L)/c`, `L = log(c/(1 + |β|))`, on `5/8 ≤ σ/c² ≤ 3/2`

Three layers: the Coulomb layer for `|β| ≤ 24` (Cvs.Prolate.LiouvilleGreen.CoulombLayerExplicit), the Bessel layer for `β ≥ 24` (Cvs.Prolate.LiouvilleGreen.BesselLayer) and the Airy layer at
`q(t₂) = cX`, `X = 8(1 + b)^{1/3}`, `b = 2|β|`, for `β ≤ −24` (Cvs.Prolate.LiouvilleGreen.AiryLayerBelowCoulomb); in each, Cvs.Prolate.LiouvilleGreen.StretchClosedForms bounds the stretch to the layer
by a multiple of `(1 + L)/c`.
-/

noncomputable section

open Real Set Filter Topology
open Cvs.Prolate.RegularSolutionEdge (regSol sqC)
open Cvs.Prolate.TopRungDepthBound (af qf wf af_pos af_sq)
open Cvs.Prolate.LiouvilleGreen.RateStrictlyDecreasing (kappa)
open Cvs.Prolate.LiouvilleGreen.AdiabaticStretchBounds (qf_eq stretch)
open Cvs.Prolate.LiouvilleGreen.PruferAngleRobinRate (nodeMass energyHalf)

namespace Cvs.Prolate.LiouvilleGreen.NodeMassBandUpper
open Cvs.ZeroCounting

variable {c σ : ℝ}

/-- The band logarithm `L = log(c/(1 + |β|))`, `β = (σ − c²)/(2c)`. -/
def bandL (c σ : ℝ) : ℝ := Real.log (c / (1 + |σ - c ^ 2| / (2 * c)))

/-- The band model `M = (1 + L)/c`. -/
def bandM (c σ : ℝ) : ℝ := (1 + bandL c σ) / c

theorem kappa_half_le : kappa (1 / 2) ≤ 5 / 2 := by
  unfold kappa
  have h := Real.exp_bound_div_one_sub_of_interval (x := 1 / 3) (by norm_num) (by norm_num)
  norm_num at h ⊢
  linarith

theorem kappa_three_eighths_le : kappa (3 / 8) ≤ 19 / 10 := by
  unfold kappa
  have h := Real.exp_bound_div_one_sub_of_interval (x := 3 / 13) (by norm_num) (by norm_num)
  norm_num at h ⊢
  linarith

/-- `L ≥ 0` once `1 + |β| ≤ c`. -/
theorem bandL_nonneg (hc : 0 < c) (h : 1 + |σ - c ^ 2| / (2 * c) ≤ c) : 0 ≤ bandL c σ := by
  unfold bandL
  apply Real.log_nonneg
  rw [le_div_iff₀ (by positivity)]; linarith

/-- `log(c/R) ≤ L` whenever `1 + |β| ≤ R`. -/
theorem log_le_bandL (hc : 0 < c) {R : ℝ} (hR : 1 + |σ - c ^ 2| / (2 * c) ≤ R) :
    Real.log (c / R) ≤ bandL c σ := by
  unfold bandL
  have h1 : 0 < 1 + |σ - c ^ 2| / (2 * c) := by positivity
  exact Real.log_le_log (div_pos hc (h1.trans_le hR)) (div_le_div_of_nonneg_left hc.le h1 hR)

/-- `L − log R ≤ log(c/R')` whenever `R' ≤ R(1 + |β|)`. -/
theorem bandL_sub_le_log (hc : 0 < c) {R R' : ℝ} (hR' : 0 < R') (hR : R' ≤ R * (1 + |σ - c ^ 2| / (2 * c))) :
    bandL c σ - Real.log R ≤ Real.log (c / R') := by
  unfold bandL
  have h1 : 0 < 1 + |σ - c ^ 2| / (2 * c) := by positivity
  have hR0 : 0 < R := by
    by_contra h; push Not at h; have := mul_nonpos_of_nonpos_of_nonneg h h1.le; linarith
  rw [← Real.log_div (by positivity) hR0.ne']
  apply Real.log_le_log (by positivity)
  rw [div_div, div_le_div_iff₀ (by positivity) hR']
  exact mul_le_mul_of_nonneg_left (by linarith) hc.le

/-- **The Coulomb ceiling**: there is `K_C ≥ 0` with `N/G₀ ≤ κ(½)(√2 L + K_C)/c` for `c ≥ 400`, `|σ − c²| ≤ 48c`. -/
theorem upper_coulomb : ∃ KC : ℝ, 0 ≤ KC ∧ ∀ c σ : ℝ, 400 ≤ c → |σ - c ^ 2| ≤ 48 * c →
    nodeMass c σ / energyHalf c σ ≤ kappa (1 / 2) * (√2 * bandL c σ + KC) / c := by
  obtain ⟨KC, hKC, h⟩ := Cvs.Prolate.LiouvilleGreen.AdiabaticStretchBounds.nodeMass_le_coulomb (Cvs.Prolate.LiouvilleGreen.CoulombLayerExplicit.coulombLayer (B := 24) (by norm_num))
  refine ⟨KC, hKC, fun c σ hc hD => ?_⟩
  have hc0 : 0 < c := by linarith
  have hβ : |(σ - c ^ 2) / (2 * c)| ≤ 24 := by
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * c), div_le_iff₀ (by positivity)]; linarith
  have hσl : -(2 * c * 24) ≤ σ - c ^ 2 := by have := neg_abs_le (σ - c ^ 2); linarith
  obtain ⟨hq, -⟩ := Cvs.Prolate.LiouvilleGreen.CoulombLayerExplicit.abs_wf_coulomb (B := 24) (by norm_num) (by norm_num; linarith) hσl
  norm_num at hq
  have htc : 3 / 4 ≤ 1 - 100 / c := by
    have : 100 / c ≤ 1 / 4 := by rw [div_le_iff₀ hc0]; linarith
    linarith
  have htc1 : 1 - 100 / c < 1 := by have := div_pos (by norm_num : (0 : ℝ) < 100) hc0; linarith
  have hqp : 0 < qf c ((c ^ 2 - σ) / c) (1 - 100 / c) := lt_of_lt_of_le (by positivity) hq
  have htc2 : (1 - 100 / c) ^ 2 < 1 := by nlinarith [htc, htc1]
  have hN := h c σ (by norm_num; linarith) hc0 hβ (by norm_num; linarith) (by norm_num at htc2 ⊢; exact htc2)
    (by norm_num; exact hqp)
  norm_num at hN
  have hG := Cvs.Prolate.LiouvilleGreen.NodeMassAboveCoulomb.energyHalf_pos hc0.ne' (by nlinarith [abs_le.mp hD] : c ^ 2 / 4 < σ)
  have hs := Cvs.Prolate.LiouvilleGreen.StretchClosedForms.two_stretch_le_log (σ := σ) hc0 (by linarith) htc1
    (by rw [show (1 : ℝ) - (1 - 100 / c) = 100 / c by ring, show c ^ 2 * (100 / c) = 100 * c by field_simp]
        linarith)
  rw [show (1 : ℝ) - (1 - 100 / c) = 100 / c by ring, show 1 / (2 * (100 / c)) = c / 200 by field_simp; ring] at hs
  have hL := log_le_bandL (σ := σ) hc0 (R := 200) (by
    have : |σ - c ^ 2| / (2 * c) ≤ 24 := by rw [div_le_iff₀ (by positivity)]; linarith
    linarith)
  have hκ : 0 < kappa (1 / 2) := Cvs.Prolate.Gram.BandCellMassFloor.kappa_half_pos
  rw [div_le_iff₀ hG]
  have hs' : 2 * stretch c σ (1 - 100 / c) ≤ √2 / c * bandL c σ :=
    hs.trans (mul_le_mul_of_nonneg_left hL (by positivity))
  calc nodeMass c σ ≤ kappa (1 / 2) * (2 * stretch c σ (1 - 100 / c) + KC / c) * energyHalf c σ := hN
    _ ≤ kappa (1 / 2) * (√2 / c * bandL c σ + KC / c) * energyHalf c σ := by
        apply mul_le_mul_of_nonneg_right _ hG.le
        apply mul_le_mul_of_nonneg_left _ hκ.le
        linarith
    _ = kappa (1 / 2) * (√2 * bandL c σ + KC) / c * energyHalf c σ := by field_simp

/-- **The Bessel ceiling**: for `c ≥ 1` and `48c ≤ σ − c² ≤ c²/2`, `N/G₀ ≤ κ(11/10)(L + 3)/c`. -/
theorem upper_bessel (hc : 1 ≤ c) (hD : 48 * c ≤ σ - c ^ 2) (hD2 : σ - c ^ 2 ≤ c ^ 2 / 2) :
    nodeMass c σ / energyHalf c σ ≤ kappa (11 / 10) * (bandL c σ + 3) / c := by
  set D := σ - c ^ 2 with hD_def
  set K := (c ^ 2 - σ) / c
  have hc0 : 0 < c := by linarith
  have hc2 : 0 < c ^ 2 := by positivity
  have hD0 : 0 < D := by linarith
  have hβ' : 8 ≤ (σ - c ^ 2) / (2 * c) := by rw [le_div_iff₀ (by positivity)]; linarith
  set s₃ := 1 / (2 * D) with hs₃
  set t₃ := 1 - s₃ with ht₃
  have hs₃pos : 0 < s₃ := div_pos one_pos (by linarith)
  have hs₃le : s₃ ≤ 1 / 96 := by
    rw [hs₃, div_le_div_iff₀ (by linarith) (by norm_num)]; nlinarith
  have hDs : D * s₃ = 1 / 2 := by rw [hs₃]; field_simp
  have hh : 1 / 2 ≤ t₃ := by linarith
  have ht1 : t₃ < 1 := by linarith
  have ht₃s : t₃ ^ 2 < 1 := by nlinarith
  have hq : 0 < qf c K t₃ := by rw [qf_eq hc0.ne']; nlinarith
  have hw := Cvs.Prolate.LiouvilleGreen.BesselLayer.abs_wf_le hc hβ'
  have hG := Cvs.Prolate.LiouvilleGreen.NodeMassAboveCoulomb.energyHalf_pos hc0.ne' (by nlinarith : c ^ 2 / 4 < σ)
  have hN := Cvs.Prolate.LiouvilleGreen.AdiabaticStretchBounds.nodeMass_le_bessel hc0 (Cvs.Prolate.LiouvilleGreen.BesselLayer.besselLayer hc) hβ' hh hq (by norm_num : (11 / 10 : ℝ) < 2) hw
  have hκ : 0 < kappa (11 / 10) := by unfold kappa; positivity
  -- `a(t₃) ≥ 99/100`
  have ha := af_pos ht₃s hq
  have ha99 : 99 / 100 ≤ af c K t₃ := by
    have hqD : D ≤ qf c K t₃ := by rw [qf_eq hc0.ne']; nlinarith
    have hpq : 63 / 64 ≤ (1 - t₃ ^ 2) * qf c K t₃ := by
      have hp : 1 - t₃ ^ 2 = s₃ * (2 - s₃) := by rw [ht₃]; ring
      rw [hp]
      have h1 : s₃ * (2 - s₃) * D ≤ s₃ * (2 - s₃) * qf c K t₃ := mul_le_mul_of_nonneg_left hqD (by nlinarith)
      have h2 : s₃ * (2 - s₃) * D = (2 - s₃) / 2 := by linear_combination (2 - s₃) * hDs
      linarith
    have h : (99 / 100 : ℝ) ^ 2 ≤ af c K t₃ ^ 2 := by rw [af_sq ht₃s hq]; linarith
    exact (pow_le_pow_iff_left₀ (by norm_num) ha.le two_ne_zero).mp h
  have hlayer : 435 / 100 * s₃ / af c K t₃ ≤ 1 / c := by
    rw [div_le_div_iff₀ ha hc0]
    have : s₃ * c ≤ 1 / 96 := by
      rw [hs₃, one_div_mul_eq_div, div_le_div_iff₀ (by linarith) (by norm_num)]; nlinarith
    nlinarith
  -- the stretch
  have ht3m : 1 - (σ - c ^ 2) / c ^ 2 ≤ t₃ := by
    have : s₃ ≤ D / c ^ 2 := by
      rw [hs₃, div_le_div_iff₀ (by linarith) hc2]; nlinarith
    simp only [ht₃]; linarith
  have hst := Cvs.Prolate.LiouvilleGreen.StretchClosedForms.two_stretch_le_bessel hc0 (by linarith) hD2 ht3m ht1
  have hlog : Real.log (c ^ 2 / (2 * (σ - c ^ 2))) ≤ bandL c σ := by
    rw [show c ^ 2 / (2 * (σ - c ^ 2)) = c / (2 * D / c) by rw [hD_def]; field_simp]
    apply log_le_bandL hc0
    rw [abs_of_pos hD0]
    have e1 : D / (2 * c) = (D / c) / 2 := by field_simp
    have e2 : 2 * D / c = 2 * (D / c) := by ring
    have h48 : 48 ≤ D / c := by rw [le_div_iff₀ hc0]; linarith
    rw [e1, e2]; linarith
  rw [div_le_iff₀ hG]
  calc nodeMass c σ ≤ kappa (11 / 10) * (2 * stretch c σ t₃ + 435 / 100 * s₃ / af c K t₃) *
        energyHalf c σ := hN
    _ ≤ kappa (11 / 10) * ((1 / c * bandL c σ + 2 / c) + 1 / c) * energyHalf c σ := by
        apply mul_le_mul_of_nonneg_right _ hG.le
        apply mul_le_mul_of_nonneg_left _ hκ.le
        have := mul_le_mul_of_nonneg_left hlog (by positivity : (0 : ℝ) ≤ 1 / c)
        linarith
    _ = kappa (11 / 10) * (bandL c σ + 3) / c * energyHalf c σ := by field_simp; ring

/-- The Airy offset `X(b) = 8(1 + b)^{1/3}`. -/
def airyX (b : ℝ) : ℝ := 8 * (1 + b) ^ ((3 : ℕ)⁻¹ : ℝ)

theorem airyX_cube {b : ℝ} (hb : 0 ≤ b) : airyX b ^ 3 = 512 * (1 + b) := by
  unfold airyX
  rw [mul_pow, Real.rpow_inv_natCast_pow (by linarith) (by norm_num)]; norm_num

/-- For `b ≥ 48`: `8 ≤ X < b`, `16(b + X) ≤ X³ ≤ 1024b`. -/
theorem airyX_props {b : ℝ} (hb : 48 ≤ b) :
    8 ≤ airyX b ∧ airyX b < b ∧ 16 * (b + airyX b) ≤ airyX b ^ 3 ∧ airyX b ^ 3 ≤ 1024 * b := by
  have h3 := airyX_cube (b := b) (by linarith)
  have hX0 : 0 ≤ airyX b := by unfold airyX; positivity
  have h8 : 8 ≤ airyX b := by
    unfold airyX
    have : 1 ≤ (1 + b) ^ ((3 : ℕ)⁻¹ : ℝ) := Real.one_le_rpow (by linarith) (by positivity)
    linarith
  have hlt : airyX b < b := by
    have h1 : 48 * 48 ≤ b * b := mul_le_mul hb hb (by norm_num) (by linarith)
    have h2 : 48 * 48 * b ≤ b * b * b := mul_le_mul_of_nonneg_right h1 (by linarith)
    have : airyX b ^ 3 < b ^ 3 := by rw [h3]; nlinarith
    exact lt_of_pow_lt_pow_left₀ 3 (by linarith) this
  refine ⟨h8, hlt, ?_, by rw [h3]; linarith⟩
  rw [h3]; linarith

set_option maxHeartbeats 1600000 in
/-- **The Airy ceiling**: for `c ≥ 2¹⁴`, `σ ≥ 5c²/8` and `σ − c² ≤ −48c`,
`N/G₀ ≤ κ(3/8)(√2 L + 2 + C_A(1024))/c`. -/
theorem upper_airy (hc : 16384 ≤ c) (hσl : 5 * c ^ 2 / 8 ≤ σ) (hD : σ - c ^ 2 ≤ -(48 * c)) :
    nodeMass c σ / energyHalf c σ ≤ kappa (3 / 8) * (√2 * bandL c σ + 2 + Cvs.Prolate.LiouvilleGreen.AiryLayerBelowCoulomb.airyConst 1024) / c := by
  have hc0 : 0 < c := by linarith
  have hc2 : 0 < c ^ 2 := by positivity
  set b := (c ^ 2 - σ) / c with hb
  have hcb : c * b = c ^ 2 - σ := by rw [hb]; field_simp
  have hb48 : 48 ≤ b := by rw [hb, le_div_iff₀ hc0]; linarith
  set X := airyX b
  obtain ⟨hX8, hXb, hXw, hK⟩ := airyX_props hb48
  have hσ : σ < c ^ 2 := by nlinarith
  have h2 : c ^ 2 / 4 < σ - c * X := by
    have : c * X < c * b := mul_lt_mul_of_pos_left hXb hc0
    nlinarith
  obtain ⟨hw, hL⟩ := Cvs.Prolate.LiouvilleGreen.AiryLayerBelowCoulomb.airy_layer hc0 hσ hX8 hXb.le hXw hK h2
  set t₂ := √((σ - c * X) / c ^ 2)
  have ht22 : t₂ ^ 2 = (σ - c * X) / c ^ 2 := Real.sq_sqrt (div_pos (by linarith) hc2).le
  have ht2h : 1 / 2 ≤ t₂ := by
    have : (1 / 2 : ℝ) ^ 2 ≤ t₂ ^ 2 := by rw [ht22, le_div_iff₀ hc2]; linarith
    nlinarith [Real.sqrt_nonneg ((σ - c * X) / c ^ 2)]
  have hX0 : 0 < X := by linarith
  have ht21 : t₂ ^ 2 < 1 := by rw [ht22, div_lt_one hc2]; nlinarith
  have hq2 : 0 < qf c ((c ^ 2 - σ) / c) t₂ := by
    rw [qf_eq hc0.ne', ht22]; field_simp; nlinarith
  have hCA : 0 ≤ Cvs.Prolate.LiouvilleGreen.AiryLayerBelowCoulomb.airyConst 1024 := by unfold Cvs.Prolate.LiouvilleGreen.AiryLayerBelowCoulomb.airyConst; positivity
  have hN := Cvs.Prolate.LiouvilleGreen.AdiabaticStretchBounds.nodeMass_le hc0.ne' ht2h ht21 hq2 (by norm_num : (3 / 8 : ℝ) < 2) hw
    (div_nonneg hCA hc0.le) hL
  have hG := Cvs.Prolate.LiouvilleGreen.NodeMassAboveCoulomb.energyHalf_pos hc0.ne' (by nlinarith : c ^ 2 / 4 < σ)
  have hps : (c ^ 2 - σ) / c ^ 2 ≤ 3 / 8 := by rw [div_le_iff₀ hc2]; linarith
  have hts : √(1 - 2 * ((c ^ 2 - σ) / c ^ 2)) ≤ t₂ := by
    apply Real.sqrt_le_sqrt
    rw [le_div_iff₀ hc2]
    have : 1 - 2 * ((c ^ 2 - σ) / c ^ 2) = (2 * σ - c ^ 2) / c ^ 2 := by field_simp; ring
    rw [this, div_mul_cancel₀ _ hc2.ne']
    have : c * X ≤ c * b := mul_le_mul_of_nonneg_left hXb.le hc0.le
    linarith
  have htq : t₂ ^ 2 < 1 - (c ^ 2 - σ) / c ^ 2 := by
    rw [ht22, show 1 - (c ^ 2 - σ) / c ^ 2 = σ / c ^ 2 by field_simp; ring]
    exact div_lt_div_of_pos_right (by nlinarith) hc2
  have hst := Cvs.Prolate.LiouvilleGreen.StretchClosedForms.two_stretch_le_airy hc0 hσ hps hts htq
  have hlog : Real.log (1 / (2 * ((c ^ 2 - σ) / c ^ 2))) ≤ bandL c σ := by
    rw [show 1 / (2 * ((c ^ 2 - σ) / c ^ 2)) = c / (2 * b) by rw [← hcb]; field_simp]
    apply log_le_bandL hc0
    rw [abs_of_neg (by linarith), show -(σ - c ^ 2) = c * b by rw [hcb]; ring,
      show c * b / (2 * c) = b / 2 by field_simp]
    linarith
  have hκ : 0 < kappa (3 / 8) := by unfold kappa; positivity
  rw [div_le_iff₀ hG]
  calc nodeMass c σ ≤ kappa (3 / 8) * (2 * stretch c σ t₂ + Cvs.Prolate.LiouvilleGreen.AiryLayerBelowCoulomb.airyConst 1024 / c) * energyHalf c σ := hN
    _ ≤ kappa (3 / 8) * ((√2 / c * bandL c σ + 2 / c) + Cvs.Prolate.LiouvilleGreen.AiryLayerBelowCoulomb.airyConst 1024 / c) * energyHalf c σ := by
        apply mul_le_mul_of_nonneg_right _ hG.le
        apply mul_le_mul_of_nonneg_left _ hκ.le
        have := mul_le_mul_of_nonneg_left hlog (by positivity : (0 : ℝ) ≤ √2 / c)
        linarith
    _ = kappa (3 / 8) * (√2 * bandL c σ + 2 + Cvs.Prolate.LiouvilleGreen.AiryLayerBelowCoulomb.airyConst 1024) / c * energyHalf c σ := by
        field_simp

end Cvs.Prolate.LiouvilleGreen.NodeMassBandUpper

end
