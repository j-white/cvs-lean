import Mathlib
import Cvs.Prolate.Gram.BandCellMassFloor
import Cvs.Prolate.LiouvilleGreen.AdiabaticStretchBounds
import Cvs.Prolate.LiouvilleGreen.AiryLayerBelowCoulomb
import Cvs.Prolate.LiouvilleGreen.CoulombLayerExplicit
import Cvs.Prolate.LiouvilleGreen.NodeMassAboveCoulomb
import Cvs.Prolate.LiouvilleGreen.NodeMassBandUpper
import Cvs.Prolate.LiouvilleGreen.PruferAngleRobinRate
import Cvs.Prolate.LiouvilleGreen.RateStrictlyDecreasing
import Cvs.Prolate.LiouvilleGreen.StretchClosedForms
import Cvs.Prolate.LiouvilleGreen.WeightedVirialFloor
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
# `N/G₀` is at least a multiple of `(1 + L)/c` on `5/8 ≤ σ/c² ≤ 3/2`

`WeightedVirialFloor`'s `1/q`-weighted virial at the Coulomb edge `t_c = 1 − 100/c` (for `σ − c² ≥ −48c`) or at the Airy point `t₂`
(for `σ − c² ≤ −48c`) gives `N/G₀ ≥ m/(2κ)`, and Cvs.Prolate.LiouvilleGreen.StretchClosedForms gives `m ≥ max(a₀/c, (L − log 200)/(4√2 c))`.
-/

noncomputable section

open Real Set Filter Topology
open Cvs.Prolate.RegularSolutionEdge (regSol sqC)
open Cvs.Prolate.TopRungDepthBound (af qf wf af_pos af_sq)
open Cvs.Prolate.LiouvilleGreen.RateStrictlyDecreasing (kappa)
open Cvs.Prolate.LiouvilleGreen.AdiabaticStretchBounds (qf_eq stretch)
open Cvs.Prolate.LiouvilleGreen.PruferAngleRobinRate (nodeMass energyHalf)
open Cvs.Prolate.LiouvilleGreen.NodeMassBandUpper (bandL bandM airyX)

namespace Cvs.Prolate.LiouvilleGreen.NodeMassBandLower
open Cvs.ZeroCounting

variable {c σ : ℝ}

/-- **Two floors make one**: `x ≥ a₀/c` and, when `L > 2A + 1`, `x ≥ (L − A)/(Bc)` give
`x ≥ min(a₀/(2A + 2), 1/(2B))·(1 + L)/c`. -/
theorem comb_floor {x c L a₀ A B : ℝ} (hc : 0 < c) (hL : 0 ≤ L) (ha₀ : 0 < a₀) (hA : 0 ≤ A) (hB : 0 < B)
    (h1 : a₀ / c ≤ x) (h2 : 2 * A + 1 < L → (L - A) / (B * c) ≤ x) :
    min (a₀ / (2 * A + 2)) (1 / (2 * B)) * ((1 + L) / c) ≤ x := by
  rcases le_or_gt L (2 * A + 1) with h | h
  · refine le_trans ?_ h1
    calc min (a₀ / (2 * A + 2)) (1 / (2 * B)) * ((1 + L) / c) ≤ a₀ / (2 * A + 2) * ((1 + L) / c) :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)
      _ ≤ a₀ / (2 * A + 2) * ((2 * A + 2) / c) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (by linarith) hc.le) (by positivity)
      _ = a₀ / c := by field_simp
  · refine le_trans ?_ (h2 h)
    calc min (a₀ / (2 * A + 2)) (1 / (2 * B)) * ((1 + L) / c) ≤ 1 / (2 * B) * ((1 + L) / c) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
      _ ≤ (L - A) / (B * c) := by
          rw [div_mul_div_comm, one_mul, div_le_div_iff₀ (by positivity) (by positivity)]
          have h3 : 1 + L ≤ 2 * (L - A) := by linarith
          have h4 : 0 ≤ B * c := by positivity
          nlinarith [mul_le_mul_of_nonneg_right h3 h4]

/-- **The weighted virial in `N/G₀` form**: under `WeightedVirialFloor`'s hypotheses and `m(t_e) ≥ κ²/q(t_e)`,
`N/G₀ ≥ m(t_e)/(2κ)`. -/
theorem half_le_nodeMass_div (hc : 0 < c) {te M : ℝ} (hh : 1 / 2 ≤ te) (hs : te ^ 2 < 1)
    (hq : 0 < qf c ((c ^ 2 - σ) / c) te) (hM0 : 0 ≤ M) (hM : M < 2)
    (hwM : |wf c ((c ^ 2 - σ) / c) te| ≤ M) (hG : 0 < energyHalf c σ)
    (hbig : kappa M ^ 2 / qf c ((c ^ 2 - σ) / c) te ≤ stretch c σ te) :
    stretch c σ te / (2 * kappa M) ≤ nodeMass c σ / energyHalf c σ := by
  have hv := Cvs.Prolate.LiouvilleGreen.WeightedVirialFloor.stretch_le_integral_sq hc.ne' hh hs hq hM0 hM hwM
  have hκ : 0 < kappa M := lt_of_lt_of_le one_pos (Cvs.Prolate.LiouvilleGreen.WeightedVirialFloor.one_le_kappa hM0 hM)
  have hsplit := Cvs.Prolate.LiouvilleGreen.AdiabaticStretchBounds.nodeMass_split c σ te hh
  have hrest : 0 ≤ ∫ s in te..1, regSol (sqC c) σ s ^ 2 :=
    intervalIntegral.integral_nonneg (by nlinarith) fun s _ => sq_nonneg _
  set G := energyHalf c σ
  set q := qf c ((c ^ 2 - σ) / c) te
  set m := stretch c σ te
  have h1 : G / kappa M * m - kappa M * G / (2 * q) ≤ nodeMass c σ := by linarith
  have h2 : kappa M * G / (2 * q) ≤ G / kappa M * m / 2 := by
    rw [div_le_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left hbig (by positivity : (0 : ℝ) ≤ G / kappa M)
    have e1 : G / kappa M * (kappa M ^ 2 / q) = kappa M * G / q := by field_simp
    have e2 : G / kappa M * m / 2 * (2 * q) = G / kappa M * m * q := by ring
    rw [e2]
    have e3 : kappa M * G = kappa M * G / q * q := by field_simp
    nlinarith [this]
  rw [div_le_div_iff₀ (by positivity) hG]
  have : G / kappa M * m / 2 ≤ nodeMass c σ := by linarith
  have hκ2 : (0 : ℝ) ≤ 2 * kappa M := by positivity
  calc m * G = (G / kappa M * m / 2) * (2 * kappa M) := by field_simp
    _ ≤ nodeMass c σ * (2 * kappa M) := mul_le_mul_of_nonneg_right this hκ2

/-- The band floor constant `k(a₀, κ) = min(a₀/(2 log 200 + 2), 1/(8√2))/(2κ)`. -/
def kFloor (a₀ κ : ℝ) : ℝ := min (a₀ / (2 * Real.log 200 + 2)) (1 / (2 * (4 * √2))) / (2 * κ)

set_option maxHeartbeats 1600000 in
/-- **The Coulomb-side floor**: for `c ≥ 400` and `−48c ≤ σ − c² ≤ c²/2`, `N/G₀ ≥ k(1/9, 5/2)·(1 + L)/c`. -/
theorem lower_coulomb (hc : 400 ≤ c) (hσl : -(48 * c) ≤ σ - c ^ 2) (hσu : σ - c ^ 2 ≤ c ^ 2 / 2) :
    kFloor (1 / 9) (5 / 2) * bandM c σ ≤ nodeMass c σ / energyHalf c σ := by
  have hc0 : 0 < c := by linarith
  have hc2 : 0 < c ^ 2 := by positivity
  obtain ⟨hq, hw⟩ := Cvs.Prolate.LiouvilleGreen.CoulombLayerExplicit.abs_wf_coulomb (c := c) (B := 24) (σ := σ) (by norm_num) (by norm_num; linarith)
    (by linarith)
  norm_num at hq hw
  set tc := 1 - 100 / c with htc
  have h100 : 100 / c ≤ 1 / 4 := by rw [div_le_iff₀ hc0]; linarith
  have htc0 : 3 / 4 ≤ tc := by linarith
  have htc1 : tc < 1 := by have := div_pos (by norm_num : (0 : ℝ) < 100) hc0; linarith
  have htc2 : tc ^ 2 < 1 := by nlinarith
  have hqp : 0 < qf c ((c ^ 2 - σ) / c) tc := lt_of_lt_of_le (by positivity) hq
  have hG := Cvs.Prolate.LiouvilleGreen.NodeMassAboveCoulomb.energyHalf_pos hc0.ne' (by nlinarith : c ^ 2 / 4 < σ)
  have hκ := Cvs.Prolate.LiouvilleGreen.NodeMassBandUpper.kappa_half_le
  have hκ0 : 0 < kappa (1 / 2) := Cvs.Prolate.Gram.BandCellMassFloor.kappa_half_pos
  -- the crude floor
  have hcr := Cvs.Prolate.LiouvilleGreen.StretchClosedForms.crude_le_two_stretch hc0 (Q := 9 / 8) (by norm_num) (by linarith) htc1 hqp (by nlinarith)
  have hcr' : 1 / 9 / c ≤ stretch c σ tc := by
    have : 1 / 4 / (9 / 8 * c) ≤ (tc - 1 / 2) / (9 / 8 * c) := div_le_div_of_nonneg_right (by linarith) (by positivity)
    have e : 1 / 4 / (9 / 8 * c) = 2 * (1 / 9 / c) := by field_simp; ring
    linarith
  have hbig : kappa (1 / 2) ^ 2 / qf c ((c ^ 2 - σ) / c) tc ≤ stretch c σ tc := by
    refine le_trans ?_ hcr'
    rw [div_le_div_iff₀ hqp hc0]
    have h1 : kappa (1 / 2) ^ 2 ≤ 25 / 4 := by nlinarith
    nlinarith
  have hhalf := half_le_nodeMass_div hc0 (by linarith) htc2 hqp (by norm_num) (by norm_num) hw hG hbig
  -- the log floor
  have hβ : 1 + |σ - c ^ 2| / (2 * c) ≤ c := by
    have : |σ - c ^ 2| ≤ c ^ 2 / 2 := by rw [abs_le]; constructor <;> nlinarith
    have : |σ - c ^ 2| / (2 * c) ≤ c / 4 := by rw [div_le_iff₀ (by positivity)]; nlinarith
    linarith
  have hL0 := Cvs.Prolate.LiouvilleGreen.NodeMassBandUpper.bandL_nonneg hc0 hβ
  have hlog : (bandL c σ - Real.log 200) / (4 * √2 * c) ≤ stretch c σ tc := by
    have hs2 : 0 < √2 := by positivity
    rcases le_or_gt (σ - c ^ 2) (100 * c) with h | h
    · have hD : |σ - c ^ 2| ≤ c ^ 2 * (1 - tc) := by
        rw [htc, show (1 : ℝ) - (1 - 100 / c) = 100 / c by ring, show c ^ 2 * (100 / c) = 100 * c by field_simp,
          abs_le]; constructor <;> linarith
      have h1 := Cvs.Prolate.LiouvilleGreen.StretchClosedForms.log_le_two_stretch hc0 (by linarith) htc1 hD hqp
      rw [htc, show (1 : ℝ) - (1 - 100 / c) = 100 / c by ring, show 1 / (2 * (100 / c)) = c / 200 by
        field_simp; ring] at h1
      have h2 := Cvs.Prolate.LiouvilleGreen.NodeMassBandUpper.bandL_sub_le_log (σ := σ) hc0 (R := 200) (R' := 200) (by norm_num) (by
        have := abs_nonneg (σ - c ^ 2); nlinarith [div_nonneg this (by positivity : (0 : ℝ) ≤ 2 * c)])
      have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 1 / (2 * √2 * c))
      have e : (bandL c σ - Real.log 200) / (4 * √2 * c) = 1 / (2 * √2 * c) * (bandL c σ - Real.log 200) / 2 := by
        field_simp; ring
      rw [e]; linarith
    · set D := σ - c ^ 2 with hD_def
      have hD0 : 0 < D := by linarith
      set tn := 1 - D / c ^ 2
      have htn : 1 / 2 ≤ tn := by
        have : D / c ^ 2 ≤ 1 / 2 := by rw [div_le_iff₀ hc2]; linarith
        simp only [tn]; linarith
      have htntc : tn ≤ tc := by
        have : 100 / c ≤ D / c ^ 2 := by rw [div_le_div_iff₀ hc0 hc2]; nlinarith
        simp only [tn, htc]; linarith
      have htn1 : tn < 1 := by simp only [tn]; have := div_pos hD0 hc2; linarith
      have hqn : 0 < qf c ((c ^ 2 - σ) / c) tn := by
        rw [qf_eq hc0.ne']; have : tn ^ 2 ≤ 1 := by nlinarith
        nlinarith
      have hDn : |σ - c ^ 2| ≤ c ^ 2 * (1 - tn) := by
        rw [abs_of_pos hD0]; simp only [tn]; field_simp; linarith
      have h1 := Cvs.Prolate.LiouvilleGreen.StretchClosedForms.log_le_two_stretch hc0 htn htn1 hDn hqn
      have hmono := Cvs.Prolate.LiouvilleGreen.StretchClosedForms.stretch_mono (σ := σ) hc0.ne' htn htntc htc2 hqp
      rw [show 1 / (2 * (1 - tn)) = c / (2 * D / c) by
        rw [show (1 : ℝ) - tn = D / c ^ 2 by simp only [tn]; ring]; have := hD0.ne'; field_simp] at h1
      have h2 := Cvs.Prolate.LiouvilleGreen.NodeMassBandUpper.bandL_sub_le_log (σ := σ) hc0 (R := 200) (R' := 2 * D / c) (by positivity) (by
        rw [abs_of_pos hD0]
        have e : 2 * D / c = 4 * (D / (2 * c)) := by field_simp; ring
        rw [e]; have := div_pos hD0 (by positivity : (0 : ℝ) < 2 * c); nlinarith)
      have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 1 / (2 * √2 * c))
      have e : (bandL c σ - Real.log 200) / (4 * √2 * c) = 1 / (2 * √2 * c) * (bandL c σ - Real.log 200) / 2 := by
        field_simp; ring
      rw [e]; linarith
  have hfloor := comb_floor (x := stretch c σ tc) hc0 hL0 (by norm_num : (0 : ℝ) < 1 / 9)
    (Real.log_nonneg (by norm_num) : (0 : ℝ) ≤ Real.log 200) (by positivity : (0 : ℝ) < 4 * √2) hcr'
    (fun _ => by rw [show 4 * √2 * c = (4 * √2) * c by ring] at hlog; exact hlog)
  unfold kFloor bandM
  have hκ2 : 2 * kappa (1 / 2) ≤ 2 * (5 / 2) := by linarith
  calc min (1 / 9 / (2 * Real.log 200 + 2)) (1 / (2 * (4 * √2))) / (2 * (5 / 2)) * ((1 + bandL c σ) / c)
        = min (1 / 9 / (2 * Real.log 200 + 2)) (1 / (2 * (4 * √2))) * ((1 + bandL c σ) / c) / (2 * (5 / 2)) := by
        ring
    _ ≤ stretch c σ tc / (2 * (5 / 2)) := div_le_div_of_nonneg_right hfloor (by norm_num)
    _ ≤ stretch c σ tc / (2 * kappa (1 / 2)) :=
        div_le_div_of_nonneg_left (le_trans (by positivity) hcr') (by positivity) hκ2
    _ ≤ _ := hhalf

set_option maxHeartbeats 1600000 in
/-- **The Airy-side floor**: for `c ≥ 2¹⁴`, `σ ≥ 5c²/8` and `σ − c² ≤ −48c`, `N/G₀ ≥ k(4/25, 19/10)·(1 + L)/c`. -/
theorem lower_airy (hc : 16384 ≤ c) (hσl : 5 * c ^ 2 / 8 ≤ σ) (hD : σ - c ^ 2 ≤ -(48 * c)) :
    kFloor (4 / 25) (19 / 10) * bandM c σ ≤ nodeMass c σ / energyHalf c σ := by
  have hc0 : 0 < c := by linarith
  have hc2 : 0 < c ^ 2 := by positivity
  set b := (c ^ 2 - σ) / c with hb
  have hcb : c * b = c ^ 2 - σ := by rw [hb]; field_simp
  have hb48 : 48 ≤ b := by rw [hb, le_div_iff₀ hc0]; linarith
  have hbc : b ≤ 3 * c / 8 := by rw [hb, div_le_iff₀ hc0]; nlinarith
  set X := airyX b
  obtain ⟨hX8, hXb, hXw, hK⟩ := Cvs.Prolate.LiouvilleGreen.NodeMassBandUpper.airyX_props hb48
  have hX3 := Cvs.Prolate.LiouvilleGreen.NodeMassBandUpper.airyX_cube (b := b) (by linarith)
  have hσ : σ < c ^ 2 := by nlinarith
  have h2 : c ^ 2 / 4 < σ - c * X := by
    have : c * X < c * b := mul_lt_mul_of_pos_left hXb hc0
    nlinarith
  obtain ⟨hw, -⟩ := Cvs.Prolate.LiouvilleGreen.AiryLayerBelowCoulomb.airy_layer hc0 hσ hX8 hXb.le hXw hK h2
  set t₂ := √((σ - c * X) / c ^ 2)
  have ht22 : t₂ ^ 2 = (σ - c * X) / c ^ 2 := Real.sq_sqrt (div_pos (by linarith) hc2).le
  have ht20 : 0 ≤ t₂ := Real.sqrt_nonneg _
  have hX0 : 0 < X := by linarith
  have ht21 : t₂ ^ 2 < 1 := by rw [ht22, div_lt_one hc2]; nlinarith
  have hq2e : qf c ((c ^ 2 - σ) / c) t₂ = c * X := by rw [qf_eq hc0.ne', ht22]; field_simp; ring
  have hq2 : 0 < qf c ((c ^ 2 - σ) / c) t₂ := by rw [hq2e]; positivity
  have hG := Cvs.Prolate.LiouvilleGreen.NodeMassAboveCoulomb.energyHalf_pos hc0.ne' (by nlinarith : c ^ 2 / 4 < σ)
  have hκ := Cvs.Prolate.LiouvilleGreen.NodeMassBandUpper.kappa_three_eighths_le
  have hκ0 : 0 < kappa (3 / 8) := by unfold kappa; positivity
  -- `X ≤ c/64`, so `t₂ ≥ 39/50`
  have hXc : X ≤ c / 64 := by
    have h1 : X ^ 3 ≤ (c / 64) ^ 3 := by
      rw [hX3]
      have hc28 : (2 : ℝ) ^ 28 ≤ c ^ 2 := by
        have : (2 : ℝ) ^ 28 = 16384 ^ 2 := by norm_num
        rw [this]; exact pow_le_pow_left₀ (by norm_num) hc 2
      have e : (c / 64) ^ 3 = c * c ^ 2 / 262144 := by ring
      rw [e, le_div_iff₀ (by norm_num)]
      nlinarith
    exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) h1
  have ht2l : 39 / 50 ≤ t₂ := by
    have h1 : (39 / 50 : ℝ) ^ 2 ≤ t₂ ^ 2 := by
      rw [ht22, le_div_iff₀ hc2]
      have : c * X ≤ c * (c / 64) := mul_le_mul_of_nonneg_left hXc hc0.le
      nlinarith
    exact le_of_pow_le_pow_left₀ (by norm_num) ht20 h1
  -- the crude floor
  have hcr := Cvs.Prolate.LiouvilleGreen.StretchClosedForms.crude_le_two_stretch hc0 (Q := 7 / 8) (by norm_num) (by linarith) (by nlinarith) hq2
    (by nlinarith)
  have hcr' : 4 / 25 / c ≤ stretch c σ t₂ := by
    have : 7 / 25 / (7 / 8 * c) ≤ (t₂ - 1 / 2) / (7 / 8 * c) :=
      div_le_div_of_nonneg_right (by linarith) (by positivity)
    have e : 7 / 25 / (7 / 8 * c) = 2 * (4 / 25 / c) := by field_simp; ring
    linarith
  have hX29 : 29 ≤ X := by
    have : (29 : ℝ) ^ 3 ≤ X ^ 3 := by rw [hX3]; nlinarith
    exact le_of_pow_le_pow_left₀ (by norm_num) hX0.le this
  have hbig : kappa (3 / 8) ^ 2 / qf c ((c ^ 2 - σ) / c) t₂ ≤ stretch c σ t₂ := by
    refine le_trans ?_ hcr'
    rw [hq2e, div_le_div_iff₀ (by positivity) hc0]
    have h1 : kappa (3 / 8) ^ 2 ≤ 361 / 100 := by nlinarith
    nlinarith
  have hhalf := half_le_nodeMass_div hc0 (by linarith) ht21 hq2 (by norm_num) (by norm_num) hw hG hbig
  -- the log floor
  have hβ' : |σ - c ^ 2| / (2 * c) = b / 2 := by
    rw [abs_of_neg (by linarith), show -(σ - c ^ 2) = c * b by rw [hcb]; ring]; field_simp
  have hβ : 1 + |σ - c ^ 2| / (2 * c) ≤ c := by rw [hβ']; linarith
  have hL0 := Cvs.Prolate.LiouvilleGreen.NodeMassBandUpper.bandL_nonneg hc0 hβ
  have hlog : 2 * Real.log 200 + 1 < bandL c σ →
      (bandL c σ - Real.log 200) / (4 * √2 * c) ≤ stretch c σ t₂ := by
    intro hLbig
    have hb4 : b ≤ c / 4 := by
      by_contra hcon; push Not at hcon
      have : bandL c σ ≤ Real.log 8 := by
        unfold bandL; rw [hβ']
        apply Real.log_le_log (by positivity)
        rw [div_le_iff₀ (by positivity)]; linarith
      have h8 : Real.log 8 ≤ Real.log 200 := Real.log_le_log (by norm_num) (by norm_num)
      have h0 : 0 ≤ Real.log 200 := Real.log_nonneg (by norm_num)
      linarith
    set tk := 1 - 2 * b / c
    have htk : 1 / 2 ≤ tk := by
      have : 2 * b / c ≤ 1 / 2 := by rw [div_le_iff₀ hc0]; linarith
      simp only [tk]; linarith
    have htk1 : tk < 1 := by simp only [tk]; have := div_pos (by linarith : (0 : ℝ) < 2 * b) hc0; linarith
    have htk2 : tk ^ 2 ≤ tk := by nlinarith
    have htkt : tk ≤ t₂ := by
      have h1 : tk ≤ t₂ ^ 2 := by
        rw [ht22, le_div_iff₀ hc2]
        have : c * X ≤ c * b := mul_le_mul_of_nonneg_left hXb.le hc0.le
        have e : (1 - 2 * b / c) * c ^ 2 = c ^ 2 - 2 * (c * b) := by field_simp
        simp only [tk]; rw [e]; linarith
      have h2 : tk ^ 2 ≤ t₂ ^ 2 := htk2.trans h1
      exact le_of_pow_le_pow_left₀ (by norm_num) ht20 h2
    have hqk : 0 < qf c ((c ^ 2 - σ) / c) tk := by
      rw [qf_eq hc0.ne']
      have e : c ^ 2 * tk = c ^ 2 - 2 * (c * b) := by simp only [tk]; field_simp
      have : c ^ 2 * tk ^ 2 ≤ c ^ 2 * tk := mul_le_mul_of_nonneg_left htk2 hc2.le
      nlinarith
    have hDk : |σ - c ^ 2| ≤ c ^ 2 * (1 - tk) := by
      rw [abs_of_neg (by linarith), show (1 : ℝ) - tk = 2 * b / c by simp only [tk]; ring]
      have e : c ^ 2 * (2 * b / c) = 2 * (c * b) := by field_simp
      rw [e]; nlinarith
    have h1 := Cvs.Prolate.LiouvilleGreen.StretchClosedForms.log_le_two_stretch hc0 htk htk1 hDk hqk
    have hmono := Cvs.Prolate.LiouvilleGreen.StretchClosedForms.stretch_mono (σ := σ) hc0.ne' htk htkt ht21 hq2
    rw [show 1 / (2 * (1 - tk)) = c / (4 * b) by
      rw [show (1 : ℝ) - tk = 2 * b / c by simp only [tk]; ring]; have := (by linarith : (0 : ℝ) < b).ne'
      field_simp; ring] at h1
    have h2 := Cvs.Prolate.LiouvilleGreen.NodeMassBandUpper.bandL_sub_le_log (σ := σ) hc0 (R := 200) (R' := 4 * b) (by linarith) (by
      rw [hβ']; nlinarith)
    have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 1 / (2 * √2 * c))
    have e : (bandL c σ - Real.log 200) / (4 * √2 * c) =
        1 / (2 * √2 * c) * (bandL c σ - Real.log 200) / 2 := by field_simp; ring
    rw [e]; linarith
  have hfloor := comb_floor (x := stretch c σ t₂) hc0 hL0 (by norm_num : (0 : ℝ) < 4 / 25)
    (Real.log_nonneg (by norm_num) : (0 : ℝ) ≤ Real.log 200) (by positivity : (0 : ℝ) < 4 * √2) hcr'
    (fun h => by have := hlog h; rwa [show 4 * √2 * c = (4 * √2) * c by ring] at this)
  unfold kFloor bandM
  have hκ2 : 2 * kappa (3 / 8) ≤ 2 * (19 / 10) := by linarith
  calc min (4 / 25 / (2 * Real.log 200 + 2)) (1 / (2 * (4 * √2))) / (2 * (19 / 10)) * ((1 + bandL c σ) / c)
        = min (4 / 25 / (2 * Real.log 200 + 2)) (1 / (2 * (4 * √2))) * ((1 + bandL c σ) / c) /
          (2 * (19 / 10)) := by ring
    _ ≤ stretch c σ t₂ / (2 * (19 / 10)) := div_le_div_of_nonneg_right hfloor (by norm_num)
    _ ≤ stretch c σ t₂ / (2 * kappa (3 / 8)) :=
        div_le_div_of_nonneg_left (le_trans (by positivity) hcr') (by positivity) hκ2
    _ ≤ _ := hhalf

end Cvs.Prolate.LiouvilleGreen.NodeMassBandLower

end
