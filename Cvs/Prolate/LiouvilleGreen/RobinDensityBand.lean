import Mathlib
import Cvs.Prolate.Gram.BandCellMassFloor
import Cvs.Prolate.Gram.RobinNodeLatticeDualFloor
import Cvs.Prolate.LiouvilleGreen.AiryLayerBelowCoulomb
import Cvs.Prolate.LiouvilleGreen.NodeMassAboveCoulomb
import Cvs.Prolate.LiouvilleGreen.NodeMassBandLower
import Cvs.Prolate.LiouvilleGreen.NodeMassBandUpper
import Cvs.Prolate.LiouvilleGreen.PruferAngleRobinRate
import Cvs.Prolate.LiouvilleGreen.RateStrictlyDecreasing
import Cvs.Prolate.LiouvilleGreen.RobinCellPhaseIncrement
import Cvs.Prolate.LiouvilleGreen.RobinDensityHighLevel
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
# LemQ's (H2) on the band `5/8 ≤ σ/c² ≤ 3/2`

Cvs.Prolate.LiouvilleGreen.NodeMassBandUpper–Cvs.Prolate.LiouvilleGreen.NodeMassBandLower pin `N/G₀` between multiples of `M = (1 + L)/c`; there `r = 4a₀/(3c) ∈ [½, 2]`, so the Robin rate is
within `[k₁M/2, 2k₂M]`; `M` moves by at most a factor `1 + log(1 + π/k₁)` across a cell, and `RobinCellPhaseIncrement`'s cell identity
gives (H2) with a constant.
-/

noncomputable section

open Real Set Filter Topology
open Cvs.Prolate.RegularSolutionEdge (regSol sqC)
open Cvs.Prolate.TopRungDepthBound (af qf)
open Cvs.Prolate.LiouvilleGreen.RateStrictlyDecreasing (kappa)
open Cvs.Prolate.LiouvilleGreen.AdiabaticStretchBounds (qf_eq stretch)
open Cvs.Prolate.LiouvilleGreen.PruferAngleRobinRate (nodeMass energyHalf af_half)
open Cvs.Prolate.LiouvilleGreen.RobinCellPhaseIncrement (nodeRate ConsecNodes)
open Cvs.Prolate.LiouvilleGreen.RobinDensityHighLevel (H2 H2Upper H2Lower)
open Cvs.Prolate.LiouvilleGreen.NodeMassBandUpper (bandL bandM)

namespace Cvs.Prolate.LiouvilleGreen.RobinDensityBand
open Cvs.ZeroCounting

variable {c σ : ℝ}

/-- **`N/G₀ ≍ M` on the band**: there are `0 < k₁ ≤ k₂` with `k₁M ≤ N/G₀ ≤ k₂M` for `c ≥ 2¹⁴` and
`5c²/8 ≤ σ ≤ 3c²/2`. -/
theorem band_bounds : ∃ k₁ k₂ : ℝ, 0 < k₁ ∧ 0 < k₂ ∧ ∀ c σ : ℝ, 16384 ≤ c → 5 * c ^ 2 / 8 ≤ σ →
    σ ≤ 3 * c ^ 2 / 2 → k₁ * bandM c σ ≤ nodeMass c σ / energyHalf c σ ∧
      nodeMass c σ / energyHalf c σ ≤ k₂ * bandM c σ := by
  obtain ⟨KC, hKC, hup⟩ := Cvs.Prolate.LiouvilleGreen.NodeMassBandUpper.upper_coulomb
  have hk1 : 0 < Cvs.Prolate.LiouvilleGreen.NodeMassBandLower.kFloor (1 / 9) (5 / 2) := by
    unfold Cvs.Prolate.LiouvilleGreen.NodeMassBandLower.kFloor; have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 200); positivity
  have hk2 : 0 < Cvs.Prolate.LiouvilleGreen.NodeMassBandLower.kFloor (4 / 25) (19 / 10) := by
    unfold Cvs.Prolate.LiouvilleGreen.NodeMassBandLower.kFloor; have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 200); positivity
  have hCA : 0 ≤ Cvs.Prolate.LiouvilleGreen.AiryLayerBelowCoulomb.airyConst 1024 := by unfold Cvs.Prolate.LiouvilleGreen.AiryLayerBelowCoulomb.airyConst; positivity
  have hκ1 : 0 < kappa (1 / 2) := Cvs.Prolate.Gram.BandCellMassFloor.kappa_half_pos
  have hκ2 : 0 < kappa (11 / 10) := by unfold kappa; positivity
  have hκ3 : 0 < kappa (3 / 8) := by unfold kappa; positivity
  set K₂ := kappa (1 / 2) * (√2 + KC) + 3 * kappa (11 / 10) + kappa (3 / 8) * (√2 + 2 + Cvs.Prolate.LiouvilleGreen.AiryLayerBelowCoulomb.airyConst 1024)
  refine ⟨min (Cvs.Prolate.LiouvilleGreen.NodeMassBandLower.kFloor (1 / 9) (5 / 2)) (Cvs.Prolate.LiouvilleGreen.NodeMassBandLower.kFloor (4 / 25) (19 / 10)), K₂, lt_min hk1 hk2,
    by positivity, fun c σ hc hσl hσu => ?_⟩
  have hc0 : 0 < c := by linarith
  have hβ : 1 + |σ - c ^ 2| / (2 * c) ≤ c := by
    have : |σ - c ^ 2| ≤ c ^ 2 / 2 := by rw [abs_le]; constructor <;> nlinarith
    have : |σ - c ^ 2| / (2 * c) ≤ c / 4 := by rw [div_le_iff₀ (by positivity)]; nlinarith
    linarith
  have hL := Cvs.Prolate.LiouvilleGreen.NodeMassBandUpper.bandL_nonneg hc0 hβ
  have hM : bandM c σ = (1 + bandL c σ) / c := rfl
  have hMpos : 0 ≤ bandM c σ := by rw [hM]; positivity
  have hs2 : 0 ≤ √2 := Real.sqrt_nonneg _
  constructor
  · rcases le_or_gt (-(48 * c)) (σ - c ^ 2) with h | h
    · exact le_trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hMpos)
        (Cvs.Prolate.LiouvilleGreen.NodeMassBandLower.lower_coulomb (by linarith) h (by linarith))
    · exact le_trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hMpos)
        (Cvs.Prolate.LiouvilleGreen.NodeMassBandLower.lower_airy hc hσl h.le)
  · -- each ceiling is `(αL + γ)/c ≤ K₂(1 + L)/c`
    have key : ∀ α γ : ℝ, 0 ≤ α → 0 ≤ γ → α ≤ K₂ → γ ≤ K₂ → (α * bandL c σ + γ) / c ≤ K₂ * bandM c σ := by
      intro α γ hα hγ hαK hγK
      rw [hM, mul_div_assoc']
      apply div_le_div_of_nonneg_right _ hc0.le
      nlinarith
    have hK1 : kappa (1 / 2) * (√2 + KC) ≤ K₂ := by simp only [K₂]; nlinarith
    have hK2 : 3 * kappa (11 / 10) ≤ K₂ := by simp only [K₂]; nlinarith
    have hK3 : kappa (3 / 8) * (√2 + 2 + Cvs.Prolate.LiouvilleGreen.AiryLayerBelowCoulomb.airyConst 1024) ≤ K₂ := by simp only [K₂]; nlinarith
    rcases le_or_gt (|σ - c ^ 2|) (48 * c) with h | h
    · refine (hup c σ (by linarith) h).trans ?_
      rw [show kappa (1 / 2) * (√2 * bandL c σ + KC) / c =
        (kappa (1 / 2) * √2 * bandL c σ + kappa (1 / 2) * KC) / c by ring]
      exact key _ _ (by positivity) (by positivity) (by nlinarith) (by nlinarith)
    · rcases le_or_gt 0 (σ - c ^ 2) with h0 | h0
      · rw [abs_of_nonneg h0] at h
        refine (Cvs.Prolate.LiouvilleGreen.NodeMassBandUpper.upper_bessel (by linarith) h.le (by linarith)).trans ?_
        rw [show kappa (11 / 10) * (bandL c σ + 3) / c =
          (kappa (11 / 10) * bandL c σ + 3 * kappa (11 / 10)) / c by ring]
        exact key _ _ (by positivity) (by positivity) (by nlinarith) hK2
      · rw [abs_of_neg h0] at h
        refine (Cvs.Prolate.LiouvilleGreen.NodeMassBandUpper.upper_airy hc hσl (by linarith)).trans ?_
        rw [show kappa (3 / 8) * (√2 * bandL c σ + 2 + Cvs.Prolate.LiouvilleGreen.AiryLayerBelowCoulomb.airyConst 1024) / c =
          (kappa (3 / 8) * √2 * bandL c σ + kappa (3 / 8) * (2 + Cvs.Prolate.LiouvilleGreen.AiryLayerBelowCoulomb.airyConst 1024)) / c by ring]
        exact key _ _ (by positivity) (by positivity) (by nlinarith) (by nlinarith)

/-- **The Robin rate on the band**: `N/(2G₀) ≤ nodeRate ≤ 2N/G₀` for `5c²/8 ≤ σ ≤ 3c²/2`. -/
theorem rate_band (hc : 0 < c) (hσl : 5 * c ^ 2 / 8 ≤ σ) (hσu : σ ≤ 3 * c ^ 2 / 2) :
    nodeMass c σ / energyHalf c σ / 2 ≤ nodeRate c σ ∧ nodeRate c σ ≤ 2 * (nodeMass c σ / energyHalf c σ) := by
  have hc2 : 0 < c ^ 2 := by positivity
  have hσq : c ^ 2 / 4 < σ := by nlinarith
  have hG := Cvs.Prolate.LiouvilleGreen.NodeMassAboveCoulomb.energyHalf_pos hc.ne' hσq
  have he := Cvs.Prolate.LiouvilleGreen.RobinDensityHighLevel.nodeRate_mul_energyHalf hc hσq
  set r := 4 * af c ((c ^ 2 - σ) / c) (1 / 2) / (3 * c)
  set X := (c * regSol (sqC c) σ (1 / 2)) ^ 2
  set Y := Cvs.Prolate.RegularSolutionEdge.regV (sqC c) σ (1 / 2) ^ 2
  have hR : 0 < X + Y := Cvs.Prolate.LiouvilleGreen.RobinCellPhaseIncrement.refNorm_pos hc.ne' σ
  have hX : 0 ≤ X := sq_nonneg _
  have hY : 0 ≤ Y := sq_nonneg _
  have hN := (Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.nodeMass_pos c σ).le
  -- `r ∈ [½, 2]`
  have hr2 : r ^ 2 = 4 / 3 * (σ - c ^ 2 / 4) / c ^ 2 := by
    simp only [r]; rw [af_half hc.ne', div_pow, mul_pow, Real.sq_sqrt (by linarith)]; field_simp
  have hr0 : 0 ≤ r := by
    simp only [r]; exact div_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) (by positivity)
  have hrl : 1 / 2 ≤ r := by
    have : (1 / 2 : ℝ) ^ 2 ≤ r ^ 2 := by rw [hr2, le_div_iff₀ hc2]; nlinarith
    exact le_of_pow_le_pow_left₀ (by norm_num) hr0 this
  have hru : r ≤ 2 := by
    have : r ^ 2 ≤ 2 ^ 2 := by rw [hr2, div_le_iff₀ hc2]; nlinarith
    exact le_of_pow_le_pow_left₀ (by norm_num) (by norm_num) this
  have hr0' : 0 < r := by linarith
  have hF1 : (X + Y) / 2 ≤ r * X + Y / r := by
    have h1 : X / 2 ≤ r * X := by nlinarith
    have h2 : Y / 2 ≤ Y / r := div_le_div_of_nonneg_left hY hr0' hru
    linarith
  have hF2 : r * X + Y / r ≤ 2 * (X + Y) := by
    have h1 : r * X ≤ 2 * X := by nlinarith
    have h2 : Y / r ≤ 2 * Y := by rw [div_le_iff₀ hr0']; nlinarith
    linarith
  constructor
  · rw [div_div, div_le_iff₀ (by positivity)]
    have : nodeMass c σ * ((X + Y) / 2) ≤ nodeMass c σ * (r * X + Y / r) := mul_le_mul_of_nonneg_left hF1 hN
    have e : nodeRate c σ * energyHalf c σ * (X + Y) = nodeMass c σ * (r * X + Y / r) := by
      rw [he]; field_simp
    nlinarith
  · rw [mul_div_assoc', le_div_iff₀ hG]
    have : nodeMass c σ * (r * X + Y / r) ≤ nodeMass c σ * (2 * (X + Y)) := mul_le_mul_of_nonneg_left hF2 hN
    have e : nodeRate c σ * energyHalf c σ * (X + Y) = nodeMass c σ * (r * X + Y / r) := by
      rw [he]; field_simp
    nlinarith

/-- **`M` varies slowly**: if `|σ' − σ| ≤ 2cδ` (`δ ≥ 0`) and `L(σ') ≥ 0`, then `M(σ) ≤ (1 + log(1 + δ))M(σ')`. -/
theorem bandM_slow (hc : 0 < c) {σ' δ : ℝ} (hδ : 0 ≤ δ) (hd : |σ' - σ| ≤ 2 * c * δ) (hL : 0 ≤ bandL c σ') :
    bandM c σ ≤ (1 + Real.log (1 + δ)) * bandM c σ' := by
  set β := |σ - c ^ 2| / (2 * c)
  set β' := |σ' - c ^ 2| / (2 * c)
  have hβ0 : 0 ≤ β := by positivity
  have hβ'0 : 0 ≤ β' := by positivity
  have hββ : β ≤ β' + δ := by
    simp only [β, β']
    rw [div_le_iff₀ (by positivity), add_mul, div_mul_cancel₀ _ (by positivity)]
    have := abs_sub_abs_le_abs_sub (σ - c ^ 2) (σ' - c ^ 2)
    rw [show σ - c ^ 2 - (σ' - c ^ 2) = -(σ' - σ) by ring, abs_neg] at this
    nlinarith
  have hb : 1 + β ≤ (1 + δ) * (1 + β') := by nlinarith
  have hℓ : 0 ≤ Real.log (1 + δ) := Real.log_nonneg (by linarith)
  -- `L(σ') ≤ L(σ) + log(1 + δ)`
  have hLL : bandL c σ' ≤ bandL c σ + Real.log (1 + δ) := by
    unfold bandL
    rw [← Real.log_mul (by positivity) (by positivity)]
    apply Real.log_le_log (by positivity)
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hL0 : 0 ≤ bandL c σ ∨ bandL c σ < 0 := le_or_gt 0 _
  unfold bandM
  rw [mul_div_assoc']
  apply div_le_div_of_nonneg_right _ hc.le
  -- `1 + L ≤ (1 + ℓ)(1 + L')` from `L ≤ L' + ℓ`, `L' ≥ 0`
  have hLL' : bandL c σ ≤ bandL c σ' + Real.log (1 + δ) := by
    unfold bandL
    rw [← Real.log_mul (by positivity) (by positivity)]
    apply Real.log_le_log (by positivity)
    have hb' : 1 + β' ≤ (1 + δ) * (1 + β) := by
      have : β' ≤ β + δ := by
        simp only [β, β']
        rw [div_le_iff₀ (by positivity), add_mul, div_mul_cancel₀ _ (by positivity)]
        have := abs_sub_abs_le_abs_sub (σ' - c ^ 2) (σ - c ^ 2)
        rw [show σ' - c ^ 2 - (σ - c ^ 2) = σ' - σ by ring] at this
        nlinarith
      nlinarith
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  nlinarith

set_option maxHeartbeats 1600000 in
/-- **lemQ (H2) on the band** `5/8 ≤ τ ≤ 3/2`, Coulomb layer and soft edge included. -/
theorem h2_band : H2 (Icc (5 / 8) (3 / 2)) := by
  obtain ⟨k₁, k₂, hk₁, hk₂, hb⟩ := band_bounds
  set ℓ := Real.log (1 + π / k₁)
  have hℓ : 0 ≤ ℓ := Real.log_nonneg (by have := div_pos pi_pos hk₁; linarith)
  set C := 4 * k₂ * (1 + ℓ) ^ 2 / k₁
  have hC : 0 < C := by positivity
  refine ⟨C, 16384, hC, ?_, ?_⟩
  all_goals
    intro c χ σ σ' hc hcell hσI hσ'I
    have hc0 : 0 < c := by linarith
    have hc2 : 0 < c ^ 2 := by positivity
    have hlt := hcell.1
    have hσl : 5 * c ^ 2 / 8 ≤ σ := by
      have := (le_div_iff₀ hc2).mp hσI.1; linarith
    have hσ'u : σ' ≤ 3 * c ^ 2 / 2 := by
      have := (div_le_iff₀ hc2).mp hσ'I.2; linarith
    have hin : ∀ s ∈ Icc σ σ', 5 * c ^ 2 / 8 ≤ s ∧ s ≤ 3 * c ^ 2 / 2 := fun s hs =>
      ⟨hσl.trans hs.1, hs.2.trans hσ'u⟩
    have hLnn : ∀ s ∈ Icc σ σ', 0 ≤ bandL c s := by
      intro s hs
      obtain ⟨h1, h2⟩ := hin s hs
      apply Cvs.Prolate.LiouvilleGreen.NodeMassBandUpper.bandL_nonneg hc0
      have : |s - c ^ 2| ≤ c ^ 2 / 2 := by rw [abs_le]; constructor <;> nlinarith
      have : |s - c ^ 2| / (2 * c) ≤ c / 4 := by rw [div_le_iff₀ (by positivity)]; nlinarith
      linarith
    have hrate : ∀ s ∈ Icc σ σ', k₁ * bandM c s / 2 ≤ nodeRate c s ∧ nodeRate c s ≤ 2 * k₂ * bandM c s := by
      intro s hs
      obtain ⟨h1, h2⟩ := hin s hs
      obtain ⟨hm1, hm2⟩ := hb c s hc h1 h2
      obtain ⟨hr1, hr2⟩ := rate_band hc0 h1 h2
      constructor <;> nlinarith
    have hM1 : ∀ s ∈ Icc σ σ', 1 / c ≤ bandM c s := fun s hs => by
      unfold bandM; exact div_le_div_of_nonneg_right (by linarith [hLnn s hs]) hc0.le
    -- the cell is short
    have hlen : σ' - σ ≤ π / (k₁ / (2 * c)) := by
      refine Cvs.Prolate.LiouvilleGreen.RobinCellPhaseIncrement.cell_length_le hc0 hcell (by positivity) fun s hs _ => ?_
      have hsI : s ∈ Icc σ σ' := ⟨hs.1.le, hs.2.le⟩
      have h1 := (hrate s hsI).1
      have h2 := mul_le_mul_of_nonneg_left (hM1 s hsI) hk₁.le
      calc k₁ / (2 * c) = k₁ * (1 / c) / 2 := by ring
        _ ≤ k₁ * bandM c s / 2 := by linarith
        _ ≤ nodeRate c s := h1
    have hlen' : σ' - σ ≤ 2 * c * (π / k₁) := by
      rw [show 2 * c * (π / k₁) = π / (k₁ / (2 * c)) by field_simp]; exact hlen
    have hslow : ∀ u ∈ Icc σ σ', ∀ v ∈ Icc σ σ', bandM c u ≤ (1 + ℓ) * bandM c v := by
      intro u hu v hv
      refine bandM_slow hc0 (by positivity) ?_ (hLnn v hv)
      rw [abs_le]; constructor <;> linarith [hu.1, hu.2, hv.1, hv.2]
    obtain ⟨ξ, hξ, hξe⟩ := Cvs.Prolate.LiouvilleGreen.RobinCellPhaseIncrement.exists_nodeRate_mul_eq hc0 hcell
    have hξI : ξ ∈ Icc σ σ' := ⟨hξ.1.le, hξ.2.le⟩
    have hrξ : 0 < nodeRate c ξ := Cvs.Prolate.LiouvilleGreen.RobinCellPhaseIncrement.nodeRate_pos hc0 ξ
    have hratio : ∀ ν, nodeRate c ν / π * (σ' - σ) = nodeRate c ν / nodeRate c ξ := by
      intro ν
      have : σ' - σ = π / nodeRate c ξ := by rw [eq_div_iff hrξ.ne']; linarith
      rw [this]; field_simp
    have hMξ : 0 < bandM c ξ := lt_of_lt_of_le (by positivity) (hM1 ξ hξI)
    have hupper : ∀ ν ∈ Icc σ σ', nodeRate c ν / nodeRate c ξ ≤ C := by
      intro ν hν
      rw [div_le_iff₀ hrξ]
      have h1 := (hrate ν hν).2
      have h2 := (hrate ξ hξI).1
      have h3 := hslow ν hν ξ hξI
      have h4 : 1 + ℓ ≤ (1 + ℓ) ^ 2 := by nlinarith
      calc nodeRate c ν ≤ 2 * k₂ * bandM c ν := h1
        _ ≤ 2 * k₂ * ((1 + ℓ) * bandM c ξ) := by gcongr
        _ ≤ 2 * k₂ * ((1 + ℓ) ^ 2 * bandM c ξ) := by gcongr
        _ = C * (k₁ * bandM c ξ / 2) := by simp only [C]; field_simp; ring
        _ ≤ C * nodeRate c ξ := by gcongr
    have hlower : ∀ ν ∈ Icc σ σ', 1 / C ≤ nodeRate c ν / nodeRate c ξ := by
      intro ν hν
      rw [le_div_iff₀ hrξ]
      have h1 := (hrate ν hν).1
      have h2 := (hrate ξ hξI).2
      have h3 := hslow ξ hξI ν hν
      have h4 : 1 + ℓ ≤ (1 + ℓ) ^ 2 := by nlinarith
      have hMν : 0 < bandM c ν := lt_of_lt_of_le (by positivity) (hM1 ν hν)
      calc 1 / C * nodeRate c ξ ≤ 1 / C * (2 * k₂ * bandM c ξ) := by gcongr
        _ ≤ 1 / C * (2 * k₂ * ((1 + ℓ) ^ 2 * bandM c ν)) := by
            gcongr; exact h3.trans (mul_le_mul_of_nonneg_right h4 hMν.le)
        _ = k₁ * bandM c ν / 2 := by simp only [C]; field_simp; ring
        _ ≤ nodeRate c ν := h1
  · have hτ : ∀ ν ∈ Icc σ σ', C ≤ C * (1 + ν / c ^ 2) := fun ν hν => by
      have : 0 ≤ ν / c ^ 2 := div_nonneg (by nlinarith [(hin ν hν).1]) hc2.le
      nlinarith
    refine ⟨?_, ?_⟩
    · rw [hratio]; exact (hupper σ ⟨le_rfl, hlt.le⟩).trans (hτ σ ⟨le_rfl, hlt.le⟩)
    · rw [hratio]; exact (hupper σ' ⟨hlt.le, le_rfl⟩).trans (hτ σ' ⟨hlt.le, le_rfl⟩)
  · have hτ : ∀ ν ∈ Icc σ σ', 1 / (C * (1 + ν / c ^ 2)) ≤ 1 / C := fun ν hν => by
      have : 0 ≤ ν / c ^ 2 := div_nonneg (by nlinarith [(hin ν hν).1]) hc2.le
      apply one_div_le_one_div_of_le hC; nlinarith
    refine ⟨?_, ?_⟩
    · rw [hratio]; exact (hτ σ ⟨le_rfl, hlt.le⟩).trans (hlower σ ⟨le_rfl, hlt.le⟩)
    · rw [hratio]; exact (hτ σ' ⟨hlt.le, le_rfl⟩).trans (hlower σ' ⟨hlt.le, le_rfl⟩)

end Cvs.Prolate.LiouvilleGreen.RobinDensityBand

end
