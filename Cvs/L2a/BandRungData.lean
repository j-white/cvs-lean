import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.BandECouplingCollar
import Cvs.L2a.BandRungOutgoingWave
import Cvs.L2a.FullSpanIndexFloor
import Cvs.Prolate.Envelope.AngularEdgeEnvelope
import Cvs.Prolate.EvenLevelIndexLemma
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.LandauHalfEvenSpectrum
import Cvs.Prolate.LandauLowerPivot
import Cvs.Prolate.RungFamilyRangePartners

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# `‖g‖₁ ≤ 2F/|μ|` and the band rung data `(χ, λ, F)` at `c = 2πx`
On `[−1, 1]`, `|g| = |ψ|/|μ|`, so `‖g‖₁ ≤ 2 sup|ψ|/|μ|`; Landau's `λ ≥ ½` gives `1/|μ| ≤ √(c/π)`. On the band
`c² − χ < 10c` the rung has `0 < c² − χ`, `λ ≥ ½`, the envelope `|ψ| ≤ K_A|ψ(1)|` and `‖g‖₁ ≤ 2K_A√(c/π)|ψ(1)|`.
-/

noncomputable section

open MeasureTheory Set Real Interval Cvs.L2a.AngularProlateTailPositive

namespace Cvs.L2a.BandRungData

open Cvs.L2a.BandRungOutgoingWave (gL1)
open Cvs.Prolate.EvenRungsByIndex (rung rung₁ rung₂ lev muR rung_spec rung_ne_zero psi_rung)

/-- **`‖g‖₁ ≤ 2F/|μ|`** when `ψ = μg` on `[−1, 1]`, `μ ≠ 0` and `|ψ| ≤ F` on `[−1, 1]`. -/
theorem gL1_le_of_psi {g : ℝ → ℝ} {c μ F : ℝ} (hμ : ∀ s ∈ Icc (-1 : ℝ) 1, psi c g s = μ * g s) (hμ0 : μ ≠ 0)
    (hF : ∀ s ∈ Icc (-1 : ℝ) 1, |psi c g s| ≤ F) : gL1 g ≤ 2 * F / |μ| := by
  have hμa : 0 < |μ| := abs_pos.2 hμ0
  have hb : ∀ s ∈ Ι (-1 : ℝ) 1, ‖|g s|‖ ≤ F / |μ| := fun s hs => by
    rw [uIoc_of_le (by norm_num)] at hs
    have hs' : s ∈ Icc (-1 : ℝ) 1 := ⟨hs.1.le, hs.2⟩
    have h := hF s hs'
    rw [hμ s hs', abs_mul] at h
    rw [Real.norm_eq_abs, abs_abs, le_div_iff₀ hμa, mul_comm]
    exact h
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [Real.norm_eq_abs, show |(1 : ℝ) - (-1)| = 2 by norm_num] at h
  unfold gL1
  have e : F / |μ| * 2 = 2 * F / |μ| := by ring
  exact (le_abs_self _).trans (h.trans e.le)

/-- **`1/|μ| ≤ √(c/π)`** from `λ = (μ√(c/(2π)))² ≥ ½`. -/
theorem inv_abs_le_of_half {c μ : ℝ} (hc : 0 < c) (hlam : 1 / 2 ≤ (μ * √(c / (2 * π))) ^ 2) :
    0 < |μ| ∧ 1 / |μ| ≤ √(c / π) := by
  have hπ := Real.pi_pos
  have hsq : (μ * √(c / (2 * π))) ^ 2 = μ ^ 2 * (c / (2 * π)) := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  rw [hsq] at hlam
  have hμ2 : π / c ≤ μ ^ 2 := by
    rw [div_le_iff₀ hc]
    have := mul_le_mul_of_nonneg_right hlam (by positivity : (0 : ℝ) ≤ 2 * π)
    field_simp at this
    nlinarith
  have hμ0 : 0 < |μ| := by
    have : 0 < μ ^ 2 := lt_of_lt_of_le (by positivity) hμ2
    exact abs_pos.2 (by rintro rfl; simp at this)
  refine ⟨hμ0, ?_⟩
  have hroot : √(π / c) ≤ |μ| := by
    rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt hμ2
  have hinv : √(c / π) = 1 / √(π / c) := by
    have hp : 0 < √(π / c) := Real.sqrt_pos.2 (by positivity)
    rw [eq_div_iff hp.ne', ← Real.sqrt_mul (by positivity), div_mul_div_comm, mul_comm c π,
      div_self (by positivity), Real.sqrt_one]
  rw [hinv]
  exact one_div_le_one_div_of_le (Real.sqrt_pos.2 (by positivity)) hroot

/-- **The Landau form of `‖g‖₁`**: `ψ = μg` on `[−1, 1]`, `λ ≥ ½` and `|ψ| ≤ K|ψ(1)|` everywhere give
`‖g‖₁ ≤ 2K√(c/π)|ψ(1)|`. -/
theorem gL1_le_landau {g : ℝ → ℝ} {c μ K : ℝ} (hc : 0 < c) (hμ : ∀ s ∈ Icc (-1 : ℝ) 1, psi c g s = μ * g s)
    (hlam : 1 / 2 ≤ (μ * √(c / (2 * π))) ^ 2) (hK : ∀ t, |psi c g t| ≤ K * |psi c g 1|) :
    gL1 g ≤ 2 * K * √(c / π) * |psi c g 1| := by
  obtain ⟨hμ0, hinv⟩ := inv_abs_le_of_half hc hlam
  have h := gL1_le_of_psi hμ (abs_pos.1 hμ0) (fun s _ => hK s)
  have hF0 : 0 ≤ K * |psi c g 1| := (abs_nonneg _).trans (hK 1)
  calc gL1 g ≤ 2 * (K * |psi c g 1|) / |μ| := h
    _ = 2 * (K * |psi c g 1|) * (1 / |μ|) := by ring
    _ ≤ 2 * (K * |psi c g 1|) * √(c / π) := mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = 2 * K * √(c / π) * |psi c g 1| := by ring

/-! ### The band rungs at `c = 2πx` -/

/-- **The band rung's level and concentration**: for `j` in the band `c² − χ_j < 10c` at `c = 2πx ≥ 80`,
`0 ≤ χ_j`, `0 < c² − χ_j < 10c` and Landau's `λ_j = (μ_j√(c/(2π)))² ≥ ½`. -/
theorem band_rung_basic (x : ℕ) (hx : 80 ≤ 2 * π * x) (j : Finset.range x)
    (hj : j ∈ Cvs.L2a.BandECouplingCollar.bandSetG (2 * π * x) 10 (Cvs.L2a.BandECouplingCollar.chiX x)) :
    0 ≤ Cvs.L2a.BandECouplingCollar.chiX x j ∧ 0 < (2 * π * x) ^ 2 - Cvs.L2a.BandECouplingCollar.chiX x j
      ∧ (2 * π * x) ^ 2 - Cvs.L2a.BandECouplingCollar.chiX x j < 10 * (2 * π * x)
      ∧ 1 / 2 ≤ (muR (2 * π * x) (2 * (j : ℕ)) * √((2 * π * x) / (2 * π))) ^ 2 := by
  have hc0 : 0 < 2 * π * (x : ℝ) := by linarith
  have hσ0 := Cvs.L2a.FullSpanIndexFloor.sigmaLow_pos (c := 2 * π * x) (by linarith)
  have hσ := Cvs.Prolate.RungFamilyRangePartners.sigmaLow_le_main hx j
  have hband : (2 * π * x) ^ 2 - Cvs.L2a.BandECouplingCollar.chiX x j < 10 * (2 * π * x) := by
    unfold Cvs.L2a.BandECouplingCollar.bandSetG at hj
    exact (Finset.mem_filter.1 hj).2
  have hL := Cvs.Prolate.LandauLowerPivot.landau_lower_pivot x hx
  have hspec := rung_spec (Cvs.Prolate.RungFamilyRangePartners.exists_main hx j)
  refine ⟨Cvs.Prolate.RungFamilyRangePartners.lev_main_nonneg hx j, ?_, hband, ?_⟩
  · unfold Cvs.L2a.BandECouplingCollar.chiX; linarith
  · exact Cvs.Prolate.LandauHalfEvenSpectrum.half_le_lam_of_lower hc0 hL hspec.1 hspec.2.1 hspec.2.2.1 hspec.2.2.2.1
      hspec.2.2.2.2.1 (rung_ne_zero (Cvs.Prolate.RungFamilyRangePartners.exists_main hx j))
      (psi_rung (Cvs.Prolate.RungFamilyRangePartners.exists_main hx j)) (Cvs.Prolate.RungFamilyRangePartners.ncard_main_le hx j)

/-- **The band rung data from an envelope**: for a band rung at `c = 2πx ≥ 80` with `|ψ_j| ≤ K|ψ_j(1)|`, the level
facts, `λ_j ≥ ½` and `‖g_j‖₁ ≤ 2K√(c/π)|ψ_j(1)|`. -/
theorem band_rung_data_of_env (x : ℕ) (hx : 80 ≤ 2 * π * x) (j : Finset.range x)
    (hj : j ∈ Cvs.L2a.BandECouplingCollar.bandSetG (2 * π * x) 10 (Cvs.L2a.BandECouplingCollar.chiX x)) {K : ℝ}
    (hK : ∀ t, |psi (2 * π * x) (Cvs.L2a.BandECouplingCollar.gX x j) t|
      ≤ K * |psi (2 * π * x) (Cvs.L2a.BandECouplingCollar.gX x j) 1|) :
    0 ≤ Cvs.L2a.BandECouplingCollar.chiX x j ∧ 0 < (2 * π * x) ^ 2 - Cvs.L2a.BandECouplingCollar.chiX x j
      ∧ (2 * π * x) ^ 2 - Cvs.L2a.BandECouplingCollar.chiX x j < 10 * (2 * π * x)
      ∧ 1 / 2 ≤ (muR (2 * π * x) (2 * (j : ℕ)) * √((2 * π * x) / (2 * π))) ^ 2
      ∧ gL1 (Cvs.L2a.BandECouplingCollar.gX x j)
        ≤ 2 * K * √((2 * π * x) / π) * |psi (2 * π * x) (Cvs.L2a.BandECouplingCollar.gX x j) 1| := by
  obtain ⟨h1, h2, h3, h4⟩ := band_rung_basic x hx j hj
  exact ⟨h1, h2, h3, h4, gL1_le_landau (by linarith) (psi_rung (Cvs.Prolate.RungFamilyRangePartners.exists_main hx j)) h4 hK⟩

/-- **The band rung data `(χ, λ, F)`**: for `j` in the band at `c = 2πx ≥ 80`, `0 ≤ χ_j`, `0 < c² − χ_j < 10c`,
`λ_j ≥ ½`, the envelope `|ψ_j| ≤ K_A|ψ_j(1)|` and `‖g_j‖₁ ≤ 2K_A√(c/π)|ψ_j(1)|`. -/
theorem band_rung_data (x : ℕ) (hx : 80 ≤ 2 * π * x) (j : Finset.range x)
    (hj : j ∈ Cvs.L2a.BandECouplingCollar.bandSetG (2 * π * x) 10 (Cvs.L2a.BandECouplingCollar.chiX x)) :
    0 ≤ Cvs.L2a.BandECouplingCollar.chiX x j ∧ 0 < (2 * π * x) ^ 2 - Cvs.L2a.BandECouplingCollar.chiX x j
      ∧ (2 * π * x) ^ 2 - Cvs.L2a.BandECouplingCollar.chiX x j < 10 * (2 * π * x)
      ∧ 1 / 2 ≤ (muR (2 * π * x) (2 * (j : ℕ)) * √((2 * π * x) / (2 * π))) ^ 2
      ∧ (∀ t, |psi (2 * π * x) (Cvs.L2a.BandECouplingCollar.gX x j) t|
          ≤ Cvs.Prolate.Envelope.AngularEdgeEnvelope.KA * |psi (2 * π * x) (Cvs.L2a.BandECouplingCollar.gX x j) 1|)
      ∧ gL1 (Cvs.L2a.BandECouplingCollar.gX x j) ≤ 2 * Cvs.Prolate.Envelope.AngularEdgeEnvelope.KA * √((2 * π * x) / π)
          * |psi (2 * π * x) (Cvs.L2a.BandECouplingCollar.gX x j) 1| := by
  obtain ⟨h1, h2, h3, -⟩ := band_rung_basic x hx j hj
  have hspec := rung_spec (Cvs.Prolate.RungFamilyRangePartners.exists_main hx j)
  have hK : ∀ t, |psi (2 * π * x) (Cvs.L2a.BandECouplingCollar.gX x j) t|
      ≤ Cvs.Prolate.Envelope.AngularEdgeEnvelope.KA * |psi (2 * π * x) (Cvs.L2a.BandECouplingCollar.gX x j) 1| :=
    Cvs.Prolate.Envelope.AngularEdgeEnvelope.abs_psi_le_band hspec.1 hspec.2.1 hspec.2.2.1 hspec.2.2.2.1 hspec.2.2.2.2.1 h1
      (by unfold Cvs.L2a.BandECouplingCollar.chiX at h2; linarith) (psi_rung (Cvs.Prolate.RungFamilyRangePartners.exists_main hx j)) hx h3
  obtain ⟨-, -, -, h4, h5⟩ := band_rung_data_of_env x hx j hj hK
  exact ⟨h1, h2, h3, h4, hK, h5⟩

end Cvs.L2a.BandRungData
