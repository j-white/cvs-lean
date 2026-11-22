import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.BandCouplingDischarged
import Cvs.L2a.BandRungOutgoingWave
import Cvs.L2a.BandTransferBandForm
import Cvs.L2a.FullSpanIndexFloor
import Cvs.L2a.FullSpanThreshold
import Cvs.L2a.OrbitGapIntegerM
import Cvs.Prolate.BandMassLaw
import Cvs.Prolate.CosineChristoffelDarboux
import Cvs.Prolate.EvenLevelIndexLemma
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.RungConnectionIdentity
import Cvs.Prolate.RungExactOrthogonality
import Cvs.Prolate.RungFamilyRangePartners
import Cvs.Prolate.RungMirrorIdentity
import Cvs.Prolate.RungOrthogonalityAtInfinity

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The E-coupling on the band `c² − χ < 10c` with the collar schedule `δ = t = c^{−1/3}`
With `δ = t = c^{−1/3}`, `d = 1/2`, `r = 1/4` in THEOREM E (Cvs.L2a.BandRungOutgoingWave), the collar's sharp part is at most
`40c^{−1/6}` times the main term `√(ψ(1)²Λ̂C_E/c)`, and the mass law at band edge `10` bounds the main term by
`√(ē_main·Mⱼ)`. The remaining terms of the bracket at most `K_r c^{−1/8}` times the main term give the E-coupling
`ē_main(1 + ω)²`, `ω = (40 + K_r)c^{−1/8} ≤ 1/1000` past `c₀^F`.
-/

noncomputable section

open MeasureTheory Set Real Cvs.L2a.AngularProlateTailPositive

namespace Cvs.L2a.BandECouplingCollar

open Cvs.L2a.BandRungOutgoingWave (lamHat lamB cE lM gL1 collarK tauBar nuCut topE bulkE)
open Cvs.Prolate.BandMassLaw (wUp twoK wBar)
open Cvs.Prolate.EvenRungsByIndex (rung rung₁ rung₂ lev muR rung_spec rung_ne_zero psi_rung)

/-! ### The band, the main constant, the schedule -/

/-- The band at edge `s`: the indices with `c² − χᵢ < s·c`. -/
def bandSetG {ι : Type} [Fintype ι] (c s : ℝ) (χ : ι → ℝ) : Finset ι := by
  classical exact Finset.univ.filter fun i => c ^ 2 - χ i < s * c

/-- The main E-coupling constant at band edge `s`, `ē_main = 2πΛ̂(w(c, 2))C_E/(log(1 + c) − 2k(2, s))`. -/
def eMain (c s : ℝ) : ℝ := 2 * π * lamHat (wUp c 2) * cE / (Real.log (1 + c) - twoK c 2 s)

/-- The collar schedule `δ(c) = t(c) = c^{−1/3}`. -/
def deltaS (c : ℝ) : ℝ := c ^ (-(1 / 3 : ℝ))

/-- The collar ratio constant. -/
def kCol : ℝ := 40

/-- The relative E-residual `ω(K_r, c) = (40 + K_r)c^{−1/8}`. -/
def omegaE (Kr c : ℝ) : ℝ := (kCol + Kr) * c ^ (-(1 / 8 : ℝ))

/-- The main term of THEOREM E's bracket, `√(ψ(1)²Λ̂(w(c, 2))C_E/c)`. -/
def mainA (c : ℝ) (g : ℝ → ℝ) : ℝ := √(psi c g 1 ^ 2 * lamHat (wUp c 2) * cE / c)

/-- The sharp collar part of `N_{m,0}·m`, `4|ψ(1)|√Λ̂(w(c, 3/2))/(√5c)` (Cvs.L2a.BandRungOutgoingWave.norm_nuSi_le_collar). -/
def K0si (c : ℝ) (g : ℝ → ℝ) : ℝ := 4 * |psi c g 1| * √(lamHat (wUp c (3 / 2))) / (√5 * c)

/-! ### Elementary facts -/

theorem lamB_ge_one {w : ℝ} (hw0 : 0 ≤ w) (hw : w ≤ 1) : 1 ≤ lamB w := by
  unfold lamB
  have h1 : 0 < 1 - w / 2 := by linarith
  have h2 : 1 - w / 2 ≤ 1 := by linarith
  rw [le_div_iff₀ (by positivity)]; nlinarith

theorem one_le_lamHat {w : ℝ} (hw0 : 0 ≤ w) (hw : w ≤ 1) : 1 ≤ lamHat w := by
  unfold lamHat
  have := lamB_ge_one hw0 hw
  have := Real.sqrt_nonneg (lamB w ^ 2 - 1)
  linarith

/-- `Λ̂(w) ≤ 2` for `0 ≤ w ≤ 1/5`. -/
theorem lamHat_le_two {w : ℝ} (hw0 : 0 ≤ w) (hw : w ≤ 1 / 5) : lamHat w ≤ 2 := by
  have hB : lamB w ≤ 5 / 4 := by
    unfold lamB
    have h1 : 9 / 10 ≤ 1 - w / 2 := by linarith
    have h2 : (4 : ℝ) / 5 ≤ (1 - w / 2) ^ 2 := by nlinarith
    rw [div_le_iff₀ (by positivity)]; linarith
  have hB1 := lamB_ge_one hw0 (by linarith)
  have hs : √(lamB w ^ 2 - 1) ≤ 3 / 4 := by
    rw [Real.sqrt_le_left (by norm_num)]; nlinarith
  unfold lamHat; linarith

theorem wUp_two_eq (c : ℝ) : wUp c 2 = 4 / (3 * c) := by
  unfold wUp Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval.pP; ring

theorem wUp_three_halves_eq (c : ℝ) : wUp c (3 / 2) = 12 / (5 * c) := by
  unfold wUp Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval.pP; field_simp; ring

/-- `C_E ≥ 1/200`, from `C_E ≥ L₂/π` and `L₂ = log(3(19 − 8√3)/13)/4`. -/
theorem cE_ge : (1 / 200 : ℝ) ≤ cE := by
  have h0 : lM 2 ≤ ∑' n : ℕ, lM ((n : ℝ) + 2) := by
    have := Cvs.L2a.BandRungOutgoingWave.summable_lM.sum_le_tsum {0}
      (fun i _ => Cvs.L2a.BandRungOutgoingWave.lM_nonneg' i)
    simpa using this
  have hs3 : √3 ≤ 7 / 4 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hy : (15 / 13 : ℝ) ≤ 3 * (19 - 8 * √3) / 13 := by
    rw [div_le_div_iff_of_pos_right (by norm_num)]; linarith
  have hy0 : (0 : ℝ) < 3 * (19 - 8 * √3) / 13 := lt_of_lt_of_le (by norm_num) hy
  have hl := Real.one_sub_inv_le_log_of_pos hy0
  have hinv : (3 * (19 - 8 * √3) / 13)⁻¹ ≤ 13 / 15 := by
    rw [inv_le_comm₀ hy0 (by norm_num)]; norm_num; linarith
  have hL2 : (2 / 15) / 4 ≤ lM 2 := by
    rw [Cvs.L2a.BandRungOutgoingWave.lM_two]; linarith
  have hpi := Real.pi_lt_d2
  have hpi0 := Real.pi_pos
  unfold cE
  rw [le_div_iff₀ hpi0]
  nlinarith

theorem cE_pos : 0 < cE := lt_of_lt_of_le (by norm_num) cE_ge

/-- `2k(2, 10) ≤ 15/4`. -/
theorem twoK_two_ten_le {c : ℝ} (hc : 0 < c) : twoK c 2 10 ≤ 15 / 4 := by
  have h := Cvs.Prolate.BandMassLaw.twoK_le (c := c) (r₀ := 2) (s := 10) hc (by norm_num) (by norm_num)
  have hw := Cvs.L2a.BandCouplingDischarged.wBar_two_le_one hc
  have h1 : 1 / 2 ≤ 1 - wBar c 2 / 2 := by linarith
  have h2 : 1 / (1 - wBar c 2 / 2) ^ 2 ≤ 4 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  linarith

/-- The denominator of `ē_main` at edge `10` is positive for `c ≥ 80`. -/
theorem eMain_den_pos {c : ℝ} (hc : 80 ≤ c) : 0 < Real.log (1 + c) - twoK c 2 10 := by
  have := twoK_two_ten_le (by linarith : (0 : ℝ) < c)
  have := Cvs.L2a.BandCouplingDischarged.four_lt_log hc
  linarith

theorem eMain_nonneg {c : ℝ} (hc : 80 ≤ c) : 0 ≤ eMain c 10 := by
  have := eMain_den_pos hc
  have := Cvs.L2a.BandRungOutgoingWave.lamHat_nonneg (wUp c 2)
  have := cE_pos
  unfold eMain; positivity

/-! ### The schedule `c^{−1/3}` -/

theorem deltaS_pos {c : ℝ} (hc : 0 < c) : 0 < deltaS c := Real.rpow_pos_of_pos hc _

theorem deltaS_lt_one {c : ℝ} (hc : 1 < c) : deltaS c < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg hc (by norm_num)

/-- `√δ(c) = c^{−1/6} ≤ c^{−1/8}` for `c ≥ 1`. -/
theorem sqrt_deltaS_le {c : ℝ} (hc : 1 ≤ c) : √(deltaS c) ≤ c ^ (-(1 / 8 : ℝ)) := by
  have hc0 : 0 ≤ c := by linarith
  unfold deltaS
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hc0]
  exact Real.rpow_le_rpow_of_exponent_le hc (by norm_num)

/-- `K_col(δ, δ) ≤ (4κ_S + 1/6)δ/π` for `0 ≤ δ ≤ 1`. -/
theorem collarK_diag_le {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    collarK δ δ ≤ (4 * (181 / 462) + 1 / 6) * δ / π := by
  unfold collarK
  apply div_le_div_of_nonneg_right _ Real.pi_pos.le
  nlinarith

/-! ### The collar against the main term -/

/-- **The collar schedule**: for `c ≥ 80` and `δ = t = c^{−1/3}`, the sharp collar term of THEOREM E is at most
`40√δ` times the main term: `K₀^si√(cK_col(δ, δ)) ≤ 40√δ·√(ψ(1)²Λ̂(w(c, 2))C_E/c)`. -/
theorem collar_le_main {c : ℝ} (hc : 80 ≤ c) (g : ℝ → ℝ) :
    K0si c g * √(c * collarK (deltaS c) (deltaS c)) ≤ kCol * √(deltaS c) * mainA c g := by
  have hc0 : 0 < c := by linarith
  set δ := deltaS c with hδ
  have hδ0 : 0 < δ := deltaS_pos hc0
  have hδ1 : δ ≤ 1 := (deltaS_lt_one (by linarith)).le
  set L₃ := lamHat (wUp c (3 / 2)) with hL₃
  set L₂ := lamHat (wUp c 2) with hL₂
  have hw3 : 0 ≤ wUp c (3 / 2) ∧ wUp c (3 / 2) ≤ 1 / 5 := by
    rw [wUp_three_halves_eq]
    exact ⟨by positivity, by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith⟩
  have hw2 : 0 ≤ wUp c 2 ∧ wUp c 2 ≤ 1 := by
    rw [wUp_two_eq]
    exact ⟨by positivity, by rw [div_le_iff₀ (by positivity)]; linarith⟩
  have hL3 : L₃ ≤ 2 := lamHat_le_two hw3.1 hw3.2
  have hL30 : 0 ≤ L₃ := Cvs.L2a.BandRungOutgoingWave.lamHat_nonneg _
  have hL2 : 1 ≤ L₂ := one_le_lamHat hw2.1 hw2.2
  have hK := collarK_diag_le hδ0.le hδ1
  have hK0 : 0 ≤ collarK δ δ := by unfold collarK; positivity
  have hcE := cE_ge
  set ψ1 := psi c g 1 with hψ1
  have hpi := Real.pi_gt_three
  -- squares
  have hl : (K0si c g * √(c * collarK δ δ)) ^ 2 = 16 * ψ1 ^ 2 * L₃ * collarK δ δ / (5 * c) := by
    unfold K0si
    rw [mul_pow, div_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt hL30, Real.sq_sqrt (by norm_num),
      Real.sq_sqrt (by positivity), sq_abs]
    field_simp; ring
  have hr : (kCol * √δ * mainA c g) ^ 2 = 1600 * δ * (ψ1 ^ 2 * L₂ * cE / c) := by
    unfold mainA kCol
    rw [mul_pow, mul_pow, Real.sq_sqrt hδ0.le, Real.sq_sqrt (by have := cE_pos; have := hL2; positivity)]
    ring
  have hψ0 : 0 ≤ ψ1 ^ 2 := sq_nonneg _
  have key : 16 * L₃ * collarK δ δ ≤ 5 * 1600 * δ * L₂ * cE := by
    have h1 : 16 * L₃ * collarK δ δ ≤ 32 * ((4 * (181 / 462) + 1 / 6) * δ / π) := by
      have := mul_le_mul hL3 hK hK0 (by norm_num)
      nlinarith
    have h2 : 32 * ((4 * (181 / 462) + 1 / 6) * δ / π) ≤ 32 * ((4 * (181 / 462) + 1 / 6) * δ / 3) := by
      gcongr
    have h3 : 32 * ((4 * (181 / 462) + 1 / 6) * δ / 3) ≤ 5 * 1600 * δ * 1 * (1 / 200) := by
      nlinarith
    have h4 : 5 * 1600 * δ * 1 * (1 / 200) ≤ 5 * 1600 * δ * L₂ * cE := by
      have : (1 : ℝ) * (1 / 200) ≤ L₂ * cE := mul_le_mul hL2 hcE (by norm_num) (by linarith)
      nlinarith
    linarith
  have hsq : (K0si c g * √(c * collarK δ δ)) ^ 2 ≤ (kCol * √δ * mainA c g) ^ 2 := by
    rw [hl, hr]
    have e1 : 16 * ψ1 ^ 2 * L₃ * collarK δ δ / (5 * c) = ψ1 ^ 2 * (16 * L₃ * collarK δ δ) / (5 * c) := by ring
    have e2 : 1600 * δ * (ψ1 ^ 2 * L₂ * cE / c) = ψ1 ^ 2 * (5 * 1600 * δ * L₂ * cE) / (5 * c) := by
      field_simp
    rw [e1, e2]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left key hψ0) (by positivity)
  have hR0 : 0 ≤ kCol * √δ * mainA c g := by unfold kCol mainA; positivity
  exact le_of_pow_le_pow_left₀ two_ne_zero hR0 hsq

/-! ### The main term against the mass at band edge `10` -/

/-- **The edge value against the mass at edge `10`**: for `0 ≤ χ < c²`, `c² − χ ≤ 10c`, `c ≥ 80` and
`psi c g = μg`, `ψ(1)²·(log(1 + c) − 2k(2, 10)) ≤ 2πλc·∫_1^∞ ψ²`. -/
theorem psi_one_sq_le_mass_ten {g g₁ g₂ : ℝ → ℝ} {c χ μ : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) (hμ : ∀ s ∈ Icc (-1 : ℝ) 1, psi c g s = μ * g s)
    (hc : 80 ≤ c) (hχ : 0 ≤ χ) (hχc : χ < c ^ 2) (hband : c ^ 2 - χ ≤ 10 * c) :
    psi c g 1 ^ 2 * (Real.log (1 + c) - twoK c 2 10)
      ≤ 2 * π * (μ * √(c / (2 * π))) ^ 2 * c * ∫ t in Ioi 1, psi c g t ^ 2 := by
  have hc0 : 0 < c := by linarith
  have hconn := Cvs.Prolate.RungConnectionIdentity.tau_sq_connection hc0 heven hμ
  have hml := (Cvs.Prolate.BandMassLaw.rung_band_mass_law (r₀ := 2) hg hg₁ hg₂c hang hc0 hχ hχc (by norm_num)
    (Cvs.Prolate.BandMassLaw.wBar_lt_two hc0 (by norm_num))).2
  have hlog : Real.log (1 + 2 * c / 2) = Real.log (1 + c) := by congr 1; ring
  rw [hlog] at hml
  have hs : (c ^ 2 - χ) / c ≤ 10 := by rw [div_le_iff₀ hc0]; linarith
  have hmono := Cvs.Prolate.BandMassLaw.twoK_mono (c := c) (r₀ := 2) hc0 (by norm_num) hs
  set A := Cvs.Prolate.RungOrthogonalityAtInfinity.ampl g ^ 2 / c with hA
  set τ2 := (μ * √(c / (2 * π))) ^ 2 with hτ2
  set D := Real.log (1 + c) - twoK c 2 10 with hD
  set Mj := ∫ t in Ioi 1, psi c g t ^ 2 with hMj
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hAD : A * D ≤ 4 * (c * Mj) := by
    have : A / 4 * D ≤ A / 4 * (Real.log (1 + c) - twoK c 2 ((c ^ 2 - χ) / c)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  have hψ : psi c g 1 ^ 2 = π / 2 * (τ2 * A) := by
    rw [hconn]; field_simp
  rw [hψ]
  have hτ0 : 0 ≤ τ2 := sq_nonneg _
  calc π / 2 * (τ2 * A) * D = π / 2 * τ2 * (A * D) := by ring
    _ ≤ π / 2 * τ2 * (4 * (c * Mj)) := mul_le_mul_of_nonneg_left hAD (by positivity)
    _ = 2 * π * τ2 * c * Mj := by ring

/-- **The main term against the mass**: for a band rung at edge `10` with `|τ| ≤ 1`,
`√(ψ(1)²Λ̂(w(c, 2))C_E/c) ≤ √(ē_main(c, 10)·Mⱼ)`. -/
theorem mainA_le {g g₁ g₂ : ℝ → ℝ} {c χ μ : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) (hμ : ∀ s ∈ Icc (-1 : ℝ) 1, psi c g s = μ * g s)
    (hg0 : ∃ s ∈ Icc (-1 : ℝ) 1, g s ≠ 0)
    (hc : 80 ≤ c) (hχ : 0 ≤ χ) (hχc : χ < c ^ 2) (hband : c ^ 2 - χ ≤ 10 * c) :
    mainA c g ≤ √(eMain c 10 * ∫ t in Ioi 1, psi c g t ^ 2) := by
  have hc0 : 0 < c := by linarith
  have h := psi_one_sq_le_mass_ten hg hg₁ hg₂c hang heven hμ hc hχ hχc hband
  have habs := Cvs.Prolate.RungMirrorIdentity.abs_tau_le_one hc0
    (Cvs.Prolate.CosineChristoffelDarboux.continuousOn_of_hasDerivAt hg) heven hμ hg0
  have hτ1 : (μ * √(c / (2 * π))) ^ 2 ≤ 1 := by rw [sq_le_one_iff_abs_le_one]; exact habs
  have hD := eMain_den_pos hc
  set D := Real.log (1 + c) - twoK c 2 10 with hDdef
  set Mj := ∫ t in Ioi 1, psi c g t ^ 2 with hMj
  have hM0 : 0 ≤ Mj := setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _
  have hL0 := Cvs.L2a.BandRungOutgoingWave.lamHat_nonneg (wUp c 2)
  have hcE := cE_pos
  have h1 : psi c g 1 ^ 2 ≤ 2 * π * c * Mj / D := by
    rw [le_div_iff₀ hD]
    have : 2 * π * (μ * √(c / (2 * π))) ^ 2 * c * Mj ≤ 2 * π * 1 * c * Mj := by
      have hπ := Real.pi_pos
      have := mul_le_mul_of_nonneg_left hτ1 (by positivity : (0 : ℝ) ≤ 2 * π)
      have := mul_le_mul_of_nonneg_right this (by positivity : (0 : ℝ) ≤ c * Mj)
      nlinarith
    linarith
  unfold mainA eMain
  apply Real.sqrt_le_sqrt
  rw [← hDdef]
  calc psi c g 1 ^ 2 * lamHat (wUp c 2) * cE / c
      ≤ 2 * π * c * Mj / D * lamHat (wUp c 2) * cE / c := by gcongr
    _ = 2 * π * lamHat (wUp c 2) * cE / D * Mj := by field_simp

/-! ### `ω ≤ 1/1000` past `c₀^F` -/

/-- **`ω(K_r, c) ≤ 1/1000` past `c₀^F`** for `K_r ≤ 10⁴⁵`: `c ≥ c₀^F ≥ e¹³⁶⁰` gives `c^{−1/8} ≤ e^{−170} ≤ 2^{−170}`. -/
theorem omegaE_le {Kr c : ℝ} (hKr : Kr ≤ 10 ^ 45) (hc : Cvs.L2a.FullSpanThreshold.c0F ≤ c) :
    omegaE Kr c ≤ 1 / 1000 := by
  have h1 := Cvs.L2a.FullSpanThreshold.c0F_bounds.1.trans hc
  have hp : c ^ (-(1 / 8 : ℝ)) ≤ Real.exp 1360 ^ (-(1 / 8 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (Real.exp_pos _) h1 (by norm_num)
  rw [← Real.exp_mul] at hp
  have he : Real.exp (1360 * (-(1 / 8 : ℝ))) = (Real.exp 170)⁻¹ := by
    rw [← Real.exp_neg]; norm_num
  rw [he] at hp
  have h2 : (2 : ℝ) ^ 170 ≤ Real.exp 170 := by
    have h21 : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
    have : Real.exp 170 = Real.exp 1 ^ 170 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]; exact pow_le_pow_left₀ (by norm_num) h21 170
  have hinv : (Real.exp 170)⁻¹ ≤ ((2 : ℝ) ^ 170)⁻¹ := inv_anti₀ (by positivity) h2
  have hr0 : 0 ≤ c ^ (-(1 / 8 : ℝ)) := Real.rpow_nonneg (le_trans (Real.exp_pos _).le h1) _
  unfold omegaE kCol
  calc (40 + Kr) * c ^ (-(1 / 8 : ℝ)) ≤ (40 + 10 ^ 45) * ((2 : ℝ) ^ 170)⁻¹ :=
        mul_le_mul (by linarith) (hp.trans hinv) hr0 (by norm_num)
    _ ≤ 1 / 1000 := by norm_num

theorem omegaE_nonneg {Kr c : ℝ} (hKr0 : 0 ≤ Kr) (hc : 0 ≤ c) : 0 ≤ omegaE Kr c := by
  unfold omegaE kCol; have := Real.rpow_nonneg hc (-(1 / 8 : ℝ)); positivity

/-! ### The E-coupling on the band of the span -/

/-- The span rungs `g_j = rung c (2j)` at `c = 2πx`. -/
def gX (x : ℕ) (j : Finset.range x) : ℝ → ℝ := rung (2 * π * x) (2 * (j : ℕ))

/-- The span levels `χ_j = lev c (2j)` at `c = 2πx`. -/
def chiX (x : ℕ) (j : Finset.range x) : ℝ := lev (2 * π * x) (2 * (j : ℕ))

/-- **THEOREM E's inputs on the band at the schedule**: for every `M ≥ 3` and band rung `j`, cut multipliers in
`C³` with `N_{m,0} ≤ (K₀^si + K₀^c)/m`, `N_{m,i} ≤ (K_b/m)i!/r^i` (`r = 1/4`), the top and bulk bounds, and the
non-main, non-sharp-collar part of the bracket at most `K_r c^{−1/8}` times the main term. -/
def BandInputs (x : ℕ) (a : Finset.range x → ℝ) (Kr : ℝ) : Prop :=
  ∀ M : ℕ, 3 ≤ M → ∀ j ∈ bandSetG (2 * π * x) 10 (chiX x),
    ∃ (N : ℕ → ℕ → ℝ) (ν₁ ν₂ ν₃ : ℕ → ℝ → ℂ) (K0c Kb T ηB : ℝ), 0 ≤ K0c ∧ 0 ≤ Kb ∧
      (∀ m ∈ Finset.Ico 2 M, Cvs.L2a.BandTransferBandForm.IsBandMult
        (fun η => nuCut (2 * π * x) (gX x j) m m ((2 * π * x) * η))
        (ν₁ m) (ν₂ m) (ν₃ m) (deltaS (2 * π * x)) (Cvs.L2a.OrbitGapIntegerM.Ymax m) (N m)) ∧
      (∀ m ∈ Finset.Ico 2 M, N m 0 ≤ (K0si (2 * π * x) (gX x j) + K0c) / m) ∧
      (∀ m ∈ Finset.Ico 2 M, ∀ i ≤ 3, N m i ≤ Kb / m * ((i.factorial : ℝ) / (1 / 4) ^ i)) ∧
      |topE (2 * π * x) (gX x j) a (chiX x) (gX x) M|
        ≤ T * √(∫ ξ in Ioi 1, (∑ i, a i * psi (2 * π * x) (gX x i) ξ) ^ 2) ∧
      |bulkE (2 * π * x) (gX x j) a (chiX x) (gX x) M|
        ≤ ηB * √(∫ ξ in Ioi 1, (∑ i, a i * psi (2 * π * x) (gX x i) ξ) ^ 2) ∧
      gL1 (gX x j) * √(54 * (π ^ 2 / 12 - 11 / 16) / (π * (2 * π * x) ^ 3))
          + K0c * √((2 * π * x) * collarK (deltaS (2 * π * x)) (deltaS (2 * π * x)))
          + Kb * tauBar (2 * π * x) (1 / 2) (deltaS (2 * π * x)) (1 / 4)
            * √(8 * (1 + 1 / deltaS (2 * π * x)) * (Fintype.card (Finset.range x) : ℝ))
          + T + ηB
        ≤ Kr * (2 * π * x) ^ (-(1 / 8 : ℝ)) * mainA (2 * π * x) (gX x j)

/-- **The E-coupling on the band `c² − χ < 10c` at the collar schedule**: at `c = 2πx ≥ 80` with THEOREM E's
inputs at `δ = t = c^{−1/3}`, `d = 1/2`, `r = 1/4` and residual `K_r ≥ 0`, the E-coupling holds with
`ē = ē_main(c, 10)(1 + ω(K_r, c))²`. -/
theorem eCoupling_band (x : ℕ) (hx : 80 ≤ 2 * π * x) (a : Finset.range x → ℝ) {Kr : ℝ} (hKr : 0 ≤ Kr)
    (hin : BandInputs x a Kr) :
    Cvs.L2a.BandCouplingDischarged.ECoupling (2 * π * x) (gX x) a (bandSetG (2 * π * x) 10 (chiX x))
      (eMain (2 * π * x) 10 * (1 + omegaE Kr (2 * π * x)) ^ 2) := by
  classical
  set c : ℝ := 2 * π * x with hcdef
  have hc0 : 0 < c := by linarith
  have hc1 : 1 < c := by linarith
  have hspec := fun j => rung_spec (Cvs.Prolate.RungFamilyRangePartners.exists_main hx j)
  have hσ := Cvs.L2a.FullSpanIndexFloor.sigmaLow_pos (c := c) hc1
  have hχ0 : ∀ i, 0 ≤ chiX x i := Cvs.Prolate.RungFamilyRangePartners.lev_main_nonneg hx
  have hχc : ∀ i, chiX x i < c ^ 2 := fun i => by
    have := Cvs.Prolate.RungFamilyRangePartners.sigmaLow_le_main hx i
    unfold chiX; linarith
  intro M hM j hj
  obtain ⟨N, ν₁, ν₂, ν₃, K0c, Kb, T, ηB, hK0c, hKb, hμ, hN0, hN, htop, hbulk, hrest⟩ := hin M hM j hj
  have hbandj : c ^ 2 - chiX x j ≤ 10 * c := by
    unfold bandSetG at hj
    exact (Finset.mem_filter.1 hj).2.le
  -- the mass on `(1, M)`
  have hmass : ∀ i, 0 < ∫ t in (1 : ℝ)..M, psi c (gX x i) t ^ 2 := fun i => by
    have h3 := Cvs.Prolate.RungFamilyRangePartners.mass_main hx i
    have hM3 : (3 : ℝ) ≤ M := by exact_mod_cast hM
    have hint : IntegrableOn (fun t => psi c (gX x i) t ^ 2) (Ioi 1) :=
      (Cvs.Prolate.RungExactOrthogonality.memLp_psi (hspec i).1 (hspec i).2.1 (hspec i).2.2.1 (hspec i).2.2.2.1
        hc0).integrable_sq
    refine lt_of_lt_of_le h3 (intervalIntegral.integral_mono_interval le_rfl (by norm_num) hM3
      (ae_of_all _ fun _ => sq_nonneg _) ?_)
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).2
      (hint.mono_set Ioc_subset_Ioi_self)
  -- the bracket
  set ω := omegaE Kr c with hω
  have hω0 : 0 ≤ ω := omegaE_nonneg hKr (by linarith)
  set Mj := ∫ ξ in Ioi 1, psi c (gX x j) ξ ^ 2 with hMj
  have hMj0 : 0 ≤ Mj := setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _
  have hmain := mainA_le (hspec j).1 (hspec j).2.1 (hspec j).2.2.1 (hspec j).2.2.2.1 (hspec j).2.2.2.2.1
    (psi_rung (Cvs.Prolate.RungFamilyRangePartners.exists_main hx j)) (rung_ne_zero (Cvs.Prolate.RungFamilyRangePartners.exists_main hx j))
    hx (hχ0 j) (hχc j) hbandj
  have hcol := collar_le_main hx (gX x j)
  have hsd := sqrt_deltaS_le hc1.le
  have hA0 : 0 ≤ mainA c (gX x j) := Real.sqrt_nonneg _
  have hr0 : 0 ≤ c ^ (-(1 / 8 : ℝ)) := Real.rpow_nonneg hc0.le _
  have hK0si : 0 ≤ K0si c (gX x j) := by unfold K0si; positivity
  have hbr : mainA c (gX x j)
        + gL1 (gX x j) * √(54 * (π ^ 2 / 12 - 11 / 16) / (π * c ^ 3))
        + (K0si c (gX x j) + K0c) * √(c * collarK (deltaS c) (deltaS c))
        + Kb * tauBar c (1 / 2) (deltaS c) (1 / 4)
          * √(8 * (1 + 1 / deltaS c) * (Fintype.card (Finset.range x) : ℝ))
        + T + ηB ≤ √(eMain c 10 * (1 + ω) ^ 2 * Mj) := by
    have hcol' : K0si c (gX x j) * √(c * collarK (deltaS c) (deltaS c))
        ≤ kCol * c ^ (-(1 / 8 : ℝ)) * mainA c (gX x j) :=
      hcol.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsd (by unfold kCol; norm_num)) hA0)
    have hsum : mainA c (gX x j)
          + gL1 (gX x j) * √(54 * (π ^ 2 / 12 - 11 / 16) / (π * c ^ 3))
          + (K0si c (gX x j) + K0c) * √(c * collarK (deltaS c) (deltaS c))
          + Kb * tauBar c (1 / 2) (deltaS c) (1 / 4)
            * √(8 * (1 + 1 / deltaS c) * (Fintype.card (Finset.range x) : ℝ))
          + T + ηB ≤ (1 + ω) * mainA c (gX x j) := by
      have e : (1 + ω) * mainA c (gX x j) = mainA c (gX x j) + kCol * c ^ (-(1 / 8 : ℝ)) * mainA c (gX x j)
          + Kr * c ^ (-(1 / 8 : ℝ)) * mainA c (gX x j) := by
        rw [hω]; unfold omegaE; ring
      rw [e]
      nlinarith [hrest, hcol']
    have he : √(eMain c 10 * (1 + ω) ^ 2 * Mj) = (1 + ω) * √(eMain c 10 * Mj) := by
      rw [show eMain c 10 * (1 + ω) ^ 2 * Mj = (1 + ω) ^ 2 * (eMain c 10 * Mj) by ring,
        Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by linarith)]
    rw [he]
    exact hsum.trans (mul_le_mul_of_nonneg_left hmain (by linarith))
  have he0 : 0 ≤ eMain c 10 * (1 + ω) ^ 2 := mul_nonneg (eMain_nonneg hx) (sq_nonneg _)
  exact Cvs.L2a.BandCouplingDischarged.eCoup_sq_le_of_unif (ι := Finset.range x) a
    (g₁ := fun j => rung₁ c (2 * (j : ℕ))) (g₂ := fun j => rung₂ c (2 * (j : ℕ))) (χ := chiX x)
    (gj₁ := rung₁ c (2 * (j : ℕ))) (gj₂ := rung₂ c (2 * (j : ℕ))) (χj := chiX x j)
    (d := 1 / 2) (δ := deltaS c) (t := deltaS c) (r := 1 / 4) (K0 := K0si c (gX x j) + K0c) (Kb := Kb)
    (T := T) (ηB := ηB) (ν₁ := ν₁) (ν₂ := ν₂) (ν₃ := ν₃) (N := N)
    (fun i => (hspec i).1) (fun i => (hspec i).2.1) (fun i => (hspec i).2.2.1) (fun i => (hspec i).2.2.2.1)
    hx hχ0 hχc (Cvs.Prolate.RungFamilyRangePartners.lev_main_injective hx)
    (hspec j).1 (hspec j).2.1 (hspec j).2.2.1 (hspec j).2.2.2.1 (hspec j).2.2.2.2.1 (hχ0 j) (hχc j) hmass
    (by norm_num) (by norm_num) (deltaS_pos hc0) (deltaS_lt_one hc1) (deltaS_pos hc0) (by norm_num)
    (by positivity) hKb he0 hμ hN0 hN htop hbulk hbr

end Cvs.L2a.BandECouplingCollar
