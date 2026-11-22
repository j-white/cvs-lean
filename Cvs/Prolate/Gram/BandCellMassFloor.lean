import Mathlib
import Cvs.Approximant.SpineSubspace
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.Gram.BandFloorFromRobinQZero
import Cvs.Prolate.Gram.ProlateCellGramHalfUnit
import Cvs.Prolate.Gram.RobinNodeLatticeDualFloor
import Cvs.Prolate.Gram.RungCellGramDisplacement
import Cvs.Prolate.Gram.TunnellingFloorSumPlunge
import Cvs.Prolate.LiouvilleGreen.AdiabaticStretchBounds
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.LiouvilleGreen.PruferAngleRobinRate
import Cvs.Prolate.LiouvilleGreen.RateStrictlyDecreasing
import Cvs.Prolate.RegularSolutionEdge
import Cvs.Prolate.RungEqRegularSolution
import Cvs.Prolate.TopRungDepthBound
import Cvs.Route.Visibility.WindowChainCellFloors

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The band cell mass floor CP-a-H: `C_jj ≥ 1/(1 + 40κ(½)²)` on `T_j > ¾`

For `y = regSol (sqC c) σ`, `u = −U` and `G = ay² + u²/a`, `(yu)' = u²/p − qy²` and `u²/p + qy² = (a/p)G`; on
`[½, t₁]` the adiabatic bound keeps `G ≥ G₀/κ`, so `2q(½)∫_{½}^{t₁} y² ≥ (t₁ − ½)√q(t₁) G₀/κ − (1 + κ)G₀/2`, while
`∫_0^{½} y² ≤ κG₀/√(3q(½))`. With `C_jj = N/(∫_0^1 y²)` and `t₁ = 3/5` this is a uniform floor on the band.
-/

noncomputable section

open Real Set Filter Topology MeasureTheory intervalIntegral
open Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval (pP)
open Cvs.Prolate.RegularSolutionEdge (regSol regU sqC continuousOn_regSol hasDerivAt_regSol hasDerivAt_regU pP_mul_regV)
open Cvs.Prolate.TopRungDepthBound (af qf wf af_pos af_sq)
open Cvs.Prolate.LiouvilleGreen.RateStrictlyDecreasing (kappa qf_le_qf abs_wf_strictMonoOn wf_mul_af_mul_qf)
open Cvs.Prolate.LiouvilleGreen.AdiabaticStretchBounds (energyAt energyAt_le_kappa sq_le_energyAt_div qf_eq energyAt_half mem_allowed)
open Cvs.Prolate.LiouvilleGreen.PruferAngleRobinRate (nodeMass energyHalf)

namespace Cvs.Prolate.Gram.BandCellMassFloor
open Cvs.ZeroCounting

variable {c σ : ℝ}

/-! ### The first-order system -/

theorem hasDerivAt_y {t : ℝ} (ht : -1 < t) (hp : t ^ 2 < 1) :
    HasDerivAt (regSol (sqC c) σ) (-regU (sqC c) σ t / (1 - t ^ 2)) t := by
  have hd := hasDerivAt_regSol (sqC c) σ ht
  have hpv := pP_mul_regV (sqC c) σ ht
  unfold pP at hpv
  have hp' : (1 : ℝ) - t ^ 2 ≠ 0 := by nlinarith
  refine hd.congr_deriv ?_
  field_simp; linarith

theorem hasDerivAt_u (hc : c ≠ 0) {t : ℝ} (ht : -1 < t) :
    HasDerivAt (fun s => -regU (sqC c) σ s) (-(qf c ((c ^ 2 - σ) / c) t * regSol (sqC c) σ t)) t := by
  refine (hasDerivAt_regU (sqC c) σ ht).neg.congr_deriv ?_
  rw [qf_eq hc, Cvs.Prolate.TopRungDepthBound.sqC_apply]; ring

/-- The energy at `t` in terms of `u = −U`. -/
theorem energyAt_eq (t : ℝ) : energyAt c σ t =
    af c ((c ^ 2 - σ) / c) t * regSol (sqC c) σ t ^ 2 + (-regU (sqC c) σ t) ^ 2 / af c ((c ^ 2 - σ) / c) t := by
  unfold energyAt Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact.energy; rw [neg_sq]

/-! ### The lower bound on `[½, t₁]` -/

/-- **The virial lower bound**: for `½ ≤ t₁`, `t₁² < 1`, `q(t₁) > 0` and `|w(t₁)| ≤ M < 2`,
`2q(½)∫_{½}^{t₁} y² ≥ (t₁ − ½)√q(t₁) G₀/κ(M) − (1 + κ(M))G₀/2`. -/
theorem virial_lower (hc : c ≠ 0) {t₁ M : ℝ} (hh : 1 / 2 ≤ t₁) (hs : t₁ ^ 2 < 1)
    (hq : 0 < qf c ((c ^ 2 - σ) / c) t₁) (hM : M < 2) (hwM : |wf c ((c ^ 2 - σ) / c) t₁| ≤ M) :
    (t₁ - 1 / 2) * √(qf c ((c ^ 2 - σ) / c) t₁) * energyHalf c σ / kappa M - (1 + kappa M) * energyHalf c σ / 2
      ≤ 2 * qf c ((c ^ 2 - σ) / c) (1 / 2) * ∫ s in (1 / 2 : ℝ)..t₁, regSol (sqC c) σ s ^ 2 := by
  set K := (c ^ 2 - σ) / c
  set y := regSol (sqC c) σ
  set u : ℝ → ℝ := fun s => -regU (sqC c) σ s
  set G₀ := energyHalf c σ
  set κ := kappa M
  set Q₀ := qf c K (1 / 2)
  set Q₁ := qf c K t₁
  have h0 : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hmem := fun t (ht : t ∈ Icc (1 / 2 : ℝ) t₁) => mem_allowed h0 hs hq ht
  have hgt : ∀ t ∈ Icc (1 / 2 : ℝ) t₁, -1 < t := fun t ht => by linarith [ht.1]
  have hκ : 0 < κ := by
    simp only [κ, kappa]; have : 0 < 2 - M := by linarith
    have : 0 < 2 + M ∨ 2 + M ≤ 0 := lt_or_ge 0 (2 + M)
    rcases this with h | h
    · positivity
    · exfalso
      have hw0 := abs_nonneg (wf c K t₁)
      linarith
  have hwt : ∀ t ∈ Icc (1 / 2 : ℝ) t₁, |wf c K t| ≤ M := fun t ht =>
    ((abs_wf_strictMonoOn hc h0 hs hq).monotoneOn ht ⟨hh, le_rfl⟩ ht.2).trans hwM
  have hG : ∀ t ∈ Icc (1 / 2 : ℝ) t₁, energyAt c σ t ≤ κ * G₀ ∧ G₀ ≤ κ * energyAt c σ t := fun t ht => by
    have := energyAt_le_kappa hc h0 ht.1 (hmem t ht).1 (hmem t ht).2 hM (hwt t ht)
    rwa [energyAt_half] at this
  have hG0 : 0 ≤ G₀ := by
    have ha := af_pos (hmem _ ⟨le_rfl, hh⟩).1 (hmem _ ⟨le_rfl, hh⟩).2
    have e : G₀ = energyAt c σ (1 / 2) := (energyAt_half c σ).symm
    rw [e, energyAt_eq]; positivity
  -- the derivative of `yu`
  set f : ℝ → ℝ := fun t => u t ^ 2 / (1 - t ^ 2) - qf c K t * y t ^ 2 with hf
  have hderiv : ∀ t ∈ uIcc (1 / 2 : ℝ) t₁, HasDerivAt (fun s => y s * u s) (f t) t := by
    intro t ht
    rw [uIcc_of_le hh] at ht
    have h1 := hasDerivAt_y (c := c) (σ := σ) (hgt t ht) (hmem t ht).1
    have h2 := hasDerivAt_u (σ := σ) hc (hgt t ht)
    refine (h1.mul h2).congr_deriv ?_
    simp only [hf, u, y]; ring
  have hcont : ContinuousOn f (uIcc (1 / 2 : ℝ) t₁) := by
    rw [uIcc_of_le hh]
    intro t ht
    have h1 := (hasDerivAt_y (c := c) (σ := σ) (hgt t ht) (hmem t ht).1).continuousAt
    have h2 := (hasDerivAt_u (σ := σ) hc (hgt t ht)).continuousAt
    have hp : (1 : ℝ) - t ^ 2 ≠ 0 := by nlinarith [(hmem t ht).1]
    refine ContinuousAt.continuousWithinAt ?_
    simp only [hf]
    have hq' : ContinuousAt (fun s => qf c K s) t := by unfold qf; fun_prop
    exact ((h2.pow 2).div (by fun_prop) hp).sub (hq'.mul (h1.pow 2))
  have hFTC := integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
  -- the pointwise lower bound
  have hpt : ∀ t ∈ Icc (1 / 2 : ℝ) t₁, √Q₁ * G₀ / κ - 2 * Q₀ * y t ^ 2 ≤ f t := by
    intro t ht
    obtain ⟨hst, hqt⟩ := hmem t ht
    have ha := af_pos hst hqt
    have ha2 := af_sq hst hqt
    have hp : 0 < 1 - t ^ 2 := by linarith
    have hp1 : 1 - t ^ 2 ≤ 1 := by nlinarith
    have hQ1t : Q₁ ≤ qf c K t := qf_le_qf (h0.trans ht.1) ht.2
    have hQ0t : qf c K t ≤ Q₀ := qf_le_qf h0 ht.1
    have hE := energyAt_eq (c := c) (σ := σ) t
    have hid : u t ^ 2 / (1 - t ^ 2) + qf c K t * y t ^ 2 = af c K t / (1 - t ^ 2) * energyAt c σ t := by
      rw [hE]; field_simp; rw [ha2]; ring
    have hratio : √Q₁ ≤ af c K t / (1 - t ^ 2) := by
      rw [le_div_iff₀ hp]
      have hs1 : √Q₁ ≤ √(qf c K t) := Real.sqrt_le_sqrt hQ1t
      have : √(qf c K t) * (1 - t ^ 2) ≤ af c K t := by
        rw [Cvs.Prolate.TopRungDepthBound.af, Real.sqrt_mul hp.le, mul_comm]
        have h3 : √(1 - t ^ 2) ^ 2 = 1 - t ^ 2 := Real.sq_sqrt hp.le
        have h4 : (1 - t ^ 2) ≤ √(1 - t ^ 2) := by
          have : √(1 - t ^ 2) ≤ 1 := Real.sqrt_le_one.mpr hp1
          nlinarith [Real.sqrt_nonneg (1 - t ^ 2)]
        exact mul_le_mul_of_nonneg_right h4 (Real.sqrt_nonneg _)
      have : √Q₁ * (1 - t ^ 2) ≤ √(qf c K t) * (1 - t ^ 2) := mul_le_mul_of_nonneg_right hs1 hp.le
      linarith
    have hGt := (hG t ht).2
    have hGt' : G₀ / κ ≤ energyAt c σ t := by rw [div_le_iff₀ hκ]; linarith
    have hprod : √Q₁ * G₀ / κ ≤ af c K t / (1 - t ^ 2) * energyAt c σ t := by
      rw [mul_div_assoc]
      exact mul_le_mul hratio hGt' (div_nonneg hG0 hκ.le) (div_nonneg ha.le hp.le)
    have hy2 : qf c K t * y t ^ 2 ≤ Q₀ * y t ^ 2 := mul_le_mul_of_nonneg_right hQ0t (sq_nonneg _)
    simp only [hf]
    linarith
  have hyint : IntervalIntegrable (fun s => y s ^ 2) volume (1 / 2) t₁ :=
    (((continuousOn_regSol (sqC c) σ).mono fun t ht => by
      rw [uIcc_of_le hh] at ht; exact hgt t ht).pow 2).intervalIntegrable
  have hmono := integral_mono_on hh ((intervalIntegrable_const).sub (hyint.const_mul (2 * Q₀)))
    hcont.intervalIntegrable hpt
  rw [integral_sub intervalIntegrable_const (hyint.const_mul (2 * Q₀)), intervalIntegral.integral_const, smul_eq_mul,
    intervalIntegral.integral_const_mul, hFTC] at hmono
  -- the boundary terms
  have hb : ∀ t ∈ Icc (1 / 2 : ℝ) t₁, 2 * |y t * u t| ≤ energyAt c σ t := fun t ht => by
    have ha := af_pos (hmem t ht).1 (hmem t ht).2
    have := Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact.two_mul_abs_le_energy (a := af c K) (ψ := y) (u := u) ha
    rwa [show Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact.energy (af c K) y u t = energyAt c σ t by rw [energyAt_eq]; rfl] at this
  have hb1 := hb t₁ ⟨hh, le_rfl⟩
  have hb0 := hb (1 / 2) ⟨le_rfl, hh⟩
  rw [energyAt_half] at hb0
  have hG1 := (hG t₁ ⟨hh, le_rfl⟩).1
  have e1 := le_abs_self (y t₁ * u t₁)
  have e2 := neg_abs_le (y (1 / 2) * u (1 / 2))
  have hsq : 0 ≤ (t₁ - 1 / 2) * √Q₁ * G₀ / κ := by
    have : 0 ≤ t₁ - 1 / 2 := by linarith
    positivity
  have : (t₁ - 1 / 2) * (√Q₁ * G₀ / κ) = (t₁ - 1 / 2) * √Q₁ * G₀ / κ := by ring
  have hκG : (1 + κ) * G₀ / 2 = G₀ / 2 + κ * G₀ / 2 := by ring
  nlinarith

/-! ### The upper bound on `[0, ½]` -/

/-- **The central mass**: under `virial_lower`'s hypotheses, `∫_0^{½} y² ≤ κ(M)G₀/√(3q(½))`. -/
theorem central_upper (hc : c ≠ 0) {t₁ M : ℝ} (hh : 1 / 2 ≤ t₁) (hs : t₁ ^ 2 < 1)
    (hq : 0 < qf c ((c ^ 2 - σ) / c) t₁) (hM : M < 2) (hwM : |wf c ((c ^ 2 - σ) / c) t₁| ≤ M) :
    ∫ s in (0 : ℝ)..(1 / 2), regSol (sqC c) σ s ^ 2
      ≤ kappa M * energyHalf c σ / √(3 * qf c ((c ^ 2 - σ) / c) (1 / 2)) := by
  set K := (c ^ 2 - σ) / c
  set Q₀ := qf c K (1 / 2)
  have h0 : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hQ0 : 0 < Q₀ := hq.trans_le (qf_le_qf h0 hh)
  have hw2 : |wf c K (1 / 2)| ≤ M :=
    ((abs_wf_strictMonoOn hc h0 hs hq).monotoneOn ⟨le_rfl, hh⟩ ⟨hh, le_rfl⟩ hh).trans hwM
  have hh2 : (1 / 2 : ℝ) ^ 2 < 1 := by norm_num
  have h3 : 0 < √(3 * Q₀) := Real.sqrt_pos.mpr (by linarith)
  have hpt : ∀ s ∈ Icc (0 : ℝ) (1 / 2), regSol (sqC c) σ s ^ 2 ≤ 2 * (kappa M * energyHalf c σ / √(3 * Q₀)) := by
    intro s hs'
    have hss : s ^ 2 < 1 := by nlinarith [hs'.1, hs'.2]
    have hqs : Q₀ ≤ qf c K s := qf_le_qf hs'.1 hs'.2
    have hqs0 : 0 < qf c K s := hQ0.trans_le hqs
    have ha := af_pos hss hqs0
    have ha2 := af_sq hss hqs0
    have hk := (energyAt_le_kappa hc hs'.1 hs'.2 hh2 hQ0 hM hw2).2
    rw [energyAt_half] at hk
    have hy := sq_le_energyAt_div (c := c) (σ := σ) ha
    have hal : √(3 * Q₀) / 2 ≤ af c K s := by
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
      have : (√(3 * Q₀)) ^ 2 ≤ (af c K s * 2) ^ 2 := by
        rw [Real.sq_sqrt (by linarith), mul_pow, ha2]
        have : (3 : ℝ) / 4 ≤ 1 - s ^ 2 := by nlinarith [hs'.1, hs'.2]
        nlinarith
      exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp this
    have hE0 : 0 ≤ energyAt c σ s := by
      unfold energyAt Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact.energy; positivity
    calc regSol (sqC c) σ s ^ 2 ≤ energyAt c σ s / af c K s := hy
      _ ≤ kappa M * energyHalf c σ / af c K s := div_le_div_of_nonneg_right hk ha.le
      _ ≤ kappa M * energyHalf c σ / (√(3 * Q₀) / 2) :=
          div_le_div_of_nonneg_left (le_trans hE0 hk) (by positivity) hal
      _ = 2 * (kappa M * energyHalf c σ / √(3 * Q₀)) := by field_simp
  have hint : IntervalIntegrable (fun s => regSol (sqC c) σ s ^ 2) volume 0 (1 / 2) :=
    (((continuousOn_regSol (sqC c) σ).mono fun t ht => by
      rw [uIcc_of_le h0] at ht; show (-1 : ℝ) < t; linarith [ht.1]).pow 2).intervalIntegrable
  have := integral_mono_on h0 hint intervalIntegrable_const hpt
  rw [intervalIntegral.integral_const, smul_eq_mul] at this
  linarith

/-! ### The cell mass as a ratio of masses of `y` -/

/-- `C_jj (∫_0^{½} y² + N) = N` for `y = y_{χ_j}`, from `∫_{−1}^1 h_{4j}² = 1`, evenness and `h_{4j} = h_{4j}(1)y`. -/
theorem cellGram_self_mul {x : ℕ} (hx : 80 ≤ 2 * π * x) (j : Fin x) :
    Cvs.Prolate.Gram.ProlateCellGramHalfUnit.cellGram x j j * ((∫ s in (0 : ℝ)..(1 / 2), regSol (sqC (2 * π * x)) (Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.chi x j) s ^ 2) +
      nodeMass (2 * π * x) (Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.chi x j)) = nodeMass (2 * π * x) (Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.chi x j) := by
  have hlev : ∃ χ, Cvs.Prolate.EvenRungsByIndex.IsLevelIdx (2 * π * x) (2 * (j : ℕ)) χ := Cvs.Prolate.Gram.RungCellGramDisplacement.rungIdx_level hx j
  obtain ⟨-, -, -, -, heven, hnorm⟩ := Cvs.Prolate.EvenRungsByIndex.rung_spec hlev
  obtain ⟨-, hr⟩ := Cvs.Prolate.RungEqRegularSolution.rung_eq_mul_regSol hlev
  set r1 := Cvs.Prolate.EvenRungsByIndex.rung (2 * π * x) (2 * (j : ℕ)) 1
  set R : ℝ → ℝ := Cvs.Prolate.EvenRungsByIndex.rung (2 * π * x) (2 * (j : ℕ)) with hR
  set y := regSol (sqC (2 * π * x)) (Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.chi x j)
  have hrc : ContinuousOn (fun s => R s ^ 2) (Icc (-1) 1) := (Cvs.Prolate.Gram.ProlateCellGramHalfUnit.continuousOn_rung _ _).pow 2
  have hi : ∀ a b : ℝ, a ∈ Icc (-1 : ℝ) 1 → b ∈ Icc (-1 : ℝ) 1 →
      IntervalIntegrable (fun s => R s ^ 2) volume a b := fun a b ha hb =>
    (hrc.mono (Set.uIcc_subset_Icc ha hb)).intervalIntegrable
  have hm1 : (-1 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨le_rfl, by norm_num⟩
  have hz : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hp1 : (1 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, le_rfl⟩
  have h1 : ∫ s in (-1 : ℝ)..1, R s ^ 2 = (∫ s in (-1 : ℝ)..0, R s ^ 2) + ∫ s in (0 : ℝ)..1, R s ^ 2 :=
    (integral_add_adjacent_intervals (hi _ _ hm1 hz) (hi _ _ hz hp1)).symm
  have h2 : ∫ s in (-1 : ℝ)..0, R s ^ 2 = ∫ s in (0 : ℝ)..1, R s ^ 2 := by
    have := intervalIntegral.integral_comp_neg (a := 0) (b := 1) (fun s => R s ^ 2)
    rw [neg_zero] at this
    rw [← this]
    refine integral_congr fun s hs => ?_
    rw [uIcc_of_le zero_le_one] at hs
    show R (-s) ^ 2 = R s ^ 2
    rw [heven s ⟨by linarith [hs.1], hs.2⟩]
  have h3 : ∫ s in (0 : ℝ)..1, R s ^ 2 = r1 ^ 2 * ∫ s in (0 : ℝ)..1, y s ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    refine integral_congr fun s hs => ?_
    rw [uIcc_of_le zero_le_one] at hs
    show R s ^ 2 = r1 ^ 2 * y s ^ 2
    rw [hr s ⟨by linarith [hs.1], hs.2⟩]
    ring
  have hyc : ContinuousOn (fun s => y s ^ 2) (Ioi (-1)) := (continuousOn_regSol _ _).pow 2
  have hyi : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → IntervalIntegrable (fun s => y s ^ 2) volume a b := fun a b ha hb =>
    (hyc.mono fun t ht => by
      show (-1 : ℝ) < t
      rcases le_total a b with h | h
      · rw [uIcc_of_le h] at ht; linarith [ht.1]
      · rw [uIcc_of_ge h] at ht; linarith [ht.1]).intervalIntegrable
  have h4 : ∫ s in (0 : ℝ)..1, y s ^ 2 =
      (∫ s in (0 : ℝ)..(1 / 2), y s ^ 2) + nodeMass (2 * π * x) (Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.chi x j) := by
    unfold nodeMass
    exact (integral_add_adjacent_intervals (hyi _ _ le_rfl (by norm_num)) (hyi _ _ (by norm_num)
      (by norm_num))).symm
  have hC := Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.cellGram_self hx j
  have hN := (Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.nodeMass_pos (2 * π * x) (Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.chi x j)).le
  rw [hC, mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sq_sqrt hN]
  have hnorm' : (2 : ℝ) * r1 ^ 2 * ((∫ s in (0 : ℝ)..(1 / 2), y s ^ 2) + nodeMass (2 * π * x) (Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.chi x j)) = 1 := by
    rw [← h4, mul_assoc, ← h3, two_mul]
    nth_rewrite 1 [← h2]
    rw [← h1]
    exact hnorm
  calc 2 * r1 ^ 2 * nodeMass (2 * π * x) (Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.chi x j) *
        ((∫ s in (0 : ℝ)..(1 / 2), y s ^ 2) + nodeMass (2 * π * x) (Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.chi x j))
      = (2 * r1 ^ 2 * ((∫ s in (0 : ℝ)..(1 / 2), y s ^ 2) + nodeMass (2 * π * x) (Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.chi x j))) *
          nodeMass (2 * π * x) (Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.chi x j) := by ring
    _ = nodeMass (2 * π * x) (Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.chi x j) := by rw [hnorm', one_mul]

/-! ### The band floor -/

/-- The CP-a-H constant `h₀ = 1/(1 + 40κ(½)²)`, `κ(½) = (5/3)e^{1/3}`. -/
def h0 : ℝ := 1 / (1 + 40 * kappa (1 / 2) ^ 2)

theorem kappa_half_pos : 0 < kappa (1 / 2) := by unfold kappa; positivity

theorem h0_pos : 0 < h0 := by unfold h0; positivity

/-- The algebra of the floor: `√Q₁G₀/(20κ) ≤ 2Q₀N`, `M₀ ≤ κG₀/√(3Q₀)` and `Q₀ ≤ 3Q₁` give `M₀ ≤ 40κ²N`. -/
theorem le_of_virial {κ G₀ Q₀ Q₁ N M₀ : ℝ} (hκ : 0 < κ) (hG0 : 0 ≤ G₀) (hQ0 : 0 < Q₀)
    (hQ01 : Q₀ ≤ 3 * Q₁) (hlow : √Q₁ * G₀ / (20 * κ) ≤ 2 * Q₀ * N) (hup : M₀ ≤ κ * G₀ / √(3 * Q₀)) :
    M₀ ≤ 40 * κ ^ 2 * N := by
  set A := √(3 * Q₀)
  set B := √Q₁
  have hA : 0 < A := Real.sqrt_pos.mpr (by linarith)
  have hAB : Q₀ ≤ A * B := by
    rw [← Real.sqrt_mul (by linarith)]
    refine Real.le_sqrt_of_sq_le ?_
    nlinarith
  have h2 : B * G₀ ≤ 40 * κ * Q₀ * N := by
    rw [div_le_iff₀ (by positivity)] at hlow
    linarith
  have h1 : κ * G₀ * Q₀ ≤ κ * G₀ * (A * B) := mul_le_mul_of_nonneg_left hAB (by positivity)
  have h3 : κ * G₀ * (A * B) = κ * A * (B * G₀) := by ring
  have h4 : κ * A * (B * G₀) ≤ κ * A * (40 * κ * Q₀ * N) := mul_le_mul_of_nonneg_left h2 (by positivity)
  have h5 : κ * G₀ * Q₀ ≤ (40 * κ ^ 2 * N * A) * Q₀ := by
    have : κ * A * (40 * κ * Q₀ * N) = (40 * κ ^ 2 * N * A) * Q₀ := by ring
    linarith
  have h6 : κ * G₀ ≤ 40 * κ ^ 2 * N * A := le_of_mul_le_mul_right h5 hQ0
  refine hup.trans ?_
  rw [div_le_iff₀ hA]
  exact h6

/-- `|w(3/5)| ≤ ½` once `q(3/5) > (39/100)c²` and `c ≥ 80`. -/
theorem abs_wf_le_half {c K : ℝ} (hc80 : 80 ≤ c) (hQ1 : 39 / 100 * c ^ 2 < qf c K (3 / 5)) :
    |wf c K (3 / 5)| ≤ 1 / 2 := by
  set Q₁ := qf c K (3 / 5)
  have hs : (3 / 5 : ℝ) ^ 2 < 1 := by norm_num
  have hc2 : 6400 ≤ c ^ 2 := by nlinarith
  have hQ1pos : 0 < Q₁ := by nlinarith
  have ha := af_pos hs hQ1pos
  have ha2 := af_sq (c := c) (K := K) hs hQ1pos
  have hwq := wf_mul_af_mul_qf (c := c) (K := K) hs hQ1pos
  have ha4 : 4 ≤ af c K (3 / 5) := by
    have : (4 : ℝ) ^ 2 ≤ af c K (3 / 5) ^ 2 := by rw [ha2]; nlinarith
    exact (pow_le_pow_iff_left₀ (by norm_num) ha.le two_ne_zero).mp this
  have hneg : wf c K (3 / 5) ≤ 0 := Cvs.Prolate.TopRungDepthBound.wf_nonpos (by norm_num) hs hQ1pos
  rw [abs_of_nonpos hneg]
  have hprod : 0 < af c K (3 / 5) * Q₁ := mul_pos ha hQ1pos
  have key : -wf c K (3 / 5) * (af c K (3 / 5) * Q₁) = 3 / 5 * (Q₁ + c ^ 2 * (1 - (3 / 5) ^ 2)) := by
    linear_combination -hwq
  have hb : 3 / 5 * (Q₁ + c ^ 2 * (1 - (3 / 5) ^ 2)) ≤ 1 / 2 * (af c K (3 / 5) * Q₁) := by
    have : 2 * Q₁ ≤ 1 / 2 * (af c K (3 / 5) * Q₁) := by nlinarith
    nlinarith
  by_contra hcon
  push Not at hcon
  have : 1 / 2 * (af c K (3 / 5) * Q₁) < -wf c K (3 / 5) * (af c K (3 / 5) * Q₁) :=
    mul_lt_mul_of_pos_right hcon hprod
  linarith

/-- **The central-to-cell ratio**: for `c ≥ max(80, 20κ(1 + κ))` and `σ > ¾c²`, `∫_0^{½} y² ≤ 40κ(½)² N`. -/
theorem central_le_nodeMass {c σ : ℝ} (hc80 : 80 ≤ c) (hck : 20 * kappa (1 / 2) * (1 + kappa (1 / 2)) ≤ c)
    (hσ : 3 / 4 * c ^ 2 < σ) :
    ∫ s in (0 : ℝ)..(1 / 2), regSol (sqC c) σ s ^ 2 ≤ 40 * kappa (1 / 2) ^ 2 * nodeMass c σ := by
  have hκ : 0 < kappa (1 / 2) := kappa_half_pos
  have hc0 : c ≠ 0 := by positivity
  have hq1 : qf c ((c ^ 2 - σ) / c) (3 / 5) = σ - 9 / 25 * c ^ 2 := by rw [qf_eq hc0]; ring
  have hq0 : qf c ((c ^ 2 - σ) / c) (1 / 2) = σ - 1 / 4 * c ^ 2 := by rw [qf_eq hc0]; ring
  have hQ1 : 39 / 100 * c ^ 2 < qf c ((c ^ 2 - σ) / c) (3 / 5) := by rw [hq1]; linarith
  have hc2 : 6400 ≤ c ^ 2 := by nlinarith
  have hQ1pos : 0 < qf c ((c ^ 2 - σ) / c) (3 / 5) := by nlinarith
  have hs : (3 / 5 : ℝ) ^ 2 < 1 := by norm_num
  have hh : (1 / 2 : ℝ) ≤ 3 / 5 := by norm_num
  have hw := abs_wf_le_half (K := (c ^ 2 - σ) / c) hc80 hQ1
  have hM : (1 / 2 : ℝ) < 2 := by norm_num
  have hlow := virial_lower (σ := σ) hc0 hh hs hQ1pos hM hw
  have hup := central_upper (σ := σ) hc0 hh hs hQ1pos hM hw
  have hG0 : 0 ≤ energyHalf c σ := by
    have e : energyHalf c σ = energyAt c σ (1 / 2) := (energyAt_half c σ).symm
    have ha := af_pos (c := c) (K := (c ^ 2 - σ) / c) (by norm_num : (1 / 2 : ℝ) ^ 2 < 1) (by rw [hq0]; nlinarith)
    rw [e]; unfold energyAt Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact.energy; positivity
  have hIN : ∫ s in (1 / 2 : ℝ)..(3 / 5), regSol (sqC c) σ s ^ 2 ≤ nodeMass c σ := by
    have := Cvs.Prolate.LiouvilleGreen.AdiabaticStretchBounds.nodeMass_split c σ (3 / 5) hh
    have hr : 0 ≤ ∫ s in (3 / 5 : ℝ)..1, regSol (sqC c) σ s ^ 2 :=
      intervalIntegral.integral_nonneg (by norm_num) fun s _ => sq_nonneg _
    linarith
  have hsq : 10 * kappa (1 / 2) * (1 + kappa (1 / 2)) ≤ √(qf c ((c ^ 2 - σ) / c) (3 / 5)) := by
    refine Real.le_sqrt_of_sq_le ?_
    have h1 : (20 * kappa (1 / 2) * (1 + kappa (1 / 2))) ^ 2 ≤ c ^ 2 := pow_le_pow_left₀ (by positivity) hck 2
    nlinarith
  have hQ0pos : 0 < qf c ((c ^ 2 - σ) / c) (1 / 2) := by rw [hq0]; nlinarith
  have hQ01 : qf c ((c ^ 2 - σ) / c) (1 / 2) ≤ 3 * qf c ((c ^ 2 - σ) / c) (3 / 5) := by
    rw [hq0, hq1]; nlinarith
  refine le_of_virial hκ hG0 hQ0pos hQ01 ?_ hup
  set B := √(qf c ((c ^ 2 - σ) / c) (3 / 5))
  set G₀ := energyHalf c σ
  set κ := kappa (1 / 2)
  have hb : (1 + κ) * G₀ / 2 ≤ B * G₀ / (20 * κ) := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    have := mul_le_mul_of_nonneg_right hsq hG0
    nlinarith
  have e2 : (3 / 5 - 1 / 2 : ℝ) * B * G₀ / κ = 2 * (B * G₀ / (20 * κ)) := by field_simp; ring
  have := mul_le_mul_of_nonneg_left hIN (by positivity : (0 : ℝ) ≤ 2 * qf c ((c ^ 2 - σ) / c) (1 / 2))
  linarith

/-- **CP-a-H on the band**: at `c = 2πx ≥ max(80, 20κ(1 + κ))`, every rung with `T_j > ¾` has `C_jj ≥ h₀`. -/
theorem h0_le_cellGram {x : ℕ} (hx : 80 ≤ 2 * π * x)
    (hxk : 20 * kappa (1 / 2) * (1 + kappa (1 / 2)) ≤ 2 * π * x) (j : Fin x)
    (hj : 3 / 4 < Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.chi x j / (2 * π * x) ^ 2) : h0 ≤ Cvs.Prolate.Gram.ProlateCellGramHalfUnit.cellGram x j j := by
  have hσ : 3 / 4 * (2 * π * x) ^ 2 < Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.chi x j := by
    have := (lt_div_iff₀ (by positivity : (0 : ℝ) < (2 * π * x) ^ 2)).mp hj; linarith
  have hr := central_le_nodeMass hx hxk hσ
  have hid := cellGram_self_mul hx j
  have hN := Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.nodeMass_pos (2 * π * x) (Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.chi x j)
  have hM0 : 0 ≤ ∫ s in (0 : ℝ)..(1 / 2), regSol (sqC (2 * π * x)) (Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.chi x j) s ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) fun s _ => sq_nonneg _
  have hpos : 0 < (∫ s in (0 : ℝ)..(1 / 2), regSol (sqC (2 * π * x)) (Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.chi x j) s ^ 2) +
      nodeMass (2 * π * x) (Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.chi x j) := by linarith
  have hC : Cvs.Prolate.Gram.ProlateCellGramHalfUnit.cellGram x j j = nodeMass (2 * π * x) (Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.chi x j) /
      ((∫ s in (0 : ℝ)..(1 / 2), regSol (sqC (2 * π * x)) (Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.chi x j) s ^ 2) +
        nodeMass (2 * π * x) (Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.chi x j)) := by
    rw [eq_div_iff hpos.ne']; exact hid
  rw [hC, h0, div_le_div_iff₀ (by have := kappa_half_pos; positivity) hpos]
  linarith

/-- **CP-a-H, eventually on the band**: `C_jj ≥ h₀` for every rung with `T_j > ¾`, for all large `x`. -/
theorem bandCellMass_const : ∀ᶠ x : ℕ in atTop, ∀ j : Cvs.Approximant.SpineSubspace.SF x, 3 / 4 < Cvs.Prolate.Gram.TunnellingFloorSumPlunge.tLev x j →
    h0 ≤ Cvs.Prolate.Gram.ProlateCellGramHalfUnit.cellGram x (Cvs.Route.Visibility.WindowChainCellFloors.finOfSF j) (Cvs.Route.Visibility.WindowChainCellFloors.finOfSF j) := by
  have ht : Tendsto (fun x : ℕ => 2 * π * (x : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity)
  filter_upwards [ht.eventually_ge_atTop 80,
    ht.eventually_ge_atTop (20 * kappa (1 / 2) * (1 + kappa (1 / 2)))] with x h1 h2 j hj
  exact h0_le_cellGram h1 h2 (Cvs.Route.Visibility.WindowChainCellFloors.finOfSF j) hj

/-- **The band cell mass floor** `BandCellMass` holds. -/
theorem bandCellMass : Cvs.Prolate.Gram.BandFloorFromRobinQZero.BandCellMass := Cvs.Prolate.Gram.BandFloorFromRobinQZero.bandCellMass_of_const h0_pos bandCellMass_const

/-- **The band floor from Theorem Q₀ on the Robin lattice**: `RobinQ0` gives `TunnellingFloorSumPlunge`'s `BandFloor`. -/
theorem bandFloor_of_robinQ0 (hQ : Cvs.Prolate.Gram.BandFloorFromRobinQZero.RobinQ0) : Cvs.Prolate.Gram.TunnellingFloorSumPlunge.BandFloor :=
  Cvs.Prolate.Gram.BandFloorFromRobinQZero.bandFloor_of_robinQ0 bandCellMass hQ

end Cvs.Prolate.Gram.BandCellMassFloor

end
