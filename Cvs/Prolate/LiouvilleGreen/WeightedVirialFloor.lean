import Mathlib
import Cvs.Prolate.LiouvilleGreen.AdiabaticStretchBounds
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.LiouvilleGreen.PruferAngleRobinRate
import Cvs.Prolate.LiouvilleGreen.RateStrictlyDecreasing
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
# The `1/q`-weighted virial floor: `∫_{½}^{t_e} y² ≥ (G₀/κ) m(t_e) − κG₀/(2q(t_e))`

For `F = yU/q`, `2y² = G/a + F' − 2c²t yU/q²` with `G/a = y² + U²/(pq)`; on `[½, t_e]` with `|w(t_e)| ≤ M < 2` the
adiabatic bound `G₀/κ ≤ G ≤ κG₀`, `2|yU| ≤ G` and `∫ 2c²t/q² = 1/q(t_e) − 1/q(½)` give the floor.
-/

noncomputable section

open Real Set Filter Topology MeasureTheory intervalIntegral
open Cvs.Prolate.RegularSolutionEdge (regSol regU regV sqC continuousOn_regSol hasDerivAt_regSol hasDerivAt_regU pP_mul_regV)
open Cvs.Prolate.TopRungDepthBound (af qf wf af_pos af_sq sqC_apply)
open Cvs.Prolate.LiouvilleGreen.RateStrictlyDecreasing (kappa abs_wf_strictMonoOn)
open Cvs.Prolate.LiouvilleGreen.AdiabaticStretchBounds (energyAt qf_eq stretch mem_allowed energyAt_le_kappa energyAt_half continuous_af)
open Cvs.Prolate.LiouvilleGreen.PruferAngleRobinRate (nodeMass energyHalf)

namespace Cvs.Prolate.LiouvilleGreen.WeightedVirialFloor

variable {c σ : ℝ}

theorem one_le_kappa {M : ℝ} (hM0 : 0 ≤ M) (hM : M < 2) : 1 ≤ kappa M := by
  unfold kappa
  have h2 : 0 < 2 - M := by linarith
  have h1 : 1 ≤ (2 + M) / (2 - M) := by rw [le_div_iff₀ h2]; linarith
  have h3 : 1 ≤ exp (M / (2 - M)) := one_le_exp (div_nonneg hM0 h2.le)
  nlinarith

/-- **The `1/q`-weighted virial floor**: for `½ ≤ t_e`, `t_e² < 1`, `q(t_e) > 0` and `|w(t_e)| ≤ M < 2`,
`(G₀/κ(M)) m(t_e) − κ(M)G₀/(2q(t_e)) ≤ ∫_{½}^{t_e} y²`. -/
theorem stretch_le_integral_sq (hc : c ≠ 0) {te M : ℝ} (hh : 1 / 2 ≤ te) (hs : te ^ 2 < 1)
    (hq : 0 < qf c ((c ^ 2 - σ) / c) te) (hM0 : 0 ≤ M) (hM : M < 2)
    (hwM : |wf c ((c ^ 2 - σ) / c) te| ≤ M) :
    energyHalf c σ / kappa M * stretch c σ te - kappa M * energyHalf c σ / (2 * qf c ((c ^ 2 - σ) / c) te)
      ≤ ∫ s in (1 / 2 : ℝ)..te, regSol (sqC c) σ s ^ 2 := by
  set K := (c ^ 2 - σ) / c
  set y := regSol (sqC c) σ
  set U := regU (sqC c) σ
  set G₀ := energyHalf c σ
  set κ := kappa M
  set q := qf c K
  set a := af c K
  have h0 : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hmem := fun t (ht : t ∈ Icc (1 / 2 : ℝ) te) => mem_allowed h0 hs hq ht
  have hgt : ∀ t ∈ Icc (1 / 2 : ℝ) te, -1 < t := fun t ht => by linarith [ht.1]
  have hκ1 : 1 ≤ κ := one_le_kappa hM0 hM
  have hκ : 0 < κ := by linarith
  have hwt : ∀ t ∈ Icc (1 / 2 : ℝ) te, |wf c K t| ≤ M := fun t ht =>
    ((abs_wf_strictMonoOn hc h0 hs hq).monotoneOn ht ⟨hh, le_rfl⟩ ht.2).trans hwM
  have hG : ∀ t ∈ Icc (1 / 2 : ℝ) te, energyAt c σ t ≤ κ * G₀ ∧ G₀ ≤ κ * energyAt c σ t := fun t ht => by
    have := energyAt_le_kappa hc h0 ht.1 (hmem t ht).1 (hmem t ht).2 hM (hwt t ht)
    rwa [energyAt_half] at this
  have ha : ∀ t ∈ Icc (1 / 2 : ℝ) te, 0 < a t := fun t ht => af_pos (hmem t ht).1 (hmem t ht).2
  have hqt : ∀ t ∈ Icc (1 / 2 : ℝ) te, 0 < q t := fun t ht => (hmem t ht).2
  have hqe : ∀ t, q t = σ - c ^ 2 * t ^ 2 := fun t => qf_eq hc t
  have hqcont : Continuous q := by simp only [q]; unfold qf; fun_prop
  have hG0 : 0 ≤ G₀ := by
    have h := (hG (1 / 2) ⟨le_rfl, hh⟩).2
    have hE : 0 ≤ energyAt c σ (1 / 2) := by
      unfold energyAt Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact.energy
      have := ha (1 / 2) ⟨le_rfl, hh⟩
      positivity
    rw [energyAt_half] at hE; exact hE
  -- `2|yU| ≤ G ≤ κG₀`
  have hyU : ∀ t ∈ Icc (1 / 2 : ℝ) te, 2 * |y t * U t| ≤ κ * G₀ := fun t ht =>
    (Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact.two_mul_abs_le_energy (ψ := y) (u := U) (ha t ht)).trans (hG t ht).1
  -- the derivative of `F = yU/q`
  set F : ℝ → ℝ := fun t => y t * U t / q t
  set F' : ℝ → ℝ := fun t => (-(U t) ^ 2 / (1 - t ^ 2) + q t * y t ^ 2) / q t +
    y t * U t * (2 * c ^ 2 * t) / q t ^ 2
  have hderiv : ∀ t ∈ uIcc (1 / 2 : ℝ) te, HasDerivAt F (F' t) t := by
    intro t ht
    rw [uIcc_of_le hh] at ht
    have hp : (1 : ℝ) - t ^ 2 ≠ 0 := by have := (hmem t ht).1; linarith
    have hy : HasDerivAt y (-U t / (1 - t ^ 2)) t := by
      have hd := hasDerivAt_regSol (sqC c) σ (hgt t ht)
      have hpv := pP_mul_regV (sqC c) σ (hgt t ht)
      unfold Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval.pP at hpv
      refine hd.congr_deriv ?_
      field_simp; linarith
    have hU : HasDerivAt U (q t * y t) t := by
      refine (hasDerivAt_regU (sqC c) σ (hgt t ht)).congr_deriv ?_
      rw [hqe, sqC_apply]; ring
    have hqd : HasDerivAt q (-(2 * c ^ 2 * t)) t := Cvs.Prolate.TopRungDepthBound.hasDerivAt_qf c K t
    refine ((hy.mul hU).div hqd (hqt t ht).ne').congr_deriv ?_
    have hq0 := (hqt t ht).ne'
    simp only [F', Pi.mul_apply]
    field_simp
    ring
  have hcontF' : ContinuousOn F' (uIcc (1 / 2 : ℝ) te) := by
    rw [uIcc_of_le hh]
    have hyc : ContinuousOn y (Icc (1 / 2) te) := (continuousOn_regSol (sqC c) σ).mono fun t ht => hgt t ht
    have hUc : ContinuousOn U (Icc (1 / 2) te) := fun t ht =>
      (hasDerivAt_regU (sqC c) σ (hgt t ht)).continuousAt.continuousWithinAt
    have hqc : ContinuousOn q (Icc (1 / 2) te) := hqcont.continuousOn
    refine ((((hUc.pow 2).neg.div (by fun_prop) fun t ht => ?_).add (hqc.mul (hyc.pow 2))).div hqc
      fun t ht => (hqt t ht).ne').add (((hyc.mul hUc).mul (by fun_prop)).div (hqc.pow 2)
      fun t ht => pow_ne_zero 2 (hqt t ht).ne')
    have := (hmem t ht).1; linarith
  have hFTC := integral_eq_sub_of_hasDerivAt hderiv hcontF'.intervalIntegrable
  -- the comparison function
  set g : ℝ → ℝ := fun t => 2 * y t ^ 2 - G₀ / κ * (1 / a t) + κ * G₀ / 2 * (2 * c ^ 2 * t / q t ^ 2)
  have hpt : ∀ t ∈ Icc (1 / 2 : ℝ) te, F' t ≤ g t := by
    intro t ht
    have hp : 0 < 1 - t ^ 2 := by have := (hmem t ht).1; linarith
    have hqt0 := hqt t ht
    have hat := ha t ht
    have ha2 : a t ^ 2 = (1 - t ^ 2) * q t := af_sq (hmem t ht).1 (hmem t ht).2
    have hGa : energyAt c σ t / a t = y t ^ 2 + U t ^ 2 / ((1 - t ^ 2) * q t) := by
      have hEt : energyAt c σ t = a t * y t ^ 2 + U t ^ 2 / a t := rfl
      rw [hEt, ← ha2]; field_simp
    have hlow : G₀ / κ * (1 / a t) ≤ energyAt c σ t / a t := by
      rw [div_mul_div_comm, mul_one, div_le_div_iff₀ (by positivity) hat]
      have := (hG t ht).2
      nlinarith
    have e1 : (-(U t) ^ 2 / (1 - t ^ 2) + q t * y t ^ 2) / q t = 2 * y t ^ 2 - energyAt c σ t / a t := by
      rw [hGa]; field_simp; ring
    have e2 : y t * U t * (2 * c ^ 2 * t) / q t ^ 2 ≤ κ * G₀ / 2 * (2 * c ^ 2 * t / q t ^ 2) := by
      have ht0 : 0 ≤ 2 * c ^ 2 * t / q t ^ 2 := by have := ht.1; positivity
      have h1 : y t * U t ≤ κ * G₀ / 2 := by
        have := hyU t ht; have := le_abs_self (y t * U t); linarith
      calc y t * U t * (2 * c ^ 2 * t) / q t ^ 2 = y t * U t * (2 * c ^ 2 * t / q t ^ 2) := by ring
        _ ≤ κ * G₀ / 2 * (2 * c ^ 2 * t / q t ^ 2) := mul_le_mul_of_nonneg_right h1 ht0
    simp only [F', g]
    rw [e1]
    linarith
  -- integrability and the integral of `2c²t/q²`
  have hyc2 : ContinuousOn (fun t => y t ^ 2) (Icc (1 / 2) te) :=
    ((continuousOn_regSol (sqC c) σ).mono fun t ht => hgt t ht).pow 2
  have hac : ContinuousOn (fun t => 1 / a t) (Icc (1 / 2) te) :=
    continuousOn_const.div (continuous_af c K).continuousOn fun t ht => (ha t ht).ne'
  have hqc : ContinuousOn (fun t => 2 * c ^ 2 * t / q t ^ 2) (Icc (1 / 2) te) := by
    have hnum : ContinuousOn (fun t : ℝ => 2 * c ^ 2 * t) (Icc (1 / 2) te) :=
      (continuous_const.mul continuous_id).continuousOn
    have hden : ContinuousOn (fun t => q t ^ 2) (Icc (1 / 2) te) := hqcont.continuousOn.pow 2
    exact ContinuousOn.div₀ (f := fun t : ℝ => 2 * c ^ 2 * t) (g := fun t => q t ^ 2) hnum hden
      fun t ht => pow_ne_zero 2 (hqt t ht).ne'
  have hgi : IntervalIntegrable g volume (1 / 2) te := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hh]
    exact ((continuousOn_const.mul hyc2).sub (continuousOn_const.mul hac)).add (continuousOn_const.mul hqc)
  have hmono := integral_mono_on hh hcontF'.intervalIntegrable hgi hpt
  have hinvq : ∫ t in (1 / 2 : ℝ)..te, 2 * c ^ 2 * t / q t ^ 2 = 1 / q te - 1 / q (1 / 2) := by
    have hd : ∀ t ∈ uIcc (1 / 2 : ℝ) te, HasDerivAt (fun t => 1 / q t) (2 * c ^ 2 * t / q t ^ 2) t := by
      intro t ht
      rw [uIcc_of_le hh] at ht
      have h := (Cvs.Prolate.TopRungDepthBound.hasDerivAt_qf c K t).inv (hqt t ht).ne'
      simp only [one_div]
      refine h.congr_deriv ?_
      have h1 : qf c K t ≠ 0 := (hqt t ht).ne'
      change -(-(2 * c ^ 2 * t)) / qf c K t ^ 2 = 2 * c ^ 2 * t / qf c K t ^ 2
      ring
    have hi : IntervalIntegrable (fun t => 2 * c ^ 2 * t / q t ^ 2) volume (1 / 2) te :=
      (by rw [uIcc_of_le hh]; exact hqc : ContinuousOn _ (uIcc (1 / 2 : ℝ) te)).intervalIntegrable
    exact integral_eq_sub_of_hasDerivAt hd hi
  have hyi : IntervalIntegrable (fun t => y t ^ 2) volume (1 / 2) te :=
    (by rw [uIcc_of_le hh]; exact hyc2 : ContinuousOn _ (uIcc (1 / 2 : ℝ) te)).intervalIntegrable
  have hai : IntervalIntegrable (fun t => 1 / a t) volume (1 / 2) te :=
    (by rw [uIcc_of_le hh]; exact hac : ContinuousOn _ (uIcc (1 / 2 : ℝ) te)).intervalIntegrable
  have hqi : IntervalIntegrable (fun t => 2 * c ^ 2 * t / q t ^ 2) volume (1 / 2) te :=
    (by rw [uIcc_of_le hh]; exact hqc : ContinuousOn _ (uIcc (1 / 2 : ℝ) te)).intervalIntegrable
  have hgint : ∫ t in (1 / 2 : ℝ)..te, g t = 2 * (∫ t in (1 / 2 : ℝ)..te, y t ^ 2) -
      G₀ / κ * (∫ t in (1 / 2 : ℝ)..te, 1 / a t) + κ * G₀ / 2 * (1 / q te - 1 / q (1 / 2)) := by
    simp only [g]
    rw [integral_add (hyi.const_mul 2 |>.sub (hai.const_mul _)) (hqi.const_mul _),
      integral_sub (hyi.const_mul 2) (hai.const_mul _), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, hinvq]
  rw [hFTC, hgint] at hmono
  -- the boundary terms
  have hFe : |F te| ≤ κ * G₀ / (2 * q te) := by
    simp only [F]
    rw [abs_div, abs_of_pos (hqt te ⟨hh, le_rfl⟩), div_le_div_iff₀ (hqt te ⟨hh, le_rfl⟩) (by
      have := hqt te ⟨hh, le_rfl⟩; positivity)]
    have := hyU te ⟨hh, le_rfl⟩
    nlinarith [hqt te ⟨hh, le_rfl⟩]
  have hFh : |F (1 / 2)| ≤ κ * G₀ / (2 * q (1 / 2)) := by
    simp only [F]
    have hq0 := hqt (1 / 2) ⟨le_rfl, hh⟩
    rw [abs_div, abs_of_pos hq0, div_le_div_iff₀ hq0 (by positivity)]
    have := hyU (1 / 2) ⟨le_rfl, hh⟩
    nlinarith
  have hstr : stretch c σ te = 1 / 2 * ∫ t in (1 / 2 : ℝ)..te, 1 / a t := rfl
  have hq0e : q te ≤ q (1 / 2) := Cvs.Prolate.LiouvilleGreen.RateStrictlyDecreasing.qf_le_qf h0 hh
  have hqe0 := hqt te ⟨hh, le_rfl⟩
  have hq00 := hqt (1 / 2) ⟨le_rfl, hh⟩
  have e1 : κ * G₀ / (2 * q te) = κ * G₀ / 2 * (1 / q te) := by ring
  have e2 : κ * G₀ / (2 * q (1 / 2)) = κ * G₀ / 2 * (1 / q (1 / 2)) := by ring
  rw [e1] at hFe; rw [e2] at hFh
  have hFe' := neg_abs_le (F te)
  have hFh' := le_abs_self (F (1 / 2))
  rw [hstr]
  have e3 : G₀ / κ * (1 / 2 * ∫ t in (1 / 2 : ℝ)..te, 1 / a t) - κ * G₀ / (2 * q te) =
      G₀ / κ * (1 / 2 * ∫ t in (1 / 2 : ℝ)..te, 1 / a t) - κ * G₀ / 2 * (1 / q te) := by ring
  rw [e3]
  nlinarith

end Cvs.Prolate.LiouvilleGreen.WeightedVirialFloor

end
