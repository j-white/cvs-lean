import Mathlib
import Cvs.Prolate.Gram.BandCellMassFloor
import Cvs.Prolate.Gram.RobinNodeLatticeDualFloor
import Cvs.Prolate.LiouvilleGreen.AdiabaticStretchBounds
import Cvs.Prolate.LiouvilleGreen.BesselLayer
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
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
# `N/G₀` above the Coulomb layer: `(11/400)/(κ(½)√σ) ≤ N/G₀ ≤ 2κ(11/10)/√(σ − c²)`

The lower bound is `BandCellMassFloor`'s virial bound at `t₁ = 3/5` for every `σ ≥ c²`; the upper bound is the adiabatic stretch
on `[½, t₃]`, `∫_{½}^{t₃} 1/a ≤ 2/√(3(σ − c²))`, with `BesselLayer`'s Bessel layer, for `σ − c² ≥ 16c`.
-/

noncomputable section

open Real Set Filter Topology MeasureTheory intervalIntegral
open Cvs.Prolate.RegularSolutionEdge (regSol regU regV sqC continuousOn_regSol)
open Cvs.Prolate.TopRungDepthBound (af qf wf af_pos af_sq)
open Cvs.Prolate.LiouvilleGreen.RateStrictlyDecreasing (kappa)
open Cvs.Prolate.LiouvilleGreen.AdiabaticStretchBounds (energyAt qf_eq stretch nodeMass_split)
open Cvs.Prolate.LiouvilleGreen.PruferAngleRobinRate (nodeMass energyHalf af_half)

namespace Cvs.Prolate.LiouvilleGreen.NodeMassAboveCoulomb
open Cvs.ZeroCounting

variable {c σ : ℝ}

/-- The energy at `½` is positive once `σ > c²/4`. -/
theorem energyHalf_pos (hc : c ≠ 0) (hσ : c ^ 2 / 4 < σ) : 0 < energyHalf c σ := by
  have ha : 0 < af c ((c ^ 2 - σ) / c) (1 / 2) := by
    rw [af_half hc]; apply Real.sqrt_pos.mpr; linarith
  have h := Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.ref_pos c σ
  unfold energyHalf Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact.energy
  set y := regSol (sqC c) σ (1 / 2)
  set U := regU (sqC c) σ (1 / 2)
  set a := af c ((c ^ 2 - σ) / c) (1 / 2)
  rcases (show y ≠ 0 ∨ U ≠ 0 by
    by_contra hh; push Not at hh; rw [hh.1, hh.2] at h; norm_num at h) with h0 | h0
  · have : 0 < a * y ^ 2 := by positivity
    have : 0 ≤ U ^ 2 / a := by positivity
    linarith
  · have : 0 < U ^ 2 / a := by positivity
    have : 0 ≤ a * y ^ 2 := by positivity
    linarith

/-- **The virial floor**: for `c ≥ max(80, 20κ(1 + κ))`, `κ = κ(½)`, and `σ ≥ c²`, `N/G₀ ≥ (11/400)/(κ√σ)`. -/
theorem le_nodeMass_div (hc80 : 80 ≤ c) (hck : 20 * kappa (1 / 2) * (1 + kappa (1 / 2)) ≤ c)
    (hσ : c ^ 2 ≤ σ) : 11 / 400 / (kappa (1 / 2) * √σ) ≤ nodeMass c σ / energyHalf c σ := by
  set κ := kappa (1 / 2)
  set K := (c ^ 2 - σ) / c
  have hc0 : 0 < c := by linarith
  have hκ : 0 < κ := Cvs.Prolate.Gram.BandCellMassFloor.kappa_half_pos
  have hG := energyHalf_pos hc0.ne' (by nlinarith : c ^ 2 / 4 < σ)
  have hσ0 : 0 < σ := by nlinarith
  have hq1 : qf c K (3 / 5) = σ - 9 / 25 * c ^ 2 := by rw [qf_eq hc0.ne']; ring
  have hq0 : qf c K (1 / 2) = σ - 1 / 4 * c ^ 2 := by rw [qf_eq hc0.ne']; ring
  have hQ1pos : 0 < qf c K (3 / 5) := by rw [hq1]; nlinarith
  have hw := Cvs.Prolate.Gram.BandCellMassFloor.abs_wf_le_half (K := K) hc80 (by rw [hq1]; nlinarith)
  have hv := Cvs.Prolate.Gram.BandCellMassFloor.virial_lower (σ := σ) hc0.ne' (t₁ := 3 / 5) (M := 1 / 2) (by norm_num) (by norm_num)
    hQ1pos (by norm_num) hw
  have hsqrt1 : 4 / 5 * √σ ≤ √(qf c K (3 / 5)) := by
    rw [hq1]
    have : (4 / 5 * √σ) ^ 2 ≤ σ - 9 / 25 * c ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hσ0.le]; nlinarith
    exact Real.le_sqrt_of_sq_le this
  have hsσ : c ≤ √σ := Real.le_sqrt_of_sq_le hσ
  have hsσ0 : 0 < √σ := Real.sqrt_pos.mpr hσ0
  have hrest : 0 ≤ ∫ s in (3 / 5 : ℝ)..1, regSol (sqC c) σ s ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) fun s _ => sq_nonneg _
  have hsplit := nodeMass_split c σ (3 / 5) (by norm_num)
  set I := ∫ s in (1 / 2 : ℝ)..(3 / 5), regSol (sqC c) σ s ^ 2
  have hN : I ≤ nodeMass c σ := by linarith
  have hI0 : 0 ≤ I := intervalIntegral.integral_nonneg (by norm_num) fun s _ => sq_nonneg _
  set G := energyHalf c σ
  -- `(1 + κ)/2 ≤ √σ/(40κ)`
  have hb : (1 + κ) * G / 2 ≤ √σ * G / (40 * κ) := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    have : 20 * κ * (1 + κ) ≤ √σ := hck.trans hsσ
    nlinarith
  have hmain : 11 / 200 * √σ * G / κ ≤ 2 * qf c K (1 / 2) * I := by
    have h1 : (3 / 5 - 1 / 2) * (4 / 5 * √σ) * G / κ ≤
        (3 / 5 - 1 / 2) * √(qf c K (3 / 5)) * G / κ := by gcongr
    have e : 11 / 200 * √σ * G / κ = (3 / 5 - 1 / 2) * (4 / 5 * √σ) * G / κ - √σ * G / (40 * κ) := by
      field_simp; ring
    linarith
  have hq0le : 2 * qf c K (1 / 2) * I ≤ 2 * σ * nodeMass c σ := by
    rw [hq0]
    have : σ - 1 / 4 * c ^ 2 ≤ σ := by nlinarith
    have hq0p : 0 ≤ σ - 1 / 4 * c ^ 2 := by nlinarith
    calc 2 * (σ - 1 / 4 * c ^ 2) * I ≤ 2 * σ * I := by gcongr
      _ ≤ 2 * σ * nodeMass c σ := by gcongr
  rw [div_le_div_iff₀ (by positivity) hG]
  have hσs : σ = √σ * √σ := (Real.mul_self_sqrt hσ0.le).symm
  have h3 : 11 / 200 * √σ * G ≤ κ * (2 * σ * nodeMass c σ) := by
    have h := hmain.trans hq0le
    rw [div_le_iff₀ hκ] at h
    linarith
  have h3' : 11 / 200 * √σ * G ≤ κ * (2 * (√σ * √σ) * nodeMass c σ) := by rw [← hσs]; exact h3
  have h5 : √σ * (11 / 400 * G) ≤ √σ * (nodeMass c σ * (κ * √σ)) := by linarith [h3']
  exact le_of_mul_le_mul_left h5 hsσ0

/-- **The stretch to the Bessel layer**: for `σ − c² = D > 0` and `½ ≤ t < 1`, `2·stretch(t) ≤ 2/√(3D)`. -/
theorem stretch_le (hc : c ≠ 0) {t : ℝ} (hD : c ^ 2 < σ) (ht : 1 / 2 ≤ t) (ht1 : t < 1) :
    2 * stretch c σ t ≤ 2 / √(3 * (σ - c ^ 2)) := by
  set D := σ - c ^ 2
  set K := (c ^ 2 - σ) / c
  have hD0 : 0 < D := by linarith
  have hderiv : ∀ s ∈ uIcc (1 / 2 : ℝ) t, HasDerivAt (fun r => -2 * √(1 - r)) (1 / √(1 - s)) s := by
    intro s hs
    rw [uIcc_of_le ht] at hs
    have hs1 : 0 < 1 - s := by linarith [hs.2]
    have h := (((hasDerivAt_id s).const_sub 1).sqrt hs1.ne').const_mul (-2)
    refine h.congr_deriv ?_
    have : √(1 - s) ≠ 0 := (Real.sqrt_pos.mpr hs1).ne'
    simp only [id]
    field_simp
  have hcont : ContinuousOn (fun s : ℝ => 1 / √(1 - s)) (uIcc (1 / 2 : ℝ) t) := by
    rw [uIcc_of_le ht]
    exact continuousOn_const.div (by fun_prop) fun s hs => (Real.sqrt_pos.mpr (by linarith [hs.2])).ne'
  have hFTC := integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
  have hval : ∫ s in (1 / 2 : ℝ)..t, 1 / √(1 - s) ≤ 2 * √(1 / 2) := by
    rw [hFTC]
    have : 0 ≤ √(1 - t) := Real.sqrt_nonneg _
    have e : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
    rw [e]; linarith
  have hpt : ∀ s ∈ Icc (1 / 2 : ℝ) t, 1 / af c K s ≤ 1 / √(3 * D / 2) * (1 / √(1 - s)) := by
    intro s hs
    have hs1 : 0 < 1 - s := by linarith [hs.2]
    have hss : s ^ 2 < 1 := by nlinarith [hs.1, hs.2]
    have hq : D ≤ qf c K s := by rw [qf_eq hc]; nlinarith [hs.1, hs.2]
    have hqp : 0 < qf c K s := hD0.trans_le hq
    have ha := af_pos hss hqp
    rw [one_div_mul_one_div, one_div_le_one_div ha (by positivity), ← Real.sqrt_mul (by positivity)]
    unfold af
    apply Real.sqrt_le_sqrt
    have hp : 3 / 2 * (1 - s) ≤ 1 - s ^ 2 := by nlinarith [hs.1, hs.2]
    have : 3 * D / 2 * (1 - s) = (3 / 2 * (1 - s)) * D := by ring
    rw [this]
    exact mul_le_mul hp hq hD0.le (by nlinarith)
  have hint1 : IntervalIntegrable (fun s => 1 / af c K s) volume (1 / 2) t := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le ht]
    refine continuousOn_const.div (Cvs.Prolate.LiouvilleGreen.AdiabaticStretchBounds.continuous_af c K).continuousOn fun s hs => ?_
    have hss : s ^ 2 < 1 := by nlinarith [hs.1, hs.2]
    have hq : 0 < qf c K s := by rw [qf_eq hc]; nlinarith [hs.1, hs.2]
    exact (af_pos hss hq).ne'
  have hmono := integral_mono_on ht hint1 (hcont.intervalIntegrable.const_mul (1 / √(3 * D / 2))) hpt
  rw [intervalIntegral.integral_const_mul] at hmono
  unfold stretch
  have hs2 : √(1 / 2) * (1 / √(3 * D / 2)) = 1 / √(3 * D) := by
    rw [mul_one_div, div_eq_div_iff (Real.sqrt_pos.mpr (by positivity)).ne'
      (Real.sqrt_pos.mpr (by positivity)).ne', one_mul, ← Real.sqrt_mul (by norm_num)]
    congr 1; ring
  have hpos : 0 < 1 / √(3 * D / 2) := by positivity
  calc 2 * (1 / 2 * ∫ s in (1 / 2 : ℝ)..t, 1 / af c K s) = ∫ s in (1 / 2 : ℝ)..t, 1 / af c K s := by ring
    _ ≤ 1 / √(3 * D / 2) * ∫ s in (1 / 2 : ℝ)..t, 1 / √(1 - s) := hmono
    _ ≤ 1 / √(3 * D / 2) * (2 * √(1 / 2)) := mul_le_mul_of_nonneg_left hval hpos.le
    _ = 2 * (√(1 / 2) * (1 / √(3 * D / 2))) := by ring
    _ = 2 / √(3 * D) := by rw [hs2]; ring

/-- **The Bessel-side ceiling**: for `c ≥ 1` and `σ − c² ≥ 16c`, `N/G₀ ≤ 2κ(11/10)/√(σ − c²)`. -/
theorem nodeMass_div_le (hc : 1 ≤ c) (hβ : 16 * c ≤ σ - c ^ 2) :
    nodeMass c σ / energyHalf c σ ≤ 2 * kappa (11 / 10) / √(σ - c ^ 2) := by
  set D := σ - c ^ 2 with hD_def
  set K := (c ^ 2 - σ) / c
  have hc0 : 0 < c := by linarith
  have hD0 : 0 < D := by linarith
  have hβ' : 8 ≤ (σ - c ^ 2) / (2 * c) := by rw [le_div_iff₀ (by positivity)]; linarith
  set s₃ := 1 / (2 * D) with hs₃
  set t₃ := 1 - s₃ with ht₃
  have hs₃pos : 0 < s₃ := div_pos one_pos (by linarith)
  have hs₃le : s₃ ≤ 1 / 32 := by
    rw [hs₃, div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have hDs : D * s₃ = 1 / 2 := by rw [hs₃]; field_simp
  have hh : 1 / 2 ≤ t₃ := by linarith
  have ht1 : t₃ < 1 := by linarith
  have ht₃s : t₃ ^ 2 < 1 := by nlinarith
  have hq : 0 < qf c K t₃ := by rw [qf_eq hc0.ne']; nlinarith
  have hw := Cvs.Prolate.LiouvilleGreen.BesselLayer.abs_wf_le hc hβ'
  have hG := energyHalf_pos hc0.ne' (by nlinarith : c ^ 2 / 4 < σ)
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
  have hσc : c ^ 2 < σ := by have := hD0; rw [hD_def] at this; linarith
  have hst := stretch_le hc0.ne' hσc hh ht1
  have hsD : 4 ≤ √D := by
    have : (4 : ℝ) ^ 2 ≤ D := by norm_num; linarith
    exact Real.le_sqrt_of_sq_le this
  have hsD0 : 0 < √D := by linarith
  have hD2 : D = √D * √D := (Real.mul_self_sqrt hD0.le).symm
  -- the layer term
  have hlayer : 435 / 100 * s₃ / af c K t₃ ≤ 11 / 20 / √D := by
    rw [div_le_div_iff₀ ha hsD0]
    have h1 : s₃ * √D * 4 ≤ s₃ * √D * √D := mul_le_mul_of_nonneg_left hsD (by positivity)
    have h2 : s₃ * √D * √D = 1 / 2 := by rw [mul_assoc, ← hD2, mul_comm]; exact hDs
    linarith
  have h3 : √3 * √D = √(3 * D) := (Real.sqrt_mul (by norm_num) D).symm
  have hs3 : 7 / 5 < √3 := by
    rw [show (7 / 5 : ℝ) = √((7 / 5) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hstr : 2 / √(3 * D) ≤ 29 / 20 / √D := by
    rw [← h3, div_le_div_iff₀ (by positivity) hsD0]
    have := mul_lt_mul_of_pos_right hs3 hsD0
    nlinarith
  rw [div_le_iff₀ hG]
  calc nodeMass c σ ≤ kappa (11 / 10) * (2 * stretch c σ t₃ + 435 / 100 * s₃ / af c K t₃) * energyHalf c σ := hN
    _ ≤ kappa (11 / 10) * (29 / 20 / √D + 11 / 20 / √D) * energyHalf c σ := by gcongr; linarith
    _ = 2 * kappa (11 / 10) / √D * energyHalf c σ := by ring

end Cvs.Prolate.LiouvilleGreen.NodeMassAboveCoulomb

end
