import Mathlib
import Cvs.Prolate.LiouvilleGreen.AiryLayerBelowCoulomb
import Cvs.Prolate.LiouvilleGreen.CoulombLayerExplicit
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.LiouvilleGreen.PruferAngleRobinRate
import Cvs.Prolate.LiouvilleGreen.RobinCellPhaseIncrement
import Cvs.Prolate.RegularSolutionEdge

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The far Robin rate: `θ'(σ) ≤ c` on `c²/4 ≤ σ < 5c²/8`, so `FarRate` with `K = 1`

On `[½, t*]`, `t* = √(σ/c²)`, the Sonin function `f = pqy² + U²` decreases (Cvs.Prolate.LiouvilleGreen.AiryLayerBelowCoulomb), so `|U| ≤ √f(½)` and
`|y(t)| ≤ |y(½)| + (t − ½)√f(½)/(1 − σ/c²)`; beyond `t*`, `1 ≤ y` decreases, so the same bound holds on `[½, 1]`.
At `½`, `f(½) ≤ (9/16)((cy)² + y'²)` since `σ − c²/4 < 3c²/8`, so `N = ∫_{½}^1 y² ≤ (3/4)((cy)² + y'²)` and
`θ' = (4c/3)N/((cy)² + y'²) ≤ c`. The turning point may sit at `½` itself: no Airy estimate is used.
-/

noncomputable section

open Real Set Filter Topology MeasureTheory intervalIntegral
open Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval (pP)
open Cvs.Prolate.RegularSolutionEdge (regSol regU regV sqC continuousOn_regSol hasDerivAt_regSol pP_mul_regV)
open Cvs.Prolate.LiouvilleGreen.PruferAngleRobinRate (nodeMass regV_half)
open Cvs.Prolate.LiouvilleGreen.RobinCellPhaseIncrement (nodeRate)
open Cvs.Prolate.LiouvilleGreen.CoulombLayerExplicit (soninF)

namespace Cvs.Prolate.LiouvilleGreen.FarRobinRate
open Cvs.ZeroCounting

variable {c σ : ℝ}

/-- **The sup on `[½, 1]`**: for `c²/4 ≤ σ < c²` and `½ ≤ t ≤ 1`,
`|y(t)| ≤ |y(½)| + (t* − ½)√f(½)/(1 − σ/c²)` with `t* = √(σ/c²)`. -/
theorem abs_regSol_le_half (hc : 0 < c) (hσ4 : c ^ 2 / 4 ≤ σ) (hσ : σ < c ^ 2) {t : ℝ}
    (ht : t ∈ Icc (1 / 2 : ℝ) 1) :
    |regSol (sqC c) σ t| ≤ |regSol (sqC c) σ (1 / 2)| +
      (√(σ / c ^ 2) - 1 / 2) * √(soninF c σ (1 / 2)) / (1 - σ / c ^ 2) := by
  set ts := √(σ / c ^ 2) with hts
  have hc2 : 0 < c ^ 2 := by positivity
  have hσ0 : 0 < σ := by linarith
  have hts2 : ts ^ 2 = σ / c ^ 2 := Real.sq_sqrt (div_pos hσ0 hc2).le
  have hps : 0 < 1 - σ / c ^ 2 := by rw [sub_pos, div_lt_one hc2]; exact hσ
  have hhalf : 1 / 2 ≤ ts := by
    rw [hts, show (1 / 2 : ℝ) = √(1 / 4) by
      rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by rw [le_div_iff₀ hc2]; linarith)
  have hts1 : ts ≤ 1 := by
    rw [hts, show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt (by rw [div_le_one hc2]; linarith)
  -- the bound on the allowed side `[½, t*]`
  have hallow : ∀ t ∈ Icc (1 / 2 : ℝ) ts, |regSol (sqC c) σ t| ≤ |regSol (sqC c) σ (1 / 2)| +
      (t - 1 / 2) * √(soninF c σ (1 / 2)) / (1 - σ / c ^ 2) := by
    intro t ht
    have hderiv : ∀ x ∈ Icc (1 / 2 : ℝ) t,
        HasDerivWithinAt (regSol (sqC c) σ) (regV (sqC c) σ x) (Icc (1 / 2) t) x :=
      fun x hx => (hasDerivAt_regSol (sqC c) σ (by linarith [hx.1])).hasDerivWithinAt
    have hbound : ∀ x ∈ Ico (1 / 2 : ℝ) t, ‖regV (sqC c) σ x‖ ≤ √(soninF c σ (1 / 2)) / (1 - σ / c ^ 2) := by
      intro x hx
      have hxI : x ∈ Icc (1 / 2 : ℝ) ts := ⟨hx.1, hx.2.le.trans ht.2⟩
      have hx0 : 0 ≤ x := by linarith [hx.1]
      have hxs : x ^ 2 ≤ σ / c ^ 2 := by rw [← hts2]; nlinarith [hxI.2]
      have hp : 1 - σ / c ^ 2 ≤ 1 - x ^ 2 := by linarith
      have hp0 : 0 < 1 - x ^ 2 := lt_of_lt_of_le hps hp
      have hpv := pP_mul_regV (sqC c) σ (show (-1 : ℝ) < x by linarith)
      unfold pP at hpv
      have hV : regV (sqC c) σ x = -regU (sqC c) σ x / (1 - x ^ 2) := by field_simp; linarith
      have hU : |regU (sqC c) σ x| ≤ √(soninF c σ (1 / 2)) :=
        Real.abs_le_sqrt (Cvs.Prolate.LiouvilleGreen.AiryLayerBelowCoulomb.regU_sq_le_soninF hc hσ0 hσ le_rfl hxI)
      rw [Real.norm_eq_abs, hV, abs_div, abs_neg, abs_of_pos hp0]
      calc |regU (sqC c) σ x| / (1 - x ^ 2) ≤ √(soninF c σ (1 / 2)) / (1 - x ^ 2) :=
            div_le_div_of_nonneg_right hU hp0.le
        _ ≤ √(soninF c σ (1 / 2)) / (1 - σ / c ^ 2) :=
            div_le_div_of_nonneg_left (Real.sqrt_nonneg _) hps hp
    have h := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound t ⟨ht.1, le_rfl⟩
    rw [Real.norm_eq_abs] at h
    have := abs_sub_abs_le_abs_sub (regSol (sqC c) σ t) (regSol (sqC c) σ (1 / 2))
    have e : √(soninF c σ (1 / 2)) / (1 - σ / c ^ 2) * (t - 1 / 2) =
        (t - 1 / 2) * √(soninF c σ (1 / 2)) / (1 - σ / c ^ 2) := by ring
    linarith
  rcases le_total t ts with h | h
  · refine (hallow t ⟨ht.1, h⟩).trans ?_
    have : 0 ≤ √(soninF c σ (1 / 2)) / (1 - σ / c ^ 2) := div_nonneg (Real.sqrt_nonneg _) hps.le
    have e : ∀ s : ℝ, s * √(soninF c σ (1 / 2)) / (1 - σ / c ^ 2) =
        s * (√(soninF c σ (1 / 2)) / (1 - σ / c ^ 2)) := fun s => by ring
    rw [e, e]
    nlinarith
  · have hI : t ∈ Icc ts 1 := ⟨h, ht.2⟩
    have hts' : ts ∈ Icc ts 1 := ⟨le_rfl, hts1⟩
    have h1 := Cvs.Prolate.LiouvilleGreen.AiryLayerBelowCoulomb.one_le_forbidden hc hI
    have hmono := Cvs.Prolate.LiouvilleGreen.AiryLayerBelowCoulomb.antitoneOn_forbidden hc hσ0 hts' hI h
    have hts0 := hallow ts ⟨hhalf, le_rfl⟩
    rw [abs_of_pos (by linarith)]
    exact hmono.trans ((le_abs_self _).trans hts0)

/-- `f(½) = (3/4)(σ − c²/4)y(½)² + U(½)²`. -/
theorem soninF_half (c σ : ℝ) :
    soninF c σ (1 / 2) = 3 / 4 * (σ - c ^ 2 / 4) * regSol (sqC c) σ (1 / 2) ^ 2 + regU (sqC c) σ (1 / 2) ^ 2 := by
  unfold soninF; ring

/-- **The mass bound**: for `c ≥ 2` and `c²/4 ≤ σ < 5c²/8`, `N = ∫_{½}^1 y² ≤ (3/4)((cy(½))² + y'(½)²)`. -/
theorem nodeMass_le_far (hc : 2 ≤ c) (hσ4 : c ^ 2 / 4 ≤ σ) (hσ : σ < 5 * c ^ 2 / 8) :
    nodeMass c σ ≤ 3 / 4 * ((c * regSol (sqC c) σ (1 / 2)) ^ 2 + regV (sqC c) σ (1 / 2) ^ 2) := by
  have hc0 : 0 < c := by linarith
  have hc2 : 0 < c ^ 2 := by positivity
  have hσ0 : 0 < σ := by linarith
  have hσ1 : σ < c ^ 2 := by linarith
  set a := regSol (sqC c) σ (1 / 2)
  set u := regU (sqC c) σ (1 / 2)
  set D := (c * a) ^ 2 + regV (sqC c) σ (1 / 2) ^ 2 with hD
  have hDe : D = c ^ 2 * a ^ 2 + 16 / 9 * u ^ 2 := by rw [hD, regV_half]; ring
  set f := soninF c σ (1 / 2)
  have hf : f = 3 / 4 * (σ - c ^ 2 / 4) * a ^ 2 + u ^ 2 := soninF_half c σ
  have hf0 : 0 ≤ f := by rw [hf]; have := sq_nonneg a; have := sq_nonneg u; nlinarith
  have hfD : f ≤ 9 / 16 * D := by
    rw [hf, hDe]
    have : 3 / 4 * (σ - c ^ 2 / 4) * a ^ 2 ≤ 3 / 4 * (3 * c ^ 2 / 8) * a ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg a)
    have := mul_nonneg hc2.le (sq_nonneg a)
    linarith
  set ts := √(σ / c ^ 2)
  have hts2 : ts ^ 2 = σ / c ^ 2 := Real.sq_sqrt (div_pos hσ0 hc2).le
  have hτ : σ / c ^ 2 < 5 / 8 := by rw [div_lt_iff₀ hc2]; linarith
  have hτ4 : 1 / 4 ≤ σ / c ^ 2 := by rw [le_div_iff₀ hc2]; linarith
  have hts45 : ts ≤ 4 / 5 := by nlinarith [Real.sqrt_nonneg (σ / c ^ 2)]
  have hhalf : 1 / 2 ≤ ts := by nlinarith [Real.sqrt_nonneg (σ / c ^ 2)]
  have hps : 3 / 8 < 1 - σ / c ^ 2 := by linarith
  set B := (ts - 1 / 2) / (1 - σ / c ^ 2)
  have hB0 : 0 ≤ B := div_nonneg (by linarith) (by linarith)
  have hB : B ≤ 4 / 5 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  set A := |a| + B * √f
  have hA : ∀ t ∈ Icc (1 / 2 : ℝ) 1, regSol (sqC c) σ t ^ 2 ≤ A ^ 2 := by
    intro t ht
    have h := abs_regSol_le_half hc0 hσ4 hσ1 ht
    have e : (ts - 1 / 2) * √f / (1 - σ / c ^ 2) = B * √f := by simp only [B]; ring
    rw [e] at h
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
  have hint : nodeMass c σ ≤ (1 - 1 / 2) * A ^ 2 := by
    unfold nodeMass
    have hcont : ContinuousOn (fun t => regSol (sqC c) σ t ^ 2) (Icc (1 / 2 : ℝ) 1) :=
      ((continuousOn_regSol (sqC c) σ).mono fun t ht => show (-1 : ℝ) < t by linarith [ht.1]).pow 2
    have hii : IntervalIntegrable (fun t => regSol (sqC c) σ t ^ 2) volume (1 / 2 : ℝ) 1 := by
      rw [← uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)] at hcont; exact hcont.intervalIntegrable
    have := intervalIntegral.integral_mono_on (by norm_num : (1 / 2 : ℝ) ≤ 1) hii
      (intervalIntegrable_const (c := A ^ 2)) hA
    rwa [intervalIntegral.integral_const, smul_eq_mul] at this
  have hsq : (√f) ^ 2 = f := Real.sq_sqrt hf0
  have ha2 : a ^ 2 ≤ D / 4 := by
    have h4 : 4 * a ^ 2 ≤ c ^ 2 * a ^ 2 := mul_le_mul_of_nonneg_right (by nlinarith) (sq_nonneg a)
    rw [hDe]; have := sq_nonneg u; linarith
  have hA2 : A ^ 2 ≤ 2 * a ^ 2 + 2 * (B * √f) ^ 2 := by
    have h1 := sq_nonneg (|a| - B * √f)
    have h2 := sq_abs a
    show (|a| + B * √f) ^ 2 ≤ _
    nlinarith
  have hBf : (B * √f) ^ 2 ≤ 16 / 25 * f := by
    rw [mul_pow, hsq]; exact mul_le_mul_of_nonneg_right (by nlinarith) hf0
  nlinarith

/-- **The far Robin rate**: for `c ≥ 2` and `c²/4 ≤ σ < 5c²/8`, `θ'(σ) ≤ c`. -/
theorem nodeRate_le_far (hc : 2 ≤ c) (hσ4 : c ^ 2 / 4 ≤ σ) (hσ : σ < 5 * c ^ 2 / 8) : nodeRate c σ ≤ c := by
  have hc0 : 0 < c := by linarith
  have hD := Cvs.Prolate.LiouvilleGreen.RobinCellPhaseIncrement.refNorm_pos hc0.ne' σ
  have hN := nodeMass_le_far hc hσ4 hσ
  unfold nodeRate
  rw [div_le_iff₀ hD]
  have : 4 * c / 3 * nodeMass c σ ≤ 4 * c / 3 * (3 / 4 *
      ((c * regSol (sqC c) σ (1 / 2)) ^ 2 + regV (sqC c) σ (1 / 2) ^ 2)) :=
    mul_le_mul_of_nonneg_left hN (by positivity)
  linarith

end Cvs.Prolate.LiouvilleGreen.FarRobinRate

end
