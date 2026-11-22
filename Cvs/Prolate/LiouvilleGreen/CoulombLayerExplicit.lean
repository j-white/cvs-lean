import Mathlib
import Cvs.Prolate.LiouvilleGreen.AdiabaticStretchBounds
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.LiouvilleGreen.RegularSolutionNodeLaw
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
# The Coulomb layer with an explicit constant: `AdiabaticStretchBounds`'s `CoulombLayer B c₀` for `c₀ = 4(4B + 4)`

On `[t_c, 1]`, `t_c = 1 − U₀/c`, `U₀ = 4B + 4`: steps of length `1/(2Q̄)`, `Q̄ = c(2B + 4U₀) ≥ |q|`, double
`max |y|`, so `|y| ≤ 2ⁿ`; `f = pqy² + U²` has `f' = −g y²`, `f(1) = 0`, and `g ≥ 0` up to the turning point, `∫ g = 0`
beyond it while `y² ↓`, so `f(t_c) ≥ c²ℓ²/4`; hence `G(t_c) ≥ f(t_c)/a(t_c)` bounds `∫_{t_c}^1 y² ≤ U₀4ⁿ/c`.
-/

noncomputable section

open Real Set Filter Topology MeasureTheory intervalIntegral
open Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval (pP)
open Cvs.Prolate.RegularSolutionEdge (regSol regU regV sqC continuousOn_regSol hasDerivAt_regSol hasDerivAt_regU pP_mul_regV regSol_one)
open Cvs.Prolate.TopRungDepthBound (af qf wf af_pos af_sq sqC_apply)
open Cvs.Prolate.LiouvilleGreen.AdiabaticStretchBounds (energyAt qf_eq LayerBound CoulombLayer)

namespace Cvs.Prolate.LiouvilleGreen.CoulombLayerExplicit

variable {c σ : ℝ}

/-- `U(t) = ∫_t^1 (c²s² − σ)y`, so `|U(t)| ≤ Q̄ Y (1 − t)` when `|c²s² − σ| ≤ Q̄` and `|y| ≤ Y` on `[t, 1]`. -/
theorem abs_regU_le_of {t Q Y : ℝ} (ht : t ≤ 1) (hQ : ∀ s ∈ Icc t 1, |c ^ 2 * s ^ 2 - σ| ≤ Q)
    (hY : ∀ s ∈ Icc t 1, |regSol (sqC c) σ s| ≤ Y) (hQ0 : 0 ≤ Q) :
    |regU (sqC c) σ t| ≤ Q * Y * (1 - t) := by
  unfold regU
  rw [abs_neg]
  have hb : ∀ s ∈ uIoc (1 : ℝ) t, ‖(sqC c s - σ) * regSol (sqC c) σ s‖ ≤ Q * Y := by
    intro s hs
    rw [uIoc_of_ge ht] at hs
    have hsI : s ∈ Icc t 1 := ⟨hs.1.le, hs.2⟩
    rw [Real.norm_eq_abs, abs_mul, sqC_apply]
    exact mul_le_mul (hQ s hsI) (hY s hsI) (abs_nonneg _) hQ0
  have h := norm_integral_le_of_norm_le_const hb
  rw [Real.norm_eq_abs, abs_of_nonpos (by linarith : t - 1 ≤ 0)] at h
  linarith

/-- `|y'(v)| ≤ Q̄Y` on `[t, 1)` for `t ≥ 0`, from `y' = −U/(1 − v²)`. -/
theorem abs_regV_le_of {t v Q Y : ℝ} (ht0 : 0 ≤ t) (hv : v ∈ Ico t 1)
    (hQ : ∀ s ∈ Icc t 1, |c ^ 2 * s ^ 2 - σ| ≤ Q) (hY : ∀ s ∈ Icc t 1, |regSol (sqC c) σ s| ≤ Y)
    (hQ0 : 0 ≤ Q) : |regV (sqC c) σ v| ≤ Q * Y := by
  have hv1 : v < 1 := hv.2
  have hv0 : 0 ≤ v := ht0.trans hv.1
  have hp : 0 < 1 - v ^ 2 := by nlinarith
  have hpv := pP_mul_regV (sqC c) σ (show (-1 : ℝ) < v by linarith)
  unfold pP at hpv
  have hV : regV (sqC c) σ v = -regU (sqC c) σ v / (1 - v ^ 2) := by field_simp; linarith
  have hU := abs_regU_le_of hv1.le (fun s hs => hQ s ⟨hv.1.trans hs.1, hs.2⟩)
    (fun s hs => hY s ⟨hv.1.trans hs.1, hs.2⟩) hQ0
  have hY0 : 0 ≤ Y := (abs_nonneg _).trans (hY v ⟨hv.1, hv1.le⟩)
  rw [hV, abs_div, abs_neg, abs_of_pos hp, div_le_iff₀ hp]
  have e : 1 - v ^ 2 = (1 - v) * (1 + v) := by ring
  rw [e]
  have h1 : Q * Y * (1 - v) ≤ Q * Y * ((1 - v) * (1 + v)) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity); nlinarith
  linarith

/-- **The doubling steps**: if `|c²s² − σ| ≤ Q̄` on `[1 − L, 1] ⊆ [0, 1]`, then `|y| ≤ 2^m` on `[1 − m/(2Q̄), 1]`
whenever `m/(2Q̄) ≤ L`. -/
theorem abs_regSol_le_pow {Q L : ℝ} (hQ0 : 0 < Q) (hL1 : L ≤ 1)
    (hQ : ∀ s ∈ Icc (1 - L) 1, |c ^ 2 * s ^ 2 - σ| ≤ Q) :
    ∀ m : ℕ, (m : ℝ) / (2 * Q) ≤ L → ∀ t ∈ Icc (1 - m / (2 * Q)) 1, |regSol (sqC c) σ t| ≤ 2 ^ m := by
  intro m
  induction m with
  | zero =>
    intro _ t ht
    simp only [Nat.cast_zero, zero_div, sub_zero] at ht
    rw [le_antisymm ht.2 ht.1, regSol_one]; simp
  | succ m ih =>
    intro hm t ht
    set a := 1 - ((m + 1 : ℕ) : ℝ) / (2 * Q)
    set b := 1 - (m : ℝ) / (2 * Q)
    have hab : a ≤ b := by simp only [a, b]; push_cast; gcongr; linarith
    have hb1 : b ≤ 1 := by
      have : 0 ≤ (m : ℝ) / (2 * Q) := by positivity
      simp only [b]; linarith
    have hmL : (m : ℝ) / (2 * Q) ≤ L := le_trans (by gcongr; linarith) hm
    have ha0 : 0 ≤ a := by simp only [a]; linarith
    have hcont : ContinuousOn (fun s => |regSol (sqC c) σ s|) (Icc a 1) :=
      ((continuousOn_regSol (sqC c) σ).mono fun s hs => show (-1 : ℝ) < s by linarith [hs.1]).abs
    obtain ⟨tm, htm, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr (hab.trans hb1)) hcont
    set Y := |regSol (sqC c) σ tm|
    have hY : ∀ s ∈ Icc a 1, |regSol (sqC c) σ s| ≤ Y := fun s hs => hmax hs
    have hQa : ∀ s ∈ Icc a 1, |c ^ 2 * s ^ 2 - σ| ≤ Q := fun s hs =>
      hQ s ⟨by simp only [a] at hs; linarith [hs.1], hs.2⟩
    have hYm : Y ≤ 2 ^ (m + 1) := by
      rcases le_or_gt b tm with h | h
      · have := ih hmL tm ⟨h, htm.2⟩
        calc Y ≤ 2 ^ m := this
          _ ≤ 2 ^ (m + 1) := pow_le_pow_right₀ (by norm_num) (Nat.le_succ m)
      · -- `|y(tm) − y(b)| ≤ (b − tm) Q̄ Y ≤ Y/2`
        have hderiv : ∀ x ∈ Icc tm b, HasDerivWithinAt (regSol (sqC c) σ) (regV (sqC c) σ x) (Icc tm b) x :=
          fun x hx => (hasDerivAt_regSol (sqC c) σ (by linarith [htm.1, hx.1])).hasDerivWithinAt
        have hbound : ∀ x ∈ Ico tm b, ‖regV (sqC c) σ x‖ ≤ Q * Y := fun x hx =>
          abs_regV_le_of ha0 ⟨htm.1.trans hx.1, hx.2.trans_le hb1⟩ hQa hY hQ0.le
        have hmv := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound b ⟨h.le, le_rfl⟩
        rw [Real.norm_eq_abs] at hmv
        have hyb := ih hmL b ⟨le_rfl, hb1⟩
        have hlen : Q * Y * (b - tm) ≤ Y / 2 := by
          have : b - tm ≤ 1 / (2 * Q) := by
            have : b - a = 1 / (2 * Q) := by simp only [a, b]; push_cast; field_simp; ring
            linarith [htm.1]
          calc Q * Y * (b - tm) ≤ Q * Y * (1 / (2 * Q)) := mul_le_mul_of_nonneg_left this (by positivity)
            _ = Y / 2 := by field_simp
        have := abs_sub_abs_le_abs_sub (regSol (sqC c) σ tm) (regSol (sqC c) σ b)
        rw [abs_sub_comm] at hmv
        have h2 : (2 : ℝ) ^ (m + 1) = 2 * 2 ^ m := by ring
        linarith
    exact (hY t ⟨by simpa [a] using ht.1, ht.2⟩).trans hYm

/-- The Sonin–Pólya flux `f = (1 − t²)(σ − c²t²)y² + U²`. -/
def soninF (c σ t : ℝ) : ℝ :=
  (1 - t ^ 2) * (σ - c ^ 2 * t ^ 2) * regSol (sqC c) σ t ^ 2 + regU (sqC c) σ t ^ 2

/-- The rate `g = 2t(σ + c² − 2c²t²) = −((1 − t²)(σ − c²t²))'`. -/
def soninG (c σ t : ℝ) : ℝ := 2 * t * (σ + c ^ 2 - 2 * c ^ 2 * t ^ 2)

/-- **`f' = −g y²`** for `t > −1`. -/
theorem hasDerivAt_soninF {t : ℝ} (ht : -1 < t) :
    HasDerivAt (soninF c σ) (-(soninG c σ t * regSol (sqC c) σ t ^ 2)) t := by
  have hy := hasDerivAt_regSol (sqC c) σ ht
  have hU := hasDerivAt_regU (sqC c) σ ht
  have hpv := pP_mul_regV (sqC c) σ ht
  unfold pP at hpv
  have hpq : HasDerivAt (fun t => (1 - t ^ 2) * (σ - c ^ 2 * t ^ 2))
      (-(2 * t) * (σ - c ^ 2 * t ^ 2) + (1 - t ^ 2) * (-(c ^ 2 * (2 * t)))) t := by
    have h1 : HasDerivAt (fun t : ℝ => 1 - t ^ 2) (-(2 * t)) t := by
      simpa using (hasDerivAt_pow 2 t).const_sub 1
    have h2 : HasDerivAt (fun t : ℝ => σ - c ^ 2 * t ^ 2) (-(c ^ 2 * (2 * t))) t := by
      simpa using ((hasDerivAt_pow 2 t).const_mul (c ^ 2)).const_sub σ
    exact h1.mul h2
  have h := (hpq.mul (hy.pow 2)).add (hU.pow 2)
  unfold soninF
  refine h.congr_deriv ?_
  unfold soninG
  rw [sqC_apply]
  simp only [Nat.cast_ofNat, Pi.pow_apply]
  linear_combination (-(2 * (σ - c ^ 2 * t ^ 2) * regSol (sqC c) σ t)) * hpv

theorem regU_one (c σ : ℝ) : regU (sqC c) σ 1 = 0 := by simp [regU]

/-- **The flux as an integral**: `f(t₀) = ∫_{t₀}^1 g y²` for `−1 < t₀ ≤ 1`. -/
theorem soninF_eq_integral {t₀ : ℝ} (ht₀ : -1 < t₀) (ht1 : t₀ ≤ 1) :
    soninF c σ t₀ = ∫ t in t₀..1, soninG c σ t * regSol (sqC c) σ t ^ 2 := by
  have hd : ∀ t ∈ uIcc t₀ 1, HasDerivAt (soninF c σ) (-(soninG c σ t * regSol (sqC c) σ t ^ 2)) t :=
    fun t ht => hasDerivAt_soninF (by rw [uIcc_of_le ht1] at ht; linarith [ht.1])
  have hc : ContinuousOn (fun t => -(soninG c σ t * regSol (sqC c) σ t ^ 2)) (uIcc t₀ 1) := by
    rw [uIcc_of_le ht1]
    have : ContinuousOn (regSol (sqC c) σ) (Icc t₀ 1) :=
      (continuousOn_regSol (sqC c) σ).mono fun t ht => show (-1 : ℝ) < t by linarith [ht.1]
    unfold soninG
    exact ((by fun_prop : Continuous fun t : ℝ => 2 * t * (σ + c ^ 2 - 2 * c ^ 2 * t ^ 2)).continuousOn.mul
      (this.pow 2)).neg
  have h := integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable
  rw [intervalIntegral.integral_neg] at h
  have h1 : soninF c σ 1 = 0 := by unfold soninF; rw [regU_one]; ring
  linarith

/-- **The local piece**: if `g ≥ 2c²(e − t)` and `y² ≥ ¼` on `[e − ℓ, e]`, then `∫_{e−ℓ}^e g y² ≥ c²ℓ²/4`. -/
theorem piece_ge {e ℓ : ℝ} (hℓ : 0 ≤ ℓ) (he : -1 < e - ℓ)
    (hg : ∀ t ∈ Icc (e - ℓ) e, 2 * c ^ 2 * (e - t) ≤ soninG c σ t)
    (hy : ∀ t ∈ Icc (e - ℓ) e, 1 / 4 ≤ regSol (sqC c) σ t ^ 2) :
    c ^ 2 * ℓ ^ 2 / 4 ≤ ∫ t in (e - ℓ)..e, soninG c σ t * regSol (sqC c) σ t ^ 2 := by
  have hle : e - ℓ ≤ e := by linarith
  have hyc : ContinuousOn (regSol (sqC c) σ) (Icc (e - ℓ) e) :=
    (continuousOn_regSol (sqC c) σ).mono fun t ht => show (-1 : ℝ) < t by linarith [ht.1]
  have hint : IntervalIntegrable (fun t => soninG c σ t * regSol (sqC c) σ t ^ 2) volume (e - ℓ) e := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hle]; unfold soninG
    exact (by fun_prop : Continuous fun t : ℝ => 2 * t * (σ + c ^ 2 - 2 * c ^ 2 * t ^ 2)).continuousOn.mul
      (hyc.pow 2)
  have hlin : Continuous fun t : ℝ => c ^ 2 / 2 * (e - t) := by fun_prop
  have hmono := integral_mono_on hle (hlin.intervalIntegrable _ _) hint fun t ht => by
      have h1 := hg t ht
      have h2 := hy t ht
      have h3 : 0 ≤ 2 * c ^ 2 * (e - t) := by have := ht.2; positivity
      calc c ^ 2 / 2 * (e - t) = 2 * c ^ 2 * (e - t) * (1 / 4) := by ring
        _ ≤ soninG c σ t * regSol (sqC c) σ t ^ 2 := mul_le_mul h1 h2 (by norm_num) (h3.trans h1)
  have hval : ∫ t in (e - ℓ)..e, c ^ 2 / 2 * (e - t) = c ^ 2 * ℓ ^ 2 / 4 := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub intervalIntegrable_const
      intervalIntegrable_id, integral_id, intervalIntegral.integral_const, smul_eq_mul]
    ring
  linarith

/-- `y ≥ ½` near a point `e` with `y(e) ≥ 1` on a window `ℓ` with `Q̄Yℓ ≤ ½`. -/
theorem half_le_of_near {e ℓ t₀ Q Y : ℝ} (ht₀ : 0 ≤ t₀) (hwin : t₀ ≤ e - ℓ) (he1 : e ≤ 1) (hℓ : 0 ≤ ℓ)
    (hQ : ∀ s ∈ Icc t₀ 1, |c ^ 2 * s ^ 2 - σ| ≤ Q) (hY : ∀ s ∈ Icc t₀ 1, |regSol (sqC c) σ s| ≤ Y)
    (hQ0 : 0 ≤ Q) (hsmall : Q * Y * ℓ ≤ 1 / 2) (hye : 1 ≤ regSol (sqC c) σ e) :
    ∀ t ∈ Icc (e - ℓ) e, 1 / 4 ≤ regSol (sqC c) σ t ^ 2 := by
  intro t ht
  have hderiv : ∀ x ∈ Icc t e, HasDerivWithinAt (regSol (sqC c) σ) (regV (sqC c) σ x) (Icc t e) x :=
    fun x hx => (hasDerivAt_regSol (sqC c) σ (by linarith [ht.1, hx.1])).hasDerivWithinAt
  have hbound : ∀ x ∈ Ico t e, ‖regV (sqC c) σ x‖ ≤ Q * Y := fun x hx =>
    abs_regV_le_of ht₀ ⟨hwin.trans (ht.1.trans hx.1), hx.2.trans_le he1⟩ hQ hY hQ0
  have h := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound e ⟨ht.2, le_rfl⟩
  rw [Real.norm_eq_abs] at h
  have h2 : Q * Y * (e - t) ≤ 1 / 2 := by
    have hY0 : 0 ≤ Q * Y := mul_nonneg hQ0 ((abs_nonneg _).trans (hY e ⟨by linarith, he1⟩))
    calc Q * Y * (e - t) ≤ Q * Y * ℓ := mul_le_mul_of_nonneg_left (by linarith [ht.1]) hY0
      _ ≤ 1 / 2 := hsmall
  have h3 : 1 / 2 ≤ regSol (sqC c) σ t := by
    have := le_abs_self (regSol (sqC c) σ e - regSol (sqC c) σ t)
    linarith
  nlinarith

/-- **Beyond the turning point**: for `0 < σ < c²` and `t* = √(σ/c²)`, `∫_{t*}^1 g y² ≥ 0`, since `y ≥ 1` decreases
there, `g` changes sign once, at `t_f = √((σ + c²)/(2c²))`, and `∫_{t*}^1 g = 0`. -/
theorem forbidden_nonneg (hc : 0 < c) (hσ0 : 0 < σ) (hσ : σ < c ^ 2) :
    0 ≤ ∫ t in √(σ / c ^ 2)..1, soninG c σ t * regSol (sqC c) σ t ^ 2 := by
  set ts := √(σ / c ^ 2)
  set y := regSol (sqC c) σ
  have hc2 : 0 < c ^ 2 := by positivity
  have hts0 : 0 < ts := Real.sqrt_pos.mpr (div_pos hσ0 hc2)
  have hts2 : ts ^ 2 = σ / c ^ 2 := Real.sq_sqrt (div_pos hσ0 hc2).le
  have hts1 : ts ≤ 1 := by
    rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt (by rw [div_le_one hc2]; linarith)
  have hσts : σ = c ^ 2 * ts ^ 2 := by rw [hts2]; field_simp
  -- `y ≥ 1` on `[t*, 1]`
  have hy1 : ∀ x ∈ Icc ts 1, 1 ≤ y x := by
    intro x hx
    have h := Cvs.Prolate.LiouvilleGreen.RegularSolutionNodeLaw.one_le_regSol (c := c) (τ := σ / c ^ 2) x hx
    rwa [show c ^ 2 * (σ / c ^ 2) = σ by field_simp] at h
  -- `y` decreases on `[t*, 1]`
  have hanti : AntitoneOn y (Icc ts 1) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := regV (sqC c) σ) (convex_Icc ts 1)
      ((continuousOn_regSol (sqC c) σ).mono fun x hx => show (-1 : ℝ) < x by linarith [hx.1])
      (fun x hx => ?_) (fun x hx => ?_)
    · rw [interior_Icc] at hx
      exact (hasDerivAt_regSol (sqC c) σ (by linarith [hx.1])).hasDerivWithinAt
    · rw [interior_Icc] at hx
      have hx1 : -1 < x := by linarith [hx.1]
      have hpv := pP_mul_regV (sqC c) σ hx1
      unfold pP at hpv
      have hp : x ^ 2 - 1 < 0 := by nlinarith [hx.1, hx.2]
      have hU : 0 ≤ regU (sqC c) σ x := by
        unfold regU
        rw [intervalIntegral.integral_symm, neg_neg]
        refine intervalIntegral.integral_nonneg hx.2.le fun s hs => ?_
        rw [sqC_apply]
        have h1 : σ ≤ c ^ 2 * s ^ 2 := by
          rw [hσts]; have : ts ^ 2 ≤ s ^ 2 := by nlinarith [hs.1, hx.1]
          exact mul_le_mul_of_nonneg_left this hc2.le
        exact mul_nonneg (by linarith) (by linarith [hy1 s ⟨hx.1.le.trans hs.1, hs.2⟩])
      nlinarith
  -- the sign change of `g`
  set tf := √((σ + c ^ 2) / (2 * c ^ 2))
  have htf2 : tf ^ 2 = (σ + c ^ 2) / (2 * c ^ 2) := Real.sq_sqrt (by positivity)
  have htf1 : tf ≤ 1 := by
    rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt (by rw [div_le_one (by positivity)]; linarith)
  have htsf : ts ≤ tf := Real.sqrt_le_sqrt (by
    rw [div_le_div_iff₀ hc2 (by positivity)]; nlinarith)
  have hpt : ∀ t ∈ Icc ts 1, 0 ≤ soninG c σ t * (y t ^ 2 - y tf ^ 2) := by
    intro t ht
    have ht0 : 0 ≤ t := hts0.le.trans ht.1
    have hyt := hy1 t ht
    have hyf := hy1 tf ⟨htsf, htf1⟩
    unfold soninG
    rcases le_total t tf with h | h
    · have hg : 0 ≤ σ + c ^ 2 - 2 * c ^ 2 * t ^ 2 := by
        have : t ^ 2 ≤ tf ^ 2 := by nlinarith
        rw [htf2] at this
        have := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ 2 * c ^ 2)
        rw [mul_div_cancel₀ _ (by positivity)] at this
        linarith
      have hyy : y tf ≤ y t := hanti ht ⟨htsf, htf1⟩ h
      have : 0 ≤ y t ^ 2 - y tf ^ 2 := by nlinarith
      positivity
    · have hg : σ + c ^ 2 - 2 * c ^ 2 * t ^ 2 ≤ 0 := by
        have : tf ^ 2 ≤ t ^ 2 := by nlinarith [htsf]
        rw [htf2] at this
        have := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ 2 * c ^ 2)
        rw [mul_div_cancel₀ _ (by positivity)] at this
        linarith
      have hyy : y t ≤ y tf := hanti ⟨htsf, htf1⟩ ht h
      have : y t ^ 2 - y tf ^ 2 ≤ 0 := by nlinarith
      have : 2 * t * (σ + c ^ 2 - 2 * c ^ 2 * t ^ 2) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hg
      nlinarith
  -- `∫_{t*}^1 g = 0`
  have hgint : ∫ t in ts..1, soninG c σ t = 0 := by
    have hd : ∀ t ∈ uIcc ts 1, HasDerivAt (fun t => -((1 - t ^ 2) * (σ - c ^ 2 * t ^ 2))) (soninG c σ t) t := by
      intro t _
      have h1 : HasDerivAt (fun t : ℝ => 1 - t ^ 2) (-(2 * t)) t := by
        simpa using (hasDerivAt_pow 2 t).const_sub 1
      have h2 : HasDerivAt (fun t : ℝ => σ - c ^ 2 * t ^ 2) (-(c ^ 2 * (2 * t))) t := by
        simpa using ((hasDerivAt_pow 2 t).const_mul (c ^ 2)).const_sub σ
      refine (h1.mul h2).neg.congr_deriv ?_
      unfold soninG; ring
    have hcg : ContinuousOn (soninG c σ) (uIcc ts 1) := by unfold soninG; fun_prop
    rw [integral_eq_sub_of_hasDerivAt hd hcg.intervalIntegrable, hσts]
    ring
  have hyc : ContinuousOn y (Icc ts 1) :=
    (continuousOn_regSol (sqC c) σ).mono fun x hx => show (-1 : ℝ) < x by linarith [hx.1]
  have hcg : ContinuousOn (soninG c σ) (Icc ts 1) := by unfold soninG; fun_prop
  have hi1 : IntervalIntegrable (fun t => soninG c σ t * (y t ^ 2 - y tf ^ 2)) volume ts 1 :=
    (by rw [uIcc_of_le hts1]; exact hcg.mul ((hyc.pow 2).sub continuousOn_const) :
      ContinuousOn _ (uIcc ts 1)).intervalIntegrable
  have hi2 : IntervalIntegrable (fun t => y tf ^ 2 * soninG c σ t) volume ts 1 :=
    (by rw [uIcc_of_le hts1]; exact continuousOn_const.mul hcg : ContinuousOn _ (uIcc ts 1)).intervalIntegrable
  have hsplit : ∫ t in ts..1, soninG c σ t * y t ^ 2 =
      (∫ t in ts..1, soninG c σ t * (y t ^ 2 - y tf ^ 2)) + ∫ t in ts..1, y tf ^ 2 * soninG c σ t := by
    rw [← intervalIntegral.integral_add hi1 hi2]
    congr 1; funext t; ring
  rw [hsplit, intervalIntegral.integral_const_mul, hgint, mul_zero, add_zero]
  exact intervalIntegral.integral_nonneg hts1 hpt

/-- **The Coulomb edge is adiabatic**: for `B ≥ 0`, `c ≥ 4U₀`, `U₀ = 4B + 4` and `σ − c² ≥ −2cB`,
`q(1 − U₀/c) ≥ c(5B + 7)` and `|w(1 − U₀/c)| ≤ ½`. -/
theorem abs_wf_coulomb {B : ℝ} (hB : 0 ≤ B) (hc : 4 * (4 * B + 4) ≤ c)
    (hσl : -(2 * c * B) ≤ σ - c ^ 2) :
    c * (5 * B + 7) ≤ qf c ((c ^ 2 - σ) / c) (1 - (4 * B + 4) / c) ∧
      |wf c ((c ^ 2 - σ) / c) (1 - (4 * B + 4) / c)| ≤ 1 / 2 := by
  set U₀ := 4 * B + 4
  set K := (c ^ 2 - σ) / c
  have hc0 : 0 < c := by linarith
  set s := U₀ / c with hs
  have hs0 : 0 < s := by positivity
  have hs4 : s ≤ 1 / 4 := by rw [hs, div_le_iff₀ hc0]; linarith
  have hsc : c * s = U₀ := by rw [hs]; field_simp
  set t := 1 - s
  have hq : c * (5 * B + 7) ≤ qf c K t := by
    rw [qf_eq hc0.ne']
    have e : σ - c ^ 2 * t ^ 2 = (σ - c ^ 2) + c * (c * s) * (2 - s) := by simp only [t]; ring
    rw [e, hsc]
    have : U₀ * (7 / 4) ≤ U₀ * (2 - s) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    nlinarith
  refine ⟨hq, ?_⟩
  have hqp : 0 < qf c K t := lt_of_lt_of_le (by positivity) hq
  have ht2 : t ^ 2 < 1 := by simp only [t]; nlinarith
  have ht0 : 0 ≤ t := by simp only [t]; linarith
  set p := 1 - t ^ 2 with hp
  have hpe : p = s * (2 - s) := by simp only [hp, t]; ring
  have hp0 : 0 < p := by rw [hpe]; nlinarith
  have hpU : p ≤ 2 * U₀ / c := by
    rw [hpe, le_div_iff₀ hc0]; nlinarith
  have hpl : 7 / 4 * s ≤ p := by rw [hpe]; nlinarith
  have ha := af_pos ht2 hqp
  have ha2 : af c K t ^ 2 = p * qf c K t := af_sq ht2 hqp
  set a := af c K t
  set q := qf c K t
  have ha7 : 7 ≤ a := by
    have h1 : 7 / 4 * s * (c * (5 * B + 7)) ≤ p * q := mul_le_mul hpl hq (by positivity) hp0.le
    have h2 : 7 / 4 * s * (c * (5 * B + 7)) = 7 / 4 * U₀ * (5 * B + 7) := by rw [← hsc]; ring
    have : (7 : ℝ) ^ 2 ≤ a ^ 2 := by rw [ha2]; nlinarith
    exact (pow_le_pow_iff_left₀ (by norm_num) ha.le two_ne_zero).mp this
  have hw0 : wf c K t ≤ 0 := Cvs.Prolate.TopRungDepthBound.wf_nonpos ht0 ht2 hqp
  have hw : wf c K t = -(t / a + c ^ 2 * t * p / (a * q)) := rfl
  rw [abs_of_nonpos hw0, hw, neg_neg]
  have h1 : t / a ≤ 1 / 7 := by
    rw [div_le_div_iff₀ ha (by norm_num)]; simp only [t]; linarith
  have h2 : c ^ 2 * t * p / (a * q) ≤ 1 / 3 := by
    rw [div_le_div_iff₀ (mul_pos ha hqp) (by norm_num)]
    have hcube : 9 * c ^ 4 * p ≤ q ^ 3 := by
      have h3 : (c * (5 * B + 7)) ^ 3 ≤ q ^ 3 := pow_le_pow_left₀ (by positivity) hq 3
      have h4 : 9 * c ^ 4 * p ≤ 9 * c ^ 4 * (2 * U₀ / c) := mul_le_mul_of_nonneg_left hpU (by positivity)
      have h5 : 9 * c ^ 4 * (2 * U₀ / c) = c ^ 3 * (18 * U₀) := by field_simp; ring
      have h6 : 18 * U₀ ≤ (5 * B + 7) ^ 3 := by simp only [U₀]; nlinarith [sq_nonneg B]
      have h7 : c ^ 3 * (18 * U₀) ≤ c ^ 3 * (5 * B + 7) ^ 3 := mul_le_mul_of_nonneg_left h6 (by positivity)
      rw [mul_pow] at h3
      linarith
    -- `(3c²tp)² ≤ (aq)²`
    have hsq : (3 * (c ^ 2 * t * p)) ^ 2 ≤ (a * q) ^ 2 := by
      have ht1 : t ≤ 1 := by simp only [t]; linarith
      have e : (a * q) ^ 2 = p * q ^ 3 := by rw [mul_pow, ha2]; ring
      rw [e]
      have : (3 * (c ^ 2 * t * p)) ^ 2 ≤ 9 * c ^ 4 * p * p := by
        have : t ^ 2 ≤ 1 := by nlinarith
        have h0 : 0 ≤ c ^ 4 * p ^ 2 := by positivity
        nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hcube hp0.le]
    have hpos : 0 ≤ 3 * (c ^ 2 * t * p) := by positivity
    nlinarith [(pow_le_pow_iff_left₀ hpos (by positivity) two_ne_zero).mp hsq]
  linarith

theorem intervalIntegrable_soninG_mul {a b : ℝ} (ha : -1 < a) (hb : -1 < b) :
    IntervalIntegrable (fun t => soninG c σ t * regSol (sqC c) σ t ^ 2) volume a b := by
  apply ContinuousOn.intervalIntegrable
  have : ContinuousOn (regSol (sqC c) σ) (uIcc a b) := (continuousOn_regSol (sqC c) σ).mono fun t ht =>
    show (-1 : ℝ) < t from lt_of_lt_of_le (lt_min ha hb) ht.1
  unfold soninG
  exact (by fun_prop : Continuous fun t : ℝ => 2 * t * (σ + c ^ 2 - 2 * c ^ 2 * t ^ 2)).continuousOn.mul
    (this.pow 2)

theorem integral_soninG_mul_nonneg {a b : ℝ} (hab : a ≤ b) (hg : ∀ t ∈ Icc a b, 0 ≤ soninG c σ t) :
    0 ≤ ∫ t in a..b, soninG c σ t * regSol (sqC c) σ t ^ 2 :=
  intervalIntegral.integral_nonneg hab fun t ht => mul_nonneg (hg t ht) (sq_nonneg _)

/-- **The flux floor without a turning point**: for `σ ≥ c²`, `½ ≤ t_c ≤ 1 − ℓ`, `ℓ ≥ 0` and `y ≥ ½` on `[1 − ℓ, 1]`,
`f(t_c) ≥ c²ℓ²/4`. -/
theorem soninF_ge_of_le {tc ℓ : ℝ} (hσ : c ^ 2 ≤ σ) (htc : 1 / 2 ≤ tc) (hℓ : 0 ≤ ℓ) (hℓtc : tc ≤ 1 - ℓ)
    (hy : ∀ t ∈ Icc (1 - ℓ) 1, 1 / 4 ≤ regSol (sqC c) σ t ^ 2) : c ^ 2 * ℓ ^ 2 / 4 ≤ soninF c σ tc := by
  rw [soninF_eq_integral (by linarith) (by linarith)]
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_soninG_mul (c := c) (σ := σ) (a := tc) (b := 1 - ℓ) (by linarith) (by linarith))
    (intervalIntegrable_soninG_mul (c := c) (σ := σ) (a := 1 - ℓ) (b := 1) (by linarith) (by norm_num))
  have h1 := integral_soninG_mul_nonneg (c := c) (σ := σ) hℓtc fun t ht => by
    unfold soninG
    have ht0 : 0 ≤ t := by linarith [ht.1]
    have : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
    have : 0 ≤ σ + c ^ 2 - 2 * c ^ 2 * t ^ 2 := by nlinarith
    positivity
  have hg : ∀ t ∈ Icc (1 - ℓ) 1, 2 * c ^ 2 * (1 - t) ≤ soninG c σ t := by
    intro t ht
    unfold soninG
    have ht1 : t ≤ 1 := ht.2
    have ht2 : 1 / 2 ≤ t := by linarith [ht.1]
    have h3 : 2 * c ^ 2 * (1 - t ^ 2) ≤ σ + c ^ 2 - 2 * c ^ 2 * t ^ 2 := by linarith
    have h4 : 1 ≤ 2 * t * (1 + t) := by nlinarith
    have h1t : 0 ≤ 1 - t := by linarith
    have h5 : 0 ≤ 2 * c ^ 2 * (1 - t) := by positivity
    have e : 2 * t * (2 * c ^ 2 * (1 - t ^ 2)) = 2 * c ^ 2 * (1 - t) * (2 * t * (1 + t)) := by ring
    have h6 : 2 * c ^ 2 * (1 - t) ≤ 2 * t * (2 * c ^ 2 * (1 - t ^ 2)) := by
      rw [e]; exact le_mul_of_one_le_right h5 h4
    have h7 : 2 * t * (2 * c ^ 2 * (1 - t ^ 2)) ≤ 2 * t * (σ + c ^ 2 - 2 * c ^ 2 * t ^ 2) :=
      mul_le_mul_of_nonneg_left h3 (by linarith)
    linarith
  have h2 := piece_ge (c := c) (σ := σ) (e := 1) hℓ (by linarith) hg hy
  linarith

/-- **The flux floor across a turning point**: for `0 < σ < c²`, `t* = √(σ/c²)`, `½ ≤ t_c ≤ t* − ℓ`, `ℓ ≥ 0` and
`y ≥ ½` on `[t* − ℓ, t*]`, `f(t_c) ≥ c²ℓ²/4`. -/
theorem soninF_ge_of_lt {tc ℓ : ℝ} (hc : 0 < c) (hσ0 : 0 < σ) (hσ : σ < c ^ 2) (htc : 1 / 2 ≤ tc)
    (hℓ : 0 ≤ ℓ) (hℓtc : tc ≤ √(σ / c ^ 2) - ℓ)
    (hy : ∀ t ∈ Icc (√(σ / c ^ 2) - ℓ) √(σ / c ^ 2), 1 / 4 ≤ regSol (sqC c) σ t ^ 2) :
    c ^ 2 * ℓ ^ 2 / 4 ≤ soninF c σ tc := by
  set ts := √(σ / c ^ 2)
  have hc2 : 0 < c ^ 2 := by positivity
  have hts2 : ts ^ 2 = σ / c ^ 2 := Real.sq_sqrt (div_pos hσ0 hc2).le
  have hts1 : ts ≤ 1 := by
    rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt (by rw [div_le_one hc2]; linarith)
  have hσts : σ = c ^ 2 * ts ^ 2 := by rw [hts2]; field_simp
  rw [soninF_eq_integral (by linarith) (by linarith)]
  have hs1 := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_soninG_mul (c := c) (σ := σ) (a := tc) (b := ts - ℓ) (by linarith) (by linarith))
    (intervalIntegrable_soninG_mul (c := c) (σ := σ) (a := ts - ℓ) (b := ts) (by linarith) (by linarith))
  have hs2 := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_soninG_mul (c := c) (σ := σ) (a := tc) (b := ts) (by linarith) (by linarith))
    (intervalIntegrable_soninG_mul (c := c) (σ := σ) (a := ts) (b := 1) (by linarith) (by norm_num))
  have h1 := integral_soninG_mul_nonneg (c := c) (σ := σ) hℓtc fun t ht => by
    unfold soninG
    have ht0 : 0 ≤ t := by linarith [ht.1]
    have : t ^ 2 ≤ ts ^ 2 := by nlinarith [ht.2]
    have : 0 ≤ σ + c ^ 2 - 2 * c ^ 2 * t ^ 2 := by nlinarith
    positivity
  have hg : ∀ t ∈ Icc (ts - ℓ) ts, 2 * c ^ 2 * (ts - t) ≤ soninG c σ t := by
    intro t ht
    unfold soninG
    have ht2 : 1 / 2 ≤ t := by linarith [ht.1]
    have h0 : 0 ≤ ts - t := by linarith [ht.2]
    have hst : 1 ≤ ts + t := by linarith [ht.2]
    have e1 : σ + c ^ 2 - 2 * c ^ 2 * t ^ 2 = (c ^ 2 - σ) + 2 * c ^ 2 * (ts - t) * (ts + t) := by
      rw [hσts]; ring
    have hp : 0 ≤ 2 * c ^ 2 * (ts - t) := by positivity
    have h3 : 2 * c ^ 2 * (ts - t) ≤ 2 * c ^ 2 * (ts - t) * (ts + t) := le_mul_of_one_le_right hp hst
    have h4 : 2 * c ^ 2 * (ts - t) ≤ σ + c ^ 2 - 2 * c ^ 2 * t ^ 2 := by rw [e1]; linarith
    have h6 : 0 ≤ σ + c ^ 2 - 2 * c ^ 2 * t ^ 2 := le_trans hp h4
    have h7 : σ + c ^ 2 - 2 * c ^ 2 * t ^ 2 ≤ 2 * t * (σ + c ^ 2 - 2 * c ^ 2 * t ^ 2) :=
      le_mul_of_one_le_left h6 (by linarith)
    linarith
  have h2 := piece_ge (c := c) (σ := σ) (e := ts) hℓ (by linarith) hg hy
  have h3 := forbidden_nonneg hc hσ0 hσ
  linarith

set_option maxHeartbeats 1600000 in
/-- **Lemma 3.8 (the Coulomb layer)** with an explicit constant: `AdiabaticStretchBounds`'s `CoulombLayer B c₀` holds for
`c₀ = 4(4B + 4)`. -/
theorem coulombLayer {B : ℝ} (hB : 0 ≤ B) : CoulombLayer B (4 * (4 * B + 4)) := by
  set U₀ := 4 * B + 4 with hU₀
  set W := 2 * B + 4 * U₀ with hW
  obtain ⟨n, hn1, hn2⟩ : ∃ n : ℕ, 2 * U₀ * W ≤ n ∧ (n : ℝ) < 2 * U₀ * W + 1 :=
    ⟨⌈2 * U₀ * W⌉₊, Nat.le_ceil _, Nat.ceil_lt_add_one (by simp only [hW, hU₀]; positivity)⟩
  obtain ⟨Yh, hYhd⟩ : ∃ Yh : ℝ, Yh = 2 ^ n := ⟨_, rfl⟩
  set A2 := 2 * U₀ * W
  have hU4 : 4 ≤ U₀ := by simp only [hU₀]; linarith
  have hW16 : 16 ≤ W := by simp only [hW]; linarith
  have hYh : 1 ≤ Yh := by rw [hYhd]; exact one_le_pow₀ (by norm_num)
  have hA2 : 0 < A2 := by positivity
  refine ⟨16 * U₀ * W ^ 2 * Yh ^ 4 * √A2, by positivity, fun c σ hc hβ => ?_⟩
  have hc0 : 0 < c := by linarith
  have hβ' : |σ - c ^ 2| ≤ 2 * c * B := by
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * c), div_le_iff₀ (by positivity)] at hβ; linarith
  obtain ⟨hq, hw⟩ := abs_wf_coulomb hB hc (by have := neg_abs_le (σ - c ^ 2); linarith)
  refine ⟨hw, ?_⟩
  set tc := 1 - U₀ / c with htc
  set K := (c ^ 2 - σ) / c
  set y := regSol (sqC c) σ
  have hsU : U₀ / c ≤ 1 / 4 := by rw [div_le_iff₀ hc0]; linarith
  have hsU0 : 0 < U₀ / c := by positivity
  have htc0 : 3 / 4 ≤ tc := by simp only [htc]; linarith
  have htc1 : tc < 1 := by simp only [htc]; linarith
  -- the doubling bound
  set Q := c * W
  set L := 2 * U₀ / c
  have hQ0 : 0 < Q := by positivity
  have hL : L ≤ 1 / 2 := by simp only [L]; rw [div_le_iff₀ hc0]; linarith
  have hσl : -(2 * c * B) ≤ σ - c ^ 2 := by have := neg_abs_le (σ - c ^ 2); linarith
  have hσu : σ - c ^ 2 ≤ 2 * c * B := (le_abs_self _).trans hβ'
  have hcL : c ^ 2 * (2 * L) = 4 * c * U₀ := by simp only [L]; field_simp; ring
  have hQb : ∀ x ∈ Icc (1 - L) 1, |c ^ 2 * x ^ 2 - σ| ≤ Q := by
    intro x hx
    have hx2 : 1 - x ^ 2 ≤ 2 * L := by nlinarith [hx.1, hx.2]
    have hx1 : 0 ≤ 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
    have h1 : c ^ 2 * (1 - x ^ 2) ≤ 4 * c * U₀ := by
      rw [← hcL]; exact mul_le_mul_of_nonneg_left hx2 (by positivity)
    have h2 : 0 ≤ c ^ 2 * (1 - x ^ 2) := by positivity
    have e : c ^ 2 * x ^ 2 - σ = -(c ^ 2 * (1 - x ^ 2)) - (σ - c ^ 2) := by ring
    have hQe : Q = 2 * c * B + 4 * c * U₀ := by simp only [Q, hW]; ring
    rw [e, abs_le, hQe]; constructor <;> linarith
  have hnL : (n : ℝ) / (2 * Q) ≤ L := by
    simp only [Q, L]
    rw [div_le_div_iff₀ (by positivity) hc0]
    have : (1 : ℝ) ≤ 2 * U₀ * W := by nlinarith
    nlinarith
  have hnU : U₀ / c ≤ (n : ℝ) / (2 * Q) := by
    simp only [Q]
    rw [div_le_div_iff₀ hc0 (by positivity)]
    nlinarith
  set t₀ := 1 - (n : ℝ) / (2 * Q)
  have ht₀c : t₀ ≤ tc := by simp only [t₀, htc]; linarith
  have ht₀0 : 1 / 2 ≤ t₀ := by simp only [t₀]; linarith
  have hYb : ∀ x ∈ Icc t₀ 1, |y x| ≤ Yh := by rw [hYhd]; exact abs_regSol_le_pow hQ0 (by linarith) hQb n hnL
  have hQb' : ∀ x ∈ Icc t₀ 1, |c ^ 2 * x ^ 2 - σ| ≤ Q := fun x hx =>
    hQb x ⟨by simp only [t₀] at hx; linarith [hx.1], hx.2⟩
  set ℓ := 1 / (2 * Q * Yh)
  have hℓ0 : 0 < ℓ := by positivity
  have hQℓ : Q * Yh * ℓ = 1 / 2 := by simp only [ℓ]; field_simp
  have hℓU : ℓ ≤ 4 / c := by
    simp only [ℓ, Q]; rw [div_le_div_iff₀ (by positivity) hc0]; nlinarith
  have hc4 : 4 / c ≤ U₀ / c := div_le_div_of_nonneg_right hU4 hc0.le
  -- `f(t_c) ≥ c²ℓ²/4`
  have hf : c ^ 2 * ℓ ^ 2 / 4 ≤ soninF c σ tc := by
    rcases le_or_gt (c ^ 2) σ with hσ | hσ
    · exact soninF_ge_of_le hσ (by linarith) hℓ0.le (by simp only [htc]; linarith)
        (half_le_of_near (t₀ := t₀) (by linarith) (by linarith) le_rfl hℓ0.le hQb' hYb hQ0.le hQℓ.le
          (by rw [regSol_one]))
    · have hσ0 : 0 < σ := by nlinarith
      have hc2 : 0 < c ^ 2 := by positivity
      have hts2 : √(σ / c ^ 2) ^ 2 = σ / c ^ 2 := Real.sq_sqrt (div_pos hσ0 hc2).le
      have hts1 : √(σ / c ^ 2) ≤ 1 := by
        rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt (by rw [div_le_one hc2]; linarith)
      have htsl : 1 - 2 * B / c ≤ √(σ / c ^ 2) := by
        have h1 : 1 - 2 * B / c ≤ σ / c ^ 2 := by
          rw [le_div_iff₀ hc2]
          have : (1 - 2 * B / c) * c ^ 2 = c ^ 2 - 2 * c * B := by field_simp
          linarith
        have h2 : σ / c ^ 2 ≤ √(σ / c ^ 2) := by
          have h0 := Real.sqrt_nonneg (σ / c ^ 2)
          calc σ / c ^ 2 = √(σ / c ^ 2) ^ 2 := hts2.symm
            _ ≤ √(σ / c ^ 2) := by rw [sq]; exact mul_le_of_le_one_left h0 hts1
        linarith
      have hBc : 4 / c + 2 * B / c ≤ U₀ / c := by
        rw [← add_div]; exact div_le_div_of_nonneg_right (by simp only [hU₀]; linarith) hc0.le
      have hfin : tc ≤ √(σ / c ^ 2) - ℓ := by linarith only [htc, hℓU, htsl, hBc]
      exact soninF_ge_of_lt hc0 hσ0 hσ (by linarith only [htc0]) hℓ0.le hfin
        (half_le_of_near (t₀ := t₀) (by linarith only [ht₀0]) (ht₀c.trans hfin) hts1 hℓ0.le
          hQb' hYb hQ0.le hQℓ.le (by
            have h := Cvs.Prolate.LiouvilleGreen.RegularSolutionNodeLaw.one_le_regSol (c := c) (τ := σ / c ^ 2) √(σ / c ^ 2) ⟨le_rfl, hts1⟩
            rwa [show c ^ 2 * (σ / c ^ 2) = σ by field_simp] at h))
  -- `G(t_c) = f(t_c)/a(t_c)` and `a(t_c)² ≤ 2U₀W`
  have hqp : 0 < qf c K tc := lt_of_lt_of_le (by positivity) hq
  have htc2 : tc ^ 2 < 1 := by
    have h0 : 0 ≤ tc := by linarith only [htc0]
    nlinarith only [htc1, h0]
  have ha := af_pos htc2 hqp
  have ha2 : af c K tc ^ 2 = (1 - tc ^ 2) * qf c K tc := af_sq htc2 hqp
  have hfG : soninF c σ tc = af c K tc * energyAt c σ tc := by
    have hE : energyAt c σ tc = af c K tc * y tc ^ 2 + regU (sqC c) σ tc ^ 2 / af c K tc := rfl
    have ha2' := ha2
    rw [qf_eq hc0.ne'] at ha2'
    rw [hE]; unfold soninF
    rw [mul_add, ← mul_assoc, ← sq, ha2', mul_div_cancel₀ _ ha.ne']
  have haA : af c K tc ≤ √A2 := by
    rw [show af c K tc = √(af c K tc ^ 2) by rw [Real.sqrt_sq ha.le]]
    apply Real.sqrt_le_sqrt
    rw [ha2]
    have hp1 : 1 - tc ^ 2 ≤ 2 * U₀ / c := by
      have e : 1 - tc ^ 2 = 2 * U₀ / c - (U₀ / c) ^ 2 := by rw [htc]; ring
      rw [e]; nlinarith [sq_nonneg (U₀ / c)]
    have hp0 : 0 ≤ 1 - tc ^ 2 := by linarith
    have hUL : U₀ / c ≤ 2 * U₀ / c := div_le_div_of_nonneg_right (by linarith) hc0.le
    have h1L : 1 - L ≤ tc := by simp only [htc, L]; linarith
    have hqQ : qf c K tc ≤ Q := by
      have := hQb tc ⟨h1L, htc1.le⟩
      rw [qf_eq hc0.ne']; rw [abs_le] at this; linarith [this.1]
    calc (1 - tc ^ 2) * qf c K tc ≤ (2 * U₀ / c) * Q := mul_le_mul hp1 hqQ hqp.le (by positivity)
      _ = A2 := by simp only [Q, A2]; field_simp
  -- the layer integral
  have hint : ∫ t in tc..1, y t ^ 2 ≤ U₀ / c * Yh ^ 2 := by
    have hb : ∀ t ∈ uIoc tc 1, ‖y t ^ 2‖ ≤ Yh ^ 2 := by
      intro t ht
      rw [uIoc_of_le htc1.le] at ht
      rw [Real.norm_eq_abs, abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hYb t ⟨ht₀c.trans ht.1.le, ht.2⟩) 2
    have h := norm_integral_le_of_norm_le_const hb
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - tc), show 1 - tc = U₀ / c by simp only [htc]; ring] at h
    have := le_abs_self (∫ t in tc..1, y t ^ 2)
    rw [Real.norm_eq_abs] at h
    linarith
  unfold LayerBound
  have hE0 : 0 < energyAt c σ tc := by
    have : 0 < soninF c σ tc := lt_of_lt_of_le (by positivity) hf
    rw [hfG] at this
    exact pos_of_mul_pos_right this ha.le
  have hsA : 0 < √A2 := Real.sqrt_pos.mpr hA2
  have hEl : c ^ 2 * ℓ ^ 2 / 4 ≤ √A2 * energyAt c σ tc := by
    calc c ^ 2 * ℓ ^ 2 / 4 ≤ soninF c σ tc := hf
      _ = af c K tc * energyAt c σ tc := hfG
      _ ≤ √A2 * energyAt c σ tc := mul_le_mul_of_nonneg_right haA hE0.le
  have hf0 : c ^ 2 * ℓ ^ 2 / 4 = 1 / (16 * W ^ 2 * Yh ^ 2) := by
    simp only [ℓ, Q]; field_simp; ring
  rw [hf0] at hEl
  have key : U₀ / c * Yh ^ 2 = 16 * U₀ * W ^ 2 * Yh ^ 4 * √A2 / c * (1 / (16 * W ^ 2 * Yh ^ 2) / √A2) := by
    field_simp
  have hEl' : 1 / (16 * W ^ 2 * Yh ^ 2) / √A2 ≤ energyAt c σ tc := by
    rw [div_le_iff₀ hsA]; linarith
  calc ∫ t in tc..1, y t ^ 2 ≤ U₀ / c * Yh ^ 2 := hint
    _ = 16 * U₀ * W ^ 2 * Yh ^ 4 * √A2 / c * (1 / (16 * W ^ 2 * Yh ^ 2) / √A2) := key
    _ ≤ 16 * U₀ * W ^ 2 * Yh ^ 4 * √A2 / c * energyAt c σ tc :=
        mul_le_mul_of_nonneg_left hEl' (by positivity)

end Cvs.Prolate.LiouvilleGreen.CoulombLayerExplicit

end
