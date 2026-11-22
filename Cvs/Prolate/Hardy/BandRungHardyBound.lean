import Mathlib
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.Gram.CentralResolventTrace
import Cvs.Prolate.Hardy.CarrierBoundHolomorphicPhase
import Cvs.Prolate.Hardy.CentralRungExpansion
import Cvs.Prolate.Hardy.CosineSynthesisPlancherel
import Cvs.Prolate.Hardy.ExtensionTraceColumnIntegral
import Cvs.Prolate.Hardy.HardyExtensionOperator
import Cvs.Prolate.LiouvilleGreen.ComplexSymbols
import Cvs.Prolate.LiouvilleGreen.HalfStripPhase
import Cvs.Prolate.LiouvilleGreen.RecessiveCoefficientBound
import Cvs.Prolate.LiouvilleGreen.RecessiveSolvesProlate
import Cvs.Prolate.LiouvilleGreen.RecessiveVolterra
import Cvs.Prolate.LiouvilleGreen.RungRecessiveRealPart
import Cvs.Upstream.HalfStripRayIntegrals
import Cvs.Upstream.JordanArcIntegral

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The Hardy extension of a band rung is `O(1)` away from `T = ¾`

At level `χ = c²T`, `¾ ≤ T ≤ 1`, take the ellipse `L² = 2T/3`, `B² = L² − ¼` and the strip `a² = 5T/6`. The margin
`δ_T = κB − L/2`, `κ² = (T − L²)/(1 − L²)`, satisfies `δ_T ≥ (4T − 3)/16`; for `c ≥ 2255` and `cδ_T ≥ 1`,
`‖J_c(Qh_k)‖ ≤ 100`.
-/

noncomputable section

open Real Set MeasureTheory
open Complex (I)
open scoped Interval
open Cvs.Upstream.HalfStripRayIntegrals (strip)
open Cvs.Prolate.LiouvilleGreen.ComplexSymbols
open Cvs.Prolate.LiouvilleGreen.HalfStripPhase
open Cvs.Prolate.LiouvilleGreen.RecessiveVolterra
open Cvs.Prolate.LiouvilleGreen.RecessiveSolvesProlate

namespace Cvs.Prolate.Hardy.BandRungHardyBound
open Cvs.ZeroCounting

/-- The strip half-width `a_T = √(5T/6)`. -/
def aT (T : ℝ) : ℝ := √(5 * T / 6)

/-- The ellipse semi-major axis `L_T = √(2T/3)`. -/
def lT (T : ℝ) : ℝ := √(2 * T / 3)

/-- The ellipse semi-minor axis `B_T = √(2T/3 − ¼)`. -/
def bT (T : ℝ) : ℝ := √(2 * T / 3 - 1 / 4)

/-- The confocal parameter `η_T = arsinh(2B_T)`, so `cosh η_T = 2L_T`. -/
def etaT (T : ℝ) : ℝ := Real.arsinh (2 * bT T)

/-- The upward rate `κ_T = √((T − L²)/(1 − L²))`. -/
def kapT (T : ℝ) : ℝ := √((T - lT T ^ 2) / (1 - lT T ^ 2))

/-- **The margin** `δ_T = κ_TB_T − L_T/2`. -/
def delT (T : ℝ) : ℝ := kapT T * bT T - lT T / 2

section geom

variable {T : ℝ}

theorem lT_sq (hT : 0 ≤ T) : lT T ^ 2 = 2 * T / 3 := Real.sq_sqrt (by positivity)

theorem aT_sq (hT : 0 ≤ T) : aT T ^ 2 = 5 * T / 6 := Real.sq_sqrt (by positivity)

theorem bT_sq (hT : 3 / 4 ≤ T) : bT T ^ 2 = 2 * T / 3 - 1 / 4 := Real.sq_sqrt (by linarith)

theorem sinh_etaT : Real.sinh (etaT T) = 2 * bT T := Real.sinh_arsinh _

theorem cosh_etaT (hT : 3 / 4 ≤ T) : Real.cosh (etaT T) = 2 * lT T := by
  rw [etaT, Real.cosh_arsinh, mul_pow, bT_sq hT]
  rw [show 1 + 2 ^ 2 * (2 * T / 3 - 1 / 4) = (2 * lT T) ^ 2 by rw [mul_pow, lT_sq (by linarith)]; ring,
    Real.sqrt_sq (by unfold lT; positivity)]

theorem half_cosh_etaT (hT : 3 / 4 ≤ T) : 1 / 2 * Real.cosh (etaT T) = lT T := by rw [cosh_etaT hT]; ring

theorem half_sinh_etaT : 1 / 2 * Real.sinh (etaT T) = bT T := by rw [sinh_etaT]; ring

theorem etaT_pos (hT : 3 / 4 ≤ T) : 0 < etaT T := by
  unfold etaT
  rw [Real.arsinh_pos_iff]
  unfold bT
  have : 0 < 2 * T / 3 - 1 / 4 := by linarith
  positivity

theorem lT_lt_aT (hT : 3 / 4 ≤ T) : lT T < aT T := by
  unfold lT aT; exact Real.sqrt_lt_sqrt (by linarith) (by linarith)

theorem aT_sq_lt (hT : 3 / 4 ≤ T) : aT T ^ 2 < T := by rw [aT_sq (by linarith)]; linarith

theorem half_lt_aT (hT : 3 / 4 ≤ T) : 1 / 2 < aT T := by
  unfold aT
  rw [show (1 / 2 : ℝ) = √(1 / 4) by rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)] ]
  exact Real.sqrt_lt_sqrt (by norm_num) (by linarith)

theorem lT_le_one (hT1 : T ≤ 1) : lT T ≤ 1 := by
  unfold lT; rw [Real.sqrt_le_one]; linarith

theorem half_le_bT (hT : 3 / 4 ≤ T) : 1 / 2 ≤ bT T := by
  unfold bT
  rw [show (1 / 2 : ℝ) = √(1 / 4) by rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)] ]
  exact Real.sqrt_le_sqrt (by linarith)

theorem bT_le_one (hT1 : T ≤ 1) : bT T ≤ 1 := by unfold bT; rw [Real.sqrt_le_one]; linarith

/-- **The margin is linear at `T = ¾`**: `δ_T ≥ (4T − 3)/16`. -/
theorem delT_ge (hT : 3 / 4 ≤ T) (hT1 : T ≤ 1) : (4 * T - 3) / 16 ≤ delT T := by
  have hL2 := lT_sq (by linarith : (0 : ℝ) ≤ T)
  have hB2 := bT_sq hT
  have hκ2 : kapT T ^ 2 = T / (3 - 2 * T) := by
    unfold kapT
    rw [Real.sq_sqrt (by rw [hL2]; exact div_nonneg (by linarith) (by linarith)), hL2]
    field_simp; ring
  have hκ0 : 0 ≤ kapT T := Real.sqrt_nonneg _
  have hB0 : 0 ≤ bT T := Real.sqrt_nonneg _
  have hL0 : 0 ≤ lT T := Real.sqrt_nonneg _
  have hκ1 : kapT T ≤ 1 := by
    unfold kapT; rw [Real.sqrt_le_one, hL2, div_le_one (by linarith)]; linarith
  have hB1 := bT_le_one hT1
  have hL1 := lT_le_one hT1
  have key : (kapT T * bT T) ^ 2 - (lT T / 2) ^ 2 = T * (4 * T - 3) / (4 * (3 - 2 * T)) := by
    have hκm : kapT T ^ 2 * (3 - 2 * T) = T := by rw [hκ2, div_mul_cancel₀ _ (by linarith)]
    rw [eq_div_iff (by linarith : 4 * (3 - 2 * T) ≠ 0), mul_pow, hB2, div_pow, hL2]
    linear_combination 4 * (2 * T / 3 - 1 / 4) * hκm
  have hsum : kapT T * bT T + lT T / 2 ≤ 2 := by nlinarith [mul_le_one₀ hκ1 hB0 hB1]
  have hpos : 0 ≤ T * (4 * T - 3) / (4 * (3 - 2 * T)) := div_nonneg (by nlinarith) (by linarith)
  have h8 : (4 * T - 3) / 8 ≤ T * (4 * T - 3) / (4 * (3 - 2 * T)) := by
    rw [div_le_div_iff₀ (by norm_num) (by linarith)]; nlinarith
  unfold delT
  have hfac : (kapT T * bT T - lT T / 2) * (kapT T * bT T + lT T / 2) =
      T * (4 * T - 3) / (4 * (3 - 2 * T)) := by rw [← key]; ring
  have hLp : 0 < lT T := by unfold lT; positivity
  have hy : 0 < kapT T * bT T + lT T / 2 := by have := mul_nonneg hκ0 hB0; linarith
  by_contra h
  push Not at h
  have h1 := mul_lt_mul_of_pos_right h hy
  have h2 : (4 * T - 3) / 16 * (kapT T * bT T + lT T / 2) ≤ (4 * T - 3) / 16 * 2 :=
    mul_le_mul_of_nonneg_left hsum (by linarith)
  linarith

/-- **The error-control constant** at `a² = 5T/6`: `V ≤ 205`. -/
theorem vV_le (hT : 3 / 4 ≤ T) (hT1 : T ≤ 1) : vV (aT T) T ≤ 205 := by
  have hm : T - aT T ^ 2 = T / 6 := by rw [aT_sq (by linarith)]; ring
  unfold vV kR
  rw [hm]
  have hm0 : (1 : ℝ) / 8 ≤ T / 6 := by linarith
  have h1 : 5 / 4 * (T * (1 - T)) / (T / 6) ≤ 15 / 8 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have h2 : (1 + 5 / 4 * (T * (1 - T)) / (T / 6)) / (T / 6) ≤ 23 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have h3 : π / √(T / 6) ≤ 3.1416 * 2.83 := by
    have hs : 1 / 2.83 ≤ √(T / 6) := by
      rw [show (1 / 2.83 : ℝ) = √((1 / 2.83) ^ 2) by rw [Real.sqrt_sq (by norm_num)] ]
      exact Real.sqrt_le_sqrt (by norm_num; linarith)
    rw [div_le_iff₀ (by positivity)]
    have := Real.pi_lt_d4
    nlinarith only [hs, this]
  have h4 : 0 ≤ (1 + 5 / 4 * (T * (1 - T)) / (T / 6)) / (T / 6) := by
    have : 0 ≤ T * (1 - T) := mul_nonneg (by linarith) (by linarith)
    positivity
  calc (1 + 5 / 4 * (T * (1 - T)) / (T / 6)) / (T / 6) * (π / √(T / 6)) ≤ 23 * (3.1416 * 2.83) :=
        mul_le_mul h2 h3 (by positivity) (by norm_num)
    _ ≤ 205 := by norm_num

end geom

/-! ### The band rung -/

section rung

variable {T c : ℝ}

/-- **The Hardy extension of a rung at `χ = c²T`**: `‖J_c(Qh_k)‖ ≤ 100` for `¾ ≤ T ≤ 1`, `c ≥ 2255`, `cδ_T ≥ 1`. -/
theorem norm_hardyJ_rung_le (hT : 3 / 4 ≤ T) (hT1 : T ≤ 1) (hc : 2255 ≤ c) (hδ : 1 ≤ c * delT T) {k : ℕ}
    (hk : ∃ χ, Cvs.Prolate.EvenRungsByIndex.IsLevelIdx c k χ) (hev : Even k) (hχ : Cvs.Prolate.EvenRungsByIndex.lev c k = c ^ 2 * T) :
    ‖Cvs.Prolate.Hardy.HardyExtensionOperator.hardyJ c (Cvs.Prolate.Hardy.CentralRungExpansion.qI (Cvs.Prolate.Hardy.CentralRungExpansion.continuous_hk c k))‖ ≤ 100 := by
  have hc0 : 0 < c := by linarith
  have ha2 : (aT T) ^ 2 < T := aT_sq_lt hT
  have ha : 1 / 2 < aT T := half_lt_aT hT
  have ha0 : 0 < aT T := by linarith
  have hT0 : 0 < T := by linarith
  have hμ : Cvs.Prolate.EvenRungsByIndex.muR c k ≠ 0 := (Cvs.Prolate.EvenRungsByIndex.muR_pos_of_even hc0 hk hev).ne'
  have hV := vV_le hT hT1
  have hV0 := vV_nonneg ha2 hT1
  obtain ⟨q, hq_def⟩ : ∃ q : ℝ, q = vV (aT T) T / c := ⟨_, rfl⟩
  have hq : q ≤ 1 / 11 := by rw [hq_def, div_le_iff₀ hc0]; linarith
  have hq0 : 0 ≤ q := by rw [hq_def]; exact div_nonneg hV0 hc0.le
  have hq1 : q < 1 := by linarith
  obtain ⟨ε, hε, hfix⟩ := exists_eps ha2 hT1 hc0 (hq_def ▸ hq1)
  obtain ⟨B, hB_def⟩ : ∃ B : ℝ, B = q / (1 - q) := ⟨_, rfl⟩
  have hB : B ≤ 1 / 10 := by rw [hB_def, div_le_iff₀ (by linarith)]; linarith
  have hB0 : 0 ≤ B := by rw [hB_def]; exact div_nonneg hq0 (by linarith)
  have hε' : Good (aT T) ε B := by rwa [hB_def, hq_def]
  have hW : vV (aT T) T * (1 + B) < c * (1 - B) := by
    have : vV (aT T) T ≤ c / 11 := by rw [le_div_iff₀ (by norm_num)]; linarith
    nlinarith
  obtain ⟨α, hα⟩ := Cvs.Prolate.LiouvilleGreen.RungRecessiveRealPart.exists_alpha ha0 ha2 hT1 hc0 hε' hfix hW hk hμ hχ
  have hα2 := Cvs.Prolate.LiouvilleGreen.RecessiveCoefficientBound.norm_alpha_sq_le ha (by linarith) ha2 hT1 (by linarith) hε' hB hk hα
  have hαn : ‖α‖ ≤ 3 / 2 := by nlinarith [norm_nonneg α]
  -- the holomorphic carrier `F = 2αH₊`
  let F : ℂ → ℂ := fun z => 2 * α * hP c T ε z
  have hPd : DifferentiableOn ℂ (hP c T ε) (strip (aT T)) :=
    (((differentiableOn_lam ha2 hT1).mul (((differentiableOn_Phi ha2 hT1).const_mul _).cexp)).mul
      ((differentiableOn_const 1).add hε'.1))
  have hFd : ∀ z ∈ strip (aT T), DifferentiableAt ℂ F z := fun z hz =>
    ((hPd z hz).differentiableAt ((Cvs.Upstream.HalfStripRayIntegrals.isOpen_strip (aT T)).mem_nhds hz)).const_mul _
  obtain ⟨m, hm_def⟩ : ∃ m : ℝ, m = T - (aT T) ^ 2 := ⟨_, rfl⟩
  have hm : m = T / 6 := by rw [hm_def, aT_sq hT0.le]; ring
  obtain ⟨M₀, hM₀_def⟩ : ∃ M₀ : ℝ, M₀ = 2 * ‖α‖ * √(1 / m) * (1 + B) := ⟨_, rfl⟩
  have hM00 : 0 ≤ M₀ := by rw [hM₀_def]; positivity
  -- `|F(z)| ≤ M₀ e^{−c Im Φ_T(z)}` on the strip
  have hFz : ∀ z ∈ strip (aT T), ‖F z‖ ≤ M₀ * Real.exp (-(c * (Phi T z).im)) := by
    intro z hz
    have h1 := norm_lam_sq_le ha2 hT1 hz
    have hl : ‖lam T z‖ ≤ √(1 / m) := by
      rw [← Real.sqrt_sq (norm_nonneg _), hm_def]
      refine Real.sqrt_le_sqrt (h1.trans ?_)
      exact one_div_le_one_div_of_le (by linarith) (by nlinarith [sq_nonneg z.im])
    have h2 : ‖1 + ε z‖ ≤ 1 + B := (norm_add_le _ _).trans (by rw [norm_one]; linarith [hε'.2 z hz])
    have h3 : ‖Complex.exp (I * c * Phi T z)‖ = Real.exp (-(c * (Phi T z).im)) := by
      rw [Complex.norm_exp]; congr 1; simp [Complex.mul_re]
    simp only [F, hP, norm_mul, h3, show ‖(2 : ℂ)‖ = 2 by simp]
    rw [hM₀_def]
    calc 2 * ‖α‖ * (‖lam T z‖ * Real.exp (-(c * (Phi T z).im)) * ‖1 + ε z‖) =
          2 * ‖α‖ * ‖lam T z‖ * ‖1 + ε z‖ * Real.exp (-(c * (Phi T z).im)) := by ring
      _ ≤ 2 * ‖α‖ * √(1 / m) * (1 + B) * Real.exp (-(c * (Phi T z).im)) := by gcongr
  -- the confocal ellipse
  set η₀ := etaT T
  have hη₀ := etaT_pos hT
  have hLc := half_cosh_etaT hT
  have hBs : 1 / 2 * Real.sinh η₀ = bT T := half_sinh_etaT
  have hLa := lT_lt_aT hT
  have hrect : ∀ ζ ∈ [[(0 : ℝ), η₀]] ×ℂ [[(0 : ℝ), π]], (1 / 2 : ℂ) * Complex.cosh ζ ∈ strip (aT T) := by
    intro ζ hζ
    have hre : ζ.re ∈ [[(0 : ℝ), η₀]] := hζ.1
    have him : ζ.im ∈ [[(0 : ℝ), π]] := hζ.2
    rw [uIcc_of_le hη₀.le] at hre
    rw [uIcc_of_le Real.pi_pos.le] at him
    have e : (1 / 2 : ℂ) * Complex.cosh ζ = ((1 / 2 * Real.cosh ζ.re * Real.cos ζ.im : ℝ) : ℂ) +
        I * ((1 / 2 * Real.sinh ζ.re * Real.sin ζ.im : ℝ) : ℂ) := by
      have h := Cvs.Upstream.JordanArcIntegral.cosh_arc (1 / 2) ζ.re ζ.im
      rw [Complex.re_add_im] at h
      push_cast at h ⊢
      linear_combination h
    rw [e]
    constructor
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_im, zero_mul, sub_zero, mul_zero, add_zero]
      have hc1 : Real.cosh ζ.re ≤ Real.cosh η₀ := by
        rw [Real.cosh_le_cosh, abs_of_nonneg hre.1, abs_of_nonneg hη₀.le]; exact hre.2
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), abs_of_pos (Real.cosh_pos _)]
      calc 1 / 2 * Real.cosh ζ.re * |Real.cos ζ.im| ≤ 1 / 2 * Real.cosh η₀ * 1 := by
            gcongr; exact Real.abs_cos_le_one _
        _ < aT T := by rw [mul_one, hLc]; exact hLa
    · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, zero_mul, one_mul, zero_add]
      have : 0 ≤ 1 / 2 * Real.sinh ζ.re * Real.sin ζ.im :=
        mul_nonneg (mul_nonneg (by norm_num) (Real.sinh_nonneg_iff.2 hre.1))
          (Real.sin_nonneg_of_nonneg_of_le_pi him.1 him.2)
      linarith
  have hreal : ∀ x : ℝ, |x| ≤ 1 / 2 * Real.cosh η₀ → (x : ℂ) ∈ strip (aT T) := fun x hx =>
    ⟨by simpa using hx.trans_lt (hLc ▸ hLa), by simp⟩
  have hFx : ∀ x : ℝ, |x| ≤ 1 / 2 * Real.cosh η₀ → ContinuousAt F x := fun x hx =>
    (hFd _ (hreal x hx)).continuousAt
  have hM₀ : ∀ x : ℝ, |x| ≤ 1 / 2 * Real.cosh η₀ → ‖F x‖ ≤ M₀ := by
    intro x hx
    have h := hFz _ (hreal x hx)
    rw [im_Phi_ofReal ha2 hT1 (hx.trans_lt (hLc ▸ hLa)), mul_zero, neg_zero, Real.exp_zero, mul_one] at h
    exact h
  obtain ⟨t, ht_def⟩ : ∃ t : ℝ, t = c * delT T := ⟨_, rfl⟩
  have hM : ∀ θ ∈ Icc 0 π, ‖F ((1 / 2 : ℂ) * Complex.cosh (η₀ + θ * I)) *
      Complex.exp (-(I * ((c / 2 : ℝ) : ℂ) * ((1 / 2 : ℂ) * Complex.sinh (η₀ + θ * I))))‖ ≤
        M₀ * Real.exp (-t * Real.sin θ) := by
    intro θ hθ
    have hsθ : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 hθ.2
    have hz : (1 / 2 : ℂ) * Complex.cosh (η₀ + θ * I) = ((lT T * Real.cos θ : ℝ) : ℂ) +
        ((bT T * Real.sin θ : ℝ) : ℂ) * I := by
      have h := Cvs.Upstream.JordanArcIntegral.cosh_arc (1 / 2) η₀ θ
      rw [show 1 / 2 * Real.cosh η₀ = lT T from hLc, show 1 / 2 * Real.sinh η₀ = bT T from hBs] at h
      push_cast at h ⊢
      linear_combination h
    have hS : (1 / 2 : ℂ) * Complex.sinh (η₀ + θ * I) = ((bT T * Real.cos θ : ℝ) : ℂ) +
        I * ((lT T * Real.sin θ : ℝ) : ℂ) := by
      have h := Cvs.Upstream.JordanArcIntegral.sinh_arc (1 / 2) η₀ θ
      rw [show 1 / 2 * Real.cosh η₀ = lT T from hLc, show 1 / 2 * Real.sinh η₀ = bT T from hBs] at h
      push_cast at h ⊢
      linear_combination h
    have hzs := hrect (η₀ + θ * I) ⟨by simp, by
      simp [uIcc_of_le Real.pi_pos.le, hθ.1, hθ.2]⟩
    have h1 := hFz _ hzs
    have hIm : kapT T * (bT T * Real.sin θ) ≤ (Phi T ((1 / 2 : ℂ) * Complex.cosh (η₀ + θ * I))).im := by
      rw [hz]
      exact im_Phi_ge ha2 hT1 hLa (by
        rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _) |>.trans_eq
          (abs_of_nonneg (Real.sqrt_nonneg _))) (mul_nonneg (Real.sqrt_nonneg _) hsθ)
    have h2 : ‖Complex.exp (-(I * ((c / 2 : ℝ) : ℂ) * ((1 / 2 : ℂ) * Complex.sinh (η₀ + θ * I))))‖ =
        Real.exp (c / 2 * (lT T * Real.sin θ)) := by
      rw [Complex.norm_exp, hS]; congr 1
      simp [Complex.mul_re, Complex.mul_im, -Complex.ofReal_sin, -Complex.ofReal_cos]
    rw [norm_mul, h2]
    calc ‖F ((1 / 2 : ℂ) * Complex.cosh (η₀ + θ * I))‖ * Real.exp (c / 2 * (lT T * Real.sin θ)) ≤
          M₀ * Real.exp (-(c * (kapT T * (bT T * Real.sin θ)))) * Real.exp (c / 2 * (lT T * Real.sin θ)) := by
          gcongr
          exact h1.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith only [hc0, hIm])) hM00)
      _ = M₀ * Real.exp (-t * Real.sin θ) := by
          rw [mul_assoc, ← Real.exp_add]; congr 2; rw [ht_def]; simp only [delT]; ring
  have hf : (Cvs.Prolate.Hardy.CentralRungExpansion.qI (Cvs.Prolate.Hardy.CentralRungExpansion.continuous_hk c k) : ℝ → ℝ) =ᵐ[volume.restrict Cvs.Prolate.Hardy.CosineSynthesisPlancherel.cI]
      fun x : ℝ => (F x).re := by
    filter_upwards [Cvs.Prolate.Hardy.CentralRungExpansion.coeFn_qI (Cvs.Prolate.Hardy.CentralRungExpansion.continuous_hk c k), ae_restrict_mem measurableSet_Icc] with x h1 h2
    have hx1 : x ∈ Icc (-1 : ℝ) 1 := ⟨by linarith only [h2.1], by linarith only [h2.2]⟩
    have hxa : |x| < aT T := by rw [abs_lt]; constructor <;> linarith only [ha, h2.1, h2.2]
    rw [h1, Cvs.Prolate.Hardy.CentralRungExpansion.hk_eq hk hx1, hα x hxa]
  have ht1 : 1 ≤ t := ht_def ▸ hδ
  have ht : 0 < t := by linarith only [ht1]
  have hJ := Cvs.Prolate.Hardy.CarrierBoundHolomorphicPhase.norm_hardyJ_le hc0 hη₀ ht (fun ζ hζ => hFd _ (hrect ζ hζ)) hFx hM₀ hM hf
  rw [hLc, hBs] at hJ
  -- the arithmetic
  have hB12 := half_le_bT hT
  have hL1 := lT_le_one hT1
  have hs1 : √(1 / (t * (2 * π * bT T))) ≤ 1 := by
    rw [Real.sqrt_le_one, div_le_one (by positivity)]
    have hpi : 3 < π := Real.pi_gt_three
    have h2b : 1 ≤ 2 * π * bT T := by nlinarith only [hpi, hB12]
    nlinarith only [ht1, h2b]
  have hs2 : √(2 * (lT T - 1 / 2)) ≤ 1 := by rw [Real.sqrt_le_one]; linarith only [hL1]
  have hM₀b : M₀ ≤ 10 := by
    have hm8 : √(1 / m) ≤ 2.83 := by
      rw [hm, show (2.83 : ℝ) = √(2.83 ^ 2) by rw [Real.sqrt_sq (by norm_num)] ]
      exact Real.sqrt_le_sqrt (by rw [div_le_iff₀ (by linarith only [hT])]; nlinarith only [hT])
    have h1 : 2 * ‖α‖ ≤ 3 := by linarith only [hαn]
    have h2 : 1 + B ≤ 11 / 10 := by linarith only [hB]
    have h3 : 2 * ‖α‖ * √(1 / m) ≤ 3 * 2.83 := mul_le_mul h1 hm8 (Real.sqrt_nonneg _) (by norm_num)
    have h4 : 2 * ‖α‖ * √(1 / m) * (1 + B) ≤ 3 * 2.83 * (11 / 10) :=
      mul_le_mul h3 h2 (by linarith only [hB0]) (by norm_num)
    rw [hM₀_def]
    linarith only [h4]
  have hπ := Real.pi_lt_d2
  have hterm1 : M₀ * lT T * π * √(1 / (t * (2 * π * bT T))) ≤ M₀ * 3.15 := by
    have ha1 : M₀ * lT T ≤ M₀ := mul_le_of_le_one_right hM00 hL1
    have ha2' : M₀ * lT T * π ≤ M₀ * 3.15 :=
      (mul_le_mul_of_nonneg_right ha1 Real.pi_pos.le).trans (mul_le_mul_of_nonneg_left hπ.le hM00)
    have ha3' : M₀ * lT T * π * √(1 / (t * (2 * π * bT T))) ≤ M₀ * lT T * π :=
      mul_le_of_le_one_right (mul_nonneg (mul_nonneg hM00 (Real.sqrt_nonneg _)) Real.pi_pos.le) hs1
    linarith only [ha2', ha3']
  have hterm2 : M₀ * √(2 * (lT T - 1 / 2)) ≤ M₀ := mul_le_of_le_one_right hM00 hs2
  linarith only [hJ, hM₀b, hterm1, hterm2]

end rung

end Cvs.Prolate.Hardy.BandRungHardyBound

end
