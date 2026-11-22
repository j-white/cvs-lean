import Mathlib
import Cvs.PNT.ResidueCalcOnRectangles
import Cvs.Zeta.MollifiedDetectorSeries
import Cvs.Zeta.ZeroCounting.ZeroDensityBlueprint

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The smoothed Gaussian Mellin kernel and right-edge Dirichlet expansion

Shifting `Re w > 0` in `gaussMellin β L q = (2π)⁻¹ ∫_{-L}^L (e^{w²} / w) q^w dv` gives polynomial main-range bounds,
`O(T^{-3} n^{-3})` tail decay for `n > T^{1 + ε}`, and a Dirichlet series expansion on `Re(z + w) = 3` via `Cvs.Zeta.MollifiedDetectorSeries`.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology Finset
open Cvs.Zeta.ZeroCounting.ZeroDensityBlueprint (truncMoebiusSum)
open Cvs.Zeta.MollifiedDetectorSeries (mollifiedDetector norm_truncMoebiusSum_le_self mollifiedDetector_eq_tsum)

namespace Cvs.Zeta.GaussKernel.SmoothedGaussMellin

/-- The Gaussian Mellin integrand `(e^{w²} / w) q^w`. -/
def gaussMellinIntegrand (q : ℝ) (w : ℂ) : ℂ :=
  Complex.exp (w ^ 2) * (q : ℂ) ^ w / w

/-- The vertical-segment Gaussian Mellin weight on `Re w = β`, `Im w ∈ [-L, L]`. -/
def gaussMellin (β L q : ℝ) : ℂ :=
  (1 / (2 * Real.pi)) * ∫ v in (-L)..L, gaussMellinIntegrand q ((β : ℂ) + (v : ℂ) * I)

/-- Bridge to `VIntegral` divided by `2πi`. -/
theorem vIntegral_div_two_pi_I_eq_gaussMellin (β L q : ℝ) :
    ((1 / (2 * (Real.pi : ℂ) * I)) • VIntegral (gaussMellinIntegrand q) β (-L) L)
      = gaussMellin β L q := by
  simp only [VIntegral, gaussMellin, smul_eq_mul]
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hI : (I : ℂ) ≠ 0 := I_ne_zero
  field_simp

/-- `‖exp((x + iy)²)‖ = exp(x² - y²)`. -/
theorem norm_exp_sq (x y : ℝ) :
    ‖Complex.exp (((x : ℂ) + (y : ℂ) * I) ^ 2)‖ = Real.exp (x ^ 2 - y ^ 2) := by
  rw [Complex.norm_exp]
  congr 1
  simp [sq]

/-- Pointwise norm bound on `gaussMellinIntegrand` when `Re w = x ≠ 0` and `q > 0`. -/
theorem norm_gaussMellinIntegrand_le_of_re_ne_zero {q x : ℝ} (hq : 0 < q) (hx : x ≠ 0) (y : ℝ) :
    ‖gaussMellinIntegrand q ((x : ℂ) + (y : ℂ) * I)‖
      ≤ Real.exp (x ^ 2 - y ^ 2) * q ^ x / |x| := by
  unfold gaussMellinIntegrand
  have hre : (((x : ℂ) + (y : ℂ) * I)).re = x := by simp
  have hw : |x| ≤ ‖(x : ℂ) + (y : ℂ) * I‖ := by
    simpa only [hre] using Complex.abs_re_le_norm ((x : ℂ) + (y : ℂ) * I)
  rw [norm_div, norm_mul, norm_exp_sq, Complex.norm_cpow_eq_rpow_re_of_pos hq, hre]
  exact div_le_div_of_nonneg_left (by positivity) (abs_pos.mpr hx) hw

/-- Pointwise norm bound on `gaussMellinIntegrand` when `Im w = y ≠ 0` and `q > 0`. -/
theorem norm_gaussMellinIntegrand_le_of_im_ne_zero {q y : ℝ} (hq : 0 < q) (hy : y ≠ 0) (x : ℝ) :
    ‖gaussMellinIntegrand q ((x : ℂ) + (y : ℂ) * I)‖
      ≤ Real.exp (x ^ 2 - y ^ 2) * q ^ x / |y| := by
  unfold gaussMellinIntegrand
  have him : (((x : ℂ) + (y : ℂ) * I)).im = y := by simp
  have hw : |y| ≤ ‖(x : ℂ) + (y : ℂ) * I‖ := by
    simpa only [him] using Complex.abs_im_le_norm ((x : ℂ) + (y : ℂ) * I)
  rw [norm_div, norm_mul, norm_exp_sq, Complex.norm_cpow_eq_rpow_re_of_pos hq,
    show (((x : ℂ) + (y : ℂ) * I)).re = x by simp]
  exact div_le_div_of_nonneg_left (by positivity) (abs_pos.mpr hy) hw

/-- `gaussMellinIntegrand q` is holomorphic on `ℂ \ {0}` for `q > 0`. -/
theorem differentiableOn_gaussMellinIntegrand {q : ℝ} (hq : 0 < q) :
    DifferentiableOn ℂ (gaussMellinIntegrand q) {0}ᶜ := by
  intro w hw
  unfold gaussMellinIntegrand
  have hq0 : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq.ne'
  exact (((differentiableAt_id.pow 2).cexp.mul
    (differentiableAt_id.const_cpow (Or.inl hq0))).div differentiableAt_id hw).differentiableWithinAt

/-- Elementary Gaussian integral bound: `∫_{-L}^L e^{-v²} dv ≤ π` via `e^{-v²} ≤ (1 + v²)⁻¹`. -/
theorem integral_exp_neg_sq_le_pi {L : ℝ} (hL : 0 ≤ L) :
    ∫ v in (-L)..L, Real.exp (-(v ^ 2)) ≤ Real.pi := by
  have hLL : -L ≤ L := by linarith
  have hpt : ∀ v ∈ Icc (-L) L, Real.exp (-(v ^ 2)) ≤ (1 + v ^ 2)⁻¹ := by
    intro v _
    rw [Real.exp_neg]
    exact inv_anti₀ (by positivity) (by linarith [Real.add_one_le_exp (v ^ 2)])
  have hint1 : IntervalIntegrable (fun v : ℝ => Real.exp (-(v ^ 2))) volume (-L) L :=
    (by fun_prop : Continuous fun v : ℝ => Real.exp (-(v ^ 2))).intervalIntegrable _ _
  have hint2 : IntervalIntegrable (fun v : ℝ => (1 + v ^ 2)⁻¹) volume (-L) L :=
    (Continuous.inv₀ (f := fun v : ℝ => 1 + v ^ 2) (by fun_prop)
      (fun v => by positivity)).intervalIntegrable _ _
  have hmono := intervalIntegral.integral_mono_on hLL hint1 hint2 hpt
  have harc : ∫ v in (-L)..L, (1 + v ^ 2)⁻¹ = Real.arctan L - Real.arctan (-L) := by
    have h := integral_one_div_one_add_sq (a := -L) (b := L)
    simp only [one_div] at h
    exact h
  rw [harc, Real.arctan_neg] at hmono
  linarith [Real.arctan_lt_pi_div_two L, hmono]

/-- Vertical-line norm bound: for `γ > 0`, `L ≥ 0`, `q > 0`,
`‖gaussMellin γ L q‖ ≤ e^{γ²} q^γ / (2γ)`. -/
theorem norm_gaussMellin_le {γ L q : ℝ} (hγ : 0 < γ) (hL : 0 ≤ L) (hq : 0 < q) :
    ‖gaussMellin γ L q‖ ≤ Real.exp (γ ^ 2) * q ^ γ / (2 * γ) := by
  unfold gaussMellin
  have hLL : -L ≤ L := by linarith
  have hpi : 0 < Real.pi := Real.pi_pos
  have hc : ‖(1 : ℂ) / (2 * (Real.pi : ℂ))‖ = 1 / (2 * Real.pi) := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_of_nonneg hpi.le]
  rw [norm_mul, hc]
  have hint_norm : IntervalIntegrable
      (fun v : ℝ => ‖gaussMellinIntegrand q ((γ : ℂ) + (v : ℂ) * I)‖) volume (-L) L := by
    refine Continuous.intervalIntegrable ?_ (-L) L
    refine Continuous.norm ?_
    unfold gaussMellinIntegrand
    have hq0 : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq.ne'
    refine Continuous.div₀ ?_ (by fun_prop) (fun v => ?_)
    · exact (Continuous.cexp (f := fun v : ℝ => ((γ : ℂ) + (v : ℂ) * I) ^ 2) (by fun_prop)).mul
        (Continuous.const_cpow (f := fun v : ℝ => (γ : ℂ) + (v : ℂ) * I) (by fun_prop) (Or.inl hq0))
    · intro h
      have hre := congrArg Complex.re h
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_im, Complex.zero_re, mul_zero, mul_one, sub_zero, add_zero] at hre
      linarith
  have hint_rhs : IntervalIntegrable
      (fun v : ℝ => (Real.exp (γ ^ 2) * q ^ γ / γ) * Real.exp (-(v ^ 2))) volume (-L) L :=
    (by fun_prop : Continuous _).intervalIntegrable _ _
  have hpt : ∀ v ∈ Icc (-L) L,
      ‖gaussMellinIntegrand q ((γ : ℂ) + (v : ℂ) * I)‖
        ≤ (Real.exp (γ ^ 2) * q ^ γ / γ) * Real.exp (-(v ^ 2)) := by
    intro v _
    refine (norm_gaussMellinIntegrand_le_of_re_ne_zero hq hγ.ne' v).trans_eq ?_
    rw [abs_of_pos hγ, show γ ^ 2 - v ^ 2 = γ ^ 2 + -(v ^ 2) by ring, Real.exp_add]
    ring
  have h1 := (intervalIntegral.norm_integral_le_integral_norm hLL).trans
    (intervalIntegral.integral_mono_on hLL hint_norm hint_rhs hpt)
  rw [intervalIntegral.integral_const_mul] at h1
  have h2 : (1 / (2 * Real.pi)) * ((Real.exp (γ ^ 2) * q ^ γ / γ) * ∫ v in (-L)..L, Real.exp (-(v ^ 2)))
      ≤ (1 / (2 * Real.pi)) * ((Real.exp (γ ^ 2) * q ^ γ / γ) * Real.pi) :=
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (integral_exp_neg_sq_le_pi hL) (by positivity)) (by positivity)
  calc 1 / (2 * Real.pi) * ‖∫ v in (-L)..L, gaussMellinIntegrand q ((γ : ℂ) + (v : ℂ) * I)‖
      ≤ 1 / (2 * Real.pi) * ((Real.exp (γ ^ 2) * q ^ γ / γ) * ∫ v in (-L)..L, Real.exp (-(v ^ 2))) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ ≤ 1 / (2 * Real.pi) * ((Real.exp (γ ^ 2) * q ^ γ / γ) * Real.pi) := h2
    _ = Real.exp (γ ^ 2) * q ^ γ / (2 * γ) := by field_simp

/-- Convexity of `x ↦ q ^ x` on `[a, b]` for `q > 0`: `q ^ x ≤ max (q ^ a) (q ^ b)`. -/
theorem rpow_le_max_endpoints {q a b x : ℝ} (hq : 0 < q) (hx : x ∈ Icc a b) :
    q ^ x ≤ max (q ^ a) (q ^ b) := by
  rcases le_or_gt 1 q with hq1 | hq1
  · exact (Real.rpow_le_rpow_of_exponent_le hq1 hx.2).trans (le_max_right _ _)
  · exact (Real.rpow_le_rpow_of_exponent_ge hq hq1.le hx.1).trans (le_max_left _ _)

/-- **Contour shift of `gaussMellin` inside `Re w > 0`**: for `0 < a ≤ b`, `0 < L`, `0 < q`,
shifting between `Re w = a` and `Re w = b` incurs only the top/bottom horizontal segments. -/
theorem norm_gaussMellin_sub_le {a b L q : ℝ} (ha : 0 < a) (hab : a ≤ b) (hL : 0 < L) (hq : 0 < q) :
    ‖gaussMellin b L q - gaussMellin a L q‖
      ≤ ((b - a) / (Real.pi * L)) * Real.exp (b ^ 2 - L ^ 2) * max (q ^ a) (q ^ b) := by
  set z : ℂ := (a : ℂ) - (L : ℂ) * I
  set w : ℂ := (b : ℂ) + (L : ℂ) * I
  have hz_re : z.re = a := by simp [z]
  have hz_im : z.im = -L := by simp [z]
  have hw_re : w.re = b := by simp [w]
  have hw_im : w.im = L := by simp [w]
  have hsub : Rectangle z w ⊆ {0}ᶜ := by
    intro u hu
    simp only [Rectangle, hz_re, hz_im, hw_re, hw_im, uIcc_of_le hab,
      uIcc_of_le (show -L ≤ L by linarith), mem_reProdIm, Set.mem_Icc] at hu
    intro hu0
    rw [mem_singleton_iff] at hu0
    rw [hu0] at hu
    simp at hu
    linarith
  have hrect : RectangleIntegral (gaussMellinIntegrand q) z w = 0 :=
    HolomorphicOn.vanishesOnRectangle (differentiableOn_gaussMellinIntegrand hq) hsub
  simp only [RectangleIntegral, hz_re, hz_im, hw_re, hw_im] at hrect
  have hv_eq : VIntegral (gaussMellinIntegrand q) b (-L) L - VIntegral (gaussMellinIntegrand q) a (-L) L
      = HIntegral (gaussMellinIntegrand q) a b L - HIntegral (gaussMellinIntegrand q) a b (-L) := by
    linear_combination hrect
  have hgm : gaussMellin b L q - gaussMellin a L q
      = (1 / (2 * (Real.pi : ℂ) * I)) * (HIntegral (gaussMellinIntegrand q) a b L
          - HIntegral (gaussMellinIntegrand q) a b (-L)) := by
    rw [← vIntegral_div_two_pi_I_eq_gaussMellin b L q, ← vIntegral_div_two_pi_I_eq_gaussMellin a L q]
    simp only [smul_eq_mul, ← mul_sub, hv_eq]
  have hhor : ∀ y : ℝ, |y| = L →
      ‖HIntegral (gaussMellinIntegrand q) a b y‖
        ≤ (b - a) * (Real.exp (b ^ 2 - L ^ 2) * max (q ^ a) (q ^ b) / L) := by
    intro y hy
    have hy0 : y ≠ 0 := by intro h; rw [h, abs_zero] at hy; linarith
    unfold HIntegral
    refine (intervalIntegral.norm_integral_le_of_norm_le_const
      (C := Real.exp (b ^ 2 - L ^ 2) * max (q ^ a) (q ^ b) / L) ?_).trans ?_
    · intro x hx
      rw [uIoc_of_le hab] at hx
      have hxIcc : x ∈ Icc a b := ⟨hx.1.le, hx.2⟩
      have hx2 : x ^ 2 ≤ b ^ 2 := by nlinarith [hxIcc.1, hxIcc.2, ha]
      have hy2 : y ^ 2 = L ^ 2 := by rw [← sq_abs, hy]
      refine (norm_gaussMellinIntegrand_le_of_im_ne_zero hq hy0 x).trans ?_
      rw [hy, hy2]
      refine div_le_div_of_nonneg_right ?_ hL.le
      exact mul_le_mul (Real.exp_le_exp.mpr (by linarith))
        (rpow_le_max_endpoints hq hxIcc) (by positivity) (by positivity)
    · rw [abs_of_nonneg (sub_nonneg.mpr hab), mul_comm]
  rw [hgm, norm_mul]
  have hpi : 0 < Real.pi := Real.pi_pos
  have h1 : ‖(1 : ℂ) / (2 * (Real.pi : ℂ) * I)‖ = 1 / (2 * Real.pi) := by
    rw [norm_div, norm_one, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_of_nonneg hpi.le, norm_I, mul_one]
  rw [h1]
  have h2 := (norm_sub_le _ _).trans (add_le_add (hhor L (abs_of_pos hL))
    (hhor (-L) (by rw [abs_neg, abs_of_pos hL])))
  calc 1 / (2 * Real.pi) * ‖HIntegral (gaussMellinIntegrand q) a b L
          - HIntegral (gaussMellinIntegrand q) a b (-L)‖
      ≤ 1 / (2 * Real.pi) * (2 * ((b - a) * (Real.exp (b ^ 2 - L ^ 2) * max (q ^ a) (q ^ b) / L))) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = ((b - a) / (Real.pi * L)) * Real.exp (b ^ 2 - L ^ 2) * max (q ^ a) (q ^ b) := by field_simp

/-! ### Main-range and super-polynomial tail bounds at `L = log T`, `q = T / n` -/

/-- **Main-range kernel bound**: for `T ≥ e⁵`, `0 < η ≤ 1`, `β ∈ [3/2, 5/2]`, and any `n ≥ 1`,
`‖gaussMellin β (log T) (T / n)‖ ≤ (e / η) · T^η`. -/
theorem norm_gaussMellin_le_main {T β η : ℝ} (hT : Real.exp 5 ≤ T)
    (hβ : β ∈ Icc (3 / 2 : ℝ) (5 / 2)) (hη0 : 0 < η) (hη1 : η ≤ 1) {n : ℕ} (hn : 1 ≤ n) :
    ‖gaussMellin β (Real.log T) (T / n)‖ ≤ (Real.exp 1 / η) * T ^ η := by
  have hT1 : 1 < T := lt_of_lt_of_le (Real.one_lt_exp_iff.mpr (by norm_num)) hT
  have hT0 : 0 < T := by linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set L := Real.log T
  have hL : 5 ≤ L := by
    have := Real.log_le_log (Real.exp_pos 5) hT
    rwa [Real.log_exp] at this
  have hL0 : 0 < L := by linarith
  set q := T / n
  have hq0 : 0 < q := div_pos hT0 hn0
  have hqT : q ≤ T := div_le_self hT0.le hn1
  have hab : η ≤ β := hη1.trans (by linarith [hβ.1])
  have hmain : ‖gaussMellin η L q‖ ≤ (Real.exp 1 / (2 * η)) * T ^ η := by
    refine (norm_gaussMellin_le hη0 hL0.le hq0).trans ?_
    have he : Real.exp (η ^ 2) ≤ Real.exp 1 := Real.exp_le_exp.mpr (by nlinarith)
    have hqη : q ^ η ≤ T ^ η := Real.rpow_le_rpow hq0.le hqT hη0.le
    calc Real.exp (η ^ 2) * q ^ η / (2 * η)
        ≤ Real.exp 1 * T ^ η / (2 * η) :=
          div_le_div_of_nonneg_right (mul_le_mul he hqη (by positivity) (by positivity)) (by positivity)
      _ = (Real.exp 1 / (2 * η)) * T ^ η := by ring
  have hmax : max (q ^ η) (q ^ β) ≤ T ^ (3 : ℝ) := by
    have h1 : q ^ η ≤ T ^ (3 : ℝ) :=
      (Real.rpow_le_rpow hq0.le hqT hη0.le).trans (Real.rpow_le_rpow_of_exponent_le hT1.le (by linarith))
    have h2 : q ^ β ≤ T ^ (3 : ℝ) :=
      (Real.rpow_le_rpow hq0.le hqT (by linarith [hβ.1])).trans
        (Real.rpow_le_rpow_of_exponent_le hT1.le (by linarith [hβ.2]))
    exact max_le h1 h2
  have herr : ‖gaussMellin β L q - gaussMellin η L q‖ ≤ (Real.exp 1 / (2 * η)) * T ^ η := by
    refine (norm_gaussMellin_sub_le hη0 hab hL0 hq0).trans ?_
    have hpi : 3 < Real.pi := Real.pi_gt_three
    have hcoef : (β - η) / (Real.pi * L) ≤ 1 := by
      rw [div_le_one (by positivity)]
      nlinarith [hβ.2]
    have hexp : Real.exp (β ^ 2 - L ^ 2) * T ^ (3 : ℝ) ≤ 1 := by
      rw [show T ^ (3 : ℝ) = Real.exp (3 * L) by
        rw [← Real.exp_log hT0, ← Real.exp_mul]; congr 1; ring, ← Real.exp_add]
      exact Real.exp_le_one_iff.mpr (by nlinarith [hβ.1, hβ.2, hL])
    have hbase : 1 ≤ (Real.exp 1 / (2 * η)) * T ^ η := by
      have he1 : (2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
      have h1 : 1 ≤ Real.exp 1 / (2 * η) := by rw [ one_le_div (by positivity) ]; linarith
      have h2 : 1 ≤ T ^ η := Real.one_le_rpow hT1.le hη0.le
      nlinarith
    calc ((β - η) / (Real.pi * L)) * Real.exp (β ^ 2 - L ^ 2) * max (q ^ η) (q ^ β)
        ≤ 1 * Real.exp (β ^ 2 - L ^ 2) * T ^ (3 : ℝ) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_right hcoef (by positivity)) hmax
            (by positivity) (by positivity)
      _ = Real.exp (β ^ 2 - L ^ 2) * T ^ (3 : ℝ) := by ring
      _ ≤ 1 := hexp
      _ ≤ (Real.exp 1 / (2 * η)) * T ^ η := hbase
  calc ‖gaussMellin β L q‖
      ≤ ‖gaussMellin η L q‖ + ‖gaussMellin β L q - gaussMellin η L q‖ := by
        simpa [add_comm] using norm_add_le (gaussMellin η L q) (gaussMellin β L q - gaussMellin η L q)
    _ ≤ (Real.exp 1 / (2 * η)) * T ^ η + (Real.exp 1 / (2 * η)) * T ^ η := add_le_add hmain herr
    _ = (Real.exp 1 / η) * T ^ η := by ring

/-- **Super-polynomial tail bound**: for `0 < ε ≤ 1/4`, `α ∈ [1/2, 3/2]`, `T ≥ exp(64 / ε²)`,
and `(n : ℝ) > T^{1 + ε}`, `‖gaussMellin (3 - α) (log T) (T / n)‖ · n^{-α} ≤ T^{-3} · n^{-3}`. -/
theorem norm_gaussMellin_tail_le {T α ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 4)
    (hα : α ∈ Icc (1 / 2 : ℝ) (3 / 2)) (hT : Real.exp (64 / ε ^ 2) ≤ T)
    {n : ℕ} (hn : T ^ (1 + ε) < (n : ℝ)) :
    ‖gaussMellin (3 - α) (Real.log T) (T / n)‖ * (n : ℝ) ^ (-α)
      ≤ T ^ (-(3 : ℝ)) * (n : ℝ) ^ (-(3 : ℝ)) := by
  have h64 : (1024 : ℝ) ≤ 64 / ε ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg ε]
  have hT1 : 1 < T := lt_of_lt_of_le (Real.one_lt_exp_iff.mpr (by linarith)) hT
  have hT0 : 0 < T := by linarith
  have hn1 : (1 : ℝ) < n := (Real.one_lt_rpow hT1 (by linarith)).trans hn
  have hn0 : (0 : ℝ) < n := by linarith
  set L := Real.log T
  have hL64 : 64 / ε ^ 2 ≤ L := by
    have := Real.log_le_log (Real.exp_pos _) hT
    rwa [Real.log_exp] at this
  have hL1024 : 1024 ≤ L := h64.trans hL64
  have hL0 : 0 < L := by linarith
  set β := 3 - α
  have hβ1 : 3 / 2 ≤ β := by linarith [hα.2]
  have hβ2 : β ≤ 5 / 2 := by linarith [hα.1]
  set δ := (ε / 2) * L
  have hδ2 : 16 * L ≤ δ ^ 2 := by
    have hεL : 64 ≤ ε ^ 2 * L := by
      have := (div_le_iff₀ (show (0 : ℝ) < ε ^ 2 by positivity)).mp hL64
      linarith
    have : δ ^ 2 = (ε ^ 2 * L / 4) * L := by dsimp only [δ]; ring
    rw [this]
    nlinarith
  have hδ_hi : δ ≤ L / 8 := by dsimp only [δ]; nlinarith
  set γ := 3 + δ
  have hβ0 : 0 < β := by linarith
  have hγ0 : 0 < γ := by dsimp only [γ, δ]; positivity
  have hab : β ≤ γ := by dsimp only [γ, δ]; linarith [mul_nonneg hε0.le hL0.le]
  set q := T / n
  have hq0 : 0 < q := div_pos hT0 hn0
  have hq_lt : q < T ^ (-ε) := by
    rw [div_lt_iff₀ hn0]
    have : T ^ (-ε) * T ^ (1 + ε) = T := by
      rw [← Real.rpow_add hT0]; norm_num
    nlinarith [Real.rpow_pos_of_pos hT0 (-ε)]
  have hq1 : q < 1 := hq_lt.trans (Real.rpow_lt_one_of_one_lt_of_neg hT1 (by linarith))
  have he_half : Real.exp (-1) ≤ 1 / 2 := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
    linarith [Real.exp_one_gt_d9]
  -- Part 1: vertical integral at `Re w = γ`
  have hp1 : ‖gaussMellin γ L q‖ * (n : ℝ) ^ (-α) ≤ (1 / 2) * T ^ (-(3 : ℝ)) * (n : ℝ) ^ (-(3 : ℝ)) := by
    have hv := mul_le_mul_of_nonneg_right (norm_gaussMellin_le hγ0 hL0.le hq0)
      (Real.rpow_nonneg hn0.le (-α))
    refine hv.trans ?_
    have h2γ : 1 ≤ 2 * γ := by dsimp only [γ, δ]; linarith [mul_nonneg hε0.le hL0.le]
    have hdiv : Real.exp (γ ^ 2) * q ^ γ / (2 * γ) ≤ Real.exp (γ ^ 2) * q ^ γ :=
      div_le_self (by positivity) h2γ
    have hqγ : q ^ γ * (n : ℝ) ^ (-α) ≤ T ^ (3 : ℝ) * q ^ δ * (n : ℝ) ^ (-(3 : ℝ)) := by
      have hsplit : q ^ γ = q ^ (3 : ℝ) * q ^ δ := Real.rpow_add hq0 3 δ
      have hq3 : q ^ (3 : ℝ) = T ^ (3 : ℝ) * (n : ℝ) ^ (-(3 : ℝ)) := by
        dsimp only [q]
        rw [div_eq_mul_inv, Real.mul_rpow hT0.le (inv_nonneg.mpr hn0.le), Real.inv_rpow hn0.le,
          ← Real.rpow_neg hn0.le]
      have hnα : (n : ℝ) ^ (-α) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn1.le (by linarith [hα.1])
      rw [hsplit, hq3]
      calc T ^ (3 : ℝ) * (n : ℝ) ^ (-(3 : ℝ)) * q ^ δ * (n : ℝ) ^ (-α)
          ≤ T ^ (3 : ℝ) * (n : ℝ) ^ (-(3 : ℝ)) * q ^ δ * 1 :=
            mul_le_mul_of_nonneg_left hnα (by positivity)
        _ = T ^ (3 : ℝ) * q ^ δ * (n : ℝ) ^ (-(3 : ℝ)) := by ring
    have hqδ : q ^ δ ≤ Real.exp (-2 * δ ^ 2) := by
      have h1 : q ^ δ ≤ (T ^ (-ε)) ^ δ := Real.rpow_le_rpow hq0.le hq_lt.le (by dsimp only [δ]; positivity)
      rw [← Real.rpow_mul hT0.le, ← Real.exp_log hT0, ← Real.exp_mul] at h1
      refine h1.trans (Real.exp_le_exp.mpr ?_)
      have : L * (-ε * δ) = -2 * δ ^ 2 := by dsimp only [δ]; ring
      linarith
    have hexp_main : Real.exp (γ ^ 2) * T ^ (3 : ℝ) * Real.exp (-2 * δ ^ 2)
        ≤ (1 / 2) * T ^ (-(3 : ℝ)) := by
      have hT3 : T ^ (3 : ℝ) = Real.exp (3 * L) := by
        rw [← Real.exp_log hT0, ← Real.exp_mul]; congr 1; ring
      have hTm3 : T ^ (-(3 : ℝ)) = Real.exp (-3 * L) := by
        rw [← Real.exp_log hT0, ← Real.exp_mul]; congr 1; ring
      rw [hT3, hTm3, ← Real.exp_add, ← Real.exp_add]
      have hlin : γ ^ 2 + 3 * L + -2 * δ ^ 2 ≤ -1 + (-3 * L) := by
        have hγ2 : γ ^ 2 = 9 + 6 * δ + δ ^ 2 := by dsimp only [γ]; ring
        linarith [hγ2, hδ2, hδ_hi, hL1024]
      calc Real.exp (γ ^ 2 + 3 * L + -2 * δ ^ 2)
          ≤ Real.exp (-1 + (-3 * L)) := Real.exp_le_exp.mpr hlin
        _ = Real.exp (-1) * Real.exp (-3 * L) := Real.exp_add _ _
        _ ≤ (1 / 2) * Real.exp (-3 * L) := mul_le_mul_of_nonneg_right he_half (by positivity)
    calc (Real.exp (γ ^ 2) * q ^ γ / (2 * γ)) * (n : ℝ) ^ (-α)
        ≤ (Real.exp (γ ^ 2) * q ^ γ) * (n : ℝ) ^ (-α) :=
          mul_le_mul_of_nonneg_right hdiv (by positivity)
      _ = Real.exp (γ ^ 2) * (q ^ γ * (n : ℝ) ^ (-α)) := by ring
      _ ≤ Real.exp (γ ^ 2) * (T ^ (3 : ℝ) * q ^ δ * (n : ℝ) ^ (-(3 : ℝ))) :=
          mul_le_mul_of_nonneg_left hqγ (by positivity)
      _ ≤ Real.exp (γ ^ 2) * (T ^ (3 : ℝ) * Real.exp (-2 * δ ^ 2) * (n : ℝ) ^ (-(3 : ℝ))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hqδ (by positivity)) (by positivity))
            (by positivity)
      _ = (Real.exp (γ ^ 2) * T ^ (3 : ℝ) * Real.exp (-2 * δ ^ 2)) * (n : ℝ) ^ (-(3 : ℝ)) := by ring
      _ ≤ ((1 / 2) * T ^ (-(3 : ℝ))) * (n : ℝ) ^ (-(3 : ℝ)) :=
          mul_le_mul_of_nonneg_right hexp_main (by positivity)
      _ = (1 / 2) * T ^ (-(3 : ℝ)) * (n : ℝ) ^ (-(3 : ℝ)) := by ring
  -- Part 2: horizontal shift error between `β` and `γ`
  have hp2 : ‖gaussMellin γ L q - gaussMellin β L q‖ * (n : ℝ) ^ (-α)
      ≤ (1 / 2) * T ^ (-(3 : ℝ)) * (n : ℝ) ^ (-(3 : ℝ)) := by
    have hs := mul_le_mul_of_nonneg_right (norm_gaussMellin_sub_le hβ0 hab hL0 hq0)
      (Real.rpow_nonneg hn0.le (-α))
    refine hs.trans ?_
    have hmax : max (q ^ β) (q ^ γ) = q ^ β :=
      max_eq_left (Real.rpow_le_rpow_of_exponent_ge hq0 hq1.le hab)
    have hqβ : q ^ β * (n : ℝ) ^ (-α) ≤ T ^ (3 : ℝ) * (n : ℝ) ^ (-(3 : ℝ)) := by
      have h1 : q ^ β = T ^ β * (n : ℝ) ^ (-β) := by
        dsimp only [q]
        rw [div_eq_mul_inv, Real.mul_rpow hT0.le (inv_nonneg.mpr hn0.le), Real.inv_rpow hn0.le,
          ← Real.rpow_neg hn0.le]
      rw [h1, mul_assoc, ← Real.rpow_add hn0, show -β + -α = -(3 : ℝ) by dsimp only [β]; ring]
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le hT1.le (by linarith [hβ2])) (by positivity)
    have hcoef : (γ - β) / (Real.pi * L) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have hpi : 3 < Real.pi := Real.pi_gt_three
      nlinarith [hδ_hi, hL1024, hβ1]
    have hexp_hor : Real.exp (γ ^ 2 - L ^ 2) * T ^ (3 : ℝ) ≤ (1 / 2) * T ^ (-(3 : ℝ)) := by
      have hT3 : T ^ (3 : ℝ) = Real.exp (3 * L) := by
        rw [← Real.exp_log hT0, ← Real.exp_mul]; congr 1; ring
      have hTm3 : T ^ (-(3 : ℝ)) = Real.exp (-3 * L) := by
        rw [← Real.exp_log hT0, ← Real.exp_mul]; congr 1; ring
      rw [hT3, hTm3, ← Real.exp_add]
      have hγ_half : γ ≤ L / 2 := by dsimp only [γ]; linarith [hδ_hi, hL1024]
      have hlin : γ ^ 2 - L ^ 2 + 3 * L ≤ -1 + (-3 * L) := by
        nlinarith [hγ_half, hγ0, hL1024]
      calc Real.exp (γ ^ 2 - L ^ 2 + 3 * L)
          ≤ Real.exp (-1 + (-3 * L)) := Real.exp_le_exp.mpr hlin
        _ = Real.exp (-1) * Real.exp (-3 * L) := Real.exp_add _ _
        _ ≤ (1 / 2) * Real.exp (-3 * L) := mul_le_mul_of_nonneg_right he_half (by positivity)
    rw [hmax]
    calc ((γ - β) / (Real.pi * L) * Real.exp (γ ^ 2 - L ^ 2) * q ^ β) * (n : ℝ) ^ (-α)
        = ((γ - β) / (Real.pi * L)) * Real.exp (γ ^ 2 - L ^ 2) * (q ^ β * (n : ℝ) ^ (-α)) := by ring
      _ ≤ 1 * Real.exp (γ ^ 2 - L ^ 2) * (T ^ (3 : ℝ) * (n : ℝ) ^ (-(3 : ℝ))) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hcoef (by positivity)) hqβ
            (by positivity) (by positivity)
      _ = (Real.exp (γ ^ 2 - L ^ 2) * T ^ (3 : ℝ)) * (n : ℝ) ^ (-(3 : ℝ)) := by ring
      _ ≤ ((1 / 2) * T ^ (-(3 : ℝ))) * (n : ℝ) ^ (-(3 : ℝ)) :=
          mul_le_mul_of_nonneg_right hexp_hor (by positivity)
      _ = (1 / 2) * T ^ (-(3 : ℝ)) * (n : ℝ) ^ (-(3 : ℝ)) := by ring
  have htri : ‖gaussMellin β L q‖ ≤ ‖gaussMellin γ L q‖ + ‖gaussMellin γ L q - gaussMellin β L q‖ := by
    have := norm_sub_le (gaussMellin γ L q) (gaussMellin γ L q - gaussMellin β L q)
    simpa [sub_sub_cancel] using this
  calc ‖gaussMellin β L q‖ * (n : ℝ) ^ (-α)
      ≤ (‖gaussMellin γ L q‖ + ‖gaussMellin γ L q - gaussMellin β L q‖) * (n : ℝ) ^ (-α) :=
        mul_le_mul_of_nonneg_right htri (by positivity)
    _ = ‖gaussMellin γ L q‖ * (n : ℝ) ^ (-α)
          + ‖gaussMellin γ L q - gaussMellin β L q‖ * (n : ℝ) ^ (-α) := add_mul _ _ _
    _ ≤ (1 / 2) * T ^ (-(3 : ℝ)) * (n : ℝ) ^ (-(3 : ℝ))
          + (1 / 2) * T ^ (-(3 : ℝ)) * (n : ℝ) ^ (-(3 : ℝ)) := add_le_add hp1 hp2
    _ = T ^ (-(3 : ℝ)) * (n : ℝ) ^ (-(3 : ℝ)) := by ring

/-! ### Right-edge Dirichlet series expansion on `Re(z + w) = 3` -/

/-- `(n : ℂ)^{-(z + w)} · T^w = n^{-z} · (T / n)^w` for `T > 0` and `n ≥ 1`. -/
theorem natCast_cpow_neg_add_mul_cpow {T : ℝ} (hT : 0 < T) {n : ℕ} (hn : 1 ≤ n) (z w : ℂ) :
    (n : ℂ) ^ (-(z + w)) * (T : ℂ) ^ w = (n : ℂ) ^ (-z) * (((T / n : ℝ) : ℂ) ^ w) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have h1 : (n : ℂ) ^ (-(z + w)) = (n : ℂ) ^ (-z) * (n : ℂ) ^ (-w) := by
    rw [show -(z + w) = -z + -w by ring, Complex.cpow_add _ _ hnC]
  have h2 : (T : ℂ) ^ w = (((T / n : ℝ) : ℂ) ^ w) * (n : ℂ) ^ w := by
    have hmul := Complex.mul_cpow_ofReal_nonneg (div_nonneg hT.le hnR.le) (Nat.cast_nonneg n) w
    simp only [Complex.ofReal_natCast] at hmul
    have hdiv : (((T / (n : ℝ) : ℝ) : ℂ) * (n : ℂ)) = (T : ℂ) := by
      exact_mod_cast div_mul_cancel₀ T hnR.ne'
    rw [hdiv] at hmul
    exact hmul
  have h3 : (n : ℂ) ^ (-w) * (n : ℂ) ^ w = 1 := by
    rw [← Complex.cpow_add _ _ hnC, neg_add_cancel, Complex.cpow_zero]
  rw [h1, h2]
  calc (n : ℂ) ^ (-z) * (n : ℂ) ^ (-w) * ((((T / n : ℝ) : ℂ) ^ w) * (n : ℂ) ^ w)
      = (n : ℂ) ^ (-z) * (((T / n : ℝ) : ℂ) ^ w) * ((n : ℂ) ^ (-w) * (n : ℂ) ^ w) := by ring
    _ = (n : ℂ) ^ (-z) * (((T / n : ℝ) : ℂ) ^ w) := by rw [h3, mul_one]

/-- **Right-edge Dirichlet expansion**: for `X ≥ 1`, `T > 0`, `L > 0`, and `z = α + it` with
`α ∈ [1/2, 3/2]`, the vertical integral on `Re w = 3 - α` (`Re(z + w) = 3`) equals the convergent
Dirichlet series `∑'_{n > X} truncMoebiusSum X n · gaussMellin (3 - α) L (T / n) · n^{-z}`. -/
theorem rightEdge_eq_tsum {X : ℕ} (hX : 1 ≤ X) {T L α t : ℝ} (hT : 0 < T) (hL : 0 < L)
    (hα : α ∈ Icc (1 / 2 : ℝ) (3 / 2)) :
    ((1 / (2 * (Real.pi : ℂ) * I)) • VIntegral
        (fun w => mollifiedDetector X (((α : ℂ) + (t : ℂ) * I) + w) * gaussMellinIntegrand T w)
        (3 - α) (-L) L)
      = ∑' n : ℕ, if X < n then (truncMoebiusSum X n : ℂ)
          * gaussMellin (3 - α) L (T / n) * (n : ℂ) ^ (-((α : ℂ) + (t : ℂ) * I)) else 0 := by
  set z : ℂ := (α : ℂ) + (t : ℂ) * I
  set β : ℝ := 3 - α
  have hβ : 3 / 2 ≤ β := by dsimp only [β]; linarith [hα.2]
  have hβ0 : 0 < β := by linarith
  set F : ℕ → ℝ → ℂ := fun n v =>
    if X < n then (truncMoebiusSum X n : ℂ) * (n : ℂ) ^ (-z)
      * gaussMellinIntegrand (T / n) ((β : ℂ) + (v : ℂ) * I) else 0
  have hpt_eq : ∀ v : ℝ,
      mollifiedDetector X (z + ((β : ℂ) + (v : ℂ) * I)) * gaussMellinIntegrand T ((β : ℂ) + (v : ℂ) * I)
        = ∑' n : ℕ, F n v := by
    intro v
    have hre : (z + ((β : ℂ) + (v : ℂ) * I)).re = 3 := by simp [z, β]
    rw [mollifiedDetector_eq_tsum hX (by linarith), ← tsum_mul_right]
    refine tsum_congr fun n => ?_
    dsimp only [F]
    split_ifs with hnX
    · have hn1 : 1 ≤ n := by omega
      unfold gaussMellinIntegrand
      have hpow := natCast_cpow_neg_add_mul_cpow hT hn1 z ((β : ℂ) + (v : ℂ) * I)
      calc (truncMoebiusSum X n : ℂ) * (n : ℂ) ^ (-(z + ((β : ℂ) + (v : ℂ) * I)))
            * (Complex.exp (((β : ℂ) + (v : ℂ) * I) ^ 2) * (T : ℂ) ^ ((β : ℂ) + (v : ℂ) * I)
              / ((β : ℂ) + (v : ℂ) * I))
          = (truncMoebiusSum X n : ℂ) * Complex.exp (((β : ℂ) + (v : ℂ) * I) ^ 2)
              * ((n : ℂ) ^ (-(z + ((β : ℂ) + (v : ℂ) * I))) * (T : ℂ) ^ ((β : ℂ) + (v : ℂ) * I))
              / ((β : ℂ) + (v : ℂ) * I) := by ring
        _ = (truncMoebiusSum X n : ℂ) * (n : ℂ) ^ (-z)
              * (Complex.exp (((β : ℂ) + (v : ℂ) * I) ^ 2)
                * (((T / n : ℝ) : ℂ) ^ ((β : ℂ) + (v : ℂ) * I)) / ((β : ℂ) + (v : ℂ) * I)) := by
            rw [hpow]; ring
    · simp
  -- uniform summable bound in `v` for `intervalIntegral.integral_tsum`
  set M : ℕ → ℝ := fun n => (Real.exp (β ^ 2) * T ^ β / β) * (n : ℝ) ^ (-(2 : ℝ))
  have hM_sum : Summable M :=
    (Real.summable_nat_rpow.mpr (by norm_num)).mul_left _
  have hF_bound : ∀ n : ℕ, ∀ v : ℝ, ‖F n v‖ ≤ M n := by
    intro n v
    dsimp only [F, M]
    split_ifs with hnX
    · have hn1 : 1 ≤ n := by omega
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
      have hq0 : 0 < T / n := div_pos hT hn0
      rw [norm_mul, norm_mul, Complex.norm_natCast_cpow_of_pos hn1]
      have hre_z : (-z).re = -α := by simp [z]
      rw [hre_z]
      have h1 := norm_truncMoebiusSum_le_self X n
      have h2 := norm_gaussMellinIntegrand_le_of_re_ne_zero hq0 hβ0.ne' v
      rw [abs_of_pos hβ0] at h2
      have h3 : Real.exp (β ^ 2 - v ^ 2) ≤ Real.exp (β ^ 2) :=
        Real.exp_le_exp.mpr (by nlinarith [sq_nonneg v])
      have h4 : (T / n) ^ β = T ^ β * (n : ℝ) ^ (-β) := by
        rw [div_eq_mul_inv, Real.mul_rpow hT.le (inv_nonneg.mpr hn0.le), Real.inv_rpow hn0.le,
          ← Real.rpow_neg hn0.le]
      have h5 : (n : ℝ) * (n : ℝ) ^ (-α) * (n : ℝ) ^ (-β) = (n : ℝ) ^ (-(2 : ℝ)) := by
        calc (n : ℝ) * (n : ℝ) ^ (-α) * (n : ℝ) ^ (-β)
            = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-α) * (n : ℝ) ^ (-β) := by rw [Real.rpow_one]
          _ = (n : ℝ) ^ (-(2 : ℝ)) := by
              rw [← Real.rpow_add hn0, ← Real.rpow_add hn0]
              congr 1; dsimp only [β]; ring
      calc ‖(truncMoebiusSum X n : ℂ)‖ * (n : ℝ) ^ (-α)
            * ‖gaussMellinIntegrand (T / n) ((β : ℂ) + (v : ℂ) * I)‖
          ≤ (n : ℝ) * (n : ℝ) ^ (-α) * (Real.exp (β ^ 2) * (T ^ β * (n : ℝ) ^ (-β)) / β) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_right h1 (by positivity)) ?_
              (by positivity) (by positivity)
            refine h2.trans ?_
            rw [h4]
            exact div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_right h3 (by positivity)) hβ0.le
        _ = (Real.exp (β ^ 2) * T ^ β / β) * ((n : ℝ) * (n : ℝ) ^ (-α) * (n : ℝ) ^ (-β)) := by ring
        _ = (Real.exp (β ^ 2) * T ^ β / β) * (n : ℝ) ^ (-(2 : ℝ)) := by rw [h5]
    · rw [norm_zero]; positivity
  have hF_cont : ∀ n : ℕ, Continuous (F n) := by
    intro n
    dsimp only [F]
    split_ifs with hnX
    · have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 1 ≤ n by omega)
      have hq0 : (0 : ℝ) < T / n := div_pos hT hn0
      have hqC : ((T / n : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq0.ne'
      refine continuous_const.mul ?_
      unfold gaussMellinIntegrand
      refine Continuous.div₀ ?_ (by fun_prop) (fun v => ?_)
      · exact (Continuous.cexp (f := fun v : ℝ => ((β : ℂ) + (v : ℂ) * I) ^ 2) (by fun_prop)).mul
          (Continuous.const_cpow (f := fun v : ℝ => (β : ℂ) + (v : ℂ) * I) (by fun_prop)
            (Or.inl hqC))
      · intro h; have hre := congrArg Complex.re h
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.ofReal_im, Complex.zero_re, mul_zero, mul_one, sub_zero, add_zero] at hre
        linarith
    · exact continuous_const
  -- swap integral and tsum via dominated convergence on `Ioc (-L) L`
  have hLL : -L ≤ L := by linarith
  have hint : ∀ n : ℕ, IntegrableOn (F n) (Set.Ioc (-L) L) :=
    fun n => (hF_cont n).integrableOn_Ioc
  have hsum_int : Summable (fun n : ℕ => ∫ v in Set.Ioc (-L) L, ‖F n v‖) := by
    refine (hM_sum.mul_left (2 * L)).of_nonneg_of_le
      (fun n => setIntegral_nonneg measurableSet_Ioc fun _ _ => norm_nonneg _) (fun n => ?_)
    rw [← intervalIntegral.integral_of_le hLL]
    calc ∫ v in (-L)..L, ‖F n v‖
        ≤ ∫ _v in (-L)..L, M n :=
          intervalIntegral.integral_mono_on hLL ((hF_cont n).norm.intervalIntegrable _ _)
            intervalIntegrable_const (fun v _ => hF_bound n v)
      _ = (2 * L) * M n := by rw [intervalIntegral.integral_const, smul_eq_mul]; ring
  have hswap : (∫ v in (-L)..L, ∑' n : ℕ, F n v) = ∑' n : ℕ, ∫ v in (-L)..L, F n v := by
    rw [intervalIntegral.integral_of_le hLL,
      ← MeasureTheory.integral_tsum_of_summable_integral_norm hint hsum_int]
    exact tsum_congr fun n => (intervalIntegral.integral_of_le hLL).symm
  have hcoeff : ((1 / (2 * (Real.pi : ℂ) * I)) • VIntegral
      (fun w => mollifiedDetector X (z + w) * gaussMellinIntegrand T w) β (-L) L)
      = (1 / (2 * (Real.pi : ℂ))) * ∫ v in (-L)..L, ∑' n : ℕ, F n v := by
    simp only [VIntegral, smul_eq_mul]
    rw [intervalIntegral.integral_congr fun v _ => hpt_eq v]
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hI : (I : ℂ) ≠ 0 := I_ne_zero
    field_simp
  rw [hcoeff, hswap, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  dsimp only [F]
  split_ifs with hnX
  · rw [intervalIntegral.integral_const_mul]
    unfold gaussMellin
    ring
  · rw [intervalIntegral.integral_zero, mul_zero]

end Cvs.Zeta.GaussKernel.SmoothedGaussMellin

end
