import Mathlib
import Cvs.L2a.BandTransferBandForm
import Cvs.L2a.FarIntegrationByParts
import Cvs.L2a.OrbitGapIntegerM
import Cvs.L2a.QIdentityCutPoint
import Cvs.L2a.QIdentityIterated
import Cvs.Prolate.Envelope.RungCountEnvelope
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.RungCauchySplit

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The exact cut kernel against the simplified one

`μ = μ_si + e^{icxy}(2cxy/(Q(cy + ξ)) + pQ′/Q²)`, so `c|μ − μ_si| ≤ K|μ_si|` with `K` explicit in `(x, y, η)`, bounded
uniformly on the bottom near, bottom far and top near ranges, and on the `m = 2` strip after the weight `1 − wF ≤ π²(2 − t)²`.
Averaging `sin²(ct)` against a `C¹` weight costs `O(1/c)`.
-/

noncomputable section

namespace Cvs.L2a.CutKernelSimplified

open Real Set MeasureTheory Complex intervalIntegral
open Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.AngularProlateTailPositive Cvs.L2a.FarIntegrationByParts Cvs.Prolate.RungCauchySplit
open scoped ComplexConjugate

/-- The simplified kernel of R1/R2: `μ_si(ξ) = −i e^{icxy}/(cy + ξ)`. -/
def muSi (c y x ξ : ℝ) : ℂ := -I * eF c y x / ((c * y + ξ : ℝ) : ℂ)

/-- **The exact cut kernel against the simplified one**: `μ = μ_si + e^{icxy}(2cxy/(Q(cy + ξ)) + pQ′/Q²)`. -/
theorem muCut_eq_muSi_add {c y x ξ : ℝ} (hc : 0 < c) (hx : 0 < x) (hy : 0 < y) (hξ : c * y + ξ ≠ 0) :
    Cvs.L2a.QIdentityCutPoint.muCut c y x ξ = muSi c y x ξ + eF c y x * (((2 * c * x * y : ℝ) : ℂ)
      / (Cvs.L2a.QIdentityCutPoint.qQk c y x ξ * ((c * y + ξ : ℝ) : ℂ)) + ((pP x : ℝ) : ℂ) * qQ₁ c y x / Cvs.L2a.QIdentityCutPoint.qQk c y x ξ ^ 2) := by
  have hQ : Cvs.L2a.QIdentityCutPoint.qQk c y x ξ ≠ 0 := by
    intro h
    have h1 := Cvs.L2a.QIdentityCutPoint.le_norm_qQk_im (ξ := ξ) hc.le hx.le hy.le
    rw [h, norm_zero] at h1
    have : 0 < 2 * c * x * y := by positivity
    linarith
  have hs : ((c * y + ξ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hξ
  have key : ((pP x : ℝ) : ℂ) * (I * ((ξ - c * y : ℝ) : ℂ)) * ((c * y + ξ : ℝ) : ℂ)
      = -I * Cvs.L2a.QIdentityCutPoint.qQk c y x ξ + ((2 * c * x * y : ℝ) : ℂ) := by
    unfold Cvs.L2a.QIdentityCutPoint.qQk
    push_cast
    linear_combination (-(2 * (c : ℂ) * x * y)) * I_sq
  have h1 : ((pP x : ℝ) : ℂ) * (I * ((ξ - c * y : ℝ) : ℂ) / Cvs.L2a.QIdentityCutPoint.qQk c y x ξ)
      = -I / ((c * y + ξ : ℝ) : ℂ) + ((2 * c * x * y : ℝ) : ℂ) / (Cvs.L2a.QIdentityCutPoint.qQk c y x ξ * ((c * y + ξ : ℝ) : ℂ)) := by
    rw [div_add_div _ _ hs (mul_ne_zero hQ hs), ← mul_div_assoc,
      div_eq_div_iff hQ (mul_ne_zero hs (mul_ne_zero hQ hs))]
    linear_combination (((c * y + ξ : ℝ) : ℂ) * Cvs.L2a.QIdentityCutPoint.qQk c y x ξ) * key
  unfold Cvs.L2a.QIdentityCutPoint.muCut Cvs.L2a.QIdentityCutPoint.muQ muSi
  rw [mul_add, h1]
  ring

/-- The comparison factor `K = 2xy/(p|y² − η²|) + 2(x|y² − 1| + y/c)|y + η|/(p(y² − η²)²)`. -/
def kCmp (c x y η : ℝ) : ℝ :=
  2 * x * y / (pP x * |y ^ 2 - η ^ 2|) + 2 * (x * |y ^ 2 - 1| + y / c) * |y + η| / (pP x * (y ^ 2 - η ^ 2) ^ 2)

/-- **The `O(1/c)` comparison**: `c|μ − μ_si| ≤ K|μ_si|` at `ξ = cη`. -/
theorem mul_norm_muCut_sub_muSi_le {c y x η : ℝ} (hc : 0 < c) (hx : 1 < x) (hy : 0 < y) (hη : y + η ≠ 0)
    (hD : y ^ 2 ≠ η ^ 2) :
    c * ‖Cvs.L2a.QIdentityCutPoint.muCut c y x (c * η) - muSi c y x (c * η)‖ ≤ kCmp c x y η * ‖muSi c y x (c * η)‖ := by
  have hp : 0 < pP x := by unfold pP; nlinarith
  have hs : c * y + c * η ≠ 0 := by rw [← mul_add]; exact mul_ne_zero hc.ne' hη
  have ha : 0 < |y + η| := abs_pos.2 hη
  have hDp : 0 < |y ^ 2 - η ^ 2| := abs_pos.2 (sub_ne_zero.2 hD)
  have hQL : pP x * c ^ 2 * |y ^ 2 - η ^ 2| ≤ ‖Cvs.L2a.QIdentityCutPoint.qQk c y x (c * η)‖ := by
    have h := Cvs.L2a.QIdentityCutPoint.le_norm_qQk_re (c := c) (y := y) (ξ := c * η) hx.le
    have e : c ^ 2 * y ^ 2 - (c * η) ^ 2 = c ^ 2 * (y ^ 2 - η ^ 2) := by ring
    rw [e, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < c ^ 2), ← mul_assoc] at h
    exact h
  have hL : 0 < pP x * c ^ 2 * |y ^ 2 - η ^ 2| := by positivity
  have hQpos : 0 < ‖Cvs.L2a.QIdentityCutPoint.qQk c y x (c * η)‖ := lt_of_lt_of_le hL hQL
  have hQ1 := Cvs.L2a.QIdentityIterated.norm_qQ₁_le_abs (c := c) (y := y) (x := x) (by linarith) hy.le hc.le
  rw [muCut_eq_muSi_add hc (by linarith) hy hs, add_sub_cancel_left]
  have hsi : ‖muSi c y x (c * η)‖ = 1 / (c * |y + η|) := by
    unfold muSi
    rw [norm_div, norm_mul, norm_neg, Complex.norm_I, (continuous_eF c y).2, Complex.norm_real,
      Real.norm_eq_abs, ← mul_add, abs_mul, abs_of_pos hc, one_mul]
  have hT1 : ‖((2 * c * x * y : ℝ) : ℂ) / (Cvs.L2a.QIdentityCutPoint.qQk c y x (c * η) * ((c * y + c * η : ℝ) : ℂ))‖
      = 2 * c * x * y / (‖Cvs.L2a.QIdentityCutPoint.qQk c y x (c * η)‖ * (c * |y + η|)) := by
    rw [norm_div, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (by have : 0 < x := by linarith
                     positivity), ← mul_add, abs_mul, abs_of_pos hc]
  have hT2 : ‖((pP x : ℝ) : ℂ) * qQ₁ c y x / Cvs.L2a.QIdentityCutPoint.qQk c y x (c * η) ^ 2‖
      = pP x * ‖qQ₁ c y x‖ / ‖Cvs.L2a.QIdentityCutPoint.qQk c y x (c * η)‖ ^ 2 := by
    rw [norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp]
  rw [hsi, norm_mul, (continuous_eF c y).2, one_mul]
  have hx0 : 0 < x := by linarith
  calc c * ‖((2 * c * x * y : ℝ) : ℂ) / (Cvs.L2a.QIdentityCutPoint.qQk c y x (c * η) * ((c * y + c * η : ℝ) : ℂ))
          + ((pP x : ℝ) : ℂ) * qQ₁ c y x / Cvs.L2a.QIdentityCutPoint.qQk c y x (c * η) ^ 2‖
        ≤ c * (‖((2 * c * x * y : ℝ) : ℂ) / (Cvs.L2a.QIdentityCutPoint.qQk c y x (c * η) * ((c * y + c * η : ℝ) : ℂ))‖
          + ‖((pP x : ℝ) : ℂ) * qQ₁ c y x / Cvs.L2a.QIdentityCutPoint.qQk c y x (c * η) ^ 2‖) := by
        gcongr; exact norm_add_le _ _
    _ = c * (2 * c * x * y / (‖Cvs.L2a.QIdentityCutPoint.qQk c y x (c * η)‖ * (c * |y + η|))
          + pP x * ‖qQ₁ c y x‖ / ‖Cvs.L2a.QIdentityCutPoint.qQk c y x (c * η)‖ ^ 2) := by rw [hT1, hT2]
    _ ≤ c * (2 * c * x * y / (pP x * c ^ 2 * |y ^ 2 - η ^ 2| * (c * |y + η|))
          + pP x * (2 * c ^ 2 * x * |y ^ 2 - 1| + 2 * c * y) / (pP x * c ^ 2 * |y ^ 2 - η ^ 2|) ^ 2) := by
        gcongr
    _ = kCmp c x y η * (1 / (c * |y + η|)) := by
        unfold kCmp
        rw [← sq_abs (y ^ 2 - η ^ 2)]
        field_simp

/-- The near-range factor: `y ≤ y₀ < 1 ≤ |η| ≤ Y`. -/
def kNear (c x y₀ Y : ℝ) : ℝ :=
  2 * x * y₀ / (pP x * (1 - y₀ ^ 2)) + 2 * (x + y₀ / c) * (y₀ + Y) / (pP x * (1 - y₀ ^ 2) ^ 2)

theorem kCmp_le_near {c x y η y₀ Y : ℝ} (hc : 0 < c) (hx : 1 < x) (hy : 0 < y) (hyy : y ≤ y₀) (hy₀ : y₀ < 1)
    (hη1 : 1 ≤ |η|) (hηY : |η| ≤ Y) : kCmp c x y η ≤ kNear c x y₀ Y := by
  have hp : 0 < pP x := by unfold pP; nlinarith
  have hx0 : 0 < x := by linarith
  have hy₀0 : 0 < y₀ := lt_of_lt_of_le hy hyy
  have h1y : 0 < 1 - y₀ ^ 2 := by nlinarith
  have hη2 : 1 ≤ η ^ 2 := by rw [← sq_abs]; nlinarith [abs_nonneg η]
  have hy2 : y ^ 2 ≤ y₀ ^ 2 := by gcongr
  have hDa : 1 - y₀ ^ 2 ≤ |y ^ 2 - η ^ 2| := by
    rw [abs_sub_comm, abs_of_nonneg (by nlinarith)]; linarith
  have hD2 : (1 - y₀ ^ 2) ^ 2 ≤ (y ^ 2 - η ^ 2) ^ 2 := by rw [← sq_abs (y ^ 2 - η ^ 2)]; gcongr
  have hE : x * |y ^ 2 - 1| ≤ x := by
    have : |y ^ 2 - 1| ≤ 1 := by rw [abs_le]; constructor <;> nlinarith
    nlinarith
  have hyc : y / c ≤ y₀ / c := by gcongr
  have hA : |y + η| ≤ y₀ + Y := (abs_add_le y η).trans (by rw [abs_of_pos hy]; linarith)
  unfold kCmp kNear
  have t1 : 2 * x * y / (pP x * |y ^ 2 - η ^ 2|) ≤ 2 * x * y₀ / (pP x * (1 - y₀ ^ 2)) := by
    apply div_le_div₀ (by positivity) (by gcongr) (by positivity) (by gcongr)
  have t2 : 2 * (x * |y ^ 2 - 1| + y / c) * |y + η| / (pP x * (y ^ 2 - η ^ 2) ^ 2)
      ≤ 2 * (x + y₀ / c) * (y₀ + Y) / (pP x * (1 - y₀ ^ 2) ^ 2) := by
    apply div_le_div₀ (by have : 0 ≤ y₀ + Y := by linarith [abs_nonneg η]
                          positivity) _ (by positivity) (by gcongr)
    gcongr
  linarith

/-- The far-range factor: `y ≥ y₁ > Y ≥ |η|`. -/
def kFar (c x y₁ Y : ℝ) : ℝ :=
  2 * x * y₁ / (pP x * (y₁ ^ 2 - Y ^ 2)) + 2 * x / (pP x * (y₁ - Y))
    + 2 * x / (pP x ^ 2 * (y₁ - Y) * (y₁ ^ 2 - Y ^ 2)) + 2 * y₁ / (c * pP x * (y₁ - Y) * (y₁ ^ 2 - Y ^ 2))

theorem kCmp_le_far {c x y η y₁ Y : ℝ} (hc : 0 < c) (hx : 1 < x) (hY : 1 ≤ Y) (hηY : |η| ≤ Y)
    (hYx : Y ^ 2 ≤ 1 + 1 / (x ^ 2 - 1)) (hy₁ : Y < y₁) (hy : y₁ ≤ y) : kCmp c x y η ≤ kFar c x y₁ Y := by
  have hp : 0 < pP x := by unfold pP; nlinarith
  have hp' : pP x = x ^ 2 - 1 := rfl
  have hx0 : 0 < x := by linarith
  have hη := abs_le.1 hηY
  have hη2 : η ^ 2 ≤ Y ^ 2 := by rw [← sq_abs]; gcongr
  have hA₁ : 0 < y₁ - Y := by linarith
  have hB₁ : 0 < y₁ ^ 2 - Y ^ 2 := by nlinarith
  have hA : y₁ - Y ≤ y - η := by linarith
  have hB : y₁ ^ 2 - Y ^ 2 ≤ y ^ 2 - η ^ 2 := by nlinarith
  have hApos : 0 < y - η := by linarith
  have hBpos : 0 < y ^ 2 - η ^ 2 := by linarith
  have hy0 : 0 < y := by linarith
  have hyb : y / (y ^ 2 - η ^ 2) ≤ y₁ / (y₁ ^ 2 - Y ^ 2) := by
    rw [div_le_div_iff₀ hBpos hB₁]
    nlinarith [mul_nonneg (sub_nonneg.2 hy) (add_nonneg (mul_nonneg hy0.le (by linarith)) (sq_nonneg Y) : (0 : ℝ) ≤ y * y₁ + Y ^ 2),
      mul_nonneg (by linarith : (0 : ℝ) ≤ y₁) (sub_nonneg.2 hη2)]
  have hE : |y ^ 2 - 1| = y ^ 2 - 1 := abs_of_nonneg (by nlinarith)
  have hS : |y + η| = y + η := abs_of_pos (by linarith)
  have hDa : |y ^ 2 - η ^ 2| = y ^ 2 - η ^ 2 := abs_of_pos hBpos
  have hsplit : y ^ 2 - 1 ≤ (y ^ 2 - η ^ 2) + 1 / pP x := by rw [hp']; linarith
  unfold kCmp kFar
  rw [hE, hS, hDa]
  have e2 : 2 * (x * (y ^ 2 - 1) + y / c) * (y + η) / (pP x * (y ^ 2 - η ^ 2) ^ 2)
      = 2 * x * (y ^ 2 - 1) / (pP x * (y - η) * (y ^ 2 - η ^ 2))
        + 2 / (c * pP x) * (1 / (y - η)) * (y / (y ^ 2 - η ^ 2)) := by
    have : y + η ≠ 0 := by linarith
    field_simp
    ring
  have t1 : 2 * x * y / (pP x * (y ^ 2 - η ^ 2)) ≤ 2 * x * y₁ / (pP x * (y₁ ^ 2 - Y ^ 2)) := by
    have e : ∀ u v : ℝ, 2 * x * u / (pP x * v) = 2 * x / pP x * (u / v) := by intro u v; ring
    rw [e, e]
    gcongr
  have t2 : 2 * x * (y ^ 2 - 1) / (pP x * (y - η) * (y ^ 2 - η ^ 2))
      ≤ 2 * x / (pP x * (y₁ - Y)) + 2 * x / (pP x ^ 2 * (y₁ - Y) * (y₁ ^ 2 - Y ^ 2)) := by
    calc 2 * x * (y ^ 2 - 1) / (pP x * (y - η) * (y ^ 2 - η ^ 2))
        ≤ 2 * x * ((y ^ 2 - η ^ 2) + 1 / pP x) / (pP x * (y - η) * (y ^ 2 - η ^ 2)) := by
          gcongr
      _ = 2 * x / (pP x * (y - η)) + 2 * x / (pP x ^ 2 * (y - η) * (y ^ 2 - η ^ 2)) := by
          field_simp
      _ ≤ 2 * x / (pP x * (y₁ - Y)) + 2 * x / (pP x ^ 2 * (y₁ - Y) * (y₁ ^ 2 - Y ^ 2)) := by
          gcongr
  have t3 : 2 / (c * pP x) * (1 / (y - η)) * (y / (y ^ 2 - η ^ 2))
      ≤ 2 * y₁ / (c * pP x * (y₁ - Y) * (y₁ ^ 2 - Y ^ 2)) := by
    calc 2 / (c * pP x) * (1 / (y - η)) * (y / (y ^ 2 - η ^ 2))
        ≤ 2 / (c * pP x) * (1 / (y₁ - Y)) * (y₁ / (y₁ ^ 2 - Y ^ 2)) := by
          gcongr
      _ = _ := by field_simp
  rw [e2]
  linarith

/-- `Ymax` decreases on `(1, ∞)`: `Ymax x ≤ x₀/√(x₀² − 1)` for `1 < x₀ ≤ x`. -/
theorem Ymax_le_of_le {x₀ x : ℝ} (hx₀ : 1 < x₀) (h : x₀ ≤ x) :
    Cvs.L2a.OrbitGapIntegerM.Ymax x ≤ x₀ / √(x₀ ^ 2 - 1) := by
  unfold Cvs.L2a.OrbitGapIntegerM.Ymax
  have h0 : 0 < x₀ ^ 2 - 1 := by nlinarith
  have h1 : 0 < x ^ 2 - 1 := by nlinarith
  rw [div_le_div_iff₀ (Real.sqrt_pos.2 h1) (Real.sqrt_pos.2 h0)]
  refine (pow_le_pow_iff_left₀ (mul_nonneg (by linarith) (Real.sqrt_nonneg _))
    (mul_nonneg (by linarith) (Real.sqrt_nonneg _)) two_ne_zero).1 ?_
  rw [mul_pow, mul_pow, Real.sq_sqrt h0.le, Real.sq_sqrt h1.le]
  nlinarith

/-- The bottom near range is uniform in `m ≥ 3`, attained at `m = 3`. -/
theorem kNear_bot_le (m : ℕ) (hm : 3 ≤ m) {c : ℝ} (hc : 1 ≤ c) :
    kNear c m (2 / m) (Cvs.L2a.OrbitGapIntegerM.Ymax m) ≤ 9 / 10 + 2 * (3 + 2 / 3) * (2 / 3 + 3 / √8) / (8 * (5 / 9) ^ 2) := by
  have hm3 : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hY : Cvs.L2a.OrbitGapIntegerM.Ymax m ≤ 3 / √8 := by
    have := Ymax_le_of_le (x₀ := 3) (by norm_num) hm3
    norm_num at this
    exact this
  have hY0 : 0 ≤ Cvs.L2a.OrbitGapIntegerM.Ymax m := by unfold Cvs.L2a.OrbitGapIntegerM.Ymax; positivity
  have hq : 2 / (m : ℝ) ≤ 2 / 3 := by gcongr
  have hq0 : 0 < 2 / (m : ℝ) := by positivity
  have hqm : 2 / (m : ℝ) * m = 2 := by field_simp
  have hsq : 5 / 9 ≤ 1 - (2 / (m : ℝ)) ^ 2 := by nlinarith
  have hp : pP (m : ℝ) = (m : ℝ) ^ 2 - 1 := rfl
  have hp0 : 0 < (m : ℝ) ^ 2 - 1 := by nlinarith
  unfold kNear
  rw [hp]
  have t1 : 2 * m * (2 / m) / (((m : ℝ) ^ 2 - 1) * (1 - (2 / m) ^ 2)) ≤ 9 / 10 := by
    rw [div_le_iff₀ (by positivity), show 2 * (m : ℝ) * (2 / m) = 4 by field_simp; ring]
    have : (1 - (2 / (m : ℝ)) ^ 2) * m ^ 2 = m ^ 2 - 4 := by field_simp; norm_num
    nlinarith [mul_nonneg (by nlinarith : (0 : ℝ) ≤ (m : ℝ) ^ 2 - 9) (by nlinarith : (0 : ℝ) ≤ 9 * (m : ℝ) ^ 2 - 4)]
  have hA : ((m : ℝ) + 2 / m / c) / ((m : ℝ) ^ 2 - 1) ≤ (3 + 2 / 3) / 8 := by
    have : 2 / (m : ℝ) / c ≤ 2 / m := div_le_self hq0.le hc
    rw [div_le_div_iff₀ hp0 (by norm_num)]
    nlinarith
  have t2 : 2 * ((m : ℝ) + 2 / m / c) * (2 / m + Cvs.L2a.OrbitGapIntegerM.Ymax m)
        / (((m : ℝ) ^ 2 - 1) * (1 - (2 / m) ^ 2) ^ 2)
      ≤ 2 * (3 + 2 / 3) * (2 / 3 + 3 / √8) / (8 * (5 / 9) ^ 2) := by
    calc 2 * ((m : ℝ) + 2 / m / c) * (2 / m + Cvs.L2a.OrbitGapIntegerM.Ymax m)
          / (((m : ℝ) ^ 2 - 1) * (1 - (2 / m) ^ 2) ^ 2)
        = 2 * (((m : ℝ) + 2 / m / c) / ((m : ℝ) ^ 2 - 1)) * (2 / m + Cvs.L2a.OrbitGapIntegerM.Ymax m)
          * (1 / (1 - (2 / m) ^ 2) ^ 2) := by
          generalize (1 - (2 / (m : ℝ)) ^ 2) = u
          generalize (m : ℝ) ^ 2 - 1 = v
          ring
      _ ≤ 2 * ((3 + 2 / 3) / 8) * (2 / 3 + 3 / √8) * (1 / (5 / 9) ^ 2) := by
          have : 0 < c := by linarith
          gcongr
      _ = _ := by ring
  linarith

/-- The far-gap polynomial: `22Mm² ≤ 24((m² − 1)M² − m⁴)` for `2 ≤ m`, `m + 1 ≤ M`. -/
theorem far_gap_poly {m M : ℝ} (hm : 2 ≤ m) (hMm : m + 1 ≤ M) :
    22 * M * m ^ 2 ≤ 24 * ((m ^ 2 - 1) * M ^ 2 - m ^ 4) := by
  have hk0 : 0 ≤ M - m - 1 := by linarith
  have h1 : 0 ≤ (m - 2) * (26 * m ^ 2 + 30 * m + 12) :=
    mul_nonneg (by linarith) (by positivity)
  have h2 : 0 ≤ (M - m - 1) * (48 * (m ^ 2 - 1) * (m + 1) - 22 * m ^ 2) :=
    mul_nonneg hk0 (by nlinarith)
  have h3 : 0 ≤ (M - m - 1) ^ 2 * (m ^ 2 - 1) := mul_nonneg (sq_nonneg _) (by nlinarith)
  linear_combination h1 + h2 + 24 * h3

/-- The four far terms in `(p, A, B) = (m² − 1, y₁ − Y, y₁² − Y²)`, given the two lower bounds on `pA` and `pB`. -/
theorem kFar_terms_le {m M p A B c : ℝ} (hm2 : 2 ≤ m) (hM : 3 ≤ M) (hp : p = m ^ 2 - 1) (hc : 0 < c)
    (hDl : m ^ 2 - m / 2 - 1 ≤ m * (p * A)) (hFl : 22 * M ≤ 24 * (p * B)) :
    2 * m * (M / m) / (p * B) + 2 * m / (p * A) + 2 * m / (p ^ 2 * A * B) + 2 * (M / m) / (c * p * A * B)
      ≤ 84 / 11 + 40 / (11 * c) := by
  have hm0 : 0 < m := by linarith
  have hp0 : 0 < p := by rw [hp]; nlinarith
  have hPA : m / 2 ≤ p * A := by
    by_contra h
    have h' := lt_of_not_ge h
    nlinarith [mul_lt_mul_of_pos_left h' hm0]
  have hPB : 11 / 4 ≤ p * B := by linarith
  have hPA0 : 0 < p * A := by linarith
  have hPB0 : 0 < p * B := by linarith
  have hA0 : 0 < A := pos_of_mul_pos_right hPA0 hp0.le
  have hB0 : 0 < B := pos_of_mul_pos_right hPB0 hp0.le
  have t1 : 2 * m * (M / m) / (p * B) ≤ 24 / 11 := by
    rw [show 2 * m * (M / m) = 2 * M by rw [mul_assoc, mul_div_cancel₀ _ hm0.ne'], div_le_iff₀ hPB0]
    linarith
  have t2 : 2 * m / (p * A) ≤ 4 := by
    rw [div_le_iff₀ hPA0]; linarith
  have t3 : 2 * m / (p ^ 2 * A * B) ≤ 16 / 11 := by
    rw [show p ^ 2 * A * B = (p * A) * (p * B) by ring, div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul hPA hPB (by norm_num) hPA0.le]
  have t4 : 2 * (M / m) / (c * p * A * B) ≤ 40 / (11 * c) := by
    have hPA' : (m ^ 2 - m / 2 - 1) / m ≤ p * A := by rw [div_le_iff₀ hm0]; linarith
    have hnum : 0 ≤ (m ^ 2 - m / 2 - 1) / m := by
      apply div_nonneg _ hm0.le; nlinarith
    have key : 22 * (M / m) * p ≤ 40 * ((p * A) * (p * B)) := by
      calc 22 * (M / m) * p = 22 * (M / m) * (m ^ 2 - 1) := by rw [hp]
        _ ≤ 22 * (M / m) * ((m ^ 2 - m / 2 - 1) * (5 / 3)) := by
            have : 0 ≤ 22 * (M / m) := by positivity
            gcongr
            nlinarith
        _ = 40 * (((m ^ 2 - m / 2 - 1) / m) * (11 * M / 12)) := by field_simp; ring
        _ ≤ 40 * ((p * A) * (p * B)) := by gcongr; linarith
    have key' : 22 * (M / m) ≤ 40 * (p * A * B) := by
      have : 22 * (M / m) * p ≤ 40 * (p * A * B) * p := by linarith
      exact le_of_mul_le_mul_right this hp0
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have : 40 / (11 * c) = 40 / 11 / c := by rw [div_div]
  linarith

/-- The bottom far range is uniform in `2 ≤ m ≤ M − 1`: `t₁ ≤ 24/11`, `t₂ ≤ 4`, `t₃ ≤ 16/11`, `t₄ ≤ 40/(11c)`. -/
theorem kFar_bot_le (M m : ℕ) (hm : 2 ≤ m) (hmM : m ≤ M - 1) {c : ℝ} (hc : 0 < c) :
    kFar c m ((M : ℝ) / m) (Cvs.L2a.OrbitGapIntegerM.Ymax m) ≤ 84 / 11 + 40 / (11 * c) := by
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hMm : (m : ℝ) + 1 ≤ M := by exact_mod_cast (by omega : m + 1 ≤ M)
  have hm0 : (0 : ℝ) < m := by linarith
  have hp1 : 0 < (m : ℝ) ^ 2 - 1 := by nlinarith
  obtain ⟨s, hsd⟩ : ∃ s, s = √((m : ℝ) ^ 2 - 1) := ⟨_, rfl⟩
  have hs2 : s ^ 2 = (m : ℝ) ^ 2 - 1 := by rw [hsd]; exact Real.sq_sqrt hp1.le
  have hs0 : 0 < s := by rw [hsd]; exact Real.sqrt_pos.2 hp1
  have hms : (m : ℝ) * s ≤ m ^ 2 - 1 / 2 := by
    refine (pow_le_pow_iff_left₀ (by positivity) (by nlinarith) two_ne_zero).1 ?_
    rw [mul_pow, hs2]
    nlinarith
  have hY : Cvs.L2a.OrbitGapIntegerM.Ymax (m : ℝ) = m / s := by rw [hsd]; rfl
  obtain ⟨p, hpd⟩ : ∃ p, p = pP (m : ℝ) := ⟨_, rfl⟩
  have hp : p = (m : ℝ) ^ 2 - 1 := hpd
  obtain ⟨A, hAd⟩ : ∃ A, A = (M : ℝ) / m - Cvs.L2a.OrbitGapIntegerM.Ymax m := ⟨_, rfl⟩
  obtain ⟨B, hBd⟩ : ∃ B, B = ((M : ℝ) / m) ^ 2 - Cvs.L2a.OrbitGapIntegerM.Ymax m ^ 2 := ⟨_, rfl⟩
  have hk : kFar c m ((M : ℝ) / m) (Cvs.L2a.OrbitGapIntegerM.Ymax m)
      = 2 * m * (M / m) / (p * B) + 2 * m / (p * A) + 2 * m / (p ^ 2 * A * B) + 2 * (M / m) / (c * p * A * B) := by
    unfold kFar
    rw [← hpd, ← hAd, ← hBd]
  have hpA : (m : ℝ) * (p * A) = ((m : ℝ) ^ 2 - 1) * M - m * (m * s) := by
    rw [hp, hAd, hY]
    have hss : ((m : ℝ) ^ 2 - 1) / s = s := by rw [← hs2]; field_simp
    calc (m : ℝ) * (((m : ℝ) ^ 2 - 1) * (M / m - m / s))
        = ((m : ℝ) ^ 2 - 1) * M - m * m * (((m : ℝ) ^ 2 - 1) / s) := by field_simp
      _ = _ := by rw [hss]; ring
  have hpB : (m : ℝ) ^ 2 * (p * B) = ((m : ℝ) ^ 2 - 1) * M ^ 2 - m ^ 4 := by
    rw [hp, hBd, hY, div_pow, div_pow, hs2]
    field_simp
  have hDl : (m : ℝ) ^ 2 - m / 2 - 1 ≤ m * (p * A) := by
    rw [hpA]
    nlinarith [mul_le_mul_of_nonneg_left hMm hp1.le, mul_le_mul_of_nonneg_left hms hm0.le]
  have hFl : 22 * (M : ℝ) ≤ 24 * (p * B) := by
    have key := far_gap_poly hm2 hMm
    rw [← hpB] at key
    have hm20 : (0 : ℝ) < m ^ 2 := by positivity
    have : 22 * (M : ℝ) * m ^ 2 ≤ 24 * (p * B) * m ^ 2 := by linarith
    exact le_of_mul_le_mul_right this hm20
  rw [hk]
  exact kFar_terms_le hm2 (by linarith) hp hc hDl hFl

/-- **The `t`-average**: `|∫_a^b w cos(λt)| ≤ (|w(a)| + |w(b)| + ∫_a^b |w′|)/|λ|`, one integration by parts. -/
theorem abs_integral_mul_cos_le {w w' : ℝ → ℝ} {a b lam : ℝ} (hab : a ≤ b) (hlam : lam ≠ 0)
    (hw : ∀ t ∈ uIcc a b, HasDerivAt w (w' t) t) (hw' : IntervalIntegrable w' volume a b) :
    |∫ t in a..b, w t * Real.cos (lam * t)| ≤ (|w a| + |w b| + ∫ t in a..b, |w' t|) / |lam| := by
  have hv : ∀ t ∈ uIcc a b, HasDerivAt (fun t => Real.sin (lam * t) / lam) (Real.cos (lam * t)) t := by
    intro t _
    have := (((hasDerivAt_id t).const_mul lam).sin).div_const lam
    refine this.congr_deriv ?_
    simp only [id, mul_one]
    field_simp
  have hv' : IntervalIntegrable (fun t => Real.cos (lam * t)) volume a b :=
    (Real.continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable a b
  rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul hw hv hw' hv']
  have hl : 0 < |lam| := abs_pos.2 hlam
  have hbd : ∀ (f : ℝ → ℝ) (u : ℝ), |f u * (Real.sin (lam * u) / lam)| ≤ |f u| / |lam| := by
    intro f u
    rw [abs_mul, abs_div, ← mul_div_assoc]
    gcongr
    calc |f u| * |Real.sin (lam * u)| ≤ |f u| * 1 := by gcongr; exact Real.abs_sin_le_one _
      _ = |f u| := mul_one _
  have hcs : ContinuousOn (fun t => Real.sin (lam * t) / lam) (uIcc a b) :=
    ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).div_const lam).continuousOn
  have hI : |∫ t in a..b, w' t * (Real.sin (lam * t) / lam)| ≤ (∫ t in a..b, |w' t|) / |lam| := by
    calc |∫ t in a..b, w' t * (Real.sin (lam * t) / lam)|
        ≤ ∫ t in a..b, |w' t * (Real.sin (lam * t) / lam)| :=
          intervalIntegral.abs_integral_le_integral_abs hab
      _ ≤ ∫ t in a..b, |w' t| / |lam| := by
          apply intervalIntegral.integral_mono_on hab (hw'.mul_continuousOn hcs).abs (hw'.abs.div_const _)
          intro u _
          exact hbd w' u
      _ = (∫ t in a..b, |w' t|) / |lam| := intervalIntegral.integral_div _ _
  calc |w b * (Real.sin (lam * b) / lam) - w a * (Real.sin (lam * a) / lam)
        - ∫ t in a..b, w' t * (Real.sin (lam * t) / lam)|
      ≤ |w b * (Real.sin (lam * b) / lam) - w a * (Real.sin (lam * a) / lam)|
        + |∫ t in a..b, w' t * (Real.sin (lam * t) / lam)| := abs_sub _ _
    _ ≤ |w b * (Real.sin (lam * b) / lam)| + |w a * (Real.sin (lam * a) / lam)|
        + |∫ t in a..b, w' t * (Real.sin (lam * t) / lam)| := by gcongr; exact abs_sub _ _
    _ ≤ |w b| / |lam| + |w a| / |lam| + (∫ t in a..b, |w' t|) / |lam| := by
        gcongr
        · exact hbd w b
        · exact hbd w a
    _ = _ := by ring

/-- The sample difference: `|S[μ] − S[ν]| ≤ (|μ(k) − ν(k)| + |μ(−k) − ν(−k)|)R/2`. -/
theorem norm_smp_sub_le {μ ν : ℝ → ℂ} {c χ x : ℝ} {g : ℝ → ℝ} (hx : 1 < x) (hc : 0 < c) (hχc : χ < c ^ 2) :
    ‖Cvs.L2a.BandTransferBandForm.smp μ c χ g x - Cvs.L2a.BandTransferBandForm.smp ν c χ g x‖
      ≤ (‖μ (kP c χ x) - ν (kP c χ x)‖ + ‖μ (-kP c χ x) - ν (-kP c χ x)‖)
        * (Cvs.Prolate.Envelope.RungCountEnvelope.rungAmp c χ g x / 2) := by
  have h1 : ‖psiP c χ g x‖ = Cvs.Prolate.Envelope.RungCountEnvelope.rungAmp c χ g x / 2 := norm_psiP hx hc hχc
  have h2 : ‖conj (psiP c χ g x)‖ = Cvs.Prolate.Envelope.RungCountEnvelope.rungAmp c χ g x / 2 := by
    rw [RCLike.norm_conj, h1]
  unfold Cvs.L2a.BandTransferBandForm.smp
  calc ‖μ (kP c χ x) * psiP c χ g x + μ (-kP c χ x) * conj (psiP c χ g x)
        - (ν (kP c χ x) * psiP c χ g x + ν (-kP c χ x) * conj (psiP c χ g x))‖
      = ‖(μ (kP c χ x) - ν (kP c χ x)) * psiP c χ g x
          + (μ (-kP c χ x) - ν (-kP c χ x)) * conj (psiP c χ g x)‖ := by congr 1; ring
    _ ≤ ‖(μ (kP c χ x) - ν (kP c χ x)) * psiP c χ g x‖
          + ‖(μ (-kP c χ x) - ν (-kP c χ x)) * conj (psiP c χ g x)‖ := norm_add_le _ _
    _ = _ := by rw [norm_mul, norm_mul, h1, h2]; ring

end Cvs.L2a.CutKernelSimplified
