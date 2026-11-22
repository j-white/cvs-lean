import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Cvs.Prolate.Mellin.FrozenRiccatiRoot
import Cvs.Prolate.Mellin.FrozenRootLogIntegral

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The local residual of the frozen root and the cubic lattice sum

For `Re p ≥ 1`, `|p| ≥ 4c`, `c ≥ 10`, `|χ| ≤ c²`, with `a = 1 − χ/(p(p − 1))`, `b = c²/((p − 1)(p + 2))`,
`σ = σ(p^{−2})`, `σ₊ = σ((p + 2)^{−2})`: `|aσ₊ + b − σσ₊| ≤ (9/2)c²/|p|³`, `|b| ≤ (40/39)c²/|p|²` and `|σ|, |σ₊| ≥ 3/4`.
On the lattice `p_m = τ + 2m − ig`, `τ ≥ −1/2`, the arctan telescope gives `Σ_{m ≤ N} 1/|p_m|³ ≤ (3π/8)/g²`.
-/

noncomputable section

open Real Set Complex Filter Topology
open Cvs.Prolate.Mellin.FrozenRiccatiRoot (sig hh sig_sq norm_sig_sub_one_le norm_sig_sub_le)

namespace Cvs.Prolate.Mellin.FrozenRootResidual

/-- The lattice point `p_m = (τ + 2m) − ig`. -/
def pm (τ g : ℝ) (m : ℕ) : ℂ := ((τ + 2 * m : ℝ) : ℂ) + ((-g : ℝ) : ℂ) * I

/-- `a(p) = 1 − χ/(p(p − 1))`. -/
def aR (χ : ℝ) (p : ℂ) : ℂ := 1 - χ / (p * (p - 1))

/-- `b(p) = c²/((p − 1)(p + 2))`. -/
def bR (c : ℝ) (p : ℂ) : ℂ := c ^ 2 / ((p - 1) * (p + 2))

/-- `|p + t| ≥ |p|` for `Re p ≥ 0`, `t ≥ 0`. -/
theorem norm_le_norm_add {p : ℂ} (hp : 0 ≤ p.re) {t : ℝ} (ht : 0 ≤ t) : ‖p‖ ≤ ‖p + t‖ := by
  have h1 : ‖p‖ ^ 2 ≤ ‖p + t‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, normSq_apply, normSq_apply]
    simp only [add_re, ofReal_re, add_im, ofReal_im, add_zero]
    nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) (by norm_num)).1 h1

theorem c_sq_w_le {c : ℝ} {q : ℂ} (hc : 0 < c) (hq : 4 * c ≤ ‖q‖) : c ^ 2 * ‖(q ^ 2)⁻¹‖ ≤ 1 / 16 := by
  have hq0 : 0 < ‖q‖ := by linarith
  rw [Cvs.Prolate.Mellin.FrozenRootLogIntegral.c_sq_norm_inv, div_le_iff₀ (by positivity)]; nlinarith

/-- `3/4 ≤ |σ(q^{−2})| ≤ 5/4` for `|q| ≥ 4c`. -/
theorem norm_sig_bounds {χ c : ℝ} (hc : 0 < c) (hχ : |χ| ≤ c ^ 2) {q : ℂ} (hq : 4 * c ≤ ‖q‖) :
    3 / 4 ≤ ‖sig χ c ((q ^ 2)⁻¹)‖ ∧ ‖sig χ c ((q ^ 2)⁻¹)‖ ≤ 5 / 4 := by
  have hw := c_sq_w_le hc hq
  have h := norm_sig_sub_one_le hχ (w := (q ^ 2)⁻¹) (by linarith)
  have h1 := norm_sub_norm_le (sig χ c ((q ^ 2)⁻¹)) 1
  have h2 := norm_sub_norm_le 1 (sig χ c ((q ^ 2)⁻¹))
  rw [norm_one] at h1 h2
  rw [norm_sub_rev] at h2
  constructor <;> linarith

/-- `|q^{−2} − p^{−2}| ≤ t(2|p| + t)/|p|⁴` for `q = p + t`, `Re p ≥ 0`, `t ≥ 0`. -/
theorem norm_w_sub_le {p : ℂ} (hp : 0 ≤ p.re) (hp0 : p ≠ 0) {t : ℝ} (ht : 0 ≤ t) :
    ‖((p + t) ^ 2)⁻¹ - (p ^ 2)⁻¹‖ ≤ t * (2 * ‖p‖ + t) / ‖p‖ ^ 4 := by
  have hpt := norm_le_norm_add hp ht
  have hP : 0 < ‖p‖ := norm_pos_iff.2 hp0
  have hq0 : p + t ≠ 0 := fun h => by rw [h, norm_zero] at hpt; linarith
  have e : ((p + t) ^ 2)⁻¹ - (p ^ 2)⁻¹ = -(t * (2 * p + t)) / (p ^ 2 * (p + t) ^ 2) := by
    field_simp; ring
  rw [e, norm_div, norm_neg, norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ht]
  have hnum : ‖2 * p + (t : ℂ)‖ ≤ 2 * ‖p‖ + t := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht]
  have hden : ‖p‖ ^ 4 ≤ ‖p‖ ^ 2 * ‖p + t‖ ^ 2 := by
    have := pow_le_pow_left₀ hP.le hpt 2
    nlinarith [pow_pos hP 2]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h4 : 0 < ‖p‖ ^ 4 := by positivity
  calc t * ‖2 * p + (t : ℂ)‖ * ‖p‖ ^ 4 ≤ t * (2 * ‖p‖ + t) * ‖p‖ ^ 4 := by gcongr
    _ ≤ t * (2 * ‖p‖ + t) * (‖p‖ ^ 2 * ‖p + ↑t‖ ^ 2) := by gcongr

/-- **The local residual of the frozen root**: for `Re p ≥ 1`, `|p| ≥ 4c`, `c ≥ 10`, `|χ| ≤ c²`,
`|aσ₊ + b − σσ₊| ≤ (9/2)c²/|p|³`. -/
theorem norm_residual_le {χ c : ℝ} (hc : 10 ≤ c) (hχ : |χ| ≤ c ^ 2) {p : ℂ} (hp : 1 ≤ p.re)
    (hpc : 4 * c ≤ ‖p‖) :
    ‖aR χ p * sig χ c (((p + 2) ^ 2)⁻¹) + bR c p - sig χ c ((p ^ 2)⁻¹) * sig χ c (((p + 2) ^ 2)⁻¹)‖
      ≤ 9 / 2 * c ^ 2 / ‖p‖ ^ 3 := by
  have hc0 : 0 < c := by linarith
  set P := ‖p‖ with hPd
  have hP40 : 40 ≤ P := by linarith
  have hP0 : 0 < P := by linarith
  have hp0 : p ≠ 0 := norm_pos_iff.1 hP0
  have hp2 : P ≤ ‖p + 2‖ := by
    have := norm_le_norm_add (p := p) (by linarith) (t := 2) (by norm_num); simpa using this
  have hp1 : P - 1 ≤ ‖p - 1‖ := by
    have := norm_sub_norm_le p 1; rw [norm_one] at this; linarith
  have hpm1 : p - 1 ≠ 0 := fun h => by rw [h, norm_zero] at hp1; linarith
  have hpp2 : p + 2 ≠ 0 := fun h => by rw [h, norm_zero] at hp2; linarith
  have hcw : c ^ 2 * ‖(p ^ 2)⁻¹‖ ≤ 1 / 16 := c_sq_w_le hc0 hpc
  have hcwq : c ^ 2 * ‖((p + 2) ^ 2)⁻¹‖ ≤ 1 / 16 := c_sq_w_le hc0 (hpc.trans hp2)
  obtain ⟨hs1, hs2⟩ := norm_sig_bounds hc0 hχ hpc
  obtain ⟨hsq1, hsq2⟩ := norm_sig_bounds hc0 hχ (hpc.trans hp2)
  set w := (p ^ 2)⁻¹ with hwd
  set wq := ((p + 2) ^ 2)⁻¹ with hwqd
  set s := sig χ c w with hsd
  set sq := sig χ c wq with hsqd
  -- the decomposition
  have hfix : s ^ 2 = (1 - χ * w) * s + c ^ 2 * w := sig_sq χ c w
  have hs0 : s ≠ 0 := fun h => by rw [h, norm_zero] at hs1; linarith
  have hdec : aR χ p * sq + bR c p - s * sq = (aR χ p - (1 - χ * w)) * sq + (bR c p - c ^ 2 * w)
      + (sq - s) * ((1 - χ * w) - s) := by
    linear_combination -hfix
  have hah : (1 - χ * w) - s = -(c ^ 2 * w) / s := by
    rw [eq_div_iff hs0]
    linear_combination -hfix
  rw [hdec, hah]
  have hw : ‖w‖ = 1 / P ^ 2 := by rw [hwd, norm_inv, norm_pow, one_div]
  -- the three terms
  have t1 : ‖(aR χ p - (1 - χ * w)) * sq‖ ≤ 50 / 39 * c ^ 2 / P ^ 3 := by
    have e : aR χ p - (1 - χ * w) = -(χ / (p ^ 2 * (p - 1))) := by
      unfold aR; rw [hwd]; field_simp; ring
    rw [e, norm_mul, norm_neg, norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    have hP1 : 0 < P ^ 2 * (P - 1) := by nlinarith
    have h1 : |χ| / (P ^ 2 * ‖p - 1‖) ≤ c ^ 2 / (P ^ 2 * (P - 1)) :=
      div_le_div₀ (sq_nonneg c) hχ hP1 (mul_le_mul_of_nonneg_left hp1 (sq_nonneg P))
    calc |χ| / (P ^ 2 * ‖p - 1‖) * ‖sq‖ ≤ c ^ 2 / (P ^ 2 * (P - 1)) * (5 / 4) :=
          mul_le_mul h1 hsq2 (norm_nonneg _) (by positivity)
      _ ≤ 50 / 39 * c ^ 2 / P ^ 3 := by
          rw [div_mul_eq_mul_div, div_le_div_iff₀ hP1 (by positivity)]
          have : (5 / 4) * P ≤ 50 / 39 * (P - 1) := by nlinarith
          have hc2 : 0 ≤ c ^ 2 := sq_nonneg c
          nlinarith [mul_le_mul_of_nonneg_left this (mul_nonneg hc2 (sq_nonneg P))]
  have t2 : ‖bR c p - c ^ 2 * w‖ ≤ 42 / 39 * c ^ 2 / P ^ 3 := by
    have e : bR c p - c ^ 2 * w = c ^ 2 * (2 - p) / (p ^ 2 * ((p - 1) * (p + 2))) := by
      unfold bR; rw [hwd]; field_simp; ring
    rw [e, norm_div, norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      sq_abs]
    have hn : ‖(2 : ℂ) - p‖ ≤ P + 2 := by
      refine (norm_sub_le _ _).trans ?_; rw [Complex.norm_ofNat]; linarith
    have hd0 : 0 < P ^ 2 * ((P - 1) * P) := by
      have : 0 < P - 1 := by linarith
      positivity
    have hd : P ^ 2 * ((P - 1) * P) ≤ P ^ 2 * (‖p - 1‖ * ‖p + 2‖) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hp1 hp2 hP0.le (norm_nonneg _)) (sq_nonneg P)
    calc c ^ 2 * ‖(2 : ℂ) - p‖ / (P ^ 2 * (‖p - 1‖ * ‖p + 2‖)) ≤ c ^ 2 * (P + 2) / (P ^ 2 * ((P - 1) * P)) :=
          div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hn (sq_nonneg c)) hd0 hd
      _ ≤ 42 / 39 * c ^ 2 / P ^ 3 := by
          rw [div_le_div_iff₀ hd0 (by positivity)]
          have : (P + 2) ≤ 42 / 39 * (P - 1) := by nlinarith
          have hc2 : 0 ≤ c ^ 2 := sq_nonneg c
          nlinarith [mul_le_mul_of_nonneg_left this (mul_nonneg hc2 (pow_nonneg hP0.le 3))]
  have t3 : ‖(sq - s) * (-(c ^ 2 * w) / s)‖ ≤ 41 / 20 * c ^ 2 / P ^ 3 := by
    have hlip := norm_sig_sub_le hχ hcwq hcw
    have hws := norm_w_sub_le (p := p) (by linarith) hp0 (t := 2) (by norm_num)
    push_cast at hws
    rw [← hwqd, ← hwd] at hws
    rw [norm_mul, norm_div, norm_neg, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, hw]
    have hA : ‖sq - s‖ ≤ 6 * c ^ 2 * (2 * (2 * P + 2) / P ^ 4) := hlip.trans (by gcongr)
    have hB : c ^ 2 * (1 / P ^ 2) / ‖s‖ ≤ 4 / 3 * (c ^ 2 / P ^ 2) := by
      calc c ^ 2 * (1 / P ^ 2) / ‖s‖ ≤ c ^ 2 * (1 / P ^ 2) / (3 / 4) :=
            div_le_div_of_nonneg_left (by positivity) (by norm_num) hs1
        _ = 4 / 3 * (c ^ 2 / P ^ 2) := by ring
    have hc16 : 16 * c ^ 2 ≤ P ^ 2 := by nlinarith
    have key : 32 * c ^ 2 * (P + 1) / P ^ 3 ≤ 41 / 20 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_right hc16 (by linarith : (0 : ℝ) ≤ 2 * (P + 1))]
    calc ‖sq - s‖ * (c ^ 2 * (1 / P ^ 2) / ‖s‖)
        ≤ 6 * c ^ 2 * (2 * (2 * P + 2) / P ^ 4) * (4 / 3 * (c ^ 2 / P ^ 2)) :=
          mul_le_mul hA hB (by positivity) (by positivity)
      _ = c ^ 2 / P ^ 3 * (32 * c ^ 2 * (P + 1) / P ^ 3) := by field_simp; ring
      _ ≤ c ^ 2 / P ^ 3 * (41 / 20) := mul_le_mul_of_nonneg_left key (by positivity)
      _ = 41 / 20 * c ^ 2 / P ^ 3 := by ring
  have hsum : 50 / 39 * c ^ 2 / P ^ 3 + 42 / 39 * c ^ 2 / P ^ 3 + 41 / 20 * c ^ 2 / P ^ 3
      = (50 / 39 + 42 / 39 + 41 / 20) * (c ^ 2 / P ^ 3) := by ring
  have hc3 : 0 ≤ c ^ 2 / P ^ 3 := by positivity
  calc _ ≤ ‖(aR χ p - (1 - χ * w)) * sq‖ + ‖bR c p - c ^ 2 * w‖ + ‖(sq - s) * (-(c ^ 2 * w) / s)‖ :=
        norm_add₃_le
    _ ≤ 50 / 39 * c ^ 2 / P ^ 3 + 42 / 39 * c ^ 2 / P ^ 3 + 41 / 20 * c ^ 2 / P ^ 3 := by linarith
    _ ≤ 9 / 2 * c ^ 2 / P ^ 3 := by
        rw [hsum, show 9 / 2 * c ^ 2 / P ^ 3 = 9 / 2 * (c ^ 2 / P ^ 3) by ring]
        exact mul_le_mul_of_nonneg_right (by norm_num) hc3

/-- `|b(p)| ≤ (40/39)c²/|p|²` for `Re p ≥ 1`, `|p| ≥ 40`. -/
theorem norm_bR_le {c : ℝ} {p : ℂ} (hp : 1 ≤ p.re) (hP : 40 ≤ ‖p‖) : ‖bR c p‖ ≤ 40 / 39 * c ^ 2 / ‖p‖ ^ 2 := by
  set P := ‖p‖
  have hp2 : P ≤ ‖p + 2‖ := by
    have := norm_le_norm_add (p := p) (by linarith) (t := 2) (by norm_num); simpa using this
  have hp1 : P - 1 ≤ ‖p - 1‖ := by
    have := norm_sub_norm_le p 1; rw [norm_one] at this; linarith
  have hd0 : 0 < (P - 1) * P := by nlinarith
  unfold bR
  rw [norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  calc c ^ 2 / (‖p - 1‖ * ‖p + 2‖) ≤ c ^ 2 / ((P - 1) * P) :=
        div_le_div_of_nonneg_left (sq_nonneg c) hd0 (mul_le_mul hp1 hp2 (by linarith) (norm_nonneg _))
    _ ≤ 40 / 39 * c ^ 2 / P ^ 2 := by
        rw [div_le_div_iff₀ hd0 (by positivity)]
        have : P ^ 2 ≤ 40 / 39 * ((P - 1) * P) := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_left this (sq_nonneg c)]

/-- **The recurrence coefficients after the frozen-root normalisation**: `|a/σ + b/(σσ₊) − 1| ≤ 8c²/|p|³` and
`|b/(σσ₊)| ≤ 3/25` for `Re p ≥ 1`, `|p| ≥ 4c`, `c ≥ 10`, `|χ| ≤ c²`. -/
theorem coeff_bounds {χ c : ℝ} (hc : 10 ≤ c) (hχ : |χ| ≤ c ^ 2) {p : ℂ} (hp : 1 ≤ p.re) (hpc : 4 * c ≤ ‖p‖) :
    ‖aR χ p / sig χ c ((p ^ 2)⁻¹) + bR c p / (sig χ c ((p ^ 2)⁻¹) * sig χ c (((p + 2) ^ 2)⁻¹)) - 1‖
        ≤ 8 * c ^ 2 / ‖p‖ ^ 3
      ∧ ‖bR c p / (sig χ c ((p ^ 2)⁻¹) * sig χ c (((p + 2) ^ 2)⁻¹))‖ ≤ 3 / 25 := by
  have hc0 : 0 < c := by linarith
  have hP40 : 40 ≤ ‖p‖ := by linarith
  have hp2 : ‖p‖ ≤ ‖p + 2‖ := by
    have := norm_le_norm_add (p := p) (by linarith) (t := 2) (by norm_num); simpa using this
  obtain ⟨hs1, -⟩ := norm_sig_bounds hc0 hχ hpc
  obtain ⟨hsq1, -⟩ := norm_sig_bounds hc0 hχ (hpc.trans hp2)
  set s := sig χ c ((p ^ 2)⁻¹)
  set sq := sig χ c (((p + 2) ^ 2)⁻¹)
  have hs0 : s ≠ 0 := fun h => by rw [h, norm_zero] at hs1; linarith
  have hsq0 : sq ≠ 0 := fun h => by rw [h, norm_zero] at hsq1; linarith
  have hprod : 9 / 16 ≤ ‖s * sq‖ := by rw [norm_mul]; nlinarith
  have hres := norm_residual_le hc hχ hp hpc
  constructor
  · have e : aR χ p / s + bR c p / (s * sq) - 1 = (aR χ p * sq + bR c p - s * sq) / (s * sq) := by
      field_simp
    rw [e, norm_div]
    calc ‖aR χ p * sq + bR c p - s * sq‖ / ‖s * sq‖ ≤ 9 / 2 * c ^ 2 / ‖p‖ ^ 3 / (9 / 16) :=
          div_le_div₀ (by positivity) hres (by norm_num) hprod
      _ = 8 * c ^ 2 / ‖p‖ ^ 3 := by ring
  · rw [norm_div]
    have hb := norm_bR_le (c := c) hp hP40
    have hP2 : 16 * c ^ 2 ≤ ‖p‖ ^ 2 := by nlinarith
    calc ‖bR c p‖ / ‖s * sq‖ ≤ 40 / 39 * c ^ 2 / ‖p‖ ^ 2 / (9 / 16) :=
          div_le_div₀ (by positivity) hb (by norm_num) hprod
      _ ≤ 3 / 25 := by
          rw [div_div, div_le_iff₀ (by positivity)]
          nlinarith

/-- `1/(x² + g²) ≤ (arctan(x/g) − arctan((x − 2)/g))/(2g)` for `x ≥ 1`, `g > 0`. -/
theorem inv_sq_add_le_arctan {x g : ℝ} (hx : 1 ≤ x) (hg : 0 < g) :
    1 / (x ^ 2 + g ^ 2) ≤ (arctan (x / g) - arctan ((x - 2) / g)) / (2 * g) := by
  have hd : ∀ t, HasDerivAt (fun t : ℝ => arctan (t / g)) (1 / (1 + (t / g) ^ 2) * (1 / g)) t := fun t => by
    exact (hasDerivAt_arctan (t / g)).comp t ((hasDerivAt_id t).div_const g)
  obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope (fun t : ℝ => arctan (t / g))
    (fun t => 1 / (1 + (t / g) ^ 2) * (1 / g)) (by linarith : x - 2 < x)
    (by fun_prop) (fun t _ => hd t)
  have hξ2 : ξ ^ 2 ≤ x ^ 2 := by
    have h1 := hξ.1; have h2 := hξ.2
    nlinarith
  have hlow : g / (x ^ 2 + g ^ 2) ≤ 1 / (1 + (ξ / g) ^ 2) * (1 / g) := by
    rw [show 1 / (1 + (ξ / g) ^ 2) * (1 / g) = g / (ξ ^ 2 + g ^ 2) by field_simp; ring]
    exact div_le_div_of_nonneg_left hg.le (by positivity) (by linarith)
  rw [hslope, show x - (x - 2) = 2 by ring] at hlow
  rw [le_div_iff₀ (by positivity)]
  have : g / (x ^ 2 + g ^ 2) = 1 / (x ^ 2 + g ^ 2) * g := by ring
  rw [this] at hlow
  linarith

/-- **The cubic lattice sum**: `Σ_{m < N} 1/|p_{m+1}|³ ≤ (3π/8)/g²` for `τ ≥ −1/2`, `g ≥ 1`. -/
theorem sum_inv_norm_cube_le {τ g : ℝ} (hτ : -1 / 2 ≤ τ) (hg : 1 ≤ g) (N : ℕ) :
    ∑ m ∈ Finset.range N, 1 / ‖pm τ g (m + 1)‖ ^ 3 ≤ 3 * π / 8 / g ^ 2 := by
  have hg0 : 0 < g := by linarith
  have hterm : ∀ m : ℕ, 1 / ‖pm τ g (m + 1)‖ ^ 3
      ≤ (arctan ((τ + 2 * ((m + 1 : ℕ) : ℝ)) / g) - arctan ((τ + 2 * (m : ℝ)) / g)) / (2 * g) / g := by
    intro m
    set x := τ + 2 * ((m + 1 : ℕ) : ℝ) with hx
    have hx1 : 1 ≤ x := by rw [hx]; push_cast; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    have hn : ‖pm τ g (m + 1)‖ ^ 2 = x ^ 2 + g ^ 2 := Cvs.Prolate.Mellin.FrozenRootLogIntegral.norm_line _ _
    have hng : g ≤ ‖pm τ g (m + 1)‖ := Cvs.Prolate.Mellin.FrozenRootLogIntegral.le_norm_line
    have h3 : g * (x ^ 2 + g ^ 2) ≤ ‖pm τ g (m + 1)‖ ^ 3 := by
      rw [show ‖pm τ g (m + 1)‖ ^ 3 = ‖pm τ g (m + 1)‖ ^ 2 * ‖pm τ g (m + 1)‖ by ring, hn, mul_comm]
      exact mul_le_mul_of_nonneg_left hng (by positivity)
    have ha := inv_sq_add_le_arctan hx1 hg0
    have hx2 : x - 2 = τ + 2 * (m : ℝ) := by rw [hx]; push_cast; ring
    rw [hx2] at ha
    calc 1 / ‖pm τ g (m + 1)‖ ^ 3 ≤ 1 / (g * (x ^ 2 + g ^ 2)) :=
          div_le_div_of_nonneg_left zero_le_one (by positivity) h3
      _ = 1 / (x ^ 2 + g ^ 2) / g := by field_simp
      _ ≤ _ := div_le_div_of_nonneg_right ha hg0.le
  refine (Finset.sum_le_sum fun m _ => hterm m).trans ?_
  rw [← Finset.sum_div, ← Finset.sum_div]
  have htel := Finset.sum_range_sub (fun m : ℕ => arctan ((τ + 2 * (m : ℝ)) / g)) N
  have e : ∀ m : ℕ, ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := fun m => by push_cast; ring
  simp only [e] at htel ⊢
  rw [htel]
  have h1 := arctan_lt_pi_div_two ((τ + 2 * (N : ℝ)) / g)
  have h2 : -(π / 4) ≤ arctan ((τ + 2 * ((0 : ℕ) : ℝ)) / g) := by
    rw [← arctan_one, ← arctan_neg]
    refine arctan_strictMono.monotone ?_
    rw [le_div_iff₀ hg0]; push_cast; linarith
  rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have hpi := Real.pi_pos
  nlinarith

end Cvs.Prolate.Mellin.FrozenRootResidual

end
