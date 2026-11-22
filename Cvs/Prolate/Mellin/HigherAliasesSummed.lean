import Mathlib
import Cvs.Prolate.Mellin.AliasAboveBandEdges

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The aliases above the first, summed, from bounds outside the unit circle

For an even entire `H` with `|H(v)| ≤ P e^{c|Im v|}` and `|H′(v)| ≤ (|v| + 1)P′e^{c|Im v|}` on `|v| ≥ 1`, the rectangle
of height `1` bounds the aliases `W_n(ζ) = ∫_{−1}^{1} H(tζ) cos(cnt) dt`, `n ≥ 2`, `|ζ| = 1`, by
`Σ_{n ≥ 2} |W_n(ζ)| ≤ e^{c|Im ζ|}(2Pe^{−c}/(1 − e^{−c}) + 6P′y₀/c + (2P/c) log(1/y₀))` for every `y₀ ∈ (0, 1]`.
-/

noncomputable section

open Real Set MeasureTheory Filter Complex Topology

namespace Cvs.Prolate.Mellin.HigherAliasesSummed

variable {H : ℂ → ℂ} {c P P' : ℝ}

/-- For even `φ`, `∫_{−1}^{1} φ(t) cos(at) = ∫_{−1}^{1} φ(t) e^{iat}`. -/
theorem integral_cos_eq_exp {φ : ℂ → ℂ} (hφ : Continuous φ) (heven : ∀ t, φ (-t) = φ t) (a : ℝ) :
    ∫ t in (-1 : ℝ)..1, φ t * Complex.cos (a * t) = ∫ t in (-1 : ℝ)..1, φ t * Complex.exp (I * a * t) := by
  have hneg : ∫ t in (-1 : ℝ)..1, φ t * Complex.exp (-(I * a * t))
      = ∫ t in (-1 : ℝ)..1, φ t * Complex.exp (I * a * t) := by
    have := intervalIntegral.integral_comp_neg (a := (-1 : ℝ)) (b := 1)
      (fun t : ℝ => φ t * Complex.exp (I * a * t))
    simp only [neg_neg, ofReal_neg, heven] at this
    rw [← this]
    refine intervalIntegral.integral_congr fun t _ => ?_
    congr 2; ring
  have hi1 : IntervalIntegrable (fun t : ℝ => φ t * Complex.exp (I * a * t)) volume (-1) 1 :=
    (by fun_prop : Continuous fun t : ℝ => φ t * Complex.exp (I * a * t)).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun t : ℝ => φ t * Complex.exp (-(I * a * t))) volume (-1) 1 :=
    (by fun_prop : Continuous fun t : ℝ => φ t * Complex.exp (-(I * a * t))).intervalIntegrable _ _
  have e : (fun t : ℝ => φ t * Complex.cos (a * t))
      = fun t : ℝ => (φ t * Complex.exp (I * a * t) + φ t * Complex.exp (-(I * a * t))) / 2 := by
    funext t; rw [Complex.cos]; ring_nf
  rw [e, intervalIntegral.integral_div, intervalIntegral.integral_add hi1 hi2, hneg]
  ring

/-- `|Im((x + iy)ζ)| ≤ |x||Im ζ| + |y|` for `|ζ| = 1`. -/
theorem abs_im_mul_le {ζ : ℂ} (hζ : ‖ζ‖ = 1) (x y : ℝ) :
    |(((x : ℂ) + y * I) * ζ).im| ≤ |x| * |ζ.im| + |y| := by
  have h1 : (((x : ℂ) + y * I) * ζ).im = x * ζ.im + y * ζ.re := by
    simp only [mul_im, add_re, add_im, ofReal_re, ofReal_im, mul_re, I_re, I_im]; ring
  have h2 : |ζ.re| ≤ 1 := hζ ▸ Complex.abs_re_le_norm ζ
  rw [h1]
  calc |x * ζ.im + y * ζ.re| ≤ |x| * |ζ.im| + |y| * |ζ.re| := by
        rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ |x| * |ζ.im| + |y| * 1 := by gcongr
    _ = _ := by ring

theorem norm_mul_unit {ζ : ℂ} (hζ : ‖ζ‖ = 1) (z : ℂ) : ‖z * ζ‖ = ‖z‖ := by rw [norm_mul, hζ, mul_one]

theorem one_le_norm_add_I (x y : ℝ) (h : 1 ≤ |y|) : 1 ≤ ‖(x : ℂ) + y * I‖ :=
  calc (1 : ℝ) ≤ |y| := h
    _ = |((x : ℂ) + y * I).im| := by simp
    _ ≤ _ := Complex.abs_im_le_norm _

theorem one_le_norm_one_add (y : ℝ) : 1 ≤ ‖(1 : ℂ) + y * I‖ :=
  calc (1 : ℝ) = |((1 : ℂ) + y * I).re| := by simp
    _ ≤ _ := Complex.abs_re_le_norm _

/-- **The top of the rectangle**: `‖∫_{−1}^{1} H((x + i)ζ)e^{ia(x + i)}‖ ≤ 2Pe^{c(|Im ζ| + 1)}e^{−a}`. -/
theorem norm_top_le (hP : ∀ v : ℂ, 1 ≤ ‖v‖ → ‖H v‖ ≤ P * Real.exp (c * |v.im|))
    (hc : 0 ≤ c) {ζ : ℂ} (hζ : ‖ζ‖ = 1) (a : ℝ) :
    ‖∫ x in (-1 : ℝ)..1, H ((x + (1 : ℝ) * I) * ζ) * Complex.exp (I * a * ((x : ℂ) + (1 : ℝ) * I))‖
      ≤ 2 * (P * Real.exp (c * (|ζ.im| + 1)) * Real.exp (-a)) := by
  have hb : ∀ x ∈ Set.uIoc (-1 : ℝ) 1, ‖H ((x + (1 : ℝ) * I) * ζ) * Complex.exp (I * a * ((x : ℂ) + (1 : ℝ) * I))‖
      ≤ P * Real.exp (c * (|ζ.im| + 1)) * Real.exp (-a) := by
    intro x hx
    rw [uIoc_of_le (by norm_num)] at hx
    have hx1 : |x| ≤ 1 := abs_le.2 ⟨by linarith [hx.1], hx.2⟩
    rw [norm_mul, Cvs.Prolate.Mellin.AliasAboveBandEdges.norm_exp_top, mul_one]
    have hv : 1 ≤ ‖((x : ℂ) + (1 : ℝ) * I) * ζ‖ := by
      rw [norm_mul_unit hζ]; exact one_le_norm_add_I x 1 (by simp)
    have h1 := hP _ hv
    have h2 := abs_im_mul_le hζ x 1
    have hP0 : 0 ≤ P := by
      have := (norm_nonneg _).trans h1; exact nonneg_of_mul_nonneg_left this (Real.exp_pos _)
    gcongr
    refine h1.trans ?_
    gcongr
    calc |(((x : ℂ) + (1 : ℝ) * I) * ζ).im| ≤ |x| * |ζ.im| + |(1 : ℝ)| := h2
      _ ≤ 1 * |ζ.im| + 1 := by rw [abs_one]; gcongr
      _ = |ζ.im| + 1 := by ring
  have := intervalIntegral.norm_integral_le_of_norm_le_const hb
  calc _ ≤ P * Real.exp (c * (|ζ.im| + 1)) * Real.exp (-a) * |1 - (-1 : ℝ)| := this
    _ = _ := by norm_num; ring

/-- The edge difference `D(y) = H((−1 + iy)ζ) − H((1 + iy)ζ)` at most `2Pe^{c(|Im ζ| + y)}`. -/
theorem norm_side_le (hP : ∀ v : ℂ, 1 ≤ ‖v‖ → ‖H v‖ ≤ P * Real.exp (c * |v.im|)) (hc : 0 ≤ c) {ζ : ℂ}
    (hζ : ‖ζ‖ = 1) {y : ℝ} (hy : 0 ≤ y) :
    ‖H ((-1 + y * I) * ζ) - H ((1 + y * I) * ζ)‖ ≤ 2 * (P * Real.exp (c * (|ζ.im| + y))) := by
  have b : ∀ x : ℝ, |x| = 1 → ‖H ((x + y * I) * ζ)‖ ≤ P * Real.exp (c * (|ζ.im| + y)) := fun x hx => by
    have hv : 1 ≤ ‖((x : ℂ) + y * I) * ζ‖ := by
      rw [norm_mul_unit hζ]
      calc (1 : ℝ) = |((x : ℂ) + y * I).re| := by simp [hx]
        _ ≤ _ := Complex.abs_re_le_norm _
    have h1 := hP _ hv
    have h2 := abs_im_mul_le hζ x y
    rw [hx, abs_of_nonneg hy, one_mul] at h2
    have hP0 : 0 ≤ P := nonneg_of_mul_nonneg_left ((norm_nonneg _).trans h1) (Real.exp_pos _)
    exact h1.trans (by gcongr)
  have h1 := b (-1) (by simp)
  have h2 := b 1 (by simp)
  push_cast at h1 h2
  calc _ ≤ ‖H ((-1 + y * I) * ζ)‖ + ‖H ((1 + y * I) * ζ)‖ := norm_sub_le _ _
    _ ≤ _ := by linarith

/-- The edge difference at most `6yP′e^{c(|Im ζ| + y)}` for `0 ≤ y ≤ 1`, by the derivative along `(1 + iτ)ζ`. -/
theorem norm_side_le_deriv (hH : Differentiable ℂ H) (heven : ∀ v, H (-v) = H v)
    (hP' : ∀ v : ℂ, 1 ≤ ‖v‖ → ‖deriv H v‖ ≤ (‖v‖ + 1) * P' * Real.exp (c * |v.im|)) (hc : 0 ≤ c) {ζ : ℂ}
    (hζ : ‖ζ‖ = 1) {y : ℝ} (hy : 0 ≤ y) (hy1 : y ≤ 1) :
    ‖H ((-1 + y * I) * ζ) - H ((1 + y * I) * ζ)‖ ≤ 6 * y * (P' * Real.exp (c * (|ζ.im| + y))) := by
  set g : ℝ → ℂ := fun τ => H ((1 + τ * I) * ζ) with hg
  have hP'0 : 0 ≤ P' := by
    have h := hP' 1 (by simp)
    have h0 : 0 ≤ (‖(1 : ℂ)‖ + 1) * P' * Real.exp (c * |(1 : ℂ).im|) := (norm_nonneg _).trans h
    have hpos : 0 < (‖(1 : ℂ)‖ + 1) * Real.exp (c * |(1 : ℂ).im|) := by positivity
    by_contra hneg
    have := mul_neg_of_pos_of_neg hpos (not_le.1 hneg)
    nlinarith
  have hd : ∀ τ : ℝ, HasDerivAt g (deriv H ((1 + τ * I) * ζ) * (I * ζ)) τ := fun τ => by
    have h1 : HasDerivAt (fun τ : ℝ => ((1 : ℂ) + τ * I) * ζ) (I * ζ) τ := by
      have := ((hasDerivAt_id (τ : ℂ)).mul_const I).const_add 1 |>.mul_const ζ
      have h2 := this.comp_ofReal (z := τ)
      simpa using h2
    exact ((hH _).hasDerivAt).comp τ h1
  have hbound : ∀ τ ∈ Ico (-y) y, ‖deriv H ((1 + τ * I) * ζ) * (I * ζ)‖ ≤ 3 * (P' * Real.exp (c * (|ζ.im| + y))) := by
    intro τ hτ
    have hτ1 : |τ| ≤ y := abs_le.2 ⟨hτ.1, hτ.2.le⟩
    rw [norm_mul, norm_mul, Complex.norm_I, hζ, one_mul, mul_one]
    have hv : 1 ≤ ‖((1 : ℂ) + τ * I) * ζ‖ := by rw [norm_mul_unit hζ]; exact one_le_norm_one_add τ
    have hn : ‖((1 : ℂ) + τ * I) * ζ‖ ≤ 2 := by
      rw [norm_mul_unit hζ]
      calc ‖(1 : ℂ) + τ * I‖ ≤ ‖(1 : ℂ)‖ + ‖(τ : ℂ) * I‖ := norm_add_le _ _
        _ = 1 + |τ| := by simp
        _ ≤ 2 := by linarith
    have him := abs_im_mul_le hζ 1 τ
    rw [abs_one, one_mul] at him
    have h1 := hP' _ hv
    push_cast at him
    calc ‖deriv H ((1 + τ * I) * ζ)‖ ≤ (‖((1 : ℂ) + τ * I) * ζ‖ + 1) * P'
          * Real.exp (c * |(((1 : ℂ) + τ * I) * ζ).im|) := h1
      _ ≤ (2 + 1) * P' * Real.exp (c * (|ζ.im| + y)) := by
          gcongr
          exact him.trans (by linarith)
      _ = 3 * (P' * Real.exp (c * (|ζ.im| + y))) := by ring
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment' (a := -y) (b := y)
    (fun τ _ => (hd τ).hasDerivWithinAt) hbound y ⟨by linarith, le_rfl⟩
  have e1 : H ((-1 + y * I) * ζ) = g (-y) := by
    simp only [hg]
    rw [← heven]; congr 1; push_cast; ring
  have e2 : H ((1 + y * I) * ζ) = g y := rfl
  rw [e1, e2, norm_sub_rev]
  calc ‖g y - g (-y)‖ ≤ 3 * (P' * Real.exp (c * (|ζ.im| + y))) * (y - -y) := hmv
    _ = 6 * y * (P' * Real.exp (c * (|ζ.im| + y))) := by ring

/-- `Σ_{m < N} e^{−c(m + 1)y} ≤ 1/(cy)` for `c, y > 0`. -/
theorem sum_exp_le {c y : ℝ} (hc : 0 < c) (hy : 0 < y) (N : ℕ) :
    ∑ m ∈ Finset.range N, Real.exp (-(c * (m + 1) * y)) ≤ 1 / (c * y) := by
  set r := Real.exp (-(c * y)) with hr
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := by rw [hr, Real.exp_lt_one_iff]; nlinarith
  have e : ∀ m : ℕ, Real.exp (-(c * (m + 1) * y)) = r * r ^ m := fun m => by
    rw [hr, ← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring
  simp only [e, ← Finset.mul_sum]
  have hg := geom_sum_mul_neg r N
  have h1 : 0 < 1 - r := by linarith
  have hsum : ∑ m ∈ Finset.range N, r ^ m ≤ 1 / (1 - r) := by
    rw [le_div_iff₀ h1, hg]; linarith [pow_pos hr0 N]
  have hcy : 0 < c * y := mul_pos hc hy
  have hx : r * (1 + c * y) ≤ 1 := by
    have := Real.add_one_le_exp (c * y)
    rw [hr, Real.exp_neg]
    rw [inv_mul_le_iff₀ (Real.exp_pos _)]; linarith
  calc r * ∑ m ∈ Finset.range N, r ^ m ≤ r * (1 / (1 - r)) := by gcongr
    _ ≤ 1 / (c * y) := by
        rw [mul_one_div, div_le_div_iff₀ h1 hcy]; nlinarith

/-- **The aliases above the first, summed**: `Σ_{m < N} |W_{m+2}(ζ)| ≤ e^{c|Im ζ|}Ω` with
`Ω = 2Pe^{−c}/(1 − e^{−c}) + 6P′y₀/c + (2P/c) log(1/y₀)`. -/
theorem sum_norm_alias_le (hH : Differentiable ℂ H) (heven : ∀ v, H (-v) = H v)
    (hP : ∀ v : ℂ, 1 ≤ ‖v‖ → ‖H v‖ ≤ P * Real.exp (c * |v.im|))
    (hP' : ∀ v : ℂ, 1 ≤ ‖v‖ → ‖deriv H v‖ ≤ (‖v‖ + 1) * P' * Real.exp (c * |v.im|)) (hc : 0 < c)
    (hcI : ∀ n : ℕ, Complex.exp (I * (c * n : ℝ)) = 1) (hP0 : 0 ≤ P) (hP'0 : 0 ≤ P') {ζ : ℂ} (hζ : ‖ζ‖ = 1)
    {y₀ : ℝ} (hy₀ : 0 < y₀) (hy₁ : y₀ ≤ 1) (N : ℕ) :
    ∑ m ∈ Finset.range N, ‖∫ t in (-1 : ℝ)..1, H (t * ζ) * Complex.cos ((c * (m + 2) : ℝ) * t)‖
      ≤ Real.exp (c * |ζ.im|) * (2 * P * Real.exp (-c) / (1 - Real.exp (-c)) + 6 * P' * y₀ / c
        + 2 * P / c * Real.log (1 / y₀)) := by
  set θ := |ζ.im| with hθ
  set φ : ℂ → ℂ := fun t => H (t * ζ) with hφ
  have hφd : Differentiable ℂ φ := hH.comp (differentiable_id.mul_const ζ)
  have hφe : ∀ t, φ (-t) = φ t := fun t => by simp only [hφ, neg_mul, heven]
  set V : ℕ → ℝ → ℂ := fun m y => (Real.exp (-((c * (m + 2) : ℝ) * y)) : ℂ)
    * (φ (-1 + y * I) - φ (1 + y * I)) with hV
  set Tp : ℕ → ℂ := fun m => ∫ x in (-1 : ℝ)..1, φ (x + (1 : ℝ) * I)
    * Complex.exp (I * (c * (m + 2) : ℝ) * ((x : ℂ) + (1 : ℝ) * I)) with hTp
  -- each alias is a top plus a side
  have hsplit : ∀ m : ℕ, ∫ t in (-1 : ℝ)..1, H (t * ζ) * Complex.cos ((c * (m + 2) : ℝ) * t)
      = Tp m + I * ∫ y in (0 : ℝ)..1, V m y := by
    intro m
    have ha : Complex.exp (I * (c * (m + 2) : ℝ)) = 1 := by
      have := hcI (m + 2); push_cast at this ⊢; exact this
    rw [show (fun t : ℝ => H (t * ζ) * Complex.cos ((c * (m + 2) : ℝ) * t))
        = fun t : ℝ => φ t * Complex.cos ((c * (m + 2) : ℝ) * t) from rfl,
      integral_cos_eq_exp hφd.continuous hφe, Cvs.Prolate.Mellin.AliasAboveBandEdges.integral_exp_eq_rect hφd ha 1]
  -- the tops
  have htop : ∀ m : ℕ, ‖Tp m‖ ≤ 2 * (P * Real.exp (c * (θ + 1)) * Real.exp (-(c * (m + 2)))) := fun m => by
    have := norm_top_le hP hc.le hζ (c * (m + 2))
    simpa [hTp, hφ] using this
  have hsumtop : ∑ m ∈ Finset.range N, ‖Tp m‖ ≤ Real.exp (c * θ) * (2 * P * Real.exp (-c) / (1 - Real.exp (-c))) := by
    refine (Finset.sum_le_sum fun m _ => htop m).trans ?_
    set r := Real.exp (-c) with hr
    have hr0 : 0 < r := Real.exp_pos _
    have hr1 : r < 1 := by rw [hr, Real.exp_lt_one_iff]; linarith
    have e : ∀ m : ℕ, 2 * (P * Real.exp (c * (θ + 1)) * Real.exp (-(c * (m + 2))))
        = 2 * P * Real.exp (c * θ) * r * r ^ m := fun m => by
      rw [hr, ← Real.exp_nat_mul, show (2 : ℝ) * P * Real.exp (c * θ) * Real.exp (-c) * Real.exp (↑m * -c)
        = 2 * P * (Real.exp (c * θ) * Real.exp (-c) * Real.exp (↑m * -c)) by ring, ← Real.exp_add, ← Real.exp_add,
        show (2 : ℝ) * (P * Real.exp (c * (θ + 1)) * Real.exp (-(c * (↑m + 2))))
          = 2 * P * (Real.exp (c * (θ + 1)) * Real.exp (-(c * (↑m + 2)))) by ring, ← Real.exp_add]
      congr 2; ring
    simp only [e, ← Finset.mul_sum]
    have hg := geom_sum_mul_neg r N
    have h1 : 0 < 1 - r := by linarith
    have hsum : ∑ m ∈ Finset.range N, r ^ m ≤ 1 / (1 - r) := by
      rw [le_div_iff₀ h1, hg]; linarith [pow_pos hr0 N]
    calc 2 * P * Real.exp (c * θ) * r * ∑ m ∈ Finset.range N, r ^ m
        ≤ 2 * P * Real.exp (c * θ) * r * (1 / (1 - r)) := by gcongr
      _ = Real.exp (c * θ) * (2 * P * r / (1 - r)) := by ring
  -- the sides, summed under the integral
  have hVc : ∀ m : ℕ, Continuous (V m) := fun m => by
    have := hφd.continuous; simp only [hV]; fun_prop
  have hVi : ∀ m ∈ Finset.range N, IntervalIntegrable (fun y => ‖V m y‖) volume 0 1 := fun m _ =>
    ((hVc m).norm).intervalIntegrable _ _
  have hD0 : φ (-1 + (0 : ℝ) * I) - φ (1 + (0 : ℝ) * I) = 0 := by
    simp only [ofReal_zero, zero_mul, add_zero]; rw [← hφe 1]; simp
  have hpt : ∀ y : ℝ, ∑ m ∈ Finset.range N, ‖V m y‖
      = (∑ m ∈ Finset.range N, Real.exp (-(c * (m + 1) * y))) * Real.exp (-(c * y))
        * ‖φ (-1 + y * I) - φ (1 + y * I)‖ := by
    intro y
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [hV, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [← Real.exp_add]; congr 2; ring
  have hD : ∀ y : ℝ, φ (-1 + y * I) - φ (1 + y * I) = H ((-1 + y * I) * ζ) - H ((1 + y * I) * ζ) := fun y => rfl
  have hlow : ∀ y ∈ Icc (0 : ℝ) y₀, ∑ m ∈ Finset.range N, ‖V m y‖ ≤ 6 * P' * Real.exp (c * θ) / c := by
    intro y hy
    rw [hpt]
    rcases eq_or_lt_of_le hy.1 with h0 | h0
    · subst h0; rw [hD0, norm_zero, mul_zero]; positivity
    have h1 := sum_exp_le hc h0 N
    have h2 := norm_side_le_deriv hH heven hP' hc.le hζ hy.1 (hy.2.trans hy₁)
    rw [← hD] at h2
    have e : Real.exp (c * (θ + y)) * Real.exp (-(c * y)) = Real.exp (c * θ) := by
      rw [← Real.exp_add]; congr 1; ring
    calc (∑ m ∈ Finset.range N, Real.exp (-(c * (m + 1) * y))) * Real.exp (-(c * y))
          * ‖φ (-1 + y * I) - φ (1 + y * I)‖
        ≤ 1 / (c * y) * Real.exp (-(c * y)) * (6 * y * (P' * Real.exp (c * (θ + y)))) := by gcongr
      _ = 6 * P' * (Real.exp (c * (θ + y)) * Real.exp (-(c * y))) / c := by field_simp
      _ = 6 * P' * Real.exp (c * θ) / c := by rw [e]
  have hhigh : ∀ y ∈ Icc y₀ 1, ∑ m ∈ Finset.range N, ‖V m y‖ ≤ 2 * P * Real.exp (c * θ) / c * y⁻¹ := by
    intro y hy
    have hy0 : 0 < y := hy₀.trans_le hy.1
    rw [hpt]
    have h1 := sum_exp_le hc hy0 N
    have h2 := norm_side_le (H := H) hP hc.le hζ hy0.le
    rw [← hD] at h2
    have e : Real.exp (c * (θ + y)) * Real.exp (-(c * y)) = Real.exp (c * θ) := by
      rw [← Real.exp_add]; congr 1; ring
    calc (∑ m ∈ Finset.range N, Real.exp (-(c * (m + 1) * y))) * Real.exp (-(c * y))
          * ‖φ (-1 + y * I) - φ (1 + y * I)‖
        ≤ 1 / (c * y) * Real.exp (-(c * y)) * (2 * (P * Real.exp (c * (θ + y)))) := by gcongr
      _ = 2 * P * (Real.exp (c * (θ + y)) * Real.exp (-(c * y))) / c * y⁻¹ := by field_simp
      _ = 2 * P * Real.exp (c * θ) / c * y⁻¹ := by rw [e]
  have hSi : IntervalIntegrable (fun y => ∑ m ∈ Finset.range N, ‖V m y‖) volume 0 1 :=
    (continuous_finsetSum _ fun m _ => (hVc m).norm).intervalIntegrable _ _
  have hint : ∫ y in (0 : ℝ)..1, ∑ m ∈ Finset.range N, ‖V m y‖
      ≤ 6 * P' * Real.exp (c * θ) / c * y₀ + 2 * P * Real.exp (c * θ) / c * Real.log (1 / y₀) := by
    have hSc : Continuous fun y => ∑ m ∈ Finset.range N, ‖V m y‖ := continuous_finsetSum _ fun m _ => (hVc m).norm
    rw [← intervalIntegral.integral_add_adjacent_intervals (hSc.intervalIntegrable 0 y₀)
      (hSc.intervalIntegrable y₀ 1)]
    have i1 : ∫ y in (0 : ℝ)..y₀, ∑ m ∈ Finset.range N, ‖V m y‖ ≤ 6 * P' * Real.exp (c * θ) / c * y₀ := by
      have := intervalIntegral.integral_mono_on hy₀.le (hSc.intervalIntegrable 0 y₀)
        (intervalIntegrable_const (μ := volume) (c := 6 * P' * Real.exp (c * θ) / c)) hlow
      rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at this
      linarith
    have i2 : ∫ y in y₀..1, ∑ m ∈ Finset.range N, ‖V m y‖ ≤ 2 * P * Real.exp (c * θ) / c * Real.log (1 / y₀) := by
      have hinv : IntervalIntegrable (fun y : ℝ => 2 * P * Real.exp (c * θ) / c * y⁻¹) volume y₀ 1 := by
        refine (ContinuousOn.intervalIntegrable ?_)
        exact continuousOn_const.mul (continuousOn_inv₀.mono fun y hy => by
          rw [uIcc_of_le hy₁] at hy; exact (hy₀.trans_le hy.1).ne')
      have := intervalIntegral.integral_mono_on hy₁ (hSc.intervalIntegrable y₀ 1) hinv hhigh
      rwa [intervalIntegral.integral_const_mul, integral_inv_of_pos hy₀ one_pos] at this
    linarith
  -- assemble
  have hm : ∀ m ∈ Finset.range N, ‖∫ t in (-1 : ℝ)..1, H (t * ζ) * Complex.cos ((c * (m + 2) : ℝ) * t)‖
      ≤ ‖Tp m‖ + ∫ y in (0 : ℝ)..1, ‖V m y‖ := fun m _ => by
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_I, one_mul]
    gcongr
    exact intervalIntegral.norm_integral_le_integral_norm zero_le_one
  calc ∑ m ∈ Finset.range N, ‖∫ t in (-1 : ℝ)..1, H (t * ζ) * Complex.cos ((c * (m + 2) : ℝ) * t)‖
      ≤ ∑ m ∈ Finset.range N, (‖Tp m‖ + ∫ y in (0 : ℝ)..1, ‖V m y‖) := Finset.sum_le_sum hm
    _ = ∑ m ∈ Finset.range N, ‖Tp m‖ + ∫ y in (0 : ℝ)..1, ∑ m ∈ Finset.range N, ‖V m y‖ := by
        rw [Finset.sum_add_distrib, intervalIntegral.integral_finsetSum hVi]
    _ ≤ Real.exp (c * θ) * (2 * P * Real.exp (-c) / (1 - Real.exp (-c)))
        + (6 * P' * Real.exp (c * θ) / c * y₀ + 2 * P * Real.exp (c * θ) / c * Real.log (1 / y₀)) :=
        add_le_add hsumtop hint
    _ = _ := by ring

end Cvs.Prolate.Mellin.HigherAliasesSummed

end
