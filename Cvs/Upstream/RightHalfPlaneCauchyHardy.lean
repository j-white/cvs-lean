import Mathlib
import Cvs.Zeta.VerticalLineShift

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The Cauchy formula on the right half-plane, and the pointwise `H²` bound

For `F` holomorphic on `Re s > −ε` with `‖F s‖ ≤ C/‖s‖` on `Re s ≥ 0`, `‖s‖ ≥ R₀`, and `Re z > 0`,
`∫ F(iy)/(z − iy) dy = 2πF(z)`; with `∫ 1/|z − iy|² dy = π/Re z` and Cauchy–Schwarz this gives
`‖F z‖² ≤ (∫ ‖F(iy)‖² dy)/(4π Re z)`.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology
open scoped Interval

namespace Cvs.Upstream.RightHalfPlaneCauchyHardy

/-! ### Two real integrals -/

/-- `∫ 1/(a² + (y − b)²) dy = π/a` for `a > 0`. -/
theorem integral_inv_sq_add_sq {a : ℝ} (ha : 0 < a) (b : ℝ) :
    ∫ y : ℝ, 1 / (a ^ 2 + (y - b) ^ 2) = Real.pi / a := by
  have h1 : (∫ y : ℝ, 1 / (a ^ 2 + (y - b) ^ 2)) = ∫ y : ℝ, 1 / (a ^ 2 + y ^ 2) :=
    integral_sub_right_eq_self (fun y => 1 / (a ^ 2 + y ^ 2)) b
  have h2 : (fun y : ℝ => 1 / (a ^ 2 + y ^ 2)) = fun y => (1 / a ^ 2) * (1 + (y / a) ^ 2)⁻¹ := by
    funext y
    have : a ^ 2 + y ^ 2 = a ^ 2 * (1 + (y / a) ^ 2) := by field_simp
    rw [this]; field_simp
  rw [h1, h2, integral_const_mul, Measure.integral_comp_div (fun y => (1 + y ^ 2)⁻¹) a,
    integral_univ_inv_one_add_sq, abs_of_pos ha, smul_eq_mul]
  field_simp

/-- `y ↦ 1/(a² + (y − b)²)` is integrable for `a > 0`. -/
theorem integrable_inv_sq_add_sq {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Integrable fun y : ℝ => 1 / (a ^ 2 + (y - b) ^ 2) := by
  by_contra h
  have := integral_undef h
  rw [integral_inv_sq_add_sq ha b] at this
  exact (div_pos Real.pi_pos ha).ne' this

/-- `‖z − iy‖² = (Re z)² + (y − Im z)²`. -/
theorem norm_sub_mul_I_sq (z : ℂ) (y : ℝ) : ‖z - y * I‖ ^ 2 = z.re ^ 2 + (y - z.im) ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp; ring

/-! ### Cauchy–Schwarz for complex integrands -/

/-- **Cauchy–Schwarz** for `ℂ`-valued integrands: `‖∫ f g‖² ≤ (∫ ‖f‖²)(∫ ‖g‖²)`. -/
theorem norm_integral_mul_sq_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℂ}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hf2 : Integrable (fun a => ‖f a‖ ^ 2) μ) (hg2 : Integrable (fun a => ‖g a‖ ^ 2) μ) :
    ‖∫ a, f a * g a ∂μ‖ ^ 2 ≤ (∫ a, ‖f a‖ ^ 2 ∂μ) * ∫ a, ‖g a‖ ^ 2 ∂μ := by
  have hfm : MemLp (fun a => ‖f a‖) 2 μ :=
    (memLp_two_iff_integrable_sq hf.norm).mpr hf2
  have hgm : MemLp (fun a => ‖g a‖) 2 μ :=
    (memLp_two_iff_integrable_sq hg.norm).mpr hg2
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) Real.HolderConjugate.two_two
    (Eventually.of_forall fun a => norm_nonneg (f a)) (Eventually.of_forall fun a => norm_nonneg (g a))
    (by rw [ENNReal.ofReal_ofNat]; exact hfm) (by rw [ENNReal.ofReal_ofNat]; exact hgm)
  simp only [Real.rpow_two] at h
  have hA := integral_nonneg (μ := μ) (f := fun a => ‖f a‖ ^ 2) fun a => sq_nonneg _
  have hB := integral_nonneg (μ := μ) (f := fun a => ‖g a‖ ^ 2) fun a => sq_nonneg _
  have h1 : ‖∫ a, f a * g a ∂μ‖ ≤ ∫ a, ‖f a‖ * ‖g a‖ ∂μ :=
    (norm_integral_le_integral_norm _).trans_eq (by simp)
  have h2 : ‖∫ a, f a * g a ∂μ‖
      ≤ (∫ a, ‖f a‖ ^ 2 ∂μ) ^ (1 / (2 : ℝ)) * (∫ a, ‖g a‖ ^ 2 ∂μ) ^ (1 / (2 : ℝ)) := h1.trans h
  have e : ((∫ a, ‖f a‖ ^ 2 ∂μ) ^ (1 / (2 : ℝ)) * (∫ a, ‖g a‖ ^ 2 ∂μ) ^ (1 / (2 : ℝ))) ^ 2
      = (∫ a, ‖f a‖ ^ 2 ∂μ) * ∫ a, ‖g a‖ ^ 2 ∂μ := by
    rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_natCast (_ ^ (1 / (2 : ℝ))), ← Real.rpow_mul hA,
      ← Real.rpow_mul hB]
    norm_num
  rw [← e]
  exact pow_le_pow_left₀ (norm_nonneg _) h2 2

/-! ### The Cauchy formula -/

/-- On a vertical line far to the right, `F(s)/(s − z)` is at most `2C/(σ² + y²)`. -/
theorem norm_div_sub_le_of_far {F : ℂ → ℂ} {C R₀ : ℝ}
    (hdec : ∀ s : ℂ, 0 ≤ s.re → R₀ ≤ ‖s‖ → ‖F s‖ ≤ C / ‖s‖) {z : ℂ} {σ : ℝ} (hσ0 : 0 < σ)
    (hσR : R₀ ≤ σ) (hσz : 2 * ‖z‖ ≤ σ) (y : ℝ) :
    ‖F (σ + y * I) / (σ + y * I - z)‖ ≤ 2 * C / (σ ^ 2 + y ^ 2) := by
  set s : ℂ := σ + y * I
  have hsre : s.re = σ := by simp [s]
  have hs2 : ‖s‖ ^ 2 = σ ^ 2 + y ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp [s]; ring
  have hsσ : σ ≤ ‖s‖ := by rw [← hsre]; exact (le_abs_self _).trans (Complex.abs_re_le_norm s)
  have hs0 : 0 < ‖s‖ := hσ0.trans_le hsσ
  have hFs := hdec s (by rw [hsre]; exact hσ0.le) (hσR.trans hsσ)
  have hC : 0 ≤ C := by
    have := (norm_nonneg _).trans hFs
    rwa [le_div_iff₀ hs0, zero_mul] at this
  have hden : ‖s‖ / 2 ≤ ‖s - z‖ := by
    have := norm_sub_norm_le s z
    linarith
  rw [norm_div]
  calc ‖F s‖ / ‖s - z‖ ≤ (C / ‖s‖) / (‖s‖ / 2) :=
        div_le_div₀ (by positivity) hFs (by positivity) hden
    _ = 2 * C / ‖s‖ ^ 2 := by field_simp
    _ = 2 * C / (σ ^ 2 + y ^ 2) := by rw [hs2]

/-- **The Cauchy formula on the right half-plane**: `F` holomorphic on `Re s > −ε` with `‖F s‖ ≤ C/‖s‖` on
`Re s ≥ 0`, `‖s‖ ≥ R₀` gives `∫ F(iy)/(z − iy) dy = 2πF(z)` for `Re z > 0`. -/
theorem integral_div_sub_eq {F : ℂ → ℂ} {ε C R₀ : ℝ} (hε : 0 < ε)
    (hF : DifferentiableOn ℂ F {s | -ε < s.re})
    (hdec : ∀ s : ℂ, 0 ≤ s.re → R₀ ≤ ‖s‖ → ‖F s‖ ≤ C / ‖s‖) {z : ℂ} (hz : 0 < z.re) :
    ∫ y : ℝ, F (y * I) / (z - y * I) = 2 * Real.pi * F z := by
  set y₀ := z.im
  set φ : ℂ → ℂ := fun s => F (s + y₀ * I) with hφ
  set J : ℝ → ℂ := fun σ => ∫ y : ℝ, F (σ + y * I) / (σ + y * I - z) with hJ
  -- the strip identity, for every right line beyond `Re z`
  have hstrip : ∀ σ : ℝ, z.re < σ → J σ - J 0 = 2 * Real.pi * F z := by
    intro σ hσ
    have hφd : DifferentiableOn ℂ φ {s | (0 : ℝ) - ε < s.re ∧ s.re < σ + ε} := by
      intro s hs
      refine (hF.differentiableAt ?_).comp s (by fun_prop) |>.differentiableWithinAt
      refine (isOpen_lt continuous_const Complex.continuous_re).mem_nhds ?_
      simp only [mem_ofPred_eq, add_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
        sub_self, add_zero]
      linarith [hs.1]
    have hC : 0 ≤ C := by
      have h := hdec (R₀.toNNReal + 1 : ℝ) (by simp; positivity) (by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
        linarith [Real.le_coe_toNNReal R₀])
      have hpos : (0 : ℝ) < ‖((R₀.toNNReal + 1 : ℝ) : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs]; positivity
      have := (norm_nonneg _).trans h
      rwa [le_div_iff₀ hpos, zero_mul] at this
    have hdecφ : ∀ s : ℂ, (0 : ℝ) ≤ s.re → s.re ≤ σ → |R₀| + 2 * |y₀| + 1 ≤ |s.im| →
        ‖φ s‖ ≤ (2 * C) * (1 + |s.im|) ^ (-(1 : ℝ)) := by
      intro s h0 _ him
      have hsn : |s.im| - |y₀| ≤ ‖s + y₀ * I‖ := by
        have h1 : (s + y₀ * I).im = s.im + y₀ := by simp
        have h2 : |s.im + y₀| ≤ ‖s + y₀ * I‖ := by rw [← h1]; exact Complex.abs_im_le_norm _
        have h3 : |s.im| - |y₀| ≤ |s.im + y₀| := by
          have := abs_sub_abs_le_abs_sub s.im (-y₀)
          rwa [abs_neg, sub_neg_eq_add] at this
        linarith
      have hR : R₀ ≤ ‖s + y₀ * I‖ := by linarith [abs_nonneg y₀, le_abs_self R₀]
      have hpos : 0 < (1 + |s.im|) / 2 := by positivity
      have hle : (1 + |s.im|) / 2 ≤ ‖s + y₀ * I‖ := by linarith [abs_nonneg y₀, abs_nonneg R₀]
      have hre : 0 ≤ (s + y₀ * I).re := by simpa using h0
      have hb := hdec (s + y₀ * I) hre hR
      rw [Real.rpow_neg_one]
      calc ‖φ s‖ = ‖F (s + y₀ * I)‖ := rfl
        _ ≤ C / ‖s + y₀ * I‖ := hb
        _ ≤ C / ((1 + |s.im|) / 2) := div_le_div_of_nonneg_left hC hpos hle
        _ = 2 * C * (1 + |s.im|)⁻¹ := by field_simp
    have h := Cvs.Zeta.VerticalLineShift.integral_vline_sub_of_pole (φ := φ) (σ₁ := 0) (σ₂ := σ) (x₀ := z.re) (δ := ε)
      (κ := 1) (T₀ := |R₀| + 2 * |y₀| + 1) (B := 2 * C) hz hσ hε one_pos hφd hdecφ
    have ht : ∀ a : ℝ, (∫ y : ℝ, φ (a + y * I) / (a + y * I - z.re)) = J a := by
      intro a
      have : (fun y : ℝ => φ (a + y * I) / (a + y * I - z.re))
          = fun y : ℝ => (fun t : ℝ => F (a + t * I) / (a + t * I - z)) (y + y₀) := by
        funext y
        have hz' : z = (z.re : ℂ) + y₀ * I := (Complex.re_add_im z).symm
        simp only [hφ]
        congr 1
        · congr 1; push_cast; ring
        · conv_rhs => rw [hz']
          push_cast; ring
      rw [this, integral_add_right_eq_self (fun t : ℝ => F (a + t * I) / (a + t * I - z)) y₀]
    have hx0 : φ z.re = F z := by
      simp only [hφ]; congr 1; exact Complex.re_add_im z
    rw [ht σ, ht 0, hx0] at h
    exact h
  -- the right line integral tends to `0`
  have hlim : Tendsto J atTop (𝓝 0) := by
    have hbd : ∀ᶠ σ : ℝ in atTop, ‖J σ‖ ≤ 2 * C * (Real.pi / σ) := by
      filter_upwards [eventually_gt_atTop 0, eventually_ge_atTop R₀, eventually_ge_atTop (2 * ‖z‖)]
        with σ hσ0 hσR hσz
      have hb := norm_div_sub_le_of_far hdec hσ0 hσR hσz
      have hint : Integrable fun y : ℝ => 2 * C / (σ ^ 2 + y ^ 2) := by
        have := (integrable_inv_sq_add_sq hσ0 0).const_mul (2 * C)
        refine this.congr (Eventually.of_forall fun y => ?_)
        simp only [sub_zero]; ring
      calc ‖J σ‖ ≤ ∫ y : ℝ, 2 * C / (σ ^ 2 + y ^ 2) :=
            norm_integral_le_of_norm_le hint (Eventually.of_forall hb)
        _ = 2 * C * (Real.pi / σ) := by
            rw [← integral_inv_sq_add_sq hσ0 0, ← integral_const_mul]
            congr 1; funext y; simp only [sub_zero]; ring
    have h0 : Tendsto (fun σ : ℝ => 2 * C * (Real.pi / σ)) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds.div_atTop tendsto_id).const_mul (2 * C)
    exact squeeze_zero_norm' hbd h0
  -- so `J 0 = −2πF(z)`
  have hJ0 : J 0 = -(2 * Real.pi * F z) := by
    have hl : Tendsto (fun σ => J σ - J 0) atTop (𝓝 (0 - J 0)) := hlim.sub tendsto_const_nhds
    have hc : Tendsto (fun σ => J σ - J 0) atTop (𝓝 (2 * Real.pi * F z)) :=
      tendsto_const_nhds.congr' ((eventually_gt_atTop z.re).mono fun σ hσ => (hstrip σ hσ).symm)
    have := tendsto_nhds_unique hl hc
    linear_combination -this
  have e : (fun y : ℝ => F (y * I) / (z - y * I))
      = fun y : ℝ => -(F (((0 : ℝ) : ℂ) + y * I) / (((0 : ℝ) : ℂ) + y * I - z)) := by
    funext y
    push_cast
    rw [zero_add, ← div_neg, neg_sub]
  rw [e, integral_neg]
  have : J 0 = ∫ y : ℝ, F (((0 : ℝ) : ℂ) + y * I) / (((0 : ℝ) : ℂ) + y * I - z) := rfl
  rw [← this, hJ0, neg_neg]

/-- The decay constant is nonnegative. -/
theorem nonneg_of_dec {F : ℂ → ℂ} {C R₀ : ℝ} (hdec : ∀ s : ℂ, 0 ≤ s.re → R₀ ≤ ‖s‖ → ‖F s‖ ≤ C / ‖s‖) :
    0 ≤ C := by
  have hpos : (0 : ℝ) < ‖((|R₀| + 1 : ℝ) : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs]; positivity
  have h := hdec ((|R₀| + 1 : ℝ) : ℂ) (by simp; positivity) (by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith [le_abs_self R₀])
  have := (norm_nonneg _).trans h
  rwa [le_div_iff₀ hpos, zero_mul] at this

/-- On the imaginary axis `‖F(iy)‖ ≤ C/|y|` once `|y| ≥ R₀`. -/
theorem norm_line_le {F : ℂ → ℂ} {C R₀ : ℝ} (hdec : ∀ s : ℂ, 0 ≤ s.re → R₀ ≤ ‖s‖ → ‖F s‖ ≤ C / ‖s‖)
    {y : ℝ} (hy : R₀ ≤ |y|) : ‖F (y * I)‖ ≤ C / |y| := by
  have hn : ‖(y : ℂ) * I‖ = |y| := by simp
  have h := hdec (y * I) (by simp) (by rw [hn]; exact hy)
  rwa [hn] at h

/-- A continuous `h : ℝ → ℂ` with `‖h y‖ ≤ B/y²` for `|y| ≥ T₀ ≥ 1` is integrable. -/
theorem integrable_of_le_div_sq {h : ℝ → ℂ} (hc : Continuous h) {T₀ B : ℝ} (hT₀ : 1 ≤ T₀)
    (hd : ∀ y : ℝ, T₀ ≤ |y| → ‖h y‖ ≤ B / y ^ 2) : Integrable h := by
  refine Cvs.Zeta.VerticalLineShift.integrable_of_decay hc (T₀ := T₀) (B := 4 * B) (κ := 2) one_lt_two fun y hy => ?_
  have hy1 : 1 ≤ |y| := hT₀.trans hy
  have hb := hd y hy
  have hy2p : 0 < y ^ 2 := by rw [← sq_abs]; positivity
  have hB : 0 ≤ B := by
    have := (norm_nonneg _).trans hb
    rwa [le_div_iff₀ hy2p, zero_mul] at this
  have hpow : (1 + |y|) ^ (-(2 : ℝ)) = 1 / (1 + |y|) ^ 2 := by
    rw [Real.rpow_neg (by positivity), Real.rpow_two, one_div]
  rw [hpow]
  refine hb.trans ?_
  have hy2 : y ^ 2 = |y| ^ 2 := (sq_abs y).symm
  rw [hy2, div_le_iff₀ (by positivity)]
  have h4 : (1 + |y|) ^ 2 ≤ 4 * |y| ^ 2 := by nlinarith
  calc B = 4 * B * (1 / (1 + |y|) ^ 2) * ((1 + |y|) ^ 2 / 4) := by field_simp
    _ ≤ 4 * B * (1 / (1 + |y|) ^ 2) * |y| ^ 2 := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        linarith

/-- Under the Cauchy formula's hypotheses, `y ↦ ‖F(iy)‖²` is integrable. -/
theorem integrable_norm_sq_line {F : ℂ → ℂ} {ε C R₀ : ℝ} (hε : 0 < ε)
    (hF : DifferentiableOn ℂ F {s | -ε < s.re})
    (hdec : ∀ s : ℂ, 0 ≤ s.re → R₀ ≤ ‖s‖ → ‖F s‖ ≤ C / ‖s‖) :
    Integrable fun y : ℝ => ‖F (y * I)‖ ^ 2 := by
  have hline : Continuous fun y : ℝ => F (y * I) := by
    refine hF.continuousOn.comp_continuous (by fun_prop) fun y => ?_
    simp only [mem_ofPred_eq, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self]
    linarith
  have h := integrable_of_le_div_sq (h := fun y : ℝ => ((‖F (y * I)‖ ^ 2 : ℝ) : ℂ))
    (Complex.continuous_ofReal.comp ((hline.norm).pow 2)) (T₀ := |R₀| + 1) (B := C ^ 2)
    (by linarith [abs_nonneg R₀]) (fun y hy => ?_)
  · exact (h.norm).congr (Eventually.of_forall fun y => by simp)
  · have hb := norm_line_le hdec (show R₀ ≤ |y| by linarith [le_abs_self R₀])
    have hy0 : 0 < |y| := by linarith [abs_nonneg R₀]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity), ← sq_abs y, ← div_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hb 2

/-- Under the Cauchy formula's hypotheses, `y ↦ F(iy)/(z − iy)` is integrable for `Re z > 0`. -/
theorem integrable_div_sub_line {F : ℂ → ℂ} {ε C R₀ : ℝ} (hε : 0 < ε)
    (hF : DifferentiableOn ℂ F {s | -ε < s.re})
    (hdec : ∀ s : ℂ, 0 ≤ s.re → R₀ ≤ ‖s‖ → ‖F s‖ ≤ C / ‖s‖) {z : ℂ} (hz : 0 < z.re) :
    Integrable fun y : ℝ => F (y * I) / (z - y * I) := by
  have hC := nonneg_of_dec hdec
  have hline : Continuous fun y : ℝ => F (y * I) := by
    refine hF.continuousOn.comp_continuous (by fun_prop) fun y => ?_
    simp only [mem_ofPred_eq, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self]
    linarith
  have hne : ∀ y : ℝ, z - y * I ≠ 0 := fun y h => by
    have := congrArg Complex.re h
    simp at this; linarith
  refine integrable_of_le_div_sq (hline.div (by fun_prop) hne) (T₀ := |R₀| + 2 * ‖z‖ + 1)
    (B := 2 * C) (by linarith [abs_nonneg R₀, norm_nonneg z]) fun y hy => ?_
  have hb := norm_line_le hdec (show R₀ ≤ |y| by linarith [le_abs_self R₀, norm_nonneg z])
  have hy0 : 0 < |y| := by linarith [abs_nonneg R₀, norm_nonneg z]
  have hden : |y| / 2 ≤ ‖z - y * I‖ := by
    have h1 : ‖(y : ℂ) * I‖ = |y| := by simp
    have := norm_sub_norm_le ((y : ℂ) * I) z
    rw [h1, norm_sub_rev] at this
    linarith [abs_nonneg R₀]
  rw [norm_div, ← sq_abs y]
  calc ‖F (y * I)‖ / ‖z - y * I‖ ≤ (C / |y|) / (|y| / 2) :=
        div_le_div₀ (by positivity) hb (by positivity) hden
    _ = 2 * C / |y| ^ 2 := by field_simp

/-- **The pointwise `H²` bound**: under the Cauchy formula's hypotheses, with `‖F(iy)‖²` integrable,
`‖F z‖² ≤ (∫ ‖F(iy)‖² dy)/(4π Re z)`. -/
theorem norm_sq_le {F : ℂ → ℂ} {ε C R₀ : ℝ} (hε : 0 < ε)
    (hF : DifferentiableOn ℂ F {s | -ε < s.re})
    (hdec : ∀ s : ℂ, 0 ≤ s.re → R₀ ≤ ‖s‖ → ‖F s‖ ≤ C / ‖s‖)
    (hL2 : Integrable fun y : ℝ => ‖F (y * I)‖ ^ 2) {z : ℂ} (hz : 0 < z.re) :
    ‖F z‖ ^ 2 ≤ (∫ y : ℝ, ‖F (y * I)‖ ^ 2) / (4 * Real.pi * z.re) := by
  have hcont : ContinuousOn F {s | -ε < s.re} := hF.continuousOn
  have hline : Continuous fun y : ℝ => F (y * I) := by
    refine hcont.comp_continuous (by fun_prop) fun y => ?_
    simp only [mem_ofPred_eq, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self]
    linarith
  have hne : ∀ y : ℝ, z - y * I ≠ 0 := fun y h => by
    have := congrArg Complex.re h
    simp at this; linarith
  have hg : Continuous fun y : ℝ => 1 / (z - y * I) := by
    fun_prop (disch := exact hne _)
  have hg2 : Integrable fun y : ℝ => ‖1 / (z - y * I)‖ ^ 2 := by
    refine (integrable_inv_sq_add_sq hz z.im).congr (Eventually.of_forall fun y => ?_)
    simp only [norm_div, norm_one, div_pow, one_pow]
    rw [norm_sub_mul_I_sq]
  have hI2 : ∫ y : ℝ, ‖1 / (z - y * I)‖ ^ 2 = Real.pi / z.re := by
    rw [← integral_inv_sq_add_sq hz z.im]
    congr 1; funext y
    simp only [norm_div, norm_one, div_pow, one_pow]
    rw [norm_sub_mul_I_sq]
  have hcs := norm_integral_mul_sq_le hline.aestronglyMeasurable hg.aestronglyMeasurable hL2 hg2
  have hcf := integral_div_sub_eq hε hF hdec hz
  have e : (fun y : ℝ => F (y * I) * (1 / (z - y * I))) = fun y : ℝ => F (y * I) / (z - y * I) := by
    funext y; ring
  rw [e, hcf, hI2] at hcs
  have hn : ‖2 * (Real.pi : ℂ) * F z‖ ^ 2 = 4 * Real.pi ^ 2 * ‖F z‖ ^ 2 := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    simp; ring
  rw [hn] at hcs
  have hpi := Real.pi_pos
  rw [le_div_iff₀ (by positivity)]
  have : 4 * Real.pi ^ 2 * ‖F z‖ ^ 2 * z.re ≤ (∫ y : ℝ, ‖F (y * I)‖ ^ 2) * Real.pi := by
    have := mul_le_mul_of_nonneg_right hcs hz.le
    rwa [mul_assoc (∫ y : ℝ, ‖F (y * I)‖ ^ 2), div_mul_cancel₀ _ hz.ne'] at this
  nlinarith

end Cvs.Upstream.RightHalfPlaneCauchyHardy

end
