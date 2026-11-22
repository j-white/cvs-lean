import Mathlib

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The first alias through the profile and its dual

For even series `H = Σ b_jζ^{2j}`, `C = Σ d_lζ^{2l}`, `Σ|b_j|, Σ|d_l| < ∞`, the alias `∫_{−1}^{1} H(tζ)C(t) dt` and the
dual `∫_{−1}^{1} H(t)C(τt) dt` are even series again, and their simple fractions (Cvs.Upstream.RayTransformPowerSeries) obey the partial fractions
`2/((2j + 2l + 1)(2j + p)) = (2/(2l + 1 − p))(1/(2j + p) − 1/(2j + 2l + 1))`.
-/

noncomputable section

open Real Set MeasureTheory Filter Complex Topology

namespace Cvs.Prolate.Mellin.FirstAliasProfileDual

/-- `∫_{−1}^{1} t^{2n} dt = 2/(2n + 1)`. -/
theorem integral_pow_even (n : ℕ) : ∫ t in (-1 : ℝ)..1, ((t : ℂ)) ^ (2 * n) = 2 / (2 * n + 1) := by
  have h := integral_pow (a := (-1 : ℝ)) (b := 1) (2 * n)
  have e : ∫ t in (-1 : ℝ)..1, ((t : ℂ)) ^ (2 * n) = ((∫ t in (-1 : ℝ)..1, t ^ (2 * n) : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]; push_cast; rfl
  rw [e, h]
  have : ((-1 : ℝ)) ^ (2 * n + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num
  rw [one_pow, this]
  push_cast; ring

/-- `‖1/(2j + p)‖ ≤ 1/|Im p|`. -/
theorem norm_inv_le {p : ℂ} (hp : p.im ≠ 0) (r : ℝ) : ‖1 / ((r : ℂ) + p)‖ ≤ 1 / |p.im| := by
  rw [norm_div, norm_one]
  have : |p.im| ≤ ‖(r : ℂ) + p‖ := by
    have := Complex.abs_im_le_norm ((r : ℂ) + p); simpa using this
  exact one_div_le_one_div_of_le (abs_pos.2 hp) this

/-- `ab(2/X)/Y = 2(a/Y)(b/Z) − b(a(2/X))/Z` when `X − Y = Z`. -/
theorem partial_frac (a b X Y Z : ℂ) (hX : X ≠ 0) (hY : Y ≠ 0) (hZ : Z ≠ 0) (h : X - Y = Z) :
    a * (b * (2 / X)) / Y = 2 * (a / Y) * (b / Z) - b * (a * (2 / X)) / Z := by
  have hZ' : Z = X - Y := h.symm
  subst hZ'
  field_simp

/-- **The partial-fraction identity of the first alias**. -/
theorem ml_identity {b d : ℕ → ℂ} (hb : Summable fun j => ‖b j‖) (hd : Summable fun l => ‖d l‖) {p : ℂ}
    (hp : p.im ≠ 0) :
    ∑' j, b j * (∑' l, d l * (2 / (2 * j + 2 * l + 1))) / (2 * j + p)
      = 2 * (∑' j, b j / (2 * j + p)) * (∑' l, d l / (2 * l + 1 - p))
        - ∑' l, d l * (∑' j, b j * (2 / (2 * j + 2 * l + 1))) / (2 * l + 1 - p) := by
  have hq : (1 - p).im ≠ 0 := by simp [hp]
  have hne1 : ∀ j : ℕ, (2 * j + p : ℂ) ≠ 0 := fun j h => hp (by have := congrArg Complex.im h; simpa using this)
  have hne2 : ∀ l : ℕ, (2 * l + 1 - p : ℂ) ≠ 0 := fun l h => hp (by
    have := congrArg Complex.im h; simp at this; linarith)
  have hne3 : ∀ j l : ℕ, (2 * j + 2 * l + 1 : ℂ) ≠ 0 := fun j l h => by
    have := congrArg Complex.re h; simp at this; linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j),
      (Nat.cast_nonneg l : (0 : ℝ) ≤ l)]
  set Q := 1 / |p.im| with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have h1 : ∀ j : ℕ, ‖1 / (2 * j + p)‖ ≤ Q := fun j => by
    have := norm_inv_le hp (2 * j); push_cast at this; exact this
  have h2 : ∀ l : ℕ, ‖1 / (2 * l + 1 - p)‖ ≤ Q := fun l => by
    have := norm_inv_le (p := -p) (by simpa using hp) (2 * l + 1)
    push_cast at this; simpa [sub_eq_add_neg, add_assoc, abs_neg, hQ] using this
  have h3 : ∀ j l : ℕ, ‖(2 : ℂ) / (2 * j + 2 * l + 1)‖ ≤ 2 := fun j l => by
    rw [norm_div, Complex.norm_ofNat]
    have : 1 ≤ ‖(2 * j + 2 * l + 1 : ℂ)‖ := by
      have := Complex.abs_re_le_norm (2 * j + 2 * l + 1 : ℂ)
      simp at this
      have h0 : (0 : ℝ) ≤ 2 * j + 2 * l := by positivity
      rw [abs_of_nonneg (by linarith)] at this; linarith
    rw [div_le_iff₀ (by linarith)]; linarith
  -- the summable product family
  have hbd : Summable fun z : ℕ × ℕ => ‖b z.1‖ * ‖d z.2‖ := by
    have := summable_mul_of_summable_norm (R := ℝ) (f := fun j => ‖b j‖) (g := fun l => ‖d l‖)
      (by simpa using hb) (by simpa using hd)
    exact this
  have sumOf : ∀ (K : ℕ × ℕ → ℂ) (M : ℝ), (∀ z, ‖K z‖ ≤ M * (‖b z.1‖ * ‖d z.2‖)) → Summable K := fun K M hK =>
    Summable.of_norm_bounded (hbd.mul_left M) hK
  set A : ℕ × ℕ → ℂ := fun z => 2 * (b z.1 / (2 * z.1 + p)) * (d z.2 / (2 * z.2 + 1 - p)) with hA
  set B : ℕ × ℕ → ℂ := fun z => d z.2 * (b z.1 * (2 / (2 * z.1 + 2 * z.2 + 1))) / (2 * z.2 + 1 - p) with hB
  set K : ℕ × ℕ → ℂ := fun z => b z.1 * (d z.2 * (2 / (2 * z.1 + 2 * z.2 + 1))) / (2 * z.1 + p) with hK
  have hKAB : ∀ z, K z = A z - B z := fun z => by
    simp only [hK, hA, hB]
    have e1 := hne1 z.1; have e2 := hne2 z.2; have e3 := hne3 z.1 z.2
    exact partial_frac _ _ _ _ _ e3 e1 e2 (by ring)
  have hAs : Summable A := sumOf A (2 * Q * Q) fun z => by
    simp only [hA, norm_mul, Complex.norm_ofNat, div_eq_mul_one_div (b z.1), div_eq_mul_one_div (d z.2)]
    have := h1 z.1; have := h2 z.2
    have := norm_nonneg (b z.1); have := norm_nonneg (d z.2)
    calc 2 * (‖b z.1‖ * ‖1 / (2 * (z.1 : ℂ) + p)‖) * (‖d z.2‖ * ‖1 / (2 * (z.2 : ℂ) + 1 - p)‖)
        ≤ 2 * (‖b z.1‖ * Q) * (‖d z.2‖ * Q) := by gcongr
      _ = 2 * Q * Q * (‖b z.1‖ * ‖d z.2‖) := by ring
  have hBs : Summable B := sumOf B (2 * Q) fun z => by
    simp only [hB, norm_mul, norm_div]
    have h2' := h2 z.2; rw [norm_div, norm_one] at h2'
    have := h3 z.1 z.2; rw [norm_div] at this
    have := norm_nonneg (b z.1); have := norm_nonneg (d z.2)
    rw [div_eq_mul_one_div]
    calc ‖d z.2‖ * (‖b z.1‖ * (‖(2 : ℂ)‖ / ‖(2 * (z.1 : ℂ) + 2 * z.2 + 1)‖)) * (1 / ‖(2 * (z.2 : ℂ) + 1 - p)‖)
        ≤ ‖d z.2‖ * (‖b z.1‖ * 2) * Q := by gcongr
      _ = 2 * Q * (‖b z.1‖ * ‖d z.2‖) := by ring
  have hKs : Summable K := by
    have : K = fun z => A z - B z := funext hKAB
    rw [this]; exact hAs.sub hBs
  -- the three double sums
  have eK : ∑' j, b j * (∑' l, d l * (2 / (2 * j + 2 * l + 1))) / (2 * j + p) = ∑' z, K z := by
    rw [hKs.tsum_prod]
    refine tsum_congr fun j => ?_
    simp only [hK]
    rw [tsum_div_const, tsum_mul_left]
  have eA : ∑' z, A z = 2 * (∑' j, b j / (2 * j + p)) * (∑' l, d l / (2 * l + 1 - p)) := by
    have hb1 : Summable fun j => ‖b j / (2 * j + p)‖ :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun j => by
        rw [div_eq_mul_one_div, norm_mul]; exact mul_le_mul_of_nonneg_left (h1 j) (norm_nonneg _))
        (hb.mul_right Q)
    have hd1 : Summable fun l => ‖d l / (2 * l + 1 - p)‖ :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun l => by
        rw [div_eq_mul_one_div, norm_mul]; exact mul_le_mul_of_nonneg_left (h2 l) (norm_nonneg _))
        (hd.mul_right Q)
    rw [mul_assoc, tsum_mul_tsum_of_summable_norm hb1 hd1, ← tsum_mul_left]
    refine tsum_congr fun z => ?_
    simp only [hA]; ring
  have eB : ∑' z, B z = ∑' l, d l * (∑' j, b j * (2 / (2 * j + 2 * l + 1))) / (2 * l + 1 - p) := by
    have hBs' : Summable fun z : ℕ × ℕ => B z.swap := (Equiv.prodComm ℕ ℕ).summable_iff.2 hBs
    rw [← (Equiv.prodComm ℕ ℕ).tsum_eq B]
    change ∑' z : ℕ × ℕ, B z.swap = _
    rw [hBs'.tsum_prod]
    refine tsum_congr fun l => ?_
    simp only [Prod.swap_prod_mk, hB]
    rw [tsum_div_const, tsum_mul_left]
  rw [eK, ← eA, ← eB, ← hAs.tsum_sub hBs]
  exact tsum_congr hKAB

/-! ### The alias and the dual as even series -/

section series

variable {b d : ℕ → ℂ} {H C : ℂ → ℂ}

/-- An even series is bounded by `Σ|b_j|` on the closed unit disk. -/
theorem norm_le_of_hasSum {z : ℂ} (hz : ‖z‖ ≤ 1) (hb : Summable fun j => ‖b j‖)
    (h : HasSum (fun j => b j * z ^ (2 * j)) (H z)) : ‖H z‖ ≤ ∑' j, ‖b j‖ := by
  have hle : ∀ j, ‖b j * z ^ (2 * j)‖ ≤ ‖b j‖ := fun j => by
    rw [norm_mul, norm_pow]
    exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hz)
  have hs : Summable fun j => ‖b j * z ^ (2 * j)‖ := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hb
  rw [← h.tsum_eq]
  exact (norm_tsum_le_tsum_norm hs).trans (hs.tsum_le_tsum hle hb)

/-- `∫_{−1}^{1} t^{2j} C(t) dt = Σ_l d_l·2/(2j + 2l + 1)`. -/
theorem hasSum_moment (hd : Summable fun l => ‖d l‖)
    (hC : ∀ z : ℂ, ‖z‖ ≤ 1 → HasSum (fun l => d l * z ^ (2 * l)) (C z)) (j : ℕ) :
    HasSum (fun l => d l * (2 / (2 * j + 2 * l + 1))) (∫ t in (-1 : ℝ)..1, (t : ℂ) ^ (2 * j) * C t) := by
  have hterm : ∀ l : ℕ, ∫ t in (-1 : ℝ)..1, (t : ℂ) ^ (2 * j) * (d l * (t : ℂ) ^ (2 * l))
      = d l * (2 / (2 * j + 2 * l + 1)) := fun l => by
    have e : (fun t : ℝ => (t : ℂ) ^ (2 * j) * (d l * (t : ℂ) ^ (2 * l)))
        = fun t : ℝ => d l * (t : ℂ) ^ (2 * (j + l)) := by
      funext t; rw [mul_add, pow_add]; ring
    rw [e, intervalIntegral.integral_const_mul, integral_pow_even]; push_cast; ring_nf
  simp_rw [← hterm]
  refine intervalIntegral.hasSum_integral_of_dominated_convergence (fun l _ => ‖d l‖) (fun l => ?_)
    (fun l => ?_) ?_ ?_ ?_
  · exact (by fun_prop : Continuous fun t : ℝ => (t : ℂ) ^ (2 * j) * (d l * (t : ℂ) ^ (2 * l))).aestronglyMeasurable
  · refine Eventually.of_forall fun t ht => ?_
    rw [uIoc_of_le (by norm_num)] at ht
    have ht1 : ‖(t : ℂ)‖ ≤ 1 := by rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_le.2 ⟨by linarith [ht.1], ht.2⟩
    rw [norm_mul, norm_mul, norm_pow, norm_pow]
    calc ‖(t : ℂ)‖ ^ (2 * j) * (‖d l‖ * ‖(t : ℂ)‖ ^ (2 * l)) ≤ 1 * (‖d l‖ * 1) := by
          gcongr <;> exact pow_le_one₀ (norm_nonneg _) ht1
      _ = ‖d l‖ := by ring
  · exact Eventually.of_forall fun t _ => hd
  · exact intervalIntegrable_const
  · refine Eventually.of_forall fun t ht => ?_
    rw [uIoc_of_le (by norm_num)] at ht
    have ht1 : ‖(t : ℂ)‖ ≤ 1 := by rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_le.2 ⟨by linarith [ht.1], ht.2⟩
    exact (hC t ht1).mul_left _

/-- **The alias as an even series**: `∫_{−1}^{1} H(tζ)C(t) dt = Σ_j b_j c_j ζ^{2j}`,
`c_j = Σ_l d_l·2/(2j + 2l + 1)`. -/
theorem hasSum_alias (hb : Summable fun j => ‖b j‖) (hd : Summable fun l => ‖d l‖)
    (hCc : Continuous C) (hH : ∀ z : ℂ, ‖z‖ ≤ 1 → HasSum (fun j => b j * z ^ (2 * j)) (H z))
    (hC : ∀ z : ℂ, ‖z‖ ≤ 1 → HasSum (fun l => d l * z ^ (2 * l)) (C z)) {ζ : ℂ} (hζ : ‖ζ‖ ≤ 1) :
    HasSum (fun j => b j * (∑' l, d l * (2 / (2 * j + 2 * l + 1))) * ζ ^ (2 * j))
      (∫ t in (-1 : ℝ)..1, H (t * ζ) * C t) := by
  have hterm : ∀ j : ℕ, ∫ t in (-1 : ℝ)..1, b j * ((t : ℂ) * ζ) ^ (2 * j) * C t
      = b j * (∑' l, d l * (2 / (2 * j + 2 * l + 1))) * ζ ^ (2 * j) := fun j => by
    rw [(hasSum_moment hd hC j).tsum_eq]
    have e : (fun t : ℝ => b j * ((t : ℂ) * ζ) ^ (2 * j) * C t)
        = fun t : ℝ => (b j * ζ ^ (2 * j)) * ((t : ℂ) ^ (2 * j) * C t) := by funext t; rw [mul_pow]; ring
    rw [e, intervalIntegral.integral_const_mul]; ring
  simp_rw [← hterm]
  have hmem : ∀ t ∈ Set.uIoc (-1 : ℝ) 1, ‖(t : ℂ)‖ ≤ 1 := fun t ht => by
    rw [uIoc_of_le (by norm_num)] at ht
    rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_le.2 ⟨by linarith [ht.1], ht.2⟩
  have hCb : ∀ t ∈ Set.uIoc (-1 : ℝ) 1, ‖C t‖ ≤ ∑' l, ‖d l‖ := fun t ht =>
    norm_le_of_hasSum (hmem t ht) hd (hC t (hmem t ht))
  refine intervalIntegral.hasSum_integral_of_dominated_convergence (fun j _ => ‖b j‖ * ∑' l, ‖d l‖)
    (fun j => ?_) (fun j => ?_) ?_ ?_ ?_
  · exact (by fun_prop : Continuous fun t : ℝ => b j * ((t : ℂ) * ζ) ^ (2 * j) * C t).aestronglyMeasurable
  · refine Eventually.of_forall fun t ht => ?_
    have h1 : ‖((t : ℂ) * ζ) ^ (2 * j)‖ ≤ 1 := by
      rw [norm_pow]; refine pow_le_one₀ (norm_nonneg _) ?_
      rw [norm_mul]; exact mul_le_one₀ (hmem t ht) (norm_nonneg _) hζ
    rw [norm_mul, norm_mul]
    calc ‖b j‖ * ‖((t : ℂ) * ζ) ^ (2 * j)‖ * ‖C t‖ ≤ ‖b j‖ * 1 * ∑' l, ‖d l‖ := by
          gcongr; exact hCb t ht
      _ = ‖b j‖ * ∑' l, ‖d l‖ := by ring
  · exact Eventually.of_forall fun t _ => hb.mul_right _
  · exact intervalIntegrable_const
  · refine Eventually.of_forall fun t ht => ?_
    have h1 : ‖(t : ℂ) * ζ‖ ≤ 1 := by rw [norm_mul]; exact mul_le_one₀ (hmem t ht) (norm_nonneg _) hζ
    exact (hH _ h1).mul_right (C t)

/-- **The dual as an even series**: `∫_{−1}^{1} H(t)C(τt) dt = Σ_l d_l M_l τ^{2l}`,
`M_l = Σ_j b_j·2/(2j + 2l + 1)`. -/
theorem hasSum_dual (hb : Summable fun j => ‖b j‖) (hd : Summable fun l => ‖d l‖) (hHc : Continuous H)
    (hH : ∀ z : ℂ, ‖z‖ ≤ 1 → HasSum (fun j => b j * z ^ (2 * j)) (H z))
    (hC : ∀ z : ℂ, ‖z‖ ≤ 1 → HasSum (fun l => d l * z ^ (2 * l)) (C z)) {τ : ℂ} (hτ : ‖τ‖ ≤ 1) :
    HasSum (fun l => d l * (∑' j, b j * (2 / (2 * j + 2 * l + 1))) * τ ^ (2 * l))
      (∫ t in (-1 : ℝ)..1, H t * C (τ * t)) := by
  have hterm : ∀ l : ℕ, ∫ t in (-1 : ℝ)..1, H t * (d l * (τ * t) ^ (2 * l))
      = d l * (∑' j, b j * (2 / (2 * j + 2 * l + 1))) * τ ^ (2 * l) := fun l => by
    have hm := (hasSum_moment hb hH l).tsum_eq
    have e2 : (∑' j, b j * (2 / (2 * j + 2 * l + 1))) = ∑' j, b j * (2 / (2 * l + 2 * j + 1)) :=
      tsum_congr fun j => by ring_nf
    rw [e2, hm]
    have e : (fun t : ℝ => H t * (d l * (τ * t) ^ (2 * l)))
        = fun t : ℝ => (d l * τ ^ (2 * l)) * ((t : ℂ) ^ (2 * l) * H t) := by
      funext t; rw [mul_pow]; ring
    rw [e, intervalIntegral.integral_const_mul]; ring
  simp_rw [← hterm]
  have hmem : ∀ t ∈ Set.uIoc (-1 : ℝ) 1, ‖(t : ℂ)‖ ≤ 1 := fun t ht => by
    rw [uIoc_of_le (by norm_num)] at ht
    rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_le.2 ⟨by linarith [ht.1], ht.2⟩
  have hHb : ∀ t ∈ Set.uIoc (-1 : ℝ) 1, ‖H t‖ ≤ ∑' j, ‖b j‖ := fun t ht =>
    norm_le_of_hasSum (hmem t ht) hb (hH t (hmem t ht))
  refine intervalIntegral.hasSum_integral_of_dominated_convergence (fun l _ => (∑' j, ‖b j‖) * ‖d l‖)
    (fun l => ?_) (fun l => ?_) ?_ ?_ ?_
  · exact (by fun_prop : Continuous fun t : ℝ => H t * (d l * (τ * t) ^ (2 * l))).aestronglyMeasurable
  · refine Eventually.of_forall fun t ht => ?_
    have h1 : ‖(τ * (t : ℂ)) ^ (2 * l)‖ ≤ 1 := by
      rw [norm_pow]; refine pow_le_one₀ (norm_nonneg _) ?_
      rw [norm_mul]; exact mul_le_one₀ hτ (norm_nonneg _) (hmem t ht)
    rw [norm_mul, norm_mul]
    calc ‖H t‖ * (‖d l‖ * ‖(τ * (t : ℂ)) ^ (2 * l)‖) ≤ (∑' j, ‖b j‖) * (‖d l‖ * 1) := by
          gcongr; exact hHb t ht
      _ = (∑' j, ‖b j‖) * ‖d l‖ := by ring
  · exact Eventually.of_forall fun t _ => hd.mul_left _
  · exact intervalIntegrable_const
  · refine Eventually.of_forall fun t ht => ?_
    have h1 : ‖τ * (t : ℂ)‖ ≤ 1 := by rw [norm_mul]; exact mul_le_one₀ hτ (norm_nonneg _) (hmem t ht)
    exact (hC _ h1).mul_left (H t)

end series

end Cvs.Prolate.Mellin.FirstAliasProfileDual

end
