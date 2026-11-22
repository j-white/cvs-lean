import Mathlib
import Cvs.Zeta.Convexity.StripConvexityBound
import Cvs.Zeta.ZetaDerivCauchyEstimate
import Cvs.Zeta.ZetaDerivFunctionalEquation
import Cvs.Zeta.ZetaGrowth

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Growth of `ζ` and `ζ'` on vertical strips, and the contour integrands

On `σ₀ ≤ Re s ≤ 3`, `|ζ(s)| ≤ C(1+|t|)^{3/4−σ₀/2}`; Cauchy's estimate on circles of radius `1/8`
gives `|ζ'(s)| ≤ C(1+|t|)^{3/4−(σ₀−1/8)/2}`. Against a factor `H = O((1+|t|)^{−3})` the integrands
`ζ₁H`, `ζ'(s−1)H`, `𝒜₀ζ₁H`, `𝒜ζ₁H` and `(ζ'+𝒜ζ)(s−1)H` decay like `(1+|t|)^{−5/4−σ₀/2(+1/16)}`.
-/

noncomputable section

open Complex Metric

namespace Cvs.Zeta.ZetaDerivStripGrowth

open Cvs.Zeta.ZetaDerivFunctionalEquation (archA archA₀)

/-! ### Elementary factors -/

/-- `|s − 1| ≤ 2(1 + |t|)` on `−1/2 ≤ Re s ≤ 3`. -/
theorem norm_sub_one_le {s : ℂ} (h1 : -1/2 ≤ s.re) (h2 : s.re ≤ 3) :
    ‖s - 1‖ ≤ 2 * (1 + |s.im|) := by
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  have hre : |(s - 1).re| ≤ 2 := by
    rw [Complex.sub_re, Complex.one_re, abs_le]; constructor <;> linarith
  have him : (s - 1).im = s.im := by simp
  rw [him]
  linarith [abs_nonneg s.im]

/-- `X^a · X · X^{−3} = X^{a−2}` for `X > 0`. -/
theorem rpow_mul_self_mul_rpow_neg_three {X : ℝ} (hX : 0 < X) (a : ℝ) :
    X ^ a * X * X ^ (-3 : ℝ) = X ^ (a - 2) := by
  rw [show a - 2 = a + 1 + (-3) by ring, Real.rpow_add hX, Real.rpow_add hX, Real.rpow_one]

/-- `1 + log(2 + t) ≤ 33 (1 + t)^{1/16}` for `t ≥ 0`. -/
theorem one_add_log_le_rpow {t : ℝ} (ht : 0 ≤ t) :
    1 + Real.log (2 + t) ≤ 33 * (1 + t) ^ (1/16 : ℝ) := by
  have hY : 1 ≤ (1 + t) ^ (1/16 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hlog := Real.log_le_rpow_div (x := 2 + t) (ε := 1/16) (by linarith) (by norm_num)
  have h2 : (2 + t) ^ (1/16 : ℝ) ≤ 2 * (1 + t) ^ (1/16 : ℝ) := by
    calc (2 + t) ^ (1/16 : ℝ) ≤ (2 * (1 + t)) ^ (1/16 : ℝ) :=
          Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
      _ = 2 ^ (1/16 : ℝ) * (1 + t) ^ (1/16 : ℝ) := Real.mul_rpow (by norm_num) (by linarith)
      _ ≤ 2 * (1 + t) ^ (1/16 : ℝ) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          simpa using Real.rpow_le_rpow_of_exponent_le (x := 2) (by norm_num)
            (show (1/16 : ℝ) ≤ 1 by norm_num)
  have : Real.log (2 + t) ≤ 32 * (1 + t) ^ (1/16 : ℝ) := by
    rw [div_eq_mul_inv] at hlog; norm_num at hlog; linarith
  linarith

/-! ### `ζ` and `ζ'` on strips -/

/-- **Convexity bound on a strip.** `|ζ(s)| ≤ C(1+|t|)^{3/4−σ₀/2}` for `σ₀ ≤ Re s ≤ 3`, `|t| ≥ 1`. -/
theorem norm_zeta_le_strip {σ₀ : ℝ} (h : -1/2 ≤ σ₀) (h' : σ₀ ≤ 3/2) :
    ∃ C, ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ 3 → 1 ≤ |s.im| →
      ‖riemannZeta s‖ ≤ C * (1 + |s.im|) ^ (3/4 - σ₀/2) := by
  obtain ⟨C, hC⟩ := Cvs.Zeta.Convexity.StripConvexityBound.norm_zeta_convexity
  set D : ℝ := ∑' n : ℕ, ‖LSeries.term 1 ((3/2 : ℝ) : ℂ) n‖ with hDdef
  have hD : 0 ≤ D := tsum_nonneg fun _ => norm_nonneg _
  refine ⟨max C 0 + D, fun s h1 h2 ht => ?_⟩
  have hX : 1 ≤ 1 + |s.im| := by linarith [abs_nonneg s.im]
  have hone : 1 ≤ (1 + |s.im|) ^ (3/4 - σ₀/2) := Real.one_le_rpow hX (by linarith)
  have hM : 0 ≤ max C 0 * (1 + |s.im|) ^ (3/4 - σ₀/2) :=
    mul_nonneg (le_max_right _ _) (by linarith)
  rw [add_mul]
  rcases le_or_gt s.re (3/2) with hr | hr
  · have hmono : (1 + |s.im|) ^ (3/4 - s.re/2) ≤ (1 + |s.im|) ^ (3/4 - σ₀/2) :=
      Real.rpow_le_rpow_of_exponent_le hX (by linarith)
    have hz := hC s (by linarith) hr ht
    have h3 : C * (1 + |s.im|) ^ (3/4 - s.re/2) ≤ max C 0 * (1 + |s.im|) ^ (3/4 - σ₀/2) :=
      calc C * (1 + |s.im|) ^ (3/4 - s.re/2) ≤ max C 0 * (1 + |s.im|) ^ (3/4 - s.re/2) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
        _ ≤ max C 0 * (1 + |s.im|) ^ (3/4 - σ₀/2) :=
            mul_le_mul_of_nonneg_left hmono (le_max_right _ _)
    have : 0 ≤ D * (1 + |s.im|) ^ (3/4 - σ₀/2) := by positivity
    linarith
  · have hz : ‖riemannZeta s‖ ≤ D :=
      Cvs.Zeta.norm_riemannZeta_le_of_re_le (σ₀ := 3/2) (by norm_num) hr.le
    have : D ≤ D * (1 + |s.im|) ^ (3/4 - σ₀/2) := le_mul_of_one_le_right hD hone
    linarith

/-- **Cauchy bound for `ζ'` on a strip.** Radius `1/8` circles inside `σ₀ − 1/8 ≤ Re ≤ 3`. -/
theorem norm_deriv_zeta_le_strip {σ₀ : ℝ} (h : -3/8 ≤ σ₀) (h' : σ₀ ≤ 3/2) :
    ∃ C, ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ 2 → 2 ≤ |s.im| →
      ‖deriv riemannZeta s‖ ≤ C * (1 + |s.im|) ^ (3/4 - (σ₀ - 1/8)/2) := by
  obtain ⟨C, hC⟩ := norm_zeta_le_strip (σ₀ := σ₀ - 1/8) (by linarith) (by linarith)
  set e : ℝ := 3/4 - (σ₀ - 1/8)/2 with he
  have he0 : 0 ≤ e := by rw [he]; linarith
  refine ⟨8 * (max C 0 * 2 ^ e), fun s h1 h2 ht => ?_⟩
  have hX : 0 < 1 + |s.im| := by positivity
  have hpole : (1 : ℂ) ∉ closedBall s (1/8) := by
    intro hm
    rw [mem_closedBall, dist_eq_norm] at hm
    have him : |s.im| ≤ ‖1 - s‖ := by
      simpa using Complex.abs_im_le_norm (1 - s)
    linarith
  have hsph : ∀ w ∈ sphere s (1/8), ‖riemannZeta w‖ ≤ max C 0 * 2 ^ e * (1 + |s.im|) ^ e := by
    intro w hw
    rw [mem_sphere_iff_norm] at hw
    have hwre : |w.re - s.re| ≤ 1/8 := by
      have := Complex.abs_re_le_norm (w - s)
      simp only [Complex.sub_re] at this; linarith
    have hwim : |w.im - s.im| ≤ 1/8 := by
      have := Complex.abs_im_le_norm (w - s)
      simp only [Complex.sub_im] at this; linarith
    have hre := abs_le.mp hwre
    have hwim' : |w.im| ≤ |s.im| + 1/8 := by
      have := abs_sub_abs_le_abs_sub w.im s.im; linarith
    have hwim'' : 1 ≤ |w.im| := by
      have := abs_sub_abs_le_abs_sub s.im w.im
      rw [abs_sub_comm] at this; linarith
    have hz := hC w (by linarith [hre.1]) (by linarith [hre.2]) hwim''
    have hbase : 1 + |w.im| ≤ 2 * (1 + |s.im|) := by linarith [abs_nonneg s.im]
    calc ‖riemannZeta w‖ ≤ C * (1 + |w.im|) ^ e := hz
      _ ≤ max C 0 * (1 + |w.im|) ^ e :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ max C 0 * (2 * (1 + |s.im|)) ^ e :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (by positivity) hbase he0) (le_max_right _ _)
      _ = max C 0 * 2 ^ e * (1 + |s.im|) ^ e := by
          rw [Real.mul_rpow (by norm_num) hX.le]; ring
  have hd := Cvs.ZeroFree.norm_deriv_zeta_le (by norm_num : (0:ℝ) < 1/8) hpole hsph
  calc ‖deriv riemannZeta s‖ ≤ max C 0 * 2 ^ e * (1 + |s.im|) ^ e / (1/8) := hd
    _ = 8 * (max C 0 * 2 ^ e) * (1 + |s.im|) ^ e := by ring

/-! ### The contour integrands against `H = O((1+|t|)^{−3})` -/

/-- `ζ₁ H` decays like `(1+|t|)^{−(5/4+σ₀/2)}` on `σ₀ ≤ Re s ≤ σ₁ ≤ 3`. -/
theorem norm_zeta₁_mul_le {σ₀ σ₁ T₀ CH : ℝ} {H : ℂ → ℂ} (h : -1/2 ≤ σ₀) (h' : σ₀ ≤ 3/2)
    (h₁ : σ₁ ≤ 3)
    (hH : ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ σ₁ → T₀ ≤ |s.im| → ‖H s‖ ≤ CH * (1 + |s.im|) ^ (-3 : ℝ)) :
    ∃ B, ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ σ₁ → max T₀ 1 ≤ |s.im| →
      ‖riemannZeta₁ s * H s‖ ≤ B * (1 + |s.im|) ^ (-(5/4 + σ₀/2)) := by
  obtain ⟨C, hC⟩ := norm_zeta_le_strip h h'
  refine ⟨C * 2 * CH, fun s h1 h2 ht => ?_⟩
  have hT := le_of_max_le_left ht
  have ht1 := le_of_max_le_right ht
  have hX : 0 < 1 + |s.im| := by positivity
  have hs1 : s ≠ 1 := by
    intro hs; rw [hs] at ht1; simp at ht1; linarith
  have hζ₁ : riemannZeta₁ s = (s - 1) * riemannZeta s := by
    rw [riemannZeta_eq_inv_sub_mul hs1, ← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr hs1),
      one_mul]
  have hz := hC s (by linarith) (by linarith) ht1
  have hsub := norm_sub_one_le (s := s) (by linarith) (by linarith)
  have hh := hH s h1 h2 hT
  rw [hζ₁, norm_mul, norm_mul]
  calc ‖s - 1‖ * ‖riemannZeta s‖ * ‖H s‖
      ≤ (2 * (1 + |s.im|)) * (C * (1 + |s.im|) ^ (3/4 - σ₀/2)) * (CH * (1 + |s.im|) ^ (-3 : ℝ)) :=
        mul_le_mul (mul_le_mul hsub hz (norm_nonneg _) (by positivity)) hh (norm_nonneg _)
          (mul_nonneg (by positivity) ((norm_nonneg _).trans hz))
    _ = C * 2 * CH * ((1 + |s.im|) ^ (3/4 - σ₀/2) * (1 + |s.im|) * (1 + |s.im|) ^ (-3 : ℝ)) := by
        ring
    _ = C * 2 * CH * (1 + |s.im|) ^ (-(5/4 + σ₀/2)) := by
        rw [rpow_mul_self_mul_rpow_neg_three hX]; congr 2; ring

/-- `ζ'(s)(s−1)H` decays like `(1+|t|)^{−(5/4+σ₀/2−1/16)}` on `σ₀ ≤ Re s ≤ σ₁ ≤ 2`. -/
theorem norm_deriv_zeta_mul_le {σ₀ σ₁ T₀ CH : ℝ} {H : ℂ → ℂ} (h : -3/8 ≤ σ₀) (h' : σ₀ ≤ 3/2)
    (h₁ : σ₁ ≤ 2)
    (hH : ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ σ₁ → T₀ ≤ |s.im| → ‖H s‖ ≤ CH * (1 + |s.im|) ^ (-3 : ℝ)) :
    ∃ B, ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ σ₁ → max T₀ 2 ≤ |s.im| →
      ‖deriv riemannZeta s * (s - 1) * H s‖ ≤ B * (1 + |s.im|) ^ (-(5/4 + σ₀/2 - 1/16)) := by
  obtain ⟨C, hC⟩ := norm_deriv_zeta_le_strip h h'
  refine ⟨C * 2 * CH, fun s h1 h2 ht => ?_⟩
  have hT := le_of_max_le_left ht
  have ht2 := le_of_max_le_right ht
  have hX : 0 < 1 + |s.im| := by positivity
  have hz := hC s h1 (by linarith) ht2
  have hsub := norm_sub_one_le (s := s) (by linarith) (by linarith)
  have hh := hH s h1 h2 hT
  rw [norm_mul, norm_mul]
  calc ‖deriv riemannZeta s‖ * ‖s - 1‖ * ‖H s‖
      ≤ (C * (1 + |s.im|) ^ (3/4 - (σ₀ - 1/8)/2)) * (2 * (1 + |s.im|))
          * (CH * (1 + |s.im|) ^ (-3 : ℝ)) :=
        mul_le_mul (mul_le_mul hz hsub (norm_nonneg _) ((norm_nonneg _).trans hz)) hh
          (norm_nonneg _) (mul_nonneg ((norm_nonneg _).trans hz) (by positivity))
    _ = C * 2 * CH * ((1 + |s.im|) ^ (3/4 - (σ₀ - 1/8)/2) * (1 + |s.im|)
          * (1 + |s.im|) ^ (-3 : ℝ)) := by ring
    _ = C * 2 * CH * (1 + |s.im|) ^ (-(5/4 + σ₀/2 - 1/16)) := by
        rw [rpow_mul_self_mul_rpow_neg_three hX]; congr 2; ring

/-- `𝒜₀ ζ₁ H` decays like `(1+|t|)^{−(5/4+σ₀/2−1/16)}` on `σ₀ ≤ Re s ≤ σ₁ ≤ 1/2`. -/
theorem norm_archA₀_mul_le {σ₀ σ₁ T₀ CH : ℝ} {H : ℂ → ℂ} (h : -1/2 ≤ σ₀) (h₁ : σ₁ ≤ 1/2)
    (hH : ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ σ₁ → T₀ ≤ |s.im| → ‖H s‖ ≤ CH * (1 + |s.im|) ^ (-3 : ℝ)) :
    ∃ B, ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ σ₁ → max T₀ 2 ≤ |s.im| →
      ‖archA₀ s * riemannZeta₁ s * H s‖ ≤ B * (1 + |s.im|) ^ (-(5/4 + σ₀/2 - 1/16)) := by
  rcases lt_or_ge σ₁ σ₀ with hσ | hσ
  · exact ⟨0, fun s h1 h2 _ => absurd (h1.trans h2) (not_le.mpr hσ)⟩
  obtain ⟨B₁, hB₁⟩ := norm_zeta₁_mul_le h (by linarith) (by linarith) hH
  obtain ⟨CA, hCA⟩ := Cvs.Zeta.ZetaDerivFunctionalEquation.norm_archA₀_le
  refine ⟨|CA| * 33 * max B₁ 0, fun s h1 h2 ht => ?_⟩
  have hT := le_of_max_le_left ht
  have ht2 := le_of_max_le_right ht
  have hX : 0 < 1 + |s.im| := by positivity
  have hA : ‖archA₀ s‖ ≤ |CA| * 33 * (1 + |s.im|) ^ (1/16 : ℝ) := by
    have h0 := hCA s (by linarith) (by linarith) ht2
    have hl := one_add_log_le_rpow (abs_nonneg s.im)
    have hlpos : 0 ≤ 1 + Real.log (2 + |s.im|) := by
      have : 0 ≤ Real.log (2 + |s.im|) := Real.log_nonneg (by linarith [abs_nonneg s.im])
      linarith
    calc ‖archA₀ s‖ ≤ CA * (1 + Real.log (2 + |s.im|)) := h0
      _ ≤ |CA| * (1 + Real.log (2 + |s.im|)) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) hlpos
      _ ≤ |CA| * (33 * (1 + |s.im|) ^ (1/16 : ℝ)) :=
          mul_le_mul_of_nonneg_left hl (abs_nonneg _)
      _ = |CA| * 33 * (1 + |s.im|) ^ (1/16 : ℝ) := by ring
  have hz : ‖riemannZeta₁ s * H s‖ ≤ max B₁ 0 * (1 + |s.im|) ^ (-(5/4 + σ₀/2)) :=
    (hB₁ s h1 h2 (max_le hT (by linarith))).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  rw [mul_assoc, norm_mul]
  calc ‖archA₀ s‖ * ‖riemannZeta₁ s * H s‖
      ≤ (|CA| * 33 * (1 + |s.im|) ^ (1/16 : ℝ)) * (max B₁ 0 * (1 + |s.im|) ^ (-(5/4 + σ₀/2))) :=
        mul_le_mul hA hz (norm_nonneg _) (by positivity)
    _ = |CA| * 33 * max B₁ 0 * ((1 + |s.im|) ^ (1/16 : ℝ) * (1 + |s.im|) ^ (-(5/4 + σ₀/2))) := by
        ring
    _ = |CA| * 33 * max B₁ 0 * (1 + |s.im|) ^ (-(5/4 + σ₀/2 - 1/16)) := by
        rw [← Real.rpow_add hX]; congr 2; ring

/-- `𝒜 ζ₁ H` decays like `(1+|t|)^{−(5/4+σ₀/2−1/16)}` on `σ₀ ≤ Re s ≤ σ₁ ≤ 1/2`. -/
theorem norm_archA_mul_le {σ₀ σ₁ T₀ CH : ℝ} {H : ℂ → ℂ} (h : -1/2 ≤ σ₀) (h₁ : σ₁ ≤ 1/2)
    (hH : ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ σ₁ → T₀ ≤ |s.im| → ‖H s‖ ≤ CH * (1 + |s.im|) ^ (-3 : ℝ)) :
    ∃ B, ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ σ₁ → max T₀ 2 ≤ |s.im| →
      ‖archA s * riemannZeta₁ s * H s‖ ≤ B * (1 + |s.im|) ^ (-(5/4 + σ₀/2 - 1/16)) := by
  rcases lt_or_ge σ₁ σ₀ with hσ | hσ
  · exact ⟨0, fun s h1 h2 _ => absurd (h1.trans h2) (not_le.mpr hσ)⟩
  obtain ⟨B₁, hB₁⟩ := norm_zeta₁_mul_le h (by linarith) (by linarith) hH
  obtain ⟨B₀, hB₀⟩ := norm_archA₀_mul_le h h₁ hH
  refine ⟨max B₁ 0 / 2 + B₀, fun s h1 h2 ht => ?_⟩
  have hT := le_of_max_le_left ht
  have ht2 := le_of_max_le_right ht
  have hX1 : 1 ≤ 1 + |s.im| := by linarith [abs_nonneg s.im]
  have hs0 : s ≠ 0 := by
    intro hs; rw [hs] at ht2; simp at ht2; linarith
  have hA := Cvs.Zeta.ZetaDerivFunctionalEquation.archA_eq (s := s) (by linarith) (by linarith) hs0
  have hinv : ‖s⁻¹‖ ≤ 1/2 := by
    rw [norm_inv]
    have : |s.im| ≤ ‖s‖ := Complex.abs_im_le_norm s
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  have hz : ‖riemannZeta₁ s * H s‖ ≤ max B₁ 0 * (1 + |s.im|) ^ (-(5/4 + σ₀/2 - 1/16)) :=
    calc ‖riemannZeta₁ s * H s‖ ≤ B₁ * (1 + |s.im|) ^ (-(5/4 + σ₀/2)) :=
          hB₁ s h1 h2 (max_le hT (by linarith))
      _ ≤ max B₁ 0 * (1 + |s.im|) ^ (-(5/4 + σ₀/2)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ max B₁ 0 * (1 + |s.im|) ^ (-(5/4 + σ₀/2 - 1/16)) :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)) (le_max_right _ _)
  have h0 := hB₀ s h1 h2 ht
  have hsplit : archA s * riemannZeta₁ s * H s
      = -(s⁻¹ * (riemannZeta₁ s * H s)) + archA₀ s * riemannZeta₁ s * H s := by
    rw [hA]; ring
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  rw [norm_neg, norm_mul]
  have hP : 0 ≤ (1 + |s.im|) ^ (-(5/4 + σ₀/2 - 1/16)) := by positivity
  have h1' : ‖s⁻¹‖ * ‖riemannZeta₁ s * H s‖
      ≤ 1/2 * (max B₁ 0 * (1 + |s.im|) ^ (-(5/4 + σ₀/2 - 1/16))) :=
    mul_le_mul hinv hz (norm_nonneg _) (by norm_num)
  nlinarith

end Cvs.Zeta.ZetaDerivStripGrowth
