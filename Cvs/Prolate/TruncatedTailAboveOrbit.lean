import Mathlib
import Cvs.L2a.FarPartDirichletSplit
import Cvs.L2a.PositionTruncatedTail
import Cvs.L2a.SpectralMassLevelLeak
import Cvs.L2a.TailLogScaleTest
import Cvs.Prolate.GreenIdentityAboveOrbitFreq
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.Mellin.MellinKernelSturmLiouville
import Cvs.Prolate.Mellin.OrbitGapGreenIdentity
import Cvs.Upstream.PlancherelL1L2SpectralDensity
import Cvs.WeilForm.Archimedean.LevyIntegrandSpectral
import Cvs.WeilForm.SelfConvolutionCosine
import Cvs.WeilForm.SelfConvolutionTransform

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The truncated tail above the orbit frequency

On the edge `[1, b]` one integration by parts against `y_t = −u_t′/w` gives `‖I(1, b; t)‖ ≤ 2(P₀(1 + √b) + P₁(b − 1)√b)/√w`;
with Cvs.Prolate.GreenIdentityAboveOrbitFreq on `[2, k]` the transform of `posTail ψ k` is at most `(2(3P₀ + 2P₁) + 74√(Ē/c)(1 + log k))/|t|` for
`t² ≥ 2c²k²`, so its mass above `K ≥ √2·ck` is at most that numerator squared over `πK`.
-/

namespace Cvs.Prolate.TruncatedTailAboveOrbit

open Real Set intervalIntegral MeasureTheory Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.Prolate.Mellin.MellinKernelSturmLiouville Cvs.Prolate.Mellin.OrbitGapGreenIdentity Cvs.Prolate.Mellin.GreenBoundaryBound Cvs.L2a.FarPartDirichletSplit
open scoped FourierTransform

/-! ### The edge -/

/-- `|u_t(ξ)| ≤ √(ξw)` and `|ũ_t(ξ)| ≤ √(ξw)`, `w = t² + ¼`. -/
theorem abs_ku_le {t ξ : ℝ} (hξ : 0 < ξ) : |ku t ξ| ≤ √(ξ * (t ^ 2 + 1 / 4)) := by
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (by have := ku_sq_add_kus_sq (t := t) hξ; nlinarith [sq_nonneg (kus t ξ)])

theorem abs_kus_le {t ξ : ℝ} (hξ : 0 < ξ) : |kus t ξ| ≤ √(ξ * (t ^ 2 + 1 / 4)) := by
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (by have := ku_sq_add_kus_sq (t := t) hξ; nlinarith [sq_nonneg (ku t ξ)])

/-- **One integration by parts on the edge**: for `y` with `y = −v′/w`, `|v| ≤ √(ξw)` on `[1, b]` and `ψ′ = ψ₁`,
`|∫_1^b ψ y| ≤ (P₀(1 + √b) + P₁(b − 1)√b)/√w`. -/
theorem abs_integral_edge_le {ψ ψ₁ y v : ℝ → ℝ} {b w P₀ P₁ : ℝ} (hb : 1 ≤ b) (hw : 0 < w)
    (hψ : ∀ ξ ∈ uIcc 1 b, HasDerivAt ψ (ψ₁ ξ) ξ) (hψ₁ : ContinuousOn ψ₁ (uIcc 1 b))
    (hv : ∀ ξ ∈ uIcc 1 b, HasDerivAt v (-(w * y ξ)) ξ) (hyc : ContinuousOn y (uIcc 1 b))
    (hvb : ∀ ξ ∈ Icc 1 b, |v ξ| ≤ √(ξ * w))
    (hP₀ : ∀ ξ ∈ Icc 1 b, |ψ ξ| ≤ P₀) (hP₁ : ∀ ξ ∈ Icc 1 b, |ψ₁ ξ| ≤ P₁) :
    |∫ ξ in (1 : ℝ)..b, ψ ξ * y ξ| ≤ (P₀ * (1 + √b) + P₁ * (b - 1) * √b) / √w := by
  have hsw : 0 < √w := Real.sqrt_pos.mpr hw
  have hvc : ContinuousOn v (uIcc 1 b) := fun ξ hξ => (hv ξ hξ).continuousAt.continuousWithinAt
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hψ hv (hψ₁.intervalIntegrable)
    (show ContinuousOn (fun ξ => -(w * y ξ)) (uIcc 1 b) from (continuousOn_const.mul hyc).neg).intervalIntegrable
  have e : ∫ ξ in (1 : ℝ)..b, ψ ξ * y ξ = -(1 / w) * ∫ ξ in (1 : ℝ)..b, ψ ξ * -(w * y ξ) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun ξ _ => ?_
    field_simp
  rw [e, hibp]
  have hb1 : (1 : ℝ) ∈ Icc 1 b := ⟨le_rfl, hb⟩
  have hbb : b ∈ Icc 1 b := ⟨hb, le_rfl⟩
  have hP₀0 : 0 ≤ P₀ := le_trans (abs_nonneg _) (hP₀ 1 hb1)
  have hP₁0 : 0 ≤ P₁ := le_trans (abs_nonneg _) (hP₁ 1 hb1)
  -- the boundary terms
  have hB1 : |ψ b * v b| ≤ P₀ * (√b * √w) := by
    rw [abs_mul, ← Real.sqrt_mul (by linarith)]
    exact mul_le_mul (hP₀ b hbb) (hvb b hbb) (abs_nonneg _) hP₀0
  have hB0 : |ψ 1 * v 1| ≤ P₀ * √w := by
    rw [abs_mul]
    have := hvb 1 hb1
    rw [one_mul] at this
    exact mul_le_mul (hP₀ 1 hb1) this (abs_nonneg _) hP₀0
  -- the bulk
  have hbulk : |∫ ξ in (1 : ℝ)..b, ψ₁ ξ * v ξ| ≤ P₁ * (√b * √w) * (b - 1) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 1) (b := b) (C := P₁ * (√b * √w))
      (f := fun ξ => ψ₁ ξ * v ξ) fun ξ hξ => by
        rw [uIoc_of_le hb] at hξ
        have hξ' : ξ ∈ Icc 1 b := ⟨hξ.1.le, hξ.2⟩
        rw [Real.norm_eq_abs, abs_mul]
        refine mul_le_mul (hP₁ ξ hξ') ((hvb ξ hξ').trans ?_) (abs_nonneg _) hP₁0
        rw [Real.sqrt_mul (by linarith [hξ.1])]
        exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hξ'.2) (Real.sqrt_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ b - 1)] at h
    exact h
  have hsum : |ψ b * v b - ψ 1 * v 1 - ∫ ξ in (1 : ℝ)..b, ψ₁ ξ * v ξ|
      ≤ P₀ * (√b * √w) + P₀ * √w + P₁ * (√b * √w) * (b - 1) := by
    refine (abs_sub _ _).trans ?_
    refine add_le_add ((abs_sub _ _).trans (add_le_add hB1 hB0)) hbulk
  rw [abs_mul, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 1 / w)]
  calc 1 / w * |ψ b * v b - ψ 1 * v 1 - ∫ ξ in (1 : ℝ)..b, ψ₁ ξ * v ξ|
      ≤ 1 / w * (P₀ * (√b * √w) + P₀ * √w + P₁ * (√b * √w) * (b - 1)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (P₀ * (1 + √b) + P₁ * (b - 1) * √b) * (√w / w) := by ring
    _ = (P₀ * (1 + √b) + P₁ * (b - 1) * √b) / √w := by
        have hq : √w / w = 1 / √w := by
          rw [div_eq_div_iff hw.ne' hsw.ne', one_mul, Real.mul_self_sqrt hw.le]
        rw [hq]; ring

/-- **The edge mode**: `‖I(1, b; t)‖ ≤ 2(P₀(1 + √b) + P₁(b − 1)√b)/√w` for `ψ′ = ψ₁` on `[1, b]`. -/
theorem norm_mellinI_edge_le {ψ ψ₁ : ℝ → ℝ} {b t P₀ P₁ : ℝ} (hb : 1 ≤ b)
    (hψ : ∀ ξ ∈ uIcc 1 b, HasDerivAt ψ (ψ₁ ξ) ξ) (hψ₁ : ContinuousOn ψ₁ (uIcc 1 b))
    (hP₀ : ∀ ξ ∈ Icc 1 b, |ψ ξ| ≤ P₀) (hP₁ : ∀ ξ ∈ Icc 1 b, |ψ₁ ξ| ≤ P₁) :
    ‖mellinI ψ 1 b t‖ ≤ 2 * ((P₀ * (1 + √b) + P₁ * (b - 1) * √b) / √(t ^ 2 + 1 / 4)) := by
  have hw : 0 < t ^ 2 + 1 / 4 := by positivity
  have hpos : ∀ ξ ∈ uIcc (1 : ℝ) b, 0 < ξ := fun ξ hξ => by rw [uIcc_of_le hb] at hξ; linarith [hξ.1]
  have h1 := abs_integral_edge_le (y := ky t) (v := ku t) hb hw hψ hψ₁
    (fun ξ hξ => by have := hasDerivAt_ku (ξ := t) (hpos ξ hξ); exact this)
    (fun ξ hξ => (hasDerivAt_ky (ξ := t) (hpos ξ hξ)).continuousAt.continuousWithinAt)
    (fun ξ hξ => abs_ku_le (by linarith [hξ.1])) hP₀ hP₁
  have h2 := abs_integral_edge_le (y := kys t) (v := kus t) hb hw hψ hψ₁
    (fun ξ hξ => by have := hasDerivAt_kus (ξ := t) (hpos ξ hξ); exact this)
    (fun ξ hξ => (hasDerivAt_kys (ξ := t) (hpos ξ hξ)).continuousAt.continuousWithinAt)
    (fun ξ hξ => abs_kus_le (by linarith [hξ.1])) hP₀ hP₁
  unfold mellinI
  calc ‖((∫ ξ in (1 : ℝ)..b, ψ ξ * ky t ξ : ℝ) : ℂ) - Complex.I * ((∫ ξ in (1 : ℝ)..b, ψ ξ * kys t ξ : ℝ) : ℂ)‖
      ≤ ‖((∫ ξ in (1 : ℝ)..b, ψ ξ * ky t ξ : ℝ) : ℂ)‖ + ‖Complex.I * ((∫ ξ in (1 : ℝ)..b, ψ ξ * kys t ξ : ℝ) : ℂ)‖ :=
        norm_sub_le _ _
    _ = |∫ ξ in (1 : ℝ)..b, ψ ξ * ky t ξ| + |∫ ξ in (1 : ℝ)..b, ψ ξ * kys t ξ| := by
        rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
          Real.norm_eq_abs]
    _ ≤ _ := by linarith

/-! ### The truncated tail -/

/-- `Σ_{1≤m≤⌊k⌋} 1/m ≤ 1 + log k` for `k ≥ 1`. -/
theorem sum_inv_Icc_le {k : ℝ} (hk : 1 ≤ k) : ∑ m ∈ Finset.Icc 1 ⌊k⌋₊, (m : ℝ)⁻¹ ≤ 1 + Real.log k := by
  have h := harmonic_le_one_add_log ⌊k⌋₊
  simp_rw [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at h
  have hf : (1 : ℝ) ≤ ⌊k⌋₊ := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by
    have := Nat.floor_pos.mpr hk; omega)
  have hl : Real.log ⌊k⌋₊ ≤ Real.log k := Real.log_le_log (by linarith) (Nat.floor_le (by linarith))
  linarith

/-- **The truncated tail above the orbit frequency**: for `c ≥ 1`, `0 ≤ χ ≤ c²`, `k ≥ 1`, `t² ≥ 2c²k²`, a rung
pair on `[2, k]` with energy `≤ Ē`, and `|ψ| ≤ P₀`, `|ψ′| ≤ P₁` on `[1, 2]`:
`‖𝓕(posTail ψ k)(t)‖ ≤ (2(3P₀ + 2P₁) + 74√(Ē/c)(1 + log k))/|t|`. -/
theorem norm_fourier_posTail_le_hi {c χ k t Ebar P₀ P₁ : ℝ} {ψ ψ₁ u : ℝ → ℝ} (hc : 1 ≤ c) (hχ0 : 0 ≤ χ)
    (hχ : χ ≤ c ^ 2) (hk : 1 ≤ k) (ht : 2 * c ^ 2 * k ^ 2 ≤ t ^ 2) (hψc : ContinuousOn ψ (Icc 1 k))
    (hψ : ∀ ξ ∈ Icc 2 k, HasDerivAt ψ (u ξ / pP ξ) ξ)
    (hu : ∀ ξ ∈ Icc 2 k, HasDerivAt u (-(qP c χ ξ * ψ ξ)) ξ)
    (hE : ∀ ξ ∈ Icc 2 k, energy (aP c χ) ψ u ξ ≤ Ebar)
    (hψ₁ : ∀ ξ ∈ Icc (1 : ℝ) 2, HasDerivAt ψ (ψ₁ ξ) ξ) (hψ₁c : ContinuousOn ψ₁ (Icc 1 2))
    (hP₀ : ∀ ξ ∈ Icc (1 : ℝ) 2, |ψ ξ| ≤ P₀) (hP₁ : ∀ ξ ∈ Icc (1 : ℝ) 2, |ψ₁ ξ| ≤ P₁) :
    ‖𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf (Cvs.L2a.TailLogScaleTest.logScale (Cvs.L2a.PositionTruncatedTail.posTail ψ k)))
        (t / (2 * π))‖
      ≤ (2 * (3 * P₀ + 2 * P₁) + 74 * √(Ebar / c) * (1 + Real.log k)) / |t| := by
  set w := t ^ 2 + 1 / 4 with hwd
  have hc0 : 0 < c := by linarith
  have hk0 : 0 < k := by linarith
  have ht0 : 0 < |t| := by
    have : 0 < t ^ 2 := lt_of_lt_of_le (by positivity) ht
    exact abs_pos.mpr (by rintro rfl; simp at this)
  have hw0 : 0 < w := by positivity
  have htw : |t| ≤ √w := by
    rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by linarith)
  have hP₀0 : 0 ≤ P₀ := le_trans (abs_nonneg _) (hP₀ 1 ⟨le_rfl, by norm_num⟩)
  have hP₁0 : 0 ≤ P₁ := le_trans (abs_nonneg _) (hP₁ 1 ⟨le_rfl, by norm_num⟩)
  have hEb : 0 ≤ Ebar ∨ k < 2 := by
    rcases lt_or_ge k 2 with h | h
    · exact Or.inr h
    · left
      have h0 : 0 ≤ energy (aP c χ) ψ u 2 := by unfold energy aP; positivity
      exact le_trans h0 (hE 2 ⟨le_rfl, h⟩)
  set S := √(Ebar / (c * w)) with hSd
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hSt : S ≤ √(Ebar / c) / |t| := by
    rw [hSd, Real.sqrt_div' _ (by positivity : (0 : ℝ) ≤ c * w)]
    rcases le_or_gt Ebar 0 with hE0 | hE0
    · rw [Real.sqrt_eq_zero'.mpr hE0, zero_div, Real.sqrt_eq_zero'.mpr (div_nonpos_of_nonpos_of_nonneg hE0 hc0.le),
        zero_div]
    · rw [Real.sqrt_div' _ hc0.le, div_div, Real.sqrt_mul hc0.le]
      exact div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (by positivity)
        (mul_le_mul_of_nonneg_left htw (Real.sqrt_nonneg _))
  set E0 := 2 * ((P₀ * (1 + √2) + P₁ * (2 - 1) * √2) / √w) with hE0d
  have hE0b : E0 ≤ 2 * (3 * P₀ + 2 * P₁) / |t| := by
    have hs2 : √(2 : ℝ) ≤ 3 / 2 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
    have hn : P₀ * (1 + √2) + P₁ * (2 - 1) * √2 ≤ 3 * P₀ + 2 * P₁ := by nlinarith
    have hn0 : 0 ≤ P₀ * (1 + √2) + P₁ * (2 - 1) * √2 := by positivity
    rw [hE0d, mul_div_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    exact (div_le_div_of_nonneg_left hn0 ht0 htw).trans (div_le_div_of_nonneg_right hn (by positivity))
  -- the transform as a Dirichlet sum
  have hcont := hψc
  have hky : ContinuousOn (ky t) (Icc 1 k) := continuousOn_ky t k
  have hkys : ContinuousOn (kys t) (Icc 1 k) := continuousOn_kys t k
  rw [Cvs.L2a.TailLogScaleTest.fourier_eq _ (fun θ hθ => Cvs.L2a.PositionTruncatedTail.posTail_zero ψ k hθ) t
    (Cvs.L2a.PositionTruncatedTail.integrableOn_posTail_mul ψ hcont hky)
    (Cvs.L2a.PositionTruncatedTail.integrableOn_posTail_mul ψ hcont hkys), mellin_posTail_eq ψ hk hcont t]
  -- each mode
  have hmode : ∀ m ∈ Finset.Icc 1 ⌊k⌋₊, ‖dch m t * mellinI ψ m k t‖
      ≤ (if m = 1 then E0 else 0) + 74 * S * (m : ℝ)⁻¹ := by
    intro m hm
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    have hmk : (m : ℝ) ≤ k := (Nat.cast_le.mpr (Finset.mem_Icc.mp hm).2).trans (Nat.floor_le hk0.le)
    rw [norm_mul, norm_dch]
    have hwk : 2 * c ^ 2 * k ^ 2 ≤ w := by linarith
    rcases eq_or_lt_of_le hm1 with h1 | h2
    · -- the first mode: edge plus (if `k ≥ 2`) the Green part on `[2, k]`
      subst h1
      simp only [if_true, Nat.cast_one, Real.sqrt_one, inv_one, one_mul]
      rcases lt_or_ge k 2 with hk2 | hk2
      · have hedge := norm_mellinI_edge_le (t := t) (b := k) (ψ₁ := ψ₁) hk
          (fun ξ hξ => by rw [uIcc_of_le hk] at hξ; exact hψ₁ ξ ⟨hξ.1, hξ.2.trans hk2.le⟩)
          (hψ₁c.mono (by rw [uIcc_of_le hk]; exact Icc_subset_Icc le_rfl hk2.le))
          (fun ξ hξ => hP₀ ξ ⟨hξ.1, hξ.2.trans hk2.le⟩) (fun ξ hξ => hP₁ ξ ⟨hξ.1, hξ.2.trans hk2.le⟩)
        have hmono : P₀ * (1 + √k) + P₁ * (k - 1) * √k ≤ P₀ * (1 + √2) + P₁ * (2 - 1) * √2 := by
          have hs : √k ≤ √2 := Real.sqrt_le_sqrt hk2.le
          have : (k - 1) * √k ≤ (2 - 1) * √2 :=
            mul_le_mul (by linarith) hs (Real.sqrt_nonneg _) (by norm_num)
          nlinarith
        have h1 : ‖mellinI ψ 1 k t‖ ≤ E0 := by
          refine hedge.trans ?_
          rw [hE0d]
          exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hmono (Real.sqrt_nonneg _)) (by norm_num)
        have : 0 ≤ 74 * S := by positivity
        simp only [Nat.cast_one, inv_one, mul_one]; linarith
      · rw [mellinI_add ψ le_rfl (by norm_num : (1 : ℝ) ≤ 2) hk2 hcont t]
        have hedge := norm_mellinI_edge_le (t := t) (b := 2) (ψ₁ := ψ₁) (by norm_num)
          (fun ξ hξ => by rw [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)] at hξ; exact hψ₁ ξ hξ)
          (by rw [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)]; exact hψ₁c) hP₀ hP₁
        have hG := Cvs.Prolate.GreenIdentityAboveOrbitFreq.norm_mellinI_le_hi (t := t) hc hχ0 hχ le_rfl hk2 hwk hψ hu hE
        have hG' : ‖mellinI ψ 2 k t‖ ≤ 74 * S := by
          refine hG.trans ?_
          rw [hSd]
          have h2 : (1 : ℝ) ≤ √2 := by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
          exact div_le_self (by positivity) h2
        simp only [Nat.cast_one, inv_one, mul_one]
        exact (norm_add_le _ _).trans (add_le_add hedge hG')
    · -- a higher mode: Green on `[m, k]`
      have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast h2
      have hne : m ≠ 1 := by omega
      simp only [hne, if_false, zero_add]
      have hG := Cvs.Prolate.GreenIdentityAboveOrbitFreq.norm_mellinI_le_hi (t := t) hc hχ0 hχ hm2 hmk hwk
        (fun ξ hξ => hψ ξ ⟨hm2.trans hξ.1, hξ.2⟩) (fun ξ hξ => hu ξ ⟨hm2.trans hξ.1, hξ.2⟩)
        (fun ξ hξ => hE ξ ⟨hm2.trans hξ.1, hξ.2⟩)
      have hm0 : 0 < (m : ℝ) := by linarith
      have hsm : 0 < √(m : ℝ) := Real.sqrt_pos.mpr hm0
      calc (√(m : ℝ))⁻¹ * ‖mellinI ψ m k t‖ ≤ (√(m : ℝ))⁻¹ * (74 * √(Ebar / (c * w)) / √(m : ℝ)) :=
            mul_le_mul_of_nonneg_left hG (by positivity)
        _ = 74 * S * (m : ℝ)⁻¹ := by
            rw [hSd]
            have : √(m : ℝ) ^ 2 = m := Real.sq_sqrt hm0.le
            field_simp
            rw [this]; ring
  -- sum the modes
  have hsum := (norm_sum_le _ _).trans (Finset.sum_le_sum hmode)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have hite : ∑ m ∈ Finset.Icc 1 ⌊k⌋₊, (if m = 1 then E0 else 0) = E0 := by
    rw [Finset.sum_ite_eq' (Finset.Icc 1 ⌊k⌋₊) 1 (fun _ => E0)]
    have : 1 ∈ Finset.Icc 1 ⌊k⌋₊ := Finset.mem_Icc.mpr ⟨le_rfl, Nat.one_le_iff_ne_zero.mpr (by
      have := Nat.floor_pos.mpr hk; omega)⟩
    simp [this]
  rw [hite] at hsum
  have hH := sum_inv_Icc_le hk
  have hlog0 : 0 ≤ Real.log k := Real.log_nonneg hk
  calc _ ≤ E0 + 74 * S * ∑ m ∈ Finset.Icc 1 ⌊k⌋₊, (m : ℝ)⁻¹ := hsum
    _ ≤ 2 * (3 * P₀ + 2 * P₁) / |t| + 74 * (√(Ebar / c) / |t|) * (1 + Real.log k) := by
        gcongr
    _ = _ := by ring

/-! ### The mass above a frequency -/

/-- **The mass above `K`**: if `‖𝓕(G)(t)‖ ≤ A/|t|` for `|t| ≥ K > 0`, then `∫_{θ>1} G² − specMass G K ≤ A²/K`. -/
theorem highMass_le {G : ℝ → ℝ} (hG : ∀ θ ≤ 1, G θ = 0)
    (h2 : MemLp (Cvs.L2a.TailLogScaleTest.logScale G) 2 volume)
    (h1 : Integrable (Cvs.L2a.TailLogScaleTest.logScale G) volume) {K A : ℝ} (hK : 0 < K)
    (hA : ∀ t, K ≤ |t| → ‖𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf (Cvs.L2a.TailLogScaleTest.logScale G)) (t / (2 * π))‖ ≤ A / |t|) :
    (∫ θ in Ioi 1, G θ ^ 2) - Cvs.L2a.SpectralMassLevelLeak.specMass G K ≤ A ^ 2 / K := by
  set ρ := Cvs.WeilForm.SelfConvolutionCosine.specDensity (Cvs.L2a.TailLogScaleTest.logScale G) with hρd
  have hρ : Integrable ρ := Cvs.WeilForm.Archimedean.LevyIntegrandSpectral.integrable_specDensity h2 h1
  have hρ0 : ∀ t, 0 ≤ ρ t := fun t => Cvs.WeilForm.SelfConvolutionCosine.specDensity_nonneg _ t
  have hN : ∫ t, ρ t = ∫ θ in Ioi 1, G θ ^ 2 := by
    rw [Cvs.Upstream.PlancherelL1L2SpectralDensity.integral_specDensity h1 h2, Cvs.L2a.TailLogScaleTest.integral_sq G hG]
  set S := {t : ℝ | |t| < K} with hSd
  have hS : MeasurableSet S := Cvs.L2a.SpectralMassLevelLeak.measurableSet_abs_lt K
  have hsplit := integral_add_compl hS hρ
  have hmass : Cvs.L2a.SpectralMassLevelLeak.specMass G K = ∫ t in S, ρ t := rfl
  -- the majorant `(A²/(πK²))·(1 + (t/K)²)⁻¹` on the complement
  set g : ℝ → ℝ := fun t => A ^ 2 / (π * K ^ 2) * (1 + (t / K) ^ 2)⁻¹ with hgd
  have hgi : Integrable g := (integrable_inv_one_add_sq.comp_div hK.ne').const_mul _
  have hg : ∫ t, g t = A ^ 2 / K := by
    rw [hgd, MeasureTheory.integral_const_mul,
      Measure.integral_comp_div (fun x : ℝ => (1 + x ^ 2)⁻¹) K, integral_univ_inv_one_add_sq,
      abs_of_pos hK, smul_eq_mul]
    field_simp
  have hle : ∫ t in Sᶜ, ρ t ≤ ∫ t in Sᶜ, g t := by
    refine setIntegral_mono_on hρ.integrableOn hgi.integrableOn hS.compl fun t ht => ?_
    have htK : K ≤ |t| := not_lt.mp ht
    have ht0 : 0 < |t| := lt_of_lt_of_le hK htK
    have hA' := hA t htK
    have hAt : 0 ≤ A / |t| := le_trans (norm_nonneg _) hA'
    have hsq : ‖𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf (Cvs.L2a.TailLogScaleTest.logScale G)) (t / (2 * π))‖ ^ 2 ≤ (A / |t|) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hA' 2
    have hρt : ρ t ≤ (A / |t|) ^ 2 / (2 * π) := by
      rw [hρd]; unfold Cvs.WeilForm.SelfConvolutionCosine.specDensity
      exact div_le_div_of_nonneg_right hsq (by positivity)
    refine hρt.trans ?_
    rw [hgd, div_pow, sq_abs]
    have hK2 : K ^ 2 ≤ t ^ 2 := by rw [← sq_abs t]; exact pow_le_pow_left₀ hK.le htK 2
    have ht2 : 0 < t ^ 2 := by rw [← sq_abs]; positivity
    have hA2 : 0 ≤ A ^ 2 := sq_nonneg A
    simp only
    rw [div_pow, show (1 + t ^ 2 / K ^ 2)⁻¹ = K ^ 2 / (K ^ 2 + t ^ 2) by field_simp]
    rw [div_div, div_le_iff₀ (by positivity)]
    have : A ^ 2 / (π * K ^ 2) * (K ^ 2 / (K ^ 2 + t ^ 2)) * (t ^ 2 * (2 * π)) = A ^ 2 * (2 * t ^ 2 / (K ^ 2 + t ^ 2)) := by
      field_simp
    rw [this]
    have h1' : 1 ≤ 2 * t ^ 2 / (K ^ 2 + t ^ 2) := by rw [le_div_iff₀ (by positivity)]; linarith
    nlinarith
  have hgS : ∫ t in Sᶜ, g t ≤ ∫ t, g t :=
    setIntegral_le_integral hgi (Filter.Eventually.of_forall fun t => by rw [hgd]; positivity)
  rw [hmass, ← hN]
  linarith

end Cvs.Prolate.TruncatedTailAboveOrbit
