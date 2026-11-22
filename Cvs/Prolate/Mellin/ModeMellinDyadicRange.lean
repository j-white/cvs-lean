import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.NumberTheory.Harmonic.Bounds
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.Mellin.ModeMellinDyadicPiece

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# One mode's Mellin transform below the gap, on `[s₀, 2^J s₀]`

With `ModeMellinDyadicPiece`'s piece bound `P(s) = (8/3)(V√(G/(αs))/m + Y√(2cGs))/(c²m²s²)`, `P(2s) ≤ P(s)/2`, so the dyadic
pieces telescope: `|∫_{s₀}^{2^J s₀} ψ(mτ) y(τ)| ≤ 2P(s₀)` for every `J`.
-/

namespace Cvs.Prolate.Mellin.ModeMellinDyadicRange

open Real Set Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval

/-- `ModeMellinDyadicPiece`'s bound on the piece `[s, 2s]`. -/
noncomputable def P (c χ m G Y V s : ℝ) : ℝ :=
  8 / 3 * (V * √(G / (√3 / 2 * √(c ^ 2 - χ) * s)) / m + Y * √(2 * c * G * s)) / (c ^ 2 * m ^ 2 * s ^ 2)

/-- **The pieces halve**: `P(2s) ≤ P(s)/2`. -/
theorem P_two_mul {c χ m G Y V s : ℝ} (hc : 0 < c) (hχ : χ < c ^ 2) (hm : 0 < m) (hs : 0 < s)
    (hG : 0 ≤ G) (hY : 0 ≤ Y) (hV : 0 ≤ V) :
    P c χ m G Y V (2 * s) ≤ P c χ m G Y V s / 2 := by
  unfold P
  set α := √3 / 2 * √(c ^ 2 - χ) with hα
  have hd : 0 < c ^ 2 - χ := by linarith
  have hα0 : 0 < α := by positivity
  set A := V * √(G / (α * s)) / m with hA
  set B := Y * √(2 * c * G * s) with hB
  have h2 : √2 * √2 = 2 := mul_self_sqrt (by norm_num)
  have hs2 : 0 < √2 := by positivity
  have eA : V * √(G / (α * (2 * s))) / m = A / √2 := by
    rw [hA, show G / (α * (2 * s)) = G / (α * s) / 2 by field_simp, sqrt_div' _ (by norm_num : (0:ℝ) ≤ 2)]
    field_simp
  have eB : Y * √(2 * c * G * (2 * s)) = √2 * B := by
    rw [hB, show 2 * c * G * (2 * s) = 2 * (2 * c * G * s) by ring, sqrt_mul (by norm_num)]; ring
  rw [eA, eB]
  have hA0 : 0 ≤ A := by positivity
  have hB0 : 0 ≤ B := by positivity
  have hle : A / √2 + √2 * B ≤ 2 * (A + B) := by
    have : A / √2 ≤ 2 * A := by
      rw [div_le_iff₀ hs2]; nlinarith [Real.sqrt_nonneg 2, Real.one_lt_sqrt_two]
    have : √2 * B ≤ 2 * B := mul_le_mul_of_nonneg_right (by nlinarith [Real.one_lt_sqrt_two]) hB0
    linarith
  have hden : 0 < c ^ 2 * m ^ 2 * s ^ 2 := by positivity
  calc 8 / 3 * (A / √2 + √2 * B) / (c ^ 2 * m ^ 2 * (2 * s) ^ 2)
      = 8 / 3 * (A / √2 + √2 * B) / (c ^ 2 * m ^ 2 * s ^ 2) / 4 := by ring
    _ ≤ 8 / 3 * (2 * (A + B)) / (c ^ 2 * m ^ 2 * s ^ 2) / 4 := by
        apply div_le_div_of_nonneg_right _ (by norm_num)
        apply div_le_div_of_nonneg_right _ hden.le
        exact mul_le_mul_of_nonneg_left hle (by norm_num)
    _ = 8 / 3 * (A + B) / (c ^ 2 * m ^ 2 * s ^ 2) / 2 := by ring

/-- **One mode on `[s₀, 2^J s₀]`**: the dyadic pieces sum to at most `2P(s₀)`. -/
theorem mode_le {c χ m w s₀ G Y V : ℝ} {ψ u y v : ℝ → ℝ} (J : ℕ)
    (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχ : χ < c ^ 2) (hm : 0 < m) (hms : 2 ≤ m * s₀) (hw : 0 ≤ w)
    (hgap : w + χ ≤ c ^ 2) (hG0 : 0 ≤ G) (hY : 0 ≤ Y) (hV : 0 ≤ V)
    (hψ : ∀ ξ ∈ Icc (m * s₀) (m * (2 ^ J * s₀)), HasDerivAt ψ (u ξ / pP ξ) ξ)
    (hu : ∀ ξ ∈ Icc (m * s₀) (m * (2 ^ J * s₀)), HasDerivAt u (-(qP c χ ξ * ψ ξ)) ξ)
    (hG : ∀ ξ ∈ Icc (m * s₀) (m * (2 ^ J * s₀)), energy (aP c χ) ψ u ξ ≤ G)
    (hy : ∀ τ ∈ Icc s₀ (2 ^ J * s₀), HasDerivAt y (v τ / τ ^ 2) τ)
    (hv : ∀ τ ∈ Icc s₀ (2 ^ J * s₀), HasDerivAt v (-(w * y τ)) τ)
    (hyb : ∀ τ ∈ Icc s₀ (2 ^ J * s₀), |y τ| ≤ Y / √τ) (hvb : ∀ τ ∈ Icc s₀ (2 ^ J * s₀), |v τ| ≤ V * √τ) :
    |∫ τ in s₀..2 ^ J * s₀, ψ (m * τ) * y τ| ≤ 2 * P c χ m G Y V s₀ := by
  have hs₀ : 0 < s₀ := by by_contra h; push_neg at h; nlinarith
  set S := 2 ^ J * s₀ with hS
  have hpow : ∀ j : ℕ, 1 ≤ (2 : ℝ) ^ j := fun j => one_le_pow₀ (by norm_num)
  have hsS : s₀ ≤ S := by rw [hS]; nlinarith [hpow J]
  -- continuity of the integrand on `[s₀, S]`
  have hcont : ContinuousOn (fun τ => ψ (m * τ) * y τ) (Icc s₀ S) := by
    intro τ hτ
    have hmτ : m * τ ∈ Icc (m * s₀) (m * S) :=
      ⟨mul_le_mul_of_nonneg_left hτ.1 hm.le, mul_le_mul_of_nonneg_left hτ.2 hm.le⟩
    have h1 : ContinuousAt (fun r => ψ (m * r)) τ :=
      (hψ _ hmτ).continuousAt.comp (continuous_const.mul continuous_id).continuousAt
    exact (h1.mul (hy τ hτ).continuousAt).continuousWithinAt
  have hint : ∀ a b, s₀ ≤ a → a ≤ b → b ≤ S →
      IntervalIntegrable (fun τ => ψ (m * τ) * y τ) MeasureTheory.volume a b := fun a b ha hab hb =>
    (hcont.mono (Icc_subset_Icc ha hb)).intervalIntegrable_of_Icc hab
  -- the telescoping claim
  have claim : ∀ j : ℕ, j ≤ J →
      |∫ τ in s₀..2 ^ j * s₀, ψ (m * τ) * y τ| + 2 * P c χ m G Y V (2 ^ j * s₀) ≤ 2 * P c χ m G Y V s₀ := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have ih := ih (by omega)
      set s := 2 ^ j * s₀ with hsdef
      have hs0 : 0 < s := by positivity
      have hss : s₀ ≤ s := by rw [hsdef]; nlinarith [hpow j]
      have h2s : 2 * s ≤ S := by
        rw [hsdef, hS, ← mul_assoc, ← pow_succ']
        exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj) hs₀.le
      have e2 : (2 : ℝ) ^ (j + 1) * s₀ = 2 * s := by rw [hsdef, pow_succ]; ring
      rw [e2]
      have hms' : 2 ≤ m * s := hms.trans (mul_le_mul_of_nonneg_left hss hm.le)
      have sub1 : ∀ ξ ∈ Icc (m * s) (m * (2 * s)), ξ ∈ Icc (m * s₀) (m * S) := fun ξ hξ =>
        ⟨(mul_le_mul_of_nonneg_left hss hm.le).trans hξ.1, hξ.2.trans (mul_le_mul_of_nonneg_left h2s hm.le)⟩
      have sub2 : ∀ τ ∈ Icc s (2 * s), τ ∈ Icc s₀ S := fun τ hτ => ⟨hss.trans hτ.1, hτ.2.trans h2s⟩
      have hp := Cvs.Prolate.Mellin.ModeMellinDyadicPiece.piece_le hc hχ0 hχ hm hms' hw hgap hY hV
        (fun ξ hξ => hψ ξ (sub1 ξ hξ)) (fun ξ hξ => hu ξ (sub1 ξ hξ)) (fun ξ hξ => hG ξ (sub1 ξ hξ))
        (fun τ hτ => hy τ (sub2 τ hτ)) (fun τ hτ => hv τ (sub2 τ hτ))
        (fun τ hτ => hyb τ (sub2 τ hτ)) (fun τ hτ => hvb τ (sub2 τ hτ))
      have hadd := intervalIntegral.integral_add_adjacent_intervals (hint s₀ s le_rfl hss (by linarith))
        (hint s (2 * s) hss (by linarith) h2s)
      rw [← hadd]
      have hhalf := P_two_mul (χ := χ) (m := m) (G := G) (Y := Y) (V := V) hc hχ hm hs0 hG0 hY hV
      have htri := abs_add_le (∫ τ in s₀..s, ψ (m * τ) * y τ) (∫ τ in s..2 * s, ψ (m * τ) * y τ)
      have hpP : P c χ m G Y V s = 8 / 3 * (V * √(G / (√3 / 2 * √(c ^ 2 - χ) * s)) / m
          + Y * √(2 * c * G * s)) / (c ^ 2 * m ^ 2 * s ^ 2) := rfl
      rw [← hpP] at hp
      linarith
  have := claim J le_rfl
  have hP0 : 0 ≤ P c χ m G Y V S := by
    unfold P
    have : 0 < √3 / 2 * √(c ^ 2 - χ) := by have : 0 < c ^ 2 - χ := by linarith
                                           positivity
    have : 0 < S := by linarith
    positivity
  linarith

end Cvs.Prolate.Mellin.ModeMellinDyadicRange
