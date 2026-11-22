import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.ZetaValues
import Cvs.L2a.NonstationaryPairsOneShift
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.Mellin.FirstModeMellinEdge
import Cvs.Prolate.Mellin.ModeMellinDyadicRange

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The first `M` modes' Mellin transform below the gap, summed

`|Σ_{m ≤ M} ∫_1^b ψ(mt) y(t) dt| ≤ η|ψ(1)|Y + 8√2|ψ(1)|V/(cσ) + 32√2√(cG)Y/σ² + 2P_1(2)
+ (π²/6)(16/3)(V√(G/α) + Y√(2cG))/c²`, `b = 2^{J+1}`, for every `M`: modes `m ≥ 2` are Cvs.Prolate.Mellin.ModeMellinDyadicRange at `s₀ = 1`.
-/

namespace Cvs.Prolate.Mellin.ModesMellinSummed

open Real Set Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval

/-- `P_m(1) ≤ (8/3)(V√(G/α) + Y√(2cG))/(c² m²)`. -/
theorem P_one_le {c χ m G Y V : ℝ} (hc : 0 < c) (hχ : χ < c ^ 2) (hm : 1 ≤ m) (hG : 0 ≤ G) (hY : 0 ≤ Y)
    (hV : 0 ≤ V) :
    Cvs.Prolate.Mellin.ModeMellinDyadicRange.P c χ m G Y V 1
      ≤ 8 / 3 * (V * √(G / (√3 / 2 * √(c ^ 2 - χ))) + Y * √(2 * c * G)) / c ^ 2 * (1 / m ^ 2) := by
  unfold Cvs.Prolate.Mellin.ModeMellinDyadicRange.P
  have hm0 : 0 < m := by linarith
  simp only [mul_one, one_pow]
  have h1 : V * √(G / (√3 / 2 * √(c ^ 2 - χ))) / m ≤ V * √(G / (√3 / 2 * √(c ^ 2 - χ))) :=
    div_le_self (by positivity) hm
  calc 8 / 3 * (V * √(G / (√3 / 2 * √(c ^ 2 - χ))) / m + Y * √(2 * c * G)) / (c ^ 2 * m ^ 2)
      ≤ 8 / 3 * (V * √(G / (√3 / 2 * √(c ^ 2 - χ))) + Y * √(2 * c * G)) / (c ^ 2 * m ^ 2) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_left _ (by norm_num); linarith
    _ = _ := by field_simp

/-- **The first `M` modes, summed.** -/
theorem modes_le {c χ w G Y V η : ℝ} {ψ u y v : ℝ → ℝ} (J M : ℕ)
    (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχ : χ < c ^ 2) (hw : 0 ≤ w) (hgap : 2 * w ≤ c ^ 2 - χ)
    (hG0 : 0 ≤ G) (hY : 0 ≤ Y) (hV : 0 ≤ V) (hη : 0 < η) (hηθ : 1 + η ≤ √(1 + √(c ^ 2 - χ) / c))
    (hψ : ∀ ξ ∈ Ioc 1 ((M : ℝ) * 2 ^ (J + 1)), HasDerivAt ψ (u ξ / pP ξ) ξ)
    (hu : ∀ ξ ∈ Ioc 1 ((M : ℝ) * 2 ^ (J + 1)), HasDerivAt u (-(qP c χ ξ * ψ ξ)) ξ)
    (hG : ∀ ξ ∈ Ioc 1 ((M : ℝ) * 2 ^ (J + 1)), energy (aP c χ) ψ u ξ ≤ G)
    (hcont : ContinuousOn ψ (Icc (1 : ℝ) (2 ^ (J + 1)))) (hedge : ∀ ξ ∈ Icc (1 : ℝ) 2, |ψ ξ| ≤ |ψ 1|)
    (hy : ∀ τ ∈ Icc (1 : ℝ) (2 ^ (J + 1)), HasDerivAt y (v τ / τ ^ 2) τ)
    (hv : ∀ τ ∈ Icc (1 : ℝ) (2 ^ (J + 1)), HasDerivAt v (-(w * y τ)) τ)
    (hyb : ∀ τ ∈ Icc (1 : ℝ) (2 ^ (J + 1)), |y τ| ≤ Y / √τ)
    (hvb : ∀ τ ∈ Icc (1 : ℝ) (2 ^ (J + 1)), |v τ| ≤ V * √τ) :
    |∑ m ∈ Finset.Icc 1 M, ∫ τ in (1 : ℝ)..2 ^ (J + 1), ψ (m * τ) * y τ|
      ≤ η * |ψ 1| * Y + 8 * √2 * |ψ 1| * V / (c * √(c ^ 2 - χ)) + 32 * √2 * √(c * G) * Y / (c ^ 2 - χ)
        + 2 * Cvs.Prolate.Mellin.ModeMellinDyadicRange.P c χ 1 G Y V 2
        + π ^ 2 / 6 * (16 / 3 * (V * √(G / (√3 / 2 * √(c ^ 2 - χ))) + Y * √(2 * c * G)) / c ^ 2) := by
  set R := 8 / 3 * (V * √(G / (√3 / 2 * √(c ^ 2 - χ))) + Y * √(2 * c * G)) / c ^ 2 with hR
  have hR0 : 0 ≤ R := by positivity
  set B1 := η * |ψ 1| * Y + 8 * √2 * |ψ 1| * V / (c * √(c ^ 2 - χ)) + 32 * √2 * √(c * G) * Y / (c ^ 2 - χ)
      + 2 * Cvs.Prolate.Mellin.ModeMellinDyadicRange.P c χ 1 G Y V 2 with hB1
  have hpow : (1 : ℝ) ≤ 2 ^ (J + 1) := one_le_pow₀ (by norm_num)
  -- every mode is bounded
  have hmode : ∀ m ∈ Finset.Icc 1 M, |∫ τ in (1 : ℝ)..2 ^ (J + 1), ψ (m * τ) * y τ|
      ≤ (if m = 1 then B1 else 0) + 2 * R * (1 / (m : ℝ) ^ 2) := by
    intro m hm
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    have hmM : (m : ℝ) ≤ M := by exact_mod_cast (Finset.mem_Icc.mp hm).2
    have hm1' : (1 : ℝ) ≤ m := by exact_mod_cast hm1
    have hsub : ∀ ξ : ℝ, 1 < ξ → ξ ≤ (m : ℝ) * 2 ^ (J + 1) → ξ ∈ Ioc 1 ((M : ℝ) * 2 ^ (J + 1)) := fun ξ h1 h2 =>
      ⟨h1, h2.trans (mul_le_mul_of_nonneg_right hmM (by positivity))⟩
    by_cases h1 : m = 1
    · subst h1
      simp only [if_true, Nat.cast_one, one_mul]
      have e : (2 : ℝ) ^ (J + 1) = 2 ^ J * 2 := pow_succ 2 J
      have key := Cvs.Prolate.Mellin.FirstModeMellinEdge.first_mode_le (ψ := ψ) (u := u) (y := y) (v := v) J hc hχ0 hχ hw hgap
        hG0 hY hV hη hηθ
        (fun ξ hξ => hψ ξ (hsub ξ hξ.1 (by rw [Nat.cast_one, one_mul, e]; exact hξ.2)))
        (fun ξ hξ => hu ξ (hsub ξ hξ.1 (by rw [Nat.cast_one, one_mul, e]; exact hξ.2)))
        (fun ξ hξ => hG ξ (hsub ξ hξ.1 (by rw [Nat.cast_one, one_mul, e]; exact hξ.2)))
        (by rw [← e]; exact hcont) hedge (by rw [← e]; exact hy) (by rw [← e]; exact hv)
        (by rw [← e]; exact hyb) (by rw [← e]; exact hvb)
      rw [e]
      have : 0 ≤ 2 * R * (1 / (1 : ℝ) ^ 2) := by positivity
      linarith
    · have hm2 : (2 : ℝ) ≤ m := by
        have : 2 ≤ m := by omega
        exact_mod_cast this
      rw [if_neg h1, zero_add]
      have key := Cvs.Prolate.Mellin.ModeMellinDyadicRange.mode_le (c := c) (χ := χ) (m := m) (w := w) (s₀ := 1) (G := G)
        (Y := Y) (V := V) (ψ := ψ) (u := u) (y := y) (v := v) (J + 1) hc hχ0 hχ (by linarith)
        (by linarith) hw (by linarith) hG0 hY hV
        (fun ξ hξ => hψ ξ (hsub ξ (by nlinarith [hξ.1]) (by have := hξ.2; rw [mul_one] at this; exact this)))
        (fun ξ hξ => hu ξ (hsub ξ (by nlinarith [hξ.1]) (by have := hξ.2; rw [mul_one] at this; exact this)))
        (fun ξ hξ => hG ξ (hsub ξ (by nlinarith [hξ.1]) (by have := hξ.2; rw [mul_one] at this; exact this)))
        (by rw [mul_one]; exact hy) (by rw [mul_one]; exact hv) (by rw [mul_one]; exact hyb)
        (by rw [mul_one]; exact hvb)
      rw [mul_one] at key
      have hP := P_one_le (χ := χ) (G := G) (Y := Y) (V := V) hc hχ hm1' hG0 hY hV
      rw [← hR] at hP
      linarith
  calc |∑ m ∈ Finset.Icc 1 M, ∫ τ in (1 : ℝ)..2 ^ (J + 1), ψ (m * τ) * y τ|
      ≤ ∑ m ∈ Finset.Icc 1 M, |∫ τ in (1 : ℝ)..2 ^ (J + 1), ψ (m * τ) * y τ| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ Finset.Icc 1 M, ((if m = 1 then B1 else 0) + 2 * R * (1 / (m : ℝ) ^ 2)) := Finset.sum_le_sum hmode
    _ = (∑ m ∈ Finset.Icc 1 M, if m = 1 then B1 else 0) + 2 * R * ∑ m ∈ Finset.Icc 1 M, 1 / (m : ℝ) ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ B1 + 2 * R * (π ^ 2 / 6) := by
        apply add_le_add
        · rw [Finset.sum_ite_eq']
          split_ifs
          · exact le_rfl
          · rw [hB1]
            have : 0 ≤ Cvs.Prolate.Mellin.ModeMellinDyadicRange.P c χ 1 G Y V 2 := by
              unfold Cvs.Prolate.Mellin.ModeMellinDyadicRange.P
              have : 0 < c ^ 2 - χ := by linarith
              positivity
            have : 0 < c ^ 2 - χ := by linarith
            positivity
        · exact mul_le_mul_of_nonneg_left (Cvs.L2a.NonstationaryPairsOneShift.sum_inv_sq_le M) (by positivity)
    _ = _ := by rw [hB1, hR]; ring

end Cvs.Prolate.Mellin.ModesMellinSummed
