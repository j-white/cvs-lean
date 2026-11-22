import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# A ratio of Gamma values along integer steps

For `Re s > 0`, `Γ(s + n + 1) = Γ(s) ∏_{j ≤ n} (s + j) = Γ(s) n^s n!/Γ_n(s)` with Euler's sequence `Γ_n(s) → Γ(s)`.
Hence for `Re s > 0` and `Re(s + a) > 0`, `Γ(s + a + n + 1)/(Γ(s + n + 1) n^a) → 1` as `n → ∞`.
-/

noncomputable section

open Complex Filter Topology Finset

namespace Cvs.Upstream.GammaIntegerStepRatio

theorem Gamma_add_succ {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    Gamma (s + (n + 1 : ℕ)) = Gamma s * ∏ j ∈ range (n + 1), (s + j) := by
  induction n with
  | zero =>
    simp only [zero_add, Nat.cast_one, range_one, prod_singleton, Nat.cast_zero, add_zero]
    rw [Gamma_add_one s (fun h => by rw [h] at hs; simp at hs)]; ring
  | succ n ih =>
    rw [prod_range_succ, ← mul_assoc, ← ih]
    have hne : s + ((n + 1 : ℕ) : ℂ) ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this; have := n.cast_nonneg (α := ℝ); linarith
    rw [show s + ((n + 1 + 1 : ℕ) : ℂ) = s + ((n + 1 : ℕ) : ℂ) + 1 by push_cast; ring, Gamma_add_one _ hne]
    push_cast; ring

theorem prod_eq_GammaSeq {s : ℂ} (hs : 0 < s.re) {n : ℕ} (hn : n ≠ 0) :
    ∏ j ∈ range (n + 1), (s + j) = (n : ℂ) ^ s * (Nat.factorial n : ℂ) / GammaSeq s n := by
  have hp : ∏ j ∈ range (n + 1), (s + j) ≠ 0 := by
    rw [prod_ne_zero_iff]; intro j _ h
    have := congrArg Complex.re h; simp at this; have := j.cast_nonneg (α := ℝ); linarith
  have hnum : (n : ℂ) ^ s * (Nat.factorial n : ℂ) ≠ 0 := by
    refine mul_ne_zero ?_ (by exact_mod_cast Nat.factorial_ne_zero n)
    exact (cpow_ne_zero_iff_of_exponent_ne_zero (fun h => by rw [h] at hs; simp at hs)).mpr
      (by exact_mod_cast hn)
  unfold GammaSeq
  field_simp
  rw [div_self hnum]

/-- **`Γ(s + a + n + 1)/(Γ(s + n + 1) n^a) → 1`.** -/
theorem tendsto_Gamma_ratio {s a : ℂ} (hs : 0 < s.re) (hsa : 0 < (s + a).re) :
    Tendsto (fun n : ℕ => Gamma (s + a + (n + 1 : ℕ)) / (Gamma (s + (n + 1 : ℕ)) * (n : ℂ) ^ a))
      atTop (𝓝 1) := by
  have hG0 := Gamma_ne_zero_of_re_pos hs
  have hGa := Gamma_ne_zero_of_re_pos hsa
  have h1 := GammaSeq_tendsto_Gamma s
  have h2 := GammaSeq_tendsto_Gamma (s + a)
  have hlim : Tendsto (fun n : ℕ => Gamma (s + a) / Gamma s * (GammaSeq s n / GammaSeq (s + a) n))
      atTop (𝓝 (Gamma (s + a) / Gamma s * (Gamma s / Gamma (s + a)))) :=
    tendsto_const_nhds.mul (h1.div h2 hGa)
  rw [show Gamma (s + a) / Gamma s * (Gamma s / Gamma (s + a)) = 1 by field_simp] at hlim
  refine hlim.congr' ?_
  have hev : ∀ᶠ n : ℕ in atTop, GammaSeq s n ≠ 0 ∧ GammaSeq (s + a) n ≠ 0 :=
    (h1.eventually_ne hG0).and (h2.eventually_ne hGa)
  filter_upwards [hev, eventually_ne_atTop 0] with n ⟨hs0, hsa0⟩ hn
  rw [Gamma_add_succ hsa, Gamma_add_succ hs, prod_eq_GammaSeq hsa hn, prod_eq_GammaSeq hs hn]
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hpow : (n : ℂ) ^ (s + a) = (n : ℂ) ^ s * (n : ℂ) ^ a := cpow_add _ _ hn'
  have hns : (n : ℂ) ^ s ≠ 0 := (cpow_ne_zero_iff_of_exponent_ne_zero
    (fun h => by rw [h] at hs; simp at hs)).mpr hn'
  have hna : (n : ℂ) ^ a ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hpow
    exact (cpow_ne_zero_iff_of_exponent_ne_zero (fun h => by rw [h] at hsa; simp at hsa)).mpr hn' hpow
  have hf : (Nat.factorial n : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  rw [hpow]
  field_simp

end Cvs.Upstream.GammaIntegerStepRatio
