import Mathlib

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The tail of `M` modes on `(1, b]`

`F(θ) = Σ_{m ≤ M} ψ(mθ)` on `(1, b]`, zero elsewhere. Against a weight, `∫_{θ>1} F g = Σ_m ∫_1^b ψ(m·) g`; its prime
terms split into mode pairs, for two tails `F₁, F₂` of `ψ₁, ψ₂`:
`∫_{θ>1} F₁(θ) F₂(kθ) = Σ_{m, m'} ∫_1^{b/k} ψ₁(mθ) ψ₂(m'kθ)` for `1 ≤ k ≤ b`.
-/

namespace Cvs.L2a.TailOfModes

open Real Set MeasureTheory

/-- The tail of `M` modes on `(1, b]`. -/
noncomputable def tailF (ψ : ℝ → ℝ) (M : ℕ) (b θ : ℝ) : ℝ :=
  Set.indicator (Ioc 1 b) (fun θ => ∑ m ∈ Finset.Icc 1 M, ψ (m * θ)) θ

theorem tailF_zero (ψ : ℝ → ℝ) (M : ℕ) (b : ℝ) : ∀ θ ≤ 1, tailF ψ M b θ = 0 := fun θ h => by
  unfold tailF; rw [indicator_of_notMem]; simp only [mem_Ioc, not_and, not_le]; intro h1; linarith

/-- **The tail against a weight** is the sum of its modes' integrals. -/
theorem integral_tailF_mul (ψ g : ℝ → ℝ) (M : ℕ) {b : ℝ} (hb : 1 ≤ b)
    (hcont : ∀ m ∈ Finset.Icc 1 M, ContinuousOn (fun θ => ψ (m * θ) * g θ) (Icc 1 b)) :
    ∫ θ in Ioi 1, tailF ψ M b θ * g θ = ∑ m ∈ Finset.Icc 1 M, ∫ θ in (1 : ℝ)..b, ψ (m * θ) * g θ := by
  have e1 : ∫ θ in Ioi 1, tailF ψ M b θ * g θ = ∫ θ in Ioc 1 b, (∑ m ∈ Finset.Icc 1 M, ψ (m * θ)) * g θ := by
    have hsub : Ioc (1 : ℝ) b ⊆ Ioi 1 := fun θ hθ => hθ.1
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi hsub
      (fun θ hθ => by unfold tailF; rw [indicator_of_notMem hθ.2, zero_mul])]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro θ hθ; simp only; unfold tailF; rw [indicator_of_mem hθ]
  rw [e1, ← intervalIntegral.integral_of_le hb]
  simp_rw [Finset.sum_mul]
  rw [intervalIntegral.integral_finsetSum]
  intro m hm
  exact (hcont m hm).intervalIntegrable_of_Icc hb

/-- **The prime terms split into mode pairs**, for two tails. -/
theorem integral_tailF_pair (ψ₁ ψ₂ : ℝ → ℝ) (M : ℕ) {b k : ℝ} (hk : 1 ≤ k) (hkb : k ≤ b)
    (hcont₁ : ContinuousOn ψ₁ (Icc 1 (M * b))) (hcont₂ : ContinuousOn ψ₂ (Icc 1 (M * b))) :
    ∫ θ in Ioi 1, tailF ψ₁ M b θ * tailF ψ₂ M b (k * θ)
      = ∑ m ∈ Finset.Icc 1 M, ∑ m' ∈ Finset.Icc 1 M, ∫ θ in (1 : ℝ)..b / k, ψ₁ (m * θ) * ψ₂ (m' * (k * θ)) := by
  have hk0 : 0 < k := by linarith
  have hbk : 1 ≤ b / k := by rw [le_div_iff₀ hk0]; linarith
  have hbk' : b / k ≤ b := div_le_self (by linarith) hk
  have e1 : ∫ θ in Ioi 1, tailF ψ₁ M b θ * tailF ψ₂ M b (k * θ)
      = ∫ θ in Ioc 1 (b / k), (∑ m ∈ Finset.Icc 1 M, ψ₁ (m * θ)) * ∑ m' ∈ Finset.Icc 1 M, ψ₂ (m' * (k * θ)) := by
    have hsub : Ioc (1 : ℝ) (b / k) ⊆ Ioi 1 := fun θ hθ => hθ.1
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi hsub (fun θ hθ => by
      have hθ1 : 1 < θ := hθ.1
      have hn : k * θ ∉ Ioc 1 b := by
        intro h; apply hθ.2; exact ⟨hθ1, by rw [le_div_iff₀' hk0]; exact h.2⟩
      unfold tailF; rw [indicator_of_notMem hn, mul_zero])]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro θ hθ
    have h1 : θ ∈ Ioc 1 b := ⟨hθ.1, hθ.2.trans hbk'⟩
    have h2 : k * θ ∈ Ioc 1 b := ⟨by nlinarith [hθ.1], by rw [← le_div_iff₀' hk0]; exact hθ.2⟩
    simp only; unfold tailF; rw [indicator_of_mem h1, indicator_of_mem h2]
  rw [e1, ← intervalIntegral.integral_of_le hbk]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl; intro m hm
    rw [intervalIntegral.integral_finsetSum]
    intro m' hm'
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
    have hmM : (m : ℝ) ≤ M := by exact_mod_cast (Finset.mem_Icc.mp hm).2
    have hm1' : (1 : ℝ) ≤ m' := by exact_mod_cast (Finset.mem_Icc.mp hm').1
    have hmM' : (m' : ℝ) ≤ M := by exact_mod_cast (Finset.mem_Icc.mp hm').2
    apply ContinuousOn.intervalIntegrable_of_Icc hbk
    apply ContinuousOn.mul
    · exact hcont₁.comp (continuousOn_const.mul continuousOn_id) (fun θ hθ =>
        ⟨by nlinarith [hθ.1], by have := hθ.2.trans hbk'; nlinarith⟩)
    · exact hcont₂.comp (continuousOn_const.mul (continuousOn_const.mul continuousOn_id)) (fun θ hθ =>
        ⟨one_le_mul_of_one_le_of_one_le hm1' (one_le_mul_of_one_le_of_one_le hk hθ.1), by
          have : k * θ ≤ b := by rw [← le_div_iff₀' hk0]; exact hθ.2
          nlinarith⟩)
  · intro m hm
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
    have hmM : (m : ℝ) ≤ M := by exact_mod_cast (Finset.mem_Icc.mp hm).2
    apply ContinuousOn.intervalIntegrable_of_Icc hbk
    apply continuousOn_finsetSum; intro m' hm'
    have hm1' : (1 : ℝ) ≤ m' := by exact_mod_cast (Finset.mem_Icc.mp hm').1
    have hmM' : (m' : ℝ) ≤ M := by exact_mod_cast (Finset.mem_Icc.mp hm').2
    apply ContinuousOn.mul
    · exact hcont₁.comp (continuousOn_const.mul continuousOn_id) (fun θ hθ =>
        ⟨by nlinarith [hθ.1], by have := hθ.2.trans hbk'; nlinarith⟩)
    · exact hcont₂.comp (continuousOn_const.mul (continuousOn_const.mul continuousOn_id)) (fun θ hθ =>
        ⟨one_le_mul_of_one_le_of_one_le hm1' (one_le_mul_of_one_le_of_one_le hk hθ.1), by
          have : k * θ ≤ b := by rw [← le_div_iff₀' hk0]; exact hθ.2
          nlinarith⟩)

end Cvs.L2a.TailOfModes
