import Mathlib
import Cvs.Xi.EImageWindowPoisson

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Windows of `C¹` profiles are tame without a mean condition

`|E_G(θ)| ≤ sup_{[0,1]}|G|` on `θ > 0`, so `k_G` and `R_a k_G` are tame on `[a, 1]` for every `G ∈ C¹[0, 1]`, with
no condition on `∫₀¹ G`. For `G` continuous on `[−1, 1]` and `C¹` on `[0, 1]` the defect profile `G − ψ_G/κ` is
`C¹` on `[0, 1]`, so `R_a k_{G − ψ_G/κ}` is tame. For the spine: `R_{1/x}W_{D̃_a}`, `R_{1/x}W_{D_a}` and the leakage
piece `1_{[1/x, 1]}t_{G̃_a} = Ĩ_a + R_{1/x}W_{D̃_a}` are tame on `[1/x, 1]` at `80 ≤ 2πx`.
-/

noncomputable section

open Real Set MeasureTheory Filter

namespace Cvs.Xi.WindowCOneProfileTame

open Cvs.Xi.EImageWindowPoisson (window eimage)
open Cvs.L2a.AngularProlateTailPositive (psi)

/-- **The E-image is bounded by the profile**: `|E_G(θ)| ≤ M` for `θ > 0` when `|G| ≤ M` on `[0, 1]`. -/
theorem abs_eimage_le {a : ℝ} (ha : 0 < a) {G : ℝ → ℝ} {M : ℝ} (hM : ∀ u ∈ Icc (0 : ℝ) 1, |G u| ≤ M)
    {θ : ℝ} (hθ : 0 < θ) : |eimage a G θ| ≤ M := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 ⟨le_rfl, zero_le_one⟩)
  have hta : 0 ≤ θ / a := by positivity
  have hpt : ∀ n ∈ Finset.Icc 1 ⌊θ / a⌋₊, |G (n * a / θ)| ≤ M := by
    intro n hn
    have hnθ : (n : ℝ) ≤ θ / a := (Nat.le_floor_iff hta).mp (Finset.mem_Icc.mp hn).2
    refine hM _ ⟨by positivity, ?_⟩
    rw [div_le_one hθ]
    rwa [le_div_iff₀ ha] at hnθ
  have hsum : |∑ n ∈ Finset.Icc 1 ⌊θ / a⌋₊, G (n * a / θ)| ≤ ⌊θ / a⌋₊ * M := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum hpt).trans ?_
    rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
  have hfl : (⌊θ / a⌋₊ : ℝ) * (a / θ) ≤ 1 := by
    have := Nat.floor_le hta
    rw [← le_div_iff₀ (by positivity : 0 < a / θ)]
    calc (⌊θ / a⌋₊ : ℝ) ≤ θ / a := this
      _ = 1 / (a / θ) := by field_simp
  unfold eimage
  rw [abs_mul, abs_of_pos (by positivity : 0 < a / θ)]
  calc a / θ * |∑ n ∈ Finset.Icc 1 ⌊θ / a⌋₊, G (n * a / θ)| ≤ a / θ * (⌊θ / a⌋₊ * M) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (⌊θ / a⌋₊ * (a / θ)) * M := by ring
    _ ≤ 1 * M := mul_le_mul_of_nonneg_right hfl hM0
    _ = M := one_mul M

end Cvs.Xi.WindowCOneProfileTame
