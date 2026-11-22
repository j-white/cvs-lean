import Mathlib
import Cvs.L2a.TailLogScaleTest
import Cvs.L2a.TailModesFromProlateEquation
import Cvs.L2a.TailOfModes
import Cvs.Prolate.SlepianCommutingRelation
import Cvs.WeilForm.PrimePowerIndexed
import Cvs.WeilForm.SelfConvolutionFunctional

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# L2a for the tail of an angular prolate

If `g` solves the angular equation `(1 − s²)g'' − 2sg' − c²s²g + χg = 0` on `[−1, 1]`, its cosine transform
`ψ(ξ) = ∫_{−1}^{1} g(s) cos(cξs) ds` solves the radial one on every `[1, Ξ]` (Cvs.Prolate.SlepianCommutingRelation), so Cvs.L2a.TailModesFromProlateEquation applies: for
`0 ≤ χ ≤ c√c` and `ψ(1) ≠ 0`, the Weil form of every tail of `M` modes of `ψ` is eventually positive.
-/

namespace Cvs.L2a.AngularProlateTailPositive

open Real Set Filter Cvs.L2a.TailLogScaleTest Cvs.L2a.TailOfModes Cvs.Prolate.SlepianCommutingRelation

/-- The finite cosine transform `ψ(ξ) = ∫_{−1}^{1} g(s) cos(cξs) ds`. -/
noncomputable def psi (c : ℝ) (g : ℝ → ℝ) (ξ : ℝ) : ℝ := kint g (fun ξ s => cos (c * ξ * s)) ξ

/-- **The cosine transform is a radial solution with its derivatives as kernel integrals.** -/
theorem psi_system {g g₁ g₂ : ℝ → ℝ} {c χ : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0) :
    (∀ ξ, HasDerivAt (psi c g) (kint g (fun ξ s => -(c * s * sin (c * ξ * s))) ξ) ξ)
      ∧ (∀ ξ, HasDerivAt (kint g (fun ξ s => -(c * s * sin (c * ξ * s))))
          (kint g (fun ξ s => -(c ^ 2 * s ^ 2 * cos (c * ξ * s))) ξ) ξ)
      ∧ (∀ ξ, (ξ ^ 2 - 1) * kint g (fun ξ s => -(c ^ 2 * s ^ 2 * cos (c * ξ * s))) ξ
          + 2 * ξ * kint g (fun ξ s => -(c * s * sin (c * ξ * s))) ξ + (c ^ 2 * ξ ^ 2 - χ) * psi c g ξ = 0) := by
  have hgc : ContinuousOn g (uIcc (-1) 1) := fun s hs => (hg s hs).continuousAt.continuousWithinAt
  refine ⟨fun ξ => ?_, fun ξ => ?_, fun ξ => radial_ode hg hg₁ hg₂c hang ξ⟩
  · apply hasDerivAt_kint (C := |c|) hgc (fun s => by fun_prop) (fun ξ => by fun_prop) (fun ξ => by fun_prop)
    · intro ξ s
      have := ((hasDerivAt_id ξ).const_mul c |>.mul_const s).cos
      refine this.congr_deriv ?_; simp; ring
    · intro ξ s hs
      rw [abs_neg, abs_mul, abs_mul]
      calc |c| * |s| * |sin (c * ξ * s)| ≤ |c| * 1 * 1 :=
            mul_le_mul (mul_le_mul_of_nonneg_left hs (abs_nonneg c)) (abs_sin_le_one _) (abs_nonneg _) (by positivity)
        _ = |c| := by ring
  · apply hasDerivAt_kint (C := c ^ 2) hgc (fun s => by fun_prop) (fun ξ => by fun_prop) (fun ξ => by fun_prop)
    · intro ξ s
      have := (((hasDerivAt_id ξ).const_mul c |>.mul_const s).sin.const_mul (c * s)).neg
      refine this.congr_deriv ?_; simp; ring
    · intro ξ s hs
      rw [abs_neg, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg c), abs_of_nonneg (sq_nonneg s)]
      have hs2 : s ^ 2 ≤ 1 := by nlinarith [abs_nonneg s, sq_abs s]
      calc c ^ 2 * s ^ 2 * |cos (c * ξ * s)| ≤ c ^ 2 * 1 * 1 :=
            mul_le_mul (mul_le_mul_of_nonneg_left hs2 (sq_nonneg c)) (abs_cos_le_one _) (abs_nonneg _) (by positivity)
        _ = c ^ 2 := by ring

/-- **L2a for the tail of an angular prolate.** -/
theorem weilForm_eventually_pos (Kf : ℕ) (hKf : 1 ≤ Kf) :
    ∀ᶠ c in atTop, ∀ (χ Ξ : ℝ) (g g₁ g₂ : ℝ → ℝ) (P R N M J : ℕ),
      0 ≤ χ → χ ≤ c * √c →
      (∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) → (∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) →
      ContinuousOn g₂ (uIcc (-1) 1) →
      (∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0) →
      psi c g 1 ≠ 0 →
      1 ≤ J → 1 ≤ M → (M : ℝ) * 2 ^ (J + 1) ≤ Ξ →
      Cvs.WeilForm.PrimePowerIndexed.primePowIndex P R ⊆ Finset.Icc 2 N → (N : ℝ) + 2 ≤ 2 ^ (J + 1) →
      0 < Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (logScale (tailF (psi c g) M (2 ^ (J + 1)))) := by
  filter_upwards [Cvs.L2a.TailModesFromProlateEquation.weilForm_tailF_eventually_pos Kf hKf] with c hc
  intro χ Ξ g g₁ g₂ P R N M J hχ0 hχs hg hg₁ hg₂c hang hψ1 hJ hM hΞ hidx hrb
  obtain ⟨h1, h2, h3⟩ := psi_system hg hg₁ hg₂c hang
  exact hc χ Ξ (psi c g) _ _ P R N M J hχ0 hχs (fun r _ => h1 r) (fun r _ => h2 r) (fun r _ => h3 r) hψ1
    hJ hM hΞ hidx hrb

end Cvs.L2a.AngularProlateTailPositive
