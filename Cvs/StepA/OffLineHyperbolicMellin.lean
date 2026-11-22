import Mathlib
import Cvs.L2a.WindowFormTailLimit

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The off-line functionals are hyperbolic Mellin transforms on the line

For `v` measurable, bounded, vanishing off `[a, 1]`, `s₀ = ½ + iγ` and `ρ = s₀ + δ`:
`β_ρ(v) = M[2 sinh(δ log θ) v](s₀)` and `α_ρ(v) = M[2 cosh(δ log θ) v](s₀)` exactly; `M[v]` has derivative
`M[v log θ]`, and with `D_γ(v) = 2 M[v log θ](s₀)`, `a = e^{−L}` and `N(v) = ∫ θ^{−1/2}|v|`:
`‖β_ρ(v) − δ D_γ(v)‖ ≤ (|δ|L)³/3 · cosh(δL) · N(v)` and `‖α_ρ(v) − 2M[v](s₀)‖ ≤ (δL)² cosh(δL) · N(v)`.
-/

noncomputable section

open MeasureTheory Real Set Complex ComplexConjugate Filter Asymptotics

namespace Cvs.StepA.OffLineHyperbolicMellin

open Cvs.WeilForm.ThetaSpaceParseval (mellinR)

/-- `v` is measurable, bounded and vanishes off `[a, 1]`, `0 < a`. -/
structure Win (v : ℝ → ℝ) (a : ℝ) : Prop where
  pos : 0 < a
  supp : ∀ θ ∉ Icc a 1, v θ = 0
  meas : Measurable v
  bdd : ∃ M, ∀ θ, |v θ| ≤ M

theorem win_of_tame {v : ℝ → ℝ} {a : ℝ} (h : Cvs.L2a.WindowFormTailLimit.Tame v a 1) : Win v a :=
  ⟨h.pos, h.supp, h.meas, h.bdd⟩

variable {v : ℝ → ℝ} {a : ℝ}

/-! ### Integrability -/

theorem integrableOn_mul (hv : Win v a) {h : ℝ → ℂ} (hh : ContinuousOn h (Icc a 1)) :
    IntegrableOn (fun θ => h θ * (v θ : ℂ)) (Ioi 0) := by
  obtain ⟨M, hM⟩ := hv.bdd
  have h1 : IntegrableOn (fun θ => h θ * (v θ : ℂ)) (Icc a 1) :=
    Integrable.mul_bdd (hh.integrableOn_compact isCompact_Icc)
      (Complex.measurable_ofReal.comp hv.meas).aestronglyMeasurable
      (ae_of_all _ fun θ => by rw [Complex.norm_real, Real.norm_eq_abs]; exact hM θ)
  exact h1.of_forall_sdiff_eq_zero measurableSet_Ioi fun θ hθ => by simp [hv.supp θ hθ.2]

theorem continuousOn_cpow (ha : 0 < a) (w : ℂ) : ContinuousOn (fun θ : ℝ => (θ : ℂ) ^ w) (Icc a 1) :=
  Complex.continuous_ofReal.continuousOn.cpow_const fun _ hθ =>
    Complex.ofReal_mem_slitPlane.2 (ha.trans_le hθ.1)

/-! ### The Mellin transform is differentiable, with derivative `M[v log θ]` -/

/-! ### The exact hyperbolic forms -/

/-! ### The derivative functional and the remainders -/

/-! ### The window `L¹` norm and the bounds -/

end Cvs.StepA.OffLineHyperbolicMellin
