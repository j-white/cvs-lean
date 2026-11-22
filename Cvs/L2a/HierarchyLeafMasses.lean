import Mathlib
import Cvs.Prolate.Gram.RungCombinationNormInterval

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The leaves of the hierarchy: a weighted pair integral by the masses

A weighted pair integral with `|σ| ≤ S` is at most `(S/2)(∫ f₁² + ∫ f₂²)` pointwise, and the norm of a dilated
combination `Σ b_iψ_i(m·)` on `[L, R]` with `mL ≥ 1` is at most `(1/m)Σ b_i² M_i` by the change of variable and
orthogonality at infinity (Cvs.Prolate.Gram.RungCombinationNormInterval). Together they bound every leaf of the project, and with `b_i = a_iχ_i^k` every level.
-/

namespace Cvs.L2a.HierarchyLeafMasses

open Real Set Finset intervalIntegral

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **The norm of a dilated combination by the masses**: for `1 ≤ mL ≤ mR`, `m > 0`,
`∫_L^R (Σ b_iψ_i(mθ))² ≤ (1/m) Σ b_i² M_i` under the orthogonality-at-infinity hypotheses of Cvs.Prolate.Gram.RungCombinationNormInterval. -/
theorem dilated_norm_le {L R m : ℝ} (hm : 0 < m) (hL : 1 ≤ m * L) (hLR : L ≤ R) (ψ : ι → ℝ → ℝ) (b : ι → ℝ)
    (K : ι → ι → ℝ) (Mm : ι → ℝ) (hcont : ∀ i, ContinuousOn (ψ i) (Ici 1))
    (hcross : ∀ i j, i ≠ j → ∀ t, m * R ≤ t → |∫ ξ in (1 : ℝ)..t, ψ i ξ * ψ j ξ| ≤ K i j / t)
    (hmass : ∀ i, ∀ t, m * R ≤ t → ∫ ξ in (1 : ℝ)..t, ψ i ξ ^ 2 ≤ Mm i) :
    ∫ θ in L..R, (∑ i, b i * ψ i (m * θ)) ^ 2 ≤ 1 / m * ∑ i, b i ^ 2 * Mm i := by
  have e : (fun θ => (∑ i, b i * ψ i (m * θ)) ^ 2) = fun θ => (fun u => (∑ i, b i * ψ i u) ^ 2) (m * θ) := by
    funext θ; rfl
  rw [e, integral_comp_mul_left (fun u => (∑ i, b i * ψ i u) ^ 2) hm.ne']
  simp only [smul_eq_mul]
  have hmR : m * L ≤ m * R := mul_le_mul_of_nonneg_left hLR hm.le
  have h := Cvs.Prolate.Gram.RungCombinationNormInterval.span_norm_le hL hmR ψ b K Mm hcont hcross hmass
  have hm' : 0 ≤ m⁻¹ := by positivity
  calc m⁻¹ * ∫ u in (m * L)..(m * R), (∑ i, b i * ψ i u) ^ 2 ≤ m⁻¹ * ∑ i, b i ^ 2 * Mm i :=
        mul_le_mul_of_nonneg_left h hm'
    _ = 1 / m * ∑ i, b i ^ 2 * Mm i := by ring

end Cvs.L2a.HierarchyLeafMasses
