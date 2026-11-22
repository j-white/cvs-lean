import Mathlib

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The inertia bound: a negative definite subspace is no larger than the negative directions
If a function `Q` is nonnegative on the common kernel of linear functionals `ℓ_q` inside `V`, and
negative on `V ∖ {0}`, then `finrank V ≤ #q`; the same with a finite-dimensional space `W` of
functionals and `finrank W`. For `M = P + ∑_{q<k} (a_q a_qᵀ − b_q b_qᵀ)` with `P ⪰ 0`, every subspace
on which `xᵀMx < 0` has `finrank ≤ k`.
-/

noncomputable section

open Matrix Module

namespace Cvs.Upstream.NegativeSubspaceInertiaBound

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- **Inertia bound, functional form.** `V` meets the common kernel of the `ℓ_q` only in `0`, so
`x ↦ (ℓ_q x)_q` is injective on `V`. -/
theorem finrank_le_card {ι' : Type*} [Fintype ι'] (ℓ : ι' → Dual ℝ E) (Q : E → ℝ)
    (V : Submodule ℝ E) (hnn : ∀ x ∈ V, (∀ q, ℓ q x = 0) → 0 ≤ Q x)
    (hneg : ∀ x ∈ V, x ≠ 0 → Q x < 0) :
    finrank ℝ V ≤ Fintype.card ι' := by
  classical
  let f : V →ₗ[ℝ] (ι' → ℝ) := (LinearMap.pi ℓ).comp V.subtype
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have hq : ∀ q, ℓ q (x : E) = 0 := fun q => by
      have := congrFun hx q
      simpa [f] using this
    by_contra hne
    have hx0 : (x : E) ≠ 0 := fun h => hne (Subtype.ext h)
    exact absurd (hnn x x.2 hq) (not_le.mpr (hneg x x.2 hx0))
  have := LinearMap.finrank_le_finrank_of_injective hinj
  simpa using this

/-- The dot product with a fixed vector, as a functional. -/
def dotL {n : Type*} [Fintype n] (b : n → ℝ) : Dual ℝ (n → ℝ) where
  toFun x := b ⬝ᵥ x
  map_add' x y := dotProduct_add b x y
  map_smul' r x := by simp [dotProduct_smul]

end Cvs.Upstream.NegativeSubspaceInertiaBound
