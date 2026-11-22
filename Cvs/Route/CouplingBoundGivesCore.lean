import Mathlib
import Cvs.Upstream.MergedBoundSchurForm

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# A coupling bound against the rung span gives CORE

For a symmetric form `B` and a subspace `R` with `B ≥ 0` on `R` and `B(r₀,r₀) > 0` at some `r₀ ∈ R`,
the coupling `B(r,w)² ≤ (1−η)B(r,r)B(w,w)` (`η < 1`) for `r ∈ R`, `w ⊥ R` forces `B(w,w) ≥ 0`, so
`B ≥ 0` everywhere. At the spine scale L2a (Cvs.L2a.SpineProfileWindowNormPos) supplies both conditions on `R_F`, so `MergedBoundSchurForm`'s
`Coupling` of `QWbil` against `R_F` at any `η < 1` gives CORE(x); CORE(x) gives it at `η = 0`.
-/

noncomputable section

open Real

namespace Cvs.Route.CouplingBoundGivesCore

open scoped InnerProductSpace

section abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Positivity gives the zero-margin coupling** (Cauchy–Schwarz): `B ≥ 0` everywhere gives
`B(r,w)² ≤ B(r,r)B(w,w)`. -/
theorem coupling_zero_of_nonneg {B : LinearMap.BilinForm ℝ E} (hB : B.IsSymm) {R : Submodule ℝ E}
    (h : ∀ f, 0 ≤ B f f) : Cvs.Upstream.MergedBoundSchurForm.Coupling B ⊤ R 0 := by
  intro r _ w _ _
  have hq : ∀ t : ℝ, 0 ≤ B w w * (t * t) + 2 * B r w * t + B r r := by
    intro t
    have := h (r + t • w)
    rw [Cvs.Upstream.MergedBoundSchurForm.apply_add_add hB] at this
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at this
    nlinarith
  have hd := discrim_le_zero hq
  rw [discrim] at hd
  nlinarith

end abstract

/-! ### At the spine scale -/

end Cvs.Route.CouplingBoundGivesCore
