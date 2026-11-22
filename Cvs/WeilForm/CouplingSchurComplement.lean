import Mathlib

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The coupling as a Schur complement, and the Schur lift of a functional

For symmetric `B ≥ 0` on `W`: `B(r,w)² ≤ (1−η)B(r,r)B(w,w)` on `W` iff `η·B(r,r) ≤ B(r+w,r+w)` on `W`.
With blocks `C = Q_DD`, `X = Q_DW`, `G = Q_WW > 0`, `sup_y (aᵀXy)²/yᵀGy = aᵀXG⁻¹Xᵀa`, so the coupling
is `C − XG⁻¹Xᵀ ≥ η·C`. With `vᵢ`, `zᵢ` the `B`-representers of `αᵢ` on `E` and on `W`,
`αⱼ(vᵢ) − αⱼ(zᵢ) = B(vᵢ−zᵢ, vⱼ−zⱼ)`, and `vᵢ−zᵢ` minimises `B` on `vᵢ + W`.
-/

noncomputable section

namespace Cvs.WeilForm.CouplingSchurComplement

open Matrix
open scoped MatrixOrder

/-! ### The coupling as a lower bound on `B(r+w, r+w)` -/

section Form

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- `B(x+y, x+y) = B(x,x) + 2B(x,y) + B(y,y)` for a symmetric form. -/
theorem apply_add_self {B : LinearMap.BilinForm ℝ E} (hB : B.IsSymm) (x y : E) :
    B (x + y) (x + y) = B x x + 2 * B x y + B y y := by
  have h := hB.eq y x
  simp only [map_add, LinearMap.add_apply]
  rw [h]; ring

/-- `B(x + t•y, x + t•y) = B(x,x) + 2tB(x,y) + t²B(y,y)` for a symmetric form. -/
theorem apply_add_smul_self {B : LinearMap.BilinForm ℝ E} (hB : B.IsSymm) (x y : E) (t : ℝ) :
    B (x + t • y) (x + t • y) = B x x + 2 * t * B x y + t ^ 2 * B y y := by
  rw [apply_add_self hB]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

/-- **The margin bounds the coupling**: if `η·B(r,r) ≤ B(r+w,r+w)` for every `w ∈ W`, then
`B(r,w)² ≤ (1−η)B(r,r)B(w,w)` for every `w ∈ W`. -/
theorem sq_le_of_margin {B : LinearMap.BilinForm ℝ E} (hB : B.IsSymm) {W : Submodule ℝ E}
    {r : E} {η : ℝ} (h : ∀ w ∈ W, η * B r r ≤ B (r + w) (r + w)) {w : E} (hw : w ∈ W) :
    B r w ^ 2 ≤ (1 - η) * B r r * B w w := by
  have hq : ∀ t : ℝ, 0 ≤ B w w * (t * t) + (2 * B r w) * t + (1 - η) * B r r := by
    intro t
    have := h (t • w) (W.smul_mem t hw)
    rw [apply_add_smul_self hB] at this
    nlinarith
  have hd := discrim_le_zero hq
  rw [discrim] at hd
  nlinarith

end Form

section Coupling

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

end Coupling

/-! ### Block matrices: the supremum over `W` is `aᵀXG⁻¹Xᵀa` -/

section Block

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

end Block

/-! ### Frames: `Coupling` on spans is the block coupling of the Gram blocks -/

section Frame

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

end Frame

/-! ### The Schur lift of a functional -/

section Lift

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {ι : Type*}

end Lift

end Cvs.WeilForm.CouplingSchurComplement
