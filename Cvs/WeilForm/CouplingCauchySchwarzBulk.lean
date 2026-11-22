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
# The coupling from Cauchy–Schwarz in the geometry of a form below the bulk form

For symmetric `B` and `M` with `0 ≤ M(w,w) ≤ B(w,w)` on `W`, a bound `B(r,w)² ≤ κ·M(w,w)` on `W` with
`0 ≤ κ ≤ (1−δ)B(r,r)` gives `B(r,w)² ≤ (1−δ)B(r,r)B(w,w)` on `W`. In a frame `w` of `(span r)ᗮ` with
`0 ≺ G_M ≤ G_B`, `XG_M⁻¹Xᵀ ≤ (1−δ)C` gives `XG_B⁻¹Xᵀ ≤ (1−δ)C`, hence the coupling on `span w`. For `M = B` the
hypothesis is the coupling, and for `M = b⟪·,·⟫` it is a bulk floor with `|B(r,w)| ≤ c‖w‖`, `κ = c²/b`.
-/

noncomputable section

namespace Cvs.WeilForm.CouplingCauchySchwarzBulk

open Matrix
open scoped InnerProductSpace MatrixOrder

/-! ### The weighted Cauchy–Schwarz step -/

section Form

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- **The coupling at one pair from a weighted channel bound**: `0 ≤ M(w,w) ≤ B(w,w)`,
`B(r,w)² ≤ κ·M(w,w)` and `0 ≤ κ ≤ (1−δ)B(r,r)` give `B(r,w)² ≤ (1−δ)B(r,r)B(w,w)`. -/
theorem sq_le_of_weighted {B M : LinearMap.BilinForm ℝ E} {r w : E} {κ δ : ℝ} (hM0 : 0 ≤ M w w)
    (hMB : M w w ≤ B w w) (hκ0 : 0 ≤ κ) (hc : B r w ^ 2 ≤ κ * M w w) (hr : κ ≤ (1 - δ) * B r r) :
    B r w ^ 2 ≤ (1 - δ) * B r r * B w w :=
  calc B r w ^ 2 ≤ κ * M w w := hc
    _ ≤ κ * B w w := mul_le_mul_of_nonneg_left hMB hκ0
    _ ≤ (1 - δ) * B r r * B w w := mul_le_mul_of_nonneg_right hr (hM0.trans hMB)

end Form

section Orth

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **`MergedBoundSchurForm`'s coupling from a weighted channel bound**: with `0 ≤ M ≤ B` on `H ∩ Rᗮ`, and for each `r ∈ R` a
channel bound `B(r,w)² ≤ κ(r)·M(w,w)` on `H ∩ Rᗮ` with `0 ≤ κ(r) ≤ (1−δ)B(r,r)`, `Coupling B H R δ` holds. -/
theorem coupling_of_weighted' {B M : LinearMap.BilinForm ℝ E} {H R : Submodule ℝ E} {κ : E → ℝ} {δ : ℝ}
    (hM : ∀ w ∈ H, w ∈ Rᗮ → 0 ≤ M w w ∧ M w w ≤ B w w) (hκ0 : ∀ r ∈ R, 0 ≤ κ r)
    (hc : ∀ r ∈ R, ∀ w ∈ H, w ∈ Rᗮ → B r w ^ 2 ≤ κ r * M w w)
    (hr : ∀ r ∈ R, κ r ≤ (1 - δ) * B r r) : Cvs.Upstream.MergedBoundSchurForm.Coupling B H R δ :=
  fun r hr' w hw hwR => sq_le_of_weighted (hM w hw hwR).1 (hM w hw hwR).2 (hκ0 r hr') (hc r hr' w hw hwR)
    (hr r hr')

/-! ### The scalar weight `M = b⟪·,·⟫` -/

/-- `b • innerₗ E` evaluates to `b‖w‖²` on the diagonal. -/
theorem smul_innerₗ_self (b : ℝ) (w : E) : (b • innerₗ E) w w = b * ‖w‖ ^ 2 := by
  simp

/-- **The bulk floor is the operator floor of `b⟪·,·⟫`**: for `b ≥ 0`, `BulkFloor B H R b` iff
`0 ≤ b‖w‖² ≤ B(w,w)` on `H ∩ Rᗮ`. -/
theorem bulkFloor_iff_smul_innerₗ {B : LinearMap.BilinForm ℝ E} {H R : Submodule ℝ E} {b : ℝ}
    (hb : 0 ≤ b) :
    Cvs.Upstream.MergedBoundSchurForm.BulkFloor B H R b ↔
      ∀ w ∈ H, w ∈ Rᗮ → 0 ≤ (b • innerₗ E) w w ∧ (b • innerₗ E) w w ≤ B w w := by
  simp only [smul_innerₗ_self]
  exact ⟨fun h w hw hwR => ⟨by positivity, h w hw hwR⟩, fun h w hw hwR => (h w hw hwR).2⟩

/-- **A norm channel bound is a weighted channel bound for `b⟪·,·⟫`**: for `b > 0`, `|B(r,w)| ≤ c‖w‖` gives
`B(r,w)² ≤ (c²/b)·b‖w‖²`. -/
theorem sq_le_smul_innerₗ {B : LinearMap.BilinForm ℝ E} {r w : E} {b c : ℝ} (hb : 0 < b)
    (h : |B r w| ≤ c * ‖w‖) : B r w ^ 2 ≤ c ^ 2 / b * (b • innerₗ E) w w := by
  rw [smul_innerₗ_self, ← mul_assoc, div_mul_cancel₀ _ hb.ne', ← mul_pow, ← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) h 2

/-- **The scalar ratio is the weighted ratio of `b⟪·,·⟫`**: for `b > 0`, `c² ≤ (1−δ)b·B(r,r)` iff
`c²/b ≤ (1−δ)B(r,r)`. -/
theorem sq_div_le_iff {B : LinearMap.BilinForm ℝ E} {r : E} {b c δ : ℝ} (hb : 0 < b) :
    c ^ 2 / b ≤ (1 - δ) * B r r ↔ c ^ 2 ≤ (1 - δ) * b * B r r := by
  rw [div_le_iff₀ hb]; constructor <;> intro h <;> linarith

/-! ### Frames: Loewner antitonicity of the inverse Gram -/

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]

end Orth

end Cvs.WeilForm.CouplingCauchySchwarzBulk
