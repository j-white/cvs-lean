import Mathlib
import Cvs.WeilForm.CouplingSchurComplement

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Positivity of a form on `R + W` from positivity on each piece and a coupling

For a symmetric `B`, `B(r,r), B(w,w) ≥ 0` and `B(r,w)² ≤ (1−δ)B(r,r)B(w,w)` give
`B(r+w,r+w) ≥ B(r,r) + B(w,w) − 2√((1−δ)B(r,r)B(w,w)) ≥ (1 − √(1−δ))(B(r,r) + B(w,w))`, which is
`≥ 0` for `δ ≥ 0`. In blocks `C = B_RR`, `X = B_RW`, `G = B_WW > 0`: `aᵀXG⁻¹Xᵀa` is the largest value
of `(aᵀXy)²/yᵀGy` over `y ≠ 0`, and the coupling is `XG⁻¹Xᵀ ≤ (1−δ)C` in the Loewner order.
-/

noncomputable section

namespace Cvs.Upstream.FormPositivitySumCoupling

open Matrix
open scoped MatrixOrder

/-! ### The algebraic core -/

section Form

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- **The cross term**: `B(r,w)² ≤ (1−δ)B(r,r)B(w,w)` gives `−√((1−δ)B(r,r)B(w,w)) ≤ B(r,w)`. -/
theorem neg_sqrt_le_cross {B : LinearMap.BilinForm ℝ E} {r w : E} {δ : ℝ}
    (h : B r w ^ 2 ≤ (1 - δ) * B r r * B w w) : -√((1 - δ) * B r r * B w w) ≤ B r w := by
  have h1 := Real.sqrt_le_sqrt h
  rw [Real.sqrt_sq_eq_abs] at h1
  linarith [neg_abs_le (B r w)]

/-- **The Cauchy–Schwarz lower bound**: for symmetric `B` and the coupling at `(r, w)`,
`B(r,r) + B(w,w) − 2√((1−δ)B(r,r)B(w,w)) ≤ B(r+w, r+w)`. -/
theorem apply_add_ge {B : LinearMap.BilinForm ℝ E} (hB : B.IsSymm) {r w : E} {δ : ℝ}
    (h : B r w ^ 2 ≤ (1 - δ) * B r r * B w w) :
    B r r + B w w - 2 * √((1 - δ) * B r r * B w w) ≤ B (r + w) (r + w) := by
  rw [Cvs.WeilForm.CouplingSchurComplement.apply_add_self hB]
  linarith [neg_sqrt_le_cross h]

/-- `2√((1−δ)ac) ≤ √(1−δ)(a + c)` for `a, c ≥ 0`. -/
theorem two_sqrt_le {a c δ : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) :
    2 * √((1 - δ) * a * c) ≤ √(1 - δ) * (a + c) := by
  rcases le_or_gt 0 (1 - δ) with hδ | hδ
  · rw [mul_assoc, Real.sqrt_mul hδ, Real.sqrt_mul ha]
    have hs : 2 * (√a * √c) ≤ a + c := by
      nlinarith [sq_nonneg (√a - √c), Real.sq_sqrt ha, Real.sq_sqrt hc]
    nlinarith [Real.sqrt_nonneg (1 - δ)]
  · have h0 : (1 - δ) * a * c ≤ 0 := by
      rw [mul_assoc]; exact mul_nonpos_of_nonpos_of_nonneg hδ.le (mul_nonneg ha hc)
    rw [Real.sqrt_eq_zero'.2 h0, Real.sqrt_eq_zero'.2 hδ.le]
    simp

/-- **The margin**: for symmetric `B`, `B(r,r), B(w,w) ≥ 0` and the coupling at `(r, w)`,
`(1 − √(1−δ))(B(r,r) + B(w,w)) ≤ B(r+w, r+w)`. -/
theorem margin_le_apply_add {B : LinearMap.BilinForm ℝ E} (hB : B.IsSymm) {r w : E} {δ : ℝ}
    (hr : 0 ≤ B r r) (hw : 0 ≤ B w w) (h : B r w ^ 2 ≤ (1 - δ) * B r r * B w w) :
    (1 - √(1 - δ)) * (B r r + B w w) ≤ B (r + w) (r + w) := by
  have h1 := apply_add_ge hB h
  have h2 := two_sqrt_le (δ := δ) hr hw
  linarith

/-- `0 ≤ 1 − √(1−δ)` for `0 ≤ δ`. -/
theorem one_sub_sqrt_nonneg {δ : ℝ} (hδ : 0 ≤ δ) : 0 ≤ 1 - √(1 - δ) := by
  have : √(1 - δ) ≤ 1 := Real.sqrt_le_one.mpr (by linarith)
  linarith

end Form

/-! ### Blocks: the supremum over `W` and the Loewner form -/

section Block

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

end Block

/-! ### Frames -/

section Frame

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

end Frame

end Cvs.Upstream.FormPositivitySumCoupling
