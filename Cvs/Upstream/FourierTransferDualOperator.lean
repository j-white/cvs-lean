import Mathlib

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The Fourier-transfer dual in operator form

For symmetric idempotents `Q` (inner region) and `P` (rung span) and a symmetric contraction `T`, the map
`T̃ = P + (1 − P)T(1 − P)` is a symmetric contraction fixing the rung span. If `Φ = f + T̃(QΦ)` with `T̃f = f`, then
`w = Φ − QΦ` has `⟨w, ψ⟩ = ⟨f, ψ⟩` for every `T̃`-fixed `ψ` and `‖w‖² ≤ ‖f‖² + 2⟨QΦ, Qf⟩`.
-/

noncomputable section

open Matrix

namespace Cvs.Upstream.FourierTransferDualOperator


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A symmetric idempotent: `P² = P` and `⟨Px, y⟩ = ⟨x, Py⟩`. -/
structure IsSymmProj (P : E →ₗ[ℝ] E) : Prop where
  idem : ∀ x, P (P x) = P x
  symm : ∀ x y, inner ℝ (P x) y = inner ℝ x (P y)

namespace IsSymmProj

variable {P : E →ₗ[ℝ] E}

/-- The range and the kernel of a symmetric idempotent are orthogonal: `⟨Px, y − Py⟩ = 0`. -/
theorem inner_sub (hP : IsSymmProj P) (x y : E) : inner ℝ (P x) (y - P y) = 0 := by
  rw [inner_sub_right, hP.symm x (P y), hP.idem, ← hP.symm, sub_self]

/-- Pythagoras for a symmetric idempotent: `‖Px‖² + ‖x − Px‖² = ‖x‖²`. -/
theorem norm_sq_add (hP : IsSymmProj P) (x : E) : ‖P x‖ ^ 2 + ‖x - P x‖ ^ 2 = ‖x‖ ^ 2 := by
  have h := norm_add_sq_real (P x) (x - P x)
  rw [hP.inner_sub, add_sub_cancel] at h
  linarith

/-- `‖x − Px‖ ≤ ‖x‖`. -/
theorem norm_sub_le (hP : IsSymmProj P) (x : E) : ‖x - P x‖ ≤ ‖x‖ := by
  have h := hP.norm_sq_add x
  nlinarith [norm_nonneg (P x), norm_nonneg x, norm_nonneg (x - P x), sq_nonneg ‖P x‖]

end IsSymmProj

/-- The rung-fixed transfer `T̃ = P + (1 − P)T(1 − P)`. -/
def fixT (P T : E →ₗ[ℝ] E) : E →ₗ[ℝ] E :=
  P + ((LinearMap.id : E →ₗ[ℝ] E) - P) ∘ₗ T ∘ₗ ((LinearMap.id : E →ₗ[ℝ] E) - P)

/-- `T̃x = Px + (T(x − Px) − P T(x − Px))`. -/
theorem fixT_apply (P T : E →ₗ[ℝ] E) (x : E) :
    fixT P T x = P x + (T (x - P x) - P (T (x - P x))) := by
  simp [fixT]

/-- `T̃` is symmetric when `T` is. -/
theorem fixT_symm {P T : E →ₗ[ℝ] E} (hP : IsSymmProj P) (hT : ∀ x y, inner ℝ (T x) y = inner ℝ x (T y))
    (x y : E) : inner ℝ (fixT P T x) y = inner ℝ x (fixT P T y) := by
  rw [fixT_apply, fixT_apply]
  have e1 : inner ℝ (T (x - P x) - P (T (x - P x))) y = inner ℝ (T (x - P x)) (y - P y) := by
    rw [inner_sub_left, hP.symm, ← inner_sub_right]
  have e2 : inner ℝ x (T (y - P y) - P (T (y - P y))) = inner ℝ (x - P x) (T (y - P y)) := by
    rw [inner_sub_right, ← hP.symm, ← inner_sub_left]
  rw [inner_add_left, inner_add_right, e1, e2, hT, hP.symm]

/-- `T̃` is a contraction when `T` is. -/
theorem fixT_norm_le {P T : E →ₗ[ℝ] E} (hP : IsSymmProj P) (hT : ∀ x, ‖T x‖ ≤ ‖x‖) (x : E) :
    ‖fixT P T x‖ ≤ ‖x‖ := by
  set y := T (x - P x) - P (T (x - P x)) with hy
  have horth : inner ℝ (P x) y = 0 := hP.inner_sub x _
  have h1 : ‖y‖ ≤ ‖x - P x‖ := (hP.norm_sub_le _).trans (hT _)
  have h2 := hP.norm_sq_add x
  have h4 : ‖fixT P T x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [fixT_apply, ← hy, norm_add_sq_real, horth]
    nlinarith [norm_nonneg y, norm_nonneg (x - P x)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) (by norm_num)).1 h4

/-! ### The transfer identity -/

section Transfer

variable {Q F : E →ₗ[ℝ] E}

/-- **Theorem T(i)**: if `Φ = f + F(QΦ)` with `F` symmetric, then `⟨Φ − QΦ, ψ⟩ = ⟨f, ψ⟩` for every `F`-fixed `ψ`. -/
theorem inner_transfer (hF : ∀ x y, inner ℝ (F x) y = inner ℝ x (F y)) {f Φ ψ : E}
    (hΦ : Φ = f + F (Q Φ)) (hψ : F ψ = ψ) : inner ℝ (Φ - Q Φ) ψ = inner ℝ f ψ := by
  have e : Φ - Q Φ = f + F (Q Φ) - Q Φ := by rw [← hΦ]
  rw [e, inner_sub_left, inner_add_left, hF, hψ]
  ring

/-- The transfer solution has no inner part: `Q(Φ − QΦ) = 0`. -/
theorem inner_part_transfer (hQ : IsSymmProj Q) (Φ : E) : Q (Φ - Q Φ) = 0 := by
  rw [map_sub, hQ.idem, sub_self]

/-- **Theorem T(ii)** (exact energy): if `Φ = f + F(QΦ)`, `F` symmetric and `Ff = f`, then with `r = QΦ`,
`‖Φ − QΦ‖² + (‖r‖² − ‖Fr‖²) = ‖f‖² + 2⟨r, Qf⟩`. -/
theorem norm_sq_transfer (hQ : IsSymmProj Q) (hF : ∀ x y, inner ℝ (F x) y = inner ℝ x (F y)) {f Φ : E}
    (hΦ : Φ = f + F (Q Φ)) (hf : F f = f) :
    ‖Φ - Q Φ‖ ^ 2 + (‖Q Φ‖ ^ 2 - ‖F (Q Φ)‖ ^ 2) = ‖f‖ ^ 2 + 2 * inner ℝ (Q Φ) (Q f) := by
  set r := Q Φ with hr
  have hQr : Q r = r := hQ.idem Φ
  have hrQ : r = Q f + Q (F r) := by rw [hr, ← hr]; conv_lhs => rw [hr, hΦ, map_add]
  -- w = Φ − r = (f − Qf) + (Fr − Q(Fr))
  have hw : Φ - r = (f - Q f) + (F r - Q (F r)) := by
    have : Φ = f + F r := hΦ
    rw [this]
    have := hrQ
    linear_combination (norm := module) (-1 : ℝ) • this
  -- cross term ⟨f − Qf, Fr − Q(Fr)⟩ = ‖Qf‖²
  have hx1 : inner ℝ (f - Q f) (F r - Q (F r)) = inner ℝ (f - Q f) (F r) := by
    rw [inner_sub_right, real_inner_comm (Q (F r)) (f - Q f), hQ.inner_sub, sub_zero]
  have hx2 : inner ℝ (f - Q f) (F r) = inner ℝ f r - inner ℝ (Q f) (F r) := by
    rw [inner_sub_left, ← hF, hf]
  have hx3 : inner ℝ f r = inner ℝ (Q f) r := by rw [← hQr, ← hQ.symm, hQr]
  have hx4 : inner ℝ (Q f) (F r) = inner ℝ (Q f) (Q (F r)) := by rw [← hQ.symm (Q f) (F r), hQ.idem]
  have hx5 : Q (F r) = r - Q f := by rw [hrQ]; abel_nf; rw [← hrQ]
  have hcross : inner ℝ (f - Q f) (F r - Q (F r)) = ‖Q f‖ ^ 2 := by
    rw [hx1, hx2, hx3, hx4, hx5, inner_sub_right, real_inner_self_eq_norm_sq]; ring
  -- ‖Fr − Q(Fr)‖² = ‖Fr‖² − ‖r − Qf‖²
  have hn1 : ‖F r - Q (F r)‖ ^ 2 = ‖F r‖ ^ 2 - ‖Q (F r)‖ ^ 2 := by
    have := hQ.norm_sq_add (F r); linarith
  have hn2 : ‖f - Q f‖ ^ 2 = ‖f‖ ^ 2 - ‖Q f‖ ^ 2 := by have := hQ.norm_sq_add f; linarith
  have hn3 : ‖r - Q f‖ ^ 2 = ‖r‖ ^ 2 - 2 * inner ℝ r (Q f) + ‖Q f‖ ^ 2 := norm_sub_sq_real r (Q f)
  rw [hw, norm_add_sq_real, hcross, hn1, hn2, hx5, hn3]
  ring

/-- **Theorem T(ii)** (bound): for `F` a symmetric contraction with `Ff = f`, `‖Φ − QΦ‖² ≤ ‖f‖² + 2⟨QΦ, Qf⟩`. -/
theorem norm_sq_transfer_le (hQ : IsSymmProj Q) (hF : ∀ x y, inner ℝ (F x) y = inner ℝ x (F y))
    (hFc : ∀ x, ‖F x‖ ≤ ‖x‖) {f Φ : E} (hΦ : Φ = f + F (Q Φ)) (hf : F f = f) :
    ‖Φ - Q Φ‖ ^ 2 ≤ ‖f‖ ^ 2 + 2 * inner ℝ (Q Φ) (Q f) := by
  have h := norm_sq_transfer hQ hF hΦ hf
  have h2 : ‖F (Q Φ)‖ ^ 2 ≤ ‖Q Φ‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hFc _) 2
  linarith

end Transfer

/-! ### The transfer floor -/

section Floor

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ι → Prop} [DecidablePred p] {Q F : E →ₗ[ℝ] E}

end Floor

end Cvs.Upstream.FourierTransferDualOperator

end
