import Mathlib
import Cvs.Finite.WindowMatrixSymbolKernel
import Cvs.Route.OneCellCriterion
import Cvs.Route.OneCellLaplaceTransform
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The one-cell criterion as a Chebyshev inequality with exact constants

`Ψ½(x) = Σ_{n≤x} Λ(n) n^{−1/2} log(x/n)` and `M(x) = 4√x + (A₀/2) log x + (S₀ − 8) − Σ_{k≥1} x^{−b_k}/b_k²`,
with `A₀ = ψ(¼) − log π` and `S₀ = Σ_k b_k^{−2}`, satisfy `G(log x) = 2(M(x) − Ψ½(x))` for `x ≥ 1`, so
`RH ⟺ Ψ½(x) ≤ M(x) for every x > 1` (`cheb_iff_rh`). The inequality has no other hypothesis.
-/

noncomputable section

open MeasureTheory Real Set Filter Topology
open scoped ArithmeticFunction

namespace Cvs.Route.OneCellChebyshevInequality
open Cvs.ZeroCounting

open Cvs.Finite.WindowMatrixSymbolKernel (bk bk_pos)
open Cvs.Route.OneCellLaplaceTransform (G ladder primeSide summable_inv_bk_sq)

/-- The Riesz mean `Σ_{n≤x} Λ(n) n^{−1/2} log(x/n)`. -/
def Psihalf (x : ℝ) : ℝ := ∑' n : ℕ, Λ n / Real.sqrt n * max (Real.log x - Real.log n) 0

/-- `S₀ = Σ_k b_k^{−2} = ψ'(¼)/4`. -/
def S0 : ℝ := ∑' k : ℕ, 1 / bk k ^ 2

/-- The trivial zeros' contribution `Σ_{k≥1} x^{−b_k}/b_k²`. -/
def trivTail (x : ℝ) : ℝ := ∑' k : ℕ, Real.exp (-(bk (k + 1) * Real.log x)) / bk (k + 1) ^ 2

/-- The smooth majorant `M(x) = 4√x + (A₀/2) log x + (S₀ − 8) − Σ_{k≥1} x^{−b_k}/b_k²`. -/
def M (x : ℝ) : ℝ :=
  4 * Real.sqrt x + Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 / 2 * Real.log x + (S0 - 8) - trivTail x

theorem Psihalf_eq (x : ℝ) : Psihalf x = primeSide (Real.log x) := rfl

theorem summable_exp_div_bk_sq {L : ℝ} (hL : 0 ≤ L) :
    Summable fun k : ℕ => Real.exp (-(bk k * L)) / bk k ^ 2 := by
  refine summable_inv_bk_sq.of_nonneg_of_le (fun k => by have := bk_pos k; positivity) fun k => ?_
  have := bk_pos k
  have h1 : Real.exp (-(bk k * L)) ≤ 1 := by rw [Real.exp_le_one_iff]; nlinarith
  rw [div_le_div_iff_of_pos_right (by positivity)]
  exact h1

/-- The ladder split: `ladder L = S₀ − 4e^{−L/2} − Σ_{k≥1} e^{−b_k L}/b_k²`. -/
theorem ladder_eq {L : ℝ} (hL : 0 ≤ L) :
    ladder L = S0 - 4 * Real.exp (-(L / 2)) - ∑' k : ℕ, Real.exp (-(bk (k + 1) * L)) / bk (k + 1) ^ 2 := by
  have hs := summable_exp_div_bk_sq hL
  have h1 : ladder L = S0 - ∑' k : ℕ, Real.exp (-(bk k * L)) / bk k ^ 2 := by
    unfold ladder S0
    rw [← summable_inv_bk_sq.tsum_sub hs]
    congr 1; funext k
    have := bk_pos k
    field_simp
  rw [h1, hs.tsum_eq_zero_add]
  have hb0 : bk 0 = 1 / 2 := by unfold bk; simp
  rw [hb0]
  have : Real.exp (-(1 / 2 * L)) / (1 / 2 : ℝ) ^ 2 = 4 * Real.exp (-(L / 2)) := by
    rw [show -(1 / 2 * L) = -(L / 2) by ring]; ring
  rw [this]; ring

/-- **`G(log x) = 2(M(x) − Ψ½(x))`** for `x ≥ 1`. -/
theorem G_log_eq {x : ℝ} (hx : 1 ≤ x) : G (Real.log x) = 2 * (M x - Psihalf x) := by
  have hx0 : 0 < x := by linarith
  have hL : 0 ≤ Real.log x := Real.log_nonneg hx
  have hsq : Real.exp (Real.log x / 2) = Real.sqrt x := by rw [Real.exp_half, Real.exp_log hx0]
  have hsq' : Real.exp (-(Real.log x / 2)) = 1 / Real.sqrt x := by
    rw [Real.exp_neg, hsq, one_div]
  have hcosh : 16 * (Real.cosh (Real.log x / 2) - 1) = 8 * Real.sqrt x + 8 / Real.sqrt x - 16 := by
    rw [Real.cosh_eq, hsq, hsq']; ring
  unfold G M Psihalf trivTail primeSide
  rw [ladder_eq hL, hcosh, hsq']
  ring

/-- **The one-cell criterion as a Chebyshev inequality**: `RH ⟺ Ψ½(x) ≤ M(x)` for every `x > 1`. -/
theorem cheb_iff_rh : (∀ x : ℝ, 1 < x → Psihalf x ≤ M x) ↔ RiemannHypothesis := by
  rw [Cvs.Route.OneCellCriterion.riemannHypothesis_iff_G_nonneg]
  constructor
  · intro h L hL
    have hx : 1 < Real.exp L := by rw [Real.one_lt_exp_iff]; exact hL
    have := h (Real.exp L) hx
    rw [← Real.log_exp L, G_log_eq hx.le]
    linarith
  · intro h x hx
    have := h (Real.log x) (Real.log_pos hx)
    rw [G_log_eq hx.le] at this
    linarith

end Cvs.Route.OneCellChebyshevInequality
