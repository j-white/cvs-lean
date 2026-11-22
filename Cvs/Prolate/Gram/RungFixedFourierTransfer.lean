import Mathlib
import Cvs.Prolate.Gram.EvenFirstCellEnergyGram
import Cvs.Prolate.Gram.FiniteFourierSplitCells
import Cvs.Prolate.Gram.WindowFloorExtension
import Cvs.Prolate.Gram.WindowFloorTransferSolutions
import Cvs.Upstream.FourierTransferDualOperator

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# (WF′) from the rung-fixed Fourier transfer

`P_V z = Σ_b ⟨e_b, z⟩ e_b` projects `E2` on the rung span, and `𝓕̃ = P_V + (1 − P_V)𝓕(1 − P_V)` is a symmetric
contraction fixing every rung. If the transfer equations `Φ_j = e_j + 𝓕̃(QΦ_j)` are solvable (`TransferSolvable`)
and every solution on the layer has row Gram `‖Σ a_j(Φ_j − QΦ_j)‖² ≤ c|a|²` with `μ*C₀∞/2 + ε ≤ 1/c`
(`TransferGram`), then (WF′) holds.
-/

noncomputable section

open Real Filter Matrix

namespace Cvs.Prolate.Gram.RungFixedFourierTransfer
open Cvs.ZeroCounting

open Cvs.Upstream.FourierTransferDualOperator (IsSymmProj fixT)
open Cvs.Prolate.Gram.WindowFloorTransferSolutions (E2 rungE innerProj inner_rungE)
open Cvs.Prolate.Gram.FiniteFourierSplitCells (fourierE2)

/-- The projection `P_V z = Σ_b ⟨e_b, z⟩ e_b` on the span of the rungs. -/
def rungProj {x : ℕ} (hx : 80 ≤ 2 * π * x) : E2 →ₗ[ℝ] E2 where
  toFun z := ∑ b, inner ℝ (rungE hx b) z • rungE hx b
  map_add' z w := by simp only [inner_add_right, add_smul, Finset.sum_add_distrib]
  map_smul' r z := by simp only [inner_smul_right, mul_smul, Finset.smul_sum, RingHom.id_apply]

/-- `P_V z = Σ_b ⟨e_b, z⟩ e_b`. -/
theorem rungProj_apply {x : ℕ} (hx : 80 ≤ 2 * π * x) (z : E2) :
    rungProj hx z = ∑ b, inner ℝ (rungE hx b) z • rungE hx b := rfl

/-- `P_V` is a symmetric idempotent. -/
theorem isSymmProj_rungProj {x : ℕ} (hx : 80 ≤ 2 * π * x) : IsSymmProj (rungProj hx) where
  idem z := by simp only [rungProj_apply, inner_sum, inner_smul_right, inner_rungE, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  symm z w := by
    simp only [rungProj_apply, sum_inner, inner_sum, inner_smul_left, inner_smul_right, conj_trivial]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [real_inner_comm (rungE hx b) z]; ring

/-- The rung-fixed Fourier transfer `𝓕̃ = P_V + (1 − P_V)𝓕(1 − P_V)` at `c = 2πx`. -/
def fourierFixed {x : ℕ} (hx : 80 ≤ 2 * π * x) : E2 →ₗ[ℝ] E2 := fixT (rungProj hx) (fourierE2 (2 * π * x))

/-- `𝓕̃` is symmetric. -/
theorem fourierFixed_symm {x : ℕ} (hx : 80 ≤ 2 * π * x) (z w : E2) :
    inner ℝ (fourierFixed hx z) w = inner ℝ z (fourierFixed hx w) :=
  Cvs.Upstream.FourierTransferDualOperator.fixT_symm (isSymmProj_rungProj hx) (Cvs.Prolate.Gram.FiniteFourierSplitCells.fourierE2_symm _) z w

/-- `𝓕̃` is a contraction. -/
theorem fourierFixed_norm_le {x : ℕ} (hx : 80 ≤ 2 * π * x) (z : E2) : ‖fourierFixed hx z‖ ≤ ‖z‖ :=
  Cvs.Upstream.FourierTransferDualOperator.fixT_norm_le (isSymmProj_rungProj hx) (Cvs.Prolate.Gram.FiniteFourierSplitCells.norm_fourierE2_le (by linarith)) z

end Cvs.Prolate.Gram.RungFixedFourierTransfer

end
