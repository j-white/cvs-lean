import Mathlib

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# MV step 1 — the quadratic-form bound `U ≤ 73 V` (arXiv:2203.14950 Thm 1.2 shape)

`U := Σ_{m≠n} δ_m^{3/2} δ_n^{1/2} t_m t_n/(freq m − freq n)²  ≤  73 Σ t_n² ` for nonneg `t`:
Cauchy–Schwarz `U² ≤ V·W`; `W = S + T` (diagonal/off-diagonal of the expanded square);
`S ≤ 27V` (σ=4 spacing); `T ≤ 72U` (two-point lemma); the quadratic inequality gives `U ≤ 73V`.
-/

noncomputable section
open Real Finset
open scoped BigOperators

namespace Cvs.Zeta.Base
namespace MV

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {freq δ : ι → ℝ}

/-- Swap the two layers of an `erase`-nested double sum. -/
lemma sum_erase_comm {M : Type*} [AddCommMonoid M] (F : ι → ι → M) :
    ∑ m, ∑ n ∈ Finset.univ.erase m, F m n = ∑ n, ∑ m ∈ Finset.univ.erase n, F m n := by
  rw [Finset.sum_comm' (t' := Finset.univ) (s' := fun n => Finset.univ.erase n)]
  intro n m
  simp only [Finset.mem_univ, Finset.mem_erase, true_and, and_true]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

end MV
end Cvs.Zeta.Base
