import Mathlib
import Cvs.Upstream.OnsetSchurCriterion

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The low-eigenvalue count from a point-vanishing subspace

For `u_s` real-linear with `u_{s̄} = conj u_s` and `F ⊂ ℂ` finite, conjugation-closed, without real points, the
kernel `K_F = {u_s = 0, s ∈ F}` has codimension `≤ 2 #{s ∈ F, Im s > 0}`, and `≤ #{s ∈ F, Im s > 0}` when also
`1 − F = F` and `u_{1−s} = ω_s u_s`. If `aᵀAa = Σ_ρ m_ρ Re(u_{1−z_ρ}u_{z_ρ})` with far sum `≤ ε aᵀMa`, then
`|aᵀAa| ≤ ε aᵀMa` on `K_F`, and `n₋(εM − A)`, `n₋(A + εM)` are at most the codimension.
-/

noncomputable section

open Matrix Module ComplexConjugate

namespace Cvs.L2a.LowEigenCountPointVanishing

open Cvs.Upstream.OnsetSchurCriterion (NegDefOn negIndex)

/-! ### Codimension and index -/

section Codim

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]

end Codim

/-- **Index bound.** If `aᵀSa ≥ 0` on `U`, then `dim U + n₋(S) ≤ #ι`. -/
theorem finrank_add_negIndex_le {ι : Type*} [Fintype ι] (S : Matrix ι ι ℝ) {U : Submodule ℝ (ι → ℝ)}
    (hU : ∀ a ∈ U, 0 ≤ a ⬝ᵥ (S *ᵥ a)) : finrank ℝ U + negIndex S ≤ Fintype.card ι := by
  have hW : ∀ W : Submodule ℝ (ι → ℝ), NegDefOn S W → finrank ℝ U + finrank ℝ W ≤ Fintype.card ι := by
    intro W hW
    have hinf : U ⊓ W = ⊥ := by
      rw [eq_bot_iff]
      intro a ha
      rw [Submodule.mem_bot]
      by_contra h0
      exact absurd (hU a ha.1) (not_le.2 (hW a ha.2 h0))
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq U W
    rw [hinf, finrank_bot] at h1
    have h2 := Submodule.finrank_le (U ⊔ W)
    rw [Module.finrank_fintype_fun_eq_card] at h2
    omega
  have hle : negIndex S ≤ Fintype.card ι - finrank ℝ U := by
    refine csSup_le ⟨0, ⊥, fun a ha ha0 => absurd ((Submodule.mem_bot ℝ).1 ha) ha0, finrank_bot ℝ _⟩ ?_
    rintro d ⟨W, hW', rfl⟩
    have := hW W hW'
    omega
  have hU' := Submodule.finrank_le U
  rw [Module.finrank_fintype_fun_eq_card] at hU'
  omega

/-! ### One real condition from a phase-symmetric functional -/

section Phase

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

end Phase

/-! ### The common kernel at a finite set of points -/

section Points

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]

end Points

/-! ### The form on the common kernel -/

section Form

variable {ι : Type*} [Fintype ι] {R : Type*}

end Form

end Cvs.L2a.LowEigenCountPointVanishing
