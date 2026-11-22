import Mathlib
import Cvs.StepA.Edge.FiniteTopGap
import Cvs.StepA.TopQuadruple
import Cvs.WeilForm.CouplingAngle
import Cvs.WeilForm.MellinZeroSum
import Cvs.Zeta.GaussKernel.ZeroChain
import Cvs.Zeta.GaussKernel.ZetaZeroStatement

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Step (a) and the depths of the zeros tending to zero

Given edge positivity of finite families and odd eigenpairs on RH, RH is equivalent to step (a)
together with finitely many nontrivial zeros in every band `|Re ρ − 1/2| ≥ ε`, `ε > 0`.
-/

noncomputable section

namespace Cvs.StepA.DepthToZero
open Cvs.ZeroCounting

open Cvs.Zeta.GaussKernel.AdmissibleKernel (nonTrivialZeroSet)
open Cvs.StepA.Edge.FiniteTopGap (FiniteTop)

/-- Every band `|Re ρ − 1/2| ≥ ε`, `ε > 0`, holds finitely many nontrivial zeros. -/
def DepthToZero : Prop :=
  ∀ ε : ℝ, 0 < ε → {ρ : nonTrivialZeroSet | ε ≤ |Cvs.GaussKernel.del ρ|}.Finite

/-- RH gives `DepthToZero`: every band off the line is empty. -/
theorem depthToZero_of_RH (h : RiemannHypothesis) : DepthToZero := by
  intro ε hε
  refine Set.Finite.subset Set.finite_empty fun ρ hρ => ?_
  have hd : Cvs.GaussKernel.del ρ = 0 := by
    rw [Cvs.GaussKernel.del, Cvs.WeilForm.CouplingAngle.re_eq_half_of_rh h ρ, sub_self]
  simp only [Set.mem_ofPred_eq, hd, abs_zero] at hρ
  linarith

/-- **`DepthToZero` without RH gives a finite top set**: the zeros at the largest distance from the
line among the finitely many at least as far as a given zero off the line. -/
theorem exists_finiteTop_of_depthToZero (hD : DepthToZero) (h : ¬ RiemannHypothesis) :
    ∃ (S : Finset nonTrivialZeroSet) (δ : ℝ), FiniteTop S δ := by
  classical
  obtain ⟨ρ₀, h₀⟩ := Cvs.StepA.TopQuadruple.exists_offLine_of_not_RH h
  have hε : 0 < |Cvs.GaussKernel.del ρ₀| :=
    abs_pos.mpr (Cvs.GaussKernel.del_ne_zero_iff.mpr h₀)
  have hfin := hD _ hε
  have hne : hfin.toFinset.Nonempty :=
    ⟨ρ₀, hfin.mem_toFinset.mpr (show |Cvs.GaussKernel.del ρ₀| ≤ |Cvs.GaussKernel.del ρ₀| from le_rfl)⟩
  obtain ⟨σ, hσ, hmax⟩ := hfin.toFinset.exists_max_image (fun ρ => |Cvs.GaussKernel.del ρ|) hne
  have hσε : |Cvs.GaussKernel.del ρ₀| ≤ |Cvs.GaussKernel.del σ| := hfin.mem_toFinset.mp hσ
  refine ⟨hfin.toFinset.filter fun ρ => |Cvs.GaussKernel.del ρ| = |Cvs.GaussKernel.del σ|,
    |Cvs.GaussKernel.del σ|, lt_of_lt_of_le hε hσε, ⟨σ, Finset.mem_filter.mpr ⟨hσ, rfl⟩⟩,
    fun ρ hρ => (Finset.mem_filter.mp hρ).2, fun ρ hρ => ?_⟩
  by_cases hin : ρ ∈ hfin.toFinset
  · exact lt_of_le_of_ne (hmax ρ hin) fun heq => hρ (Finset.mem_filter.mpr ⟨hin, heq⟩)
  · have : ¬ |Cvs.GaussKernel.del ρ₀| ≤ |Cvs.GaussKernel.del ρ| := fun h' =>
      hin (hfin.mem_toFinset.mpr h')
    exact (not_le.mp this).trans_le hσε

end Cvs.StepA.DepthToZero
