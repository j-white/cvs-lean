import Mathlib.Analysis.Calculus.DiffContOnCl
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Cvs.Zeta.ConvexityAuxDifferentiable
import Cvs.Zeta.ConvexityEvenBranch

/-!
# `DiffContOnCl`, the last structural hypothesis

`PhragmenLindelof.vertical_strip` needs `DiffContOnCl ℂ f (re ⁻¹' Ioo α β)`: differentiable on
the open strip, continuous on its closure.
-/

open Complex

namespace Cvs.ArchScore

/-- The closed-strip condition the branch argument actually needs. -/
def closedOK (c β : ℝ) (s : ℂ) : Prop := 0 ≤ s.re + c ∧ s.re ≤ β

theorem differentiableAt_evenLog' {c K β : ℝ} (hK : (β + c) ^ 2 < K)
    {s : ℂ} (hs : closedOK c β s) :
    DifferentiableAt ℂ (Cvs.ArchScore.evenLog c K) s := by
  have hslit : ((K : ℂ) - (s + (c : ℂ)) ^ 2) ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inl (Cvs.ArchScore.arg_re_pos hK hs.1 hs.2))
  have hinner : DifferentiableAt ℂ (fun z : ℂ => (K : ℂ) - (z + (c : ℂ)) ^ 2) s := by fun_prop
  unfold Cvs.ArchScore.evenLog
  exact (hinner.clog hslit).div_const 2

theorem differentiableAt_aux' {f : ℂ → ℂ} {c K β a' b' : ℝ} (hK : (β + c) ^ 2 < K)
    {s : ℂ} (hs : closedOK c β s) (hf : DifferentiableAt ℂ f s) :
    DifferentiableAt ℂ (Cvs.Zeta.ConvexityAuxDifferentiable.aux f c K a' b') s := by
  refine hf.mul (DifferentiableAt.cexp ?_)
  have hlin : DifferentiableAt ℂ (fun z : ℂ => -((a' : ℂ) + (b' : ℂ) * z)) s := by fun_prop
  exact hlin.mul (differentiableAt_evenLog' hK hs)

/-- The closure of the open strip sits inside the closed strip. -/
theorem closure_strip_subset (α β : ℝ) :
    closure (Cvs.Zeta.ConvexityAuxDifferentiable.strip α β) ⊆ Complex.re ⁻¹' Set.Icc α β := by
  refine closure_minimal (fun s hs => ⟨le_of_lt hs.1, le_of_lt hs.2⟩) ?_
  exact IsClosed.preimage Complex.continuous_re isClosed_Icc

/-- **The structural hypothesis of `vertical_strip`, discharged.**  Differentiable on the open
strip and continuous on its closure — both from `ConvexityEvenBranch`'s positivity, which holds on the closed
strip as well. -/
theorem diffContOnCl_aux {f : ℂ → ℂ} {c K α β a' b' : ℝ} (hK : (β + c) ^ 2 < K)
    (hαc : 0 ≤ α + c)
    (hf : ∀ s : ℂ, s.re ∈ Set.Icc α β → DifferentiableAt ℂ f s) :
    DiffContOnCl ℂ (Cvs.Zeta.ConvexityAuxDifferentiable.aux f c K a' b') (Cvs.Zeta.ConvexityAuxDifferentiable.strip α β) := by
  constructor
  · intro s hs
    have hok : closedOK c β s := ⟨by have := hs.1; linarith, le_of_lt hs.2⟩
    exact (differentiableAt_aux' hK hok
      (hf s ⟨le_of_lt hs.1, le_of_lt hs.2⟩)).differentiableWithinAt
  · intro s hs
    have hmem := closure_strip_subset α β hs
    have hok : closedOK c β s := ⟨by have := hmem.1; linarith, hmem.2⟩
    exact (differentiableAt_aux' hK hok (hf s hmem)).continuousAt.continuousWithinAt

end Cvs.ArchScore
