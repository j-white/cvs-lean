import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Topology.Instances.AddCircle.Defs
import Cvs.Upstream.SymmetricOpNormQuadForm
import Cvs.WeilForm.MaskedShift.ChainArithmetic
import Cvs.WeilForm.MaskedShift.ChebFactorMonotone
import Cvs.WeilForm.MaskedShift.MaskedRotationFormIntegral
import Cvs.WeilForm.MaskedShift.MaskedRotationLowerBound
import Cvs.WeilForm.MaskedShift.MaskedShiftComposition
import Cvs.WeilForm.MaskedShift.MasksCompose
import Cvs.WeilForm.MaskedShift.PathGraphSpectrum
import Cvs.WeilForm.MaskedShift.SchurEstimateAssembled
import Cvs.WeilForm.MaskedShift.SchurIntegrability
import Cvs.WeilForm.MaskedShift.SchurMajorantIntegrable

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

open MeasureTheory Real
open scoped NNReal

namespace Cvs.Operator

open Cvs.Operator Cvs.Operator Cvs.Operator Cvs.Operator Cvs.Operator Cvs.Operator

variable {β : ℝ}

/-! # B38: the upper bound, unconditionally

The Schur chain, assembled.
-/

/-- **The quadratic form is bounded by `ν ⌈1/β⌉ · ‖f‖²`.** -/
theorem abs_inner_W_le (hβ : 0 < β) (hβ1 : β < 1) (f : L2) :
    |inner ℝ ((S β + ContinuousLinearMap.adjoint (S β)) f) f|
      ≤ Cvs.Operator.chebFactor (cap 1 β) * ‖f‖ ^ 2 := by
  set G : AddCircle (1 : ℝ) → ℝ := fun x =>
    (maskFwd β).indicator
      ((f : AddCircle (1 : ℝ) → ℝ) ∘ fun y => y + (β : AddCircle (1 : ℝ))) x
      * (f : AddCircle (1 : ℝ) → ℝ) x with hG
  have hHint : Integrable (fun x => Hf β f x + Hb β f x) volume :=
    (integrable_Hf hβ f).add (integrable_Hb hβ f)
  -- the cross term, bounded by the majorants
  have step1 : |2 * ∫ x, G x| ≤ ∫ x, (Hf β f x + Hb β f x) := by
    have h1 : |2 * ∫ x, G x| ≤ 2 * ∫ x, |G x| := by
      rw [abs_mul, abs_two]
      have := norm_integral_le_integral_norm (μ := (volume : Measure (AddCircle (1:ℝ)))) G
      simpa [Real.norm_eq_abs] using
        (mul_le_mul_of_nonneg_left this (by norm_num : (0:ℝ) ≤ 2))
    have h2 : 2 * ∫ x, |G x| = ∫ x, 2 * |G x| := by
      rw [integral_const_mul]
    have h3 : ∫ x, 2 * |G x| ≤ ∫ x, (Hf β f x + Hb β f x) := by
      refine integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun x => by positivity) hHint
        (Filter.Eventually.of_forall fun x => ?_)
      exact two_abs_cross_le hβ f x
    linarith [h1, h2 ▸ h3]
  -- fold the forward half and collect
  have step2 : ∫ x, (Hf β f x + Hb β f x)
      ≤ Cvs.Operator.chebFactor (cap 1 β) * ‖f‖ ^ 2 := by
    rw [integral_add (integrable_Hf hβ f) (integrable_Hb hβ f),
      show (∫ x, Hf β f x) = ∫ x, Bw β f x from Cvs.Operator.integral_fwd_eq_bwd hβ hβ1 f,
      ← integral_add (integrable_Bw hβ f) (integrable_Hb hβ f),
      norm_sq_eq_integral f, ← integral_const_mul]
    refine integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun x => ?_)
      (((Cvs.Operator.integrable_sq f).const_mul (Cvs.Operator.chebFactor (cap 1 β))))
      (Filter.Eventually.of_forall fun x => ?_)
    · exact add_nonneg (Bw_nonneg hβ f x) (Hb_nonneg hβ f x)
    · exact Hsum_le hβ f x
  rw [Cvs.Operator.inner_W_eq_integral]
  exact le_trans step1 step2

/-- **The upper half of the norm law, unconditionally.** -/
theorem norm_W_le (hβ : 0 < β) (hβ1 : β < 1) :
    ‖S β + ContinuousLinearMap.adjoint (S β)‖ ≤ Cvs.Operator.chebFactor (cap 1 β) := by
  have hsym : ∀ x y : L2,
      inner ℝ ((S β + ContinuousLinearMap.adjoint (S β)) x) y
        = inner ℝ x ((S β + ContinuousLinearMap.adjoint (S β)) y) := by
    intro x y
    have hsa : ContinuousLinearMap.adjoint (S β + ContinuousLinearMap.adjoint (S β))
        = S β + ContinuousLinearMap.adjoint (S β) := by
      rw [map_add, ContinuousLinearMap.adjoint_adjoint, add_comm]
    rw [← ContinuousLinearMap.adjoint_inner_left, hsa]
  have hcheb : 0 ≤ Cvs.Operator.chebFactor (cap 1 β) := by
    have hcap : 0 < cap 1 β := by unfold cap; rw [Nat.ceil_pos]; positivity
    exact Cvs.Operator.chebFactor_nonneg _ hcap
  exact Cvs.Operator.opNorm_le_of_quadForm_le hsym hcheb (abs_inner_W_le hβ hβ1)

/-- **The norm law.**  `‖W β‖ = ν ⌈1/β⌉`, with no hypotheses beyond `0 < β < 1`. -/
theorem norm_W (hβ : 0 < β) (hβ1 : β < 1) :
    ‖S β + ContinuousLinearMap.adjoint (S β)‖ = Cvs.Operator.chebFactor (cap 1 β) :=
  le_antisymm (norm_W_le hβ hβ1) (Cvs.Operator.le_norm_W hβ hβ1)

end Cvs.Operator
