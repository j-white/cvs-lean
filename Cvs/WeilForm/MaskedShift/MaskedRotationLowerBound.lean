import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Adjoint
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
import Cvs.WeilForm.MaskedShift.ChainArithmetic
import Cvs.WeilForm.MaskedShift.ChainEigenvectorPointwise
import Cvs.WeilForm.MaskedShift.ChainTestFunctionL2
import Cvs.WeilForm.MaskedShift.ChebFactorMonotone
import Cvs.WeilForm.MaskedShift.LongChainsPositiveMeasure
import Cvs.WeilForm.MaskedShift.MaskedShiftComposition
import Cvs.WeilForm.MaskedShift.MasksCompose
import Cvs.WeilForm.MaskedShift.PathGraphSpectrum

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

open Cvs.Operator Cvs.Operator Cvs.Operator Cvs.Operator Cvs.Operator

variable {β : ℝ}

/-! # B29: the lower bound

B28's pointwise identity lifted through `coeFn_S` and `coeFn_adjoint_S`:
`W β (testFun β) = ν ⌈1/β⌉ • testFun β`.  Since `testFun β ≠ 0` (B26), the
operator norm is at least `ν ⌈1/β⌉`.
-/

/-- **The masked rotation, applied to any vector obeying the recurrence.** Nothing in this proof
is about the test function. -/
theorem coeFn_W_of_masked (hβ : 0 ≤ β) (hβ1 : β ≤ 1) {v : L2}
    {val : AddCircle (1 : ℝ) → ℝ} {lam : ℝ}
    (hv : (v : AddCircle (1 : ℝ) → ℝ) =ᵐ[volume] val)
    (hrec : ∀ z : AddCircle (1 : ℝ),
      (if rep z + β < 1 then val (z + (β : AddCircle (1 : ℝ))) else 0)
        + (if β ≤ rep z then val (z - (β : AddCircle (1 : ℝ))) else 0) = lam * val z) :
    ((S β + ContinuousLinearMap.adjoint (S β)) v : AddCircle (1 : ℝ) → ℝ)
      =ᵐ[volume] fun z => lam * val z := by
  have h1 := coeFn_S β v
  have h2 := coeFn_adjoint_S β v
  have h4 := (quasi_shift β).ae_eq_comp hv
  have h5 := (quasi_shift (-β)).ae_eq_comp hv
  have hsum : ((S β + ContinuousLinearMap.adjoint (S β)) v
      : AddCircle (1 : ℝ) → ℝ)
      =ᵐ[volume] fun z => (S β v : AddCircle (1 : ℝ) → ℝ) z
        + (ContinuousLinearMap.adjoint (S β) v : AddCircle (1 : ℝ) → ℝ) z := by
    rw [add_apply]
    exact Lp.coeFn_add _ _
  filter_upwards [hsum, h1, h2, h4, h5] with z hadd hs hsa hf hfa
  rw [hadd, hs, hsa]
  -- convert the two indicator terms to the `if` form the recurrence is stated in
  have hfwd : (maskFwd β).indicator
      ((v : AddCircle (1 : ℝ) → ℝ) ∘ fun x => x + (β : AddCircle (1 : ℝ))) z
      = if rep z + β < 1 then val (z + (β : AddCircle (1 : ℝ))) else 0 := by
    by_cases hm : rep z + β < 1
    · have hm' : z ∈ maskFwd β := hm
      rw [Set.indicator_of_mem hm', if_pos hm, Function.comp_apply]
      exact hf
    · have hm' : z ∉ maskFwd β := hm
      rw [Set.indicator_of_notMem hm', if_neg hm]
  have hbwd : (maskFwd β).indicator (fun y => (v : AddCircle (1 : ℝ) → ℝ) y)
      (z + ((-β : ℝ) : AddCircle (1 : ℝ)))
      = if β ≤ rep z then val (z - (β : AddCircle (1 : ℝ))) else 0 := by
    have hsub : z + ((-β : ℝ) : AddCircle (1 : ℝ)) = z - (β : AddCircle (1 : ℝ)) := by
      simp [sub_eq_add_neg]
    rw [hsub]
    by_cases hm : z - (β : AddCircle (1 : ℝ)) ∈ maskFwd β
    · rw [Set.indicator_of_mem hm,
        if_pos ((mem_maskFwd_sub_iff hβ hβ1 z).mp hm)]
      exact hfa
    · rw [Set.indicator_of_notMem hm,
        if_neg (fun hc => hm ((mem_maskFwd_sub_iff hβ hβ1 z).mpr hc))]
  rw [hfwd, hbwd]
  exact hrec z

/-- The masked rotation applied to the test function, pointwise: the chain
weight is the solution the recurrence was built from. -/
theorem coeFn_W_testFun (hβ : 0 < β) (hβ1 : β < 1) :
    ((S β + ContinuousLinearMap.adjoint (S β)) (testFun β) : AddCircle (1 : ℝ) → ℝ)
      =ᵐ[volume] fun z => Cvs.Operator.chebFactor (cap 1 β) * testVal β z :=
  coeFn_W_of_masked hβ.le hβ1.le (coeFn_testFun β) (masked_apply hβ hβ1)

/-- **The test function is an eigenvector of the masked rotation.** -/
theorem W_testFun (hβ : 0 < β) (hβ1 : β < 1) :
    (S β + ContinuousLinearMap.adjoint (S β)) (testFun β)
      = Cvs.Operator.chebFactor (cap 1 β) • testFun β := by
  refine Lp.ext ?_
  filter_upwards [coeFn_W_testFun hβ hβ1,
    Lp.coeFn_smul (Cvs.Operator.chebFactor (cap 1 β)) (testFun β), coeFn_testFun β]
    with z hz hsm hf
  rw [hz, hsm, Pi.smul_apply, hf, smul_eq_mul]

/-! ## The lower bound -/

/-- **`ν ⌈1/β⌉ ≤ ‖W β‖`.**  The test function is a non-zero eigenvector with
that eigenvalue. -/
theorem le_norm_W (hβ : 0 < β) (hβ1 : β < 1) :
    Cvs.Operator.chebFactor (cap 1 β) ≤ ‖S β + ContinuousLinearMap.adjoint (S β)‖ := by
  have hne : testFun β ≠ 0 := Cvs.Operator.testFun_ne_zero hβ hβ1
  have hnorm : 0 < ‖testFun β‖ := norm_pos_iff.mpr hne
  have hcheb : 0 ≤ Cvs.Operator.chebFactor (cap 1 β) := by
    have hcap : 0 < cap 1 β := by
      unfold cap; rw [Nat.ceil_pos]; positivity
    exact Cvs.Operator.chebFactor_nonneg _ hcap
  have happ : ‖(S β + ContinuousLinearMap.adjoint (S β)) (testFun β)‖
      = Cvs.Operator.chebFactor (cap 1 β) * ‖testFun β‖ := by
    rw [W_testFun hβ hβ1, norm_smul, Real.norm_eq_abs, abs_of_nonneg hcheb]
  have hle := (S β + ContinuousLinearMap.adjoint (S β)).le_opNorm (testFun β)
  rw [happ] at hle
  exact le_of_mul_le_mul_right (by linarith) hnorm

end Cvs.Operator
