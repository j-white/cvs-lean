import Mathlib
import Cvs.Prolate.GevreyTailCircle
import Cvs.WeilForm.MaskedShift.AtomNormLaw
import Cvs.WeilForm.MaskedShift.ChainArithmetic
import Cvs.WeilForm.MaskedShift.ChebFactorMonotone
import Cvs.WeilForm.MaskedShift.CoherentFamilyDefs
import Cvs.WeilForm.MaskedShift.MaskedRotationFormIntegral
import Cvs.WeilForm.MaskedShift.MaskedShiftComposition
import Cvs.WeilForm.MaskedShift.MasksCompose
import Cvs.WeilForm.MaskedShift.PointwiseSchurEstimate
import Cvs.WeilForm.MaskedShift.PrimeAtomRealisation
import Cvs.WeilForm.MaskedShift.PrimeOperatorBudgetGap
import Cvs.WeilForm.MaskedShift.PrimePowerRotationNumber
import Cvs.WeilForm.MaskedShift.PrimeSideAtomBudget
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

/-!
# Exact Path-Law Sum-of-Squares Deficit for the Prime Operator

Replaces the unmasked Dirichlet identity of `B71` with the exact Path-Law chain-weighted
sum-of-squares decomposition relative to the staircase budget `atomBudget c P R`.
-/

noncomputable section

open MeasureTheory Real
open scoped InnerProductSpace NNReal

namespace Cvs.WeilForm.PrimeOperatorPathLawDeficit

open Cvs.Operator Cvs.WeilForm.MaskedShift.PrimeAtomRealisation Cvs.PrimeOperator

attribute [local instance] Classical.propDecidable

/-! ### 1. Algebraic Schur Ratio Square Completion -/

/-- The product of reciprocal square-root weight ratios is `1`. -/
theorem sqrt_ratio_mul_sqrt_ratio_inv {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    √(a / b) * √(b / a) = 1 := by
  have h1 : a / b * (b / a) = 1 := by field_simp
  rw [← Real.sqrt_mul (div_nonneg ha.le hb.le), h1, Real.sqrt_one]

/-- Exact square completion for a weighted difference with ratio `a / b`. -/
theorem sqrt_ratio_sq_sub {a b u v : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (√(a / b) * u - √(b / a) * v) ^ 2
      = (a / b) * u ^ 2 + (b / a) * v ^ 2 - 2 * (u * v) := by
  have h1 : √(a / b) ^ 2 = a / b := Real.sq_sqrt (div_nonneg ha.le hb.le)
  have h2 : √(b / a) ^ 2 = b / a := Real.sq_sqrt (div_nonneg hb.le ha.le)
  have h3 : √(a / b) * √(b / a) = 1 := sqrt_ratio_mul_sqrt_ratio_inv ha hb
  calc (√(a / b) * u - √(b / a) * v) ^ 2
      = √(a / b) ^ 2 * u ^ 2 + √(b / a) ^ 2 * v ^ 2
          - 2 * (√(a / b) * √(b / a)) * (u * v) := by ring
    _ = (a / b) * u ^ 2 + (b / a) * v ^ 2 - 2 * (u * v) := by rw [h1, h2, h3, mul_one]

/-- Exact square completion for a weighted sum with ratio `a / b`. -/
theorem sqrt_ratio_sq_add {a b u v : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (√(a / b) * u + √(b / a) * v) ^ 2
      = (a / b) * u ^ 2 + (b / a) * v ^ 2 + 2 * (u * v) := by
  have h1 : √(a / b) ^ 2 = a / b := Real.sq_sqrt (div_nonneg ha.le hb.le)
  have h2 : √(b / a) ^ 2 = b / a := Real.sq_sqrt (div_nonneg hb.le ha.le)
  have h3 : √(a / b) * √(b / a) = 1 := sqrt_ratio_mul_sqrt_ratio_inv ha hb
  calc (√(a / b) * u + √(b / a) * v) ^ 2
      = √(a / b) ^ 2 * u ^ 2 + √(b / a) ^ 2 * v ^ 2
          + 2 * (√(a / b) * √(b / a)) * (u * v) := by ring
    _ = (a / b) * u ^ 2 + (b / a) * v ^ 2 + 2 * (u * v) := by rw [h1, h2, h3, mul_one]

/-! ### 2. Non-Stationary Path-Law Schur Squares and Short-Chain Defect -/

/-- The non-stationary Path-Law Schur difference square along each Steinhaus chain. -/
def schurDiffSq (β : ℝ) (f : L2) (x : AddCircle (1 : ℝ)) : ℝ :=
  if rep x + β < 1 then
    (√(chainWeight β (rep x) / chainWeight β (rep x + β))
        * (f : AddCircle (1 : ℝ) → ℝ) (x + (β : AddCircle (1 : ℝ)))
      - √(chainWeight β (rep x + β) / chainWeight β (rep x))
        * (f : AddCircle (1 : ℝ) → ℝ) x) ^ 2
  else 0

/-- The non-stationary Path-Law Schur companion (sum) square along each Steinhaus chain. -/
def schurPlusSq (β : ℝ) (f : L2) (x : AddCircle (1 : ℝ)) : ℝ :=
  if rep x + β < 1 then
    (√(chainWeight β (rep x) / chainWeight β (rep x + β))
        * (f : AddCircle (1 : ℝ) → ℝ) (x + (β : AddCircle (1 : ℝ)))
      + √(chainWeight β (rep x + β) / chainWeight β (rep x))
        * (f : AddCircle (1 : ℝ) → ℝ) x) ^ 2
  else 0

/-- The pointwise Steinhaus short-chain capacity defect `(ν(⌈1/β⌉) - ν(ℓ(x))) · f(x)²`. -/
def shortChainDefect (β : ℝ) (f : L2) (x : AddCircle (1 : ℝ)) : ℝ :=
  (Cvs.Operator.chebFactor (cap 1 β)
      - Cvs.Operator.chebFactor (chainLength β (chainBase β (rep x))))
    * (f : AddCircle (1 : ℝ) → ℝ) x ^ 2

/-- The Path-Law Schur difference square is pointwise nonnegative. -/
theorem schurDiffSq_nonneg (β : ℝ) (f : L2) (x : AddCircle (1 : ℝ)) :
    0 ≤ schurDiffSq β f x := by
  unfold schurDiffSq
  split_ifs
  · exact sq_nonneg _
  · exact le_rfl

/-- The Path-Law Schur companion square is pointwise nonnegative. -/
theorem schurPlusSq_nonneg (β : ℝ) (f : L2) (x : AddCircle (1 : ℝ)) :
    0 ≤ schurPlusSq β f x := by
  unfold schurPlusSq
  split_ifs
  · exact sq_nonneg _
  · exact le_rfl

/-- The short-chain capacity defect is pointwise nonnegative for `0 < β`. -/
theorem shortChainDefect_nonneg {β : ℝ} (hβ : 0 < β) (f : L2) (x : AddCircle (1 : ℝ)) :
    0 ≤ shortChainDefect β f x := by
  unfold shortChainDefect
  have hle : Cvs.Operator.chebFactor (chainLength β (chainBase β (rep x)))
      ≤ Cvs.Operator.chebFactor (cap 1 β) :=
    Cvs.Operator.chebFactor_monotone
      (chainLength_le_cap β (chainBase β (rep x)) hβ
        (chainBase_nonneg β (rep x) hβ (rep_nonneg x)))
  exact mul_nonneg (sub_nonneg.mpr hle) (sq_nonneg _)

/-- Pointwise expansion of `schurDiffSq` into `Hf + Hb` minus twice the guarded cross term. -/
theorem schurDiffSq_eq {β : ℝ} (hβ : 0 < β) (f : L2) (x : AddCircle (1 : ℝ)) :
    schurDiffSq β f x
      = Hf β f x + Hb β f x
        - 2 * ((maskFwd β).indicator
            ((f : AddCircle (1 : ℝ) → ℝ) ∘ fun y => y + (β : AddCircle (1 : ℝ))) x
          * (f : AddCircle (1 : ℝ) → ℝ) x) := by
  unfold schurDiffSq Hf Hb
  by_cases hm : rep x + β < 1
  · have hmem : x ∈ maskFwd β := hm
    rw [if_pos hm, if_pos hm, if_pos hm, Set.indicator_of_mem hmem, Function.comp_apply]
    exact sqrt_ratio_sq_sub (chainWeight_pos β (rep x) hβ (rep_lt_one x))
      (chainWeight_pos β (rep x + β) hβ hm)
  · have hmem : x ∉ maskFwd β := hm
    rw [if_neg hm, if_neg hm, if_neg hm, Set.indicator_of_notMem hmem]
    ring

/-- Pointwise expansion of `schurPlusSq` into `Hf + Hb` plus twice the guarded cross term. -/
theorem schurPlusSq_eq {β : ℝ} (hβ : 0 < β) (f : L2) (x : AddCircle (1 : ℝ)) :
    schurPlusSq β f x
      = Hf β f x + Hb β f x
        + 2 * ((maskFwd β).indicator
            ((f : AddCircle (1 : ℝ) → ℝ) ∘ fun y => y + (β : AddCircle (1 : ℝ))) x
          * (f : AddCircle (1 : ℝ) → ℝ) x) := by
  unfold schurPlusSq Hf Hb
  by_cases hm : rep x + β < 1
  · have hmem : x ∈ maskFwd β := hm
    rw [if_pos hm, if_pos hm, if_pos hm, Set.indicator_of_mem hmem, Function.comp_apply]
    exact sqrt_ratio_sq_add (chainWeight_pos β (rep x) hβ (rep_lt_one x))
      (chainWeight_pos β (rep x + β) hβ hm)
  · have hmem : x ∉ maskFwd β := hm
    rw [if_neg hm, if_neg hm, if_neg hm, Set.indicator_of_notMem hmem]
    ring

/-- Exact pointwise equality `Bw + Hb = ν(ℓ(x)) · f(x)²` from the Schur recurrence. -/
theorem Bw_add_Hb_eq {β : ℝ} (hβ : 0 < β) (f : L2) (x : AddCircle (1 : ℝ)) :
    Bw β f x + Hb β f x
      = Cvs.Operator.chebFactor (chainLength β (chainBase β (rep x)))
        * (f : AddCircle (1 : ℝ) → ℝ) x ^ 2 := by
  unfold Bw Hb
  have hratio := Cvs.Operator.ratio_sum hβ (rep_nonneg x) (rep_lt_one x)
  by_cases h1 : rep x + β < 1 <;> by_cases h2 : β ≤ rep x <;>
    simp only [h1, h2, if_true, if_false] at hratio ⊢ <;>
    linear_combination (f : AddCircle (1 : ℝ) → ℝ) x ^ 2 * hratio

/-- Exact pointwise decomposition of `ν(⌈1/β⌉) · f(x)²` into `Bw + Hb + shortChainDefect`. -/
theorem Bw_add_Hb_add_shortChainDefect {β : ℝ} (hβ : 0 < β) (f : L2) (x : AddCircle (1 : ℝ)) :
    Bw β f x + Hb β f x + shortChainDefect β f x
      = Cvs.Operator.chebFactor (cap 1 β) * (f : AddCircle (1 : ℝ) → ℝ) x ^ 2 := by
  rw [Bw_add_Hb_eq hβ f x, shortChainDefect]
  ring

/-! ### 3. Integrability and Single-Atom Path-Law Sum-of-Squares Identities -/

/-- The guarded cross term of `S β` is integrable on `AddCircle 1`. -/
theorem integrable_cross_maskFwd {β : ℝ} (hβ : 0 < β) (f : L2) :
    Integrable (fun x : AddCircle (1 : ℝ) =>
      (maskFwd β).indicator
        ((f : AddCircle (1 : ℝ) → ℝ) ∘ fun y => y + (β : AddCircle (1 : ℝ))) x
        * (f : AddCircle (1 : ℝ) → ℝ) x) volume := by
  have hH : Integrable (fun x => Hf β f x + Hb β f x) volume :=
    (integrable_Hf hβ f).add (integrable_Hb hβ f)
  refine Integrable.mono' (hH.const_mul (1 / 2)) ?_ ?_
  · refine (AEStronglyMeasurable.indicator ?_ (measurableSet_maskFwd β)).mul (Lp.aestronglyMeasurable f)
    exact aesm_f_shift β f
  · refine Filter.Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs]
    have h := two_abs_cross_le hβ f x
    linarith

/-- `shortChainDefect β f` is integrable for `0 < β`. -/
theorem integrable_shortChainDefect {β : ℝ} (hβ : 0 < β) (f : L2) :
    Integrable (shortChainDefect β f) volume := by
  have hBH : Integrable (fun x => Bw β f x + Hb β f x) volume :=
    (integrable_Bw hβ f).add (integrable_Hb hβ f)
  have heq : shortChainDefect β f = fun x =>
      Cvs.Operator.chebFactor (cap 1 β) * (f : AddCircle (1 : ℝ) → ℝ) x ^ 2
        - (Bw β f x + Hb β f x) := by
    funext x
    linarith [Bw_add_Hb_add_shortChainDefect hβ f x]
  rw [heq]
  exact ((Cvs.Operator.integrable_sq f).const_mul _).sub hBH

/-- Folding `Hf` onto `Bw` holds for all `0 < β` (since both vanish when `1 ≤ β`). -/
theorem integral_Hf_eq_integral_Bw {β : ℝ} (hβ : 0 < β) (f : L2) :
    (∫ x : AddCircle (1 : ℝ), Hf β f x) = ∫ x : AddCircle (1 : ℝ), Bw β f x := by
  rcases lt_or_ge β 1 with hβ1 | hβ1
  · exact Cvs.Operator.integral_fwd_eq_bwd hβ hβ1 f
  · have h1 : Hf β f = fun _ => 0 := by
      funext x; unfold Hf
      rw [if_neg (by linarith [rep_nonneg x])]
    have h2 : Bw β f = fun _ => 0 := by
      funext x; unfold Bw
      rw [if_neg (by linarith [rep_lt_one x])]
    rw [h1, h2]

/-- The integral of `Hf + Hb + shortChainDefect` is `ν(⌈1/β⌉) · ‖f‖²`. -/
theorem integral_Hf_add_Hb_add_shortChainDefect {β : ℝ} (hβ : 0 < β) (f : L2) :
    (∫ x, Hf β f x) + (∫ x, Hb β f x) + (∫ x, shortChainDefect β f x)
      = Cvs.Operator.chebFactor (cap 1 β) * ‖f‖ ^ 2 := by
  have hBH : Integrable (fun x => Bw β f x + Hb β f x) volume :=
    (integrable_Bw hβ f).add (integrable_Hb hβ f)
  rw [integral_Hf_eq_integral_Bw hβ f,
    ← integral_add (integrable_Bw hβ f) (integrable_Hb hβ f),
    ← integral_add hBH (integrable_shortChainDefect hβ f)]
  have hcongr : (fun x => Bw β f x + Hb β f x + shortChainDefect β f x)
      = fun x => Cvs.Operator.chebFactor (cap 1 β) * (f : AddCircle (1 : ℝ) → ℝ) x ^ 2 :=
    funext (Bw_add_Hb_add_shortChainDefect hβ f)
  rw [hcongr, integral_const_mul, norm_sq_eq_integral]

/-- **Single-Atom Path-Law Sum-of-Squares Deficit Identity**: for any `0 < β`,
`ν(⌈1/β⌉) · ‖f‖² - ⟪W_β f, f⟫ = ∫ schurDiffSq β f + ∫ shortChainDefect β f`. -/
theorem chebFactor_norm_sq_sub_inner_W {β : ℝ} (hβ : 0 < β) (f : L2) :
    Cvs.Operator.chebFactor (cap 1 β) * ‖f‖ ^ 2
        - ⟪(S β + ContinuousLinearMap.adjoint (S β)) f, f⟫_ℝ
      = (∫ x, schurDiffSq β f x) + ∫ x, shortChainDefect β f x := by
  have hH : Integrable (fun x => Hf β f x + Hb β f x) volume :=
    (integrable_Hf hβ f).add (integrable_Hb hβ f)
  have heq : (∫ x, schurDiffSq β f x)
      = (∫ x, Hf β f x) + (∫ x, Hb β f x)
        - 2 * ∫ x, (maskFwd β).indicator
            ((f : AddCircle (1 : ℝ) → ℝ) ∘ fun y => y + (β : AddCircle (1 : ℝ))) x
          * (f : AddCircle (1 : ℝ) → ℝ) x := by
    have hfun : schurDiffSq β f = fun x => (Hf β f x + Hb β f x)
        - 2 * ((maskFwd β).indicator
            ((f : AddCircle (1 : ℝ) → ℝ) ∘ fun y => y + (β : AddCircle (1 : ℝ))) x
          * (f : AddCircle (1 : ℝ) → ℝ) x) := funext (schurDiffSq_eq hβ f)
    rw [hfun, integral_sub hH ((integrable_cross_maskFwd hβ f).const_mul 2),
      integral_add (integrable_Hf hβ f) (integrable_Hb hβ f), integral_const_mul]
  have hW : ⟪(S β + ContinuousLinearMap.adjoint (S β)) f, f⟫_ℝ
      = 2 * ∫ x, (maskFwd β).indicator
          ((f : AddCircle (1 : ℝ) → ℝ) ∘ fun y => y + (β : AddCircle (1 : ℝ))) x
        * (f : AddCircle (1 : ℝ) → ℝ) x := Cvs.Operator.inner_W_eq_integral β f
  linarith [integral_Hf_add_Hb_add_shortChainDefect hβ f, heq, hW]

/-- **Single-Atom Path-Law Companion Sum-of-Squares Identity**: for any `0 < β`,
`ν(⌈1/β⌉) · ‖f‖² + ⟪W_β f, f⟫ = ∫ schurPlusSq β f + ∫ shortChainDefect β f`. -/
theorem chebFactor_norm_sq_add_inner_W {β : ℝ} (hβ : 0 < β) (f : L2) :
    Cvs.Operator.chebFactor (cap 1 β) * ‖f‖ ^ 2
        + ⟪(S β + ContinuousLinearMap.adjoint (S β)) f, f⟫_ℝ
      = (∫ x, schurPlusSq β f x) + ∫ x, shortChainDefect β f x := by
  have hH : Integrable (fun x => Hf β f x + Hb β f x) volume :=
    (integrable_Hf hβ f).add (integrable_Hb hβ f)
  have heq : (∫ x, schurPlusSq β f x)
      = (∫ x, Hf β f x) + (∫ x, Hb β f x)
        + 2 * ∫ x, (maskFwd β).indicator
            ((f : AddCircle (1 : ℝ) → ℝ) ∘ fun y => y + (β : AddCircle (1 : ℝ))) x
          * (f : AddCircle (1 : ℝ) → ℝ) x := by
    have hfun : schurPlusSq β f = fun x => (Hf β f x + Hb β f x)
        + 2 * ((maskFwd β).indicator
            ((f : AddCircle (1 : ℝ) → ℝ) ∘ fun y => y + (β : AddCircle (1 : ℝ))) x
          * (f : AddCircle (1 : ℝ) → ℝ) x) := funext (schurPlusSq_eq hβ f)
    rw [hfun, integral_add hH ((integrable_cross_maskFwd hβ f).const_mul 2),
      integral_add (integrable_Hf hβ f) (integrable_Hb hβ f), integral_const_mul]
  have hW : ⟪(S β + ContinuousLinearMap.adjoint (S β)) f, f⟫_ℝ
      = 2 * ∫ x, (maskFwd β).indicator
          ((f : AddCircle (1 : ℝ) → ℝ) ∘ fun y => y + (β : AddCircle (1 : ℝ))) x
        * (f : AddCircle (1 : ℝ) → ℝ) x := Cvs.Operator.inner_W_eq_integral β f
  linarith [integral_Hf_add_Hb_add_shortChainDefect hβ f, heq, hW]

/-! ### 4. Prime-Operator Path-Law Sum-of-Squares Decomposition -/

/-- The summed non-stationary Path-Law Schur difference form of `primeOperator c P R`. -/
def atomSchurDiffForm (c P R : ℕ) (f : L2) : ℝ :=
  ∑ p ∈ primeRange P, ∑ r ∈ Finset.Icc 1 R,
    wt (p ^ r) * ∫ x, schurDiffSq ((rot c (p ^ r) : ℝ≥0) : ℝ) f x

/-- The summed non-stationary Path-Law Schur companion form of `primeOperator c P R`. -/
def atomSchurPlusForm (c P R : ℕ) (f : L2) : ℝ :=
  ∑ p ∈ primeRange P, ∑ r ∈ Finset.Icc 1 R,
    wt (p ^ r) * ∫ x, schurPlusSq ((rot c (p ^ r) : ℝ≥0) : ℝ) f x

/-- The summed Steinhaus short-chain capacity defect form of `primeOperator c P R`. -/
def atomShortChainForm (c P R : ℕ) (f : L2) : ℝ :=
  ∑ p ∈ primeRange P, ∑ r ∈ Finset.Icc 1 R,
    wt (p ^ r) * ∫ x, shortChainDefect ((rot c (p ^ r) : ℝ≥0) : ℝ) f x

/-- `atomSchurDiffForm` is manifestly nonnegative. -/
theorem atomSchurDiffForm_nonneg (c P R : ℕ) (f : L2) :
    0 ≤ atomSchurDiffForm c P R f :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    mul_nonneg (wt_nonneg _) (integral_nonneg (schurDiffSq_nonneg _ f))

/-- `atomSchurPlusForm` is manifestly nonnegative. -/
theorem atomSchurPlusForm_nonneg (c P R : ℕ) (f : L2) :
    0 ≤ atomSchurPlusForm c P R f :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    mul_nonneg (wt_nonneg _) (integral_nonneg (schurPlusSq_nonneg _ f))

/-- For `1 < c` and `1 < q`, the rotation step `rot c q` is strictly positive. -/
theorem coe_rot_pos {c q : ℕ} (hc : 1 < c) (hq : 1 < q) :
    0 < ((rot c q : ℝ≥0) : ℝ) := by
  have hlc : 0 < Real.log c := Cvs.PrimeOperator.log_pos_of_one_lt hc
  have hlq : 0 < Real.log q := Cvs.Operator.log_pos_of_one_lt hq
  have hdiv : 0 < Real.log q / Real.log c := div_pos hlq hlc
  rw [rot, Real.coe_toNNReal _ hdiv.le]
  exact hdiv

/-- For `1 < c` and `1 < q`, `cap 1 (rot c q) = cap (log c) (log q)`. -/
theorem cap_one_rot_eq {c q : ℕ} (hc : 1 < c) (hq : 1 < q) :
    cap 1 ((rot c q : ℝ≥0) : ℝ) = cap (Real.log c) (Real.log q) := by
  have hlc : 0 < Real.log c := Cvs.PrimeOperator.log_pos_of_one_lt hc
  have hlq : 0 < Real.log q := Cvs.Operator.log_pos_of_one_lt hq
  rw [rot, Real.coe_toNNReal _ (div_pos hlq hlc).le, cap_one_div]

/-- `atomShortChainForm` is manifestly nonnegative for `1 < c`. -/
theorem atomShortChainForm_nonneg {c : ℕ} (hc : 1 < c) (P R : ℕ) (f : L2) :
    0 ≤ atomShortChainForm c P R f := by
  refine Finset.sum_nonneg fun p hp => Finset.sum_nonneg fun r hr => ?_
  have hprime : p.Prime := (Finset.mem_filter.mp hp).2
  have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
  have h1 : 1 < p ^ r := Nat.one_lt_pow (by omega) hprime.one_lt
  exact mul_nonneg (wt_nonneg _)
    (integral_nonneg (shortChainDefect_nonneg (coe_rot_pos hc h1) f))

/-- Single-atom quadratic form deficit identity for `1 < c` and `1 < q`. -/
theorem inner_atom_eq_chebFactor_sub_schur {c q : ℕ} (hc : 1 < c) (hq : 1 < q) (f : L2) :
    ⟪atom c q f, f⟫_ℝ
      = Cvs.Operator.chebFactor (cap (Real.log c) (Real.log q)) * wt q * ‖f‖ ^ 2
        - wt q * ((∫ x, schurDiffSq ((rot c q : ℝ≥0) : ℝ) f x)
          + ∫ x, shortChainDefect ((rot c q : ℝ≥0) : ℝ) f x) := by
  have hβ : 0 < ((rot c q : ℝ≥0) : ℝ) := coe_rot_pos hc hq
  have hdef := chebFactor_norm_sq_sub_inner_W hβ f
  rw [cap_one_rot_eq hc hq] at hdef
  have hatom : ⟪atom c q f, f⟫_ℝ
      = wt q * ⟪(S ((rot c q : ℝ≥0) : ℝ)
          + ContinuousLinearMap.adjoint (S ((rot c q : ℝ≥0) : ℝ))) f, f⟫_ℝ := by
    rw [atom_eq, smul_apply, real_inner_smul_left]
    rfl
  rw [hatom]
  linear_combination -wt q * hdef

/-- Single-atom quadratic form companion identity for `1 < c` and `1 < q`. -/
theorem inner_atom_eq_schurPlus_sub_chebFactor {c q : ℕ} (hc : 1 < c) (hq : 1 < q) (f : L2) :
    ⟪atom c q f, f⟫_ℝ
      = wt q * ((∫ x, schurPlusSq ((rot c q : ℝ≥0) : ℝ) f x)
          + ∫ x, shortChainDefect ((rot c q : ℝ≥0) : ℝ) f x)
        - Cvs.Operator.chebFactor (cap (Real.log c) (Real.log q)) * wt q * ‖f‖ ^ 2 := by
  have hβ : 0 < ((rot c q : ℝ≥0) : ℝ) := coe_rot_pos hc hq
  have hdef := chebFactor_norm_sq_add_inner_W hβ f
  rw [cap_one_rot_eq hc hq] at hdef
  have hatom : ⟪atom c q f, f⟫_ℝ
      = wt q * ⟪(S ((rot c q : ℝ≥0) : ℝ)
          + ContinuousLinearMap.adjoint (S ((rot c q : ℝ≥0) : ℝ))) f, f⟫_ℝ := by
    rw [atom_eq, smul_apply, real_inner_smul_left]
    rfl
  rw [hatom]
  linear_combination wt q * hdef

/-- **Exact Path-Law Sum-of-Squares Identity for `primeOperator`**:
`⟪primeOperator c P R f, f⟫ = atomBudget c P R · ‖f‖² - (atomSchurDiffForm + atomShortChainForm)`. -/
theorem inner_primeOperator_eq_atomBudget_sub_schur {c : ℕ} (hc : 1 < c) (P R : ℕ) (f : L2) :
    ⟪primeOperator c P R f, f⟫_ℝ
      = atomBudget c P R * ‖f‖ ^ 2
        - (atomSchurDiffForm c P R f + atomShortChainForm c P R f) := by
  rw [inner_primeOperator, atomBudget, atomSchurDiffForm, atomShortChainForm,
    Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun r hr => ?_
  have hprime : p.Prime := (Finset.mem_filter.mp hp).2
  have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
  have h1 : 1 < p ^ r := Nat.one_lt_pow (by omega) hprime.one_lt
  rw [inner_atom_eq_chebFactor_sub_schur hc h1 f]
  ring

/-- **Exact Path-Law Companion Identity for `primeOperator`**:
`⟪primeOperator c P R f, f⟫ = (atomSchurPlusForm + atomShortChainForm) - atomBudget c P R · ‖f‖²`. -/
theorem inner_primeOperator_eq_schurPlus_sub_atomBudget {c : ℕ} (hc : 1 < c) (P R : ℕ) (f : L2) :
    ⟪primeOperator c P R f, f⟫_ℝ
      = (atomSchurPlusForm c P R f + atomShortChainForm c P R f)
        - atomBudget c P R * ‖f‖ ^ 2 := by
  rw [inner_primeOperator, atomBudget, atomSchurPlusForm, atomShortChainForm,
    Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun r hr => ?_
  have hprime : p.Prime := (Finset.mem_filter.mp hp).2
  have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
  have h1 : 1 < p ^ r := Nat.one_lt_pow (by omega) hprime.one_lt
  rw [inner_atom_eq_schurPlus_sub_chebFactor hc h1 f]
  ring

end Cvs.WeilForm.PrimeOperatorPathLawDeficit
