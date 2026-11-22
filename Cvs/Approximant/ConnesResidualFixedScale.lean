import Mathlib
import Cvs.Approximant.ConnesErrorColumn
import Cvs.Approximant.ConnesFullColumnBudget
import Cvs.Approximant.ConnesTailWeightedEnergy
import Cvs.Approximant.ConnesVectorRealScale
import Cvs.Approximant.CosineColumnTailPairing
import Cvs.Finite.DiscreteTwoGap
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationQuadraticForm
import Cvs.Finite.TruncationZeroFreeOffAxes
import Cvs.Finite.WindowCosineBessel
import Cvs.Route.JointGapFromResidual
import Cvs.Upstream.SymmetricMatrixBottom
import Cvs.WeilForm.EvenBoundaryKernelBound
import Cvs.WeilForm.ThetaSpaceParseval

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The actual Connes residual at a fixed scale

The complete tail column has square-summable cosine coordinates. Its centered
variance is the limit of the actual finite arithmetic residual as the cosine
cutoff grows, with the vanishing form truncation column retained in the passage.
-/

noncomputable section

open Real Matrix Finset Filter MeasureTheory
open scoped Topology

namespace Cvs.Approximant.ConnesResidualFixedScale
open Cvs.ZeroCounting

open Cvs.Finite.SymmetricModeSet (Idx mode negI)

/-- The physical test for one scalar cosine frequency. -/
def scalarTest (x n : ℕ) : ℝ → ℝ :=
  Cvs.Approximant.CosineColumnTailPairing.pullTest (log x) (fun s => cos (2 * π * (n : ℝ) / log x * s))

/-- The actual complete tail pairing against one scalar cosine frequency. -/
def scalarTail (x n : ℕ) : ℝ :=
  -Cvs.WeilForm.ThetaSpaceParseval.weilθ (Cvs.Approximant.CosineColumnTailPairing.connesTail x) (scalarTest x n)

/-- The complete coefficient square mass, with both signed copies normalized. -/
def coefficientMass (x : ℕ) : ℝ :=
  Cvs.Approximant.ConnesTailWeightedEnergy.coef x 0 ^ 2 + (1 / 2 : ℝ) * ∑' k : ℕ, Cvs.Approximant.ConnesTailWeightedEnergy.coef x (k + 1) ^ 2

/-- The square mass of the complete actual signed tail column. -/
def tailMass (x : ℕ) : ℝ :=
  scalarTail x 0 ^ 2 + 2 * ∑' k : ℕ, scalarTail x (k + 1) ^ 2

/-- The pairing of the complete coefficient sequence with its actual tail column. -/
def pairingMass (x : ℕ) : ℝ :=
  Cvs.Approximant.ConnesTailWeightedEnergy.coef x 0 * scalarTail x 0 +
    ∑' k : ℕ, Cvs.Approximant.ConnesTailWeightedEnergy.coef x (k + 1) * scalarTail x (k + 1)

/-- The dimension-free centered variance of the complete actual tail column. -/
def residualLimit (x : ℕ) : ℝ :=
  (tailMass x - pairingMass x ^ 2 / coefficientMass x) /
    (log x ^ 2 * coefficientMass x)

/-- The limiting actual normalized Rayleigh value. -/
def rayleighLimit (x : ℕ) : ℝ := pairingMass x / (log x * coefficientMass x)

/-- A signed coordinate row represents exactly its one cosine frequency. -/
theorem cosineSum_cosineRow (L : ℝ) (N : ℕ) (i : Idx N) (s : ℝ) :
    Cvs.Approximant.CosineColumnTailPairing.cosineSum L N (Cvs.Approximant.CosineColumnTailPairing.cosineRow N i) s =
      cos (Cvs.Finite.TruncationZeroFreeOffAxes.omega L (mode N) i * s) := by
  classical
  have he (j : Idx N) : negI N j = i ↔ j = negI N i := by
    constructor
    · intro h
      rw [← h, Cvs.Finite.SymmetricModeSet.negI_involutive N j]
    · intro h
      rw [h, Cvs.Finite.SymmetricModeSet.negI_involutive N i]
  have hterm (j : Idx N) :
      Cvs.Approximant.CosineColumnTailPairing.cosineRow N i j * cos (Cvs.Finite.TruncationZeroFreeOffAxes.omega L (mode N) j * s) =
        (if j = i then cos (Cvs.Finite.TruncationZeroFreeOffAxes.omega L (mode N) j * s) / 2 else 0) +
        (if j = negI N i then cos (Cvs.Finite.TruncationZeroFreeOffAxes.omega L (mode N) j * s) / 2 else 0) := by
    simp only [Cvs.Approximant.CosineColumnTailPairing.cosineRow, Cvs.Finite.TruncationQuadraticForm.evenPart, Pi.single_apply, he]
    split_ifs <;> ring
  unfold Cvs.Approximant.CosineColumnTailPairing.cosineSum
  rw [sum_congr rfl (fun j _ => hterm j), sum_add_distrib]
  simp only [sum_ite_eq', mem_univ, if_true]
  have hn : Cvs.Finite.TruncationZeroFreeOffAxes.omega L (mode N) (negI N i) = -Cvs.Finite.TruncationZeroFreeOffAxes.omega L (mode N) i := by
    simp only [Cvs.Finite.TruncationZeroFreeOffAxes.omega, Cvs.Finite.SymmetricModeSet.mode_negI, Int.cast_neg]
    ring
  rw [hn, neg_mul, cos_neg]
  ring

theorem modeTest_cosineRow_none (x N : ℕ) :
    Cvs.Approximant.CosineColumnTailPairing.modeTest x N (Cvs.Approximant.CosineColumnTailPairing.cosineRow N none) = scalarTest x 0 := by
  unfold Cvs.Approximant.CosineColumnTailPairing.modeTest scalarTest
  congr 1
  funext s
  rw [cosineSum_cosineRow]
  simp [Cvs.Finite.TruncationZeroFreeOffAxes.omega, mode]

theorem modeTest_cosineRow_some (x N : ℕ) (k : Fin N) (b : Bool) :
    Cvs.Approximant.CosineColumnTailPairing.modeTest x N (Cvs.Approximant.CosineColumnTailPairing.cosineRow N (some (k,b))) = scalarTest x (k.val+1) := by
  unfold Cvs.Approximant.CosineColumnTailPairing.modeTest scalarTest
  congr 1
  funext s
  rw [cosineSum_cosineRow]
  cases b
  · simp only [Cvs.Finite.TruncationZeroFreeOffAxes.omega, mode, Bool.false_eq_true, if_false, Int.cast_neg,
      Int.cast_add, Int.cast_natCast, Int.cast_one, Nat.cast_add, Nat.cast_one]
    rw [show 2 * π * -((k.val : ℝ)+1) / log x * s =
      -(2 * π * ((k.val : ℝ)+1) / log x * s) by ring, cos_neg]
  · simp [Cvs.Finite.TruncationZeroFreeOffAxes.omega, mode]

/-- Tail coordinates at a fixed scalar frequency do not depend on the finite cutoff. -/
theorem tailColumn_none (x N : ℕ) : Cvs.Approximant.ConnesErrorColumn.tailColumn x N none = scalarTail x 0 := by
  unfold Cvs.Approximant.ConnesErrorColumn.tailColumn scalarTail
  rw [modeTest_cosineRow_none]

theorem tailColumn_some (x N : ℕ) (k : Fin N) (b : Bool) :
    Cvs.Approximant.ConnesErrorColumn.tailColumn x N (some (k,b)) = scalarTail x (k.val+1) := by
  unfold Cvs.Approximant.ConnesErrorColumn.tailColumn scalarTail
  rw [modeTest_cosineRow_some]

theorem connesCoef_none (x N : ℕ) : Cvs.Approximant.ConnesVectorRealScale.connesCoef x N none = Cvs.Approximant.ConnesTailWeightedEnergy.coef x 0 := by
  simp [Cvs.Approximant.ConnesVectorRealScale.connesCoef, Cvs.Finite.SymmetricModeSet.coeff, Cvs.Approximant.ConnesTailWeightedEnergy.coef]

theorem connesCoef_some (x N : ℕ) (k : Fin N) (b : Bool) :
    Cvs.Approximant.ConnesVectorRealScale.connesCoef x N (some (k,b)) = Cvs.Approximant.ConnesTailWeightedEnergy.coef x (k.val+1) / 2 := by
  simp [Cvs.Approximant.ConnesVectorRealScale.connesCoef, Cvs.Finite.SymmetricModeSet.coeff, Cvs.Approximant.ConnesTailWeightedEnergy.coef, k.isLt]

/-- The finite signed coefficient mass is the correctly normalized scalar partial sum. -/
theorem connesCoef_sq_eq (x N : ℕ) :
    Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ⬝ᵥ Cvs.Approximant.ConnesVectorRealScale.connesCoef x N =
      Cvs.Approximant.ConnesTailWeightedEnergy.coef x 0 ^ 2 + (1 / 2 : ℝ) * ∑ k ∈ range N, Cvs.Approximant.ConnesTailWeightedEnergy.coef x (k+1) ^ 2 := by
  rw [show Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ⬝ᵥ Cvs.Approximant.ConnesVectorRealScale.connesCoef x N =
    ∑ i, Cvs.Approximant.ConnesVectorRealScale.connesCoef x N i ^ 2 by simp only [dotProduct, sq]]
  rw [Cvs.WeilForm.EvenBoundaryKernelBound.idx_even_sq N _ (Cvs.Approximant.ConnesVectorRealScale.connesCoef_even x N), connesCoef_none]
  simp_rw [connesCoef_some]
  rw [← Fin.sum_univ_eq_sum_range]
  congr 1
  rw [mul_sum, mul_sum]
  apply sum_congr rfl
  intro k _
  ring

/-- The finite signed tail mass is its scalar partial square sum. -/
theorem tailColumn_sq_eq (x N : ℕ) :
    Cvs.Approximant.ConnesErrorColumn.tailColumn x N ⬝ᵥ Cvs.Approximant.ConnesErrorColumn.tailColumn x N =
      scalarTail x 0 ^ 2 + 2 * ∑ k ∈ range N, scalarTail x (k+1) ^ 2 := by
  rw [show Cvs.Approximant.ConnesErrorColumn.tailColumn x N ⬝ᵥ Cvs.Approximant.ConnesErrorColumn.tailColumn x N =
    ∑ i, Cvs.Approximant.ConnesErrorColumn.tailColumn x N i ^ 2 by simp only [dotProduct, sq],
    Cvs.WeilForm.EvenBoundaryKernelBound.idx_even_sq N _ (Cvs.Approximant.ConnesFullColumnBudget.tailColumn_even x N), tailColumn_none]
  simp_rw [tailColumn_some]
  rw [Fin.sum_univ_eq_sum_range (fun k => scalarTail x (k+1) ^ 2) N]

/-- The finite coefficient-tail pairing has one copy of each scalar positive mode. -/
theorem tailColumn_dot_coef_eq (x N : ℕ) :
    Cvs.Approximant.ConnesErrorColumn.tailColumn x N ⬝ᵥ Cvs.Approximant.ConnesVectorRealScale.connesCoef x N =
      Cvs.Approximant.ConnesTailWeightedEnergy.coef x 0 * scalarTail x 0 +
        ∑ k ∈ range N, Cvs.Approximant.ConnesTailWeightedEnergy.coef x (k+1) * scalarTail x (k+1) := by
  unfold dotProduct
  rw [Fintype.sum_option, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, tailColumn_none, tailColumn_some,
    connesCoef_none, connesCoef_some]
  rw [← Fin.sum_univ_eq_sum_range]
  congr 1
  · ring
  · apply sum_congr rfl
    intro k _
    ring

theorem summable_coef_sq {x : ℕ} (hx : 80 ≤ 2 * π * x) :
    Summable (fun k : ℕ => Cvs.Approximant.ConnesTailWeightedEnergy.coef x (k+1) ^ 2) := by
  apply Summable.of_nonneg_of_le (fun k => sq_nonneg _) _ (Cvs.Approximant.ConnesTailWeightedEnergy.summable_coefTerm hx)
  intro k
  have hl : 0 ≤ log ((k+1:ℕ):ℝ) := log_nonneg (by exact_mod_cast (show 1 ≤ k+1 by omega))
  unfold Cvs.Approximant.ConnesTailWeightedEnergy.coefTerm Cvs.Approximant.ConnesTailWeightedEnergy.logWeight
  nlinarith [sq_nonneg (Cvs.Approximant.ConnesTailWeightedEnergy.coef x (k+1)),
    mul_nonneg (sq_nonneg (log ((k+1:ℕ):ℝ))) (sq_nonneg (Cvs.Approximant.ConnesTailWeightedEnergy.coef x (k+1))),
    mul_nonneg hl (sq_nonneg (Cvs.Approximant.ConnesTailWeightedEnergy.coef x (k+1)))]

/-- The actual tail coordinates are square summable by the uniform complete-column bound. -/
theorem summable_scalarTail_sq {x : ℕ} (hx : 80 ≤ 2 * π * x) :
    Summable (fun k : ℕ => scalarTail x (k+1) ^ 2) := by
  apply summable_of_sum_range_le (fun k => sq_nonneg _) (c := Cvs.Approximant.ConnesFullColumnBudget.fullColumnBudget x ^ 2)
  intro N
  have h := Cvs.Approximant.ConnesFullColumnBudget.tailColumn_sq_le hx N
  have h' : Cvs.Approximant.ConnesErrorColumn.tailColumn x N ⬝ᵥ Cvs.Approximant.ConnesErrorColumn.tailColumn x N ≤
      Cvs.Approximant.ConnesFullColumnBudget.fullColumnBudget x ^ 2 := by simpa only [dotProduct, sq] using h
  rw [tailColumn_sq_eq] at h'
  have hsum : 0 ≤ ∑ k ∈ range N, scalarTail x (k+1) ^ 2 := sum_nonneg (fun _ _ => sq_nonneg _)
  nlinarith [sq_nonneg (scalarTail x 0)]

/-- The actual coefficient-tail cross series is absolutely summable. -/
theorem summable_coef_tail {x : ℕ} (hx : 80 ≤ 2 * π * x) :
    Summable (fun k : ℕ => Cvs.Approximant.ConnesTailWeightedEnergy.coef x (k+1) * scalarTail x (k+1)) := by
  apply Summable.of_norm_bounded ((summable_coef_sq hx).add (summable_scalarTail_sq hx))
  intro k
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> nlinarith [sq_nonneg (Cvs.Approximant.ConnesTailWeightedEnergy.coef x (k+1) - scalarTail x (k+1)),
    sq_nonneg (Cvs.Approximant.ConnesTailWeightedEnergy.coef x (k+1) + scalarTail x (k+1))]

theorem tendsto_coefficientMass {x : ℕ} (hx : 80 ≤ 2 * π * x) :
    Tendsto (fun N => Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ⬝ᵥ Cvs.Approximant.ConnesVectorRealScale.connesCoef x N)
      atTop (𝓝 (coefficientMass x)) := by
  have h := (tendsto_const_nhds (x := Cvs.Approximant.ConnesTailWeightedEnergy.coef x 0 ^ 2)).add
    ((summable_coef_sq hx).hasSum.tendsto_sum_nat.const_mul (1/2:ℝ))
  simpa only [coefficientMass, connesCoef_sq_eq] using h

theorem tendsto_tailMass {x : ℕ} (hx : 80 ≤ 2 * π * x) :
    Tendsto (fun N => Cvs.Approximant.ConnesErrorColumn.tailColumn x N ⬝ᵥ Cvs.Approximant.ConnesErrorColumn.tailColumn x N)
      atTop (𝓝 (tailMass x)) := by
  have h := (tendsto_const_nhds (x := scalarTail x 0 ^ 2)).add
    ((summable_scalarTail_sq hx).hasSum.tendsto_sum_nat.const_mul 2)
  simpa only [tailMass, tailColumn_sq_eq] using h

theorem tendsto_pairingMass {x : ℕ} (hx : 80 ≤ 2 * π * x) :
    Tendsto (fun N => Cvs.Approximant.ConnesErrorColumn.tailColumn x N ⬝ᵥ Cvs.Approximant.ConnesVectorRealScale.connesCoef x N)
      atTop (𝓝 (pairingMass x)) := by
  have h := (tendsto_const_nhds (x := Cvs.Approximant.ConnesTailWeightedEnergy.coef x 0 * scalarTail x 0)).add
    (summable_coef_tail hx).hasSum.tendsto_sum_nat
  simpa only [pairingMass, tailColumn_dot_coef_eq] using h

/-- Every finite actual coefficient mass is bounded by the complete mass. -/
theorem finite_coefficientMass_le {x : ℕ} (hx : 80 ≤ 2 * π * x) (N : ℕ) :
    Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ⬝ᵥ Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ≤ coefficientMass x := by
  rw [connesCoef_sq_eq]
  unfold coefficientMass
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
    ((summable_coef_sq hx).sum_le_tsum (range N) (fun k _ => sq_nonneg _))
      (by norm_num : (0:ℝ) ≤ 1/2))

/-- One nonzero finite actual coefficient vector makes the complete mass positive. -/
theorem coefficientMass_pos {x : ℕ} (hx : 80 ≤ 2 * π * x)
    (hpos : ∃ N, Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ⬝ᵥ Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ≠ 0) :
    0 < coefficientMass x := by
  obtain ⟨N,hN⟩ := hpos
  exact (lt_of_le_of_ne (Cvs.Upstream.SymmetricMatrixBottom.dotProduct_self_nonneg' _) (Ne.symm hN)).trans_le
    (finite_coefficientMass_le hx N)

theorem eventually_connesCoef_ne_zero {x : ℕ} (hx : 80 ≤ 2 * π * x)
    (hpos : ∃ N, Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ⬝ᵥ Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ≠ 0) :
    ∀ᶠ N : ℕ in atTop, Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ⬝ᵥ Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ≠ 0 := by
  filter_upwards [(tendsto_coefficientMass hx).eventually
    (lt_mem_nhds (coefficientMass_pos hx hpos))] with N hN
  exact hN.ne'

private theorem abs_dot_le_sqrt {ι : Type*} [Fintype ι] (u v : ι → ℝ) :
    |u ⬝ᵥ v| ≤ √(u ⬝ᵥ u) * √(v ⬝ᵥ v) := by
  have h := Real.sum_mul_le_sqrt_mul_sqrt univ (fun i => |u i|) (fun i => |v i|)
  simp only [sq_abs] at h
  have ha := Finset.abs_sum_le_sum_abs (fun i => u i * v i) univ
  simp only [abs_mul] at ha
  simpa only [dotProduct, sq] using ha.trans h

private theorem tendsto_varying_dot_zero (ι : ℕ → Type*) [∀ N, Fintype (ι N)]
    (u e : (N : ℕ) → ι N → ℝ) (C : ℝ)
    (hu : ∀ N, u N ⬝ᵥ u N ≤ C)
    (he : Tendsto (fun N => e N ⬝ᵥ e N) atTop (𝓝 0)) :
    Tendsto (fun N => u N ⬝ᵥ e N) atTop (𝓝 0) := by
  have hlim : Tendsto (fun N => √C * √(e N ⬝ᵥ e N)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, sqrt_zero, mul_zero] using
      ((Real.continuous_sqrt.tendsto 0).comp he).const_mul (√C)
  apply squeeze_zero_norm _ hlim
  intro N
  rw [Real.norm_eq_abs]
  exact (abs_dot_le_sqrt _ _).trans (mul_le_mul_of_nonneg_right
    (sqrt_le_sqrt (hu N)) (sqrt_nonneg _))

private theorem center_sq {ι : Type*} [Fintype ι] (u α : ι → ℝ)
    (hα : α ⬝ᵥ α ≠ 0) :
    Cvs.Approximant.ConnesErrorColumn.center u α ⬝ᵥ Cvs.Approximant.ConnesErrorColumn.center u α = u ⬝ᵥ u - (u ⬝ᵥ α) ^ 2 / (α ⬝ᵥ α) := by
  simp only [Cvs.Approximant.ConnesErrorColumn.center, sub_dotProduct, dotProduct_sub, smul_dotProduct,
    dotProduct_smul, smul_eq_mul, dotProduct_comm α u]
  field_simp
  ring

/-- The orthogonally centered complete tail has the exact limiting variance. -/
theorem tendsto_centered_tailMass {x : ℕ} (hx : 80 ≤ 2 * π * x)
    (hpos : ∃ N, Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ⬝ᵥ Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ≠ 0) :
    Tendsto (fun N =>
      Cvs.Approximant.ConnesErrorColumn.center (Cvs.Approximant.ConnesErrorColumn.tailColumn x N) (Cvs.Approximant.ConnesVectorRealScale.connesCoef x N) ⬝ᵥ
        Cvs.Approximant.ConnesErrorColumn.center (Cvs.Approximant.ConnesErrorColumn.tailColumn x N) (Cvs.Approximant.ConnesVectorRealScale.connesCoef x N))
      atTop (𝓝 (tailMass x - pairingMass x ^ 2 / coefficientMass x)) := by
  have h := (tendsto_tailMass hx).sub
    (((tendsto_pairingMass hx).pow 2).div (tendsto_coefficientMass hx)
      (coefficientMass_pos hx hpos).ne')
  apply h.congr'
  filter_upwards [eventually_connesCoef_ne_zero hx hpos] with N hN
  exact (center_sq _ _ hN).symm

/-- The centered error remains negligible when paired with the entire growing tail column. -/
theorem tendsto_centered_tail_error_zero {x : ℕ} (hx : 80 ≤ 2 * π * x) :
    Tendsto (fun N =>
      Cvs.Approximant.ConnesErrorColumn.center (Cvs.Approximant.ConnesErrorColumn.tailColumn x N) (Cvs.Approximant.ConnesVectorRealScale.connesCoef x N) ⬝ᵥ
        Cvs.Approximant.ConnesErrorColumn.centeredErrorColumn hx N) atTop (𝓝 0) := by
  apply tendsto_varying_dot_zero (fun N => Idx N) _ _ (Cvs.Approximant.ConnesFullColumnBudget.fullColumnBudget x ^ 2)
  · intro N
    exact (Cvs.Approximant.ConnesErrorColumn.center_sq_le _ _).trans (by
      simpa only [dotProduct, sq] using Cvs.Approximant.ConnesFullColumnBudget.tailColumn_sq_le hx N)
  · simpa only [dotProduct, sq] using Cvs.Approximant.ConnesErrorColumn.tendsto_centeredErrorColumn_sq_zero hx

/-- The whole squared centered tail-minus-error column converges to the actual infinite variance. -/
theorem tendsto_centered_columnMass {x : ℕ} (hx : 80 ≤ 2 * π * x)
    (hpos : ∃ N, Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ⬝ᵥ Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ≠ 0) :
    Tendsto (fun N =>
      (Cvs.Approximant.ConnesErrorColumn.center (Cvs.Approximant.ConnesErrorColumn.tailColumn x N) (Cvs.Approximant.ConnesVectorRealScale.connesCoef x N) -
        Cvs.Approximant.ConnesErrorColumn.centeredErrorColumn hx N) ⬝ᵥ
      (Cvs.Approximant.ConnesErrorColumn.center (Cvs.Approximant.ConnesErrorColumn.tailColumn x N) (Cvs.Approximant.ConnesVectorRealScale.connesCoef x N) -
        Cvs.Approximant.ConnesErrorColumn.centeredErrorColumn hx N))
      atTop (𝓝 (tailMass x - pairingMass x ^ 2 / coefficientMass x)) := by
  have he : Tendsto (fun N => Cvs.Approximant.ConnesErrorColumn.centeredErrorColumn hx N ⬝ᵥ
      Cvs.Approximant.ConnesErrorColumn.centeredErrorColumn hx N) atTop (𝓝 0) := by
    simpa only [dotProduct, sq] using Cvs.Approximant.ConnesErrorColumn.tendsto_centeredErrorColumn_sq_zero hx
  have h := ((tendsto_centered_tailMass hx hpos).sub
    ((tendsto_centered_tail_error_zero hx).const_mul 2)).add he
  simp only [mul_zero, sub_zero, add_zero] at h
  apply h.congr
  intro N
  simp only [sub_dotProduct, dotProduct_sub,
    dotProduct_comm (Cvs.Approximant.ConnesErrorColumn.centeredErrorColumn hx N)
      (Cvs.Approximant.ConnesErrorColumn.center (Cvs.Approximant.ConnesErrorColumn.tailColumn x N) (Cvs.Approximant.ConnesVectorRealScale.connesCoef x N))]
  ring

/-- The actual finite arithmetic residual tends to a fixed-scale infinite centered variance. -/
theorem tendsto_connes_residual {x : ℕ} (hx : 80 ≤ 2 * π * x)
    (hpos : ∃ N, Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ⬝ᵥ Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ≠ 0) :
    Tendsto (fun N => Cvs.Route.JointGapFromResidual.residualSq x (Nat.clog 2 x) (log x) N
      (Cvs.Approximant.ConnesVectorRealScale.connesVec (fun _ => N) x)) atTop (𝓝 (residualLimit x)) := by
  have hL : 0 < log (x:ℝ) := log_pos (Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx)
  have hd := (tendsto_coefficientMass hx).const_mul (log (x:ℝ) ^ 2)
  have h := (tendsto_centered_columnMass hx hpos).div hd
    (mul_ne_zero (pow_ne_zero 2 hL.ne') (coefficientMass_pos hx hpos).ne')
  change Tendsto _ atTop (𝓝 (residualLimit x)) at h
  apply h.congr'
  filter_upwards [eventually_connesCoef_ne_zero hx hpos] with N hN
  have he := Cvs.Approximant.ConnesErrorColumn.connes_residual_eq_tail_error hx N hN
  dsimp only at he
  have hr : Cvs.Route.JointGapFromResidual.residualSq x (Nat.clog 2 x) (log x) N
      (Cvs.Approximant.ConnesVectorRealScale.connesVec (fun _ => N) x) =
      ((Cvs.Approximant.ConnesErrorColumn.center (Cvs.Approximant.ConnesErrorColumn.tailColumn x N) (Cvs.Approximant.ConnesVectorRealScale.connesCoef x N) -
          Cvs.Approximant.ConnesErrorColumn.centeredErrorColumn hx N) ⬝ᵥ
        (Cvs.Approximant.ConnesErrorColumn.center (Cvs.Approximant.ConnesErrorColumn.tailColumn x N) (Cvs.Approximant.ConnesVectorRealScale.connesCoef x N) -
          Cvs.Approximant.ConnesErrorColumn.centeredErrorColumn hx N)) /
        (log x ^ 2 * (Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ⬝ᵥ Cvs.Approximant.ConnesVectorRealScale.connesCoef x N)) := by
    apply (eq_div_iff (mul_ne_zero (pow_ne_zero 2 hL.ne') hN)).mpr
    simpa only [mul_comm] using he
  exact hr.symm

/-- The limiting centered tail variance is nonnegative. -/
theorem centered_variance_nonneg {x : ℕ} (hx : 80 ≤ 2 * π * x)
    (hpos : ∃ N, Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ⬝ᵥ Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ≠ 0) :
    0 ≤ tailMass x - pairingMass x ^ 2 / coefficientMass x := by
  exact ge_of_tendsto (tendsto_centered_tailMass hx hpos)
    (Eventually.of_forall fun N => Cvs.Upstream.SymmetricMatrixBottom.dotProduct_self_nonneg' _)

theorem residualLimit_nonneg {x : ℕ} (hx : 80 ≤ 2 * π * x)
    (hpos : ∃ N, Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ⬝ᵥ Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ≠ 0) :
    0 ≤ residualLimit x :=
  div_nonneg (centered_variance_nonneg hx hpos)
    (mul_nonneg (sq_nonneg _) (coefficientMass_pos hx hpos).le)

private theorem rayleigh_eq_tail_error {x : ℕ} (hx : 80 ≤ 2 * π * x) (N : ℕ)
    (hN : Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ⬝ᵥ Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ≠ 0) :
    let α := Cvs.Approximant.ConnesVectorRealScale.connesCoef x N
    let v := Cvs.Approximant.ConnesVectorRealScale.connesVec (fun _ => N) x
    v ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M x (Nat.clog 2 x) (log x) (mode N) *ᵥ v) =
      (Cvs.Approximant.ConnesErrorColumn.tailColumn x N ⬝ᵥ α - Cvs.Approximant.ConnesErrorColumn.errorColumn hx N ⬝ᵥ α) /
        (log x * (α ⬝ᵥ α)) := by
  dsimp only
  let α := Cvs.Approximant.ConnesVectorRealScale.connesCoef x N
  let M := Cvs.Finite.TruncationQuadraticForm.M x (Nat.clog 2 x) (log x) (mode N)
  have hL : log (x:ℝ) ≠ 0 := (log_pos (Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx)).ne'
  have hC : Cvs.Approximant.CosineColumnTailPairing.connesColumn hx N = log x • (M *ᵥ α) :=
    funext (Cvs.Approximant.CosineColumnTailPairing.connesColumn_eq_mulVec hx N)
  have hc := congrArg (fun u : Idx N → ℝ => u ⬝ᵥ α)
    (Cvs.Approximant.ConnesErrorColumn.connesColumn_eq_tail_sub_error hx N)
  rw [hC, smul_dotProduct, smul_eq_mul, sub_dotProduct,
    dotProduct_comm (M *ᵥ α) α] at hc
  have hq : Cvs.Approximant.ConnesVectorRealScale.connesVec (fun _ => N) x ⬝ᵥ
      (M *ᵥ Cvs.Approximant.ConnesVectorRealScale.connesVec (fun _ => N) x) = (α ⬝ᵥ (M *ᵥ α)) / (α ⬝ᵥ α) := by
    have hv : Cvs.Approximant.ConnesVectorRealScale.connesVec (fun _ => N) x = (√(α ⬝ᵥ α))⁻¹ • α := by
      simp only [Cvs.Approximant.ConnesVectorRealScale.connesVec, if_neg hN]
      rfl
    rw [hv, Cvs.Finite.DiscreteTwoGap.quad_smul, inv_pow, sq_sqrt (Cvs.Upstream.SymmetricMatrixBottom.dotProduct_self_nonneg' α)]
    ring
  change _ = _
  rw [hq]
  apply (div_eq_div_iff hN (mul_ne_zero hL hN)).mpr
  change (α ⬝ᵥ (M *ᵥ α)) * (log x * (α ⬝ᵥ α)) =
    (Cvs.Approximant.ConnesErrorColumn.tailColumn x N ⬝ᵥ α - Cvs.Approximant.ConnesErrorColumn.errorColumn hx N ⬝ᵥ α) * (α ⬝ᵥ α)
  rw [← hc]
  ring

/-- The actual normalized Connes Rayleigh values converge with no cutoff-dependent budget. -/
theorem tendsto_connes_rayleigh {x : ℕ} (hx : 80 ≤ 2 * π * x)
    (hpos : ∃ N, Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ⬝ᵥ Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ≠ 0) :
    Tendsto (fun N =>
      Cvs.Approximant.ConnesVectorRealScale.connesVec (fun _ => N) x ⬝ᵥ
        (Cvs.Finite.TruncationQuadraticForm.M x (Nat.clog 2 x) (log x) (mode N) *ᵥ Cvs.Approximant.ConnesVectorRealScale.connesVec (fun _ => N) x))
      atTop (𝓝 (rayleighLimit x)) := by
  have herr : Tendsto (fun N => Cvs.Approximant.ConnesErrorColumn.errorColumn hx N ⬝ᵥ Cvs.Approximant.ConnesVectorRealScale.connesCoef x N)
      atTop (𝓝 0) := by
    have h := tendsto_varying_dot_zero (fun N => Idx N) (Cvs.Approximant.ConnesVectorRealScale.connesCoef x)
      (Cvs.Approximant.ConnesErrorColumn.errorColumn hx) (coefficientMass x) (finite_coefficientMass_le hx)
      (by simpa only [dotProduct, sq] using Cvs.Approximant.ConnesErrorColumn.tendsto_errorColumn_sq_zero hx)
    exact h.congr fun N => dotProduct_comm _ _
  have h := ((tendsto_pairingMass hx).sub herr).div
    ((tendsto_coefficientMass hx).const_mul (log (x:ℝ)))
    (mul_ne_zero (log_pos (Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx)).ne' (coefficientMass_pos hx hpos).ne')
  simp only [sub_zero] at h
  change Tendsto _ atTop (𝓝 (rayleighLimit x)) at h
  apply h.congr'
  filter_upwards [eventually_connesCoef_ne_zero hx hpos] with N hN
  exact (rayleigh_eq_tail_error hx N hN).symm

end Cvs.Approximant.ConnesResidualFixedScale
