import Mathlib
import Cvs.Approximant.BoundaryVarianceInterval
import Cvs.Finite.DiagonalCutSymbol
import Cvs.Finite.DiagonalLevySymbol
import Cvs.Finite.ModeSumFormDomain
import Cvs.Finite.ModeSumPairValues
import Cvs.Finite.OneModeEntries
import Cvs.Finite.PairFormDividedDifference
import Cvs.Finite.PairPoleChannelClosed
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationQuadraticForm
import Cvs.Finite.TruncationZeroFreeOffAxes
import Cvs.Finite.WindowMatrixSymbolKernel
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.ArithmeticFloorAboveBand
import Cvs.WeilForm.EvenBoundaryKernelBound
import Cvs.WeilForm.PrimeSideBoundedBelow
import Cvs.Zeta.PrimePowerSideTruncated
import Cvs.Zeta.WeilPositivityStatement

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Exact prime-diagonal cancellation and actual bulk Schur costs

The prime cosine diagonal cancels before the tail floor is bounded.
The actual even matrix has a shifted arch diagonal and a positive remainder.
Low/high projections give explicit leakage and damped Schur comparisons.
Their low-head arithmetic hypotheses and low-supported normal remain explicit.
-/

noncomputable section
set_option maxHeartbeats 1000000
open Real Matrix Finset MeasureTheory Set Cvs.Zeta.Explicit.Weil
namespace Cvs.WeilForm.PrimeDiagonalBulkSchur
open Cvs.ZeroCounting

open Cvs.Finite.SymmetricModeSet (Idx mode negI)

/-- The actual positive arch boundary, including its finite pole atom. -/
def archMatrix (L : ℝ) (N : ℕ) : Matrix (Idx N) (Idx N) ℝ :=
  fun i j => Cvs.Finite.WindowMatrixSymbolKernel.kArch L (2*π*(mode N i : ℝ)/L) (2*π*(mode N j : ℝ)/L)/L

/-- The actual full prime translation form, with no cosine diagonal charged twice. -/
def translationPrimeMatrix (P R : ℕ) (L : ℝ) (N : ℕ) : Matrix (Idx N) (Idx N) ℝ :=
  fun i j => Cvs.Finite.ModeSumPairValues.primePair P R L (mode N i) (mode N j)/2

def primeCost (P R : ℕ) : ℝ := 2*Cvs.WeilForm.PrimeSideBoundedBelow.primeWeightTotal P R

def improvedFloor (P R : ℕ) (T : ℝ) : ℝ := Cvs.WeilForm.ArithmeticFloorAboveBand.archLower T-primeCost P R

/-- The actual arch plus prime translation defect is positive on even coefficients. -/
def positiveRemainder (P R : ℕ) (L : ℝ) (N : ℕ) : Matrix (Idx N) (Idx N) ℝ :=
  archMatrix L N+Matrix.diagonal (fun _ => primeCost P R)-translationPrimeMatrix P R L N

def remainderBudget (P R : ℕ) (L : ℝ) : ℝ := Cvs.WeilForm.EvenBoundaryKernelBound.archBudget L+2*primeCost P R

private theorem quad_eq_sum {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (v : ι → ℝ) :
    v ⬝ᵥ (A *ᵥ v)=∑ i, ∑ j, v i*v j*A i j := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem archMatrix_symm (L : ℝ) (N : ℕ) (i j : Idx N) :
    archMatrix L N i j=archMatrix L N j i := by
  unfold archMatrix
  apply congrArg (fun z => z/L)
  unfold Cvs.Finite.WindowMatrixSymbolKernel.kArch
  congr 1
  · ring
  · apply tsum_congr
    intro k
    ring

theorem matrix_eq_arch_sub_prime {L : ℝ} (hL : 0<L) (P R N : ℕ) :
    Cvs.Finite.TruncationQuadraticForm.M P R L (mode N)=
      Matrix.diagonal (fun i => Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol (2*π*(mode N i : ℝ)/L))+
        archMatrix L N-translationPrimeMatrix P R L N := by
  ext i j
  rw [Cvs.Finite.WindowMatrixSymbolKernel.M_apply_kernel hL P R (Cvs.Finite.SymmetricModeSet.mode_injective N)]
  simp only [one_div_mul_eq_div, Cvs.Finite.WindowMatrixSymbolKernel.kK, add_div, Cvs.WeilForm.EvenBoundaryKernelBound.kPrime_eq hL,
    (Cvs.Finite.SymmetricModeSet.mode_injective N).eq_iff, Matrix.sub_apply, Matrix.add_apply,
    Matrix.diagonal_apply, archMatrix, translationPrimeMatrix, Cvs.Finite.WindowMatrixSymbolKernel.symbolCut]
  by_cases h : i=j <;> simp only [h, if_true, if_false] <;> ring

theorem translationPrimeMatrix_symm {L : ℝ} (hL : 0<L) (P R N : ℕ) (i j : Idx N) :
    translationPrimeMatrix P R L N i j=translationPrimeMatrix P R L N j i := by
  have h := Cvs.Finite.TruncationQuadraticForm.M_symm hL P R (Cvs.Finite.SymmetricModeSet.mode_injective N) i j
  rw [matrix_eq_arch_sub_prime hL] at h
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.diagonal_apply] at h
  rw [archMatrix_symm L N i j] at h
  by_cases hij : i=j
  · subst j; rfl
  · simp only [hij, Ne.symm hij, if_false, zero_add] at h
    linarith

theorem arch_quad_interval {L : ℝ} (hL : 0<L) (N : ℕ) (v : Idx N → ℝ)
    (hv : ∀ i, v (negI N i)=v i) :
    0≤v ⬝ᵥ (archMatrix L N *ᵥ v) ∧
      v ⬝ᵥ (archMatrix L N *ᵥ v)≤Cvs.WeilForm.EvenBoundaryKernelBound.archBudget L*(v ⬝ᵥ v) := by
  rw [quad_eq_sum]
  have hn : 0≤∑ i,∑ j,v i*v j*archMatrix L N i j :=
    Cvs.Approximant.BoundaryVarianceInterval.arch_boundary_nonneg hL N v hv
  refine ⟨hn, ?_⟩
  have ha := Cvs.WeilForm.EvenBoundaryKernelBound.idx_arch_kernel_bound hL N v hv
  change |∑ i,∑ j,v i*v j*archMatrix L N i j|≤_ at ha
  rw [abs_of_nonneg hn] at ha
  simpa only [dotProduct, sq] using ha

/-- The full normalized prime translation quadratic has budget `2W`, independently of order. -/
theorem abs_translationPrime_quad_le {L : ℝ} (hL : 0<L) (P R N : ℕ) (v : Idx N → ℝ)
    (hv : ∀ i, v (negI N i)=v i) :
    |v ⬝ᵥ (translationPrimeMatrix P R L N *ᵥ v)|≤primeCost P R*(v ⬝ᵥ v) := by
  let f : ℝ → ℝ := Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L (mode N) v
  have hmem : MemLp f 2 (volume : Measure ℝ) :=
    Cvs.Finite.ModeSumFormDomain.memLp_two_of_bounded (Cvs.Finite.ModeSumPairValues.measurable_modeSum L (mode N) v)
      (Cvs.Finite.ModeSumPairValues.abs_modeSum_le L (mode N) v)
      (fun s hs => Cvs.Finite.ModeSumPairValues.modeSum_eq_zero_of_notMem L (mode N) v hs)
  have hprime := Cvs.WeilForm.PrimeSideBoundedBelow.abs_primePowerSideTruncated_le P R hmem.integrable_sq
    (fun t => hmem.integrable_mul
      (hmem.comp_measurePreserving (measurePreserving_add_right (volume : Measure ℝ) t)))
  have hn : selfConvolution f 0=L*∑ i,v i^2 := by
    rw [Cvs.Finite.PairFormDividedDifference.selfConvolution_modeSum_zero hL (Cvs.Finite.SymmetricModeSet.mode_injective N)
      (Cvs.Finite.SymmetricModeSet.negI_involutive N) (Cvs.Finite.SymmetricModeSet.mode_negI N) hv]
    simp only [dotProduct, pow_two]
  rw [hn] at hprime
  have hshift : |primePowerSideTruncated P R (selfConvolution f)/L|≤
      2*Cvs.WeilForm.PrimeSideBoundedBelow.primeWeightTotal P R*∑ i,v i^2 := by
    rw [abs_div, abs_of_pos hL]
    have h := div_le_div_of_nonneg_right hprime hL.le
    exact h.trans_eq (by field_simp)
  have hpair : (∑ i,∑ j,v i*v j*(Cvs.Finite.ModeSumPairValues.primePair P R L (mode N i) (mode N j)/2))=
      primePowerSideTruncated P R (selfConvolution f)/L := by
    rw [Cvs.Finite.ModeSumPairValues.prime_modeSum hL P R (mode N)
      (Cvs.Finite.SymmetricModeSet.negI_involutive N) (Cvs.Finite.SymmetricModeSet.mode_negI N) hv]
    simp_rw [← mul_div_assoc, ← Finset.sum_div]
    field_simp
  rw [quad_eq_sum]
  change |∑ i,∑ j,v i*v j*(Cvs.Finite.ModeSumPairValues.primePair P R L (mode N i) (mode N j)/2)|≤_
  rw [hpair]
  simpa only [primeCost, dotProduct, sq] using hshift

theorem matrix_eq_shifted_positive {L : ℝ} (hL : 0<L) (P R N : ℕ) :
    Cvs.Finite.TruncationQuadraticForm.M P R L (mode N)=
      Matrix.diagonal (fun i => Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol (2*π*(mode N i : ℝ)/L)-primeCost P R)+
        positiveRemainder P R L N := by
  rw [matrix_eq_arch_sub_prime hL]
  ext i j
  simp only [positiveRemainder, Matrix.sub_apply, Matrix.add_apply, Matrix.diagonal_apply]
  split_ifs <;> ring

theorem positiveRemainder_quad_interval {L : ℝ} (hL : 0<L) (P R N : ℕ)
    (v : Idx N → ℝ) (hv : ∀ i,v (negI N i)=v i) :
    0≤v ⬝ᵥ (positiveRemainder P R L N *ᵥ v) ∧
      v ⬝ᵥ (positiveRemainder P R L N *ᵥ v)≤remainderBudget P R L*(v ⬝ᵥ v) := by
  have ha := arch_quad_interval hL N v hv
  have hp := abs_le.mp (abs_translationPrime_quad_le hL P R N v hv)
  have hd : v ⬝ᵥ (Matrix.diagonal (fun _ : Idx N => primeCost P R) *ᵥ v)=
      primeCost P R*(v ⬝ᵥ v) := by
    simp only [dotProduct, Matrix.mulVec_diagonal, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  unfold positiveRemainder remainderBudget
  rw [Matrix.sub_mulVec, Matrix.add_mulVec, dotProduct_sub, dotProduct_add, hd]
  constructor <;> nlinarith

open Cvs.Finite.SymmetricModeSet (Idx mode negI)

/-- Retain precisely the actual signed modes with absolute order below `K`. -/
def lowPart (K N : ℕ) (v : Idx N → ℝ) : Idx N → ℝ :=
  fun i => if (mode N i).natAbs<K then v i else 0

/-- The complementary actual signed-mode projection. -/
def highPart (K N : ℕ) (v : Idx N → ℝ) : Idx N → ℝ :=
  fun i => if (mode N i).natAbs<K then 0 else v i

theorem low_high_disjoint (K N : ℕ) (u w : Idx N → ℝ) (i : Idx N) :
    lowPart K N u i*highPart K N w i=0 := by
  simp only [lowPart, highPart]
  split_ifs <;> ring

theorem low_dot_high (K N : ℕ) (u w : Idx N → ℝ) :
    lowPart K N u ⬝ᵥ highPart K N w=0 := by
  exact Finset.sum_eq_zero fun i _ => low_high_disjoint K N u w i

end Cvs.WeilForm.PrimeDiagonalBulkSchur
