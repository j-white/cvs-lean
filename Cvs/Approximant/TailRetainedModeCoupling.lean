import Mathlib
import Cvs.Approximant.ConnesFormTruncation
import Cvs.Approximant.ConnesTailWeightedEnergy
import Cvs.Approximant.CosineColumnTailPairing
import Cvs.Approximant.SpineCouplingTailPairing
import Cvs.Finite.EvenCosineVectorEmbedding
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationQuadraticForm
import Cvs.Finite.WindowMatrixSymbolKernel
import Cvs.L2a.RungTiltedPole
import Cvs.WeilForm.EvenBoundaryKernelBound
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.SymmetricBilinearForm
import Cvs.WeilForm.WeilFormOnWindowL2

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Tail and retained modes couple only through the bounded boundary kernel

Disjoint coefficient supports cancel the diagonal symbol exactly, leaving the
concrete boundary matrix and its balanced bound on the even coefficient space.
-/

noncomputable section

open Real Matrix Finset Filter

namespace Cvs.Approximant.TailRetainedModeCoupling
open Cvs.ZeroCounting

open Cvs.Finite.SymmetricModeSet (Idx mode negI coeff)

/-- The actual finite window matrix is its diagonal symbol plus the boundary matrix. -/
theorem matrix_eq_diagonal_add_boundary {L : ℝ} (hL : 0 < L) (P R N : ℕ) :
    Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) =
      Matrix.diagonal (fun i => Cvs.Finite.WindowMatrixSymbolKernel.symbolCut P R L (2 * π * (mode N i : ℝ) / L))
        + Cvs.WeilForm.EvenBoundaryKernelBound.boundaryMatrix P R L N := by
  ext i j
  rw [Cvs.Finite.WindowMatrixSymbolKernel.M_apply_kernel hL P R (Cvs.Finite.SymmetricModeSet.mode_injective N)]
  simp only [Matrix.add_apply, Matrix.diagonal_apply, Cvs.WeilForm.EvenBoundaryKernelBound.boundaryMatrix,
    one_div_mul_eq_div]

/-- Disjoint coordinates remove the diagonal part of the actual matrix pairing. -/
theorem matrix_pair_disjoint {L : ℝ} (hL : 0 < L) (P R N : ℕ)
    (f g : Idx N → ℝ) (hfg : ∀ i, f i * g i = 0) :
    f ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ g)
      = f ⬝ᵥ (Cvs.WeilForm.EvenBoundaryKernelBound.boundaryMatrix P R L N *ᵥ g) := by
  rw [matrix_eq_diagonal_add_boundary hL, Matrix.add_mulVec, dotProduct_add]
  have hd : f ⬝ᵥ (Matrix.diagonal
      (fun i => Cvs.Finite.WindowMatrixSymbolKernel.symbolCut P R L (2 * π * (mode N i : ℝ) / L)) *ᵥ g) = 0 := by
    unfold dotProduct
    simp only [Matrix.mulVec_diagonal]
    apply Finset.sum_eq_zero
    intro i _
    change f i * (Cvs.Finite.WindowMatrixSymbolKernel.symbolCut P R L (2 * π * (mode N i : ℝ) / L) * g i) = 0
    rw [show f i * (Cvs.Finite.WindowMatrixSymbolKernel.symbolCut P R L (2 * π * (mode N i : ℝ) / L) * g i)
      = Cvs.Finite.WindowMatrixSymbolKernel.symbolCut P R L (2 * π * (mode N i : ℝ) / L) * (f i * g i) by ring,
      hfg, mul_zero]
  rw [hd, zero_add]

/-- The actual continuous cosine pairing on disjoint supports is entirely a boundary pairing. -/
theorem QWbil_modeMap_disjoint {x : ℕ} (hx0 : (0 : ℝ) < x) (hx1 : (1 : ℝ) < x)
    (P R N : ℕ) (f g : Idx N → ℝ)
    (hf : ∀ i, f (negI N i) = f i) (hg : ∀ i, g (negI N i) = g i)
    (hfg : ∀ i, f i * g i = 0) :
    Cvs.WeilForm.SymmetricBilinearForm.QWbil (Real.log_natCast_nonneg x) P R
      (Cvs.Approximant.CosineColumnTailPairing.modeMap (x := x) hx0 N f) (Cvs.Approximant.CosineColumnTailPairing.modeMap (x := x) hx0 N g)
      = Real.log x * (f ⬝ᵥ (Cvs.WeilForm.EvenBoundaryKernelBound.boundaryMatrix P R (Real.log x) N *ᵥ g)) := by
  rw [Cvs.Approximant.CosineColumnTailPairing.QWbil_modeMap hx0 hx1 P R N f g hf hg,
    matrix_pair_disjoint (Real.log_pos hx1) P R N f g hfg]

/-- The actual disjoint continuous pairing has a bound independent of mode order. -/
theorem abs_QWbil_modeMap_disjoint_le {x : ℕ} (hx0 : (0 : ℝ) < x)
    (hx1 : (1 : ℝ) < x) (P R N : ℕ) (f g : Idx N → ℝ)
    (hf : ∀ i, f (negI N i) = f i) (hg : ∀ i, g (negI N i) = g i)
    (hfg : ∀ i, f i * g i = 0) {s : ℝ} (hs : 0 < s) :
    |Cvs.WeilForm.SymmetricBilinearForm.QWbil (Real.log_natCast_nonneg x) P R
      (Cvs.Approximant.CosineColumnTailPairing.modeMap (x := x) hx0 N f) (Cvs.Approximant.CosineColumnTailPairing.modeMap (x := x) hx0 N g)|
      ≤ Real.log x * Cvs.WeilForm.EvenBoundaryKernelBound.kernelBudget P R (Real.log x) / 2 *
        (s ^ 2 * (∑ i, f i ^ 2) + (∑ i, g i ^ 2) / s ^ 2) := by
  rw [QWbil_modeMap_disjoint hx0 hx1 P R N f g hf hg hfg,
    abs_mul, abs_of_pos (Real.log_pos hx1)]
  have h := mul_le_mul_of_nonneg_left
    (Cvs.WeilForm.EvenBoundaryKernelBound.boundary_bilinear_balanced_bound (Real.log_pos hx1) P R N f g hf hg hs)
    (Real.log_pos hx1).le
  exact h.trans_eq (by ring)

/-- Disjoint natural mode sets have disjoint actual signed cosine coefficient supports. -/
theorem coeff_disjoint (N : ℕ) (S T : Finset ℕ) (a b : ℕ → ℝ)
    (hST : Disjoint S T) (i : Idx N) : coeff N S a i * coeff N T b i = 0 := by
  rcases i with _ | ⟨k, u⟩ <;> simp only [coeff]
  · by_cases hS : 0 ∈ S
    · have hT : 0 ∉ T := fun h => Finset.disjoint_left.mp hST hS h
      simp [hS, hT]
    · simp [hS]
  · by_cases hS : k.val + 1 ∈ S
    · have hT : k.val + 1 ∉ T := fun h => Finset.disjoint_left.mp hST hS h
      simp [hS, hT]
    · simp [hS]

/-- Optimizing the existing balanced bound controls disjoint pairings by coefficient masses. -/
theorem abs_QWbil_modeMap_disjoint_sqrt_le {x : ℕ} (hx0 : (0 : ℝ) < x)
    (hx1 : (1 : ℝ) < x) (P R N : ℕ) (f g : Idx N → ℝ)
    (hf : ∀ i, f (negI N i) = f i) (hg : ∀ i, g (negI N i) = g i)
    (hfg : ∀ i, f i * g i = 0) :
    |Cvs.WeilForm.SymmetricBilinearForm.QWbil (Real.log_natCast_nonneg x) P R
      (Cvs.Approximant.CosineColumnTailPairing.modeMap (x := x) hx0 N f) (Cvs.Approximant.CosineColumnTailPairing.modeMap (x := x) hx0 N g)|
      ≤ 2 * Real.sqrt
        ((Real.log x * Cvs.WeilForm.EvenBoundaryKernelBound.kernelBudget P R (Real.log x) / 2 * (∑ i, f i ^ 2)) *
         (Real.log x * Cvs.WeilForm.EvenBoundaryKernelBound.kernelBudget P R (Real.log x) / 2 * (∑ i, g i ^ 2))) := by
  have hC : 0 ≤ Real.log x * Cvs.WeilForm.EvenBoundaryKernelBound.kernelBudget P R (Real.log x) / 2 := by
    have := Cvs.WeilForm.EvenBoundaryKernelBound.kernelBudget_nonneg (Real.log_pos hx1) P R
    positivity
  apply Cvs.L2a.RungTiltedPole.le_two_sqrt_mul (mul_nonneg hC (sum_nonneg fun _ _ => sq_nonneg _))
    (mul_nonneg hC (sum_nonneg fun _ _ => sq_nonneg _))
  intro t ht
  have h := abs_QWbil_modeMap_disjoint_le hx0 hx1 P R N f g hf hg hfg
    (Real.sqrt_pos.mpr ht)
  rw [Real.sq_sqrt ht.le] at h
  exact h.trans_eq (by ring)

/-- An explicit fixed-scale bound for the whole omitted-tail functional on unit coefficient tests. -/
def columnBudget (x N : ℕ) : ℝ :=
  2 * Real.sqrt
    ((Real.log x * Cvs.WeilForm.EvenBoundaryKernelBound.kernelBudget x (Nat.clog 2 x) (Real.log x) / 2) ^ 2 *
      Cvs.Approximant.ConnesTailWeightedEnergy.coefTail x N)

theorem columnBudget_nonneg (x N : ℕ) : 0 ≤ columnBudget x N := by
  unfold columnBudget
  positivity

/-- The uniform coefficient-test budget vanishes at each actual fixed scale. -/
theorem tendsto_columnBudget_zero {x : ℕ} (hx : 80 ≤ 2 * π * x) :
    Tendsto (columnBudget x) atTop (nhds 0) := by
  have h := ((Cvs.Approximant.ConnesTailWeightedEnergy.tendsto_coefTail_zero hx).const_mul
    ((Real.log x * Cvs.WeilForm.EvenBoundaryKernelBound.kernelBudget x (Nat.clog 2 x) (Real.log x) / 2) ^ 2)).sqrt.const_mul 2
  change Tendsto (fun N => 2 * Real.sqrt
    ((Real.log x * Cvs.WeilForm.EvenBoundaryKernelBound.kernelBudget x (Nat.clog 2 x) (Real.log x) / 2) ^ 2 *
      Cvs.Approximant.ConnesTailWeightedEnergy.coefTail x N)) atTop (nhds 0)
  simpa only [mul_zero, Real.sqrt_zero] using h

/-- Every finite omitted Connes tail obeys the same bound on all retained even unit tests. -/
theorem abs_QWbil_finite_tail_unit_le {x : ℕ} (hx : 80 ≤ 2 * π * x)
    {N J : ℕ} (hNJ : N ≤ J) (f : Idx N → ℝ)
    (hf : ∀ i, f (negI N i) = f i) (hunit : ∑ i, f i ^ 2 = 1) :
    |Cvs.WeilForm.SymmetricBilinearForm.QWbil (Real.log_natCast_nonneg x) x (Nat.clog 2 x)
      (Cvs.Approximant.ConnesFormTruncation.connesTrunc (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) J -
        Cvs.Approximant.ConnesFormTruncation.connesTrunc (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) N)
      (Cvs.Approximant.CosineColumnTailPairing.modeMap (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) N f)| ≤ columnBudget x N := by
  have h := abs_QWbil_modeMap_disjoint_sqrt_le (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx)
    (Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx) x (Nat.clog 2 x) J (Cvs.Approximant.ConnesTailWeightedEnergy.tailCoef x N J)
    (Cvs.Finite.EvenCosineVectorEmbedding.embed N J f) (Cvs.Approximant.ConnesTailWeightedEnergy.tailCoef_even x N J) (Cvs.Finite.EvenCosineVectorEmbedding.embed_even N J f)
    (fun i => by rw [mul_comm]; exact Cvs.Finite.EvenCosineVectorEmbedding.tailCoef_disjoint x N J f i)
  rw [Cvs.Approximant.ConnesTailWeightedEnergy.modeMap_tailCoef (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) hNJ,
    Cvs.Finite.EvenCosineVectorEmbedding.modeMap_embed (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) hNJ f hf,
    Cvs.Finite.EvenCosineVectorEmbedding.sum_embed_sq hNJ f hf, hunit, mul_one] at h
  refine h.trans ?_
  unfold columnBudget
  apply mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (by norm_num)
  have hm := (Cvs.Approximant.ConnesTailWeightedEnergy.tailCoef_norm_le x N J).trans (Cvs.Approximant.ConnesTailWeightedEnergy.tailSum_le_coefTail hx hNJ)
  calc
    (Real.log x * Cvs.WeilForm.EvenBoundaryKernelBound.kernelBudget x (Nat.clog 2 x) (Real.log x) / 2 *
      (∑ i, Cvs.Approximant.ConnesTailWeightedEnergy.tailCoef x N J i ^ 2)) *
        (Real.log x * Cvs.WeilForm.EvenBoundaryKernelBound.kernelBudget x (Nat.clog 2 x) (Real.log x) / 2)
        = (Real.log x * Cvs.WeilForm.EvenBoundaryKernelBound.kernelBudget x (Nat.clog 2 x) (Real.log x) / 2) ^ 2 *
            (∑ i, Cvs.Approximant.ConnesTailWeightedEnergy.tailCoef x N J i ^ 2) := by ring
    _ ≤ (Real.log x * Cvs.WeilForm.EvenBoundaryKernelBound.kernelBudget x (Nat.clog 2 x) (Real.log x) / 2) ^ 2 *
        Cvs.Approximant.ConnesTailWeightedEnergy.coefTail x N := mul_le_mul_of_nonneg_left hm (sq_nonneg _)

/-- The true omitted Connes class is uniformly controlled on the entire retained even unit sphere. -/
theorem abs_QWbil_connesError_unit_le {x : ℕ} (hx : 80 ≤ 2 * π * x) (N : ℕ)
    (f : Idx N → ℝ) (hf : ∀ i, f (negI N i) = f i) (hunit : ∑ i, f i ^ 2 = 1) :
    |Cvs.WeilForm.SymmetricBilinearForm.QWbil (Real.log_natCast_nonneg x) x (Nat.clog 2 x) (Cvs.Approximant.ConnesFormTruncation.connesError hx N)
      (Cvs.Approximant.CosineColumnTailPairing.modeMap (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) N f)| ≤ columnBudget x N := by
  apply le_of_tendsto (Cvs.Approximant.ConnesFormTruncation.tendsto_QWbil_finite_tail hx N f).abs
  filter_upwards [eventually_ge_atTop N] with J hJ
  exact abs_QWbil_finite_tail_unit_le hx hJ f hf hunit

end Cvs.Approximant.TailRetainedModeCoupling
