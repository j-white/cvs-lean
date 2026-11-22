import Mathlib
import Cvs.Approximant.ConnesErrorColumn
import Cvs.Approximant.ConnesFormTruncation
import Cvs.Approximant.ConnesTailWeightedEnergy
import Cvs.Approximant.ConnesVectorRealScale
import Cvs.Approximant.CosineColumnTailPairing
import Cvs.Approximant.SpineCouplingTailPairing
import Cvs.Approximant.TailRetainedModeCoupling
import Cvs.Finite.DiagonalCutSymbol
import Cvs.Finite.EvenCosineVectorEmbedding
import Cvs.Finite.OneModeEntries
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationQuadraticForm
import Cvs.Finite.WindowCosineBessel
import Cvs.Finite.WindowMatrixSymbolKernel
import Cvs.L2a.RungTiltedPole
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.EvenBoundaryKernelBound
import Cvs.WeilForm.EvenOddSplitForm
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.PhysicalCubicCorrectionColumn
import Cvs.WeilForm.SymmetricBilinearForm
import Cvs.WeilForm.ThetaSpaceParseval
import Cvs.WeilForm.WeilFormOnWindowL2

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# A uniform actual full-column budget

Logarithmic symbol growth, actual weighted coefficient summability, and the
bounded boundary kernel give one fixed-scale budget for every finite even unit
test.  The actual form truncation passage transfers this budget to the tail.
-/

noncomputable section

open Real Set MeasureTheory Matrix Finset Filter

namespace Cvs.Approximant.ConnesFullColumnBudget
open Cvs.ZeroCounting

open Cvs.Finite.SymmetricModeSet (Idx mode negI)

/-- The lattice symbol's fixed-scale logarithmic multiplier. -/
def symbolConstant (P R : ℕ) (L : ℝ) : ℝ :=
  Cvs.Approximant.ConnesTailWeightedEnergy.archLatticeConstant L + Cvs.WeilForm.EvenBoundaryKernelBound.primeDiagonalBudget P R

theorem symbolConstant_nonneg {L : ℝ} (hL : 0 < L) (P R : ℕ) :
    0 ≤ symbolConstant P R L :=
  add_nonneg (Cvs.Approximant.ConnesTailWeightedEnergy.archLatticeConstant_nonneg hL) (Cvs.WeilForm.EvenBoundaryKernelBound.primeDiagonalBudget_nonneg P R)

/-- The actual lattice symbol grows only linearly in `1 + log n`. -/
theorem abs_symbolCut_lattice {L : ℝ} (hL : 0 < L) (P R : ℕ)
    {n : ℕ} (hn : 1 ≤ n) :
    |Cvs.Finite.WindowMatrixSymbolKernel.symbolCut P R L (2 * π * n / L)|
      ≤ symbolConstant P R L * (1 + log (n : ℝ)) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := zero_lt_one.trans_le hn'
  have hlogn := log_nonneg hn'
  let A : ℝ := 2 + 2 * π / L
  have hA : 1 ≤ A := by
    dsimp [A]
    have : 0 < 2 * π / L := by positivity
    linarith
  have hA0 : 0 < A := zero_lt_one.trans_le hA
  have hlogA := log_nonneg hA
  have harg : 2 + 2 * π * n / L ≤ A * n := by
    dsimp [A]
    rw [show 2 * π * (n : ℝ) / L = (2 * π / L) * n by ring]
    nlinarith
  have hl : log (2 + 2 * π * n / L) ≤ log A + log (n : ℝ) := by
    calc _ ≤ log (A * n) := log_le_log (by positivity) harg
      _ = _ := log_mul hA0.ne' hn0.ne'
  have ha := Cvs.Approximant.ConnesTailWeightedEnergy.abs_archSymbol_bound (2 * π * n / L)
  rw [abs_of_pos (by positivity : 0 < 2 * π * n / L)] at ha
  have ha' : |Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol (2 * π * n / L)|
      ≤ Cvs.Approximant.ConnesTailWeightedEnergy.archLatticeConstant L * (1 + log (n : ℝ)) := by
    unfold Cvs.Approximant.ConnesTailWeightedEnergy.archLatticeConstant
    have hw : 1 + log (2 + 2 * π * n / L)
        ≤ (1 + log A) * (1 + log (n : ℝ)) := by
      nlinarith [mul_nonneg hlogA hlogn]
    exact ha.trans (by simpa only [A, mul_assoc] using
      mul_le_mul_of_nonneg_left hw Cvs.Approximant.ConnesTailWeightedEnergy.archBase_nonneg)
  have hp := Cvs.WeilForm.EvenBoundaryKernelBound.abs_prime_cos_le P R L (2 * π * n / L)
  have hp0 := Cvs.WeilForm.EvenBoundaryKernelBound.primeDiagonalBudget_nonneg P R
  unfold Cvs.Finite.WindowMatrixSymbolKernel.symbolCut
  calc _ ≤ |Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol (2 * π * n / L)|
        + |Cvs.Finite.OneModeEntries.primeSum P R (Cvs.Finite.DiagonalCutSymbol.cosCut L (2 * π * n / L))| := abs_sub _ _
    _ ≤ Cvs.Approximant.ConnesTailWeightedEnergy.archLatticeConstant L * (1 + log (n : ℝ))
        + Cvs.WeilForm.EvenBoundaryKernelBound.primeDiagonalBudget P R := add_le_add ha' hp
    _ ≤ _ := by unfold symbolConstant; nlinarith [mul_nonneg hp0 hlogn]

/-- The actual finite diagonal action on the Connes coefficients. -/
def diagonalColumn (x N : ℕ) (i : Idx N) : ℝ :=
  Cvs.Finite.WindowMatrixSymbolKernel.symbolCut x (Nat.clog 2 x) (log x) (2 * π * (mode N i : ℝ) / log x)
    * Cvs.Approximant.ConnesVectorRealScale.connesCoef x N i

/-- The actual nonnegative logarithm-weighted square series. -/
def weightedSeries (x : ℕ) : ℝ := ∑' k : ℕ, Cvs.Approximant.ConnesTailWeightedEnergy.coefTerm x k

theorem weightedSeries_nonneg (x : ℕ) : 0 ≤ weightedSeries x :=
  tsum_nonneg (Cvs.Approximant.ConnesTailWeightedEnergy.coefTerm_nonneg x)

/-- A uniform coefficient mass budget, retaining the actual zero coefficient. -/
def coefficientBudget (x : ℕ) : ℝ := Cvs.Approximant.ConnesTailWeightedEnergy.coef x 0 ^ 2 + weightedSeries x

/-- A uniform squared diagonal-action budget with its actual zero symbol. -/
def diagonalBudget (x : ℕ) : ℝ :=
  (Cvs.Finite.WindowMatrixSymbolKernel.symbolCut x (Nat.clog 2 x) (log x) 0 * Cvs.Approximant.ConnesTailWeightedEnergy.coef x 0) ^ 2
    + symbolConstant x (Nat.clog 2 x) (log x) ^ 2 * weightedSeries x

theorem coefficientBudget_nonneg (x : ℕ) : 0 ≤ coefficientBudget x := by
  unfold coefficientBudget
  exact add_nonneg (sq_nonneg _) (weightedSeries_nonneg x)

theorem diagonalBudget_nonneg (x : ℕ) : 0 ≤ diagonalBudget x := by
  unfold diagonalBudget
  exact add_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) (weightedSeries_nonneg x))

private theorem sum_coefTerm_fin_le {x : ℕ} (hx : 80 ≤ 2 * π * x) (N : ℕ) :
    (∑ k : Fin N, Cvs.Approximant.ConnesTailWeightedEnergy.coefTerm x k.val) ≤ weightedSeries x := by
  rw [Fin.sum_univ_eq_sum_range]
  exact (Cvs.Approximant.ConnesTailWeightedEnergy.summable_coefTerm hx).sum_le_tsum (range N)
    (fun k _ => Cvs.Approximant.ConnesTailWeightedEnergy.coefTerm_nonneg x k)

private theorem connesCoef_none (x N : ℕ) : Cvs.Approximant.ConnesVectorRealScale.connesCoef x N none = Cvs.Approximant.ConnesTailWeightedEnergy.coef x 0 := by
  simp [Cvs.Approximant.ConnesVectorRealScale.connesCoef, Cvs.Finite.SymmetricModeSet.coeff, Cvs.Approximant.ConnesTailWeightedEnergy.coef]

private theorem connesCoef_some (x N : ℕ) (k : Fin N) (b : Bool) :
    Cvs.Approximant.ConnesVectorRealScale.connesCoef x N (some (k, b)) = Cvs.Approximant.ConnesTailWeightedEnergy.coef x (k.val + 1) / 2 := by
  simp [Cvs.Approximant.ConnesVectorRealScale.connesCoef, Cvs.Finite.SymmetricModeSet.coeff, Cvs.Approximant.ConnesTailWeightedEnergy.coef, show k.val + 1 < N + 1 by omega]

/-- Every actual Connes coefficient vector obeys the same fixed-scale mass budget. -/
theorem connesCoef_sq_le {x : ℕ} (hx : 80 ≤ 2 * π * x) (N : ℕ) :
    ∑ i, Cvs.Approximant.ConnesVectorRealScale.connesCoef x N i ^ 2 ≤ coefficientBudget x := by
  rw [Cvs.WeilForm.EvenBoundaryKernelBound.idx_even_sq N _ (Cvs.Approximant.ConnesVectorRealScale.connesCoef_even x N), connesCoef_none]
  have hs : 2 * (∑ k : Fin N, Cvs.Approximant.ConnesVectorRealScale.connesCoef x N (some (k, true)) ^ 2)
      ≤ ∑ k : Fin N, Cvs.Approximant.ConnesTailWeightedEnergy.coefTerm x k.val := by
    rw [Finset.mul_sum]
    apply sum_le_sum
    intro k _
    rw [connesCoef_some]
    have hw := Cvs.Approximant.ConnesTailWeightedEnergy.logWeight_one_le (show 1 ≤ k.val + 1 by omega)
    unfold Cvs.Approximant.ConnesTailWeightedEnergy.coefTerm
    nlinarith [sq_nonneg (Cvs.Approximant.ConnesTailWeightedEnergy.coef x (k.val + 1))]
  simpa only [coefficientBudget, add_comm] using
    add_le_add_left (hs.trans (sum_coefTerm_fin_le hx N)) (Cvs.Approximant.ConnesTailWeightedEnergy.coef x 0 ^ 2)

theorem diagonalColumn_even (x N : ℕ) (i : Idx N) :
    diagonalColumn x N (negI N i) = diagonalColumn x N i := by
  simp only [diagonalColumn, Cvs.Finite.SymmetricModeSet.mode_negI, Int.cast_neg, mul_neg, neg_div,
    Cvs.Approximant.ConnesTailWeightedEnergy.symbolCut_neg, Cvs.Approximant.ConnesVectorRealScale.connesCoef_even]

/-- The complete actual diagonal column has a squared mass bound independent of mode order. -/
theorem diagonalColumn_sq_le {x : ℕ} (hx : 80 ≤ 2 * π * x) (N : ℕ) :
    ∑ i, diagonalColumn x N i ^ 2 ≤ diagonalBudget x := by
  rw [Cvs.WeilForm.EvenBoundaryKernelBound.idx_even_sq N _ (diagonalColumn_even x N)]
  have hz : diagonalColumn x N none =
      Cvs.Finite.WindowMatrixSymbolKernel.symbolCut x (Nat.clog 2 x) (log x) 0 * Cvs.Approximant.ConnesTailWeightedEnergy.coef x 0 := by
    simp [diagonalColumn, Cvs.Finite.SymmetricModeSet.mode, connesCoef_none]
  rw [hz]
  have hs : 2 * (∑ k : Fin N, diagonalColumn x N (some (k, true)) ^ 2)
      ≤ symbolConstant x (Nat.clog 2 x) (log x) ^ 2 * weightedSeries x := by
    rw [Finset.mul_sum]
    have ht : (∑ k : Fin N, 2 * diagonalColumn x N (some (k, true)) ^ 2)
        ≤ symbolConstant x (Nat.clog 2 x) (log x) ^ 2 *
          ∑ k : Fin N, Cvs.Approximant.ConnesTailWeightedEnergy.coefTerm x k.val := by
      rw [Finset.mul_sum]
      apply sum_le_sum
      intro k _
      have hp := abs_symbolCut_lattice (log_pos (Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx))
        x (Nat.clog 2 x) (show 1 ≤ k.val + 1 by omega)
      have hc := symbolConstant_nonneg (log_pos (Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx)) x (Nat.clog 2 x)
      have hl := log_nonneg (show (1 : ℝ) ≤ k.val + 1 by exact_mod_cast (show 1 ≤ k.val + 1 by omega))
      have hp2 := pow_le_pow_left₀ (abs_nonneg _) hp 2
      rw [sq_abs, mul_pow] at hp2
      have hd : diagonalColumn x N (some (k, true)) =
          Cvs.Finite.WindowMatrixSymbolKernel.symbolCut x (Nat.clog 2 x) (log x) (2 * π * (k.val + 1) / log x)
            * (Cvs.Approximant.ConnesTailWeightedEnergy.coef x (k.val + 1) / 2) := by
        simp [diagonalColumn, Cvs.Finite.SymmetricModeSet.mode, connesCoef_some]
      rw [hd]
      unfold Cvs.Approximant.ConnesTailWeightedEnergy.coefTerm Cvs.Approximant.ConnesTailWeightedEnergy.logWeight
      have hm := mul_le_mul_of_nonneg_right hp2 (sq_nonneg (Cvs.Approximant.ConnesTailWeightedEnergy.coef x (k.val + 1)))
      push_cast at hm
      push_cast
      calc
        _ ≤ Cvs.Finite.WindowMatrixSymbolKernel.symbolCut x (Nat.clog 2 x) (log x)
            (2 * π * (k.val + 1) / log x) ^ 2 * Cvs.Approximant.ConnesTailWeightedEnergy.coef x (k.val + 1) ^ 2 := by
          nlinarith [sq_nonneg (Cvs.Finite.WindowMatrixSymbolKernel.symbolCut x (Nat.clog 2 x) (log x)
            (2 * π * (k.val + 1) / log x) * Cvs.Approximant.ConnesTailWeightedEnergy.coef x (k.val + 1))]
        _ ≤ _ := by simpa only [mul_assoc] using hm
    exact ht.trans (mul_le_mul_of_nonneg_left (sum_coefTerm_fin_le hx N) (sq_nonneg _))
  simpa only [diagonalBudget, add_comm] using
    add_le_add_left hs ((Cvs.Finite.WindowMatrixSymbolKernel.symbolCut x (Nat.clog 2 x) (log x) 0 * Cvs.Approximant.ConnesTailWeightedEnergy.coef x 0) ^ 2)

private theorem abs_dot_unit_le {ι : Type*} [Fintype ι] (u f : ι → ℝ)
    (hf : ∑ i, f i ^ 2 = 1) : |u ⬝ᵥ f| ≤ √(∑ i, u i ^ 2) := by
  have h := Real.sum_mul_le_sqrt_mul_sqrt univ (fun i => |u i|) (fun i => |f i|)
  simp only [sq_abs, hf, sqrt_one, mul_one] at h
  exact (Finset.abs_sum_le_sum_abs _ _).trans (by simpa only [abs_mul] using h)

/-- The fixed-scale boundary-action budget on every actual unit coefficient test. -/
def boundaryBudget (x : ℕ) : ℝ :=
  2 * √((Cvs.WeilForm.EvenBoundaryKernelBound.kernelBudget x (Nat.clog 2 x) (log x) / 2 * coefficientBudget x) *
    (Cvs.WeilForm.EvenBoundaryKernelBound.kernelBudget x (Nat.clog 2 x) (log x) / 2))

/-- The complete fixed-scale actual full-column budget. -/
def fullColumnBudget (x : ℕ) : ℝ := log x * (√(diagonalBudget x) + boundaryBudget x)

theorem fullColumnBudget_nonneg (x : ℕ) : 0 ≤ fullColumnBudget x := by
  unfold fullColumnBudget boundaryBudget
  positivity

private theorem abs_boundary_connes_unit_le {x : ℕ} (hx : 80 ≤ 2 * π * x)
    (N : ℕ) (f : Idx N → ℝ) (hf : ∀ i, f (negI N i) = f i)
    (hunit : ∑ i, f i ^ 2 = 1) :
    |Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ⬝ᵥ (Cvs.WeilForm.EvenBoundaryKernelBound.boundaryMatrix x (Nat.clog 2 x) (log x) N *ᵥ f)|
      ≤ boundaryBudget x := by
  have hK := Cvs.WeilForm.EvenBoundaryKernelBound.kernelBudget_nonneg (log_pos (Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx)) x (Nat.clog 2 x)
  apply Cvs.L2a.RungTiltedPole.le_two_sqrt_mul
    (mul_nonneg (div_nonneg hK (by norm_num)) (coefficientBudget_nonneg x))
    (div_nonneg hK (by norm_num))
  intro t ht
  have h := Cvs.WeilForm.EvenBoundaryKernelBound.boundary_bilinear_balanced_bound (log_pos (Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx))
    x (Nat.clog 2 x) N (Cvs.Approximant.ConnesVectorRealScale.connesCoef x N) f
    (Cvs.Approximant.ConnesVectorRealScale.connesCoef_even x N) hf (sqrt_pos.mpr ht)
  rw [sq_sqrt ht.le, hunit] at h
  have hm := mul_le_mul_of_nonneg_left (connesCoef_sq_le hx N) ht.le
  have hK2 : 0 ≤ Cvs.WeilForm.EvenBoundaryKernelBound.kernelBudget x (Nat.clog 2 x) (log x) / 2 :=
    div_nonneg hK (by norm_num)
  apply h.trans
  calc
    _ ≤ Cvs.WeilForm.EvenBoundaryKernelBound.kernelBudget x (Nat.clog 2 x) (log x) / 2 *
        (t * coefficientBudget x + 1 / t) :=
      mul_le_mul_of_nonneg_left (add_le_add hm (le_refl (1 / t))) hK2
    _ = _ := by ring

/-- Every finite actual Connes matrix pairing has the same fixed-scale unit-test budget. -/
theorem abs_QWbil_connesTrunc_unit_le {x : ℕ} (hx : 80 ≤ 2 * π * x)
    (N : ℕ) (f : Idx N → ℝ) (hf : ∀ i, f (negI N i) = f i)
    (hunit : ∑ i, f i ^ 2 = 1) :
    |Cvs.WeilForm.SymmetricBilinearForm.QWbil (log_natCast_nonneg x) x (Nat.clog 2 x)
      (Cvs.Approximant.ConnesFormTruncation.connesTrunc (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) N)
      (Cvs.Approximant.CosineColumnTailPairing.modeMap (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) N f)| ≤ fullColumnBudget x := by
  rw [Cvs.Approximant.ConnesFormTruncation.connesTrunc, Cvs.Approximant.CosineColumnTailPairing.QWbil_modeMap (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx)
    (Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx) x (Nat.clog 2 x) N _ f (Cvs.Approximant.ConnesVectorRealScale.connesCoef_even x N) hf,
    Cvs.Approximant.TailRetainedModeCoupling.matrix_eq_diagonal_add_boundary (log_pos (Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx)),
    Matrix.add_mulVec, dotProduct_add, abs_mul, abs_of_pos (log_pos (Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx))]
  have hd : Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ⬝ᵥ
      (Matrix.diagonal (fun i => Cvs.Finite.WindowMatrixSymbolKernel.symbolCut x (Nat.clog 2 x) (log x)
        (2 * π * (mode N i : ℝ) / log x)) *ᵥ f) = diagonalColumn x N ⬝ᵥ f := by
    simp only [Matrix.mulVec_diagonal, dotProduct, diagonalColumn]
    apply sum_congr rfl
    intro i _
    ring
  rw [hd]
  have hd' := (abs_dot_unit_le (diagonalColumn x N) f hunit).trans
    (sqrt_le_sqrt (diagonalColumn_sq_le hx N))
  exact mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans
    (add_le_add hd' (abs_boundary_connes_unit_le hx N f hf hunit)))
    (log_natCast_nonneg x)

/-- The actual untruncated pairing has a uniform budget on every even unit cosine test. -/
theorem abs_QWbil_connesClass_unit_le {x : ℕ} (hx : 80 ≤ 2 * π * x)
    (N : ℕ) (f : Idx N → ℝ) (hf : ∀ i, f (negI N i) = f i)
    (hunit : ∑ i, f i ^ 2 = 1) :
    |Cvs.WeilForm.SymmetricBilinearForm.QWbil (log_natCast_nonneg x) x (Nat.clog 2 x) (Cvs.Approximant.CosineColumnTailPairing.connesClass hx)
      (Cvs.Approximant.CosineColumnTailPairing.modeMap (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) N f)| ≤ fullColumnBudget x := by
  let B := Cvs.WeilForm.SymmetricBilinearForm.QWbil (log_natCast_nonneg x) x (Nat.clog 2 x)
  let E := Cvs.WeilForm.EvenOddSplitForm.evenPart (log_natCast_nonneg x) (Cvs.Approximant.CosineColumnTailPairing.connesClass hx)
  let v := Cvs.Approximant.CosineColumnTailPairing.modeMap (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) N f
  have ht : Tendsto (fun J => B (Cvs.Approximant.ConnesFormTruncation.connesTrunc (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) J) v)
      atTop (nhds (B E v)) := by
    have h := (tendsto_const_nhds (x := B E v) (f := atTop (α := ℕ))).sub
      (Cvs.Approximant.ConnesFormTruncation.tendsto_QWbil_connesError_zero hx v)
    simp only [sub_zero] at h
    refine h.congr fun J => ?_
    have hs : ∀ a b c : Cvs.WeilForm.FormDomain.formDomain (log_natCast_nonneg x),
        Cvs.WeilForm.SymmetricBilinearForm.QWbil (log_natCast_nonneg x) x (Nat.clog 2 x) (a - b) c =
          Cvs.WeilForm.SymmetricBilinearForm.QWbil (log_natCast_nonneg x) x (Nat.clog 2 x) a c -
          Cvs.WeilForm.SymmetricBilinearForm.QWbil (log_natCast_nonneg x) x (Nat.clog 2 x) b c :=
      fun a b c => LinearMap.map_sub₂ _ a b c
    simp only [Cvs.Approximant.ConnesFormTruncation.connesError]
    dsimp [B, E]
    rw [hs]
    ring
  rw [Cvs.Approximant.CosineColumnTailPairing.QWbil_modeMap_eq_evenPart]
  apply le_of_tendsto ht.abs
  filter_upwards [eventually_ge_atTop N] with J hJ
  have hb := abs_QWbil_connesTrunc_unit_le hx J (Cvs.Finite.EvenCosineVectorEmbedding.embed N J f)
    (Cvs.Finite.EvenCosineVectorEmbedding.embed_even N J f)
    (by rw [Cvs.Finite.EvenCosineVectorEmbedding.sum_embed_sq hJ f hf]; exact hunit)
  rw [Cvs.Finite.EvenCosineVectorEmbedding.modeMap_embed (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) hJ f hf] at hb
  exact hb

/-- The actual tail pairing is represented by its whole even coefficient column. -/
theorem QWbil_connesClass_eq_tailColumn_dot {x : ℕ} (hx : 80 ≤ 2 * π * x)
    (N : ℕ) (f : Idx N → ℝ) (hf : ∀ i, f (negI N i) = f i) :
    Cvs.WeilForm.SymmetricBilinearForm.QWbil (log_natCast_nonneg x) x (Nat.clog 2 x) (Cvs.Approximant.CosineColumnTailPairing.connesClass hx)
      (Cvs.Approximant.CosineColumnTailPairing.modeMap (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) N f) = Cvs.Approximant.ConnesErrorColumn.tailColumn x N ⬝ᵥ f := by
  conv_lhs => rw [← Cvs.Approximant.ConnesErrorColumn.sum_smul_cosineRow N f hf]
  simp only [map_sum, map_smul, smul_eq_mul]
  unfold dotProduct Cvs.Approximant.ConnesErrorColumn.tailColumn
  apply sum_congr rfl
  intro i _
  rw [Cvs.Approximant.CosineColumnTailPairing.QWbil_connesClass_modeMap]
  ring

theorem tailColumn_even (x N : ℕ) (i : Idx N) :
    Cvs.Approximant.ConnesErrorColumn.tailColumn x N (negI N i) = Cvs.Approximant.ConnesErrorColumn.tailColumn x N i := by
  rw [Cvs.Approximant.ConnesErrorColumn.tailColumn, Cvs.Approximant.ConnesErrorColumn.cosineRow_neg]
  rfl

/-- The whole actual arithmetic tail column has a squared L² budget independent of truncation order. -/
theorem tailColumn_sq_le {x : ℕ} (hx : 80 ≤ 2 * π * x) (N : ℕ) :
    ∑ i, Cvs.Approximant.ConnesErrorColumn.tailColumn x N i ^ 2 ≤ fullColumnBudget x ^ 2 := by
  apply Cvs.WeilForm.PhysicalCubicCorrectionColumn.column_sq_le_of_unit_pairing (negI N) (Cvs.Approximant.ConnesErrorColumn.tailColumn x N)
    (tailColumn_even x N) (fullColumnBudget x)
  intro f hf hunit
  rw [← QWbil_connesClass_eq_tailColumn_dot hx N f hf]
  exact abs_QWbil_connesClass_unit_le hx N f hf hunit

end Cvs.Approximant.ConnesFullColumnBudget
