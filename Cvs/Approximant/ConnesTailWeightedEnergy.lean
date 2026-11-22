import Mathlib
import Cvs.Approximant.ConnesVectorRealScale
import Cvs.Approximant.ConnesWindowCosineDecay
import Cvs.Approximant.CosineColumnTailPairing
import Cvs.Approximant.SpineCouplingTailPairing
import Cvs.Finite.DiagonalCutSymbol
import Cvs.Finite.OneModeEntries
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationQuadraticForm
import Cvs.Finite.TruncationZeroFreeOffAxes
import Cvs.Finite.WindowCosineBessel
import Cvs.Finite.WindowMatrixSymbolKernel
import Cvs.Finite.WindowedModeSumDomain
import Cvs.L2a.BetaProfilePoissonTail
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.EvenBoundaryKernelBound
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.InfimumAttainedSphere
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.Zeta.PrimePowerSideTruncated
import Cvs.Zeta.ZetaDerivFunctionalEquation

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# A weighted energy bound for actual finite Connes tails

The logarithmic symbol bound and the full boundary-kernel bound control actual
differences of Connes truncations by the tail of a summable coefficient series.
-/

noncomputable section

open Real Finset Matrix Filter MeasureTheory

namespace Cvs.Approximant.ConnesTailWeightedEnergy
open Cvs.ZeroCounting

open Cvs.Finite.SymmetricModeSet (Idx mode negI)

/-- A fixed nonnegative constant for the actual archimedean symbol estimate. -/
def archBase : ℝ := max (Classical.choose Cvs.Zeta.ZetaDerivFunctionalEquation.abs_archSymbol_le) 0

theorem archBase_nonneg : 0 ≤ archBase := le_max_right _ _

theorem abs_archSymbol_bound (t : ℝ) :
    |Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t| ≤ archBase * (1 + Real.log (2 + |t|)) := by
  have h := Classical.choose_spec Cvs.Zeta.ZetaDerivFunctionalEquation.abs_archSymbol_le t
  have hl : 0 ≤ 1 + Real.log (2 + |t|) := by
    have : 0 ≤ Real.log (2 + |t|) := Real.log_nonneg (by linarith [abs_nonneg t])
    linarith
  exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hl)

/-- The positive-mode logarithmic square weight. -/
def logWeight (n : ℕ) : ℝ := (1 + Real.log (n : ℝ)) ^ 2

theorem logWeight_one_le {n : ℕ} (hn : 1 ≤ n) : 1 ≤ logWeight n := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hl := Real.log_nonneg hn'
  unfold logWeight
  nlinarith

/-- An explicit window-dependent multiplier for the lattice symbol. -/
def archLatticeConstant (L : ℝ) : ℝ := archBase * (1 + Real.log (2 + 2 * π / L))

theorem archLatticeConstant_nonneg {L : ℝ} (hL : 0 < L) :
    0 ≤ archLatticeConstant L := by
  have hb := archBase_nonneg
  have hl : 0 ≤ Real.log (2 + 2 * π / L) := Real.log_nonneg (by
    have h : 0 < 2 * π / L := by positivity
    linarith)
  unfold archLatticeConstant
  positivity

/-- The actual archimedean symbol on positive lattice modes is controlled by the summable weight. -/
theorem abs_archSymbol_lattice {L : ℝ} (hL : 0 < L) {n : ℕ} (hn : 1 ≤ n) :
    |Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol (2 * π * n / L)| ≤ archLatticeConstant L * logWeight n := by
  let A : ℝ := 2 + 2 * π / L
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := zero_lt_one.trans_le hn'
  have hA : 1 ≤ A := by
    have h : 0 < 2 * π / L := by positivity
    dsimp [A]
    linarith
  have hA0 : 0 < A := zero_lt_one.trans_le hA
  have hlogA := Real.log_nonneg hA
  have hlogn := Real.log_nonneg hn'
  have harg : 2 + 2 * π * n / L ≤ A * n := by
    rw [show A * n = 2 * n + 2 * π * n / L by dsimp [A]; ring]
    linarith
  have hlog : Real.log (2 + 2 * π * n / L) ≤ Real.log A + Real.log n := by
    calc Real.log (2 + 2 * π * n / L) ≤ Real.log (A * n) :=
        Real.log_le_log (by positivity) harg
      _ = Real.log A + Real.log n := Real.log_mul hA0.ne' hn0.ne'
  have hweight : 1 + Real.log (2 + 2 * π * n / L)
      ≤ (1 + Real.log A) * (1 + Real.log n) ^ 2 := by
    nlinarith [mul_nonneg hlogA hlogn, sq_nonneg (Real.log n)]
  have h := abs_archSymbol_bound (2 * π * n / L)
  rw [abs_of_nonneg (by positivity : 0 ≤ 2 * π * n / L)] at h
  exact h.trans (by
    have hm := mul_le_mul_of_nonneg_left hweight archBase_nonneg
    simpa only [archLatticeConstant, logWeight, A, mul_assoc] using hm)

/-- The actual unsigned Connes cosine coefficients. -/
def coef (x : ℕ) (n : ℕ) : ℝ := Cvs.Finite.WindowCosineBessel.coef (Real.log x) (Cvs.Approximant.ConnesVectorRealScale.connesK x) n

/-- The weighted square series already proved summable for the actual Connes profile. -/
def coefTerm (x : ℕ) (k : ℕ) : ℝ := logWeight (k + 1) * coef x (k + 1) ^ 2

theorem coefTerm_nonneg (x k : ℕ) : 0 ≤ coefTerm x k := by
  unfold coefTerm logWeight
  positivity

theorem summable_coefTerm {x : ℕ} (hx : 80 ≤ 2 * π * x) : Summable (coefTerm x) :=
  Cvs.Approximant.ConnesWindowCosineDecay.summable_connes_coef_log_sq hx

/-- The remainder after the first `N` positive modes in the weighted square series. -/
def coefTail (x N : ℕ) : ℝ := (∑' k : ℕ, coefTerm x k) - ∑ k ∈ range N, coefTerm x k

theorem coefTail_nonneg {x : ℕ} (hx : 80 ≤ 2 * π * x) (N : ℕ) : 0 ≤ coefTail x N := by
  unfold coefTail
  exact sub_nonneg.mpr ((summable_coefTerm hx).sum_le_tsum (range N)
    (fun k _ => coefTerm_nonneg x k))

theorem tendsto_coefTail_zero {x : ℕ} (hx : 80 ≤ 2 * π * x) :
    Tendsto (coefTail x) atTop (nhds 0) := by
  have hc : Tendsto (fun _ : ℕ => ∑' k : ℕ, coefTerm x k) atTop
      (nhds (∑' k : ℕ, coefTerm x k)) := tendsto_const_nhds
  have h := hc.sub (summable_coefTerm hx).hasSum.tendsto_sum_nat
  change Tendsto (fun N => (∑' k : ℕ, coefTerm x k) - ∑ k ∈ range N, coefTerm x k) atTop (nhds 0)
  simpa only [sub_self] using h

/-- The actual finite Connes truncation as a continuous form-domain class. -/
def trunc {x : ℕ} (hx0 : (0 : ℝ) < x) (N : ℕ) :
    Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x) :=
  Cvs.Approximant.CosineColumnTailPairing.modeMap hx0 N (Cvs.Approximant.ConnesVectorRealScale.connesCoef x N)

/-- The finite positive mode interval omitted by the smaller truncation. -/
def tailModes (N J : ℕ) : Finset ℕ := Icc (N + 1) J

/-- The omitted actual coefficients embedded in the larger symmetric mode set. -/
def tailCoef (x N J : ℕ) : Idx J → ℝ := Cvs.Finite.SymmetricModeSet.coeff J (tailModes N J) (coef x)

/-- The retained actual coefficients embedded in the larger symmetric mode set. -/
def headCoef (x N J : ℕ) : Idx J → ℝ := Cvs.Finite.SymmetricModeSet.coeff J (range (N + 1)) (coef x)

theorem tailCoef_even (x N J : ℕ) (i : Idx J) :
    tailCoef x N J (negI J i) = tailCoef x N J i := Cvs.Finite.SymmetricModeSet.coeff_even J _ _ i

theorem headCoef_even (x N J : ℕ) (i : Idx J) :
    headCoef x N J (negI J i) = headCoef x N J i := Cvs.Finite.SymmetricModeSet.coeff_even J _ _ i

theorem tailCoef_none (x N J : ℕ) : tailCoef x N J none = 0 := by
  simp [tailCoef, tailModes, Cvs.Finite.SymmetricModeSet.coeff]

theorem headCoef_none (x N J : ℕ) : headCoef x N J none = coef x 0 := by
  simp [headCoef, Cvs.Finite.SymmetricModeSet.coeff]

theorem tailCoef_some (x N J : ℕ) (k : Fin J) (b : Bool) :
    tailCoef x N J (some (k, b)) = if N ≤ k.val then coef x (k.val + 1) / 2 else 0 := by
  have hk : k.val + 1 ≤ J := by omega
  simp only [tailCoef, tailModes, Cvs.Finite.SymmetricModeSet.coeff, mem_Icc]
  have h : N + 1 ≤ k.val + 1 ↔ N ≤ k.val := by omega
  simp only [h, hk, and_true]

theorem headCoef_some (x N J : ℕ) (k : Fin J) (b : Bool) :
    headCoef x N J (some (k, b)) = if k.val < N then coef x (k.val + 1) / 2 else 0 := by
  simp only [headCoef, Cvs.Finite.SymmetricModeSet.coeff, mem_range]
  have h : k.val + 1 < N + 1 ↔ k.val < N := by omega
  simp only [h]

theorem head_add_tail (x N J : ℕ) :
    headCoef x N J + tailCoef x N J = Cvs.Approximant.ConnesVectorRealScale.connesCoef x J := by
  funext i
  rcases i with _ | ⟨k, b⟩
  · simp [Pi.add_apply, headCoef_none, tailCoef_none, Cvs.Approximant.ConnesVectorRealScale.connesCoef, Cvs.Finite.SymmetricModeSet.coeff, coef]
  · rw [Pi.add_apply, headCoef_some, tailCoef_some]
    have hk : k.val + 1 < J + 1 := by omega
    simp only [Cvs.Approximant.ConnesVectorRealScale.connesCoef, Cvs.Finite.SymmetricModeSet.coeff, mem_range, hk, ite_true]
    by_cases h : k.val < N
    · simp [h, show ¬ N ≤ k.val by omega, coef]
    · simp [h, show N ≤ k.val by omega, coef]

/-- Scalar window sums make the form class independent of the containing signed mode order. -/
theorem modeMap_coeff_eq {x : ℕ} (hx0 : (0 : ℝ) < x) (N J : ℕ)
    (s : Finset ℕ) (a : ℕ → ℝ) (hN : s ⊆ range (N + 1)) (hJ : s ⊆ range (J + 1)) :
    Cvs.Approximant.CosineColumnTailPairing.modeMap hx0 J (Cvs.Finite.SymmetricModeSet.coeff J s a) = Cvs.Approximant.CosineColumnTailPairing.modeMap hx0 N (Cvs.Finite.SymmetricModeSet.coeff N s a) := by
  apply Subtype.ext
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [Cvs.Approximant.CosineColumnTailPairing.coe_modeClass_ae hx0 J (Cvs.Finite.SymmetricModeSet.coeff J s a),
    Cvs.Approximant.CosineColumnTailPairing.coe_modeClass_ae hx0 N (Cvs.Finite.SymmetricModeSet.coeff N s a)] with u huJ huN
  change (((Cvs.Approximant.CosineColumnTailPairing.modeClass hx0 J (Cvs.Finite.SymmetricModeSet.coeff J s a)).val.val : ℝ → ℝ) u)
    = (((Cvs.Approximant.CosineColumnTailPairing.modeClass hx0 N (Cvs.Finite.SymmetricModeSet.coeff N s a)).val.val : ℝ → ℝ) u)
  rw [huJ, huN, ← Cvs.Finite.SymmetricModeSet.windowMode_eq_modeSum _ J s a hJ,
    ← Cvs.Finite.SymmetricModeSet.windowMode_eq_modeSum _ N s a hN]

/-- The retained coefficient embedding represents exactly the smaller actual truncation. -/
theorem modeMap_headCoef {x : ℕ} (hx0 : (0 : ℝ) < x) {N J : ℕ} (hNJ : N ≤ J) :
    Cvs.Approximant.CosineColumnTailPairing.modeMap hx0 J (headCoef x N J) = trunc hx0 N := by
  exact modeMap_coeff_eq hx0 N J (range (N + 1)) (coef x) subset_rfl
    (range_mono (by omega))

/-- Two actual truncations differ by the actual omitted coefficients in the larger order. -/
theorem modeMap_tailCoef {x : ℕ} (hx0 : (0 : ℝ) < x) {N J : ℕ} (hNJ : N ≤ J) :
    Cvs.Approximant.CosineColumnTailPairing.modeMap hx0 J (tailCoef x N J) = trunc hx0 J - trunc hx0 N := by
  have h := congrArg (Cvs.Approximant.CosineColumnTailPairing.modeMap hx0 J) (head_add_tail x N J)
  rw [map_add, modeMap_headCoef hx0 hNJ] at h
  change trunc hx0 N + Cvs.Approximant.CosineColumnTailPairing.modeMap hx0 J (tailCoef x N J) = trunc hx0 J at h
  rw [← h]
  abel

/-- A finite segment of the actual summable weighted square series. -/
def tailSum (x N J : ℕ) : ℝ := ∑ k ∈ range J \ range N, coefTerm x k

theorem tailSum_nonneg (x N J : ℕ) : 0 ≤ tailSum x N J :=
  sum_nonneg fun k _ => coefTerm_nonneg x k

theorem tailSum_eq_fin (x N J : ℕ) :
    tailSum x N J = ∑ k : Fin J, if N ≤ k.val then coefTerm x k.val else 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun k => if N ≤ k then coefTerm x k else 0) J]
  simp only [tailSum, sdiff_eq_filter, sum_filter, mem_range, not_lt]

theorem tailSum_le_coefTail {x : ℕ} (hx : 80 ≤ 2 * π * x) {N J : ℕ} (hNJ : N ≤ J) :
    tailSum x N J ≤ coefTail x N := by
  have hs := sum_sdiff (f := coefTerm x) (range_mono hNJ)
  have ht := (summable_coefTerm hx).sum_le_tsum (range J) (fun k _ => coefTerm_nonneg x k)
  unfold tailSum coefTail
  linarith

/-- The coefficient square norm is controlled by the same finite weighted tail. -/
theorem tailCoef_norm_le (x N J : ℕ) :
    (∑ i, tailCoef x N J i ^ 2) ≤ tailSum x N J := by
  rw [Cvs.WeilForm.EvenBoundaryKernelBound.idx_even_sq J (tailCoef x N J) (tailCoef_even x N J), tailCoef_none, tailSum_eq_fin]
  norm_num only [zero_pow, zero_add]
  rw [Finset.mul_sum]
  apply sum_le_sum; intro k _
  rw [tailCoef_some]
  by_cases h : N ≤ k.val
  · rw [ite_eq_left h, ite_eq_left h]
    have hw := logWeight_one_le (show 1 ≤ k.val + 1 by omega)
    unfold coefTerm
    nlinarith [sq_nonneg (coef x (k.val + 1))]
  · rw [ite_eq_right h, ite_eq_right h]
    norm_num

/-- The actual matrix's symbol and boundary decomposition in finite coefficient coordinates. -/
theorem matrix_quad_eq {L : ℝ} (hL : 0 < L) (P R J : ℕ) (f : Idx J → ℝ) :
    f ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (mode J) *ᵥ f)
      = (∑ i, f i ^ 2 * Cvs.Finite.WindowMatrixSymbolKernel.symbolCut P R L (2 * π * (mode J i : ℝ) / L))
        + f ⬝ᵥ (Cvs.WeilForm.EvenBoundaryKernelBound.boundaryMatrix P R L J *ᵥ f) := by
  change (∑ i, f i * ∑ j, Cvs.Finite.TruncationQuadraticForm.M P R L (mode J) i j * f j) = _
  simp only [Cvs.Finite.WindowMatrixSymbolKernel.M_apply_kernel hL P R (Cvs.Finite.SymmetricModeSet.mode_injective J), add_mul,
    sum_add_distrib, mul_add, ite_mul, zero_mul, sum_ite_eq, mem_univ, ite_true]
  congr 1
  · exact sum_congr rfl fun i _ => by ring
  · change (∑ i, f i * ∑ j, (1 / L * Cvs.Finite.WindowMatrixSymbolKernel.kK P R L
      (2 * π * (mode J i : ℝ) / L) (2 * π * (mode J j : ℝ) / L)) * f j)
      = ∑ i, f i * ∑ j, Cvs.WeilForm.EvenBoundaryKernelBound.boundaryMatrix P R L J i j * f j
    unfold Cvs.WeilForm.EvenBoundaryKernelBound.boundaryMatrix
    simp only [one_div_mul_eq_div]

/-- The finite prime cosine symbol adds only its fixed diagonal weight budget. -/
theorem symbolCut_positive_bound {L : ℝ} (hL : 0 < L) (P R : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    Cvs.Finite.WindowMatrixSymbolKernel.symbolCut P R L (2 * π * n / L)
      ≤ (archLatticeConstant L + Cvs.WeilForm.EvenBoundaryKernelBound.primeDiagonalBudget P R) * logWeight n := by
  have ha := abs_archSymbol_lattice hL hn
  have hp := Cvs.WeilForm.EvenBoundaryKernelBound.abs_prime_cos_le P R L (2 * π * n / L)
  have hw := logWeight_one_le hn
  have hc := Cvs.WeilForm.EvenBoundaryKernelBound.primeDiagonalBudget_nonneg P R
  unfold Cvs.Finite.WindowMatrixSymbolKernel.symbolCut
  nlinarith [le_abs_self (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol (2 * π * n / L)),
    neg_le_abs (Cvs.Finite.OneModeEntries.primeSum P R (Cvs.Finite.DiagonalCutSymbol.cosCut L (2 * π * n / L)))]

theorem symbolCut_neg (P R : ℕ) (L t : ℝ) :
    Cvs.Finite.WindowMatrixSymbolKernel.symbolCut P R L (-t) = Cvs.Finite.WindowMatrixSymbolKernel.symbolCut P R L t := by
  unfold Cvs.Finite.WindowMatrixSymbolKernel.symbolCut
  rw [Cvs.L2a.BetaProfilePoissonTail.archSymbol_neg]
  refine congrArg (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t - ·) ?_
  unfold Cvs.Finite.OneModeEntries.primeSum Cvs.Finite.DiagonalCutSymbol.cosCut
  apply sum_congr rfl; intro p _
  apply sum_congr rfl; intro r _
  by_cases h : (r : ℝ) * Real.log p ≤ L
  · simp only [ite_eq_left h, neg_mul, Real.cos_neg]
  · simp only [ite_eq_right h]

/-- The actual finite tail's diagonal energy is controlled by its weighted coefficient segment. -/
theorem tail_symbol_le {L : ℝ} (hL : 0 < L) (P R x N J : ℕ) :
    (∑ i, tailCoef x N J i ^ 2 * Cvs.Finite.WindowMatrixSymbolKernel.symbolCut P R L (2 * π * (mode J i : ℝ) / L))
      ≤ (archLatticeConstant L + Cvs.WeilForm.EvenBoundaryKernelBound.primeDiagonalBudget P R) * tailSum x N J := by
  rw [Fintype.sum_option, Fintype.sum_prod_type, tailCoef_none, tailSum_eq_fin]
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul, zero_add, Fintype.sum_bool]
  rw [Finset.mul_sum]
  apply sum_le_sum; intro k _
  rw [tailCoef_some, tailCoef_some, Cvs.WeilForm.EvenBoundaryKernelBound.idx_freq_true, Cvs.WeilForm.EvenBoundaryKernelBound.idx_freq_false, symbolCut_neg]
  unfold Cvs.WeilForm.EvenBoundaryKernelBound.positiveMode
  by_cases h : N ≤ k.val
  · rw [ite_eq_left h, ite_eq_left h]
    have hb := symbolCut_positive_bound hL P R (show 1 ≤ k.val + 1 by omega)
    have hw := logWeight_one_le (show 1 ≤ k.val + 1 by omega)
    have hc : 0 ≤ archLatticeConstant L + Cvs.WeilForm.EvenBoundaryKernelBound.primeDiagonalBudget P R :=
      add_nonneg (archLatticeConstant_nonneg hL) (Cvs.WeilForm.EvenBoundaryKernelBound.primeDiagonalBudget_nonneg P R)
    have hm := mul_le_mul_of_nonneg_left hb (sq_nonneg (coef x (k.val + 1) / 2))
    unfold coefTerm
    nlinarith [sq_nonneg (coef x (k.val + 1)), mul_nonneg hc (by positivity : 0 ≤ logWeight (k.val + 1))]
  · rw [ite_eq_right h, ite_eq_right h]
    norm_num

/-- A fixed energy multiplier for actual cosine tails. -/
def energyConstant (P R : ℕ) (L : ℝ) : ℝ :=
  L * (archLatticeConstant L + Cvs.WeilForm.EvenBoundaryKernelBound.primeDiagonalBudget P R + Cvs.WeilForm.EvenBoundaryKernelBound.kernelBudget P R L)

theorem energyConstant_nonneg {L : ℝ} (hL : 0 < L) (P R : ℕ) :
    0 ≤ energyConstant P R L := by
  have ha := archLatticeConstant_nonneg hL
  have hp := Cvs.WeilForm.EvenBoundaryKernelBound.primeDiagonalBudget_nonneg P R
  have hk := Cvs.WeilForm.EvenBoundaryKernelBound.kernelBudget_nonneg hL P R
  unfold energyConstant
  positivity

/-- The actual continuous form of every finite tail has a concrete weighted energy bound. -/
theorem Q_tailCoef_le {x : ℕ} (hx : 80 ≤ 2 * π * x) (P R N J : ℕ) :
    Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) P R
      (Cvs.Approximant.CosineColumnTailPairing.modeMap (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) J (tailCoef x N J))
      ≤ energyConstant P R (Real.log x) * tailSum x N J := by
  have hx1 := Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx
  have hL := Real.log_pos hx1
  rw [Cvs.Approximant.CosineColumnTailPairing.Q_modeMap (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) hx1 P R J _ (tailCoef_even x N J), matrix_quad_eq hL]
  have ha := tail_symbol_le hL P R x N J
  have hk := Cvs.WeilForm.EvenBoundaryKernelBound.idx_full_kernel_bound hL P R J (tailCoef x N J) (tailCoef_even x N J)
  have hke : |tailCoef x N J ⬝ᵥ (Cvs.WeilForm.EvenBoundaryKernelBound.boundaryMatrix P R (Real.log x) J *ᵥ tailCoef x N J)|
      ≤ Cvs.WeilForm.EvenBoundaryKernelBound.kernelBudget P R (Real.log x) * ∑ i, tailCoef x N J i ^ 2 := by
    convert hk using 1
    change |∑ i, tailCoef x N J i * ∑ j, Cvs.WeilForm.EvenBoundaryKernelBound.boundaryMatrix P R (Real.log x) J i j * tailCoef x N J j| = _
    simp only [Finset.mul_sum, Cvs.WeilForm.EvenBoundaryKernelBound.boundaryMatrix]
    congr 1
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring
  have hn := mul_le_mul_of_nonneg_left (tailCoef_norm_le x N J) (Cvs.WeilForm.EvenBoundaryKernelBound.kernelBudget_nonneg hL P R)
  have hq := le_trans (le_abs_self _) (hke.trans hn)
  unfold energyConstant
  nlinarith

/-- A nonnegative summable-series remainder majorizing actual truncation-difference energies. -/
def majorant (x N : ℕ) : ℝ := energyConstant x (Nat.clog 2 x) (Real.log x) * coefTail x N

theorem majorant_nonneg {x : ℕ} (hx : 80 ≤ 2 * π * x) (N : ℕ) : 0 ≤ majorant x N :=
  mul_nonneg (energyConstant_nonneg (Real.log_pos (Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx)) _ _) (coefTail_nonneg hx N)

theorem tendsto_majorant_zero {x : ℕ} (hx : 80 ≤ 2 * π * x) :
    Tendsto (majorant x) atTop (nhds 0) := by
  have h := (tendsto_coefTail_zero hx).const_mul (energyConstant x (Nat.clog 2 x) (Real.log x))
  change Tendsto (fun N => energyConstant x (Nat.clog 2 x) (Real.log x) * coefTail x N) atTop (nhds 0)
  simpa only [mul_zero] using h

/-- Every two actual Connes truncations have energy bounded by the smaller cutoff's vanishing tail. -/
theorem Q_trunc_sub_le {x : ℕ} (hx : 80 ≤ 2 * π * x) {N J : ℕ} (hNJ : N ≤ J) :
    Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) x (Nat.clog 2 x)
      (trunc (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) J - trunc (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) N)
      ≤ majorant x N := by
  rw [← modeMap_tailCoef (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) hNJ]
  have h := Q_tailCoef_le hx x (Nat.clog 2 x) N J
  exact h.trans (mul_le_mul_of_nonneg_left (tailSum_le_coefTail hx hNJ)
    (energyConstant_nonneg (Real.log_pos (Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx)) _ _))

end Cvs.Approximant.ConnesTailWeightedEnergy
