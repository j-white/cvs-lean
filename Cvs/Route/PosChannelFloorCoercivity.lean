import Mathlib
import Cvs.Finite.PairPoleChannelClosed
import Cvs.Finite.WindowMatrixSymbolKernel
import Cvs.Route.EvenMatrixSlotPoleRestored
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.LevyTermsSum
import Cvs.Zeta.Digamma
import Cvs.Zeta.DigammaLimitDischarged

/-!
# `PosChannelFloor`, `archPoleQ` Coercivity, and Even Basis Rung Elimination

Establishes positivity of `poleFactor` and `uu`, support-based coercivity of `archPoleQ` and
`posChannelQ`, and unconditional `PosChannelFloor` when low-frequency `evenBasisVec` modes lie in `Rg`.
-/

set_option maxHeartbeats 800000
set_option autoImplicit false

noncomputable section

namespace Cvs.Route.PosChannelFloorCoercivity
open Cvs.ZeroCounting

open scoped Matrix
open Real Finset
open Cvs.Finite.SymmetricModeSet
open Cvs.Route.EvenMatrixSlotPoleRestored

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Exact square identity and strict positivity of `poleFactor` and `uu` -/

/-- `poleFactor L` is the exact square `(exp(L/4) − exp(−L/4))²`. -/
theorem poleFactor_eq_sq (L : ℝ) :
    Cvs.Finite.PairPoleChannelClosed.poleFactor L = (Real.exp (L / 4) - Real.exp (-(L / 4))) ^ 2 := by
  unfold Cvs.Finite.PairPoleChannelClosed.poleFactor
  have h1 : Real.exp (L / 2) = Real.exp (L / 4) ^ 2 := by
    rw [sq, ← Real.exp_add]
    congr 1; ring
  have h2 : Real.exp (-(L / 2)) = Real.exp (-(L / 4)) ^ 2 := by
    rw [sq, ← Real.exp_add]
    congr 1; ring
  have h3 : Real.exp (L / 4) * Real.exp (-(L / 4)) = 1 := by
    rw [← Real.exp_add]
    have h0 : L / 4 + -(L / 4) = 0 := by ring
    rw [h0, Real.exp_zero]
  rw [h1, h2]
  linear_combination 2 * h3

/-- `poleFactor L` is nonnegative for all `L : ℝ`. -/
theorem poleFactor_nonneg (L : ℝ) : 0 ≤ Cvs.Finite.PairPoleChannelClosed.poleFactor L := by
  rw [poleFactor_eq_sq]
  exact sq_nonneg _

/-- The even Lorentzian factor `uu a ω = a / (a² + ω²)` is strictly positive for `0 < a`. -/
theorem uu_pos {a : ℝ} (ha : 0 < a) (ω : ℝ) : 0 < Cvs.Finite.WindowMatrixSymbolKernel.uu a ω := by
  unfold Cvs.Finite.WindowMatrixSymbolKernel.uu
  positivity

/-- At the zero mode `ω = 0` and pole abscissa `a = 1/2`, `uu (1/2) 0 = 2`. -/
theorem uu_half_zero : Cvs.Finite.WindowMatrixSymbolKernel.uu (1 / 2) 0 = 2 := by
  unfold Cvs.Finite.WindowMatrixSymbolKernel.uu
  norm_num

/-! ### Evenness and logarithmic lower bounds for `archSymbol` -/

/-- `digammaDeficit` is an even function of the frequency `t`. -/
theorem digammaDeficit_neg (t : ℝ) (k : ℕ) :
    Cvs.Zeta.digammaDeficit (-t) k = Cvs.Zeta.digammaDeficit t k := by
  rw [Cvs.Zeta.digammaDeficit_eq, Cvs.Zeta.digammaDeficit_eq]
  ring

/-- The increment `archSymbol t − archSymbol 0` is the sum of `digammaDeficit t`. -/
theorem archSymbol_sub_zero_eq_tsum (t : ℝ) :
    Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 = ∑' k, Cvs.Zeta.digammaDeficit t k := by
  unfold Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol
  rw [Cvs.WeilForm.Archimedean.LevyTermsSum.tsum_digammaDeficit]
  ring

/-- `archSymbol` is an even function: `archSymbol (−t) = archSymbol t`. -/
theorem archSymbol_neg (t : ℝ) : Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol (-t) = Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t := by
  have h1 := archSymbol_sub_zero_eq_tsum (-t)
  have h2 := archSymbol_sub_zero_eq_tsum t
  have h3 : (∑' k, Cvs.Zeta.digammaDeficit (-t) k) = ∑' k, Cvs.Zeta.digammaDeficit t k :=
    tsum_congr (digammaDeficit_neg t)
  linarith

/-- `archSymbol |t| = archSymbol t` for all `t : ℝ`. -/
theorem archSymbol_abs (t : ℝ) : Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol |t| = Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t := by
  rcases le_or_gt 0 t with ht | ht
  · rw [abs_of_nonneg ht]
  · rw [abs_of_neg ht, archSymbol_neg]

/-- Symmetric logarithmic lower bound on `archSymbol t` whenever `2 ≤ |t|`. -/
theorem archSymbol_ge_of_two_le_abs {t : ℝ} (ht : 2 ≤ |t|) :
    Real.log (|t| / 2) - 57 / |t| - Real.log Real.pi ≤ Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t := by
  rw [← archSymbol_abs t]
  exact Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol_ge ht

/-! ### Monotonicity and support-based coercivity of `archPoleQ` and `posChannelQ` -/

/-! ### Even basis vectors and low-mode elimination via the rung subspace `Rg` -/

/-- The symmetrized basis vector `e_i + e_{neg i}` at mode index `i`. -/
def evenBasisVec (neg : ι → ι) (i : ι) : ι → ℝ :=
  fun j => (if j = i then 1 else 0) + (if j = neg i then 1 else 0)

omit [Fintype ι] in
/-- `evenBasisVec neg i` belongs to `evenModeSub neg` when `neg` is involutive. -/
theorem evenBasisVec_mem_evenModeSub {neg : ι → ι} (hinv : Function.Involutive neg) (i : ι) :
    evenBasisVec neg i ∈ evenModeSub neg := by
  intro j
  unfold evenBasisVec
  have h1 : (neg j = i) ↔ (j = neg i) :=
    ⟨fun h => by rw [← h, hinv j], fun h => by rw [h, hinv i]⟩
  have h2 : (neg j = neg i) ↔ (j = i) := hinv.injective.eq_iff
  simp only [h1, h2]
  ring

omit [Fintype ι] in
/-- The submodule spanned by any family of `evenBasisVec neg` vectors is contained in `evenModeSub neg`. -/
theorem span_evenBasisVec_le_evenModeSub {neg : ι → ι} (hinv : Function.Involutive neg) (S : Set ι) :
    Submodule.span ℝ (evenBasisVec neg '' S) ≤ evenModeSub neg := by
  rw [Submodule.span_le]
  rintro _ ⟨i, _, rfl⟩
  exact evenBasisVec_mem_evenModeSub hinv i

/-- Dot product of `evenBasisVec neg i` with any `w ∈ evenModeSub neg` equals `2 * w i`. -/
theorem dotProduct_evenBasisVec_of_even {neg : ι → ι} (hinv : Function.Involutive neg)
    {w : ι → ℝ} (hw : w ∈ evenModeSub neg) (i : ι) :
    evenBasisVec neg i ⬝ᵥ w = 2 * w i := by
  have _ := hinv
  unfold evenBasisVec dotProduct
  simp only [add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  have hev : w (neg i) = w i := hw i
  linarith

/-- Any bulk vector `w ∈ Bulk (evenModeSub neg) Rg` vanishes at mode `i` if `evenBasisVec neg i ∈ Rg`. -/
theorem apply_eq_zero_of_evenBasisVec_mem_rung {neg : ι → ι} (hinv : Function.Involutive neg)
    {Rg : Submodule ℝ (ι → ℝ)} {w : ι → ℝ} (hw : Bulk (evenModeSub neg) Rg w)
    {i : ι} (hi : evenBasisVec neg i ∈ Rg) :
    w i = 0 := by
  have hdot := hw.2 (evenBasisVec neg i) hi
  rw [dotProduct_evenBasisVec_of_even hinv hw.1 i] at hdot
  linarith

end Cvs.Route.PosChannelFloorCoercivity
