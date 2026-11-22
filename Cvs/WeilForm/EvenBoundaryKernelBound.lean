import Mathlib
import Cvs.Finite.DiagonalCutSymbol
import Cvs.Finite.DiagonalLevySymbol
import Cvs.Finite.LevyKernelIncrement
import Cvs.Finite.ModeSumFormDomain
import Cvs.Finite.ModeSumPairValues
import Cvs.Finite.OneModeEntries
import Cvs.Finite.PairFormDividedDifference
import Cvs.Finite.PairPoleChannelClosed
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationQuadraticForm
import Cvs.Finite.TruncationZeroFreeOffAxes
import Cvs.Finite.WindowMatrixSymbolKernel
import Cvs.Upstream.SymmetricMatrixBottom
import Cvs.WeilForm.Archimedean.EvenLadderUniformBound
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
# A bound for the full even boundary kernel

The zero mode contributes a scalar budget, and the first ladder term bounds the pole.
The finite prime kernel is a bounded cosine diagonal minus a translation form.
Their sum bounds the full even kernel independently of mode order for each fixed
positive window and finite prime truncation.
-/

noncomputable section

open Real Finset Matrix

namespace Cvs.WeilForm.EvenBoundaryKernelBound

open Cvs.Finite.WindowMatrixSymbolKernel (bk uu vv)

theorem uu_neg (b x : ℝ) : uu b (-x) = uu b x := by simp [uu]

theorem vv_neg (b x : ℝ) : vv b (-x) = -vv b x := by simp [vv, neg_div]

/-- The coefficients of the positive archimedean ladder. -/
def weight (L : ℝ) (k : ℕ) : ℝ := 2 * (1 - Cvs.Finite.DiagonalLevySymbol.tailFactor L k)

theorem weight_nonneg {L : ℝ} (hL : 0 < L) (k : ℕ) : 0 ≤ weight L k := by
  have htf : Cvs.Finite.DiagonalLevySymbol.tailFactor L k ≤ 1 := by
    rw [Cvs.Finite.WindowMatrixSymbolKernel.tailFactor_eq_rpow]
    exact Real.exp_le_one_iff.mpr (by nlinarith [Cvs.Finite.WindowMatrixSymbolKernel.bk_pos k])
  dsimp [weight]
  linarith

/-- The positive part of each ladder pair is summable, including zero frequencies. -/
theorem summable_ladder_uu {L : ℝ} (hL : 0 < L) (A B : ℝ) :
    Summable (fun k : ℕ => weight L k * uu (bk k) A * uu (bk k) B) := by
  have h := ((Cvs.Finite.WindowMatrixSymbolKernel.summable_ladder_pair hL A B).add
    (Cvs.Finite.WindowMatrixSymbolKernel.summable_ladder_pair hL A (-B))).div_const 2
  refine h.congr fun k => ?_
  simp only [uu_neg, vv_neg]
  dsimp [weight]
  ring

section Finite

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- The ladder quadratic form is its sum of positive rank-one squares. -/
theorem ladder_quad {L : ℝ} (hL : 0 < L) (ω : ι → ℝ) (u : ι → ℝ) :
    (∑ i, ∑ j, u i * u j * Cvs.WeilForm.Archimedean.EvenLadderUniformBound.ladder L (ω i) (ω j))
      = ∑' k : ℕ, weight L k * (∑ i, u i * uu (bk k) (ω i)) ^ 2 := by
  simp only [Cvs.WeilForm.Archimedean.EvenLadderUniformBound.ladder]
  have hs : ∀ i j, Summable (fun k : ℕ =>
      u i * u j * (weight L k * uu (bk k) (ω i) * uu (bk k) (ω j))) :=
    fun i j => (summable_ladder_uu hL (ω i) (ω j)).mul_left _
  simp_rw [← tsum_mul_left]
  change (∑ i, ∑ j, ∑' k : ℕ,
    u i * u j * (weight L k * uu (bk k) (ω i) * uu (bk k) (ω j))) = _
  have h2 : ∀ i, (∑ j, ∑' k : ℕ,
      u i * u j * (weight L k * uu (bk k) (ω i) * uu (bk k) (ω j)))
      = ∑' k : ℕ, ∑ j, u i * u j *
        (weight L k * uu (bk k) (ω i) * uu (bk k) (ω j)) :=
    fun i => (Summable.tsum_finsetSum fun j _ => hs i j).symm
  simp only [h2]
  rw [← Summable.tsum_finsetSum fun i _ => summable_sum fun j _ => hs i j]
  refine tsum_congr fun k => ?_
  simp only [weight, pow_two, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

omit [DecidableEq ι] in
/-- The positive rank-one square family is summable. -/
theorem summable_ladder_square {L : ℝ} (hL : 0 < L) (ω : ι → ℝ) (u : ι → ℝ) :
    Summable (fun k : ℕ => weight L k * (∑ i, u i * uu (bk k) (ω i)) ^ 2) := by
  have hs : Summable (fun k : ℕ => ∑ i, ∑ j,
      u i * u j * (weight L k * uu (bk k) (ω i) * uu (bk k) (ω j))) :=
    summable_sum fun i _ => summable_sum fun j _ =>
      (summable_ladder_uu hL (ω i) (ω j)).mul_left _
  refine hs.congr fun k => ?_
  simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end Finite

/-- The scalar zero-mode budget of the normalized ladder. -/
def zeroBudget (L : ℝ) : ℝ := Cvs.WeilForm.Archimedean.EvenLadderUniformBound.ladder L 0 0 / L

theorem zeroBudget_nonneg {L : ℝ} (hL : 0 < L) : 0 ≤ zeroBudget L := by
  unfold zeroBudget Cvs.WeilForm.Archimedean.EvenLadderUniformBound.ladder
  apply div_nonneg (tsum_nonneg fun k => ?_) hL.le
  have hw := weight_nonneg hL k
  have hb := Cvs.Finite.WindowMatrixSymbolKernel.bk_pos k
  change 0 ≤ weight L k * uu (bk k) 0 * uu (bk k) 0
  have hu : 0 ≤ uu (bk k) 0 := by unfold uu; positivity
  positivity

section Even

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Signed frequencies with the zero mode adjoined. -/
def signedFreq (L : ℝ) (mode : ι → ℕ) : Option (ι ⊕ ι) → ℝ
  | none => 0
  | some (.inl i) => 2 * π * mode i / L
  | some (.inr i) => -(2 * π * mode i / L)

/-- Equal coefficients at opposite frequencies, with an arbitrary zero coefficient. -/
def evenCoeff (a : ℝ) (u : ι → ℝ) : Option (ι ⊕ ι) → ℝ
  | none => a
  | some (.inl i) => u i
  | some (.inr i) => u i

omit [DecidableEq ι] in
theorem even_sum_uu (L b : ℝ) (mode : ι → ℕ) (a : ℝ) (u : ι → ℝ) :
    (∑ i, evenCoeff a u i * uu b (signedFreq L mode i))
      = a * uu b 0 + 2 * ∑ i, u i * uu b (2 * π * mode i / L) := by
  simp only [Fintype.sum_option, Fintype.sum_sum_type, evenCoeff, signedFreq, uu_neg]
  ring

omit [DecidableEq ι] in
theorem even_sum_vv (L b : ℝ) (mode : ι → ℕ) (a : ℝ) (u : ι → ℝ) :
    (∑ i, evenCoeff a u i * vv b (signedFreq L mode i)) = 0 := by
  simp only [Fintype.sum_option, Fintype.sum_sum_type, evenCoeff, signedFreq, vv_neg]
  have hz : vv b 0 = 0 := by simp [vv]
  rw [hz, mul_zero]
  simp only [mul_neg, Finset.sum_neg_distrib]
  ring

omit [DecidableEq ι] in
theorem even_coeff_sq (a : ℝ) (u : ι → ℝ) :
    (∑ i, evenCoeff a u i ^ 2) = a ^ 2 + 2 * ∑ i, u i ^ 2 := by
  simp only [Fintype.sum_option, Fintype.sum_sum_type, evenCoeff]
  ring

/-- The actual even archimedean kernel form, including its zero mode and pole. -/
def archQuad (L : ℝ) (mode : ι → ℕ) (a : ℝ) (u : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, evenCoeff a u i * evenCoeff a u j *
    (Cvs.Finite.WindowMatrixSymbolKernel.kArch L (signedFreq L mode i) (signedFreq L mode j) / L)

/-- The normalized signed even ladder form, including its zero mode. -/
def evenLadderQuad (L : ℝ) (mode : ι → ℕ) (a : ℝ) (u : ι → ℝ) : ℝ :=
  (∑' k : ℕ, weight L k *
    (a * uu (bk k) 0 + 2 * ∑ i, u i * uu (bk k) (2 * π * mode i / L)) ^ 2) / L

omit [DecidableEq ι] in
theorem summable_even_square {L : ℝ} (hL : 0 < L) (mode : ι → ℕ)
    (a : ℝ) (u : ι → ℝ) :
    Summable (fun k : ℕ => weight L k *
      (a * uu (bk k) 0 + 2 * ∑ i, u i * uu (bk k) (2 * π * mode i / L)) ^ 2) := by
  simpa only [even_sum_uu] using
    summable_ladder_square hL (signedFreq L mode) (evenCoeff a u)

theorem archQuad_eq {L : ℝ} (hL : 0 < L) (mode : ι → ℕ) (a : ℝ) (u : ι → ℝ) :
    archQuad L mode a u =
      2 * Cvs.Finite.PairPoleChannelClosed.poleFactor L / L *
        (a * uu (1 / 2) 0 + 2 * ∑ i, u i * uu (1 / 2) (2 * π * mode i / L)) ^ 2
      + evenLadderQuad L mode a u := by
  unfold archQuad
  simp_rw [← mul_div_assoc, ← Finset.sum_div]
  rw [Cvs.Finite.WindowMatrixSymbolKernel.quadForm_kArch hL]
  simp only [even_sum_uu, even_sum_vv, zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero]
  unfold evenLadderQuad weight
  ring

/-- A constructed scalar bound for the signed ladder, with its zero mode. -/
def ladderBudget (L : ℝ) : ℝ := 2 * zeroBudget L + 2 * (4 + π)

theorem ladderBudget_nonneg {L : ℝ} (hL : 0 < L) : 0 ≤ ladderBudget L := by
  have h := zeroBudget_nonneg hL
  unfold ladderBudget
  positivity

/-- Splitting off zero costs a factor two, while the positive block uses the Hilbert bound. -/
theorem evenLadderQuad_le {L : ℝ} (hL : 0 < L) (mode : ι → ℕ)
    (hinj : Function.Injective mode) (hpos : ∀ i, 0 < mode i)
    (a : ℝ) (u : ι → ℝ) :
    evenLadderQuad L mode a u ≤ ladderBudget L * ∑ i, evenCoeff a u i ^ 2 := by
  let S : ℕ → ℝ := fun k => ∑ i, u i * uu (bk k) (2 * π * mode i / L)
  have hs0 := (summable_ladder_uu hL 0 0).mul_left (2 * a ^ 2)
  have hsp := (summable_ladder_square hL (fun i => 2 * π * mode i / L) u).mul_left 8
  have hpq : (∑' k : ℕ, weight L k * S k ^ 2) / L
      = u ⬝ᵥ (Cvs.WeilForm.Archimedean.EvenLadderUniformBound.positiveMatrix L mode *ᵥ u) := by
    rw [← ladder_quad hL]
    change (∑ i, ∑ j, u i * u j * Cvs.WeilForm.Archimedean.EvenLadderUniformBound.ladder L
      (2 * π * mode i / L) (2 * π * mode j / L)) / L
      = ∑ i, u i * ∑ j, Cvs.WeilForm.Archimedean.EvenLadderUniformBound.positiveMatrix L mode i j * u j
    simp only [Cvs.WeilForm.Archimedean.EvenLadderUniformBound.positiveMatrix, Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have ht := (summable_even_square hL mode a u).tsum_le_tsum
    (g := fun k : ℕ => 2 * a ^ 2 * (weight L k * uu (bk k) 0 * uu (bk k) 0)
      + 8 * (weight L k * S k ^ 2)) (fun k => by
      have hw := weight_nonneg hL k
      have hsq : (a * uu (bk k) 0 + 2 * S k) ^ 2
          ≤ 2 * a ^ 2 * uu (bk k) 0 ^ 2 + 8 * S k ^ 2 := by
        nlinarith [sq_nonneg (a * uu (bk k) 0 - 2 * S k)]
      have h := mul_le_mul_of_nonneg_left hsq hw
      dsimp [S] at h ⊢
      nlinarith) (hs0.add hsp)
  rw [hs0.tsum_add hsp, tsum_mul_left, tsum_mul_left] at ht
  have hnorm : 0 ≤ ∑ i, u i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hzero := zeroBudget_nonneg hL
  have hposq := Cvs.WeilForm.Archimedean.EvenLadderUniformBound.positiveMatrix_quad_le hL mode hinj hpos u
  have hdiv := div_le_div_of_nonneg_right ht hL.le
  change evenLadderQuad L mode a u ≤ _ at hdiv
  have hdiv' : evenLadderQuad L mode a u ≤
      2 * a ^ 2 * zeroBudget L + 8 * (u ⬝ᵥ (Cvs.WeilForm.Archimedean.EvenLadderUniformBound.positiveMatrix L mode *ᵥ u)) := by
    refine hdiv.trans_eq ?_
    rw [add_div, mul_div_assoc, mul_div_assoc, hpq]
    rfl
  rw [even_coeff_sq]
  unfold ladderBudget
  nlinarith [sq_nonneg a, Real.pi_pos]

omit [DecidableEq ι] in
theorem evenLadderQuad_nonneg {L : ℝ} (hL : 0 < L) (mode : ι → ℕ)
    (a : ℝ) (u : ι → ℝ) : 0 ≤ evenLadderQuad L mode a u := by
  apply div_nonneg (tsum_nonneg fun k => ?_) hL.le
  exact mul_nonneg (weight_nonneg hL k) (sq_nonneg _)

/-- The first ladder coefficient is strictly positive for a positive window. -/
theorem first_gap_pos {L : ℝ} (hL : 0 < L) : 0 < 1 - Cvs.Finite.DiagonalLevySymbol.tailFactor L 0 := by
  rw [Cvs.Finite.WindowMatrixSymbolKernel.tailFactor_eq_rpow]
  have h : Real.exp (-bk 0 * L) < 1 := Real.exp_lt_one_iff.mpr (by
    have hb := Cvs.Finite.WindowMatrixSymbolKernel.bk_pos 0
    nlinarith)
  simpa only [neg_mul] using (sub_pos.mpr h)

omit [DecidableEq ι] in
/-- The finite pole rank-one term is controlled by the first term of the same ladder. -/
theorem pole_le_ladder {L : ℝ} (hL : 0 < L) (mode : ι → ℕ) (a : ℝ) (u : ι → ℝ) :
    2 * Cvs.Finite.PairPoleChannelClosed.poleFactor L / L *
        (a * uu (1 / 2) 0 + 2 * ∑ i, u i * uu (1 / 2) (2 * π * mode i / L)) ^ 2
      ≤ Cvs.Finite.PairPoleChannelClosed.poleFactor L / (1 - Cvs.Finite.DiagonalLevySymbol.tailFactor L 0) * evenLadderQuad L mode a u := by
  have hp := Cvs.Finite.WindowMatrixSymbolKernel.poleFactor_nonneg L
  have hd := first_gap_pos hL
  have h := (summable_even_square hL mode a u).le_tsum 0
    (fun k _ => mul_nonneg (weight_nonneg hL k) (sq_nonneg _))
  have h' := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right h hL.le)
    (div_nonneg hp hd.le)
  refine le_of_eq_of_le ?_ h'
  unfold weight bk
  norm_num
  field_simp

/-- A constructed bound for the actual full even archimedean boundary kernel. -/
def archBudget (L : ℝ) : ℝ :=
  (1 + Cvs.Finite.PairPoleChannelClosed.poleFactor L / (1 - Cvs.Finite.DiagonalLevySymbol.tailFactor L 0)) * ladderBudget L

theorem archBudget_nonneg {L : ℝ} (hL : 0 < L) : 0 ≤ archBudget L := by
  have hp := Cvs.Finite.WindowMatrixSymbolKernel.poleFactor_nonneg L
  have hd := first_gap_pos hL
  have hl := ladderBudget_nonneg hL
  unfold archBudget
  positivity

theorem archQuad_nonneg {L : ℝ} (hL : 0 < L) (mode : ι → ℕ) (a : ℝ) (u : ι → ℝ) :
    0 ≤ archQuad L mode a u := by
  rw [archQuad_eq hL]
  have hp := Cvs.Finite.WindowMatrixSymbolKernel.poleFactor_nonneg L
  have hq := evenLadderQuad_nonneg hL mode a u
  positivity

/-- The full actual even archimedean kernel has an order-independent bound. -/
theorem archQuad_le {L : ℝ} (hL : 0 < L) (mode : ι → ℕ)
    (hinj : Function.Injective mode) (hpos : ∀ i, 0 < mode i) (a : ℝ) (u : ι → ℝ) :
    archQuad L mode a u ≤ archBudget L * ∑ i, evenCoeff a u i ^ 2 := by
  have hp := Cvs.Finite.WindowMatrixSymbolKernel.poleFactor_nonneg L
  have hd := first_gap_pos hL
  have hc : 0 ≤ 1 + Cvs.Finite.PairPoleChannelClosed.poleFactor L / (1 - Cvs.Finite.DiagonalLevySymbol.tailFactor L 0) := by positivity
  have hq := mul_le_mul_of_nonneg_left (evenLadderQuad_le hL mode hinj hpos a u) hc
  have hr := pole_le_ladder hL mode a u
  rw [archQuad_eq hL]
  unfold archBudget
  nlinarith

/-- An absolute form bound for the same concrete even kernel. -/
theorem abs_archQuad_le {L : ℝ} (hL : 0 < L) (mode : ι → ℕ)
    (hinj : Function.Injective mode) (hpos : ∀ i, 0 < mode i) (a : ℝ) (u : ι → ℝ) :
    |archQuad L mode a u| ≤ archBudget L * ∑ i, evenCoeff a u i ^ 2 := by
  rw [abs_of_nonneg (archQuad_nonneg hL mode a u)]
  exact archQuad_le hL mode hinj hpos a u

end Even

section Concrete

open Cvs.Finite.SymmetricModeSet (Idx mode negI)

/-- The positive frequencies belonging to the actual symmetric order-`N` mode set. -/
def positiveMode (N : ℕ) (k : Fin N) : ℕ := k.val + 1

theorem positiveMode_injective (N : ℕ) : Function.Injective (positiveMode N) := by
  intro i j h
  apply Fin.ext
  dsimp [positiveMode] at h
  omega

theorem positiveMode_pos (N : ℕ) (k : Fin N) : 0 < positiveMode N k := by
  dsimp [positiveMode]
  omega

theorem idx_freq_true (L : ℝ) (N : ℕ) (k : Fin N) :
    2 * π * (mode N (some (k, true)) : ℝ) / L = 2 * π * positiveMode N k / L := by
  simp [mode, positiveMode]

theorem idx_freq_false (L : ℝ) (N : ℕ) (k : Fin N) :
    2 * π * (mode N (some (k, false)) : ℝ) / L = -(2 * π * positiveMode N k / L) := by
  simp [mode, positiveMode]
  ring

theorem idx_even_pair (N : ℕ) (ξ : Idx N → ℝ)
    (heven : ∀ i, ξ (negI N i) = ξ i) (k : Fin N) :
    ξ (some (k, false)) = ξ (some (k, true)) := by
  simpa only [negI, Bool.not_true] using heven (some (k, true))

/-- The even rank-one coordinate of an actual order-`N` vector. -/
theorem idx_sum_uu (L b : ℝ) (N : ℕ) (ξ : Idx N → ℝ)
    (heven : ∀ i, ξ (negI N i) = ξ i) :
    (∑ i, ξ i * uu b (2 * π * (mode N i : ℝ) / L))
      = ξ none * uu b 0 + 2 * ∑ k : Fin N,
        ξ (some (k, true)) * uu b (2 * π * positiveMode N k / L) := by
  rw [Fintype.sum_option, Fintype.sum_prod_type]
  have hterm : ∀ k : Fin N,
      (∑ s : Bool, ξ (some (k, s)) * uu b (2 * π * (mode N (some (k, s)) : ℝ) / L))
      = 2 * ξ (some (k, true)) * uu b (2 * π * positiveMode N k / L) := by
    intro k
    simp only [Fintype.sum_bool, idx_freq_true, idx_freq_false, uu_neg, idx_even_pair N ξ heven]
    ring
  rw [show 2 * π * (mode N none : ℝ) / L = 0 by simp [mode]]
  simp_rw [hterm]
  rw [Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by ring

/-- Every odd rank-one coordinate vanishes on actual even coefficients. -/
theorem idx_sum_vv (L b : ℝ) (N : ℕ) (ξ : Idx N → ℝ)
    (heven : ∀ i, ξ (negI N i) = ξ i) :
    (∑ i, ξ i * vv b (2 * π * (mode N i : ℝ) / L)) = 0 := by
  rw [Fintype.sum_option, Fintype.sum_prod_type]
  have hterm : ∀ k : Fin N,
      (∑ s : Bool, ξ (some (k, s)) * vv b (2 * π * (mode N (some (k, s)) : ℝ) / L)) = 0 := by
    intro k
    simp only [Fintype.sum_bool, idx_freq_true, idx_freq_false, vv_neg, idx_even_pair N ξ heven]
    ring
  rw [show 2 * π * (mode N none : ℝ) / L = 0 by simp [mode]]
  simp_rw [hterm]
  simp only [Finset.sum_const_zero]
  simp [vv]

/-- The signed coefficient norm includes both copies of each positive mode. -/
theorem idx_even_sq (N : ℕ) (ξ : Idx N → ℝ) (heven : ∀ i, ξ (negI N i) = ξ i) :
    (∑ i, ξ i ^ 2) = ξ none ^ 2 + 2 * ∑ k : Fin N, ξ (some (k, true)) ^ 2 := by
  rw [Fintype.sum_option, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, idx_even_pair N ξ heven]
  rw [Finset.sum_add_distrib]
  ring

/-- The archimedean kernel bound on the actual finite symmetric mode sets. -/
theorem idx_arch_kernel_bound {L : ℝ} (hL : 0 < L) (N : ℕ) (ξ : Idx N → ℝ)
    (heven : ∀ i, ξ (negI N i) = ξ i) :
    |∑ i, ∑ j, ξ i * ξ j *
      (Cvs.Finite.WindowMatrixSymbolKernel.kArch L (2 * π * (mode N i : ℝ) / L)
        (2 * π * (mode N j : ℝ) / L) / L)|
      ≤ archBudget L * ∑ i, ξ i ^ 2 := by
  have h := abs_archQuad_le hL (positiveMode N) (positiveMode_injective N)
    (positiveMode_pos N) (ξ none) (fun k => ξ (some (k, true)))
  have heq : (∑ i, ∑ j, ξ i * ξ j *
      (Cvs.Finite.WindowMatrixSymbolKernel.kArch L (2 * π * (mode N i : ℝ) / L)
        (2 * π * (mode N j : ℝ) / L) / L))
      = archQuad L (positiveMode N) (ξ none) (fun k => ξ (some (k, true))) := by
    simp_rw [← mul_div_assoc, ← Finset.sum_div]
    rw [Cvs.Finite.WindowMatrixSymbolKernel.quadForm_kArch hL, archQuad_eq hL]
    simp only [idx_sum_uu L _ N ξ heven, idx_sum_vv L _ N ξ heven,
      zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero]
    unfold evenLadderQuad weight
    ring
  rw [heq]
  simpa only [even_coeff_sq, idx_even_sq N ξ heven] using h

end Concrete

section Prime

open MeasureTheory Cvs.Zeta.Explicit.Weil
open Cvs.Finite.DiagonalCutSymbol (sinCut cosCut)
open Cvs.Finite.OneModeEntries (primeSum)

/-- Each prime boundary atom is a diagonal cosine minus a translation-overlap atom. -/
theorem boundary_atom_eq {L t : ℝ} (hL : 0 < L) (ht : 0 < t) (m n : ℤ) :
    (if t ≤ L then t * Real.cos (t * (2 * π * m / L + 2 * π * n / L) / 2)
        * Cvs.Finite.WindowMatrixSymbolKernel.sinc (t * (2 * π * m / L - 2 * π * n / L) / 2) else 0) / L
      = (if m = n then cosCut L (2 * π * m / L) t else 0)
        - Cvs.Finite.LevyKernelIncrement.Kc L m n t / 2 := by
  by_cases hmn : m = n
  · subst n
    rw [if_pos rfl, Cvs.Finite.DiagonalCutSymbol.Kc_diag_eq]
    unfold cosCut Cvs.Finite.DiagonalCutSymbol.vcosCut
    simp only [sub_self, mul_zero, zero_div, Cvs.Finite.WindowMatrixSymbolKernel.sinc, if_true]
    by_cases h : t ≤ L
    · rw [if_pos h, if_pos h, if_pos h]
      rw [show t * (2 * π * (m : ℝ) / L + 2 * π * m / L) / 2
        = 2 * π * m / L * t by ring]
      ring
    · simp [h]
  · rw [if_neg hmn, Cvs.Finite.PairFormDividedDifference.Kc_off_eq hmn,
      Cvs.Finite.DiagonalCutSymbol.sigma_eq_sinCut, Cvs.Finite.DiagonalCutSymbol.sigma_eq_sinCut]
    have hnm : (n : ℝ) - m ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (Ne.symm hmn))
    have hω : 2 * π * (m : ℝ) / L ≠ 2 * π * n / L := by
      intro h
      have h' := congrArg (fun x : ℝ => x * L) h
      simp only [div_mul_cancel₀ _ hL.ne'] at h'
      have : (m : ℝ) = n := by nlinarith [Real.pi_pos]
      exact hmn (by exact_mod_cast this)
    rw [← Cvs.Finite.WindowMatrixSymbolKernel.dd_sinCut ht hω]
    have hden : 2 * π * (m : ℝ) / L - 2 * π * n / L
      = 2 * π * ((m : ℝ) - n) / L := by ring
    rw [hden]
    have hmn' : (m : ℝ) - n ≠ 0 := by intro h; exact hnm (by linarith)
    field_simp
    ring

/-- The actual finite prime boundary matrix is a bounded diagonal minus half the prime pairing. -/
theorem kPrime_eq {L : ℝ} (hL : 0 < L) (P R : ℕ) (m n : ℤ) :
    Cvs.Finite.WindowMatrixSymbolKernel.kPrime P R L (2 * π * m / L) (2 * π * n / L) / L
      = (if m = n then primeSum P R (cosCut L (2 * π * m / L)) else 0)
        - Cvs.Finite.ModeSumPairValues.primePair P R L m n / 2 := by
  have hi : (if m = n then primeSum P R (cosCut L (2 * π * m / L)) else 0)
      = ∑ p ∈ (Finset.range (P + 1)).filter Nat.Prime, ∑ r ∈ Finset.Icc 1 R,
        primePowerWeight p r * (2 *
          (if m = n then cosCut L (2 * π * m / L) ((r : ℝ) * Real.log p) else 0)) := by
    unfold primeSum
    split_ifs <;> simp
  rw [hi]
  unfold Cvs.Finite.WindowMatrixSymbolKernel.kPrime Cvs.Finite.ModeSumPairValues.primePair
  simp only [Finset.sum_div]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun r hr => ?_
  have hp' : (1 : ℝ) < p := by
    exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt
  have hr' : (0 : ℝ) < r := by exact_mod_cast (Finset.mem_Icc.mp hr).1
  have ht : 0 < (r : ℝ) * Real.log p := mul_pos hr' (Real.log_pos hp')
  have h := congrArg (fun x : ℝ => 2 * primePowerWeight p r * x)
    (boundary_atom_eq hL ht m n)
  convert h using 1 <;> ring

/-- A finite absolute weight budget for the diagonal cosine term. -/
def primeDiagonalBudget (P R : ℕ) : ℝ :=
  2 * ∑ p ∈ (Finset.range (P + 1)).filter Nat.Prime, ∑ r ∈ Finset.Icc 1 R,
    |primePowerWeight p r|

theorem primeDiagonalBudget_nonneg (P R : ℕ) : 0 ≤ primeDiagonalBudget P R := by
  unfold primeDiagonalBudget
  positivity

theorem abs_prime_cos_le (P R : ℕ) (L ω : ℝ) :
    |primeSum P R (cosCut L ω)| ≤ primeDiagonalBudget P R := by
  unfold primeSum primeDiagonalBudget
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum; intro p _
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum; intro r _
  rw [abs_mul, abs_mul]
  have hc : |cosCut L ω ((r : ℝ) * Real.log p)| ≤ 1 := by
    unfold cosCut
    split_ifs
    · exact Real.abs_cos_le_one _
    · norm_num
  have h := mul_le_mul_of_nonneg_left hc (abs_nonneg (primePowerWeight p r))
  norm_num at *
  nlinarith

/-- The full finite prime budget depends on the prime truncation, and never on mode order. -/
def primeBudget (P R : ℕ) : ℝ :=
  primeDiagonalBudget P R + 2 * Cvs.WeilForm.PrimeSideBoundedBelow.primeWeightTotal P R

theorem primeBudget_nonneg (P R : ℕ) : 0 ≤ primeBudget P R := by
  have h1 := primeDiagonalBudget_nonneg P R
  have h2 := Cvs.WeilForm.PrimeSideBoundedBelow.primeWeightTotal_nonneg P R
  unfold primeBudget
  positivity

/-- The finite prime boundary form has a bound independent of symmetric mode order. -/
theorem idx_prime_kernel_bound {L : ℝ} (hL : 0 < L) (P R N : ℕ) (ξ : Cvs.Finite.SymmetricModeSet.Idx N → ℝ)
    (heven : ∀ i, ξ (Cvs.Finite.SymmetricModeSet.negI N i) = ξ i) :
    |∑ i, ∑ j, ξ i * ξ j *
      (Cvs.Finite.WindowMatrixSymbolKernel.kPrime P R L (2 * π * (Cvs.Finite.SymmetricModeSet.mode N i : ℝ) / L)
        (2 * π * (Cvs.Finite.SymmetricModeSet.mode N j : ℝ) / L) / L)|
      ≤ primeBudget P R * ∑ i, ξ i ^ 2 := by
  let f : ℝ → ℝ := Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L (Cvs.Finite.SymmetricModeSet.mode N) ξ
  have hmem : MemLp f 2 (volume : Measure ℝ) :=
    Cvs.Finite.ModeSumFormDomain.memLp_two_of_bounded (Cvs.Finite.ModeSumPairValues.measurable_modeSum L (Cvs.Finite.SymmetricModeSet.mode N) ξ)
      (Cvs.Finite.ModeSumPairValues.abs_modeSum_le L (Cvs.Finite.SymmetricModeSet.mode N) ξ)
      (fun s hs => Cvs.Finite.ModeSumPairValues.modeSum_eq_zero_of_notMem L (Cvs.Finite.SymmetricModeSet.mode N) ξ hs)
  have hprime := Cvs.WeilForm.PrimeSideBoundedBelow.abs_primePowerSideTruncated_le P R hmem.integrable_sq
    (fun t => hmem.integrable_mul
      (hmem.comp_measurePreserving (measurePreserving_add_right (volume : Measure ℝ) t)))
  have hn : selfConvolution f 0 = L * ∑ i, ξ i ^ 2 := by
    rw [Cvs.Finite.PairFormDividedDifference.selfConvolution_modeSum_zero hL (Cvs.Finite.SymmetricModeSet.mode_injective N)
      (Cvs.Finite.SymmetricModeSet.negI_involutive N) (Cvs.Finite.SymmetricModeSet.mode_negI N) heven]
    simp only [dotProduct, pow_two]
  rw [hn] at hprime
  have hshift : |primePowerSideTruncated P R (selfConvolution f) / L|
      ≤ 2 * Cvs.WeilForm.PrimeSideBoundedBelow.primeWeightTotal P R * ∑ i, ξ i ^ 2 := by
    rw [abs_div, abs_of_pos hL]
    have h := div_le_div_of_nonneg_right hprime hL.le
    exact h.trans_eq (by field_simp)
  have hpair : (∑ i, ∑ j, ξ i * ξ j *
      (Cvs.Finite.ModeSumPairValues.primePair P R L (Cvs.Finite.SymmetricModeSet.mode N i) (Cvs.Finite.SymmetricModeSet.mode N j) / 2))
      = primePowerSideTruncated P R (selfConvolution f) / L := by
    rw [Cvs.Finite.ModeSumPairValues.prime_modeSum hL P R (Cvs.Finite.SymmetricModeSet.mode N)
      (Cvs.Finite.SymmetricModeSet.negI_involutive N) (Cvs.Finite.SymmetricModeSet.mode_negI N) heven]
    simp_rw [← mul_div_assoc, ← Finset.sum_div]
    field_simp
  have hd : (∑ i, ∑ j, ξ i * ξ j *
      (if Cvs.Finite.SymmetricModeSet.mode N i = Cvs.Finite.SymmetricModeSet.mode N j then
        primeSum P R (cosCut L (2 * π * (Cvs.Finite.SymmetricModeSet.mode N i : ℝ) / L)) else 0))
      = ∑ i, ξ i ^ 2 * primeSum P R (cosCut L (2 * π * (Cvs.Finite.SymmetricModeSet.mode N i : ℝ) / L)) := by
    simp only [(Cvs.Finite.SymmetricModeSet.mode_injective N).eq_iff, mul_ite, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true, pow_two]
  have hd_bound : |∑ i, ξ i ^ 2 *
      primeSum P R (cosCut L (2 * π * (Cvs.Finite.SymmetricModeSet.mode N i : ℝ) / L))|
      ≤ primeDiagonalBudget P R * ∑ i, ξ i ^ 2 := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro i _
    rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
    have h := mul_le_mul_of_nonneg_left
      (abs_prime_cos_le P R L (2 * π * (Cvs.Finite.SymmetricModeSet.mode N i : ℝ) / L)) (sq_nonneg (ξ i))
    exact h.trans_eq (by ring)
  simp_rw [kPrime_eq hL, mul_sub, Finset.sum_sub_distrib]
  rw [hd, hpair]
  have ht : |(∑ i, ξ i ^ 2 * primeSum P R (cosCut L (2 * π * (Cvs.Finite.SymmetricModeSet.mode N i : ℝ) / L)))
      - primePowerSideTruncated P R (selfConvolution f) / L|
      ≤ |∑ i, ξ i ^ 2 * primeSum P R (cosCut L (2 * π * (Cvs.Finite.SymmetricModeSet.mode N i : ℝ) / L))|
        + |primePowerSideTruncated P R (selfConvolution f) / L| := by
    simpa only [sub_eq_add_neg, abs_neg] using abs_add_le
      (∑ i, ξ i ^ 2 * primeSum P R (cosCut L (2 * π * (Cvs.Finite.SymmetricModeSet.mode N i : ℝ) / L)))
      (- (primePowerSideTruncated P R (selfConvolution f) / L))
  have h := ht.trans (add_le_add hd_bound hshift)
  exact h.trans_eq (by unfold primeBudget; ring)

/-- The bound for the full boundary kernel has only fixed window and prime-cutoff parameters. -/
def kernelBudget (P R : ℕ) (L : ℝ) : ℝ := archBudget L + primeBudget P R

theorem kernelBudget_nonneg {L : ℝ} (hL : 0 < L) (P R : ℕ) :
    0 ≤ kernelBudget P R L := add_nonneg (archBudget_nonneg hL) (primeBudget_nonneg P R)

/-- The actual full even boundary kernel, including zero, pole, and finite primes, is bounded
uniformly in the mode order. -/
theorem idx_full_kernel_bound {L : ℝ} (hL : 0 < L) (P R N : ℕ) (ξ : Cvs.Finite.SymmetricModeSet.Idx N → ℝ)
    (heven : ∀ i, ξ (Cvs.Finite.SymmetricModeSet.negI N i) = ξ i) :
    |∑ i, ∑ j, ξ i * ξ j *
      (Cvs.Finite.WindowMatrixSymbolKernel.kK P R L (2 * π * (Cvs.Finite.SymmetricModeSet.mode N i : ℝ) / L)
        (2 * π * (Cvs.Finite.SymmetricModeSet.mode N j : ℝ) / L) / L)|
      ≤ kernelBudget P R L * ∑ i, ξ i ^ 2 := by
  simp only [Cvs.Finite.WindowMatrixSymbolKernel.kK, add_div, mul_add, Finset.sum_add_distrib]
  have h := (abs_add_le _ _).trans (add_le_add
    (idx_arch_kernel_bound hL N ξ heven) (idx_prime_kernel_bound hL P R N ξ heven))
  exact h.trans_eq (by unfold kernelBudget; ring)

/-- The actual normalized full boundary matrix on the symmetric mode set. -/
def boundaryMatrix (P R : ℕ) (L : ℝ) (N : ℕ) : Matrix (Cvs.Finite.SymmetricModeSet.Idx N) (Cvs.Finite.SymmetricModeSet.Idx N) ℝ :=
  fun i j => Cvs.Finite.WindowMatrixSymbolKernel.kK P R L (2 * π * (Cvs.Finite.SymmetricModeSet.mode N i : ℝ) / L)
    (2 * π * (Cvs.Finite.SymmetricModeSet.mode N j : ℝ) / L) / L

theorem boundaryMatrix_symm {L : ℝ} (hL : 0 < L) (P R N : ℕ)
    (i j : Cvs.Finite.SymmetricModeSet.Idx N) : boundaryMatrix P R L N i j = boundaryMatrix P R L N j i := by
  have h := Cvs.Finite.TruncationQuadraticForm.M_symm hL P R (Cvs.Finite.SymmetricModeSet.mode_injective N) i j
  rw [Cvs.Finite.WindowMatrixSymbolKernel.M_apply_kernel hL P R (Cvs.Finite.SymmetricModeSet.mode_injective N),
    Cvs.Finite.WindowMatrixSymbolKernel.M_apply_kernel hL P R (Cvs.Finite.SymmetricModeSet.mode_injective N)] at h
  by_cases hij : i = j
  · subst j
    rfl
  · simp only [if_neg hij, if_neg (Ne.symm hij), zero_add, one_div_mul_eq_div] at h
    exact h

/-- Polarization turns the actual quadratic bound into a bilinear bound on the even subspace. -/
theorem boundary_bilinear_bound {L : ℝ} (hL : 0 < L) (P R N : ℕ)
    (ξ η : Cvs.Finite.SymmetricModeSet.Idx N → ℝ)
    (hξ : ∀ i, ξ (Cvs.Finite.SymmetricModeSet.negI N i) = ξ i)
    (hη : ∀ i, η (Cvs.Finite.SymmetricModeSet.negI N i) = η i) :
    |ξ ⬝ᵥ (boundaryMatrix P R L N *ᵥ η)|
      ≤ kernelBudget P R L / 2 * ((∑ i, ξ i ^ 2) + ∑ i, η i ^ 2) := by
  let A := boundaryMatrix P R L N
  have hp := idx_full_kernel_bound hL P R N (ξ + η) (by
    intro i; simp only [Pi.add_apply, hξ, hη])
  have hm := idx_full_kernel_bound hL P R N (ξ - η) (by
    intro i; simp only [Pi.sub_apply, hξ, hη])
  have hquad : ∀ v : Cvs.Finite.SymmetricModeSet.Idx N → ℝ,
      (∑ i, ∑ j, v i * v j * A i j) = v ⬝ᵥ (A *ᵥ v) := by
    intro v
    change (∑ i, ∑ j, v i * v j * A i j) = ∑ i, v i * ∑ j, A i j * v j
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  change |∑ i, ∑ j, (ξ + η) i * (ξ + η) j * A i j| ≤ _ at hp
  change |∑ i, ∑ j, (ξ - η) i * (ξ - η) j * A i j| ≤ _ at hm
  rw [hquad] at hp hm
  have hcomm := Cvs.Upstream.SymmetricMatrixBottom.dotProduct_mulVec_comm (boundaryMatrix_symm hL P R N) ξ η
  have hpolar : (ξ + η) ⬝ᵥ (A *ᵥ (ξ + η)) - (ξ - η) ⬝ᵥ (A *ᵥ (ξ - η))
      = 4 * (ξ ⬝ᵥ (A *ᵥ η)) := by
    simp only [Matrix.mulVec_add, Matrix.mulVec_sub, add_dotProduct, sub_dotProduct,
      dotProduct_add, dotProduct_sub]
    change _ = 4 * (ξ ⬝ᵥ (boundaryMatrix P R L N *ᵥ η))
    rw [hcomm]
    ring
  have hn : (∑ i, (ξ + η) i ^ 2) + (∑ i, (ξ - η) i ^ 2)
      = 2 * ((∑ i, ξ i ^ 2) + ∑ i, η i ^ 2) := by
    simp only [Pi.add_apply, Pi.sub_apply, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have ht : |(ξ + η) ⬝ᵥ (A *ᵥ (ξ + η)) - (ξ - η) ⬝ᵥ (A *ᵥ (ξ - η))|
      ≤ |(ξ + η) ⬝ᵥ (A *ᵥ (ξ + η))| + |(ξ - η) ⬝ᵥ (A *ᵥ (ξ - η))| := by
    simpa only [sub_eq_add_neg, abs_neg] using abs_add_le
      ((ξ + η) ⬝ᵥ (A *ᵥ (ξ + η))) (- ((ξ - η) ⬝ᵥ (A *ᵥ (ξ - η))))
  rw [hpolar, abs_mul] at ht
  rw [show |(4 : ℝ)| = 4 by norm_num] at ht
  have h := ht.trans (add_le_add hp hm)
  rw [← mul_add, hn] at h
  change |ξ ⬝ᵥ (A *ᵥ η)| ≤ _
  nlinarith

/-- A balanced bilinear bound for the actual full kernel, allowing arbitrarily small tail norms. -/
theorem boundary_bilinear_balanced_bound {L : ℝ} (hL : 0 < L) (P R N : ℕ)
    (ξ η : Cvs.Finite.SymmetricModeSet.Idx N → ℝ)
    (hξ : ∀ i, ξ (Cvs.Finite.SymmetricModeSet.negI N i) = ξ i)
    (hη : ∀ i, η (Cvs.Finite.SymmetricModeSet.negI N i) = η i) {s : ℝ} (hs : 0 < s) :
    |ξ ⬝ᵥ (boundaryMatrix P R L N *ᵥ η)|
      ≤ kernelBudget P R L / 2 *
        (s ^ 2 * (∑ i, ξ i ^ 2) + (∑ i, η i ^ 2) / s ^ 2) := by
  have h := boundary_bilinear_bound hL P R N
    (fun i => s * ξ i) (fun i => η i / s)
    (by intro i; rw [hξ]) (by intro i; rw [hη])
  have he : (fun i => s * ξ i) ⬝ᵥ (boundaryMatrix P R L N *ᵥ (fun i => η i / s))
      = ξ ⬝ᵥ (boundaryMatrix P R L N *ᵥ η) := by
    change (∑ i, (s * ξ i) * ∑ j, boundaryMatrix P R L N i j * (η j / s))
      = ∑ i, ξ i * ∑ j, boundaryMatrix P R L N i j * η j
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    field_simp
  rw [he] at h
  have hnξ : (∑ i, (s * ξ i) ^ 2) = s ^ 2 * ∑ i, ξ i ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hnη : (∑ i, (η i / s) ^ 2) = (∑ i, η i ^ 2) / s ^ 2 := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by ring
  simpa only [hnξ, hnη] using h

end Prime

end Cvs.WeilForm.EvenBoundaryKernelBound
