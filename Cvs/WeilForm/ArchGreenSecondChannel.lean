import Mathlib
import Cvs.Approximant.BoundaryVarianceInterval
import Cvs.Approximant.ConnesErrorColumn
import Cvs.Approximant.ResidualSymbolVariance
import Cvs.Finite.CosineModeOverlap
import Cvs.Finite.DiagonalLevySymbol
import Cvs.Finite.LevyChannelDoubleSum
import Cvs.Finite.LevyExpMoments
import Cvs.Finite.LevyKernelIncrement
import Cvs.Finite.ModeSumPairValues
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationQuadraticForm
import Cvs.Finite.WindowMatrixSymbolKernel
import Cvs.Route.GroundRouteJointGap
import Cvs.Route.JointGapFromResidual
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.EvenLadderUniformBound
import Cvs.WeilForm.Archimedean.LevyTermsSum
import Cvs.WeilForm.Archimedean.OffDiagonalLevyDividedDiff
import Cvs.WeilForm.Archimedean.OffWindowDefect
import Cvs.WeilForm.Archimedean.SymbolImaginaryHalf
import Cvs.WeilForm.Archimedean.TruncationBelowSymbol
import Cvs.WeilForm.EvenBoundaryKernelBound
import Cvs.WeilForm.GreenRemovesFirstArchChannel
import Cvs.WeilForm.TruncatedArchChannelSum
import Cvs.Zeta.Digamma
import Cvs.Zeta.DigammaEulerLimitInstance
import Cvs.Zeta.DigammaLimitDischarged

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The finite Arch plus Green kernel starts at the second channel

The actual exponential Green pairing cancels the first boundary atom.
The remaining even boundary is a positive ladder with a smaller zero-row budget.
-/

noncomputable section

open Real Set MeasureTheory Matrix Finset

namespace Cvs.WeilForm.ArchGreenSecondChannel
open Cvs.ZeroCounting

open Cvs.Finite.WindowMatrixSymbolKernel (bk uu vv)
open Cvs.Finite.DiagonalLevySymbol (tailFactor)

/-- The signed rank-two boundary atom of one archimedean channel. -/
def atom (L : ℝ) (k : ℕ) (A B : ℝ) : ℝ :=
  2*(1-tailFactor L k)*(uu (bk k) A*uu (bk k) B-vv (bk k) A*vv (bk k) B)

/-- The actual first-channel exponential pairing of the cut cosine kernel. -/
def greenEntry (L : ℝ) (m n : ℤ) : ℝ :=
  ∫ v in Ioi (0:ℝ), exp (-(bk 0*v))*Cvs.Finite.LevyKernelIncrement.Kc L m n v

/-- The actual normalized archimedean pairing plus its Green correction. -/
def archGreenEntry (L : ℝ) (m n : ℤ) : ℝ :=
  Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0*Cvs.Finite.CosineModeOverlap.K L m n 0/2+Cvs.Finite.LevyChannelDoubleSum.levyPair L m n/2+greenEntry L m n

/-- The boundary ladder after removal of the first channel. -/
def boundaryTail (L A B : ℝ) : ℝ := ∑' k : ℕ, atom L (k+1) A B

theorem summable_atom {L : ℝ} (hL : 0<L) (A B : ℝ) : Summable (fun k => atom L k A B) :=
  Cvs.Finite.WindowMatrixSymbolKernel.summable_ladder_pair hL A B

theorem full_boundary_eq {L : ℝ} (hL : 0<L) (A B : ℝ) :
    (∑' k : ℕ, atom L k A B) = atom L 0 A B+boundaryTail L A B := by
  simpa only [boundaryTail, Nat.add_comm] using (summable_atom hL A B).tsum_eq_zero_add

private theorem frequency_ne {L : ℝ} (hL : 0<L) {m n : ℤ} (hmn : m≠n) :
    2*π*m/L≠2*π*n/L := by
  intro h
  have he : (m : ℝ)=(n : ℝ) := by
    have hl := hL.ne'
    field_simp at h
    nlinarith [Real.pi_pos]
  exact hmn (Int.cast_inj.mp he)

/-- Every actual bracket moment splits into its diagonal deficit and boundary atom. -/
theorem moment_eq_deficit_atom {L : ℝ} (hL : 0<L) (m n : ℤ) (k : ℕ) :
    Cvs.Finite.LevyExpMoments.moment L m n k/2 =
      (if m=n then Cvs.Zeta.digammaDeficit (2*π*m/L) k else 0)+
        atom L k (2*π*m/L) (2*π*n/L)/L := by
  by_cases hmn : m=n
  · subst n
    rw [if_pos rfl, Cvs.Finite.DiagonalLevySymbol.moment_diag_split hL, Cvs.Finite.WindowMatrixSymbolKernel.cutTerm_eq]
    unfold atom
    ring
  · rw [if_neg hmn, zero_add, Cvs.WeilForm.Archimedean.OffDiagonalLevyDividedDiff.moment_off_split hL hmn,
      Cvs.Finite.WindowMatrixSymbolKernel.imTerm_eq, Cvs.Finite.WindowMatrixSymbolKernel.imTerm_eq]
    have hd := Cvs.Finite.WindowMatrixSymbolKernel.dd_hh (Cvs.Finite.WindowMatrixSymbolKernel.bk_pos k) (frequency_ne hL hmn)
    have hden : π*((n : ℝ)-m)≠0 := by
      exact mul_ne_zero Real.pi_ne_zero (sub_ne_zero.mpr (by exact_mod_cast Ne.symm hmn))
    have hfreq := sub_ne_zero.mpr (frequency_ne hL hmn)
    have hnm : (m : ℝ)-n≠0 := sub_ne_zero.mpr (by exact_mod_cast hmn)
    have hmn' : (n : ℝ)-m≠0 := sub_ne_zero.mpr (by exact_mod_cast Ne.symm hmn)
    unfold atom
    field_simp [hL.ne', Real.pi_ne_zero, hnm, hmn'] at hd ⊢
    linear_combination -(1-tailFactor L k)*hd

/-- The exponential integral is genuinely integrable and cancels the first bracket moment. -/
theorem greenEntry_eq_first_moment {L : ℝ} (hL : 0<L) (m n : ℤ) :
    greenEntry L m n = 2*Cvs.Finite.CosineModeOverlap.K L m n 0-Cvs.Finite.LevyExpMoments.moment L m n 0/2 := by
  let g := fun v => exp (-(bk 0*v))*(Cvs.Finite.CosineModeOverlap.K L m n 0-Cvs.Finite.LevyKernelIncrement.Kc L m n v)
  have hi1 : IntegrableOn (fun v => exp (-(bk 0*v))*Cvs.Finite.CosineModeOverlap.K L m n 0) (Ioi 0) volume := by
    change Integrable _ (volume.restrict (Ioi (0:ℝ)))
    simpa only [neg_mul] using
      (integrableOn_exp_mul_Ioi (by nlinarith [Cvs.Finite.WindowMatrixSymbolKernel.bk_pos 0] : -bk 0<0) 0).mul_const (Cvs.Finite.CosineModeOverlap.K L m n 0)
  have hi2 : IntegrableOn (fun v => exp (-(bk 0*v))*Cvs.Finite.LevyKernelIncrement.Kc L m n v) (Ioi 0) volume := by
    simpa only [neg_mul] using Cvs.Finite.ModeSumPairValues.integrableOn_exp_mul_Kc hL m n (-bk 0)
  have hm : Cvs.Finite.LevyExpMoments.moment L m n 0=2*∫ v in Ioi (0:ℝ), g v := by
    unfold Cvs.Finite.LevyExpMoments.moment
    have hs := integral_comp_mul_left_Ioi'
      (fun u => exp (-((1/4+(0:ℕ):ℝ)*u))*(Cvs.Finite.CosineModeOverlap.K L m n 0-Cvs.Finite.LevyKernelIncrement.Kc L m n (u/2)))
      0 (show (0:ℝ)<2 by norm_num)
    rw [mul_zero, smul_eq_mul] at hs
    rw [← hs]
    congr 1
    apply setIntegral_congr_fun measurableSet_Ioi
    intro v _
    simp only [g, bk, Nat.cast_zero, mul_zero, zero_add]
    rw [show 2*v/2=v by ring]
    congr 2
    ring
  have hs : (∫ v in Ioi (0:ℝ), g v)=
      (1/bk 0)*Cvs.Finite.CosineModeOverlap.K L m n 0-greenEntry L m n := by
    have he : g=(fun v => exp (-(bk 0*v))*Cvs.Finite.CosineModeOverlap.K L m n 0)-
      (fun v => exp (-(bk 0*v))*Cvs.Finite.LevyKernelIncrement.Kc L m n v) := by funext v; dsimp [g]; ring
    rw [he]
    simp only [Pi.sub_apply]
    rw [integral_sub hi1 hi2, integral_mul_const,
      Cvs.WeilForm.TruncatedArchChannelSum.integral_exp_neg_scaled (Cvs.Finite.WindowMatrixSymbolKernel.bk_pos 0)]
    rfl
  rw [hs] at hm
  norm_num [bk] at hm
  linarith

/-- The exact Green matrix entry is its first-pole diagonal minus its boundary atom. -/
theorem greenEntry_eq {L : ℝ} (hL : 0<L) (m n : ℤ) :
    greenEntry L m n=(if m=n then Cvs.WeilForm.GreenRemovesFirstArchChannel.greenMultiplier (2*π*m/L) else 0)-
      atom L 0 (2*π*m/L) (2*π*n/L)/L := by
  rw [greenEntry_eq_first_moment hL, moment_eq_deficit_atom hL]
  by_cases hmn : m=n
  · subst n
    rw [if_pos rfl, if_pos rfl]
    have hd := Cvs.WeilForm.Archimedean.TruncationBelowSymbol.gap_eq_deficit (2*π*m/L) 0
    norm_num [Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx] at hd
    rw [Cvs.Finite.CosineModeOverlap.K]
    simp only [mul_zero]
    unfold Cvs.WeilForm.GreenRemovesFirstArchChannel.greenMultiplier
    rw [← hd]
    norm_num
    ring
  · rw [if_neg hmn, if_neg hmn, Cvs.Finite.CosineModeOverlap.K, if_neg hmn]
    simp only [mul_zero, sin_zero, sub_self, zero_div, zero_sub, zero_add]

/-- The actual arch boundary before Green addition is the full ladder. -/
theorem archEntry_eq {L : ℝ} (hL : 0<L) (m n : ℤ) :
    Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0*Cvs.Finite.CosineModeOverlap.K L m n 0/2+Cvs.Finite.LevyChannelDoubleSum.levyPair L m n/2=
      (if m=n then Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol (2*π*m/L) else 0)+
        (∑' k : ℕ, atom L k (2*π*m/L) (2*π*n/L))/L := by
  rw [Cvs.Finite.LevyExpMoments.levyPair_eq_tsum hL]
  rw [← tsum_div_const, tsum_congr (moment_eq_deficit_atom hL m n)]
  have hd : Summable (fun k => if m=n then Cvs.Zeta.digammaDeficit (2*π*m/L) k else 0) := by
    split_ifs
    · exact Cvs.Transform.summable_digammaDeficit _
    · exact summable_zero
  rw [hd.tsum_add ((summable_atom hL _ _).div_const L), tsum_div_const]
  by_cases hmn : m=n
  · subst n
    simp only [↓reduceIte]
    rw [Cvs.WeilForm.Archimedean.LevyTermsSum.tsum_digammaDeficit]
    unfold Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol Cvs.Finite.CosineModeOverlap.K
    simp only [↓reduceIte, mul_zero, zero_div, Real.cos_zero, mul_one]
    ring
  · simp only [if_neg hmn, tsum_zero]
    rw [Cvs.Finite.CosineModeOverlap.K, if_neg hmn]
    simp only [mul_zero, sin_zero, sub_self, zero_div, mul_zero, zero_div, zero_add]

/-- The actual finite Arch plus Green pairing has only the shifted symbol and channels k ≥ 1. -/
theorem archGreenEntry_eq {L : ℝ} (hL : 0<L) (m n : ℤ) :
    archGreenEntry L m n=(if m=n then Cvs.WeilForm.GreenRemovesFirstArchChannel.shiftedArchSymbol (2*π*m/L) else 0)+
      boundaryTail L (2*π*m/L) (2*π*n/L)/L := by
  unfold archGreenEntry
  rw [archEntry_eq hL, greenEntry_eq hL, full_boundary_eq hL]
  by_cases hmn : m=n
  · rw [if_pos hmn, if_pos hmn, if_pos hmn]
    unfold Cvs.WeilForm.GreenRemovesFirstArchChannel.shiftedArchSymbol
    ring
  · rw [if_neg hmn, if_neg hmn, if_neg hmn]
    ring

/-- The actual CvS entry loses its pole and prime terms before Green is added. -/
theorem M_add_green_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {L : ℝ} (hL : 0<L) (P R : ℕ) {mode : ι → ℤ}
    (hinj : Function.Injective mode) (i j : ι) :
    Cvs.Finite.TruncationQuadraticForm.M P R L mode i j-Cvs.Finite.ModeSumPairValues.polePair L (mode i) (mode j)+
      Cvs.Finite.ModeSumPairValues.primePair P R L (mode i) (mode j)/2+greenEntry L (mode i) (mode j)=
      archGreenEntry L (mode i) (mode j) := by
  rw [Cvs.Finite.TruncationQuadraticForm.M_apply hL P R hinj]
  unfold Cvs.Finite.ModeSumPairValues.pairQ archGreenEntry
  ring

/-- The actual continuous dilation mean in normalized finite log-window coordinates. -/
def meanEntry (L : ℝ) (m n : ℤ) : ℝ :=
  ∫ v in Ioi (0:ℝ), exp (v/2)*Cvs.Finite.LevyKernelIncrement.Kc L m n v

theorem meanEntry_eq {L : ℝ} (hL : 0<L) (m n : ℤ) :
    meanEntry L m n=Cvs.Finite.ModeSumPairValues.polePair L m n-greenEntry L m n := by
  have hm := Cvs.Finite.ModeSumPairValues.integrableOn_exp_mul_Kc hL m n (1/2)
  have hg := Cvs.Finite.ModeSumPairValues.integrableOn_exp_mul_Kc hL m n (-(1/2))
  unfold meanEntry Cvs.Finite.ModeSumPairValues.polePair greenEntry
  have he : (fun v => (exp (-(v/2))+exp (v/2))*Cvs.Finite.LevyKernelIncrement.Kc L m n v)=
      (fun v => exp (-(1/2)*v)*Cvs.Finite.LevyKernelIncrement.Kc L m n v)+
        (fun v => exp ((1/2)*v)*Cvs.Finite.LevyKernelIncrement.Kc L m n v) := by
    funext v
    simp only [Pi.add_apply, show v/2=(1/2)*v by ring]
    ring
  rw [he]
  change (∫ v in Ioi (0:ℝ), exp (v/2)*Cvs.Finite.LevyKernelIncrement.Kc L m n v)=
    (∫ v in Ioi (0:ℝ), exp (-(1/2)*v)*Cvs.Finite.LevyKernelIncrement.Kc L m n v+
      exp ((1/2)*v)*Cvs.Finite.LevyKernelIncrement.Kc L m n v)-
        ∫ v in Ioi (0:ℝ), exp (-(bk 0*v))*Cvs.Finite.LevyKernelIncrement.Kc L m n v
  rw [integral_add hg hm]
  norm_num [bk]
  simp only [show ∀ v : ℝ, (1/2)*v=v/2 from fun v => by ring]

/-- The actual finite prime term minus its continuous dilation mean. -/
def discrepancyEntry (P R : ℕ) (L : ℝ) (m n : ℤ) : ℝ :=
  Cvs.Finite.ModeSumPairValues.primePair P R L m n/2-meanEntry L m n

/-- The actual full matrix separates shifted arch plus its positive even tail from signed discrepancy. -/
theorem M_apply_shifted {ι : Type*} [Fintype ι] [DecidableEq ι]
    {L : ℝ} (hL : 0<L) (P R : ℕ) {mode : ι → ℤ}
    (hinj : Function.Injective mode) (i j : ι) :
    Cvs.Finite.TruncationQuadraticForm.M P R L mode i j=
      (if i=j then Cvs.WeilForm.GreenRemovesFirstArchChannel.shiftedArchSymbol (2*π*mode i/L) else 0)+
        boundaryTail L (2*π*mode i/L) (2*π*mode j/L)/L-
          discrepancyEntry P R L (mode i) (mode j) := by
  have h := M_add_green_eq hL P R hinj i j
  rw [archGreenEntry_eq hL] at h
  unfold discrepancyEntry
  rw [meanEntry_eq hL]
  have hi : (mode i=mode j)↔i=j := hinj.eq_iff
  simp only [hi] at h
  linarith

/-- The remaining positive part of the boundary on reflection-even coefficients. -/
def positiveTail (L A B : ℝ) : ℝ :=
  ∑' k : ℕ, Cvs.WeilForm.EvenBoundaryKernelBound.weight L (k+1)*uu (bk (k+1)) A*uu (bk (k+1)) B

theorem positiveTail_split {L : ℝ} (hL : 0<L) (A B : ℝ) :
    Cvs.WeilForm.Archimedean.EvenLadderUniformBound.ladder L A B=Cvs.WeilForm.EvenBoundaryKernelBound.weight L 0*uu (bk 0) A*uu (bk 0) B+positiveTail L A B := by
  simpa only [Cvs.WeilForm.Archimedean.EvenLadderUniformBound.ladder, Cvs.WeilForm.EvenBoundaryKernelBound.weight, positiveTail, Nat.add_comm] using
    (Cvs.WeilForm.EvenBoundaryKernelBound.summable_ladder_uu hL A B).tsum_eq_zero_add

/-- The new normalized zero-row budget starts at the second channel. -/
def zeroTailBudget (L : ℝ) : ℝ := positiveTail L 0 0/L

/-- Removal of the first boundary is an exact reduction, including the zero mode. -/
theorem zeroTailBudget_eq {L : ℝ} (hL : 0<L) :
    zeroTailBudget L=Cvs.WeilForm.EvenBoundaryKernelBound.zeroBudget L-8*(1-tailFactor L 0)/L := by
  have h := positiveTail_split hL 0 0
  norm_num [bk, uu, Cvs.WeilForm.EvenBoundaryKernelBound.weight] at h
  unfold zeroTailBudget Cvs.WeilForm.EvenBoundaryKernelBound.zeroBudget
  rw [h]
  ring

theorem zeroTailBudget_nonneg {L : ℝ} (hL : 0<L) : 0≤zeroTailBudget L := by
  unfold zeroTailBudget positiveTail
  apply div_nonneg (tsum_nonneg fun k => ?_) hL.le
  have hw := Cvs.WeilForm.EvenBoundaryKernelBound.weight_nonneg hL (k+1)
  have hb := Cvs.Finite.WindowMatrixSymbolKernel.bk_pos (k+1)
  have hu : 0≤uu (bk (k+1)) 0 := by unfold uu; positivity
  positivity

/-- A cutoff-independent signed-even budget without the pole or first boundary atom. -/
def tailBudget (L : ℝ) : ℝ := 2*zeroTailBudget L+2*(4+π)

theorem tailBudget_nonneg {L : ℝ} (hL : 0<L) : 0≤tailBudget L := by
  unfold tailBudget
  have h := zeroTailBudget_nonneg hL
  positivity

theorem tailBudget_eq {L : ℝ} (hL : 0<L) :
    tailBudget L=Cvs.WeilForm.EvenBoundaryKernelBound.ladderBudget L-16*(1-tailFactor L 0)/L := by
  rw [tailBudget, zeroTailBudget_eq hL, Cvs.WeilForm.EvenBoundaryKernelBound.ladderBudget]
  ring

section Finite

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The actual signed tail quadratic is a convergent rank-two square sum. -/
theorem boundaryTail_quad {L : ℝ} (hL : 0<L) (ω : ι → ℝ) (ξ : ι → ℝ) :
    (∑ i, ∑ j, ξ i*ξ j*boundaryTail L (ω i) (ω j))=
      ∑' k : ℕ, Cvs.WeilForm.EvenBoundaryKernelBound.weight L (k+1)*
        ((∑ i, ξ i*uu (bk (k+1)) (ω i))^2-
          (∑ i, ξ i*vv (bk (k+1)) (ω i))^2) := by
  have hs : ∀ i j, Summable (fun k : ℕ => ξ i*ξ j*atom L (k+1) (ω i) (ω j)) :=
    fun i j => ((summable_atom hL (ω i) (ω j)).comp_injective
      (add_left_injective 1)).mul_left _
  unfold boundaryTail
  simp_rw [← tsum_mul_left]
  have h2 : ∀ i, (∑ j, ∑' k : ℕ, ξ i*ξ j*atom L (k+1) (ω i) (ω j))=
      ∑' k : ℕ, ∑ j, ξ i*ξ j*atom L (k+1) (ω i) (ω j) :=
    fun i => (Summable.tsum_finsetSum fun j _ => hs i j).symm
  simp only [h2]
  rw [← Summable.tsum_finsetSum fun i _ => summable_sum fun j _ => hs i j]
  exact tsum_congr fun k => Cvs.Finite.WindowMatrixSymbolKernel.rank2_quad _ _ _ _

/-- Odd boundary coordinates vanish on even data, leaving actual positive squares. -/
theorem boundaryTail_quad_even {L : ℝ} (hL : 0<L) (ω : ι → ℝ) (ξ : ι → ℝ)
    (hv : ∀ b : ℝ, 0<b → ∑ i, ξ i*vv b (ω i)=0) :
    (∑ i, ∑ j, ξ i*ξ j*boundaryTail L (ω i) (ω j))=
      ∑' k : ℕ, Cvs.WeilForm.EvenBoundaryKernelBound.weight L (k+1)*(∑ i, ξ i*uu (bk (k+1)) (ω i))^2 := by
  rw [boundaryTail_quad hL]
  simp only [hv _ (Cvs.Finite.WindowMatrixSymbolKernel.bk_pos _), zero_pow (by norm_num : (2:ℕ)≠0), sub_zero]

theorem boundaryTail_quad_nonneg {L : ℝ} (hL : 0<L) (ω : ι → ℝ) (ξ : ι → ℝ)
    (hv : ∀ b : ℝ, 0<b → ∑ i, ξ i*vv b (ω i)=0) :
    0≤∑ i, ∑ j, ξ i*ξ j*boundaryTail L (ω i) (ω j) := by
  rw [boundaryTail_quad_even hL ω ξ hv]
  exact tsum_nonneg fun k => mul_nonneg (Cvs.WeilForm.EvenBoundaryKernelBound.weight_nonneg hL _) (sq_nonneg _)

/-- The normalized even tail, including the zero-mode coefficient. -/
def evenTailQuad (L : ℝ) (mode : ι → ℕ) (a : ℝ) (u : ι → ℝ) : ℝ :=
  (∑' k : ℕ, Cvs.WeilForm.EvenBoundaryKernelBound.weight L (k+1)*
    (a*uu (bk (k+1)) 0+2*∑ i, u i*uu (bk (k+1)) (2*π*mode i/L))^2)/L

theorem evenTailQuad_le {L : ℝ} (hL : 0<L) (mode : ι → ℕ)
    (hinj : Function.Injective mode) (hpos : ∀ i, 0 < mode i) (a : ℝ) (u : ι → ℝ) :
    evenTailQuad L mode a u≤tailBudget L*∑ i, Cvs.WeilForm.EvenBoundaryKernelBound.evenCoeff a u i^2 := by
  let S : ℕ → ℝ := fun k => ∑ i, u i*uu (bk k) (2*π*mode i/L)
  have hs0 := ((Cvs.WeilForm.EvenBoundaryKernelBound.summable_ladder_uu hL 0 0).comp_injective
    (add_left_injective 1)).mul_left (2*a^2)
  have hsp := ((Cvs.WeilForm.EvenBoundaryKernelBound.summable_ladder_square hL (fun i => 2*π*mode i/L) u).comp_injective
    (add_left_injective 1)).mul_left 8
  have hsq : Summable (fun k : ℕ => Cvs.WeilForm.EvenBoundaryKernelBound.weight L k*
      (a*uu (bk k) 0+2*S k)^2) := Cvs.WeilForm.EvenBoundaryKernelBound.summable_even_square hL mode a u
  have ht := (hsq.comp_injective (add_left_injective 1)).tsum_le_tsum
    (g := fun k : ℕ => 2*a^2*(Cvs.WeilForm.EvenBoundaryKernelBound.weight L (k+1)*uu (bk (k+1)) 0*uu (bk (k+1)) 0)+
      8*(Cvs.WeilForm.EvenBoundaryKernelBound.weight L (k+1)*S (k+1)^2)) (fun k => by
      change Cvs.WeilForm.EvenBoundaryKernelBound.weight L (k+1)*(a*uu (bk (k+1)) 0+2*S (k+1))^2≤_
      have hw := Cvs.WeilForm.EvenBoundaryKernelBound.weight_nonneg hL (k+1)
      have h := mul_le_mul_of_nonneg_left
        (show (a*uu (bk (k+1)) 0+2*S (k+1))^2≤
          2*a^2*uu (bk (k+1)) 0^2+8*S (k+1)^2 by
          nlinarith [sq_nonneg (a*uu (bk (k+1)) 0-2*S (k+1))]) hw
      nlinarith) (hs0.add hsp)
  dsimp only [Function.comp_def, S] at hs0 hsp ht
  rw [hs0.tsum_add hsp, tsum_mul_left, tsum_mul_left] at ht
  have hpq : (∑' k : ℕ, Cvs.WeilForm.EvenBoundaryKernelBound.weight L k*S k^2)/L=
      u ⬝ᵥ (Cvs.WeilForm.Archimedean.EvenLadderUniformBound.positiveMatrix L mode *ᵥ u) := by
    rw [← Cvs.WeilForm.EvenBoundaryKernelBound.ladder_quad hL]
    simp only [Cvs.WeilForm.Archimedean.EvenLadderUniformBound.positiveMatrix, dotProduct, Matrix.mulVec, Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have htail : (∑' k : ℕ, Cvs.WeilForm.EvenBoundaryKernelBound.weight L (k+1)*S (k+1)^2)/L≤
      u ⬝ᵥ (Cvs.WeilForm.Archimedean.EvenLadderUniformBound.positiveMatrix L mode *ᵥ u) := by
    rw [← hpq, (Cvs.WeilForm.EvenBoundaryKernelBound.summable_ladder_square hL (fun i => 2*π*mode i/L) u).tsum_eq_zero_add]
    apply div_le_div_of_nonneg_right _ hL.le
    have hw := Cvs.WeilForm.EvenBoundaryKernelBound.weight_nonneg hL 0
    nlinarith [sq_nonneg (S 0)]
  have hdiv := div_le_div_of_nonneg_right ht hL.le
  change evenTailQuad L mode a u≤_ at hdiv
  have hz := zeroTailBudget_nonneg hL
  have hn : 0≤∑ i, u i^2 := sum_nonneg fun i _ => sq_nonneg _
  have hp := Cvs.WeilForm.Archimedean.EvenLadderUniformBound.positiveMatrix_quad_le hL mode hinj hpos u
  have he : evenTailQuad L mode a u≤2*a^2*zeroTailBudget L+
      8*(u ⬝ᵥ (Cvs.WeilForm.Archimedean.EvenLadderUniformBound.positiveMatrix L mode *ᵥ u)) := by
    unfold zeroTailBudget positiveTail
    rw [add_div, mul_div_assoc, mul_div_assoc] at hdiv
    exact hdiv.trans (by gcongr)
  rw [Cvs.WeilForm.EvenBoundaryKernelBound.even_coeff_sq]
  unfold tailBudget
  nlinarith [sq_nonneg a, Real.pi_pos]

end Finite

section Concrete

open Cvs.Finite.SymmetricModeSet (Idx mode negI)

/-- The actual retained signed-mode matrix of the remaining archimedean boundary. -/
def tailMatrix (L : ℝ) (N : ℕ) : Matrix (Idx N) (Idx N) ℝ :=
  fun i j => boundaryTail L (2*π*(mode N i : ℝ)/L) (2*π*(mode N j : ℝ)/L)/L

theorem boundaryTail_symm (L A B : ℝ) : boundaryTail L A B=boundaryTail L B A := by
  unfold boundaryTail
  apply tsum_congr
  intro k
  unfold atom
  ring

theorem boundaryTail_neg_neg (L A B : ℝ) : boundaryTail L (-A) (-B)=boundaryTail L A B := by
  unfold boundaryTail
  apply tsum_congr
  intro k
  simp only [atom, Cvs.WeilForm.EvenBoundaryKernelBound.uu_neg, Cvs.WeilForm.EvenBoundaryKernelBound.vv_neg]
  ring

theorem tailMatrix_symm (L : ℝ) (N : ℕ) (i j : Idx N) :
    tailMatrix L N i j=tailMatrix L N j i := by
  exact congrArg (fun z => z/L) (boundaryTail_symm _ _ _)

theorem tailMatrix_neg_neg (L : ℝ) (N : ℕ) (i j : Idx N) :
    tailMatrix L N (negI N i) (negI N j)=tailMatrix L N i j := by
  simp only [tailMatrix, Cvs.Finite.SymmetricModeSet.mode_negI, Int.cast_neg]
  rw [show 2*π*(-(mode N i : ℝ))/L=-(2*π*(mode N i : ℝ)/L) by ring,
    show 2*π*(-(mode N j : ℝ))/L=-(2*π*(mode N j : ℝ)/L) by ring,
    boundaryTail_neg_neg]

theorem tail_column_even (L : ℝ) (N : ℕ) (ξ : Idx N → ℝ)
    (hξ : ∀ i, ξ (negI N i)=ξ i) (i : Idx N) :
    (tailMatrix L N *ᵥ ξ) (negI N i)=(tailMatrix L N *ᵥ ξ) i :=
  Cvs.Route.GroundRouteJointGap.mulVec_even (Cvs.Finite.SymmetricModeSet.negI_involutive N) (tailMatrix_neg_neg L N) hξ i

/-- Both copies of every signed cosine mode are retained in the tail quadratic. -/
theorem tailMatrix_quad_eq {L : ℝ} (hL : 0<L) (N : ℕ) (ξ : Idx N → ℝ)
    (hξ : ∀ i, ξ (negI N i)=ξ i) :
    ξ ⬝ᵥ (tailMatrix L N *ᵥ ξ)=
      evenTailQuad L (Cvs.WeilForm.EvenBoundaryKernelBound.positiveMode N) (ξ none) (fun k => ξ (some (k,true))) := by
  have he : ξ ⬝ᵥ (tailMatrix L N *ᵥ ξ)=
      (∑ i, ∑ j, ξ i*ξ j*boundaryTail L
        (2*π*(mode N i : ℝ)/L) (2*π*(mode N j : ℝ)/L))/L := by
    simp only [dotProduct, Matrix.mulVec, tailMatrix, Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he, boundaryTail_quad_even hL _ _ (fun b _ => Cvs.WeilForm.EvenBoundaryKernelBound.idx_sum_vv L b N ξ hξ)]
  simp only [Cvs.WeilForm.EvenBoundaryKernelBound.idx_sum_uu L _ N ξ hξ]
  rfl

/-- The actual remaining even boundary has the cutoff-independent interval [0, tailBudget]. -/
theorem tailMatrix_quadratic_interval {L : ℝ} (hL : 0<L) (N : ℕ) (ξ : Idx N → ℝ)
    (hξ : ∀ i, ξ (negI N i)=ξ i) :
    0≤ξ ⬝ᵥ (tailMatrix L N *ᵥ ξ) ∧
      ξ ⬝ᵥ (tailMatrix L N *ᵥ ξ)≤tailBudget L*(ξ ⬝ᵥ ξ) := by
  rw [tailMatrix_quad_eq hL N ξ hξ]
  constructor
  · unfold evenTailQuad
    apply div_nonneg (tsum_nonneg fun k => ?_) hL.le
    exact mul_nonneg (Cvs.WeilForm.EvenBoundaryKernelBound.weight_nonneg hL _) (sq_nonneg _)
  · have h := evenTailQuad_le hL (Cvs.WeilForm.EvenBoundaryKernelBound.positiveMode N) (Cvs.WeilForm.EvenBoundaryKernelBound.positiveMode_injective N)
      (Cvs.WeilForm.EvenBoundaryKernelBound.positiveMode_pos N) (ξ none) (fun k => ξ (some (k,true)))
    simpa only [Cvs.WeilForm.EvenBoundaryKernelBound.even_coeff_sq, Cvs.WeilForm.EvenBoundaryKernelBound.idx_even_sq N ξ hξ, dotProduct, ← sq] using h

/-- The actual tail operator restricted to the even coefficient space. -/
def tailEven (L : ℝ) (N : ℕ) : Cvs.Route.GroundRouteJointGap.evenSub N →ₗ[ℝ] Cvs.Route.GroundRouteJointGap.evenSub N :=
  (Matrix.toEuclideanLin (tailMatrix L N)).restrict fun _ hv i => tail_column_even L N _ hv i

theorem ofLp_tailEven (L : ℝ) (N : ℕ) (f : Cvs.Route.GroundRouteJointGap.evenSub N) :
    WithLp.ofLp ((tailEven L N f : Cvs.Route.GroundRouteJointGap.evenSub N) : EuclideanSpace ℝ (Idx N))=
      tailMatrix L N *ᵥ WithLp.ofLp (f : EuclideanSpace ℝ (Idx N)) := rfl

theorem isSymmetric_tailEven (L : ℝ) (N : ℕ) : (tailEven L N).IsSymmetric :=
  LinearMap.IsSymmetric.restrict_invariant
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr (Matrix.IsHermitian.ext fun i j => by
      simp [tailMatrix_symm L N j i])) _

theorem tailEven_interval {L : ℝ} (hL : 0<L) (N : ℕ) (f : Cvs.Route.GroundRouteJointGap.evenSub N) :
    0 ≤ inner ℝ (tailEven L N f) f ∧ inner ℝ (tailEven L N f) f≤tailBudget L*‖f‖^2 := by
  rw [Cvs.Route.GroundRouteJointGap.norm_sq_evenSub, Cvs.Route.GroundRouteJointGap.inner_evenSub, ofLp_tailEven]
  rw [dotProduct_comm (tailMatrix L N *ᵥ _)]
  exact tailMatrix_quadratic_interval hL N _ f.property

private theorem norm_center_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (w v : E) (hv : ‖v‖=1) :
    ‖w-(inner ℝ w v) • v‖^2=‖w‖^2-(inner ℝ w v)^2 := by
  simp only [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, sq_abs, hv, mul_one,
    real_inner_smul_right]
  ring

/-- Centering the actual remaining boundary uses its positive interval rather than an absolute budget. -/
theorem tail_centered_sq_le {L : ℝ} (hL : 0<L) (N : ℕ) (v : Idx N → ℝ)
    (hve : ∀ i, v (negI N i)=v i) (hv : v ⬝ᵥ v=1) :
    let β := tailMatrix L N *ᵥ v
    Cvs.Approximant.ConnesErrorColumn.center β v ⬝ᵥ Cvs.Approximant.ConnesErrorColumn.center β v≤(tailBudget L-β ⬝ᵥ v)*(β ⬝ᵥ v) := by
  let v' : Cvs.Route.GroundRouteJointGap.evenSub N := ⟨WithLp.toLp 2 v, hve⟩
  let T : Cvs.Route.GroundRouteJointGap.evenSub N →L[ℝ] Cvs.Route.GroundRouteJointGap.evenSub N := (tailEven L N).toContinuousLinearMap
  let β := tailMatrix L N *ᵥ v
  have hvnorm : ‖v'‖=1 := by
    have hs : ‖v'‖^2=1 := by rw [Cvs.Route.GroundRouteJointGap.norm_sq_evenSub]; exact hv
    exact (pow_left_inj₀ (norm_nonneg _) zero_le_one two_ne_zero).mp (by simpa using hs)
  have hκ : inner ℝ (T v') v'=β ⬝ᵥ v := by
    change inner ℝ (tailEven L N v') v'= _
    rw [Cvs.Route.GroundRouteJointGap.inner_evenSub, ofLp_tailEven]
  have hβ : ‖T v'‖^2=β ⬝ᵥ β := by
    change ‖tailEven L N v'‖^2=_
    rw [Cvs.Route.GroundRouteJointGap.norm_sq_evenSub, ofLp_tailEven]
  have hc : ‖T v'-(inner ℝ (T v') v') • v'‖^2=β ⬝ᵥ β-(β ⬝ᵥ v)^2 := by
    rw [norm_center_sq _ _ hvnorm, hκ, hβ]
  have h := Cvs.Approximant.BoundaryVarianceInterval.centered_variance_le T (isSymmetric_tailEven L N) 0 (tailBudget L)
    (fun f => by
      rw [zero_mul]
      change 0 ≤ inner ℝ (tailEven L N f) f
      exact (tailEven_interval hL N f).1)
    (fun f => by
      change inner ℝ (tailEven L N f) f ≤ tailBudget L*‖f‖^2
      exact (tailEven_interval hL N f).2) v' hvnorm
  rw [hc, hκ, sub_zero] at h
  dsimp only
  rw [Cvs.Approximant.ResidualSymbolVariance.center_sq_unit β v hv]
  exact h

/-- The actual shifted arch symbol on the retained signed frequencies. -/
def shiftedCoefficients (L : ℝ) (N : ℕ) : Idx N → ℝ :=
  fun i => Cvs.WeilForm.GreenRemovesFirstArchChannel.shiftedArchSymbol (2*π*(mode N i : ℝ)/L)

/-- The actual signed prime-minus-continuous-mean matrix, with all finite gates retained. -/
def discrepancyMatrix (P R : ℕ) (L : ℝ) (N : ℕ) : Matrix (Idx N) (Idx N) ℝ :=
  fun i j => discrepancyEntry P R L (mode N i) (mode N j)

theorem matrix_eq_shifted {L : ℝ} (hL : 0<L) (P R N : ℕ) :
    Cvs.Finite.TruncationQuadraticForm.M P R L (mode N)=Matrix.diagonal (shiftedCoefficients L N)+
      tailMatrix L N-discrepancyMatrix P R L N := by
  ext i j
  rw [M_apply_shifted hL P R (Cvs.Finite.SymmetricModeSet.mode_injective N)]
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.diagonal_apply,
    shiftedCoefficients, tailMatrix, discrepancyMatrix]

/-- The actual residual retains shifted-symbol variance and signed covariance with the arithmetic discrepancy. -/
theorem residual_eq_shifted_variance {L : ℝ} (hL : 0<L) (P R N : ℕ)
    (v : Idx N → ℝ) (hv : v ⬝ᵥ v=1) :
    let d := shiftedCoefficients L N
    let β := tailMatrix L N *ᵥ v-discrepancyMatrix P R L N *ᵥ v
    Cvs.Route.JointGapFromResidual.residualSq P R L N v=Cvs.Approximant.ResidualSymbolVariance.symbolVariance d v+
      Cvs.Approximant.ConnesErrorColumn.center β v ⬝ᵥ Cvs.Approximant.ConnesErrorColumn.center β v+2*Cvs.Approximant.ResidualSymbolVariance.signedCovariance d v β := by
  dsimp only
  rw [Cvs.Approximant.ResidualSymbolVariance.center_sq_unit _ v hv]
  unfold Cvs.Route.JointGapFromResidual.residualSq
  dsimp only
  have hu : Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ v=Cvs.Approximant.ResidualSymbolVariance.diagonalColumn (shiftedCoefficients L N) v+
      (tailMatrix L N *ᵥ v-discrepancyMatrix P R L N *ᵥ v) := by
    rw [matrix_eq_shifted hL, Matrix.sub_mulVec, Matrix.add_mulVec]
    funext i
    simp only [Matrix.mulVec_diagonal, Cvs.Approximant.ResidualSymbolVariance.diagonalColumn, Pi.sub_apply, Pi.add_apply]
    ring
  have h := Cvs.Approximant.ResidualSymbolVariance.residual_diagonal_boundary _ _ _ _ hv hu
  calc
    _ = Cvs.Approximant.ResidualSymbolVariance.symbolVariance (shiftedCoefficients L N) v+
      (tailMatrix L N *ᵥ v-discrepancyMatrix P R L N *ᵥ v) ⬝ᵥ
        (tailMatrix L N *ᵥ v-discrepancyMatrix P R L N *ᵥ v)-
      ((tailMatrix L N *ᵥ v-discrepancyMatrix P R L N *ᵥ v) ⬝ᵥ v)^2+
      2*Cvs.Approximant.ResidualSymbolVariance.signedCovariance (shiftedCoefficients L N) v
        (tailMatrix L N *ᵥ v-discrepancyMatrix P R L N *ᵥ v) := h
    _ = _ := by ring

end Concrete

end Cvs.WeilForm.ArchGreenSecondChannel
