import Mathlib
import Cvs.Finite.ClosedFormEntryRemainders
import Cvs.Finite.DiagonalCutSymbol
import Cvs.Finite.DiagonalLevySymbol
import Cvs.Finite.ModeSumPairValues
import Cvs.Finite.OneModeEntries
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationQuadraticForm
import Cvs.Finite.WindowMatrixClosedForm
import Cvs.Upstream.EvenRowHarmonicSums
import Cvs.Upstream.SymmetricMatrixBottom
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.PoleFreeEntryBounds
import Cvs.WeilForm.Archimedean.PoleFreePairFunction
import Cvs.WeilForm.Archimedean.SymbolImaginaryHalf
import Cvs.WeilForm.ArithmeticFloorAboveBand
import Cvs.WeilForm.EvenBoundaryKernelBound
import Cvs.WeilForm.PrimeDiagonalBulkSchur
import Cvs.Zeta.PrimePowerSideTruncated

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Explicit distant-tail coupling and weighted energy completion

Actual arithmetic columns have a uniform separated-band bound and an explicit buffer cutoff.
-/

noncomputable section
set_option maxHeartbeats 1000000
open Real Matrix Finset
namespace Cvs.WeilForm.DistantTailCoupling
open Cvs.ZeroCounting

open Cvs.Finite.SymmetricModeSet (Idx mode negI)

/-- The finite-prime sine pairing has the same absolute budget as its cosine pairing. -/
theorem abs_prime_sin_le (P R : ℕ) (L ω : ℝ) :
    |Cvs.Finite.OneModeEntries.primeSum P R (Cvs.Finite.DiagonalCutSymbol.sinCut L ω)| ≤ Cvs.WeilForm.EvenBoundaryKernelBound.primeDiagonalBudget P R := by
  unfold Cvs.Finite.OneModeEntries.primeSum Cvs.WeilForm.EvenBoundaryKernelBound.primeDiagonalBudget
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum; intro p _
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum; intro r _
  rw [abs_mul, abs_mul]
  have hc := Cvs.Finite.DiagonalCutSymbol.abs_sinCut_le_one L ω ((r : ℝ)*Real.log p)
  have h := mul_le_mul_of_nonneg_left hc
    (abs_nonneg (Cvs.Zeta.Explicit.Weil.primePowerWeight p r))
  norm_num at *
  nlinarith

private theorem pole_ratio_le (ω : ℝ) : |ω|/(1/4+ω^2)≤1 := by
  rw [div_le_iff₀ (by positivity : (0 : ℝ)<1/4+ω^2)]
  nlinarith [sq_nonneg (|ω|-1/2), sq_abs ω]

/-- The two actual pole terms are uniformly bounded at every real frequency. -/
theorem abs_poleSin_le {L : ℝ} (hL : 0<L) (ω : ℝ) :
    |Cvs.Finite.OneModeEntries.poleSin L ω|≤Real.exp (L/2)-Real.exp (-(L/2)) := by
  have hn : Real.exp (-(L/2))≤1 := Real.exp_le_one_iff.mpr (by linarith)
  have hp : 1≤Real.exp (L/2) := Real.one_le_exp_iff.mpr (by linarith)
  have hden : (0 : ℝ)<1/4+ω^2 := by positivity
  have heq : Cvs.Finite.OneModeEntries.poleSin L ω=
      ω/(1/4+ω^2)*((1-Real.exp (-(L/2)))+(1-Real.exp (L/2))) := by
    unfold Cvs.Finite.OneModeEntries.poleSin
    rw [show ((-1/2):ℝ)*L=-(L/2) by ring,
      show ((1/2):ℝ)*L=L/2 by ring]
    norm_num
    ring
  rw [heq, abs_mul, abs_div, abs_of_pos hden]
  calc
    _ ≤ |ω|/(1/4+ω^2)*
        (|1-Real.exp (-(L/2))|+|1-Real.exp (L/2)|) := by
      exact mul_le_mul_of_nonneg_left (abs_add_le _ _) (by positivity)
    _ ≤ 1*(|1-Real.exp (-(L/2))|+|1-Real.exp (L/2)|) :=
      mul_le_mul_of_nonneg_right (pole_ratio_le ω) (by positivity)
    _ = Real.exp (L/2)-Real.exp (-(L/2)) := by
      rw [abs_of_nonneg (sub_nonneg.mpr hn), abs_of_nonpos (sub_nonpos.mpr hp)]
      ring

private theorem archSymbolIm_positive_grid_le {L : ℝ} (hL : 0 < L)
    {m : ℤ} (hm : 0 < m) :
    |Cvs.WeilForm.Archimedean.SymbolImaginaryHalf.archSymbolIm (2*π*m/L)|≤π/2+L/π := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (show (1 : ℤ) ≤ m by omega)
  have hy : (0 : ℝ)<π*(m : ℝ)/L := by positivity
  have hbase : π/L≤π*(m : ℝ)/L := by
    exact div_le_div_of_nonneg_right (by nlinarith [Real.pi_pos]) hL.le
  have hrecip : 1/(π*(m : ℝ)/L)≤L/π := by
    calc
      _ ≤ 1/(π/L) := one_div_le_one_div_of_le (by positivity) hbase
      _ = L/π := by field_simp
  have hn := Cvs.WeilForm.Archimedean.PoleFreeEntryBounds.archSymbolIm_nonneg hy.le
  have hb := Cvs.WeilForm.Archimedean.PoleFreeEntryBounds.archSymbolIm_le hy
  rw [show 2*(π*(m : ℝ)/L)=2*π*m/L by ring] at hn hb
  rw [abs_of_nonneg hn]
  linarith

/-- The actual imaginary arch symbol is bounded on the complete integer-frequency grid. -/
theorem abs_archSymbolIm_grid_le {L : ℝ} (hL : 0<L) (m : ℤ) :
    |Cvs.WeilForm.Archimedean.SymbolImaginaryHalf.archSymbolIm (2*π*m/L)|≤π/2+L/π := by
  rcases lt_trichotomy m 0 with hm | hm | hm
  · have h := archSymbolIm_positive_grid_le hL (show (0 : ℤ)< -m by omega)
    rw [Int.cast_neg, show 2*π*(-(m : ℝ))/L=-(2*π*m/L) by ring,
      Cvs.WeilForm.Archimedean.PoleFreePairFunction.archSymbolIm_neg, abs_neg] at h
    exact h
  · subst m
    simp only [Int.cast_zero, mul_zero, zero_div, Cvs.WeilForm.Archimedean.PoleFreePairFunction.archSymbolIm_zero, abs_zero]
    positivity
  · exact archSymbolIm_positive_grid_le hL hm

/-- An actual generator budget, depending only on the finite arithmetic window. -/
def generatorBudget (P R : ℕ) (L : ℝ) : ℝ :=
  2*(Real.exp (L/2)-Real.exp (-(L/2)))+π/2+L/π+
    2*Cvs.WeilForm.Archimedean.PoleFreeEntryBounds.tailMass L+Cvs.WeilForm.EvenBoundaryKernelBound.primeDiagonalBudget P R

theorem generatorBudget_nonneg {L : ℝ} (hL : 0<L) (P R : ℕ) :
    0≤generatorBudget P R L := by
  have he : Real.exp (-(L/2))≤Real.exp (L/2) := Real.exp_le_exp.mpr (by linarith)
  have ht := (Cvs.WeilForm.Archimedean.PoleFreeEntryBounds.tailMass_pos hL).le
  have hp := Cvs.WeilForm.EvenBoundaryKernelBound.primeDiagonalBudget_nonneg P R
  unfold generatorBudget
  positivity

/-- Every actual integer mode obeys the same concrete generator budget. -/
theorem abs_gen_le {L : ℝ} (hL : 0<L) (P R : ℕ) (m : ℤ) :
    |Cvs.Finite.WindowMatrixClosedForm.gen P R L m|≤generatorBudget P R L := by
  have hp := abs_poleSin_le hL (2*π*m/L)
  have ha := abs_archSymbolIm_grid_le hL m
  have ht := Cvs.Finite.ClosedFormEntryRemainders.abs_tsum_tail_imTerm_le hL (2*π*m/L) 0
  have ht' : |∑' k, Cvs.Finite.DiagonalLevySymbol.tailFactor L k*Cvs.WeilForm.Archimedean.SymbolImaginaryHalf.imTerm (2*π*m/L) k|≤
      2*Cvs.WeilForm.Archimedean.PoleFreeEntryBounds.tailMass L := by
    have he : Cvs.Finite.DiagonalLevySymbol.tailFactor L 0=Real.exp (-(L/2)) := by
      unfold Cvs.Finite.DiagonalLevySymbol.tailFactor
      congr 1
      norm_num
      ring
    simp only [Nat.cast_zero, add_zero] at ht
    rw [he] at ht
    norm_num at ht
    unfold Cvs.WeilForm.Archimedean.PoleFreeEntryBounds.tailMass
    convert ht using 1
    ring
  have hpr := abs_prime_sin_le P R L (2*π*m/L)
  unfold Cvs.Finite.WindowMatrixClosedForm.gen generatorBudget
  have hsum := abs_sub
    (2*Cvs.Finite.OneModeEntries.poleSin L (2*π*m/L)-Cvs.WeilForm.Archimedean.SymbolImaginaryHalf.archSymbolIm (2*π*m/L)+
      ∑' k, Cvs.Finite.DiagonalLevySymbol.tailFactor L k*Cvs.WeilForm.Archimedean.SymbolImaginaryHalf.imTerm (2*π*m/L) k)
    (Cvs.Finite.OneModeEntries.primeSum P R (Cvs.Finite.DiagonalCutSymbol.sinCut L (2*π*m/L)))
  have hsum2 := abs_add_le
    (2*Cvs.Finite.OneModeEntries.poleSin L (2*π*m/L)-Cvs.WeilForm.Archimedean.SymbolImaginaryHalf.archSymbolIm (2*π*m/L))
    (∑' k, Cvs.Finite.DiagonalLevySymbol.tailFactor L k*Cvs.WeilForm.Archimedean.SymbolImaginaryHalf.imTerm (2*π*m/L) k)
  have hsum3 := abs_sub (2*Cvs.Finite.OneModeEntries.poleSin L (2*π*m/L))
    (Cvs.WeilForm.Archimedean.SymbolImaginaryHalf.archSymbolIm (2*π*m/L))
  rw [abs_mul, abs_two] at hsum3
  linarith

/-- An actual off-diagonal arithmetic entry decays with the integer-mode separation. -/
theorem abs_pairQ_off_le {L : ℝ} (hL : 0<L) (P R : ℕ) {m n : ℤ} (hmn : m≠n) :
    |Cvs.Finite.ModeSumPairValues.pairQ P R L m n/2|≤
      generatorBudget P R L/(π*|(n : ℝ)-m|) := by
  rw [Cvs.Finite.WindowMatrixClosedForm.pairQ_off_closed hL P R hmn, abs_div, abs_mul,
    abs_mul, abs_two, abs_of_pos Real.pi_pos]
  have hden : (0 : ℝ)<π*|(n : ℝ)-m| := by
    have hn : (n : ℝ)-m≠0 := sub_ne_zero.mpr (by exact_mod_cast hmn.symm)
    exact mul_pos Real.pi_pos (abs_pos.mpr hn)
  have hd : (0 : ℝ) < |(n : ℝ)-m| := (mul_pos_iff_of_pos_left Real.pi_pos).mp hden
  have hb : |Cvs.Finite.WindowMatrixClosedForm.gen P R L m-Cvs.Finite.WindowMatrixClosedForm.gen P R L n|≤2*generatorBudget P R L :=
    (abs_sub _ _).trans (by linarith [abs_gen_le hL P R m, abs_gen_le hL P R n])
  rw [div_le_div_iff₀ (by positivity) hden]
  nlinarith

/-- A separated actual matrix entry retains the full distance from a fixed low band. -/
theorem abs_M_separated_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {L : ℝ} (hL : 0<L) (P R : ℕ) {modes : ι→ℤ}
    (hinj : Function.Injective modes) {J : ℝ} (i j : ι)
    (hlo : |(modes i : ℝ)|≤J) (hhi : J < |(modes j : ℝ)|) :
    |Cvs.Finite.TruncationQuadraticForm.M P R L modes i j|≤
      generatorBudget P R L/(π*(|(modes j : ℝ)|-J)) := by
  have hneq : modes i≠modes j := by intro h; rw [h] at hlo; linarith
  rw [Cvs.Finite.TruncationQuadraticForm.M_apply hL P R hinj]
  refine (abs_pairQ_off_le hL P R hneq).trans ?_
  have hsep : |(modes j : ℝ)|-J≤|(modes j : ℝ)-modes i| := by
    have h := abs_sub_abs_le_abs_sub (modes j : ℝ) (modes i : ℝ)
    linarith
  have hpos : (0 : ℝ)<π*(|(modes j : ℝ)|-J) := by positivity
  exact div_le_div_of_nonneg_left (generatorBudget_nonneg hL P R) hpos
    (mul_le_mul_of_nonneg_left hsep Real.pi_pos.le)

/-- The signed finite-mode adapter keeps the distance from the actual low-band cutoff. -/
theorem abs_M_low_high_le {L : ℝ} (hL : 0 < L) (P R N : ℕ) {J : ℕ}
    (i j : Idx N) (hlo : (mode N i).natAbs ≤ J) (hhi : J < (mode N j).natAbs) :
    |Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) i j| ≤
      generatorBudget P R L/(π*(((mode N j).natAbs : ℝ)-J)) := by
  have hlo' : |(mode N i : ℝ)| ≤ (J : ℝ) := by
    have h : ((mode N i).natAbs : ℝ) ≤ J := by exact_mod_cast hlo
    simpa only [Nat.cast_natAbs, Int.cast_abs] using h
  have hhi' : (J : ℝ) < |(mode N j : ℝ)| := by
    have h : (J : ℝ) < (mode N j).natAbs := by exact_mod_cast hhi
    simpa only [Nat.cast_natAbs, Int.cast_abs] using h
  have h := abs_M_separated_le hL P R (Cvs.Finite.SymmetricModeSet.mode_injective N) i j hlo' hhi'
  simpa only [Nat.cast_natAbs, Int.cast_abs] using h

theorem mode_natAbs_some (N : ℕ) (k : Fin N) (b : Bool) :
    (mode N (some (k,b))).natAbs=(k : ℕ)+1 := by
  cases b
  · change (-(((k : ℕ) : ℤ)+1)).natAbs=(k : ℕ)+1
    rw [show -(((k : ℕ) : ℤ)+1)= -(((k : ℕ)+1 : ℕ) : ℤ) by push_cast; ring]
    simp only [Int.natAbs_neg,Int.natAbs_natCast]
  · change (((k : ℕ) : ℤ)+1).natAbs=(k : ℕ)+1
    rw [show ((k : ℕ) : ℤ)+1=(((k : ℕ)+1 : ℕ) : ℤ) by push_cast; ring]
    exact Int.natAbs_natCast _

private theorem one_sign_radial_tail_le (N J K : ℕ) (hK : J+2≤K) :
    (∑ k ∈ Finset.range N, if K≤k+1 then
      1/((((k+1 : ℕ) : ℝ)-(J : ℝ))^2) else 0)≤
        1/((K : ℝ)-(J : ℝ)-1) := by
  let S := (Finset.range N).filter (fun k => K≤k+1)
  let T := S.image (fun k => k+1-K)
  let g : ℕ → ℝ := fun n => 1/((n : ℝ)+(K-J : ℕ))^2
  have hJK : J≤K := by omega
  have hinj : ∀ a∈S, ∀ b∈S, a+1-K=b+1-K → a=b := by
    intro a ha b hb he
    have haK := (Finset.mem_filter.mp ha).2
    have hbK := (Finset.mem_filter.mp hb).2
    omega
  have he : (∑ k∈S, 1/((((k+1 : ℕ) : ℝ)-(J : ℝ))^2))=∑ n∈T,g n := by
    dsimp only [T]
    rw [Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro k hk
    have hkK := (Finset.mem_filter.mp hk).2
    dsimp only [g]
    rw [Nat.cast_sub hkK, Nat.cast_sub hJK]
    congr 2
    push_cast
    ring
  have hs := Cvs.Upstream.EvenRowHarmonicSums.summable_inv_sq_shift (K-J)
  have hfinite : (∑ n∈T,g n)≤∑' n:ℕ,g n :=
    hs.sum_le_tsum T (fun n _ => by dsimp only [g]; positivity)
  have htail := Cvs.Upstream.EvenRowHarmonicSums.tsum_inv_sq_shift_le (N := K-J) (by omega)
  have hcast : ((K-J : ℕ) : ℝ)-1=(K : ℝ)-(J : ℝ)-1 := by
    rw [Nat.cast_sub hJK]
  calc
    _ = ∑ k∈S, 1/((((k+1 : ℕ) : ℝ)-(J : ℝ))^2) := by
      dsimp only [S]
      rw [Finset.sum_filter]
    _ = ∑ n∈T,g n := he
    _ ≤ ∑' n:ℕ,g n := hfinite
    _ ≤ 1/((K : ℝ)-(J : ℝ)-1) := by
      dsimp only [g]
      simpa only [hcast] using htail

/-- The finite signed radial inverse-square tail has an explicit separated-order budget. -/
theorem signed_radial_tail_le (N J K : ℕ) (hK : J+2≤K) :
    (∑ i : Idx N, if K≤(mode N i).natAbs then
      1/(((mode N i).natAbs : ℝ)-(J : ℝ))^2 else 0)≤
        2/((K : ℝ)-(J : ℝ)-1) := by
  have hK0 : ¬K≤0 := by omega
  rw [Fintype.sum_option, Fintype.sum_prod_type]
  simp only [mode, Int.natAbs_zero, hK0, if_false, zero_add]
  have he : (∑ k:Fin N, ∑ b:Bool, if K≤(mode N (some (k,b))).natAbs then
      1/(((mode N (some (k,b))).natAbs : ℝ)-(J : ℝ))^2 else 0)=
      2*∑ k∈Finset.range N, if K≤k+1 then
        1/((((k+1 : ℕ) : ℝ)-(J : ℝ))^2) else 0 := by
    simp only [mode_natAbs_some, Fintype.sum_bool,← two_mul]
    rw [← Finset.mul_sum]
    congr 1
    exact Fin.sum_univ_eq_sum_range (fun k:ℕ => if K≤k+1 then
      1/((((k+1 : ℕ) : ℝ)-(J : ℝ))^2) else 0) N
  change (∑ k:Fin N, ∑ b:Bool, if K≤(mode N (some (k,b))).natAbs then
      1/(((mode N (some (k,b))).natAbs : ℝ)-(J : ℝ))^2 else 0)≤_
  rw [he]
  have h := one_sign_radial_tail_le N J K hK
  exact (mul_le_mul_of_nonneg_left h (by norm_num : (0:ℝ)≤2)).trans_eq (by ring)

/-- At most two signed modes occur at each positive absolute order. -/
theorem signed_head_count_le (N J : ℕ) :
    (∑ i : Idx N, if (mode N i).natAbs≤J then (1:ℝ) else 0)≤2*(J : ℝ)+1 := by
  let S := (Finset.range N).filter (fun k => k+1≤J)
  have hsub : S⊆Finset.range J := by
    intro k hk
    exact Finset.mem_range.mpr (by have := (Finset.mem_filter.mp hk).2; omega)
  have hcard : (S.card : ℝ)≤J := by
    exact_mod_cast ((Finset.card_le_card hsub).trans_eq (Finset.card_range J))
  have hone : (∑ k∈Finset.range N,if k+1≤J then (1:ℝ) else 0)=(S.card : ℝ) := by
    dsimp only [S]
    rw [← Finset.sum_filter]
    simp
  have he : (∑ i : Idx N, if (mode N i).natAbs≤J then (1:ℝ) else 0)=
      1+2*∑ k∈Finset.range N,if k+1≤J then (1:ℝ) else 0 := by
    rw [Fintype.sum_option,Fintype.sum_prod_type]
    simp only [mode,Int.natAbs_zero,Nat.zero_le,if_true]
    change 1+(∑ k:Fin N,∑ b:Bool,if (mode N (some (k,b))).natAbs≤J then (1:ℝ) else 0)=_
    simp only [mode_natAbs_some,Fintype.sum_bool,← two_mul]
    rw [← Finset.mul_sum]
    congr 1
    congr 1
    exact Fin.sum_univ_eq_sum_range (fun k:ℕ => if k+1≤J then (1:ℝ) else 0) N
  rw [he,hone]
  linarith

/-- A high output row of the actual matrix is bounded by its distance from the input band. -/
theorem abs_mulVec_high_le_l1 {L : ℝ} (hL : 0<L) (P R N J : ℕ)
    (u : Idx N → ℝ) (hu : ∀ j,J<(mode N j).natAbs → u j=0)
    (i : Idx N) (hi : J<(mode N i).natAbs) :
    |(Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ u) i|≤
      generatorBudget P R L/(π*((mode N i).natAbs-J))*∑ j,|u j| := by
  change |∑ j,Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) i j*u j|≤_
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  by_cases hj : J<(mode N j).natAbs
  · simp [hu j hj]
  · have hb := abs_M_low_high_le hL P R N j i (le_of_not_gt hj) hi
    rw [Cvs.Finite.TruncationQuadraticForm.M_symm hL P R (Cvs.Finite.SymmetricModeSet.mode_injective N) j i] at hb
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hb (abs_nonneg _)

/-- The signed coefficient one-norm on a fixed band is controlled by its exact mode count. -/
theorem head_l1_sq_le (N J : ℕ) (u : Idx N → ℝ)
    (hu : ∀ i,J<(mode N i).natAbs → u i=0) :
    (∑ i,|u i|)^2≤(2*(J : ℝ)+1)*(u ⬝ᵥ u) := by
  let χ : Idx N → ℝ := fun i => if (mode N i).natAbs≤J then 1 else 0
  have he : (∑ i,χ i*|u i|)=∑ i,|u i| := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : (mode N i).natAbs≤J
    · simp [χ,hi]
    · simp [χ,hi,hu i (lt_of_not_ge hi)]
  have hc : (∑ i,χ i^2)≤2*(J : ℝ)+1 := by
    simpa [χ] using signed_head_count_le N J
  have hs : (∑ i,|u i|^2)=u ⬝ᵥ u := by simp [dotProduct,pow_two]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ χ (fun i => |u i|)
  rw [he,hs] at hcs
  exact hcs.trans (mul_le_mul_of_nonneg_right hc (Cvs.Upstream.SymmetricMatrixBottom.dotProduct_self_nonneg' u))

/-- The actual output beyond a separated cutoff has a uniform coefficient one-norm budget. -/
theorem high_output_mass_le_l1 {L : ℝ} (hL : 0<L) (P R N J K : ℕ)
    (hK : J+2≤K) (u : Idx N → ℝ) (hu : ∀ i,J<(mode N i).natAbs → u i=0) :
    Cvs.WeilForm.PrimeDiagonalBulkSchur.highPart K N (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ u) ⬝ᵥ
      Cvs.WeilForm.PrimeDiagonalBulkSchur.highPart K N (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ u)≤
        2*(generatorBudget P R L)^2/(π^2*((K : ℝ)-J-1))*(∑ i,|u i|)^2 := by
  let A : ℝ := generatorBudget P R L/π*∑ i,|u i|
  have hKD : (0 : ℝ)<(K : ℝ)-J-1 := by
    have h : (J : ℝ)+2≤K := by exact_mod_cast hK
    linarith
  have hA : 0≤A := by
    dsimp only [A]
    exact mul_nonneg (div_nonneg (generatorBudget_nonneg hL P R) Real.pi_pos.le)
      (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  have hrow : ∀ i : Idx N,
      (Cvs.WeilForm.PrimeDiagonalBulkSchur.highPart K N (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ u) i)^2≤
        A^2*(if K≤(mode N i).natAbs then 1/(((mode N i).natAbs : ℝ)-J)^2 else 0) := by
    intro i
    by_cases hi : K≤(mode N i).natAbs
    · have hiJ : J<(mode N i).natAbs := by omega
      have hd : (0 : ℝ)<((mode N i).natAbs : ℝ)-J := by
        have h : (J : ℝ)<(mode N i).natAbs := by exact_mod_cast hiJ
        linarith
      have hb := abs_mulVec_high_le_l1 hL P R N J u hu i hiJ
      have he : generatorBudget P R L/(π*(((mode N i).natAbs : ℝ)-J))*
          (∑ j,|u j|)=A/(((mode N i).natAbs : ℝ)-J) := by
        dsimp only [A]
        field_simp [hd.ne',Real.pi_ne_zero]
      rw [he] at hb
      have hsq := (sq_le_sq₀ (abs_nonneg _) (div_nonneg hA hd.le)).mpr hb
      rw [sq_abs,div_pow] at hsq
      simp only [Cvs.WeilForm.PrimeDiagonalBulkSchur.highPart,not_lt.mpr hi,if_false,hi,if_true]
      exact hsq.trans_eq (by ring)
    · simp [Cvs.WeilForm.PrimeDiagonalBulkSchur.highPart,lt_of_not_ge hi,hi]
  have hr := signed_radial_tail_le N J K hK
  have hs := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => hrow i)
  rw [← Finset.mul_sum] at hs
  change (∑ i,_)≤_ at hs
  have htotal := hs.trans (mul_le_mul_of_nonneg_left hr (sq_nonneg A))
  change (∑ i,_)≤_
  simp only [sq] at htotal
  exact htotal.trans_eq (by
    dsimp only [A]
    field_simp [hKD.ne',Real.pi_ne_zero])

/-- Separated actual low-to-high coupling decays uniformly in the retained matrix order. -/
theorem high_output_mass_le {L : ℝ} (hL : 0<L) (P R N J K : ℕ)
    (hK : J+2≤K) (u : Idx N → ℝ) (hu : ∀ i,J<(mode N i).natAbs → u i=0) :
    Cvs.WeilForm.PrimeDiagonalBulkSchur.highPart K N (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ u) ⬝ᵥ
      Cvs.WeilForm.PrimeDiagonalBulkSchur.highPart K N (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ u)≤
        2*(2*(J : ℝ)+1)*(generatorBudget P R L)^2/(π^2*((K : ℝ)-J-1))*(u ⬝ᵥ u) := by
  have hd : (0 : ℝ)<(K : ℝ)-J-1 := by
    have h : (J : ℝ)+2≤K := by exact_mod_cast hK
    linarith
  have hc : 0≤2*(generatorBudget P R L)^2/(π^2*((K : ℝ)-J-1)) := by positivity
  refine (high_output_mass_le_l1 hL P R N J K hK u hu).trans ?_
  have h := mul_le_mul_of_nonneg_left (head_l1_sq_le N J u hu) hc
  exact h.trans_eq (by ring)

/-- A closed integer buffer for a prescribed actual high-output mass budget. -/
def bufferCutoff (P R : ℕ) (L : ℝ) (J : ℕ) (ε : ℝ) : ℕ :=
  J+2+⌈(2*(2*(J : ℝ)+1)*(generatorBudget P R L)^2/π^2)/ε⌉₊

theorem bufferCutoff_ge (P R : ℕ) (L : ℝ) (J : ℕ) (ε : ℝ) :
    J+2≤bufferCutoff P R L J ε := by
  unfold bufferCutoff
  omega

/-- The closed buffer makes the actual separated-band coefficient smaller than its target. -/
theorem bufferCutoff_cost_lt (P R : ℕ) (L : ℝ) (J : ℕ) {ε : ℝ} (hε : 0<ε) :
    2*(2*(J : ℝ)+1)*(generatorBudget P R L)^2/
      (π^2*((bufferCutoff P R L J ε : ℝ)-J-1))<ε := by
  let B : ℝ := 2*(2*(J : ℝ)+1)*(generatorBudget P R L)^2/π^2
  have hceil : B≤(⌈B/ε⌉₊ : ℝ)*ε := (div_le_iff₀ hε).mp (Nat.le_ceil _)
  have he : (bufferCutoff P R L J ε : ℝ)-J-1=(⌈B/ε⌉₊ : ℝ)+1 := by
    unfold bufferCutoff
    push_cast
    dsimp only [B]
    ring
  have hd : 0<(bufferCutoff P R L J ε : ℝ)-J-1 := by rw [he]; positivity
  rw [← div_div]
  change B/((bufferCutoff P R L J ε : ℝ)-J-1)<ε
  rw [div_lt_iff₀ hd,he]
  nlinarith

/-- Every larger explicit buffer gives an arbitrarily small actual output mass, uniformly in order. -/
theorem high_output_mass_buffer_le {L ε : ℝ} (hL : 0<L) (hε : 0<ε)
    (P R N J K : ℕ) (hK : bufferCutoff P R L J ε≤K)
    (u : Idx N → ℝ) (hu : ∀ i,J<(mode N i).natAbs → u i=0) :
    Cvs.WeilForm.PrimeDiagonalBulkSchur.highPart K N (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ u) ⬝ᵥ
      Cvs.WeilForm.PrimeDiagonalBulkSchur.highPart K N (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ u)≤ε*(u ⬝ᵥ u) := by
  have hsep : J+2≤K := (bufferCutoff_ge P R L J ε).trans hK
  have hd : 0<π^2*((bufferCutoff P R L J ε : ℝ)-J-1) := by
    have hc : (J : ℝ)+2≤bufferCutoff P R L J ε := by
      exact_mod_cast bufferCutoff_ge P R L J ε
    have : 0<(bufferCutoff P R L J ε : ℝ)-J-1 := by linarith
    positivity
  have hden : π^2*((bufferCutoff P R L J ε : ℝ)-J-1)≤π^2*((K : ℝ)-J-1) := by
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg π)
    have : (bufferCutoff P R L J ε : ℝ)≤K := by exact_mod_cast hK
    linarith
  have hcost := (div_le_div_of_nonneg_left
    (show 0≤2*(2*(J : ℝ)+1)*(generatorBudget P R L)^2 by positivity) hd hden).trans_lt
      (bufferCutoff_cost_lt P R L J hε)
  exact (high_output_mass_le hL P R N J K hsep u hu).trans
    (mul_le_mul_of_nonneg_right hcost.le (Cvs.Upstream.SymmetricMatrixBottom.dotProduct_self_nonneg' u))

/-- The actual diagonal reserve after shifting the requested floor. -/
def shiftedDiagonal (P R : ℕ) (L μ : ℝ) (N : ℕ) (i : Idx N) : ℝ :=
  Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol (2*π*(mode N i : ℝ)/L)-Cvs.WeilForm.PrimeDiagonalBulkSchur.primeCost P R-μ

/-- Each high arithmetic column coordinate is charged its own diagonal reserve. -/
def weightedLeakage (K P R : ℕ) (L μ : ℝ) (N : ℕ) (u : Idx N → ℝ) : ℝ :=
  ∑ i, if (mode N i).natAbs<K then 0 else
    (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ u) i ^ 2/shiftedDiagonal P R L μ N i

theorem shiftedDiagonal_ge {L T μ : ℝ} (hL : 0 < L) (hT : 2 ≤ T)
    (P R N : ℕ) (i : Idx N) (hi : Cvs.WeilForm.ArithmeticFloorAboveBand.cutoffOrder L T ≤ (mode N i).natAbs) :
    Cvs.WeilForm.PrimeDiagonalBulkSchur.improvedFloor P R T-μ ≤ shiftedDiagonal P R L μ N i := by
  have h := Cvs.WeilForm.ArithmeticFloorAboveBand.archLower_le_archSymbol hT (Cvs.WeilForm.ArithmeticFloorAboveBand.cutoffOrder_frequency hL T (mode N i) hi)
  unfold shiftedDiagonal Cvs.WeilForm.PrimeDiagonalBulkSchur.improvedFloor
  linarith

/-- The positive actual remainder lets the diagonal reserve sit below full shifted energy. -/
theorem shiftedDiagonal_energy_le {L μ : ℝ} (hL : 0 < L) (P R N : ℕ)
    (w : Idx N → ℝ) (hw : ∀ i,w (negI N i)=w i) :
    (∑ i, shiftedDiagonal P R L μ N i*w i^2) ≤
      w ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ w)-μ*(w ⬝ᵥ w) := by
  have h := (Cvs.WeilForm.PrimeDiagonalBulkSchur.positiveRemainder_quad_interval hL P R N w hw).1
  rw [Cvs.WeilForm.PrimeDiagonalBulkSchur.matrix_eq_shifted_positive hL,Matrix.add_mulVec,dotProduct_add]
  simp only [dotProduct,Matrix.mulVec_diagonal,Finset.mul_sum]
  unfold shiftedDiagonal
  have he : (∑ i, (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol (2*π*(mode N i : ℝ)/L)-Cvs.WeilForm.PrimeDiagonalBulkSchur.primeCost P R-μ)*w i^2)=
      (∑ i,w i*((Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol (2*π*(mode N i : ℝ)/L)-Cvs.WeilForm.PrimeDiagonalBulkSchur.primeCost P R)*w i))-
        μ*∑ i,w i*w i := by
    rw [Finset.mul_sum,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he]
  change 0 ≤ w ⬝ᵥ (Cvs.WeilForm.PrimeDiagonalBulkSchur.positiveRemainder P R L N *ᵥ w) at h
  simp only [dotProduct] at h
  rw [←Finset.mul_sum]
  linarith

private theorem scalar_completion {d : ℝ} (hd : 0 < d) (c w : ℝ) :
    2*|c*w| ≤ c^2/d+d*w^2 := by
  have hc : c^2/d*d=c^2 := div_mul_cancel₀ _ hd.ne'
  have hp : 2*(c*w) ≤ c^2/d+d*w^2 := by
    apply (mul_le_mul_iff_right₀ hd).mp
    nlinarith [sq_nonneg (d*w-c)]
  have hm : -(2*(c*w)) ≤ c^2/d+d*w^2 := by
    apply (mul_le_mul_iff_right₀ hd).mp
    nlinarith [sq_nonneg (d*w+c)]
  have h := abs_le.mpr ⟨by linarith, hp⟩
  simpa only [abs_mul,abs_two] using h

private theorem high_zero_low {K N : ℕ} (w : Idx N → ℝ)
    (hw : Cvs.WeilForm.PrimeDiagonalBulkSchur.highPart K N w=w) (i : Idx N) (hi : (mode N i).natAbs<K) : w i=0 := by
  have h := congrArg (fun f : Idx N → ℝ => f i) hw
  simpa only [Cvs.WeilForm.PrimeDiagonalBulkSchur.highPart,if_pos hi] using h.symm

/-- The actual high energy absorbs twice the cross term at the weighted diagonal price. -/
theorem weighted_cross_completion {L T μ : ℝ} (hL : 0 < L) (hT : 2 ≤ T)
    (K P R N : ℕ) (hK : Cvs.WeilForm.ArithmeticFloorAboveBand.cutoffOrder L T ≤ K)
    (hgap : μ < Cvs.WeilForm.PrimeDiagonalBulkSchur.improvedFloor P R T)
    (u w : Idx N → ℝ) (hw : ∀ i,w (negI N i)=w i)
    (hhigh : Cvs.WeilForm.PrimeDiagonalBulkSchur.highPart K N w=w) :
    2*|u ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ w)| ≤
      weightedLeakage K P R L μ N u+
        (w ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ w)-μ*(w ⬝ᵥ w)) := by
  let M := Cvs.Finite.TruncationQuadraticForm.M P R L (mode N)
  have hdiag := shiftedDiagonal_energy_le (μ := μ) hL P R N w hw
  have hrow : 2*|u ⬝ᵥ (M *ᵥ w)| ≤
      weightedLeakage K P R L μ N u+
        ∑ i,shiftedDiagonal P R L μ N i*w i^2 := by
    rw [Cvs.Upstream.SymmetricMatrixBottom.dotProduct_mulVec_comm (Cvs.Finite.TruncationQuadraticForm.M_symm hL P R (Cvs.Finite.SymmetricModeSet.mode_injective N)) u w]
    unfold dotProduct
    refine (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by norm_num)).trans ?_
    rw [Finset.mul_sum]
    unfold weightedLeakage
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : (mode N i).natAbs<K
    · simp [high_zero_low w hhigh i hi,hi]
    · rw [if_neg hi]
      have hd := shiftedDiagonal_ge (μ := μ) hL hT P R N i (hK.trans (le_of_not_gt hi))
      have hdpos : 0 < shiftedDiagonal P R L μ N i := by linarith
      simpa only [mul_comm (w i)] using scalar_completion hdpos ((M *ᵥ u) i) (w i)
  dsimp only [M] at hrow
  linarith

/-- The comparison preserves all actual low energy and charges only weighted high coupling. -/
theorem weighted_low_high_lower {L T μ : ℝ} (hL : 0 < L) (hT : 2 ≤ T)
    (K P R N : ℕ) (hK : Cvs.WeilForm.ArithmeticFloorAboveBand.cutoffOrder L T ≤ K)
    (hgap : μ < Cvs.WeilForm.PrimeDiagonalBulkSchur.improvedFloor P R T)
    (u w : Idx N → ℝ) (hw : ∀ i,w (negI N i)=w i)
    (hlow : Cvs.WeilForm.PrimeDiagonalBulkSchur.lowPart K N u=u)
    (hhigh : Cvs.WeilForm.PrimeDiagonalBulkSchur.highPart K N w=w) :
    u ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ u)-μ*(u ⬝ᵥ u)-
        weightedLeakage K P R L μ N u ≤
      (u+w) ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ (u+w))-μ*((u+w) ⬝ᵥ (u+w)) := by
  let M := Cvs.Finite.TruncationQuadraticForm.M P R L (mode N)
  have hcross := weighted_cross_completion hL hT K P R N hK hgap u w hw hhigh
  have horth : u ⬝ᵥ w=0 := by
    have h := Cvs.WeilForm.PrimeDiagonalBulkSchur.low_dot_high K N u w
    simpa only [hlow,hhigh] using h
  have hquad : (u+w) ⬝ᵥ (M *ᵥ (u+w))=
      u ⬝ᵥ (M *ᵥ u)+2*(u ⬝ᵥ (M *ᵥ w))+w ⬝ᵥ (M *ᵥ w) := by
    simp only [Matrix.mulVec_add,add_dotProduct,dotProduct_add]
    rw [Cvs.Upstream.SymmetricMatrixBottom.dotProduct_mulVec_comm (Cvs.Finite.TruncationQuadraticForm.M_symm hL P R (Cvs.Finite.SymmetricModeSet.mode_injective N)) w u]
    ring
  have hmass : (u+w) ⬝ᵥ (u+w)=u ⬝ᵥ u+w ⬝ᵥ w := by
    simp only [add_dotProduct,dotProduct_add,dotProduct_comm w u,horth]
    ring
  change u ⬝ᵥ (M *ᵥ u)-μ*(u ⬝ᵥ u)-_≤(u+w) ⬝ᵥ (M *ᵥ (u+w))-μ*((u+w) ⬝ᵥ (u+w))
  rw [hquad,hmass]
  dsimp only [M] at *
  nlinarith [neg_abs_le (u ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ w))]

/-- Actual individual diagonal prices are no larger than the scalar high-floor price. -/
theorem weightedLeakage_le_high_norm {L T μ : ℝ} (hL : 0 < L) (hT : 2 ≤ T)
    (K P R N : ℕ) (hK : Cvs.WeilForm.ArithmeticFloorAboveBand.cutoffOrder L T ≤ K)
    (hgap : μ < Cvs.WeilForm.PrimeDiagonalBulkSchur.improvedFloor P R T) (u : Idx N → ℝ) :
    weightedLeakage K P R L μ N u ≤
      (Cvs.WeilForm.PrimeDiagonalBulkSchur.highPart K N (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ u) ⬝ᵥ
        Cvs.WeilForm.PrimeDiagonalBulkSchur.highPart K N (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ u))/
          (Cvs.WeilForm.PrimeDiagonalBulkSchur.improvedFloor P R T-μ) := by
  unfold weightedLeakage dotProduct
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : (mode N i).natAbs<K
  · simp [Cvs.WeilForm.PrimeDiagonalBulkSchur.highPart,hi]
  · simp only [if_neg hi,Cvs.WeilForm.PrimeDiagonalBulkSchur.highPart]
    have hd := shiftedDiagonal_ge (μ := μ) hL hT P R N i (hK.trans (le_of_not_gt hi))
    simpa only [pow_two] using
      div_le_div_of_nonneg_left (sq_nonneg ((Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ u) i))
        (sub_pos.mpr hgap) hd

/-- The actual weighted price is arbitrarily small after the explicit separated buffer. -/
theorem weightedLeakage_buffer_le {L T μ ε : ℝ}
    (hL : 0 < L) (hT : 2 ≤ T) (hε : 0 < ε)
    (K P R N J : ℕ) (hK : Cvs.WeilForm.ArithmeticFloorAboveBand.cutoffOrder L T ≤ K)
    (hbuffer : bufferCutoff P R L J (ε*(Cvs.WeilForm.PrimeDiagonalBulkSchur.improvedFloor P R T-μ)) ≤ K)
    (hgap : μ < Cvs.WeilForm.PrimeDiagonalBulkSchur.improvedFloor P R T)
    (u : Idx N → ℝ) (hu : ∀ i,J<(mode N i).natAbs → u i=0) :
    weightedLeakage K P R L μ N u ≤ ε*(u ⬝ᵥ u) := by
  have ha : 0 < Cvs.WeilForm.PrimeDiagonalBulkSchur.improvedFloor P R T-μ := sub_pos.mpr hgap
  have hm := high_output_mass_buffer_le hL (mul_pos hε ha) P R N J K hbuffer u hu
  have hp := weightedLeakage_le_high_norm hL hT K P R N hK hgap u
  calc
    _ ≤ _ := hp
    _ ≤ (ε*(Cvs.WeilForm.PrimeDiagonalBulkSchur.improvedFloor P R T-μ)*(u ⬝ᵥ u))/(Cvs.WeilForm.PrimeDiagonalBulkSchur.improvedFloor P R T-μ) :=
      div_le_div_of_nonneg_right hm ha.le
    _ = ε*(u ⬝ᵥ u) := by field_simp

end Cvs.WeilForm.DistantTailCoupling
