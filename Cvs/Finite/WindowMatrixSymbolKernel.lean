import Mathlib
import Cvs.Finite.DiagonalCutSymbol
import Cvs.Finite.DiagonalLevySymbol
import Cvs.Finite.OneModeEntries
import Cvs.Finite.PairPoleChannelClosed
import Cvs.Finite.TruncationQuadraticForm
import Cvs.Finite.WindowMatrixClosedForm
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.SymbolImaginaryHalf
import Cvs.Zeta.PrimePowerSideTruncated

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The window matrix as symbol plus an explicit kernel

`M = diag(symbol) + (1/L)·K`, where `K` is the pole's rank-two block, the digamma ladder
`Σ_k 2(1 − x^{−b_k})(u_k u_k' − v_k v_k')`, and the prime Schur products
`2 w_t · t cos(t(ω+ω')/2) sinc(t(ω−ω')/2)`; on vectors annihilated by the odd `v`'s the
archimedean part is a sum of squares.
-/

namespace Cvs.Finite.WindowMatrixSymbolKernel

open Real
open Cvs.Finite.DiagonalLevySymbol (tailFactor)
open Cvs.WeilForm.Archimedean.SymbolImaginaryHalf (imTerm archSymbolIm)
open Cvs.Finite.OneModeEntries Cvs.Finite.DiagonalCutSymbol

/-- `h_a(ω) = ω/(a² + ω²)`, the generator of each rank-two piece. -/
noncomputable def hh (a ω : ℝ) : ℝ := ω / (a ^ 2 + ω ^ 2)
/-- The even factor `a/(a² + ω²)`. -/
noncomputable def uu (a ω : ℝ) : ℝ := a / (a ^ 2 + ω ^ 2)
/-- The odd factor `ω/(a² + ω²)`. -/
noncomputable def vv (a ω : ℝ) : ℝ := ω / (a ^ 2 + ω ^ 2)
/-- The ladder abscissae `b_k = 2k + ½`. -/
noncomputable def bk (k : ℕ) : ℝ := 2 * (k : ℝ) + 1 / 2
/-- `sinc d = sin d / d`, with `sinc 0 = 1`. -/
noncomputable def sinc (d : ℝ) : ℝ := if d = 0 then 1 else Real.sin d / d

theorem bk_pos (k : ℕ) : 0 < bk k := by unfold bk; positivity

theorem tailFactor_eq_rpow {L : ℝ} (k : ℕ) :
    tailFactor L k = Real.exp (-(bk k * L)) := by
  unfold tailFactor bk; congr 1; ring

/-- **The divided difference of `h_a` is rank two**: `u u' − v v'`. -/
theorem dd_hh {a ω ω' : ℝ} (ha : 0 < a) (hne : ω ≠ ω') :
    (hh a ω - hh a ω') / (ω - ω') = uu a ω * uu a ω' - vv a ω * vv a ω' := by
  unfold hh uu vv
  have h1 : a ^ 2 + ω ^ 2 ≠ 0 := by positivity
  have h2 : a ^ 2 + ω' ^ 2 ≠ 0 := by positivity
  have h3 : ω - ω' ≠ 0 := sub_ne_zero.mpr hne
  field_simp
  ring

/-- **The divided difference of a cut sine** is a cosine times a sinc. -/
theorem dd_sinCut {L t ω ω' : ℝ} (ht : 0 < t) (hne : ω ≠ ω') :
    (sinCut L ω t - sinCut L ω' t) / (ω - ω')
      = if t ≤ L then t * Real.cos (t * (ω + ω') / 2) * sinc (t * (ω - ω') / 2) else 0 := by
  unfold sinCut
  by_cases hL : t ≤ L
  · rw [if_pos hL, if_pos hL, if_pos hL]
    have h3 : ω - ω' ≠ 0 := sub_ne_zero.mpr hne
    have hd : t * (ω - ω') / 2 ≠ 0 := by positivity
    rw [sinc, if_neg hd, Real.sin_sub_sin]
    have e1 : (ω * t - ω' * t) / 2 = t * (ω - ω') / 2 := by ring
    have e2 : (ω * t + ω' * t) / 2 = t * (ω + ω') / 2 := by ring
    rw [e1, e2]
    field_simp
  · rw [if_neg hL, if_neg hL, if_neg hL]; simp

/-! ### The generator as a function of the frequency -/

/-- cvsnum's generator as a function of `ω`: `−2c_x h_{½} − Σ_k 2(1 − x^{−b_k}) h_{b_k} − 2S`. -/
noncomputable def Fgen (P R : ℕ) (L ω : ℝ) : ℝ :=
  -2 * Cvs.Finite.PairPoleChannelClosed.poleFactor L * hh (1 / 2) ω
    - ∑' k, 2 * (1 - tailFactor L k) * hh (bk k) ω
    - primeSum P R (sinCut L ω)

theorem imTerm_eq (ω : ℝ) (k : ℕ) : imTerm ω k = 2 * hh (bk k) ω := by
  unfold imTerm hh bk
  have : (0:ℝ) < (1 / 4 + (k : ℝ)) ^ 2 + (ω / 2) ^ 2 := by positivity
  have : (0:ℝ) < (2 * (k : ℝ) + 1 / 2) ^ 2 + ω ^ 2 := by positivity
  field_simp
  ring

theorem two_poleSin (L ω : ℝ) :
    2 * poleSin L ω = -2 * Cvs.Finite.PairPoleChannelClosed.poleFactor L * hh (1 / 2) ω := by
  unfold poleSin Cvs.Finite.PairPoleChannelClosed.poleFactor hh
  have : (0:ℝ) < (1 / 2) ^ 2 + ω ^ 2 := by positivity
  field_simp
  ring

theorem summable_ladder {L : ℝ} (hL : 0 < L) (ω : ℝ) :
    Summable fun k => 2 * (1 - tailFactor L k) * hh (bk k) ω := by
  have h := (Cvs.WeilForm.Archimedean.SymbolImaginaryHalf.summable_imTerm ω).sub
    (Cvs.Finite.WindowMatrixClosedForm.summable_tail_imTerm hL ω)
  refine h.congr fun k => ?_
  rw [imTerm_eq]; ring

/-- **`gen` is `Fgen` at the mode frequency.** -/
theorem gen_eq_Fgen (P R : ℕ) {L : ℝ} (hL : 0 < L) (m : ℤ) :
    Cvs.Finite.WindowMatrixClosedForm.gen P R L m = Fgen P R L (2 * π * m / L) := by
  unfold Cvs.Finite.WindowMatrixClosedForm.gen Fgen
  rw [two_poleSin, ← (Cvs.WeilForm.Archimedean.SymbolImaginaryHalf.hasSum_imTerm _).tsum_eq]
  have hcomb : ∑' k, imTerm (2 * π * m / L) k - ∑' k, tailFactor L k * imTerm (2 * π * m / L) k
      = ∑' k, 2 * (1 - tailFactor L k) * hh (bk k) (2 * π * m / L) := by
    rw [← Summable.tsum_sub (Cvs.WeilForm.Archimedean.SymbolImaginaryHalf.summable_imTerm _)
      (Cvs.Finite.WindowMatrixClosedForm.summable_tail_imTerm hL _)]
    refine tsum_congr fun k => ?_
    rw [imTerm_eq]; ring
  linarith [hcomb]

/-! ### The kernel -/

/-- The archimedean kernel: pole block plus the digamma ladder. -/
noncomputable def kArch (L ω ω' : ℝ) : ℝ :=
  2 * Cvs.Finite.PairPoleChannelClosed.poleFactor L * (uu (1 / 2) ω * uu (1 / 2) ω' - vv (1 / 2) ω * vv (1 / 2) ω')
    + ∑' k, 2 * (1 - tailFactor L k) * (uu (bk k) ω * uu (bk k) ω' - vv (bk k) ω * vv (bk k) ω')

/-- The prime kernel: `2 w_{p,r} · t cos(t(ω+ω')/2) sinc(t(ω−ω')/2)` at the lags `t = r log p ≤ L`. -/
noncomputable def kPrime (P R : ℕ) (L ω ω' : ℝ) : ℝ :=
  ∑ p ∈ (Finset.range (P + 1)).filter Nat.Prime, ∑ r ∈ Finset.Icc 1 R,
    Cvs.Zeta.Explicit.Weil.primePowerWeight p r
      * (2 * (if (r : ℝ) * Real.log p ≤ L then (r : ℝ) * Real.log p
          * Real.cos ((r : ℝ) * Real.log p * (ω + ω') / 2)
          * sinc ((r : ℝ) * Real.log p * (ω - ω') / 2) else 0))

/-- The full kernel. -/
noncomputable def kK (P R : ℕ) (L ω ω' : ℝ) : ℝ := kArch L ω ω' + kPrime P R L ω ω'

/-- The symbol at the window: `archSymbol` less the cut prime cosine sum. -/
noncomputable def symbolCut (P R : ℕ) (L ω : ℝ) : ℝ :=
  Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol ω - primeSum P R (cosCut L ω)

theorem summable_ladder_pair {L : ℝ} (hL : 0 < L) (ω ω' : ℝ) :
    Summable fun k => 2 * (1 - tailFactor L k) * (uu (bk k) ω * uu (bk k) ω' - vv (bk k) ω * vv (bk k) ω') := by
  have hb : ∀ k, |uu (bk k) ω * uu (bk k) ω' - vv (bk k) ω * vv (bk k) ω'| ≤ 2 / bk k ^ 2 := by
    intro k
    have hk := bk_pos k
    have hden : 0 < bk k ^ 2 + ω ^ 2 := add_pos_of_pos_of_nonneg (pow_pos hk 2) (sq_nonneg ω)
    have hden' : 0 < bk k ^ 2 + ω' ^ 2 := add_pos_of_pos_of_nonneg (pow_pos hk 2) (sq_nonneg ω')
    have h1 : |uu (bk k) ω| ≤ 1 / bk k := by
      unfold uu; rw [abs_div, abs_of_pos hk, abs_of_pos hden, div_le_div_iff₀ hden hk]
      nlinarith [sq_nonneg ω]
    have h1' : |uu (bk k) ω'| ≤ 1 / bk k := by
      unfold uu; rw [abs_div, abs_of_pos hk, abs_of_pos hden', div_le_div_iff₀ hden' hk]
      nlinarith [sq_nonneg ω']
    have h2 : |vv (bk k) ω| ≤ 1 / bk k := by
      unfold vv; rw [abs_div, abs_of_pos hden, div_le_div_iff₀ hden hk]
      nlinarith [sq_nonneg (|ω| - bk k), abs_nonneg ω, sq_abs ω]
    have h2' : |vv (bk k) ω'| ≤ 1 / bk k := by
      unfold vv; rw [abs_div, abs_of_pos hden', div_le_div_iff₀ hden' hk]
      nlinarith [sq_nonneg (|ω'| - bk k), abs_nonneg ω', sq_abs ω']
    calc |uu (bk k) ω * uu (bk k) ω' - vv (bk k) ω * vv (bk k) ω'|
        ≤ |uu (bk k) ω * uu (bk k) ω'| + |vv (bk k) ω * vv (bk k) ω'| := abs_sub _ _
      _ = |uu (bk k) ω| * |uu (bk k) ω'| + |vv (bk k) ω| * |vv (bk k) ω'| := by rw [abs_mul, abs_mul]
      _ ≤ 1 / bk k * (1 / bk k) + 1 / bk k * (1 / bk k) :=
          add_le_add (mul_le_mul h1 h1' (abs_nonneg _) (by positivity))
            (mul_le_mul h2 h2' (abs_nonneg _) (by positivity))
      _ = 2 / bk k ^ 2 := by ring
  have hs : Summable fun k : ℕ => 2 * (2 / bk k ^ 2) := by
    have := Cvs.Finite.DiagonalLevySymbol.summable_inv_sq_quarter
    refine (this.mul_left 1).congr fun k => ?_
    unfold bk; field_simp; ring
  refine Summable.of_norm_bounded hs fun k => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
  have ht : |1 - tailFactor L k| ≤ 1 := by
    rw [abs_le]; constructor
    · have : 0 ≤ tailFactor L k := (Real.exp_pos _).le
      have : tailFactor L k ≤ 1 := by
        unfold tailFactor; apply Real.exp_le_one_iff.mpr
        have : 0 ≤ (1 / 4 + (k : ℝ)) * (2 * L) := by positivity
        linarith
      linarith
    · have : 0 ≤ tailFactor L k := (Real.exp_pos _).le; linarith
  calc 2 * |1 - tailFactor L k| * |uu (bk k) ω * uu (bk k) ω' - vv (bk k) ω * vv (bk k) ω'|
      ≤ 2 * 1 * (2 / bk k ^ 2) := by gcongr; exact hb k
    _ = 2 * (2 / bk k ^ 2) := by ring

/-- **Off the diagonal**: the divided difference of `−Fgen` is the kernel. -/
theorem dd_Fgen (P R : ℕ) {L ω ω' : ℝ} (hL : 0 < L) (hne : ω ≠ ω') :
    (Fgen P R L ω - Fgen P R L ω') / (ω' - ω) = kK P R L ω ω' := by
  unfold Fgen kK kArch kPrime primeSum
  have hs := summable_ladder hL ω
  have hs' := summable_ladder hL ω'
  have h3 : ω - ω' ≠ 0 := sub_ne_zero.mpr hne
  have h3' : ω' - ω ≠ 0 := sub_ne_zero.mpr hne.symm
  -- pole
  have hpole : (hh (1 / 2) ω - hh (1 / 2) ω') / (ω - ω')
      = uu (1 / 2) ω * uu (1 / 2) ω' - vv (1 / 2) ω * vv (1 / 2) ω' := dd_hh (by norm_num) hne
  -- ladder
  have hlad : (∑' k, 2 * (1 - tailFactor L k) * hh (bk k) ω
      - ∑' k, 2 * (1 - tailFactor L k) * hh (bk k) ω') / (ω - ω')
      = ∑' k, 2 * (1 - tailFactor L k) * (uu (bk k) ω * uu (bk k) ω' - vv (bk k) ω * vv (bk k) ω') := by
    rw [← Summable.tsum_sub hs hs', ← tsum_div_const]
    refine tsum_congr fun k => ?_
    rw [← dd_hh (bk_pos k) hne]
    field_simp
  -- primes
  have hprime : (∑ p ∈ (Finset.range (P + 1)).filter Nat.Prime, ∑ r ∈ Finset.Icc 1 R,
        Cvs.Zeta.Explicit.Weil.primePowerWeight p r * (2 * sinCut L ω ((r : ℝ) * Real.log p))
      - ∑ p ∈ (Finset.range (P + 1)).filter Nat.Prime, ∑ r ∈ Finset.Icc 1 R,
        Cvs.Zeta.Explicit.Weil.primePowerWeight p r * (2 * sinCut L ω' ((r : ℝ) * Real.log p))) / (ω - ω')
      = ∑ p ∈ (Finset.range (P + 1)).filter Nat.Prime, ∑ r ∈ Finset.Icc 1 R,
        Cvs.Zeta.Explicit.Weil.primePowerWeight p r
          * (2 * (if (r : ℝ) * Real.log p ≤ L then (r : ℝ) * Real.log p
              * Real.cos ((r : ℝ) * Real.log p * (ω + ω') / 2)
              * sinc ((r : ℝ) * Real.log p * (ω - ω') / 2) else 0)) := by
    rw [← Finset.sum_sub_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [← Finset.sum_sub_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun r hr => ?_
    have hp' : p.Prime := (Finset.mem_filter.mp hp).2
    have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
    have ht : 0 < (r : ℝ) * Real.log p := by
      have : (1 : ℝ) ≤ r := by exact_mod_cast hr1
      have : (0:ℝ) < Real.log p := Real.log_pos (by exact_mod_cast hp'.one_lt)
      positivity
    rw [← dd_sinCut ht hne]
    field_simp
  rw [show ω' - ω = -(ω - ω') by ring, div_neg, ← neg_div, neg_sub]
  have key : (Fgen P R L ω' - Fgen P R L ω) = -(Fgen P R L ω - Fgen P R L ω') := by ring
  rw [show ((-2 * Cvs.Finite.PairPoleChannelClosed.poleFactor L * hh (1 / 2) ω'
        - ∑' k, 2 * (1 - tailFactor L k) * hh (bk k) ω'
        - ∑ p ∈ (Finset.range (P + 1)).filter Nat.Prime, ∑ r ∈ Finset.Icc 1 R,
          Cvs.Zeta.Explicit.Weil.primePowerWeight p r * (2 * sinCut L ω' ((r : ℝ) * Real.log p)))
      - (-2 * Cvs.Finite.PairPoleChannelClosed.poleFactor L * hh (1 / 2) ω
        - ∑' k, 2 * (1 - tailFactor L k) * hh (bk k) ω
        - ∑ p ∈ (Finset.range (P + 1)).filter Nat.Prime, ∑ r ∈ Finset.Icc 1 R,
          Cvs.Zeta.Explicit.Weil.primePowerWeight p r * (2 * sinCut L ω ((r : ℝ) * Real.log p))))
      = 2 * Cvs.Finite.PairPoleChannelClosed.poleFactor L * (hh (1 / 2) ω - hh (1 / 2) ω')
        + (∑' k, 2 * (1 - tailFactor L k) * hh (bk k) ω
            - ∑' k, 2 * (1 - tailFactor L k) * hh (bk k) ω')
        + (∑ p ∈ (Finset.range (P + 1)).filter Nat.Prime, ∑ r ∈ Finset.Icc 1 R,
            Cvs.Zeta.Explicit.Weil.primePowerWeight p r * (2 * sinCut L ω ((r : ℝ) * Real.log p))
          - ∑ p ∈ (Finset.range (P + 1)).filter Nat.Prime, ∑ r ∈ Finset.Icc 1 R,
            Cvs.Zeta.Explicit.Weil.primePowerWeight p r * (2 * sinCut L ω' ((r : ℝ) * Real.log p)))
      by ring]
  rw [add_div, add_div, mul_div_assoc, hpole, hlad, hprime]

theorem cutTerm_eq (L : ℝ) (m : ℤ) (k : ℕ) :
    Cvs.Finite.DiagonalLevySymbol.cutTerm L m k
      = 4 * (uu (bk k) (2 * π * m / L) * uu (bk k) (2 * π * m / L)
          - vv (bk k) (2 * π * m / L) * vv (bk k) (2 * π * m / L)) := by
  unfold Cvs.Finite.DiagonalLevySymbol.cutTerm uu vv bk
  have : (0:ℝ) < (1 / 4 + (k : ℝ)) ^ 2 + (π * m / L) ^ 2 := by positivity
  have : (0:ℝ) < (2 * (k : ℝ) + 1 / 2) ^ 2 + (2 * π * m / L) ^ 2 := by positivity
  field_simp
  ring

/-- **On the diagonal**: `diag = symbolCut + (1/L) K(ω, ω)`. -/
theorem diag_eq (P R : ℕ) {L : ℝ} (hL : 0 < L) (m : ℤ) :
    Cvs.Finite.WindowMatrixClosedForm.diag P R L m
      = symbolCut P R L (2 * π * m / L) + 1 / L * kK P R L (2 * π * m / L) (2 * π * m / L) := by
  unfold Cvs.Finite.WindowMatrixClosedForm.diag symbolCut kK kArch kPrime
  rw [← Cvs.Finite.WindowMatrixClosedForm.tsum_cutTerm]
  have hc := Cvs.Finite.DiagonalLevySymbol.summable_cutTerm L m
  have hct := Cvs.Finite.DiagonalLevySymbol.summable_tail_cutTerm hL m
  have hT : ∑' k, Cvs.Finite.DiagonalLevySymbol.cutTerm L m k
      - ∑' k, tailFactor L k * Cvs.Finite.DiagonalLevySymbol.cutTerm L m k
      = 2 * ∑' k, 2 * (1 - tailFactor L k) * (uu (bk k) (2 * π * m / L) * uu (bk k) (2 * π * m / L)
          - vv (bk k) (2 * π * m / L) * vv (bk k) (2 * π * m / L)) := by
    rw [← Summable.tsum_sub hc hct, ← tsum_mul_left]
    refine tsum_congr fun k => ?_
    rw [cutTerm_eq]
    ring
  have hprime : primeSum P R (vcosCut L (2 * π * m / L))
      = ∑ p ∈ (Finset.range (P + 1)).filter Nat.Prime, ∑ r ∈ Finset.Icc 1 R,
        Cvs.Zeta.Explicit.Weil.primePowerWeight p r
          * (2 * (if (r : ℝ) * Real.log p ≤ L then (r : ℝ) * Real.log p
              * Real.cos ((r : ℝ) * Real.log p * (2 * π * m / L + 2 * π * m / L) / 2)
              * sinc ((r : ℝ) * Real.log p * (2 * π * m / L - 2 * π * m / L) / 2) else 0)) := by
    unfold primeSum vcosCut
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun r _ => ?_
    rw [sub_self, mul_zero, zero_div, sinc, if_pos rfl]
    by_cases h : (r : ℝ) * Real.log p ≤ L
    · rw [if_pos h, if_pos h]
      rw [show (r : ℝ) * Real.log p * (2 * π * m / L + 2 * π * m / L) / 2
          = 2 * π * m / L * ((r : ℝ) * Real.log p) by ring]
      ring
    · rw [if_neg h, if_neg h]
  rw [← hprime]
  unfold Cvs.Finite.PairPoleChannelClosed.freq uu vv
  have hL' : L ≠ 0 := hL.ne'
  have hden : (0:ℝ) < (1 / 2) ^ 2 + (2 * π * m / L) ^ 2 := by positivity
  have hden2 : (0:ℝ) < 1 / 4 + (2 * π * m / L) ^ 2 := by positivity
  have hpole : 2 / L * (1 / 4 - (2 * π * m / L) ^ 2) * Cvs.Finite.PairPoleChannelClosed.poleFactor L
        / (1 / 4 + (2 * π * m / L) ^ 2) ^ 2
      = 1 / L * (2 * Cvs.Finite.PairPoleChannelClosed.poleFactor L
          * (1 / 2 / ((1 / 2) ^ 2 + (2 * π * m / L) ^ 2) * (1 / 2 / ((1 / 2) ^ 2 + (2 * π * m / L) ^ 2))
            - 2 * π * m / L / ((1 / 2) ^ 2 + (2 * π * m / L) ^ 2)
              * (2 * π * m / L / ((1 / 2) ^ 2 + (2 * π * m / L) ^ 2)))) := by
    field_simp
    ring
  unfold uu vv at hT
  linear_combination (1 / (2 * L)) * hT + hpole

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The window matrix is the symbol on the diagonal plus `(1/L)` times the kernel.** -/
theorem M_apply_kernel {L : ℝ} (hL : 0 < L) (P R : ℕ) {mode : ι → ℤ}
    (hinj : Function.Injective mode) (i j : ι) :
    Cvs.Finite.TruncationQuadraticForm.M P R L mode i j
      = (if i = j then symbolCut P R L (2 * π * mode i / L) else 0)
        + 1 / L * kK P R L (2 * π * mode i / L) (2 * π * mode j / L) := by
  rw [Cvs.Finite.WindowMatrixClosedForm.M_apply_closed hL P R hinj i j]
  by_cases hij : i = j
  · subst hij; rw [if_pos rfl, if_pos rfl, diag_eq P R hL]
  · rw [if_neg hij, if_neg hij, zero_add, gen_eq_Fgen P R hL, gen_eq_Fgen P R hL]
    have hmn : mode i ≠ mode j := fun h => hij (hinj h)
    have hne : 2 * π * (mode i : ℝ) / L ≠ 2 * π * (mode j : ℝ) / L := by
      intro h
      apply hmn
      have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
      have hL' : L ≠ 0 := hL.ne'
      have : (mode i : ℝ) = mode j := by
        field_simp at h
        linarith
      exact_mod_cast this
    rw [← dd_Fgen P R hL hne]
    have hL' : L ≠ 0 := hL.ne'
    have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
    have hd : 2 * π * ((mode j : ℝ) - mode i) ≠ 0 := by
      have : ((mode j : ℝ) - mode i) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hmn.symm)
      positivity
    have hd2 : 2 * π * (mode j : ℝ) / L - 2 * π * (mode i : ℝ) / L ≠ 0 := sub_ne_zero.mpr hne.symm
    field_simp

/-! ### The archimedean kernel is a sum of squares on even data -/

theorem rank2_quad (c : ℝ) (f g ξ : ι → ℝ) :
    ∑ i, ∑ j, ξ i * ξ j * (c * (f i * f j - g i * g j))
      = c * ((∑ i, ξ i * f i) ^ 2 - (∑ i, ξ i * g i) ^ 2) := by
  rw [sq, sq, Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The archimedean quadratic form, as a sum of squares. -/
theorem quadForm_kArch {L : ℝ} (hL : 0 < L) (ω : ι → ℝ) (ξ : ι → ℝ) :
    ∑ i, ∑ j, ξ i * ξ j * kArch L (ω i) (ω j)
      = 2 * Cvs.Finite.PairPoleChannelClosed.poleFactor L
          * ((∑ i, ξ i * uu (1 / 2) (ω i)) ^ 2 - (∑ i, ξ i * vv (1 / 2) (ω i)) ^ 2)
        + ∑' k, 2 * (1 - tailFactor L k)
          * ((∑ i, ξ i * uu (bk k) (ω i)) ^ 2 - (∑ i, ξ i * vv (bk k) (ω i)) ^ 2) := by
  unfold kArch
  have hs : ∀ i j, Summable fun k => ξ i * ξ j * (2 * (1 - tailFactor L k)
      * (uu (bk k) (ω i) * uu (bk k) (ω j) - vv (bk k) (ω i) * vv (bk k) (ω j))) :=
    fun i j => (summable_ladder_pair hL (ω i) (ω j)).mul_left _
  have h1 : ∀ i j, ξ i * ξ j * (2 * Cvs.Finite.PairPoleChannelClosed.poleFactor L
        * (uu (1 / 2) (ω i) * uu (1 / 2) (ω j) - vv (1 / 2) (ω i) * vv (1 / 2) (ω j))
      + ∑' k, 2 * (1 - tailFactor L k)
        * (uu (bk k) (ω i) * uu (bk k) (ω j) - vv (bk k) (ω i) * vv (bk k) (ω j)))
      = ξ i * ξ j * (2 * Cvs.Finite.PairPoleChannelClosed.poleFactor L
        * (uu (1 / 2) (ω i) * uu (1 / 2) (ω j) - vv (1 / 2) (ω i) * vv (1 / 2) (ω j)))
      + ∑' k, ξ i * ξ j * (2 * (1 - tailFactor L k)
        * (uu (bk k) (ω i) * uu (bk k) (ω j) - vv (bk k) (ω i) * vv (bk k) (ω j))) := by
    intro i j; rw [mul_add, tsum_mul_left]
  simp only [h1, Finset.sum_add_distrib]
  rw [rank2_quad]
  congr 1
  have h2 : ∀ i, ∑ j, ∑' k, ξ i * ξ j * (2 * (1 - tailFactor L k)
      * (uu (bk k) (ω i) * uu (bk k) (ω j) - vv (bk k) (ω i) * vv (bk k) (ω j)))
      = ∑' k, ∑ j, ξ i * ξ j * (2 * (1 - tailFactor L k)
      * (uu (bk k) (ω i) * uu (bk k) (ω j) - vv (bk k) (ω i) * vv (bk k) (ω j))) :=
    fun i => (Summable.tsum_finsetSum fun j _ => hs i j).symm
  simp only [h2]
  rw [← Summable.tsum_finsetSum fun i _ => summable_sum fun j _ => hs i j]
  exact tsum_congr fun k => rank2_quad _ _ _ _

theorem poleFactor_nonneg (L : ℝ) : 0 ≤ Cvs.Finite.PairPoleChannelClosed.poleFactor L := by
  unfold Cvs.Finite.PairPoleChannelClosed.poleFactor
  have hx : 0 < Real.exp (L / 2) := Real.exp_pos _
  have hinv : Real.exp (-(L / 2)) = (Real.exp (L / 2))⁻¹ := by rw [Real.exp_neg]
  rw [hinv]
  have : Real.exp (L / 2) + (Real.exp (L / 2))⁻¹ - 2
      = (Real.exp (L / 2) - 1) ^ 2 / Real.exp (L / 2) := by field_simp; ring
  rw [this]; positivity

/-- **On data annihilated by the odd factors, the archimedean kernel is positive semidefinite.** -/
theorem quadForm_kArch_nonneg {L : ℝ} (hL : 0 < L) (ω : ι → ℝ) (ξ : ι → ℝ)
    (hv : ∀ a : ℝ, 0 < a → ∑ i, ξ i * vv a (ω i) = 0) :
    0 ≤ ∑ i, ∑ j, ξ i * ξ j * kArch L (ω i) (ω j) := by
  rw [quadForm_kArch hL ω ξ, hv (1 / 2) (by norm_num)]
  have hterm : ∀ k, 0 ≤ 2 * (1 - tailFactor L k)
      * ((∑ i, ξ i * uu (bk k) (ω i)) ^ 2 - (∑ i, ξ i * vv (bk k) (ω i)) ^ 2) := by
    intro k
    rw [hv (bk k) (bk_pos k)]
    have : tailFactor L k ≤ 1 := by
      unfold tailFactor; apply Real.exp_le_one_iff.mpr
      have : 0 ≤ (1 / 4 + (k : ℝ)) * (2 * L) := by positivity
      linarith
    have h0 : 0 ≤ 1 - tailFactor L k := by linarith
    have h00 : ((0 : ℝ)) ^ 2 = 0 := by norm_num
    rw [h00, sub_zero]
    positivity
  have h1 : 0 ≤ 2 * Cvs.Finite.PairPoleChannelClosed.poleFactor L
      * ((∑ i, ξ i * uu (1 / 2) (ω i)) ^ 2 - 0 ^ 2) := by
    have := poleFactor_nonneg L
    have h00 : ((0 : ℝ)) ^ 2 = 0 := by norm_num
    rw [h00, sub_zero]; positivity
  exact add_nonneg h1 (tsum_nonneg hterm)

end Cvs.Finite.WindowMatrixSymbolKernel
