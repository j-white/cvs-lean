import Mathlib
import Cvs.Finite.EvenSectorZeroSide
import Cvs.Finite.ModeSumPairValues
import Cvs.Finite.PairFormDividedDifference
import Cvs.Finite.PairingLogGrowth
import Cvs.Finite.TruncationQuadraticForm
import Cvs.Finite.TruncationZeroFreeOffAxes
import Cvs.Upstream.HarmonicLatticeSum
import Cvs.WeilForm.SelfConvolutionFunctional

/-!
# The averaged approximant: fresh modes at both signs, and its window form converges

To an even mode sum with coefficient sum `s` add `N` fresh modes `M₀ < m ≤ M₀ + N`, both signs,
coefficient `−s/2N`: the coefficient sum vanishes, so `Cvs.Finite.EvenSectorZeroSide` puts the approximant on the zero
side. Its window form is the original's plus cross and square double sums of `pairQ` against the
fresh modes; `Cvs.Finite.PairingLogGrowth`'s logarithmic growth and `Cvs.Upstream.HarmonicLatticeSum`'s harmonic sums make those `O((log N)²/N)`.
-/

noncomputable section

open Real Filter Topology

namespace Cvs.Finite.AveragedApproximant
open Cvs.ZeroCounting

/-! ### The fresh modes -/

/-- The fresh index: a mode in `Icc 1 N` and a sign. -/
abbrev J (N : ℕ) := {m : ℕ // m ∈ Finset.Icc 1 N} × Bool

/-- The fresh mode `±(M₀ + m)`. -/
def modeN (M₀ N : ℕ) : J N → ℤ :=
  fun j => if j.2 then ((M₀ : ℤ) + (j.1 : ℕ)) else -((M₀ : ℤ) + (j.1 : ℕ))

/-- The sign flip on the fresh index. -/
def negN (N : ℕ) : J N → J N := fun j => (j.1, !j.2)

theorem negN_involutive (N : ℕ) : Function.Involutive (negN N) := fun j => by simp [negN]

theorem modeN_negN (M₀ N : ℕ) (j : J N) : modeN M₀ N (negN N j) = -modeN M₀ N j := by
  rcases j with ⟨m, b⟩; cases b <;> simp [modeN, negN]

theorem abs_modeN (M₀ N : ℕ) (j : J N) :
    |((modeN M₀ N j : ℤ) : ℝ)| = (M₀ : ℝ) + ((j.1 : ℕ) : ℝ) := by
  rcases j with ⟨m, b⟩
  cases b <;> simp only [modeN, Bool.false_eq_true, ↓reduceIte, Int.cast_neg, Int.cast_add,
    Int.cast_natCast, abs_neg]
  · exact abs_of_nonneg (by positivity)
  · exact abs_of_nonneg (by positivity)

theorem abs_modeN_le (M₀ N : ℕ) (j : J N) : |((modeN M₀ N j : ℤ) : ℝ)| ≤ (M₀ : ℝ) + N := by
  rw [abs_modeN]
  have := (Finset.mem_Icc.mp j.1.2).2
  have : ((j.1 : ℕ) : ℝ) ≤ N := by exact_mod_cast this
  linarith

theorem card_J (N : ℕ) : Fintype.card (J N) = N * 2 := by
  simp [J, Fintype.card_prod, Fintype.card_coe, Nat.card_Icc]

/-! ### Reciprocal-distance sums against the fresh modes -/

/-- The harmonic sum over the fresh index, both signs. -/
theorem sum_inv_J (N : ℕ) : ∑ j : J N, 1 / ((j.1 : ℕ) : ℝ) ≤ 2 * (1 + Real.log N) := by
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  rw [Finset.sum_add_distrib]
  have h := Cvs.Upstream.HarmonicLatticeSum.sum_Icc_inv_le N
  rw [← Finset.sum_coe_sort] at h
  linarith

/-- **An old mode against the fresh ones**: `∑_j 1/|a − m_j| ≤ 2(1 + log N)` when `|a| ≤ M₀`. -/
theorem sum_inv_dist_old (M₀ N : ℕ) {a : ℤ} (ha : |(a : ℝ)| ≤ M₀) :
    ∑ j : J N, 1 / |(a : ℝ) - ((modeN M₀ N j : ℤ) : ℝ)| ≤ 2 * (1 + Real.log N) := by
  refine (Finset.sum_le_sum fun j _ => ?_).trans (sum_inv_J N)
  have hm : (1 : ℝ) ≤ ((j.1 : ℕ) : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp j.1.2).1
  have hdist : ((j.1 : ℕ) : ℝ) ≤ |(a : ℝ) - ((modeN M₀ N j : ℤ) : ℝ)| := by
    have h1 := abs_modeN M₀ N j
    have h2 : |((modeN M₀ N j : ℤ) : ℝ)| - |(a : ℝ)| ≤ |(a : ℝ) - ((modeN M₀ N j : ℤ) : ℝ)| := by
      rw [abs_sub_comm]; exact abs_sub_abs_le_abs_sub _ _
    linarith
  exact one_div_le_one_div_of_le (by linarith) hdist

/-- **A fresh mode against the others**: `∑_{j' ≠ j} 1/|m_j − m_j'| ≤ 5(1 + log N)`. -/
theorem sum_inv_dist_fresh (M₀ N : ℕ) (j : J N) :
    ∑ j' ∈ Finset.univ.erase j, 1 / |((modeN M₀ N j : ℤ) : ℝ) - ((modeN M₀ N j' : ℤ) : ℝ)|
      ≤ 5 * (1 + Real.log N) := by
  classical
  -- fold the erased sum into an indicator sum over everything
  have hfold : ∑ j' ∈ Finset.univ.erase j,
      1 / |((modeN M₀ N j : ℤ) : ℝ) - ((modeN M₀ N j' : ℤ) : ℝ)|
      = ∑ j' : J N, if j' = j then 0
          else 1 / |((modeN M₀ N j : ℤ) : ℝ) - ((modeN M₀ N j' : ℤ) : ℝ)| := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), if_pos rfl, zero_add]
    exact Finset.sum_congr rfl fun j' hj' => by rw [if_neg (Finset.ne_of_mem_erase hj')]
  rw [hfold]
  rcases j with ⟨m, b⟩
  have hm1 : (1 : ℝ) ≤ ((m : ℕ) : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp m.2).1
  -- termwise: the same-sign term is `1/|m − m'|` off `m' = m`, the opposite-sign term `≤ 1/m'`
  have hterm : ∀ j' : J N, (if j' = (m, b) then 0
      else 1 / |((modeN M₀ N (m, b) : ℤ) : ℝ) - ((modeN M₀ N j' : ℤ) : ℝ)|)
      ≤ (if j'.2 = b then (if (j'.1 : ℕ) = m then 0 else 1 / |((j'.1 : ℕ) : ℝ) - ((m : ℕ) : ℝ)|)
          else 1 / ((j'.1 : ℕ) : ℝ)) := by
    rintro ⟨m', b'⟩
    have hm'1 : (1 : ℝ) ≤ ((m' : ℕ) : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp m'.2).1
    by_cases hb : b' = b
    · subst hb
      simp only [if_true]
      by_cases hmm : (m' : ℕ) = m
      · have : m' = m := Subtype.ext hmm
        subst this; simp
      · have hne : (m', b') ≠ (m, b') := fun h => hmm (congrArg (fun p => (p.1 : ℕ)) h)
        rw [if_neg hne, if_neg hmm]
        refine le_of_eq ?_
        congr 1
        cases b' <;> simp only [modeN, Bool.false_eq_true, ↓reduceIte, Int.cast_neg,
          Int.cast_add, Int.cast_natCast]
        · rw [show -((M₀ : ℝ) + (m : ℕ)) - -((M₀ : ℝ) + (m' : ℕ)) = ((m' : ℕ) : ℝ) - (m : ℕ) by ring]
        · rw [show ((M₀ : ℝ) + (m : ℕ)) - ((M₀ : ℝ) + (m' : ℕ)) = -(((m' : ℕ) : ℝ) - (m : ℕ)) by ring,
            abs_neg]
    · have hne : (m', b') ≠ (m, b) := fun h => hb (congrArg Prod.snd h)
      rw [if_neg hne, if_neg hb]
      refine one_div_le_one_div_of_le (by linarith) ?_
      have hb' : b' = !b := by cases b <;> cases b' <;> simp_all
      subst hb'
      cases b <;> simp only [modeN, Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte,
        Int.cast_neg, Int.cast_add, Int.cast_natCast]
      · rw [show -((M₀ : ℝ) + (m : ℕ)) - ((M₀ : ℝ) + (m' : ℕ))
          = -(2 * (M₀ : ℝ) + (m : ℕ) + (m' : ℕ)) by ring, abs_neg,
          abs_of_nonneg (by positivity)]
        linarith [(Nat.cast_nonneg M₀ : (0:ℝ) ≤ M₀)]
      · rw [show ((M₀ : ℝ) + (m : ℕ)) - -((M₀ : ℝ) + (m' : ℕ))
          = 2 * (M₀ : ℝ) + (m : ℕ) + (m' : ℕ) by ring, abs_of_nonneg (by positivity)]
        linarith [(Nat.cast_nonneg M₀ : (0:ℝ) ≤ M₀)]
  refine (Finset.sum_le_sum fun j' _ => hterm j').trans ?_
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  -- split into the same-sign and opposite-sign columns
  have hsplit : ∀ m' : {m : ℕ // m ∈ Finset.Icc 1 N},
      ((if true = b then (if (m' : ℕ) = m then 0 else 1 / |((m' : ℕ) : ℝ) - ((m : ℕ) : ℝ)|)
          else 1 / ((m' : ℕ) : ℝ))
        + (if false = b then (if (m' : ℕ) = m then 0 else 1 / |((m' : ℕ) : ℝ) - ((m : ℕ) : ℝ)|)
          else 1 / ((m' : ℕ) : ℝ)))
      = (if (m' : ℕ) = m then 0 else 1 / |((m' : ℕ) : ℝ) - ((m : ℕ) : ℝ)|)
        + 1 / ((m' : ℕ) : ℝ) := by
    intro m'
    cases b <;> (simp only [Bool.true_eq_false, Bool.false_eq_true, if_true, if_false]; try ring)
  simp only [hsplit]
  rw [Finset.sum_add_distrib]
  have hA : ∑ m' : {m : ℕ // m ∈ Finset.Icc 1 N},
      (if (m' : ℕ) = m then 0 else 1 / |((m' : ℕ) : ℝ) - ((m : ℕ) : ℝ)|)
      ≤ 3 * (1 + Real.log N) := by
    rw [Finset.sum_coe_sort (Finset.Icc 1 N)
      (fun m' : ℕ => if m' = m then 0 else 1 / |(m' : ℝ) - ((m : ℕ) : ℝ)|)]
    have h := Cvs.Upstream.HarmonicLatticeSum.sum_inv_dist_le (b := ((m : ℕ) : ℝ)) (by positivity) N
    rw [Finset.sum_filter] at h
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun m' _ => ?_)) h
    by_cases hmm : m' = m
    · subst hmm
      rw [if_pos rfl, if_neg]
      simp
    · rw [if_neg hmm, if_pos]
      have : ((m' : ℤ) : ℝ) - ((m : ℕ) : ℤ) ≠ 0 := by
        rw [sub_ne_zero]; exact_mod_cast hmm
      have h1 : (1 : ℤ) ≤ |(m' : ℤ) - ((m : ℕ) : ℤ)| :=
        Int.one_le_abs (sub_ne_zero.mpr (by exact_mod_cast hmm))
      have h2 : ((1 : ℤ) : ℝ) ≤ ((|(m' : ℤ) - ((m : ℕ) : ℤ)| : ℤ) : ℝ) := by exact_mod_cast h1
      rw [Int.cast_abs, Int.cast_sub, Int.cast_natCast, Int.cast_natCast, Int.cast_one] at h2
      exact h2
  have hB : ∑ m' : {m : ℕ // m ∈ Finset.Icc 1 N}, 1 / ((m' : ℕ) : ℝ) ≤ 1 + Real.log N := by
    rw [Finset.sum_coe_sort (Finset.Icc 1 N) (fun m' : ℕ => 1 / (m' : ℝ))]
    exact Cvs.Upstream.HarmonicLatticeSum.sum_Icc_inv_le N
  refine (add_le_add hA hB).trans ?_
  have := Real.log_natCast_nonneg N
  linarith

/-! ### The extended index -/

variable {ι : Type*} [Fintype ι]

/-- The modes of the extended index: the old ones, then the fresh ones. -/
def modeE (mode : ι → ℤ) (M₀ N : ℕ) : ι ⊕ J N → ℤ := Sum.elim mode (modeN M₀ N)

/-- The coefficients of the extended index: the old ones, then `−s/2N` on every fresh mode. -/
def xiE (xi : ι → ℝ) (N : ℕ) : ι ⊕ J N → ℝ := Sum.elim xi (fun _ => -(∑ i, xi i) / (2 * N))

/-- The involution of the extended index. -/
def negE (neg : ι → ι) (N : ℕ) : ι ⊕ J N → ι ⊕ J N := Sum.map neg (negN N)

omit [Fintype ι] in
theorem negE_involutive {neg : ι → ι} (hinv : Function.Involutive neg) (N : ℕ) :
    Function.Involutive (negE neg N) := by
  rintro (i | j)
  · simp [negE, hinv i]
  · simp [negE, negN_involutive N j]

omit [Fintype ι] in
theorem modeE_negE {mode : ι → ℤ} {neg : ι → ι} (hmode : ∀ i, mode (neg i) = -mode i)
    (M₀ N : ℕ) (i : ι ⊕ J N) : modeE mode M₀ N (negE neg N i) = -modeE mode M₀ N i := by
  rcases i with i | j
  · simp [modeE, negE, hmode]
  · simp [modeE, negE, modeN_negN]

theorem xiE_negE {xi : ι → ℝ} {neg : ι → ι} (hxieven : ∀ i, xi (neg i) = xi i) (N : ℕ)
    (i : ι ⊕ J N) : xiE xi N (negE neg N i) = xiE xi N i := by
  rcases i with i | j <;> simp [xiE, negE, hxieven]

/-- **The extended coefficient sum vanishes.** -/
theorem sum_xiE (xi : ι → ℝ) {N : ℕ} (hN : 1 ≤ N) : ∑ i, xiE xi N i = 0 := by
  rw [Fintype.sum_sum_type]
  simp only [xiE, Sum.elim_inl, Sum.elim_inr, Finset.sum_const, Finset.card_univ, card_J,
    nsmul_eq_mul]
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  push_cast
  field_simp
  ring

/-- **The extended cosine polynomial is the old one minus `s` times the averaged fresh cosines.** -/
theorem cosPoly_E (L : ℝ) (mode : ι → ℤ) (xi : ι → ℝ) (M₀ N : ℕ) (y : ℝ) :
    Cvs.Finite.EvenSectorZeroSide.cosPoly L (modeE mode M₀ N) (xiE xi N) y
      = Cvs.Finite.EvenSectorZeroSide.cosPoly L mode xi y
        - (∑ i, xi i) / N * ∑ m : {m : ℕ // m ∈ Finset.Icc 1 N},
            Real.cos (2 * π * ((M₀ : ℝ) + (m : ℕ)) / L * y) := by
  unfold Cvs.Finite.EvenSectorZeroSide.cosPoly
  rw [Fintype.sum_sum_type]
  simp only [xiE, modeE, Cvs.Finite.TruncationZeroFreeOffAxes.omega, Sum.elim_inl, Sum.elim_inr]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  have hpair : ∀ m : {m : ℕ // m ∈ Finset.Icc 1 N},
      -(∑ i, xi i) / (2 * N) * Real.cos (2 * π * ((modeN M₀ N (m, true) : ℤ) : ℝ) / L * y)
        + -(∑ i, xi i) / (2 * N)
          * Real.cos (2 * π * ((modeN M₀ N (m, false) : ℤ) : ℝ) / L * y)
      = -((∑ i, xi i) / N * Real.cos (2 * π * ((M₀ : ℝ) + (m : ℕ)) / L * y)) := by
    intro m
    simp only [modeN, Bool.false_eq_true, ↓reduceIte, Int.cast_neg, Int.cast_add, Int.cast_natCast]
    rw [show 2 * π * -((M₀ : ℝ) + (m : ℕ)) / L * y = -(2 * π * ((M₀ : ℝ) + (m : ℕ)) / L * y) by
      ring, Real.cos_neg]
    rcases em ((N : ℝ) = 0) with hN | hN
    · rw [hN]; simp
    · field_simp
      ring
  have hsum : ∑ m : {m : ℕ // m ∈ Finset.Icc 1 N},
      (-(∑ i, xi i) / (2 * N) * Real.cos (2 * π * ((modeN M₀ N (m, true) : ℤ) : ℝ) / L * y)
        + -(∑ i, xi i) / (2 * N)
          * Real.cos (2 * π * ((modeN M₀ N (m, false) : ℤ) : ℝ) / L * y))
      = ∑ m : {m : ℕ // m ∈ Finset.Icc 1 N},
          -((∑ i, xi i) / N * Real.cos (2 * π * ((M₀ : ℝ) + (m : ℕ)) / L * y)) :=
    Finset.sum_congr rfl fun m _ => hpair m
  rw [hsum, Finset.sum_neg_distrib, ← Finset.mul_sum]
  ring

/-! ### The window form of the extension -/

/-- **The off-diagonal pair value against a common bound on `bval`.** -/
theorem abs_pairQ_off_le {L : ℝ} (hL : 0 < L) (P R : ℕ) {m n : ℤ} (hmn : m ≠ n) {B : ℝ}
    (hm : |Cvs.Finite.PairFormDividedDifference.bval P R L m| ≤ B)
    (hn : |Cvs.Finite.PairFormDividedDifference.bval P R L n| ≤ B) :
    |Cvs.Finite.ModeSumPairValues.pairQ P R L m n| ≤ (2 * L * B / π) / |(m : ℝ) - n| := by
  have hπ : 0 < π := Real.pi_pos
  have h := Cvs.Finite.PairFormDividedDifference.pairQ_off hL P R hmn
  have hmn' : (m : ℝ) - n ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hmn)
  have hden : 2 * π * m / L - 2 * π * n / L = 2 * π * ((m : ℝ) - n) / L := by ring
  rw [hden] at h
  have hval : Cvs.Finite.ModeSumPairValues.pairQ P R L m n
      = L * (Cvs.Finite.PairFormDividedDifference.bval P R L m - Cvs.Finite.PairFormDividedDifference.bval P R L n)
        / (π * ((m : ℝ) - n)) := by
    have h2 : Cvs.Finite.ModeSumPairValues.pairQ P R L m n
        = 2 * ((Cvs.Finite.PairFormDividedDifference.bval P R L m - Cvs.Finite.PairFormDividedDifference.bval P R L n)
          / (2 * π * ((m : ℝ) - n) / L)) := by linarith [h]
    rw [h2]
    field_simp
  rw [hval, abs_div, abs_mul, abs_mul, abs_of_pos hL, abs_of_pos hπ]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hB : |Cvs.Finite.PairFormDividedDifference.bval P R L m - Cvs.Finite.PairFormDividedDifference.bval P R L n| ≤ 2 * B := by
    calc _ ≤ |Cvs.Finite.PairFormDividedDifference.bval P R L m| + |Cvs.Finite.PairFormDividedDifference.bval P R L n| :=
          abs_sub _ _
      _ ≤ 2 * B := by linarith
  have hpos : 0 < |(m : ℝ) - n| := abs_pos.mpr hmn'
  rw [show 2 * L * B / π * (π * |(m : ℝ) - n|) = 2 * B * (L * |(m : ℝ) - n|) by
    field_simp]
  have h3 := mul_le_mul_of_nonneg_right hB (by positivity : (0:ℝ) ≤ L * |(m : ℝ) - n|)
  linarith [h3]

/-- The logarithmic size of the modes in play. -/
def ell (M₀ N : ℕ) : ℝ := 1 + Real.log (1 + M₀ + N)

theorem one_le_ell (M₀ N : ℕ) : 1 ≤ ell M₀ N := by
  unfold ell
  linarith [Real.log_nonneg (by linarith [(Nat.cast_nonneg M₀ : (0:ℝ) ≤ M₀),
    (Nat.cast_nonneg N : (0:ℝ) ≤ N)] : (1:ℝ) ≤ 1 + M₀ + N)]

theorem log_N_le_ell (M₀ N : ℕ) : 1 + Real.log N ≤ ell M₀ N := by
  unfold ell
  have hM : (0:ℝ) ≤ M₀ := Nat.cast_nonneg M₀
  have h1 : Real.log N ≤ Real.log (1 + M₀ + N) := by
    rcases Nat.eq_zero_or_pos N with h | h
    · rw [h, Nat.cast_zero, Real.log_zero]
      exact Real.log_nonneg (by linarith)
    · have : (0:ℝ) < N := by exact_mod_cast h
      exact Real.log_le_log this (by linarith)
  linarith

/-- A logarithmic bound at `|k| ≤ M₀ + N` is at most `ell`. -/
theorem log_mode_le_ell (M₀ N : ℕ) {k : ℝ} (hk : |k| ≤ (M₀ : ℝ) + N) :
    1 + Real.log (1 + |k|) ≤ ell M₀ N := by
  unfold ell
  linarith [Real.log_le_log (by linarith [abs_nonneg k]) (by linarith : 1 + |k| ≤ 1 + M₀ + N)]

/-- A diagonal bound at `|k| ≤ M₀ + N` is at most `2·ell`. -/
theorem log_diag_le_ell (M₀ N : ℕ) {k : ℝ} (hk : |k| ≤ (M₀ : ℝ) + N) :
    1 + Real.log (1 + (|k| + |k|)) ≤ 2 * ell M₀ N := by
  unfold ell
  have h1 : 1 + (|k| + |k|) ≤ 2 * (1 + M₀ + N) := by linarith
  have h2 := Real.log_le_log (by linarith [abs_nonneg k]) h1
  rw [Real.log_mul (by norm_num) (by linarith [(Nat.cast_nonneg M₀ : (0:ℝ) ≤ M₀),
    (Nat.cast_nonneg N : (0:ℝ) ≤ N)])] at h2
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_two_lt_d9; linarith
  have hnn : 0 ≤ Real.log (1 + M₀ + N) := Real.log_nonneg (by
    linarith [(Nat.cast_nonneg M₀ : (0:ℝ) ≤ M₀), (Nat.cast_nonneg N : (0:ℝ) ≤ N)])
  linarith

/-- **The cross term is `O(ell²/N)`.** -/
theorem abs_cross_le {L : ℝ} (hL : 0 < L) (P R : ℕ) (mode : ι → ℤ) (xi : ι → ℝ) (M₀ : ℕ)
    (hM₀ : ∀ i, |((mode i : ℤ) : ℝ)| ≤ M₀) {c' : ℝ} (hc'0 : 0 ≤ c')
    (hc' : ∀ k : ℤ, |Cvs.Finite.PairFormDividedDifference.bval P R L k| ≤ c' * (1 + Real.log (1 + |(k:ℝ)|)))
    {N : ℕ} (hN : 1 ≤ N) :
    |∑ i, ∑ j : J N, xi i * (-(∑ i, xi i) / (2 * N))
        * Cvs.Finite.ModeSumPairValues.pairQ P R L (mode i) (modeN M₀ N j)|
      ≤ (∑ i, |xi i|) * |∑ i, xi i| * (2 * L * c' / π) * ell M₀ N ^ 2 / N := by
  have hπ : 0 < π := Real.pi_pos
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  set s := ∑ i, xi i with hs
  set B := c' * ell M₀ N with hB
  have hB0 : 0 ≤ B := mul_nonneg hc'0 (by linarith [one_le_ell M₀ N])
  -- every mode in play has `|bval| ≤ B`
  have hbv : ∀ k : ℤ, |(k:ℝ)| ≤ (M₀ : ℝ) + N → |Cvs.Finite.PairFormDividedDifference.bval P R L k| ≤ B := by
    intro k hk
    exact (hc' k).trans (mul_le_mul_of_nonneg_left (log_mode_le_ell M₀ N hk) hc'0)
  have hrow : ∀ i, |∑ j : J N, xi i * (-s / (2 * N))
      * Cvs.Finite.ModeSumPairValues.pairQ P R L (mode i) (modeN M₀ N j)|
      ≤ |xi i| * (|s| / (2 * N)) * ((2 * L * B / π) * (2 * (1 + Real.log N))) := by
    intro i
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ j : J N, |xi i * (-s / (2 * N))
        * Cvs.Finite.ModeSumPairValues.pairQ P R L (mode i) (modeN M₀ N j)|
        ≤ |xi i| * (|s| / (2 * N)) * ((2 * L * B / π)
          * (1 / |((mode i : ℤ) : ℝ) - ((modeN M₀ N j : ℤ) : ℝ)|)) := by
      intro j
      rw [abs_mul, abs_mul, abs_div, abs_neg, abs_of_pos (by positivity : (0:ℝ) < 2 * N)]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have hne : mode i ≠ modeN M₀ N j := by
        intro h
        have h1 := hM₀ i
        have h2 := abs_modeN M₀ N j
        have hm1 : (1:ℝ) ≤ ((j.1 : ℕ) : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp j.1.2).1
        rw [h] at h1
        linarith
      have h := abs_pairQ_off_le hL P R hne (hbv _ ((hM₀ i).trans (by linarith)))
        (hbv _ (abs_modeN_le M₀ N j))
      rw [div_eq_mul_one_div] at h
      exact h
    refine (Finset.sum_le_sum fun j _ => hterm j).trans ?_
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity))
      (by positivity)
    exact sum_inv_dist_old M₀ N (hM₀ i)
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun i _ => hrow i).trans ?_)
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  have hlogN := log_N_le_ell M₀ N
  have hell := one_le_ell M₀ N
  have hX : 0 ≤ ∑ i, |xi i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  rw [hB]
  have key : (|s| / (2 * N)) * ((2 * L * (c' * ell M₀ N) / π) * (2 * (1 + Real.log N)))
      ≤ |s| * (2 * L * c' / π) * ell M₀ N ^ 2 / N := by
    rw [show |s| * (2 * L * c' / π) * ell M₀ N ^ 2 / N
        = (|s| / (2 * N)) * ((2 * L * (c' * ell M₀ N) / π) * (2 * ell M₀ N)) by
      field_simp]
    gcongr
  calc (∑ i, |xi i|) * (|s| / (2 * N)) * ((2 * L * (c' * ell M₀ N) / π) * (2 * (1 + Real.log N)))
      = (∑ i, |xi i|) * ((|s| / (2 * N))
          * ((2 * L * (c' * ell M₀ N) / π) * (2 * (1 + Real.log N)))) := by ring
    _ ≤ (∑ i, |xi i|) * (|s| * (2 * L * c' / π) * ell M₀ N ^ 2 / N) :=
        mul_le_mul_of_nonneg_left key hX
    _ = _ := by ring

/-- **The square term is `O(ell²/N)`.** -/
theorem abs_square_le {L : ℝ} (hL : 0 < L) (P R : ℕ) (s : ℝ) (M₀ : ℕ) {c c' : ℝ}
    (hc0 : 0 ≤ c)
    (hc : ∀ m n : ℤ, |Cvs.Finite.ModeSumPairValues.pairQ P R L m n|
      ≤ c * (1 + Real.log (1 + (|(m:ℝ)| + |(n:ℝ)|))))
    (hc'0 : 0 ≤ c')
    (hc' : ∀ k : ℤ, |Cvs.Finite.PairFormDividedDifference.bval P R L k| ≤ c' * (1 + Real.log (1 + |(k:ℝ)|)))
    {N : ℕ} (hN : 1 ≤ N) :
    |∑ j : J N, ∑ j' : J N, (-s / (2 * N)) * (-s / (2 * N))
        * Cvs.Finite.ModeSumPairValues.pairQ P R L (modeN M₀ N j) (modeN M₀ N j')|
      ≤ s ^ 2 / (2 * N) * (2 * c + 10 * L * c' / π) * ell M₀ N ^ 2 := by
  classical
  have hπ : 0 < π := Real.pi_pos
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  set B := c' * ell M₀ N with hB
  have hell := one_le_ell M₀ N
  have hlogN := log_N_le_ell M₀ N
  have hB0 : 0 ≤ B := mul_nonneg hc'0 (by linarith)
  have hbv : ∀ k : ℤ, |(k:ℝ)| ≤ (M₀ : ℝ) + N → |Cvs.Finite.PairFormDividedDifference.bval P R L k| ≤ B := by
    intro k hk
    exact (hc' k).trans (mul_le_mul_of_nonneg_left (log_mode_le_ell M₀ N hk) hc'0)
  -- one row: the diagonal entry plus the off-diagonal ones
  have hrow : ∀ j : J N, |∑ j' : J N, (-s / (2 * N)) * (-s / (2 * N))
      * Cvs.Finite.ModeSumPairValues.pairQ P R L (modeN M₀ N j) (modeN M₀ N j')|
      ≤ (s ^ 2 / (4 * N ^ 2)) * (2 * c * ell M₀ N
          + (2 * L * B / π) * (5 * (1 + Real.log N))) := by
    intro j
    rw [← Finset.mul_sum, abs_mul, show (-s / (2 * N)) * (-s / (2 * N)) = s ^ 2 / (4 * N ^ 2) by
      field_simp; ring, abs_of_nonneg (by positivity : (0:ℝ) ≤ s ^ 2 / (4 * N ^ 2))]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · refine (hc _ _).trans ?_
      have := log_diag_le_ell M₀ N (abs_modeN_le M₀ N j)
      nlinarith
    · refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have hterm : ∀ j' ∈ Finset.univ.erase j,
          |Cvs.Finite.ModeSumPairValues.pairQ P R L (modeN M₀ N j) (modeN M₀ N j')|
          ≤ (2 * L * B / π) * (1 / |((modeN M₀ N j : ℤ) : ℝ) - ((modeN M₀ N j' : ℤ) : ℝ)|) := by
        intro j' hj'
        have hne : modeN M₀ N j ≠ modeN M₀ N j' := by
          intro h
          apply Finset.ne_of_mem_erase hj'
          rcases j with ⟨m, b⟩; rcases j' with ⟨m', b'⟩
          simp only [modeN] at h
          have hm1 : (1:ℤ) ≤ (m : ℕ) := by exact_mod_cast (Finset.mem_Icc.mp m.2).1
          have hm'1 : (1:ℤ) ≤ (m' : ℕ) := by exact_mod_cast (Finset.mem_Icc.mp m'.2).1
          cases b <;> cases b' <;> simp only [Bool.false_eq_true, ↓reduceIte] at h
          · have : (m : ℕ) = m' := by omega
            rw [Subtype.ext this]
          · omega
          · omega
          · have : (m : ℕ) = m' := by omega
            rw [Subtype.ext this]
        have h := abs_pairQ_off_le hL P R hne (hbv _ (abs_modeN_le M₀ N j))
          (hbv _ (abs_modeN_le M₀ N j'))
        rw [div_eq_mul_one_div] at h
        exact h
      refine (Finset.sum_le_sum hterm).trans ?_
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (sum_inv_dist_fresh M₀ N j) (by positivity)
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun j _ => hrow j).trans ?_)
  rw [Finset.sum_const, Finset.card_univ, card_J, nsmul_eq_mul]
  push_cast
  rw [hB]
  have h5 : 5 * (1 + Real.log N) ≤ 5 * ell M₀ N := by linarith
  have key : (2 * L * (c' * ell M₀ N) / π) * (5 * (1 + Real.log N))
      ≤ (10 * L * c' / π) * ell M₀ N ^ 2 := by
    calc (2 * L * (c' * ell M₀ N) / π) * (5 * (1 + Real.log N))
        ≤ (2 * L * (c' * ell M₀ N) / π) * (5 * ell M₀ N) :=
          mul_le_mul_of_nonneg_left h5 (by positivity)
      _ = (10 * L * c' / π) * ell M₀ N ^ 2 := by ring
  have hdiag : 2 * c * ell M₀ N ≤ 2 * c * ell M₀ N ^ 2 := by
    have : ell M₀ N ≤ ell M₀ N ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_left this (by positivity)
  calc (N : ℝ) * 2 * ((s ^ 2 / (4 * N ^ 2)) * (2 * c * ell M₀ N
        + (2 * L * (c' * ell M₀ N) / π) * (5 * (1 + Real.log N))))
      ≤ (N : ℝ) * 2 * ((s ^ 2 / (4 * N ^ 2)) * (2 * c * ell M₀ N ^ 2
        + (10 * L * c' / π) * ell M₀ N ^ 2)) := by gcongr
    _ = s ^ 2 / (2 * N) * (2 * c + 10 * L * c' / π) * ell M₀ N ^ 2 := by
      field_simp; ring

/-- **The window form of the extension**: the original plus cross and square terms. -/
theorem weilForm_E_eq {L : ℝ} (hL : 0 < L) (P R : ℕ) (mode : ι → ℤ) {neg : ι → ι}
    (hinv : Function.Involutive neg) (hmode : ∀ i, mode (neg i) = -mode i) {xi : ι → ℝ}
    (hxieven : ∀ i, xi (neg i) = xi i) (M₀ N : ℕ) :
    Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L (modeE mode M₀ N) (xiE xi N))
      = Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L mode xi)
        + L / 2 * (2 * ∑ i, ∑ j : J N, xi i * (-(∑ i, xi i) / (2 * N))
            * Cvs.Finite.ModeSumPairValues.pairQ P R L (mode i) (modeN M₀ N j)
          + ∑ j : J N, ∑ j' : J N, (-(∑ i, xi i) / (2 * N)) * (-(∑ i, xi i) / (2 * N))
            * Cvs.Finite.ModeSumPairValues.pairQ P R L (modeN M₀ N j) (modeN M₀ N j')) := by
  classical
  rw [Cvs.Finite.ModeSumPairValues.weilForm_modeSum hL P R _ (negE_involutive hinv N)
    (modeE_negE hmode M₀ N) (xiE_negE hxieven N),
    Cvs.Finite.ModeSumPairValues.weilForm_modeSum hL P R mode hinv hmode hxieven]
  simp only [Fintype.sum_sum_type, xiE, modeE, Sum.elim_inl, Sum.elim_inr]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hC : ∑ j : J N, ∑ i, (-(∑ i, xi i) / (2 * N)) * xi i
      * Cvs.Finite.ModeSumPairValues.pairQ P R L (modeN M₀ N j) (mode i)
      = ∑ i, ∑ j : J N, xi i * (-(∑ i, xi i) / (2 * N))
      * Cvs.Finite.ModeSumPairValues.pairQ P R L (mode i) (modeN M₀ N j) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Cvs.Finite.TruncationQuadraticForm.pairQ_symm hL]
    ring
  rw [hC]
  ring

/-- The logarithmic factor divided by `N` vanishes. -/
theorem tendsto_ell_sq_div (M₀ : ℕ) :
    Tendsto (fun N : ℕ => ell M₀ N ^ 2 / N) atTop (𝓝 0) := by
  have h1 : Tendsto (fun N : ℕ => Real.log (1 + M₀ + N) ^ 2 / (1 * (1 + M₀ + N) + -(1 + M₀)))
      atTop (𝓝 0) := by
    have := Real.tendsto_pow_log_div_mul_add_atTop 1 (-(1 + M₀)) 2 one_ne_zero
    refine this.comp ?_
    have : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    exact tendsto_atTop_add_const_left _ _ this
  have h2 : Tendsto (fun N : ℕ => (2 : ℝ) / N) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat 2
  have h3 : Tendsto (fun N : ℕ => (2 : ℝ) / N + 2 * (Real.log (1 + M₀ + N) ^ 2
      / (1 * (1 + M₀ + N) + -(1 + M₀)))) atTop (𝓝 0) := by
    have := h2.add (h1.const_mul 2)
    simpa using this
  refine squeeze_zero (fun N => by positivity) (fun N => ?_) h3
  unfold ell
  rw [show (1 : ℝ) * (1 + M₀ + N) + -(1 + M₀) = N by ring]
  rcases Nat.eq_zero_or_pos N with h | h
  · subst h; simp
  · have hN : (0:ℝ) < N := by exact_mod_cast h
    rw [show (2 : ℝ) / N + 2 * (Real.log (1 + M₀ + N) ^ 2 / N)
        = (2 + 2 * Real.log (1 + M₀ + N) ^ 2) / N by field_simp]
    exact div_le_div_of_nonneg_right (by nlinarith [sq_nonneg (1 - Real.log (1 + M₀ + N))]) hN.le

/-- **The window form of the extension is within `K·ell²/N` of the original.** -/
theorem exists_weilForm_E_bound {L : ℝ} (hL : 0 < L) (P R : ℕ) (mode : ι → ℤ) {neg : ι → ι}
    (hinv : Function.Involutive neg) (hmode : ∀ i, mode (neg i) = -mode i) {xi : ι → ℝ}
    (hxieven : ∀ i, xi (neg i) = xi i) (M₀ : ℕ) (hM₀ : ∀ i, |((mode i : ℤ) : ℝ)| ≤ M₀) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 1 ≤ N →
      |Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R
          (Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L (modeE mode M₀ N) (xiE xi N))
        - Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L mode xi)|
        ≤ K * (ell M₀ N ^ 2 / N) := by
  have hπ : 0 < π := Real.pi_pos
  obtain ⟨c, hc0, hc⟩ := Cvs.Finite.PairingLogGrowth.exists_pairQ_bound hL P R
  obtain ⟨c', hc'0, hc'⟩ := Cvs.Finite.PairingLogGrowth.exists_bval_bound hL P R
  set s := ∑ i, xi i with hs
  set X := ∑ i, |xi i| with hX
  have hX0 : 0 ≤ X := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨L / 2 * (2 * (X * |s| * (2 * L * c' / π)) + s ^ 2 / 2 * (2 * c + 10 * L * c' / π)),
    ?_, fun N hN => ?_⟩
  · positivity
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  rw [weilForm_E_eq hL P R mode hinv hmode hxieven M₀ N, add_sub_cancel_left, abs_mul,
    abs_of_pos (by positivity : (0:ℝ) < L / 2), mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity : (0:ℝ) ≤ L / 2)
  have hcross := abs_cross_le hL P R mode xi M₀ hM₀ hc'0 hc' hN
  have hsq := abs_square_le hL P R s M₀ hc0 hc hc'0 hc' (N := N) hN
  rw [← hs, ← hX] at hcross
  calc _ ≤ |2 * ∑ i, ∑ j : J N, xi i * (-s / (2 * N))
          * Cvs.Finite.ModeSumPairValues.pairQ P R L (mode i) (modeN M₀ N j)|
        + |∑ j : J N, ∑ j' : J N, (-s / (2 * N)) * (-s / (2 * N))
          * Cvs.Finite.ModeSumPairValues.pairQ P R L (modeN M₀ N j) (modeN M₀ N j')| := abs_add_le _ _
    _ ≤ 2 * (X * |s| * (2 * L * c' / π) * ell M₀ N ^ 2 / N)
        + s ^ 2 / (2 * N) * (2 * c + 10 * L * c' / π) * ell M₀ N ^ 2 := by
        rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
        gcongr
    _ = _ := by field_simp

/-- **The window forms converge along the extension.** -/
theorem tendsto_weilForm_E {L : ℝ} (hL : 0 < L) (P R : ℕ) (mode : ι → ℤ) {neg : ι → ι}
    (hinv : Function.Involutive neg) (hmode : ∀ i, mode (neg i) = -mode i) {xi : ι → ℝ}
    (hxieven : ∀ i, xi (neg i) = xi i) (M₀ : ℕ) (hM₀ : ∀ i, |((mode i : ℤ) : ℝ)| ≤ M₀) :
    Tendsto (fun N : ℕ => Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R
        (Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L (modeE mode M₀ N) (xiE xi N))) atTop
      (𝓝 (Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L mode xi))) := by
  obtain ⟨K, hK0, hK⟩ := exists_weilForm_E_bound hL P R mode hinv hmode hxieven M₀ hM₀
  rw [← tendsto_sub_nhds_zero_iff]
  have hlim : Tendsto (fun N : ℕ => K * (ell M₀ N ^ 2 / N)) atTop (𝓝 0) := by
    simpa using (tendsto_ell_sq_div M₀).const_mul K
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN
  rw [Real.norm_eq_abs]
  exact hK N hN

end Cvs.Finite.AveragedApproximant
