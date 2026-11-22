import Mathlib
import Cvs.Finite.DiagonalCutSymbol
import Cvs.Finite.DiagonalLevySymbol
import Cvs.Finite.OneModeEntries
import Cvs.Finite.PairPoleChannelClosed
import Cvs.Finite.WindowMatrixClosedForm
import Cvs.Finite.WindowMatrixSymbolKernel
import Cvs.StepA.PosDefOffLattice
import Cvs.StepA.WindowGeneratorZeros
import Cvs.Upstream.SawtoothPartialSums
import Cvs.WeilForm.Archimedean.PoleFreeEntryBounds
import Cvs.WeilForm.Archimedean.SymbolImaginaryHalf
import Cvs.WeilForm.CouplingAngle
import Cvs.Zeta.GaussKernel.DivisorWeightCoordinates
import Cvs.Zeta.GaussKernel.ZetaZeroStatement
import Cvs.Zeta.PrimePowerSideTruncated
import Cvs.Zeta.ZeroCounting.FinitelyManyBelowOrdinate
import Cvs.Zeta.ZeroSideMoments

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Infinitely many zeros off `1/2 + 2πiℤ/L`

The window generator has Cesàro mean `−π/2`: its archimedean part tends to `−π/2` and the prime sine
sums have bounded partial sums. A zero on the line at an ordinate in `2πℤ/L` adds nothing to `gen`, so
for every `L > 0` infinitely many zeros are not of the form `1/2 + 2πik/L`, and the off-lattice squared
ordinates are infinite when finitely many zeros lie off the line at such ordinates.
-/

noncomputable section

open Real Matrix Filter Topology Cvs.WeilForm.SelfConvolutionTransform

namespace Cvs.StepA.InfinitelyManyOffLattice
open Cvs.ZeroCounting

open Cvs.Zeta.GaussKernel.AdmissibleKernel (nonTrivialZeroSet)

/-- The zeros that are not on the critical line at an ordinate in `2πℤ/L`. -/
def latticeExc (L : ℝ) : Set nonTrivialZeroSet :=
  {rho | ¬ ((rho : ℂ).re = 1 / 2 ∧ ∃ k : ℤ, (rho : ℂ).im * L = 2 * π * k)}

/-! ### The generator's Cesàro mean is `−π/2` -/

/-- For `ω ≠ 0`, `|2·poleSin L ω| ≤ 2·poleFactor L/|ω|`. -/
theorem abs_two_poleSin_le (L : ℝ) {ω : ℝ} (hω : ω ≠ 0) :
    |2 * Cvs.Finite.OneModeEntries.poleSin L ω| ≤ 2 * Cvs.Finite.PairPoleChannelClosed.poleFactor L / |ω| := by
  rw [Cvs.Finite.WindowMatrixSymbolKernel.two_poleSin]
  have hF := Cvs.Finite.WindowMatrixSymbolKernel.poleFactor_nonneg L
  have hden : (0 : ℝ) < (1 / 2) ^ 2 + ω ^ 2 := by positivity
  have hω' : 0 < |ω| := abs_pos.mpr hω
  have hhh : |Cvs.Finite.WindowMatrixSymbolKernel.hh (1 / 2) ω| ≤ 1 / |ω| := by
    unfold Cvs.Finite.WindowMatrixSymbolKernel.hh
    rw [abs_div, abs_of_pos hden, div_le_div_iff₀ hden hω']
    nlinarith [sq_abs ω]
  rw [abs_mul, abs_mul, abs_of_nonneg hF, show |(-2 : ℝ)| = 2 by norm_num]
  calc 2 * Cvs.Finite.PairPoleChannelClosed.poleFactor L * |Cvs.Finite.WindowMatrixSymbolKernel.hh (1 / 2) ω|
      ≤ 2 * Cvs.Finite.PairPoleChannelClosed.poleFactor L * (1 / |ω|) :=
        mul_le_mul_of_nonneg_left hhh (by positivity)
    _ = 2 * Cvs.Finite.PairPoleChannelClosed.poleFactor L / |ω| := by ring

/-- For `m ≥ 1`, `|gen(m) + primeSum(sinCut L ω_m) + π/2| ≤ (poleFactor L + 1 + tailMass L)·L/(πm)`. -/
theorem abs_gen_add_primeSum_add_le (P R : ℕ) {L : ℝ} (hL : 0 < L) {m : ℕ} (hm : 0 < m) :
    |Cvs.Finite.WindowMatrixClosedForm.gen P R L m
        + Cvs.Finite.OneModeEntries.primeSum P R (Cvs.Finite.DiagonalCutSymbol.sinCut L (2 * π * m / L))
        + π / 2|
      ≤ (Cvs.Finite.PairPoleChannelClosed.poleFactor L + 1 + Cvs.WeilForm.Archimedean.PoleFreeEntryBounds.tailMass L)
          * (L / (π * m)) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  set y : ℝ := π * m / L with hy
  have hy0 : 0 < y := by positivity
  have h2y : 2 * π * (m : ℝ) / L = 2 * y := by rw [hy]; ring
  have hgen : Cvs.Finite.WindowMatrixClosedForm.gen P R L m
        + Cvs.Finite.OneModeEntries.primeSum P R (Cvs.Finite.DiagonalCutSymbol.sinCut L (2 * π * m / L))
        + π / 2
      = 2 * Cvs.Finite.OneModeEntries.poleSin L (2 * y)
        - (Cvs.WeilForm.Archimedean.SymbolImaginaryHalf.archSymbolIm (2 * y) - π / 2)
        + ∑' k, Cvs.Finite.DiagonalLevySymbol.tailFactor L k * Cvs.WeilForm.Archimedean.SymbolImaginaryHalf.imTerm (2 * y) k := by
    unfold Cvs.Finite.WindowMatrixClosedForm.gen
    push_cast
    rw [h2y]
    ring
  have hA := Cvs.WeilForm.Archimedean.PoleFreeEntryBounds.abs_archSymbolIm_sub_le' hy0
  have hT := Cvs.WeilForm.Archimedean.PoleFreeEntryBounds.abs_tail_imTerm_le hL hy0
  have hP := abs_two_poleSin_le L (show 2 * y ≠ 0 by positivity)
  rw [abs_of_pos (show (0 : ℝ) < 2 * y by positivity)] at hP
  have hP' : |2 * Cvs.Finite.OneModeEntries.poleSin L (2 * y)|
      ≤ Cvs.Finite.PairPoleChannelClosed.poleFactor L * (1 / y) := by
    calc _ ≤ 2 * Cvs.Finite.PairPoleChannelClosed.poleFactor L / (2 * y) := hP
      _ = Cvs.Finite.PairPoleChannelClosed.poleFactor L * (1 / y) := by field_simp
  have hyinv : 1 / y = L / (π * m) := by rw [hy]; field_simp
  rw [hgen, ← hyinv]
  calc |2 * Cvs.Finite.OneModeEntries.poleSin L (2 * y)
          - (Cvs.WeilForm.Archimedean.SymbolImaginaryHalf.archSymbolIm (2 * y) - π / 2)
          + ∑' k, Cvs.Finite.DiagonalLevySymbol.tailFactor L k * Cvs.WeilForm.Archimedean.SymbolImaginaryHalf.imTerm (2 * y) k|
      ≤ |2 * Cvs.Finite.OneModeEntries.poleSin L (2 * y)|
          + |Cvs.WeilForm.Archimedean.SymbolImaginaryHalf.archSymbolIm (2 * y) - π / 2|
          + |∑' k, Cvs.Finite.DiagonalLevySymbol.tailFactor L k * Cvs.WeilForm.Archimedean.SymbolImaginaryHalf.imTerm (2 * y) k| :=
        (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ Cvs.Finite.PairPoleChannelClosed.poleFactor L * (1 / y) + 1 / y + 1 / y * Cvs.WeilForm.Archimedean.PoleFreeEntryBounds.tailMass L := by
        linarith
    _ = (Cvs.Finite.PairPoleChannelClosed.poleFactor L + 1 + Cvs.WeilForm.Archimedean.PoleFreeEntryBounds.tailMass L) * (1 / y) := by ring

/-- The archimedean part of the generator tends to `−π/2`: `gen(m) + primeSum(sinCut L ω_m) → −π/2`. -/
theorem tendsto_gen_add_primeSum (P R : ℕ) {L : ℝ} (hL : 0 < L) :
    Tendsto (fun m : ℕ => Cvs.Finite.WindowMatrixClosedForm.gen P R L m
        + Cvs.Finite.OneModeEntries.primeSum P R (Cvs.Finite.DiagonalCutSymbol.sinCut L (2 * π * m / L)))
      atTop (𝓝 (-(π / 2))) := by
  set K := (Cvs.Finite.PairPoleChannelClosed.poleFactor L + 1 + Cvs.WeilForm.Archimedean.PoleFreeEntryBounds.tailMass L) * (L / π)
    with hK
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun m => norm_nonneg _) ?_
    (tendsto_const_div_atTop_nhds_zero_nat K)
  filter_upwards [eventually_gt_atTop 0] with m hm
  have h := abs_gen_add_primeSum_add_le P R hL hm
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [Real.norm_eq_abs, sub_neg_eq_add]
  calc _ ≤ (Cvs.Finite.PairPoleChannelClosed.poleFactor L + 1 + Cvs.WeilForm.Archimedean.PoleFreeEntryBounds.tailMass L)
        * (L / (π * m)) := h
    _ = K / m := by rw [hK]; field_simp

/-- The partial sums of `sin(mx)` over `[p, q]` are bounded uniformly in `p` and `q`. -/
theorem exists_sin_sum_bound (x : ℝ) :
    ∃ B, 0 ≤ B ∧ ∀ p q : ℕ, |∑ m ∈ Finset.Icc p q, Real.sin (m * x)| ≤ B := by
  by_cases h : Real.sin (x / 2) = 0
  · refine ⟨0, le_rfl, fun p q => ?_⟩
    obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.mp h
    have hx : x = 2 * k * π := by linarith
    have hz : ∀ m : ℕ, Real.sin (m * x) = 0 := fun m => by
      rw [hx, show (m : ℝ) * (2 * k * π) = ((2 * k * m : ℤ) : ℝ) * π by push_cast; ring]
      exact Real.sin_int_mul_pi _
    simp [hz]
  · refine ⟨1 / |Real.sin (x / 2)|, by positivity, fun p q => ?_⟩
    have := Cvs.Upstream.SawtoothPartialSums.abs_sum_sin_mul_le p q x
    rw [le_div_iff₀ (abs_pos.mpr h)]
    exact this

/-- The cut sine at the frequencies `2πm/L`, summed over `[p, q]`, is a lattice sine sum or zero. -/
theorem sum_sinCut_eq (L v : ℝ) (p q : ℕ) :
    ∑ m ∈ Finset.Icc p q, Cvs.Finite.DiagonalCutSymbol.sinCut L (2 * π * m / L) v
      = if v ≤ L then ∑ m ∈ Finset.Icc p q, Real.sin (m * (2 * π * v / L)) else 0 := by
  unfold Cvs.Finite.DiagonalCutSymbol.sinCut
  split_ifs with h
  · refine Finset.sum_congr rfl fun m _ => ?_
    ring_nf
  · simp

/-- **The prime sine sums at the frequencies `2πm/L` have bounded partial sums over `[p, q]`.** -/
theorem exists_primeSum_partial_bound (P R : ℕ) (L : ℝ) :
    ∃ C, ∀ p q : ℕ, |∑ m ∈ Finset.Icc p q,
      Cvs.Finite.OneModeEntries.primeSum P R (Cvs.Finite.DiagonalCutSymbol.sinCut L (2 * π * m / L))| ≤ C := by
  choose B hB0 hB using exists_sin_sum_bound
  refine ⟨∑ p ∈ (Finset.range (P + 1)).filter Nat.Prime, ∑ r ∈ Finset.Icc 1 R,
    |Cvs.Zeta.Explicit.Weil.primePowerWeight p r| * (2 * B (2 * π * (r * Real.log p) / L)), fun a b => ?_⟩
  unfold Cvs.Finite.OneModeEntries.primeSum
  rw [Finset.sum_comm]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p _ => ?_)
  rw [Finset.sum_comm]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun r _ => ?_)
  rw [← Finset.mul_sum, ← Finset.mul_sum, sum_sinCut_eq, abs_mul, abs_mul, abs_two]
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by norm_num)) (abs_nonneg _)
  split_ifs
  · exact hB _ a b
  · simp [hB0]

/-- The prime sine sums at the frequencies `2πa/L` have Cesàro mean zero. -/
theorem tendsto_cesaro_primeSum (P R : ℕ) (L : ℝ) :
    Tendsto (fun A : ℕ => (A : ℝ)⁻¹ * ∑ a ∈ Finset.range A,
      Cvs.Finite.OneModeEntries.primeSum P R (Cvs.Finite.DiagonalCutSymbol.sinCut L (2 * π * a / L)))
      atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := exists_primeSum_partial_bound P R L
  have hrange : ∀ A : ℕ, |∑ a ∈ Finset.range A,
      Cvs.Finite.OneModeEntries.primeSum P R (Cvs.Finite.DiagonalCutSymbol.sinCut L (2 * π * a / L))| ≤ |C| := by
    intro A
    rcases A with _ | n
    · simp
    · rw [Finset.range_eq_Ico, Finset.Ico_add_one_right_eq_Icc]
      exact (hC 0 n).trans (le_abs_self C)
  refine squeeze_zero_norm' ?_ (tendsto_const_div_atTop_nhds_zero_nat |C|)
  filter_upwards [eventually_gt_atTop 0] with A hA
  have hAR : (0 : ℝ) < A := by exact_mod_cast hA
  rw [Real.norm_eq_abs, abs_mul, abs_inv, Nat.abs_cast, inv_mul_eq_div]
  exact div_le_div_of_nonneg_right (hrange A) hAR.le

/-- **The window generator has Cesàro mean `−π/2`**: `(1/A)·∑_{a<A} gen(a) → −π/2`. -/
theorem tendsto_cesaro_gen (P R : ℕ) {L : ℝ} (hL : 0 < L) :
    Tendsto (fun A : ℕ => (A : ℝ)⁻¹ * ∑ a ∈ Finset.range A, Cvs.Finite.WindowMatrixClosedForm.gen P R L a)
      atTop (𝓝 (-(π / 2))) := by
  have h := (tendsto_gen_add_primeSum P R hL).cesaro.sub (tendsto_cesaro_primeSum P R L)
  rw [sub_zero] at h
  refine h.congr fun A => ?_
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

/-! ### The lattice exceptions are infinite -/

/-- **If only finitely many zeros are off the critical line or off the ordinates `2πℤ/L`, then
`gen(m) → 0`.** -/
theorem tendsto_gen_of_finite {L : ℝ} (hL : 0 < L) (hfin : (latticeExc L).Finite) :
    Tendsto (fun m : ℕ => Cvs.Finite.WindowMatrixClosedForm.gen ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊ L m)
      atTop (𝓝 0) := by
  set s := hfin.toFinset
  set f : nonTrivialZeroSet → ℕ → ℝ := fun rho m => (Cvs.Criterion.divisorWeight rho : ℝ)
      * ((((8 * π * m / L : ℝ) : ℂ)) * (Complex.sin ((L : ℂ) * Cvs.ZeroCounting.zPoint rho / 2) ^ 2
          / (((2 * π * m / L : ℝ) : ℂ) ^ 2 - Cvs.ZeroCounting.zPoint rho ^ 2))).re with hf
  have hgen : ∀ m : ℕ, 0 < m →
      Cvs.Finite.WindowMatrixClosedForm.gen ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊ L m = ∑ rho ∈ s, f rho m := by
    intro m hm
    rw [Cvs.StepA.WindowGeneratorZeros.gen_eq_zeroSide hL hm, ← tsum_mul_left, tsum_eq_sum (s := s)]
    · refine Finset.sum_congr rfl fun rho _ => ?_
      rw [hf]; simp only [Complex.re_ofReal_mul]; ring
    · intro rho hrho
      have hon : ¬ rho ∈ latticeExc L := by simpa [s] using hrho
      simp only [latticeExc, Set.mem_ofPred_eq, not_not] at hon
      obtain ⟨hre, k, hk⟩ := hon
      rw [Cvs.ZeroCounting.zPoint_of_re_eq_half hre]
      have hs : Complex.sin ((L : ℂ) * (((rho : ℂ).im : ℝ) : ℂ) / 2) = 0 := by
        have : (L : ℂ) * (((rho : ℂ).im : ℝ) : ℂ) / 2 = (k : ℂ) * π := by
          have hk' : ((rho : ℂ).im * L : ℂ) = ((2 * π * k : ℝ) : ℂ) := by exact_mod_cast hk
          push_cast at hk'
          linear_combination hk' / 2
        rw [this, Complex.sin_int_mul_pi]
      simp [hs]
  have hterm : ∀ rho : nonTrivialZeroSet, Tendsto (f rho) atTop (𝓝 0) := by
    intro rho
    set z := Cvs.ZeroCounting.zPoint rho
    set c : ℂ := Complex.sin ((L : ℂ) * z / 2) ^ 2
    have hbound : ∀ᶠ m : ℕ in atTop, |f rho m|
        ≤ (Cvs.Criterion.divisorWeight rho : ℝ) * (4 * L * ‖c‖ / π) / m := by
      have hev : ∀ᶠ m : ℕ in atTop, 2 * ‖z‖ ^ 2 ≤ (2 * π * m / L) ^ 2 := by
        have ht' : Tendsto (fun m : ℕ => 2 * π * m / L) atTop atTop :=
          (tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity)).atTop_div_const hL
        have ht := (Filter.tendsto_pow_atTop (two_ne_zero)).comp ht'
        filter_upwards [ht.eventually_ge_atTop (2 * ‖z‖ ^ 2)] with m hm
        simpa using hm
      filter_upwards [hev, eventually_gt_atTop 0] with m hm hm0
      have hmr : (0 : ℝ) < m := by exact_mod_cast hm0
      set ω : ℝ := 2 * π * m / L with hω
      have hωpos : 0 < ω ^ 2 := by positivity
      have hden : ω ^ 2 / 2 ≤ ‖((ω : ℝ) : ℂ) ^ 2 - z ^ 2‖ := by
        have h1 : ‖((ω : ℝ) : ℂ) ^ 2‖ - ‖z ^ 2‖ ≤ ‖((ω : ℝ) : ℂ) ^ 2 - z ^ 2‖ := norm_sub_norm_le _ _
        rw [norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs] at h1
        linarith
      have hden0 : 0 < ‖((ω : ℝ) : ℂ) ^ 2 - z ^ 2‖ := lt_of_lt_of_le (by positivity) hden
      have hre : |((((8 * π * m / L : ℝ) : ℂ)) * (c / (((ω : ℝ) : ℂ) ^ 2 - z ^ 2))).re|
          ≤ 4 * L * ‖c‖ / π / m := by
        refine (Complex.abs_re_le_norm _).trans ?_
        rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (by positivity : (0 : ℝ) < 8 * π * m / L)]
        have hc0 : 0 ≤ ‖c‖ := norm_nonneg _
        calc 8 * π * m / L * (‖c‖ / ‖((ω : ℝ) : ℂ) ^ 2 - z ^ 2‖)
            ≤ 8 * π * m / L * (‖c‖ / (ω ^ 2 / 2)) :=
              mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hc0 (by positivity) hden)
                (by positivity)
          _ = 4 * L * ‖c‖ / π / m := by
              rw [hω]; field_simp; ring
      have hw : (0 : ℝ) ≤ (Cvs.Criterion.divisorWeight rho : ℝ) := Nat.cast_nonneg _
      show |(Cvs.Criterion.divisorWeight rho : ℝ)
          * ((((8 * π * m / L : ℝ) : ℂ)) * (c / (((ω : ℝ) : ℂ) ^ 2 - z ^ 2))).re| ≤ _
      rw [abs_mul, abs_of_nonneg hw]
      calc (Cvs.Criterion.divisorWeight rho : ℝ)
            * |((((8 * π * m / L : ℝ) : ℂ)) * (c / (((ω : ℝ) : ℂ) ^ 2 - z ^ 2))).re|
          ≤ (Cvs.Criterion.divisorWeight rho : ℝ) * (4 * L * ‖c‖ / π / m) :=
            mul_le_mul_of_nonneg_left hre hw
        _ = (Cvs.Criterion.divisorWeight rho : ℝ) * (4 * L * ‖c‖ / π) / m := by ring
    have hlim : Tendsto (fun m : ℕ => (Cvs.Criterion.divisorWeight rho : ℝ) * (4 * L * ‖c‖ / π) / m)
        atTop (𝓝 0) := tendsto_const_div_atTop_nhds_zero_nat _
    exact squeeze_zero_norm' (by simpa only [Real.norm_eq_abs] using hbound) hlim
  have hsum := tendsto_finsetSum s fun rho _ => hterm rho
  simp only [Finset.sum_const_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with m hm
  exact (hgen m hm).symm

/-- **For every `L > 0`, infinitely many nontrivial zeros are not of the form `1/2 + 2πik/L`.** -/
theorem latticeExc_infinite {L : ℝ} (hL : 0 < L) : (latticeExc L).Infinite := by
  intro hF
  have h := tendsto_nhds_unique (tendsto_gen_of_finite hL hF).cesaro (tendsto_cesaro_gen _ _ hL)
  linarith [Real.pi_pos]

/-! ### The off-lattice squared ordinates -/

/-- A set of nontrivial zeros is infinite iff its set of squared ordinates is infinite. -/
theorem infinite_sq_im_image_iff {S : Set nonTrivialZeroSet} :
    ((fun rho : nonTrivialZeroSet => ((rho : ℂ).im) ^ 2) '' S).Infinite ↔ S.Infinite := by
  constructor
  · exact fun h hS => h (hS.image _)
  · intro hS hfin
    obtain ⟨C, hC⟩ := hfin.bddAbove
    refine hS ((Cvs.Zeta.ZeroCounting.FinitelyManyBelowOrdinate.finite_ordinate_below (C + 1)).subset fun rho hrho => ?_)
    have h1 : ((rho : ℂ).im) ^ 2 ≤ C := hC ⟨rho, hrho, rfl⟩
    simp only [Set.mem_ofPred_eq]
    nlinarith [sq_abs ((rho : ℂ).im), abs_nonneg ((rho : ℂ).im)]

/-- The off-lattice squared ordinates are infinite iff the zeros whose ordinate avoids `2πℤ/L`
are infinite. -/
theorem offLatticeSq_infinite_iff (L : ℝ) :
    (Cvs.StepA.PosDefOffLattice.offLatticeSq L).Infinite
      ↔ {rho : nonTrivialZeroSet | ∀ k : ℤ, (rho : ℂ).im * L ≠ 2 * π * k}.Infinite :=
  infinite_sq_im_image_iff

/-- **If only finitely many zeros lie off the critical line at an ordinate in `2πℤ/L`, the
off-lattice squared ordinates are infinite.** -/
theorem offLatticeSq_infinite_of_finite {L : ℝ} (hL : 0 < L)
    (h : {rho : nonTrivialZeroSet |
      (rho : ℂ).re ≠ 1 / 2 ∧ ∃ k : ℤ, (rho : ℂ).im * L = 2 * π * k}.Finite) :
    (Cvs.StepA.PosDefOffLattice.offLatticeSq L).Infinite := by
  rw [offLatticeSq_infinite_iff]
  intro hA
  refine latticeExc_infinite hL ((h.union hA).subset fun rho hrho => ?_)
  by_cases hk : ∃ k : ℤ, (rho : ℂ).im * L = 2 * π * k
  · exact Or.inl ⟨fun hre => hrho ⟨hre, hk⟩, hk⟩
  · exact Or.inr fun k hk' => hk ⟨k, hk'⟩

/-- **If every zero with ordinate in `2πℤ/L` is on the critical line, the off-lattice squared
ordinates are infinite.** -/
theorem offLatticeSq_infinite_of_onLine {L : ℝ} (hL : 0 < L)
    (hlat : ∀ rho : nonTrivialZeroSet,
      (∃ k : ℤ, (rho : ℂ).im * L = 2 * π * k) → (rho : ℂ).re = 1 / 2) :
    (Cvs.StepA.PosDefOffLattice.offLatticeSq L).Infinite := by
  refine offLatticeSq_infinite_of_finite hL (Set.Finite.subset Set.finite_empty fun rho hrho => ?_)
  exact hrho.1 (hlat rho hrho.2)

/-- **Under RH the off-lattice squared ordinates are infinite.** -/
theorem offLatticeSq_infinite_of_RH (hRH : RiemannHypothesis) {L : ℝ} (hL : 0 < L) :
    (Cvs.StepA.PosDefOffLattice.offLatticeSq L).Infinite :=
  offLatticeSq_infinite_of_onLine hL fun rho _ => Cvs.WeilForm.CouplingAngle.re_eq_half_of_rh hRH rho

/-- **Under RH every mode count is below the number of off-lattice squared ordinates.** -/
theorem natCast_lt_encard_of_RH (hRH : RiemannHypothesis) {L : ℝ} (hL : 0 < L) (N : ℕ) :
    (N : ℕ∞) < (Cvs.StepA.PosDefOffLattice.offLatticeSq L).encard := by
  rw [(offLatticeSq_infinite_of_RH hRH hL).encard_eq]
  exact ENat.natCast_lt_top N

end Cvs.StepA.InfinitelyManyOffLattice
