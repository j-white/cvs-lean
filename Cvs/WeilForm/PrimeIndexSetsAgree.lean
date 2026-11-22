import Mathlib
import Cvs.WeilForm.AutocorrSelfConvolution
import Cvs.WeilForm.PrimePowerIndexed
import Cvs.WeilForm.WindowTruncatesPrimes
import Cvs.Zeta.WeilPositivityStatement

/-!
# The two prime index sets agree

    ∑_{k ∈ windowIndex P R L} = ∑_{n < ⌈exp L⌉₊}

once `exp L ≤ P` and `L ≤ R·log 2`.  What the range carries and the window does not has von
Mangoldt weight zero; what the window carries and the range does not sits at `log k = L`.
-/

set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Set Real Cvs.Zeta.Explicit.Weil

namespace Cvs.WeilForm.PrimeIndexSetsAgree

open Cvs.WeilForm.WindowTruncatesPrimes

/-- **Every prime power below the scale is in the window's index set.** -/
theorem mem_windowIndex_of_isPrimePow {L : ℝ} {P R : ℕ}
    (hP : Real.exp L ≤ P) (hR : L ≤ R * Real.log 2) {n : ℕ}
    (hn : IsPrimePow n) (hlt : (n : ℝ) < Real.exp L) :
    n ∈ windowIndex P R L := by
  classical
  obtain ⟨p, r, hp, hr, hpr⟩ := hn
  have hpn : Nat.Prime p := Nat.prime_iff.mpr hp
  have hp2 : 2 ≤ p := hpn.two_le
  have hlogp : Real.log 2 ≤ Real.log p := by
    refine Real.log_le_log (by norm_num) ?_
    exact_mod_cast hp2
  have hlog2pos : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  -- the value's logarithm
  have hcast : ((p ^ r : ℕ) : ℝ) = (p : ℝ) ^ r := by push_cast; ring
  have hlogn : Real.log n = r * Real.log p := by
    rw [← hpr, hcast, Real.log_pow]
  have hnpos : 0 < n := by
    rw [← hpr]; exact pow_pos hpn.pos r
  have hlogle : Real.log n ≤ L := by
    have h1 : Real.log (n : ℝ) < L := by
      have := Real.log_lt_log (by exact_mod_cast hnpos) hlt
      rwa [Real.log_exp] at this
    linarith
  -- the prime is below `P`
  have hple : p ≤ P := by
    have hpn' : p ≤ n := by
      rw [← hpr]
      exact Nat.le_self_pow (by omega) p
    have hnP : (n : ℝ) < (P : ℝ) := lt_of_lt_of_le hlt hP
    have : n < P := by exact_mod_cast hnP
    omega
  -- the exponent is below `R`
  have hrR : r ≤ R := by
    have h1 : (r : ℝ) * Real.log 2 ≤ (r : ℝ) * Real.log p :=
      mul_le_mul_of_nonneg_left hlogp (Nat.cast_nonneg r)
    have h2 : (r : ℝ) * Real.log p ≤ L := by rw [← hlogn]; exact hlogle
    have h3 : (r : ℝ) * Real.log 2 ≤ (R : ℝ) * Real.log 2 := by linarith
    have h4 : (r : ℝ) ≤ (R : ℝ) := le_of_mul_le_mul_right (by linarith) hlog2pos
    exact_mod_cast h4
  refine Finset.mem_filter.mpr ⟨?_, hlogle⟩
  refine Finset.mem_image.mpr ⟨(p, r), ?_, hpr⟩
  refine Finset.mem_product.mpr ⟨?_, ?_⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hpn⟩
  · exact Finset.mem_Icc.mpr ⟨hr, hrR⟩

/-- **The two prime sums agree.**  The window's own truncation and the explicit formula's
cut at `⌈exp L⌉₊` reach the same prime powers, with the same weights. -/
theorem sum_windowIndex_eq_range {L : ℝ} (hL : 0 ≤ L) {P R : ℕ}
    (hP : Real.exp L ≤ P) (hR : L ≤ R * Real.log 2) (f : ℝ → ℝ) :
    (∑ k ∈ windowIndex P R L,
        (ArithmeticFunction.vonMangoldt k * (k : ℝ) ^ (-(1/2) : ℝ))
          * (selfConvolution (Set.indicator (Set.Ioc 0 L) f) (Real.log k)
            + selfConvolution (Set.indicator (Set.Ioc 0 L) f) (-(Real.log k))))
      = ∑ n ∈ Finset.range ⌈Real.exp L⌉₊,
          (ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(1/2) : ℝ))
            * (selfConvolution (Set.indicator (Set.Ioc 0 L) f) (Real.log n)
              + selfConvolution (Set.indicator (Set.Ioc 0 L) f) (-(Real.log n))) := by
  classical
  set G : ℝ → ℝ := selfConvolution (Set.indicator (Set.Ioc 0 L) f) with hG
  set T : ℕ → ℝ := fun k => (ArithmeticFunction.vonMangoldt k * (k : ℝ) ^ (-(1/2) : ℝ))
    * (G (Real.log k) + G (-(Real.log k))) with hT
  -- terms the window carries and the range does not sit at the endpoint
  have hwin : ∀ k ∈ windowIndex P R L, k ∉ Finset.range ⌈Real.exp L⌉₊ → T k = 0 := by
    intro k hk hkr
    have hlogle : Real.log k ≤ L := (Finset.mem_filter.mp hk).2
    have hge : Real.exp L ≤ (k : ℝ) := by
      rw [Finset.mem_range, not_lt] at hkr
      exact le_trans (Nat.le_ceil _) (by exact_mod_cast hkr)
    have hkpos : (0:ℝ) < (k : ℝ) := lt_of_lt_of_le (Real.exp_pos L) hge
    have hlogge : L ≤ Real.log k := by
      have := Real.log_le_log (Real.exp_pos L) hge
      rwa [Real.log_exp] at this
    have hlogeq : Real.log k = L := le_antisymm hlogle hlogge
    have h1 : G (Real.log k) = 0 := by
      rw [hG, hlogeq]
      exact Cvs.WeilForm.AutocorrSelfConvolution.selfConvolution_indicator_eq_zero L f (le_abs_self L)
    have h2 : G (-(Real.log k)) = 0 := by
      rw [hG, hlogeq]
      refine Cvs.WeilForm.AutocorrSelfConvolution.selfConvolution_indicator_eq_zero L f ?_
      rw [abs_neg]
      exact le_abs_self L
    rw [hT]
    simp only [h1, h2]
    ring
  -- terms the range carries and the window does not have weight zero
  have hran : ∀ n ∈ Finset.range ⌈Real.exp L⌉₊, n ∉ windowIndex P R L → T n = 0 := by
    intro n hn hnw
    have hlt : (n : ℝ) < Real.exp L := Nat.lt_ceil.mp (Finset.mem_range.mp hn)
    have hΛ : ArithmeticFunction.vonMangoldt n = 0 := by
      by_contra hne
      exact hnw (mem_windowIndex_of_isPrimePow hP hR
        (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hne) hlt)
    rw [hT]
    simp [hΛ]
  have hunion₁ : (∑ k ∈ windowIndex P R L, T k)
      = ∑ k ∈ windowIndex P R L ∪ Finset.range ⌈Real.exp L⌉₊, T k := by
    refine Finset.sum_subset Finset.subset_union_left fun x hx hxn => ?_
    exact hran x ((Finset.mem_union.mp hx).resolve_left hxn) hxn
  have hunion₂ : (∑ n ∈ Finset.range ⌈Real.exp L⌉₊, T n)
      = ∑ k ∈ windowIndex P R L ∪ Finset.range ⌈Real.exp L⌉₊, T k := by
    refine Finset.sum_subset Finset.subset_union_right fun x hx hxn => ?_
    exact hwin x ((Finset.mem_union.mp hx).resolve_right hxn) hxn
  rw [hunion₁, hunion₂]

end Cvs.WeilForm.PrimeIndexSetsAgree
