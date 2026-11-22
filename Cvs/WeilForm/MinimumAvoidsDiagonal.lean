import Mathlib
import Cvs.Upstream.DiagonalRankOneMinimum
import Cvs.Upstream.TightCoordinateConvergence
import Cvs.WeilForm.EvenSectorMinimum
import Cvs.WeilForm.MinimumBelowTwoLevels

/-!
# The minimum avoids every diagonal level

    D n₀ < λ_min < D m   for every m ≠ n₀

when the diagonal is strictly smallest at `n₀` and the rank-one vector never vanishes: the
pair vector gives the upper bound, minimality itself the lower.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Cvs.Upstream.TightCoordinateConvergence Cvs.Upstream.DiagonalRankOneMinimum Cvs.WeilForm.EvenSectorMinimum Cvs.WeilForm.MinimumBelowTwoLevels

namespace Cvs.WeilForm.MinimumAvoidsDiagonal

variable {ι : Type*} [Countable ι] [DecidableEq ι] [Nonempty ι]

/-- **The pair vector beats the larger level strictly**, when the rank one does not vanish at
the smaller mode. -/
theorem diagFormVal_pairVec_lt {D v : ι → ℝ} {c : ℝ} {m₀ m₁ : ι} (hne : m₀ ≠ m₁)
    (hlt : D m₀ < D m₁) (hv₁ : v m₁ ≠ 0) :
    diagFormVal D c v (pairVec v m₀ m₁) < D m₁ := by
  have hv₁sq : 0 < (v m₁) ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hv₁))
  have hv : (v m₀) ^ 2 + (v m₁) ^ 2 ≠ 0 := by
    have : 0 < (v m₀) ^ 2 + (v m₁) ^ 2 := by nlinarith [sq_nonneg (v m₀), hv₁sq]
    exact ne_of_gt this
  have hpos : 0 < (v m₀) ^ 2 + (v m₁) ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hv)
  have hrank : rankOneVal c v (pairVec v m₀ m₁) = 0 := by
    unfold rankOneVal
    rw [tsum_mul_pairVec hne]
    ring
  have hdiag : ∑' n : ι, D n * (pairVec v m₀ m₁ n) ^ 2
      = D m₀ * ((v m₁) ^ 2 / ((v m₀) ^ 2 + (v m₁) ^ 2))
        + D m₁ * ((v m₀) ^ 2 / ((v m₀) ^ 2 + (v m₁) ^ 2)) := by
    classical
    rw [tsum_eq_sum (s := ({m₀, m₁} : Finset ι)) (fun n hn => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
      simp [pairVec_apply_notMem hn.1 hn.2])]
    rw [Finset.sum_pair hne, pairVec_fst, pairVec_snd hne, div_pow, div_pow,
      Real.sq_sqrt hpos.le]
    ring
  have hw0 : 0 < (v m₁) ^ 2 / ((v m₀) ^ 2 + (v m₁) ^ 2) := div_pos hv₁sq hpos
  have hsum1 : (v m₁) ^ 2 / ((v m₀) ^ 2 + (v m₁) ^ 2)
      + (v m₀) ^ 2 / ((v m₀) ^ 2 + (v m₁) ^ 2) = 1 := by
    rw [← add_div, div_eq_one_iff_eq hv]
    ring
  have hw1 : (v m₀) ^ 2 / ((v m₀) ^ 2 + (v m₁) ^ 2)
      = 1 - (v m₁) ^ 2 / ((v m₀) ^ 2 + (v m₁) ^ 2) := by linarith
  unfold diagFormVal
  rw [hrank, hdiag, add_zero, hw1]
  nlinarith [hw0, hlt, mul_pos hw0 (sub_pos.mpr hlt)]

/-- **The minimum is strictly below every other level.** -/
theorem min_lt_of_ne {D v : ι → ℝ} {K c : ℝ} {η : ι → ℝ} {n₀ : ι}
    (hmin : ∀ a ∈ sphereDom (fun n => D n - K), diagFormVal D c v η ≤ diagFormVal D c v a)
    (hD : ∀ m, m ≠ n₀ → D n₀ < D m) (hv : ∀ n, v n ≠ 0) {m : ι} (hm : m ≠ n₀) :
    diagFormVal D c v η < D m := by
  have hne : n₀ ≠ m := fun h => hm h.symm
  have hvsq : 0 < (v n₀) ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (hv n₀)))
  have hvsum : (v n₀) ^ 2 + (v m) ^ 2 ≠ 0 := by
    have : 0 < (v n₀) ^ 2 + (v m) ^ 2 := by nlinarith [sq_nonneg (v m), hvsq]
    exact ne_of_gt this
  exact lt_of_le_of_lt (hmin _ (pairVec_mem _ hne hvsum))
    (diagFormVal_pairVec_lt hne (hD m hm) (hv m))

/-- **The minimum is strictly above the lowest level.**  Sitting at it would force the
minimiser onto the lowest mode alone, where the rank one is not blind. -/
theorem lt_min {D v : ι → ℝ} {K c : ℝ} {η : ι → ℝ} {n₀ : ι} (hc : 0 < c)
    (hη : η ∈ sphereDom (fun n => D n - K))
    (hval : diagFormVal D c v η ≤ D n₀)
    (hD : ∀ m, m ≠ n₀ → D n₀ < D m) (hv : ∀ n, v n ≠ 0) : False := by
  obtain ⟨hnorm, hunit, hshift⟩ := hη
  have hsum : Summable fun n : ι => D n * (η n) ^ 2 := by
    have := hshift.add (hnorm.mul_left K)
    refine this.congr fun n => ?_
    ring
  -- the diagonal part is at least the bottom level
  have hge : D n₀ ≤ ∑' n : ι, D n * (η n) ^ 2 := by
    have hle : ∀ n : ι, D n₀ * (η n) ^ 2 ≤ D n * (η n) ^ 2 := by
      intro n
      by_cases h : n = n₀
      · rw [h]
      · exact mul_le_mul_of_nonneg_right (hD n h).le (sq_nonneg _)
    have := Summable.tsum_le_tsum hle (hnorm.mul_left (D n₀)) hsum
    rwa [tsum_mul_left, hunit, mul_one] at this
  -- so the rank one must vanish
  have hrank : rankOneVal c v η ≤ 0 := by
    unfold diagFormVal at hval
    linarith
  have hzero : (∑' n : ι, v n * η n) = 0 := by
    unfold rankOneVal at hrank
    have hmul : c * (∑' n : ι, v n * η n) ^ 2 ≤ c * 0 := by rw [mul_zero]; exact hrank
    have hsq : (∑' n : ι, v n * η n) ^ 2 ≤ 0 := le_of_mul_le_mul_left hmul hc
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp
      (le_antisymm hsq (sq_nonneg _))
  -- and the mass must sit on the bottom mode alone
  have htight : ∀ n : ι, n ≠ n₀ → η n = 0 := by
    intro n hn
    by_contra hne0
    have hstrict : ∑' m : ι, D n₀ * (η m) ^ 2 < ∑' m : ι, D m * (η m) ^ 2 := by
      refine Summable.tsum_lt_tsum (i := n) (fun m => ?_) ?_ (hnorm.mul_left (D n₀)) hsum
      · by_cases h : m = n₀
        · rw [h]
        · exact mul_le_mul_of_nonneg_right (hD m h).le (sq_nonneg _)
      · have hsq : 0 < (η n) ^ 2 := by positivity
        exact mul_lt_mul_of_pos_right (hD n hn) hsq
    rw [tsum_mul_left, hunit, mul_one] at hstrict
    unfold diagFormVal at hval
    have hrnn : 0 ≤ rankOneVal c v η := by
      unfold rankOneVal
      positivity
    linarith
  -- but then the rank one reads off the bottom coefficient, which cannot vanish
  have hsingle : (∑' n : ι, v n * η n) = v n₀ * η n₀ := by
    refine tsum_eq_single n₀ fun n hn => ?_
    rw [htight n hn, mul_zero]
  have hη0 : η n₀ = 0 := by
    rw [hsingle] at hzero
    rcases mul_eq_zero.mp hzero with h | h
    · exact absurd h (hv n₀)
    · exact h
  -- with every coordinate zero the norm cannot be one
  have hall : ∀ n : ι, (η n) ^ 2 = 0 := by
    intro n
    by_cases h : n = n₀
    · rw [h, hη0]; ring
    · rw [htight n h]; ring
  rw [tsum_congr hall] at hunit
  simp at hunit

/-- **The separation.**  The minimum equals no diagonal entry at all — strictly above the
lowest, strictly below every other.  This is exactly what `an earlier result` consumes for simplicity. -/
theorem min_notMem_diag {D v : ι → ℝ} {K c : ℝ} {η : ι → ℝ} {n₀ : ι} (hc : 0 < c)
    (hη : η ∈ sphereDom (fun n => D n - K))
    (hmin : ∀ a ∈ sphereDom (fun n => D n - K), diagFormVal D c v η ≤ diagFormVal D c v a)
    (hD : ∀ m, m ≠ n₀ → D n₀ < D m) (hv : ∀ n, v n ≠ 0) (n : ι) :
    diagFormVal D c v η ≠ D n := by
  by_cases h : n = n₀
  · subst h
    intro hcon
    exact lt_min hc hη (le_of_eq hcon) hD hv
  · exact ne_of_lt (min_lt_of_ne hmin hD hv h)

end Cvs.WeilForm.MinimumAvoidsDiagonal
