import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Power sums from dyadic shell counts, in closed form

For a finite family `ω_i ∈ [0, 1]` whose dyadic shells `(2^{−k−1}, 2^{−k}]` hold at most `a + bk` members, and
`q > 0`, `Σ_i ω_i^q ≤ a/(1 − r) + b·r/(1 − r)²` with `r = 2^{−q}`.
-/

noncomputable section

open Real Finset

namespace Cvs.Upstream.DyadicShellPowerSums

variable {ι : Type*}

/-- The dyadic shell `(2^{−k−1}, 2^{−k}]` as a predicate. -/
def InShell (k : ℕ) (w : ℝ) : Prop := (1 / 2 : ℝ) ^ (k + 1) < w ∧ w ≤ (1 / 2 : ℝ) ^ k

instance (k : ℕ) (w : ℝ) : Decidable (InShell k w) := by unfold InShell; infer_instance

/-- Every `w ∈ (0, 1]` lies in some dyadic shell. -/
theorem exists_inShell {w : ℝ} (h0 : 0 < w) (h1 : w ≤ 1) : ∃ k : ℕ, InShell k w := by
  have hx : 1 ≤ 1 / w := by rw [le_div_iff₀ h0]; linarith
  obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near hx (by norm_num : (1 : ℝ) < 2)
  refine ⟨n, ?_, ?_⟩
  · rw [one_div_pow, div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ h0] at hn2
    linarith
  · rw [one_div_pow, le_div_iff₀ (by positivity)]
    rw [le_div_iff₀ h0] at hn1
    linarith

/-- In shell `k`, `w^q ≤ (2^{−q})^k`. -/
theorem rpow_le_of_inShell {w q : ℝ} {k : ℕ} (hq : 0 ≤ q) (hw : 0 ≤ w) (h : InShell k w) :
    w ^ q ≤ ((1 / 2 : ℝ) ^ q) ^ k := by
  rw [← rpow_natCast, ← rpow_mul (by norm_num), mul_comm, rpow_mul (by norm_num), rpow_natCast]
  exact rpow_le_rpow hw h.2 hq

/-- The shell-weighted geometric term `(2^{−q})^k·1[w ∈ shell k]`. -/
def shellTerm (q w : ℝ) (k : ℕ) : ℝ := if InShell k w then ((1 / 2 : ℝ) ^ q) ^ k else 0

theorem shellTerm_nonneg (q w : ℝ) (k : ℕ) : 0 ≤ shellTerm q w k := by
  unfold shellTerm; split_ifs <;> positivity

theorem shellTerm_le (q w : ℝ) (k : ℕ) : shellTerm q w k ≤ ((1 / 2 : ℝ) ^ q) ^ k := by
  unfold shellTerm; split_ifs <;> [exact le_rfl; positivity]

theorem half_rpow_lt_one {q : ℝ} (hq : 0 < q) : (1 / 2 : ℝ) ^ q < 1 :=
  rpow_lt_one (by norm_num) (by norm_num) hq

theorem summable_shellTerm {q : ℝ} (hq : 0 < q) (w : ℝ) : Summable (shellTerm q w) :=
  Summable.of_nonneg_of_le (shellTerm_nonneg q w) (shellTerm_le q w)
    (summable_geometric_of_lt_one (by positivity) (half_rpow_lt_one hq))

/-- `w^q ≤ Σ_k shellTerm q w k` for `w ∈ [0, 1]`. -/
theorem rpow_le_tsum_shellTerm {q w : ℝ} (hq : 0 < q) (h0 : 0 ≤ w) (h1 : w ≤ 1) :
    w ^ q ≤ ∑' k, shellTerm q w k := by
  rcases h0.eq_or_lt with h | h
  · rw [← h, zero_rpow hq.ne']
    exact tsum_nonneg (shellTerm_nonneg q 0)
  · obtain ⟨k, hk⟩ := exists_inShell h h1
    calc w ^ q ≤ ((1 / 2 : ℝ) ^ q) ^ k := rpow_le_of_inShell hq.le h0 hk
      _ = shellTerm q w k := by simp [shellTerm, hk]
      _ ≤ ∑' k, shellTerm q w k :=
          (summable_shellTerm hq w).le_tsum k fun j _ => shellTerm_nonneg q w j

/-- **Power sum from shell counts**: if `ω_i ∈ [0, 1]` and shell `k` holds at most `a + bk` of them, then
`Σ_i ω_i^q ≤ a/(1 − r) + b·r/(1 − r)²` with `r = 2^{−q}`. -/
theorem sum_rpow_le_of_shellCount (s : Finset ι) (ω : ι → ℝ) {q a b : ℝ} (hq : 0 < q)
    (hω : ∀ i ∈ s, 0 ≤ ω i ∧ ω i ≤ 1)
    (hcount : ∀ k : ℕ, ((s.filter fun i => InShell k (ω i)).card : ℝ) ≤ a + b * k) :
    ∑ i ∈ s, ω i ^ q
      ≤ a / (1 - (1 / 2 : ℝ) ^ q) + b * ((1 / 2 : ℝ) ^ q / (1 - (1 / 2 : ℝ) ^ q) ^ 2) := by
  set r : ℝ := (1 / 2 : ℝ) ^ q with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := half_rpow_lt_one hq
  have hg : Summable fun k : ℕ => r ^ k := summable_geometric_of_lt_one hr0 hr1
  have hkg : Summable fun k : ℕ => (k : ℝ) * r ^ k := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1 (by rwa [norm_of_nonneg hr0])
  have hstep : ∀ k : ℕ, ∑ i ∈ s, shellTerm q (ω i) k = r ^ k * (s.filter fun i => InShell k (ω i)).card := by
    intro k
    simp only [shellTerm, ← hr]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  calc ∑ i ∈ s, ω i ^ q ≤ ∑ i ∈ s, ∑' k, shellTerm q (ω i) k :=
        Finset.sum_le_sum fun i hi => rpow_le_tsum_shellTerm hq (hω i hi).1 (hω i hi).2
    _ = ∑' k, ∑ i ∈ s, shellTerm q (ω i) k :=
        (Summable.tsum_finsetSum fun i _ => summable_shellTerm hq (ω i)).symm
    _ ≤ ∑' k : ℕ, (a * r ^ k + b * ((k : ℝ) * r ^ k)) := by
        refine Summable.tsum_le_tsum (fun k => ?_) ?_ ((hg.mul_left a).add (hkg.mul_left b))
        · rw [hstep k]
          calc r ^ k * ((s.filter fun i => InShell k (ω i)).card : ℝ) ≤ r ^ k * (a + b * k) :=
                mul_le_mul_of_nonneg_left (hcount k) (by positivity)
            _ = _ := by ring
        · exact summable_sum fun i _ => summable_shellTerm hq (ω i)
    _ = a / (1 - r) + b * (r / (1 - r) ^ 2) := by
        rw [Summable.tsum_add (hg.mul_left a) (hkg.mul_left b), tsum_mul_left, tsum_mul_left,
          tsum_geometric_of_lt_one hr0 hr1, tsum_coe_mul_geometric_of_norm_lt_one (by rwa [norm_of_nonneg hr0])]
        ring

end Cvs.Upstream.DyadicShellPowerSums

end
