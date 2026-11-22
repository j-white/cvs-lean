import Mathlib
import Cvs.Zeta.CompletedZeroIndex
import Cvs.Zeta.GaussKernel.DivisorWeightCoordinates
import Cvs.Zeta.GaussKernel.DivisorWeightExpansion
import Cvs.Zeta.GaussKernel.ZetaZeroStatement
import Cvs.Zeta.ZeroDensityTail
import Cvs.Zeta.ZetaZeroWindows

/-!
# The quadratic weight is summable over the zeros

Each unit bucket of zeros holds at most `352·log(n+3)` of them (`Cvs.Zeta.ZeroDensityTail`), and
`∑ log(n+3)/(1+n²)` converges, so `∑_ρ 1/(1+γ²)` converges over the nontrivial zeros with
multiplicity. Hence the zero side of a test whose window transform decays only linearly is
summable, which is what the constant mode needs.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Real Complex Cvs.Zeta.Explicit.Venue

namespace Cvs.Zeta.QuadraticWeightSummable

/-- **A bucket-cardinality envelope gives summability.** -/
theorem summable_of_bucket_card_envelope {f : CompletedZetaZeroIndex → ℝ} {a b : ℕ → ℝ}
    (hf : 0 ≤ f) (ha : 0 ≤ a)
    (hb : ∀ n, ((completedZetaZeroBucketFinset n).card : ℝ) ≤ b n)
    (hseries : Summable fun n : ℕ => b n * a n)
    (henvelope : ∀ rho, f rho ≤ a (completedZetaZeroBucket rho)) :
    Summable f := by
  let bucket : ℕ → Set CompletedZetaZeroIndex := fun n => ↑(completedZetaZeroBucketFinset n)
  have hpartition : ∀ rho, ∃! n, rho ∈ bucket n := by
    intro rho
    refine ⟨completedZetaZeroBucket rho, by simp [bucket], ?_⟩
    intro n hn
    exact (by simpa [bucket] using hn : completedZetaZeroBucket rho = n).symm
  rw [summable_partition hf hpartition]
  constructor
  · intro n
    have hfinite : (bucket n).Finite := by
      rw [show bucket n = ↑(completedZetaZeroBucketFinset n) by rfl]
      exact Finset.finite_toSet _
    letI := hfinite.fintype
    exact Summable.of_finite
  · apply hseries.of_nonneg_of_le
    · intro n
      exact tsum_nonneg fun _ => hf _
    · intro n
      have hfinite : (bucket n).Finite := by
        rw [show bucket n = ↑(completedZetaZeroBucketFinset n) by rfl]
        exact Finset.finite_toSet _
      letI := hfinite.fintype
      rw [tsum_fintype]
      calc
        ∑ rho : bucket n, f rho ≤ ∑ _rho : bucket n, a n := by
          apply Finset.sum_le_sum
          intro rho _hrho
          have hrho : completedZetaZeroBucket rho = n :=
            mem_completedZetaZeroBucketFinset.mp rho.property
          simpa [hrho] using henvelope rho
        _ = (Fintype.card (bucket n) : ℝ) * a n := by simp
        _ = ((completedZetaZeroBucketFinset n).card : ℝ) * a n := by
          simp [bucket]
        _ ≤ b n * a n := mul_le_mul_of_nonneg_right (hb n) (ha n)

/-- On the bucket `n`, the quadratic weight is at most `4/(1 + n²)`. -/
theorem sq_le_bucket (rho : CompletedZetaZeroIndex) :
    1 / (1 + ((nontrivialZetaZeroValue rho.1).im) ^ 2)
      ≤ 4 / (1 + ((completedZetaZeroBucket rho : ℕ) : ℝ) ^ 2) := by
  set m : ℝ := |(nontrivialZetaZeroValue rho.1).im| with hm
  have hm0 : 0 ≤ m := abs_nonneg _
  set n : ℕ := completedZetaZeroBucket rho with hn
  have hnm : (n : ℝ) = (Nat.ceil m : ℝ) := by rw [hn, completedZetaZeroBucket]
  have hle : m ≤ (n : ℝ) := by rw [hnm]; exact Nat.le_ceil _
  have hlt : (n : ℝ) < m + 1 := by rw [hnm]; exact_mod_cast Nat.ceil_lt_add_one hm0
  have him2 : ((nontrivialZetaZeroValue rho.1).im) ^ 2 = m ^ 2 := by rw [hm, sq_abs]
  rw [him2]
  have hd1 : (0 : ℝ) < 1 + m ^ 2 := by positivity
  have hd2 : (0 : ℝ) < 1 + (n : ℝ) ^ 2 := by positivity
  rw [div_le_div_iff₀ hd1 hd2]
  rcases le_or_gt (n : ℝ) 1 with h | h
  · have hn2 : (n : ℝ) ^ 2 ≤ 1 := pow_le_one₀ (Nat.cast_nonneg n) h
    nlinarith [sq_nonneg m]
  · have h2 : (2 : ℝ) ≤ (n : ℝ) := by
      have : 1 < n := by exact_mod_cast h
      exact_mod_cast this
    have hn2m : (n : ℝ) ≤ 2 * m := by linarith
    nlinarith [pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ (n : ℝ)) hn2m 2, sq_nonneg m]

/-- `log y ≤ 2√y` for `y ≥ 1`. -/
theorem log_le_two_sqrt {y : ℝ} (hy : 1 ≤ y) : Real.log y ≤ 2 * Real.sqrt y := by
  have hs : 0 < Real.sqrt y := Real.sqrt_pos.mpr (by linarith)
  have h1 : Real.log y = 2 * Real.log (Real.sqrt y) := by
    rw [Real.log_sqrt (by linarith)]; ring
  rw [h1]
  have := Real.log_le_sub_one_of_pos hs
  linarith

/-- The bucket bound times the quadratic weight is summable. -/
theorem summable_log_mul_sq :
    Summable fun n : ℕ => (352 * Real.log ((n : ℝ) + 3)) * (4 / (1 + (n : ℝ) ^ 2)) := by
  have hbase : Summable (fun n : ℕ => 1 / |(n : ℝ) + 1| ^ (3 / 2 : ℝ)) :=
    (Real.summable_one_div_nat_add_rpow 1 (3 / 2)).mpr (by norm_num)
  refine (hbase.mul_left 11264).of_nonneg_of_le (fun n => mul_nonneg (mul_nonneg (by norm_num)
    (Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n]))) (by positivity)) fun n => ?_
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hlog : Real.log ((n : ℝ) + 3) ≤ 2 * Real.sqrt ((n : ℝ) + 3) :=
    log_le_two_sqrt (by linarith)
  have hsq3 : Real.sqrt ((n : ℝ) + 3) ≤ 2 * Real.sqrt ((n : ℝ) + 1) := by
    rw [show (2 : ℝ) * Real.sqrt ((n : ℝ) + 1) = Real.sqrt 4 * Real.sqrt ((n : ℝ) + 1) by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)], ← Real.sqrt_mul (by norm_num)]
    exact Real.sqrt_le_sqrt (by linarith)
  have hden : ((n : ℝ) + 1) ^ 2 ≤ 2 * (1 + (n : ℝ) ^ 2) := by nlinarith [sq_nonneg ((n : ℝ) - 1)]
  have hrpow : |(n : ℝ) + 1| ^ (3 / 2 : ℝ) = ((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 1) := by
    rw [abs_of_pos hn1, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hn1, Real.rpow_one,
      Real.sqrt_eq_rpow]
  rw [hrpow]
  have hs1 : 0 < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.mpr hn1
  have hd2 : (0 : ℝ) < 1 + (n : ℝ) ^ 2 := by positivity
  -- `352 log(n+3) · 4/(1+n²) ≤ 2816 √(n+3)/(1+n²) ≤ 5632 √(n+1)/(1+n²) ≤ 11264 /((n+1)√(n+1))`
  have hsqsq : Real.sqrt ((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 1) = (n : ℝ) + 1 :=
    Real.mul_self_sqrt hn1.le
  calc (352 * Real.log ((n : ℝ) + 3)) * (4 / (1 + (n : ℝ) ^ 2))
      ≤ (352 * (2 * (2 * Real.sqrt ((n : ℝ) + 1)))) * (4 / (1 + (n : ℝ) ^ 2)) := by
        gcongr
        exact hlog.trans (by linarith)
    _ = 5632 * Real.sqrt ((n : ℝ) + 1) / (1 + (n : ℝ) ^ 2) := by ring
    _ ≤ 11264 * (1 / (((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 1))) := by
        rw [mul_one_div, div_le_div_iff₀ hd2 (by positivity)]
        nlinarith [hden, hs1, hsqsq, mul_pos hs1 hs1]

/-- **The quadratic weight is summable over the multiplicity-expanded zeros.** -/
theorem summable_sq_index :
    Summable fun rho : CompletedZetaZeroIndex =>
      1 / (1 + ((nontrivialZetaZeroValue rho.1).im) ^ 2) := by
  refine summable_of_bucket_card_envelope
    (f := fun rho : CompletedZetaZeroIndex => 1 / (1 + ((nontrivialZetaZeroValue rho.1).im) ^ 2))
    (a := fun n : ℕ => 4 / (1 + (n : ℝ) ^ 2))
    (b := fun n : ℕ => if n = 0 then ((completedZetaZeroBucketFinset 0).card : ℝ)
      else 352 * Real.log ((n : ℝ) + 3))
    (fun rho => by simp only [Pi.zero_apply]; positivity)
    (fun n => by simp only [Pi.zero_apply]; positivity) ?_ ?_ sq_le_bucket
  · intro n
    by_cases hn : n = 0
    · subst hn; simp
    · rw [if_neg hn]
      exact Cvs.Zeta.ZeroDensityTail.bucketCard_le_num n (Nat.one_le_iff_ne_zero.mpr hn)
  · refine (summable_nat_add_iff 1).mp ?_
    refine summable_log_mul_sq.comp_injective (add_left_injective 1) |>.congr fun n => ?_
    simp [Function.comp_apply, Nat.succ_ne_zero]

/-- **The divisor weight times the quadratic weight is summable** over the nontrivial zero set. -/
theorem summable_divisorWeight_sq :
    Summable fun rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet =>
      (Cvs.Criterion.divisorWeight rho : ℝ) * (1 / (1 + ((rho : ℂ).im) ^ 2)) := by
  have h := Cvs.Criterion.summable_weighted_of_sigma
    (g := fun rho : nontrivialRiemannZetaZeros =>
      1 / (1 + ((nontrivialZetaZeroValue rho).im) ^ 2))
    summable_sq_index
  rw [← Cvs.Criterion.zeroEquiv.summable_iff]
  refine h.congr fun rho => ?_
  simp only [Function.comp_apply, Cvs.Criterion.divisorWeight, Equiv.symm_apply_apply,
    Cvs.Criterion.coe_zeroEquiv]

/-! ### The zero side of a linear-decay test is summable -/

end Cvs.Zeta.QuadraticWeightSummable
