import Mathlib
import Cvs.Zeta.CompletedZeroIndex
import Cvs.Zeta.GaussKernel.DivisorWeightCoordinates
import Cvs.Zeta.GaussKernel.DivisorWeightExpansion
import Cvs.Zeta.GaussKernel.ZetaZeroStatement
import Cvs.Zeta.QuadraticWeightSummable
import Cvs.Zeta.ZeroDensityTail
import Cvs.Zeta.ZetaZeroWindows

/-!
# The logarithmic envelope is square-summable over the zeros

`phi x = (1 + log(1+x))/(1+x)` is decreasing, dominates `1/(1+x)`, and scales by at most `K`
under `x ↦ x/K`. Its square, weighted by multiplicity, is summable over the zeros: on the
bucket `n` it is at most `4(1 + log(1+n))²/(1+n)²`, and against `Cvs.Zeta.ZeroDensityTail`'s `352·log(n+3)` zeros
per bucket the series is `O(n^{-3/2})` by `log y ≤ 8·y^{1/8}`.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Real Cvs.Zeta.Explicit.Venue

namespace Cvs.Zeta.LogEnvelopeSquareSummable

/-! ### The envelope -/

/-- The envelope `(1 + log(1+x))/(1+x)`. -/
def phi (x : ℝ) : ℝ := (1 + Real.log (1 + x)) / (1 + x)

theorem one_le_num {x : ℝ} (hx : 0 ≤ x) : 1 ≤ 1 + Real.log (1 + x) := by
  linarith [Real.log_nonneg (by linarith : (1:ℝ) ≤ 1 + x)]

theorem phi_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ phi x := by
  unfold phi; exact div_nonneg (by linarith [one_le_num hx]) (by linarith)

/-- `1/(1+x) ≤ phi x`. -/
theorem one_div_le_phi {x : ℝ} (hx : 0 ≤ x) : 1 / (1 + x) ≤ phi x := by
  unfold phi
  exact div_le_div_of_nonneg_right (one_le_num hx) (by linarith)

/-- **The envelope is decreasing.** -/
theorem phi_antitone {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : phi y ≤ phi x := by
  unfold phi
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  have hx1 : (0:ℝ) < 1 + x := by linarith
  have h := Real.log_le_sub_one_of_pos (div_pos (by linarith) hx1 : (0:ℝ) < (1 + y) / (1 + x))
  rw [Real.log_div (by linarith) hx1.ne'] at h
  have h2 : (Real.log (1 + y) - Real.log (1 + x)) * (1 + x) ≤ y - x := by
    have e : ((1 + y) / (1 + x) - 1) * (1 + x) = y - x := by field_simp; ring
    have := mul_le_mul_of_nonneg_right h hx1.le
    linarith
  have hlx : 0 ≤ Real.log (1 + x) := Real.log_nonneg (by linarith)
  nlinarith [h2, mul_le_mul_of_nonneg_left hxy hlx]

/-- **Scaling the argument down by `K ≥ 1` scales the envelope up by at most `K`.** -/
theorem phi_div_le {x K : ℝ} (hx : 0 ≤ x) (hK : 1 ≤ K) : phi (x / K) ≤ K * phi x := by
  unfold phi
  have hK0 : 0 < K := by linarith
  have hxK : 0 ≤ x / K := div_nonneg hx hK0.le
  have hnum : 1 + Real.log (1 + x / K) ≤ 1 + Real.log (1 + x) := by
    have : x / K ≤ x := div_le_self hx hK
    linarith [Real.log_le_log (by linarith) (by linarith : 1 + x / K ≤ 1 + x)]
  have hden : 1 / (1 + x / K) ≤ K / (1 + x) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    have : 1 + x / K = (K + x) / K := by field_simp
    have e : K * ((K + x) / K) = K + x := by field_simp
    rw [this, e]
    linarith
  calc (1 + Real.log (1 + x / K)) / (1 + x / K)
      = (1 + Real.log (1 + x / K)) * (1 / (1 + x / K)) := by ring
    _ ≤ (1 + Real.log (1 + x)) * (K / (1 + x)) :=
        mul_le_mul hnum hden (by positivity) (by linarith [one_le_num hx])
    _ = K * ((1 + Real.log (1 + x)) / (1 + x)) := by ring

/-! ### Summability of the square over the zeros -/

/-- `log y ≤ 8·y^{1/8}` for `y ≥ 1`, with the eighth root written as three square roots. -/
theorem log_le_eight_sqrt3 {y : ℝ} (hy : 1 ≤ y) :
    Real.log y ≤ 8 * Real.sqrt (Real.sqrt (Real.sqrt y)) := by
  have hy0 : 0 ≤ y := by linarith
  have h1 : Real.log y = 8 * Real.log (Real.sqrt (Real.sqrt (Real.sqrt y))) := by
    rw [Real.log_sqrt (Real.sqrt_nonneg _), Real.log_sqrt (Real.sqrt_nonneg _), Real.log_sqrt hy0]
    ring
  rw [h1]
  have hs : 0 < Real.sqrt (Real.sqrt (Real.sqrt y)) := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr
    (Real.sqrt_pos.mpr (by linarith)))
  linarith [Real.log_le_sub_one_of_pos hs]

/-- On the bucket `n`, the squared envelope is at most `4(1 + log(1+n))²/(1+n)²`. -/
theorem phi_sq_le_bucket (rho : CompletedZetaZeroIndex) :
    phi |(nontrivialZetaZeroValue rho.1).im| ^ 2
      ≤ 4 * (1 + Real.log (1 + ((completedZetaZeroBucket rho : ℕ) : ℝ))) ^ 2
        / (1 + ((completedZetaZeroBucket rho : ℕ) : ℝ)) ^ 2 := by
  set m : ℝ := |(nontrivialZetaZeroValue rho.1).im| with hm
  have hm0 : 0 ≤ m := abs_nonneg _
  set n : ℕ := completedZetaZeroBucket rho with hn
  have hnm : (n : ℝ) = (Nat.ceil m : ℝ) := by rw [hn, completedZetaZeroBucket]
  have hle : m ≤ (n : ℝ) := by rw [hnm]; exact Nat.le_ceil _
  have hlt : (n : ℝ) < m + 1 := by rw [hnm]; exact_mod_cast Nat.ceil_lt_add_one hm0
  have hnum : 1 + Real.log (1 + m) ≤ 1 + Real.log (1 + n) := by
    linarith [Real.log_le_log (by linarith) (by linarith : 1 + m ≤ 1 + n)]
  have hden : 1 / (1 + m) ≤ 2 / (1 + n) := by
    rw [div_le_div_iff₀ (by linarith) (by positivity)]; linarith
  have hphi : phi m ≤ 2 * (1 + Real.log (1 + n)) / (1 + n) := by
    unfold phi
    calc (1 + Real.log (1 + m)) / (1 + m) = (1 + Real.log (1 + m)) * (1 / (1 + m)) := by ring
      _ ≤ (1 + Real.log (1 + n)) * (2 / (1 + n)) :=
          mul_le_mul hnum hden (by positivity) (by linarith [one_le_num (Nat.cast_nonneg n)])
      _ = 2 * (1 + Real.log (1 + n)) / (1 + n) := by ring
  have h0 := phi_nonneg hm0
  calc phi m ^ 2 ≤ (2 * (1 + Real.log (1 + n)) / (1 + n)) ^ 2 := pow_le_pow_left₀ h0 hphi 2
    _ = 4 * (1 + Real.log (1 + n)) ^ 2 / (1 + n) ^ 2 := by rw [div_pow, mul_pow]; norm_num

/-- **The bucket series converges**: `352·log(n+3)·4(1 + log(1+n))²/(1+n)² = O(n^{-3/2})`. -/
theorem summable_log_cube :
    Summable fun n : ℕ => (352 * Real.log ((n : ℝ) + 3))
      * (4 * (1 + Real.log (1 + (n : ℝ))) ^ 2 / (1 + (n : ℝ)) ^ 2) := by
  have hbase : Summable (fun n : ℕ => 1 / |(n : ℝ) + 1| ^ (3 / 2 : ℝ)) :=
    (Real.summable_one_div_nat_add_rpow 1 (3 / 2)).mpr (by norm_num)
  refine (hbase.mul_left 1140480).of_nonneg_of_le (fun n => by
    have := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n] : (1:ℝ) ≤ (n : ℝ) + 3)
    positivity) fun n => ?_
  set y : ℝ := (n : ℝ) + 1 with hy
  have hy1 : 1 ≤ y := by rw [hy]; linarith [Nat.cast_nonneg (α := ℝ) n]
  have hy0 : 0 < y := by linarith
  -- the three roots
  set r : ℝ := Real.sqrt (Real.sqrt (Real.sqrt y)) with hr
  have hr1 : 1 ≤ r := by
    rw [hr]; exact Real.one_le_sqrt.mpr (Real.one_le_sqrt.mpr (Real.one_le_sqrt.mpr hy1))
  have hr2 : r * r = Real.sqrt (Real.sqrt y) := by rw [hr]; exact Real.mul_self_sqrt (Real.sqrt_nonneg _)
  have hr4 : Real.sqrt (Real.sqrt y) * Real.sqrt (Real.sqrt y) = Real.sqrt y :=
    Real.mul_self_sqrt (Real.sqrt_nonneg _)
  have hs1 : 1 ≤ Real.sqrt (Real.sqrt y) := Real.one_le_sqrt.mpr (Real.one_le_sqrt.mpr hy1)
  have hs2 : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy0
  have hss : Real.sqrt y * Real.sqrt y = y := Real.mul_self_sqrt hy0.le
  -- `log(n+3) ≤ 10 r`
  have hlog3 : Real.log ((n : ℝ) + 3) ≤ 10 * r := by
    have h1 : Real.log ((n : ℝ) + 3) ≤ Real.log (4 * y) :=
      Real.log_le_log (by linarith [Nat.cast_nonneg (α := ℝ) n]) (by rw [hy]; linarith)
    rw [Real.log_mul (by norm_num) hy0.ne'] at h1
    have h4 : Real.log 4 ≤ 2 := by
      have : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
      have := Real.log_two_lt_d9
      linarith
    have := log_le_eight_sqrt3 hy1
    rw [← hr] at this
    linarith
  -- `(1 + log y)² ≤ 81 r²`
  have hsq : (1 + Real.log y) ^ 2 ≤ 81 * (r * r) := by
    have h1 : 1 + Real.log y ≤ 9 * r := by
      have := log_le_eight_sqrt3 hy1
      rw [← hr] at this
      linarith
    have h0 : 0 ≤ 1 + Real.log y := by linarith [Real.log_nonneg hy1]
    nlinarith
  -- `r ≤ √√y`, so the product is at most `810 √y`
  have hrle : r ≤ Real.sqrt (Real.sqrt y) := by
    rw [← hr2]; nlinarith
  have hprod : Real.log ((n : ℝ) + 3) * (1 + Real.log y) ^ 2 ≤ 810 * Real.sqrt y := by
    calc Real.log ((n : ℝ) + 3) * (1 + Real.log y) ^ 2
        ≤ (10 * r) * (81 * (r * r)) := by
          refine mul_le_mul hlog3 hsq (by positivity) (by positivity)
      _ = 810 * (r * (r * r)) := by ring
      _ ≤ 810 * (Real.sqrt (Real.sqrt y) * Real.sqrt (Real.sqrt y)) := by
          rw [hr2]; gcongr
      _ = 810 * Real.sqrt y := by rw [hr4]
  have hrpow : |(n : ℝ) + 1| ^ (3 / 2 : ℝ) = y * Real.sqrt y := by
    rw [abs_of_pos (by linarith : (0:ℝ) < (n : ℝ) + 1), show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add (by linarith), Real.rpow_one, Real.sqrt_eq_rpow, hy]
  rw [hrpow, show (1 : ℝ) + (n : ℝ) = y by rw [hy]; ring, mul_one_div]
  rw [show (352 * Real.log ((n : ℝ) + 3)) * (4 * (1 + Real.log y) ^ 2 / y ^ 2)
      = 1408 * (Real.log ((n : ℝ) + 3) * (1 + Real.log y) ^ 2) / y ^ 2 by ring]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hy2 : y ^ 2 = y * y := by ring
  calc 1408 * (Real.log ((n : ℝ) + 3) * (1 + Real.log y) ^ 2) * (y * Real.sqrt y)
      ≤ 1408 * (810 * Real.sqrt y) * (y * Real.sqrt y) := by gcongr
    _ = 1140480 * y ^ 2 := by rw [hy2]; nlinarith [hss]

/-- **The squared envelope is summable over the multiplicity-expanded zeros.** -/
theorem summable_phi_sq_index :
    Summable fun rho : CompletedZetaZeroIndex =>
      phi |(nontrivialZetaZeroValue rho.1).im| ^ 2 := by
  refine Cvs.Zeta.QuadraticWeightSummable.summable_of_bucket_card_envelope
    (f := fun rho : CompletedZetaZeroIndex => phi |(nontrivialZetaZeroValue rho.1).im| ^ 2)
    (a := fun n : ℕ => 4 * (1 + Real.log (1 + (n : ℝ))) ^ 2 / (1 + (n : ℝ)) ^ 2)
    (b := fun n : ℕ => if n = 0 then ((completedZetaZeroBucketFinset 0).card : ℝ)
      else 352 * Real.log ((n : ℝ) + 3))
    (fun rho => by simp only [Pi.zero_apply]; positivity)
    (fun n => by simp only [Pi.zero_apply]; positivity) ?_ ?_ phi_sq_le_bucket
  · intro n
    by_cases hn : n = 0
    · subst hn; simp
    · rw [if_neg hn]
      exact Cvs.Zeta.ZeroDensityTail.bucketCard_le_num n (Nat.one_le_iff_ne_zero.mpr hn)
  · refine (summable_nat_add_iff 1).mp ?_
    refine summable_log_cube.comp_injective (add_left_injective 1) |>.congr fun n => ?_
    simp [Function.comp_apply]

/-- **The divisor weight times the squared envelope is summable** over the nontrivial zero set. -/
theorem summable_divisorWeight_phi_sq :
    Summable fun rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet =>
      (Cvs.Criterion.divisorWeight rho : ℝ) * phi |((rho : ℂ)).im| ^ 2 := by
  have h := Cvs.Criterion.summable_weighted_of_sigma
    (g := fun rho : nontrivialRiemannZetaZeros => phi |(nontrivialZetaZeroValue rho).im| ^ 2)
    summable_phi_sq_index
  rw [← Cvs.Criterion.zeroEquiv.summable_iff]
  refine h.congr fun rho => ?_
  simp only [Function.comp_apply, Cvs.Criterion.divisorWeight, Equiv.symm_apply_apply,
    Cvs.Criterion.coe_zeroEquiv]

end Cvs.Zeta.LogEnvelopeSquareSummable
