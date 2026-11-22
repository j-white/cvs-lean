import Mathlib
import Cvs.Zeta.CompletedZeroIndex
import Cvs.Zeta.ZeroBucketIncrement
import Cvs.Zeta.ZetaSeamStatement
import Cvs.Zeta.ZetaZeroConfig
import Cvs.Zeta.ZetaZeroWindows

/-!
# The local count, transferred

`Cvs.Zeta.Base.RvM.zeta_local_zero_count` bounds a unit window of ordinates; the bucket is
`⌈|γ|⌉ = n`, which is two of them.  The multiplicities are the same object on both sides.
RH.md §3.20 carries the ladder.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Real Finset Cvs.Zeta.Explicit.Venue

namespace Cvs.Zeta.LocalCountTransfer

/-- **The multiplicities are the same object.**  `analyticOrderNatAt` is `.toNat` of
`analyticOrderAt`, which is what `Cvs.Zeta.Base.zeroMult` is. -/
theorem mult_eq (rho : nontrivialRiemannZetaZeros) :
    completedZetaZeroMultiplicity rho = Cvs.Zeta.Base.zeroMult (nontrivialZetaZeroValue rho) := rfl

/-- A venue zero is a `Cvs.Zeta.Base` nontrivial zero. -/
theorem isNontrivialZero (rho : nontrivialRiemannZetaZeros) :
    Cvs.Zeta.Base.IsNontrivialZero (nontrivialZetaZeroValue rho) :=
  ⟨rho.1.2, rho.2.1, rho.2.2⟩

/-- **A venue sum inside an ordinate window is under `Ncount`.** -/
theorem sum_le_Ncount {a b : ℝ} (F : Finset nontrivialRiemannZetaZeros)
    (hF : ∀ rho ∈ F, a < (nontrivialZetaZeroValue rho).im
      ∧ (nontrivialZetaZeroValue rho).im ≤ b) :
    ∑ rho ∈ F, completedZetaZeroMultiplicity rho ≤ Cvs.Zeta.Base.Ncount a b := by
  classical
  have hinj : ∀ x ∈ F, ∀ y ∈ F,
      nontrivialZetaZeroValue x = nontrivialZetaZeroValue y → x = y :=
    fun x _ y _ h => nontrivialZetaZeroEmbedding.injective h
  have hrw : ∑ rho ∈ F, completedZetaZeroMultiplicity rho
      = ∑ z ∈ F.image nontrivialZetaZeroValue, Cvs.Zeta.Base.zeroMult z := by
    rw [Finset.sum_image hinj]
    exact Finset.sum_congr rfl fun rho _ => mult_eq rho
  rw [hrw, Cvs.Zeta.Base.Ncount,
    finsum_mem_eq_finite_toFinset_sum _ (Cvs.Zeta.Base.zerosIn_finite a b)]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => Nat.zero_le _)
  intro z hz
  obtain ⟨rho, hrho, rfl⟩ := Finset.mem_image.mp hz
  exact (Set.Finite.mem_toFinset _).mpr ⟨isNontrivialZero rho, (hF rho hrho).1, (hF rho hrho).2⟩

/-- **The bucket, as a sum over the venue's zeros.**  `Cvs.Zeta.ZeroBucketIncrement`'s identity, read as a filter
split rather than a cardinality. -/
theorem card_bucket_eq (n : ℕ) (hn : 1 ≤ n) :
    (completedZetaZeroBucketFinset n).card
      = ∑ rho ∈ (nontrivialZetaZeroWindowFinset (n : ℝ)).filter
          (fun rho => ¬ (|(nontrivialZetaZeroValue rho).im| ≤ ((n - 1 : ℕ) : ℝ))),
        completedZetaZeroMultiplicity rho := by
  classical
  have hle : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.sub_le n 1
  have hlow : nontrivialZetaZeroWindowFinset ((n - 1 : ℕ) : ℝ)
      = (nontrivialZetaZeroWindowFinset (n : ℝ)).filter
          (fun rho => |(nontrivialZetaZeroValue rho).im| ≤ ((n - 1 : ℕ) : ℝ)) := by
    ext rho
    rw [Finset.mem_filter, mem_nontrivialZetaZeroWindowFinset,
      mem_nontrivialZetaZeroWindowFinset]
    exact ⟨fun h => ⟨h.trans hle, h⟩, fun h => h.2⟩
  have hsplit := Finset.sum_filter_add_sum_filter_not
      (nontrivialZetaZeroWindowFinset (n : ℝ))
      (fun rho => |(nontrivialZetaZeroValue rho).im| ≤ ((n - 1 : ℕ) : ℝ))
      completedZetaZeroMultiplicity
  have hadd := Cvs.Zeta.ZeroBucketIncrement.card_bucketFinset_add hn
  rw [nontrivialZetaZeroCount, nontrivialZetaZeroCount, hlow] at hadd
  omega

/-- **The bucket is under three unit windows.**  `⌈|γ|⌉ = n` is `(n−1, n]` on one side and
`[−n, 1−n)` on the other, and the second needs two windows because `−n` sits at an endpoint. -/
theorem bucketCard_le_Ncount (n : ℕ) (hn : 1 ≤ n) :
    (completedZetaZeroBucketFinset n).card
      ≤ Cvs.Zeta.Base.Ncount ((n : ℝ) - 1) (((n : ℝ) - 1) + 1)
        + (Cvs.Zeta.Base.Ncount (-(n : ℝ) - 1) ((-(n : ℝ) - 1) + 1)
          + Cvs.Zeta.Base.Ncount (-(n : ℝ)) ((-(n : ℝ)) + 1)) := by
  classical
  set F := (nontrivialZetaZeroWindowFinset (n : ℝ)).filter
      (fun rho => ¬ (|(nontrivialZetaZeroValue rho).im| ≤ ((n - 1 : ℕ) : ℝ))) with hF
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    have h1 : (1:ℕ) ≤ n := hn
    push_cast [Nat.cast_sub h1]; ring
  have hmem : ∀ rho ∈ F, (n : ℝ) - 1 < |(nontrivialZetaZeroValue rho).im|
      ∧ |(nontrivialZetaZeroValue rho).im| ≤ (n : ℝ) := by
    intro rho hrho
    rw [hF, Finset.mem_filter, mem_nontrivialZetaZeroWindowFinset] at hrho
    exact ⟨by rw [← hcast]; exact not_le.mp hrho.2, hrho.1⟩
  rw [card_bucket_eq n hn, ← hF]
  have hs1 := Finset.sum_filter_add_sum_filter_not F
      (fun rho => 0 < (nontrivialZetaZeroValue rho).im) completedZetaZeroMultiplicity
  have hs2 := Finset.sum_filter_add_sum_filter_not
      (F.filter (fun rho => ¬ (0 < (nontrivialZetaZeroValue rho).im)))
      (fun rho => (nontrivialZetaZeroValue rho).im ≤ -(n : ℝ)) completedZetaZeroMultiplicity
  -- the positive side
  have hA : ∑ rho ∈ F.filter (fun rho => 0 < (nontrivialZetaZeroValue rho).im),
      completedZetaZeroMultiplicity rho
      ≤ Cvs.Zeta.Base.Ncount ((n : ℝ) - 1) (((n : ℝ) - 1) + 1) := by
    refine sum_le_Ncount _ (fun rho hrho => ?_)
    rw [Finset.mem_filter] at hrho
    have hb := hmem rho hrho.1
    have hpos : 0 < (nontrivialZetaZeroValue rho).im := hrho.2
    rw [abs_of_pos hpos] at hb
    exact ⟨hb.1, by linarith [hb.2]⟩
  -- the negative side, at the endpoint
  have hB : ∑ rho ∈ (F.filter (fun rho => ¬ (0 < (nontrivialZetaZeroValue rho).im))).filter
        (fun rho => (nontrivialZetaZeroValue rho).im ≤ -(n : ℝ)),
      completedZetaZeroMultiplicity rho
      ≤ Cvs.Zeta.Base.Ncount (-(n : ℝ) - 1) ((-(n : ℝ) - 1) + 1) := by
    refine sum_le_Ncount _ (fun rho hrho => ?_)
    rw [Finset.mem_filter, Finset.mem_filter] at hrho
    have hb := hmem rho hrho.1.1
    have hnp : (nontrivialZetaZeroValue rho).im ≤ 0 := not_lt.mp hrho.1.2
    rw [abs_of_nonpos hnp] at hb
    exact ⟨by linarith [hb.2], by linarith [hrho.2]⟩
  -- and the rest of it
  have hC : ∑ rho ∈ (F.filter (fun rho => ¬ (0 < (nontrivialZetaZeroValue rho).im))).filter
        (fun rho => ¬ ((nontrivialZetaZeroValue rho).im ≤ -(n : ℝ))),
      completedZetaZeroMultiplicity rho
      ≤ Cvs.Zeta.Base.Ncount (-(n : ℝ)) ((-(n : ℝ)) + 1) := by
    refine sum_le_Ncount _ (fun rho hrho => ?_)
    rw [Finset.mem_filter, Finset.mem_filter] at hrho
    have hb := hmem rho hrho.1.1
    have hnp : (nontrivialZetaZeroValue rho).im ≤ 0 := not_lt.mp hrho.1.2
    rw [abs_of_nonpos hnp] at hb
    exact ⟨not_le.mp hrho.2, by linarith [hb.1]⟩
  omega

/-- `log(x+4) ≤ log(x+3) + 1/4` for `x ≥ 1`. -/
theorem log_add_four_le {x : ℝ} (hx : 1 ≤ x) :
    Real.log (x + 4) ≤ Real.log (x + 3) + 1/4 := by
  have h3 : (0:ℝ) < x + 3 := by linarith
  have h := Real.log_le_sub_one_of_pos (x := (x + 4) / (x + 3)) (by positivity)
  rw [Real.log_div (by linarith) h3.ne'] at h
  have hid : (x + 4) / (x + 3) - 1 = 1 / (x + 3) := by field_simp; ring
  have hq : 1 / (x + 3) ≤ 1/4 := by
    rw [div_le_div_iff₀ h3 (by norm_num)]
    linarith
  linarith [hid ▸ h, hq]

/-- **The per-bucket count, with `log`.**  Three unit windows of `zeta_local_zero_count`. -/
theorem bucketCard_le_log_of {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hA : ∀ t : ℝ, (Cvs.Zeta.Base.Ncount t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)) :
    ∀ n : ℕ, 1 ≤ n →
      ((completedZetaZeroBucketFinset n).card : ℝ) ≤ 4 * A₀ * Real.log ((n : ℝ) + 3) := by
  intro n hn
  have hnR : (1:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlog3 : (1:ℝ) ≤ Real.log ((n : ℝ) + 3) := by
    have h4 : (4:ℝ) ≤ (n : ℝ) + 3 := by linarith
    calc (1:ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log ((n : ℝ) + 3) := by
          refine Real.log_le_log (Real.exp_pos 1) ?_
          nlinarith [Real.exp_one_lt_d9]
  have hcard := bucketCard_le_Ncount n hn
  have h1 := hA ((n : ℝ) - 1)
  have h2 := hA (-(n : ℝ) - 1)
  have h3 := hA (-(n : ℝ))
  -- each window's log against `log(n+3)`
  have e1 : |(n : ℝ) - 1| + 3 ≤ (n : ℝ) + 3 := by
    rw [abs_of_nonneg (by linarith)]; linarith
  have e2 : |-(n : ℝ) - 1| + 3 = (n : ℝ) + 4 := by
    rw [abs_of_nonpos (by linarith)]; ring
  have e3 : |-(n : ℝ)| + 3 = (n : ℝ) + 3 := by
    rw [abs_of_nonpos (by linarith)]; ring
  have b1 : Real.log (|(n : ℝ) - 1| + 3) ≤ Real.log ((n : ℝ) + 3) :=
    Real.log_le_log (by positivity) e1
  have b2 : Real.log (|-(n : ℝ) - 1| + 3) ≤ Real.log ((n : ℝ) + 3) + 1/4 := by
    rw [e2]; exact log_add_four_le hnR
  have b3 : Real.log (|-(n : ℝ)| + 3) = Real.log ((n : ℝ) + 3) := by rw [e3]
  have hA0 : (0:ℝ) ≤ A₀ := by linarith
  have hsum : ((completedZetaZeroBucketFinset n).card : ℝ)
      ≤ A₀ * Real.log (|(n : ℝ) - 1| + 3)
        + (A₀ * Real.log (|-(n : ℝ) - 1| + 3) + A₀ * Real.log (|-(n : ℝ)| + 3)) := by
    have := (Nat.cast_le (α := ℝ)).mpr hcard
    push_cast at this
    linarith [this, h1, h2, h3]
  calc ((completedZetaZeroBucketFinset n).card : ℝ)
      ≤ A₀ * Real.log (|(n : ℝ) - 1| + 3)
        + (A₀ * Real.log (|-(n : ℝ) - 1| + 3) + A₀ * Real.log (|-(n : ℝ)| + 3)) := hsum
    _ ≤ 4 * A₀ * Real.log ((n : ℝ) + 3) := by
        rw [b3]
        nlinarith [b1, b2, hA0, hlog3]

end Cvs.Zeta.LocalCountTransfer
