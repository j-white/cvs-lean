import Mathlib
import Cvs.Zeta.AllZerosOnLine
import Cvs.Zeta.CompletedXiOrderOneGrowth
import Cvs.Zeta.CompletedZeroIndex
import Cvs.Zeta.ZetaZeroWindows

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The statement about `ζ`

Everything before this is indexed by an abstract family `(γ, δ)`.
-/

open Complex Real

namespace Cvs.Zeta.GaussKernel.AdmissibleKernel

/-! ## The statement about `ζ`

Everything above is indexed by an abstract family.  With the coordinate bridge
the same result can be stated over the non-trivial zeros of `ζ` themselves, with
`γ = ρ.im` and `δ = ρ.re - 1/2`, and the conclusion in the form
`Cvs.Zeta.weilZeroSide` takes — unfolded, so no dependency is needed. -/

/-- The non-trivial zeros: `ζ ρ = 0` with `0 < re ρ < 1`.  This is
`Cvs.Zeta.IsNonTrivialZero` as a set. -/
def nonTrivialZeroSet : Set ℂ := {ρ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1}

/-- Non-trivial zeros lie in the strip, so `|δ| ≤ 1/2` is free. -/
theorem abs_re_sub_half_le (ρ : nonTrivialZeroSet) :
    |((ρ : ℂ).re - 1 / 2)| ≤ 1 / 2 := by
  obtain ⟨-, h0, h1⟩ := ρ.2
  rw [abs_le]; constructor <;> linarith

/-!
## From the counting law to the arithmetic input

The counting law is a statement about `N(T)`; what the summability argument needs is a
statement about a sum over zeros.
-/

/-- The bucket majorant is summable against the counting law.  `N(n) ≤ C n log n`
from `Cvs.Zeta.Explicit.Venue.nontrivialZetaZeroCountBigO_proved`, weakened to
`C n²`, against `16/(1 + n⁴)`. -/
theorem summable_count_mul_quartic :
    Summable fun n : ℕ =>
      (Cvs.Zeta.Explicit.Venue.nontrivialZetaZeroCount n : ℝ) * (16 / (1 + (n : ℝ) ^ 4)) := by
  rcases Cvs.Zeta.Explicit.Venue.nontrivialZetaZeroCountBigO_proved with ⟨C, T0, hC, hT0, hcount⟩
  have hgbase : Summable (fun n : ℕ => 1 / |(n : ℝ) + 1| ^ (2 : ℝ)) :=
    (Real.summable_one_div_nat_add_rpow 1 2).mpr (by norm_num)
  have hg : Summable (fun n : ℕ => (64 * C) * (1 / |(n : ℝ) + 1| ^ (2 : ℝ))) :=
    hgbase.mul_left _
  apply hg.of_norm_bounded_eventually_nat
  filter_upwards [Filter.eventually_atTop.2 ⟨Nat.ceil T0, fun _ hn => hn⟩,
    Filter.eventually_atTop.2 ⟨1, fun _ hn => hn⟩] with n hnT hn1
  have hnTreal : T0 ≤ (n : ℝ) := Nat.ceil_le.mp hnT
  have hn1r : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hnpos : (0 : ℝ) < n := by linarith
  have hlog : Real.log n ≤ (n : ℝ) :=
    (Real.log_le_sub_one_of_pos hnpos).trans (by linarith)
  have hN : (Cvs.Zeta.Explicit.Venue.nontrivialZetaZeroCount n : ℝ) ≤ C * (n : ℝ) ^ 2 := by
    calc (Cvs.Zeta.Explicit.Venue.nontrivialZetaZeroCount n : ℝ)
        ≤ C * (n : ℝ) * Real.log n := hcount n hnTreal
      _ ≤ C * (n : ℝ) * (n : ℝ) :=
        mul_le_mul_of_nonneg_left hlog (mul_nonneg hC (by linarith))
      _ = C * (n : ℝ) ^ 2 := by ring
  have hden : (0 : ℝ) < 1 + (n : ℝ) ^ 4 := by positivity
  have hterm : (0 : ℝ) ≤ (Cvs.Zeta.Explicit.Venue.nontrivialZetaZeroCount n : ℝ)
      * (16 / (1 + (n : ℝ) ^ 4)) := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hterm,
    abs_of_pos (by linarith : (0 : ℝ) < (n : ℝ) + 1), Real.rpow_two]
  have hstep : (Cvs.Zeta.Explicit.Venue.nontrivialZetaZeroCount n : ℝ) * (16 / (1 + (n : ℝ) ^ 4))
      ≤ (C * (n : ℝ) ^ 2) * (16 / (1 + (n : ℝ) ^ 4)) := by gcongr
  refine hstep.trans ?_
  have hpos1 : (0 : ℝ) < ((n : ℝ) + 1) ^ 2 := by positivity
  have key : (n : ℝ) ^ 2 * ((n : ℝ) + 1) ^ 2 ≤ 4 * (1 + (n : ℝ) ^ 4) := by
    nlinarith [sq_nonneg ((n : ℝ) - 1), sq_nonneg ((n : ℝ) ^ 2 - 1), hn1r]
  rw [mul_div_assoc', div_le_iff₀ hden,
    show (64 * C) * (1 / ((n : ℝ) + 1) ^ 2) * (1 + (n : ℝ) ^ 4)
      = 64 * C * (1 + (n : ℝ) ^ 4) / ((n : ℝ) + 1) ^ 2 by ring,
    le_div_iff₀ hpos1]
  nlinarith [mul_le_mul_of_nonneg_left key (by positivity : (0 : ℝ) ≤ 16 * C)]

/-- On the ceiling bucket `n`, the quartic weight is at most `16/(1 + n⁴)`.
A zero in bucket `n` has `|γ| > n - 1`, and for `n ≥ 2` that is at least `n/2`. -/
theorem quartic_le_bucket (rho : Cvs.Zeta.Explicit.Venue.CompletedZetaZeroIndex) :
    1 / (1 + ((Cvs.Zeta.Explicit.Venue.nontrivialZetaZeroValue rho.1).im) ^ 4)
      ≤ 16 / (1 + ((Cvs.Zeta.Explicit.Venue.completedZetaZeroBucket rho : ℕ) : ℝ) ^ 4) := by
  set m : ℝ := |(Cvs.Zeta.Explicit.Venue.nontrivialZetaZeroValue rho.1).im| with hm
  have hm0 : 0 ≤ m := abs_nonneg _
  set n : ℕ := Cvs.Zeta.Explicit.Venue.completedZetaZeroBucket rho with hn
  have hnm : (n : ℝ) = (Nat.ceil m : ℝ) := by
    rw [hn, Cvs.Zeta.Explicit.Venue.completedZetaZeroBucket]
  have hle : m ≤ (n : ℝ) := by rw [hnm]; exact Nat.le_ceil _
  have hlt : (n : ℝ) < m + 1 := by rw [hnm]; exact_mod_cast Nat.ceil_lt_add_one hm0
  have him4 : ((Cvs.Zeta.Explicit.Venue.nontrivialZetaZeroValue rho.1).im) ^ 4 = m ^ 4 := by
    rw [hm, show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, sq_abs]
  rw [him4]
  have hd1 : (0 : ℝ) < 1 + m ^ 4 := by positivity
  have hd2 : (0 : ℝ) < 1 + (n : ℝ) ^ 4 := by positivity
  rw [div_le_div_iff₀ hd1 hd2]
  rcases le_or_gt (n : ℝ) 1 with h | h
  · have hn4 : (n : ℝ) ^ 4 ≤ 1 := pow_le_one₀ (Nat.cast_nonneg n) h
    nlinarith [pow_nonneg hm0 4]
  · have hn1n : 1 < n := by exact_mod_cast h
    have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 2 ≤ n)
    have hm1 : 1 ≤ m := by linarith
    have hn2m : (n : ℝ) ≤ 2 * m := by linarith
    nlinarith [pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ (n : ℝ)) hn2m 4,
      pow_nonneg hm0 4]

/-- The quartic weight is summable over the multiplicity-expanded zeros. -/
theorem summable_quartic_index :
    Summable fun rho : Cvs.Zeta.Explicit.Venue.CompletedZetaZeroIndex =>
      1 / (1 + ((Cvs.Zeta.Explicit.Venue.nontrivialZetaZeroValue rho.1).im) ^ 4) := by
  refine Cvs.Zeta.Explicit.Venue.summable_completedZetaZeroIndex_of_bucket_envelope
    (f := fun rho : Cvs.Zeta.Explicit.Venue.CompletedZetaZeroIndex =>
      1 / (1 + ((Cvs.Zeta.Explicit.Venue.nontrivialZetaZeroValue rho.1).im) ^ 4))
    (a := fun n : ℕ => 16 / (1 + (n : ℝ) ^ 4)) ?_ ?_ ?_ quartic_le_bucket
  · intro rho; simp only [Pi.zero_apply]; positivity
  · intro n; simp only [Pi.zero_apply]; positivity
  · simpa using summable_count_mul_quartic

/-- Each non-trivial zero gives a multiplicity-expanded index; multiplicity is
positive, so the fibre is nonempty and the map is defined. -/
noncomputable def toZeroIndex (ρ : nonTrivialZeroSet) :
    Cvs.Zeta.Explicit.Venue.CompletedZetaZeroIndex :=
  ⟨⟨⟨(ρ : ℂ), by simpa [riemannZetaZeros] using ρ.2.1⟩, ρ.2.2.1, ρ.2.2.2⟩,
    ⟨0, Cvs.Zeta.Explicit.Venue.completedZetaZeroMultiplicity_pos _⟩⟩

theorem toZeroIndex_value (ρ : nonTrivialZeroSet) :
    Cvs.Zeta.Explicit.Venue.nontrivialZetaZeroValue (toZeroIndex ρ).1 = (ρ : ℂ) := rfl

theorem toZeroIndex_injective : Function.Injective toZeroIndex := fun ρ σ h =>
  Subtype.ext (by rw [← toZeroIndex_value ρ, ← toZeroIndex_value σ, h])

/-- **The arithmetic input, proved.** -/
theorem summable_zeta_quartic :
    Summable fun ρ : nonTrivialZeroSet => 1 / (1 + ((ρ : ℂ).im) ^ 4) := by
  have h : Summable ((fun rho : Cvs.Zeta.Explicit.Venue.CompletedZetaZeroIndex =>
      1 / (1 + ((Cvs.Zeta.Explicit.Venue.nontrivialZetaZeroValue rho.1).im) ^ 4))
        ∘ toZeroIndex) :=
    summable_quartic_index.comp_injective toZeroIndex_injective
  refine h.congr fun ρ => ?_
  rw [Function.comp_apply, toZeroIndex_value]

/-!
## The maximality is only needed locally

A competitor far from both bumps needs no `δ`-comparison at all: in the strip `δ² ≤ 1/4`, so
`|γ ∓ a| > 1/2` already forces both outer rates below `0 < c₀`, and `a ≥ 1/2` does the same
for the cross term.
-/

/-!
## When a local maximiser exists

With the neighbourhood at fixed radius the circularity has a criterion.
-/

/-!
## What evading the construction would require

Suppose the second branch of `local_max_or_beats` holds at every integer scale.
-/

/-- The chain's members are pairwise distinct, so the evasion needs infinitely
many off-line zeros. -/
theorem evasion_chain_injective {ι : Type*} {γ δ : ι → ℝ} {c : ℕ → ι}
    (h : StrictMono (fun n => (δ (c n)) ^ 2)) : Function.Injective c :=
  fun m n hmn => h.injective (by rw [show c m = c n from hmn])

/-!
## The strip characterisation, from the functional equation

A zero with `re ≤ 0` must be trivial.
-/

/-- **A zero with `re ≤ 0` is trivial.** -/
theorem exists_eq_neg_two_mul_of_zero_of_re_nonpos {s : ℂ}
    (hz : riemannZeta s = 0) (hre : s.re ≤ 0) : ∃ n : ℕ, s = -(2 * n) := by
  by_cases hG : Complex.Gammaℝ s = 0
  · exact Complex.Gammaℝ_eq_zero_iff.mp hG
  · exfalso
    have hs0 : s ≠ 0 := fun h => hG (Complex.Gammaℝ_eq_zero_iff.mpr ⟨0, by simp [h]⟩)
    have hL : completedRiemannZeta s = 0 := by
      have hdef := riemannZeta_def_of_ne_zero hs0
      rw [hz] at hdef
      rcases div_eq_zero_iff.mp hdef.symm with h | h
      · exact h
      · exact absurd h hG
    have hre1 : (0 : ℝ) < (1 - s).re := by simp; linarith
    have hone : (1 : ℝ) ≤ (1 - s).re := by simp; linarith
    have hG1 : Complex.Gammaℝ (1 - s) ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hre1
    have hs1 : (1 : ℂ) - s ≠ 0 := fun h => by
      rw [h] at hre1; simp at hre1
    have hz1 : riemannZeta (1 - s) ≠ 0 := riemannZeta_ne_zero_of_one_le_re hone
    have hdef1 := riemannZeta_def_of_ne_zero hs1
    rw [completedRiemannZeta_one_sub, hL, zero_div] at hdef1
    exact hz1 hdef1

/-- The strip characterisation the assembly asks for, now a theorem: a
non-trivial zero other than `1` lies in `0 < re < 1`. -/
theorem mem_strip_of_nonTrivial {s : ℂ} (hz : riemannZeta s = 0)
    (htriv : ¬(∃ n : ℕ, s = -2 * (n + 1))) (_hone : s ≠ 1) :
    0 < s.re ∧ s.re < 1 := by
  refine ⟨?_, ?_⟩
  · by_contra h
    obtain ⟨n, hn⟩ := exists_eq_neg_two_mul_of_zero_of_re_nonpos hz (not_lt.mp h)
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · rw [hn] at hz
      norm_num [riemannZeta_zero] at hz
    · refine htriv ⟨n - 1, ?_⟩
      have hcast : ((n - 1 : ℕ) : ℂ) = (n : ℂ) - 1 := by
        have h1 : (1 : ℕ) ≤ n := hpos
        push_cast [Nat.cast_sub h1]
        ring
      rw [hn, hcast]; ring
  · by_contra h
    exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h) hz

/-!
## Connecting to `B8`'s statement of RH

`Cvs.Operator.AllZerosOnLine` is `RiemannHypothesis` definitionally (`Cvs.Operator.allZerosOnLine_iff_rh`).
-/

/-- **`¬RH` supplies the target**, with no side condition: the strip membership
is `mem_strip_of_nonTrivial`, proved above from the functional equation. -/
theorem exists_offLine_of_not_allZerosOnLine (hnot : ¬ Cvs.Operator.AllZerosOnLine) :
    ∃ ρ : nonTrivialZeroSet, (ρ : ℂ).re ≠ 1 / 2 := by
  rw [Cvs.Operator.AllZerosOnLine] at hnot
  push Not at hnot
  obtain ⟨s, hz, htriv, hone, hre⟩ := hnot
  obtain ⟨h0, h1⟩ := mem_strip_of_nonTrivial hz (not_exists.mpr htriv) hone
  exact ⟨⟨s, hz, h0, h1⟩, hre⟩

end Cvs.Zeta.GaussKernel.AdmissibleKernel
