import Mathlib
import Cvs.L2a.FirstModeHigherModePair
import Cvs.L2a.PrimeTermPairClassified
import Cvs.L2a.StationaryPairsWeightedTotal
import Cvs.L2a.TailCrossModeCounts
import Cvs.L2a.TailOfModes
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.ProlateArcsinMassLaw
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The norm of the tail of `M` modes, from below

`∫F² = Σ_{m,m'} ∫_1^b ψ(mθ)ψ(m'θ)` is at least the first mode's mass past `ξ₀` (the arcsin law, Cvs.Prolate.LiouvilleGreen.ProlateArcsinMassLaw) less the
cross terms: `N ≥ G_m(arccos(1/b) − arccos(1/ξ₀))/(2c) − G/(2q(ξ₀)) − 2G X̄ − (4G√κ/c²)·3(π²/6 + 6)`,
for every `M`, with window scale `1 ≤ s`, `s² ≤ c`.
-/

namespace Cvs.L2a.TailModesNormLower

open Real Set MeasureTheory Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.TailOfModes
open Cvs.L2a.StationaryPairsWeightedTotal (Aw Qw κw)

set_option maxHeartbeats 1000000 in
/-- **The norm of the tail, from below.** -/
theorem norm_ge {c χ G K Gm Ξ ξ₀ s : ℝ} {ψ u : ℝ → ℝ} (M J : ℕ)
    (hc : 1 ≤ c) (hχ0 : 0 ≤ χ) (hχ : χ < c ^ 2) (hχs : χ ≤ c * √c) (hs1 : 1 ≤ s) (hsc : s ^ 2 ≤ c)
    (hb3 : (3 : ℝ) ≤ 2 ^ (J + 1)) (hΞ : (M : ℝ) * 2 ^ (J + 1) ≤ Ξ)
    (hψ : ∀ ξ ∈ Ioc 1 Ξ, HasDerivAt ψ (u ξ / pP ξ) ξ)
    (hu : ∀ ξ ∈ Ioc 1 Ξ, HasDerivAt u (-(qP c χ ξ * ψ ξ)) ξ)
    (hG : ∀ ξ ∈ Ioc 1 Ξ, energy (aP c χ) ψ u ξ ≤ G) (hG0 : 0 ≤ G) (hK : 0 ≤ K)
    (hcont : ContinuousOn ψ (Icc 1 Ξ)) (hedge : ∀ ξ ∈ Icc 1 Ξ, |ψ ξ| ≤ |ψ 1|) (hedge1 : ψ 1 ^ 2 ≤ K * G)
    (h1ξ : 1 < ξ₀) (hξb : ξ₀ ≤ 2 ^ (J + 1)) (hGm : ∀ t ∈ Icc ξ₀ (2 ^ (J + 1)), Gm ≤ energy (aP c χ) ψ u t)
    (hGm0 : 0 ≤ Gm) (hM : 1 ≤ M) :
    Gm * (arccos (1 / 2 ^ (J + 1)) - arccos (1 / ξ₀)) / (2 * c) - G / (2 * qP c χ ξ₀)
        - 2 * G * Cvs.L2a.FirstModeHigherModePair.Xbar c χ K s
        - 4 * G * √(2 * c / (√3 * √(c ^ 2 - χ))) / c ^ 2 * (3 * (π ^ 2 / 6 + 6))
      ≤ ∫ θ in Ioi 1, tailF ψ M (2 ^ (J + 1)) θ ^ 2 := by
  set b : ℝ := 2 ^ (J + 1) with hbdef
  have hc0 : 0 < c := by linarith
  have hs0 : 0 < s := by linarith
  have hb1 : (1 : ℝ) ≤ b := by linarith
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hbΞ : b ≤ Ξ := le_trans (by nlinarith) hΞ
  set κs := √(2 * c / (√3 * √(c ^ 2 - χ))) with hκs
  have hκ0 : 0 ≤ κs := sqrt_nonneg _
  set I : ℕ → ℕ → ℝ := fun m m' => ∫ θ in (1 : ℝ)..b, ψ (m * θ) * ψ (m' * θ) with hI
  -- the norm as a double sum
  have hN : ∫ θ in Ioi 1, tailF ψ M b θ ^ 2 = ∑ m ∈ Finset.Icc 1 M, ∑ m' ∈ Finset.Icc 1 M, I m m' := by
    have e : (fun θ => tailF ψ M b θ ^ 2) = fun θ => tailF ψ M b θ * tailF ψ M b (1 * θ) := by
      funext θ; rw [one_mul]; ring
    rw [e, integral_tailF_pair ψ ψ M le_rfl hb1 (hcont.mono (Icc_subset_Icc le_rfl hΞ)) (hcont.mono (Icc_subset_Icc le_rfl hΞ))]
    apply Finset.sum_congr rfl; intro m _; apply Finset.sum_congr rfl; intro m' _
    rw [hI]; simp only [div_one, one_mul]
  rw [hN]
  -- split off the diagonal
  have hsplit : ∀ m ∈ Finset.Icc 1 M, ∑ m' ∈ Finset.Icc 1 M, I m m' = I m m + ∑ m' ∈ (Finset.Icc 1 M).erase m, I m m' :=
    fun m hm => (Finset.add_sum_erase _ _ hm).symm
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  -- the diagonal is at least the first mode's mass
  have hdiag0 : ∀ m, 0 ≤ I m m := fun m => by
    rw [hI]; simp only
    exact intervalIntegral.integral_nonneg (μ := volume) hb1 (fun θ _ => mul_self_nonneg _)
  have h1mem : 1 ∈ Finset.Icc 1 M := Finset.mem_Icc.mpr ⟨le_rfl, hM⟩
  have hdiag : I 1 1 ≤ ∑ m ∈ Finset.Icc 1 M, I m m := by
    rw [← Finset.add_sum_erase _ _ h1mem]
    have := Finset.sum_nonneg (fun m (_ : m ∈ (Finset.Icc 1 M).erase 1) => hdiag0 m)
    linarith
  -- the first mode's mass past ξ₀
  have hmass : Gm * (arccos (1 / b) - arccos (1 / ξ₀)) / (2 * c) - G / (2 * qP c χ ξ₀) ≤ I 1 1 := by
    have hsub : ∀ t ∈ Icc ξ₀ b, t ∈ Ioc 1 Ξ := fun t ht => ⟨lt_of_lt_of_le h1ξ ht.1, ht.2.trans hbΞ⟩
    have hm := (Cvs.Prolate.LiouvilleGreen.ProlateArcsinMassLaw.prolate_mass_bounds (c := c) (χ := χ) (ψ := ψ) (u := u) h1ξ hξb hc0 hχ0 hχ
      (fun t ht => hψ t (hsub t ht)) (fun t ht => hu t (hsub t ht)) hGm (fun t ht => hG t (hsub t ht)) hGm0).1
    have hc1 : ContinuousOn (fun θ => ψ θ ^ 2) (Icc 1 b) :=
      (hcont.mono (Icc_subset_Icc le_rfl hbΞ)).pow 2
    have hsplit2 := intervalIntegral.integral_add_adjacent_intervals
      ((hc1.mono (Icc_subset_Icc le_rfl hξb)).intervalIntegrable_of_Icc (μ := volume) h1ξ.le)
      ((hc1.mono (Icc_subset_Icc h1ξ.le le_rfl)).intervalIntegrable_of_Icc (μ := volume) hξb)
    have hpos : 0 ≤ ∫ θ in (1 : ℝ)..ξ₀, ψ θ ^ 2 := intervalIntegral.integral_nonneg (μ := volume) h1ξ.le (fun θ _ => sq_nonneg _)
    have e : I 1 1 = ∫ θ in (1 : ℝ)..b, ψ θ ^ 2 := by
      rw [hI]; simp only [Nat.cast_one, one_mul]; congr 1; funext θ; ring
    rw [e, ← hsplit2]
    linarith
  -- each off-diagonal pair
  have hcross : ∀ m ∈ Finset.Icc 1 M, ∀ m' ∈ (Finset.Icc 1 M).erase m,
      -((if m = 1 then G * Cvs.L2a.FirstModeHigherModePair.X c χ K s m' else 0)
        + (if m' = 1 then G * Cvs.L2a.FirstModeHigherModePair.X c χ K s m else 0)
        + 4 * G * κs / c ^ 2 * (1 / ((m : ℝ) * m' * |(m : ℝ) - m'|))) ≤ I m m' := by
    intro m hm m' hm'
    have hne : m' ≠ m := (Finset.mem_erase.mp hm').1
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    have hmM : (m : ℝ) ≤ M := by exact_mod_cast (Finset.mem_Icc.mp hm).2
    have hm1' : 1 ≤ m' := (Finset.mem_Icc.mp (Finset.mem_erase.mp hm').2).1
    have hmM' : (m' : ℝ) ≤ M := by exact_mod_cast (Finset.mem_Icc.mp (Finset.mem_erase.mp hm').2).2
    have hnb : ∀ n : ℕ, (n : ℝ) ≤ M → (n : ℝ) * b ≤ Ξ := fun n hn =>
      le_trans (mul_le_mul_of_nonneg_right hn (by linarith)) hΞ
    have hnr : 0 ≤ 4 * G * κs / c ^ 2 * (1 / ((m : ℝ) * m' * |(m : ℝ) - m'|)) := by positivity
    have hX : ∀ n : ℕ, 0 ≤ G * Cvs.L2a.FirstModeHigherModePair.X c χ K s n := fun n => by
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · subst h0; unfold Cvs.L2a.FirstModeHigherModePair.X; simp
      · exact mul_nonneg hG0 (Cvs.L2a.FirstModeHigherModePair.X_nonneg hc0 hs0 (by exact_mod_cast hpos) hK hχ)
    have hle : |I m m'| ≤ (if m = 1 then G * Cvs.L2a.FirstModeHigherModePair.X c χ K s m' else 0)
        + (if m' = 1 then G * Cvs.L2a.FirstModeHigherModePair.X c χ K s m else 0)
        + 4 * G * κs / c ^ 2 * (1 / ((m : ℝ) * m' * |(m : ℝ) - m'|)) := by
      by_cases h1 : m = 1
      · subst h1
        have hm2 : (2 : ℝ) ≤ m' := by exact_mod_cast (show 2 ≤ m' by omega)
        rw [if_pos rfl, if_neg (by omega)]
        have key := Cvs.L2a.FirstModeHigherModePair.first_cross_le (n := (m' : ℝ)) hc hχ0 hχ hχs hm2 hs1 hsc hb3 (hnb m' hmM')
          hψ hu hG hG0 hK hcont hedge hedge1
        have e : I 1 m' = ∫ θ in (1 : ℝ)..b, ψ ((m' : ℝ) * θ) * ψ θ := by
          rw [hI]; simp only [Nat.cast_one, one_mul]; congr 1; funext θ; ring
        rw [e]; linarith
      · by_cases h1' : m' = 1
        · subst h1'
          have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast (show 2 ≤ m by omega)
          rw [if_neg h1, if_pos rfl]
          have key := Cvs.L2a.FirstModeHigherModePair.first_cross_le (n := (m : ℝ)) hc hχ0 hχ hχs hm2 hs1 hsc hb3 (hnb m hmM)
            hψ hu hG hG0 hK hcont hedge hedge1
          have e : I m 1 = ∫ θ in (1 : ℝ)..b, ψ ((m : ℝ) * θ) * ψ θ := by
            rw [hI]; simp only [Nat.cast_one, one_mul]
          rw [e]; linarith
        · rw [if_neg h1, if_neg h1', zero_add, zero_add]
          have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast (show 2 ≤ m by omega)
          have hm2' : (2 : ℝ) ≤ m' := by exact_mod_cast (show 2 ≤ m' by omega)
          have hmn : (m : ℝ) ≠ m' := by intro h; apply hne; exact_mod_cast h.symm
          have hsub2 : Icc (2 : ℝ) Ξ ⊆ Ioc 1 Ξ := fun ξ h => ⟨by linarith [h.1], h.2⟩
          have key := Cvs.L2a.PrimeTermPairClassified.nonres_le (u := u) hc0 hχ0 hχ hm2 hm2' hmn hb1 (hnb m hmM) (hnb m' hmM')
            (fun ξ h => hψ ξ (hsub2 h)) (fun ξ h => hu ξ (hsub2 h)) (fun ξ h => hG ξ (hsub2 h))
          refine key.trans (le_of_eq ?_)
          rw [hκs]; field_simp
    have := neg_abs_le (I m m')
    linarith
  -- the cross terms summed
  have hXs := Cvs.L2a.FirstModeHigherModePair.X_sum_le (c := c) (χ := χ) (K := K) (s := s) M hc0 hs1 hK hχ
  have hXnn : ∀ n ∈ Finset.Icc 1 M, 0 ≤ Cvs.L2a.FirstModeHigherModePair.X c χ K s n := fun n hn =>
    Cvs.L2a.FirstModeHigherModePair.X_nonneg hc0 hs0 (by exact_mod_cast (Finset.mem_Icc.mp hn).1) hK hχ
  set Xf := fun n : ℕ => G * Cvs.L2a.FirstModeHigherModePair.X c χ K s n with hXf
  have hXf0 : ∀ n ∈ Finset.Icc 1 M, 0 ≤ Xf n := fun n hn => mul_nonneg hG0 (hXnn n hn)
  have hXsum : ∑ n ∈ Finset.Icc 1 M, Xf n ≤ G * Cvs.L2a.FirstModeHigherModePair.Xbar c χ K s := by
    rw [hXf]; simp only; rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left hXs hG0
  have hT1 : ∑ m ∈ Finset.Icc 1 M, ∑ m' ∈ (Finset.Icc 1 M).erase m, (if m = 1 then Xf m' else 0)
      ≤ G * Cvs.L2a.FirstModeHigherModePair.Xbar c χ K s := by
    have e : ∀ m ∈ Finset.Icc 1 M, ∑ m' ∈ (Finset.Icc 1 M).erase m, (if m = 1 then Xf m' else 0)
        = if m = 1 then ∑ m' ∈ (Finset.Icc 1 M).erase m, Xf m' else 0 := by
      intro m _; split_ifs <;> simp
    rw [Finset.sum_congr rfl e, Finset.sum_ite_eq' _ 1, if_pos h1mem]
    refine le_trans ?_ hXsum
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) (fun n hn _ => hXf0 n hn)
  have hT2 : ∑ m ∈ Finset.Icc 1 M, ∑ m' ∈ (Finset.Icc 1 M).erase m, (if m' = 1 then Xf m else 0)
      ≤ G * Cvs.L2a.FirstModeHigherModePair.Xbar c χ K s := by
    refine le_trans ?_ hXsum
    apply Finset.sum_le_sum; intro m hm
    rw [Finset.sum_ite_eq' _ 1]
    split_ifs
    · exact le_rfl
    · exact hXf0 m hm
  have hT3 : ∑ m ∈ Finset.Icc 1 M, ∑ m' ∈ (Finset.Icc 1 M).erase m,
      4 * G * κs / c ^ 2 * (1 / ((m : ℝ) * m' * |(m : ℝ) - m'|)) ≤ 4 * G * κs / c ^ 2 * (3 * (π ^ 2 / 6 + 6)) := by
    simp only [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (Cvs.L2a.TailCrossModeCounts.nonres_double M) (by positivity)
  have hoff : -(G * Cvs.L2a.FirstModeHigherModePair.Xbar c χ K s + G * Cvs.L2a.FirstModeHigherModePair.Xbar c χ K s
      + 4 * G * κs / c ^ 2 * (3 * (π ^ 2 / 6 + 6)))
      ≤ ∑ m ∈ Finset.Icc 1 M, ∑ m' ∈ (Finset.Icc 1 M).erase m, I m m' := by
    have hsum := Finset.sum_le_sum fun m hm => Finset.sum_le_sum fun m' hm' => hcross m hm m' hm'
    simp only [Finset.sum_neg_distrib, Finset.sum_add_distrib] at hsum
    linarith
  have hdiag' := hdiag
  linarith

end Cvs.L2a.TailModesNormLower
