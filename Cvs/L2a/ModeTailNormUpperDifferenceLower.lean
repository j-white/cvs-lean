import Mathlib
import Cvs.L2a.FirstModeHigherModePair
import Cvs.L2a.NonstationaryPairsOneShift
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
# The norm of the tail of `M` modes, from above; the norm of a difference, from below

The cross terms of `∫F² = Σ_{m,m'} ∫_1^b ψ(mθ)ψ(m'θ)` are at most `2G X̄ + (4G√κ/c²)·3(π²/6+6)` in absolute value,
the first mode's mass is at most `(ξ₀ − 1)KG + GΔ/(2σ) + G/(2q(ξ₀))` (Sonin on `[1, ξ₀]`, the arcsin law beyond) and
the mode `m ≥ 2` at most `G/(αm²)`, `σ = √(c²−χ)`, `α = (√3/2)σ`. For `ε > 0`, `∫(f − κg)² ≥ (1 − ε)∫f² − (1/ε − 1)κ²∫g²`.
-/

namespace Cvs.L2a.ModeTailNormUpperDifferenceLower

open Real Set MeasureTheory Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.TailOfModes
open Cvs.L2a.StationaryPairsWeightedTotal (Aw Qw κw)

/-- **The tail's own cross terms, two-sided**: `|Σ_m Σ_{m' ≠ m} ∫_1^b ψ(mθ)ψ(m'θ)| ≤ 2G X̄ + (4G√κ/c²)·3(π²/6+6)`. -/
theorem offdiag_abs_le {c χ G K Ξ b s : ℝ} {ψ u : ℝ → ℝ} (M : ℕ)
    (hc : 1 ≤ c) (hχ0 : 0 ≤ χ) (hχ : χ < c ^ 2) (hχs : χ ≤ c * √c) (hs1 : 1 ≤ s) (hsc : s ^ 2 ≤ c)
    (hb3 : (3 : ℝ) ≤ b) (hΞ : (M : ℝ) * b ≤ Ξ)
    (hψ : ∀ ξ ∈ Ioc 1 Ξ, HasDerivAt ψ (u ξ / pP ξ) ξ)
    (hu : ∀ ξ ∈ Ioc 1 Ξ, HasDerivAt u (-(qP c χ ξ * ψ ξ)) ξ)
    (hG : ∀ ξ ∈ Ioc 1 Ξ, energy (aP c χ) ψ u ξ ≤ G) (hG0 : 0 ≤ G) (hK : 0 ≤ K)
    (hcont : ContinuousOn ψ (Icc 1 Ξ)) (hedge : ∀ ξ ∈ Icc 1 Ξ, |ψ ξ| ≤ |ψ 1|) (hedge1 : ψ 1 ^ 2 ≤ K * G)
    (hM : 1 ≤ M) :
    |∑ m ∈ Finset.Icc 1 M, ∑ m' ∈ (Finset.Icc 1 M).erase m, ∫ θ in (1 : ℝ)..b, ψ (m * θ) * ψ (m' * θ)|
      ≤ 2 * G * Cvs.L2a.FirstModeHigherModePair.Xbar c χ K s
        + 4 * G * √(2 * c / (√3 * √(c ^ 2 - χ))) / c ^ 2 * (3 * (π ^ 2 / 6 + 6)) := by
  have hc0 : 0 < c := by linarith
  have hs0 : 0 < s := by linarith
  have hb1 : (1 : ℝ) ≤ b := by linarith
  set κs := √(2 * c / (√3 * √(c ^ 2 - χ))) with hκs
  have hκ0 : 0 ≤ κs := sqrt_nonneg _
  set I : ℕ → ℕ → ℝ := fun m m' => ∫ θ in (1 : ℝ)..b, ψ (m * θ) * ψ (m' * θ) with hI
  have h1mem : 1 ∈ Finset.Icc 1 M := Finset.mem_Icc.mpr ⟨le_rfl, hM⟩
  have hcross : ∀ m ∈ Finset.Icc 1 M, ∀ m' ∈ (Finset.Icc 1 M).erase m,
      |I m m'| ≤ (if m = 1 then G * Cvs.L2a.FirstModeHigherModePair.X c χ K s m' else 0)
        + (if m' = 1 then G * Cvs.L2a.FirstModeHigherModePair.X c χ K s m else 0)
        + 4 * G * κs / c ^ 2 * (1 / ((m : ℝ) * m' * |(m : ℝ) - m'|)) := by
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
    exact hle
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
  calc |∑ m ∈ Finset.Icc 1 M, ∑ m' ∈ (Finset.Icc 1 M).erase m, I m m'|
      ≤ ∑ m ∈ Finset.Icc 1 M, ∑ m' ∈ (Finset.Icc 1 M).erase m, |I m m'| :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ m ∈ Finset.Icc 1 M, ∑ m' ∈ (Finset.Icc 1 M).erase m,
          ((if m = 1 then Xf m' else 0) + (if m' = 1 then Xf m else 0)
            + 4 * G * κs / c ^ 2 * (1 / ((m : ℝ) * m' * |(m : ℝ) - m'|))) :=
        Finset.sum_le_sum fun m hm => Finset.sum_le_sum fun m' hm' => hcross m hm m' hm'
    _ ≤ _ := by
        simp only [Finset.sum_add_distrib]
        linarith

/-- **The diagonal**: `Σ_m ∫_1^b ψ(mθ)² ≤ (ξ₀ − 1)KG + GΔ/(2σ) + G/(2q(ξ₀)) + (G/α)(π²/6)`,
`Δ = arccos(1/b) − arccos(1/ξ₀)`, `σ = √(c²−χ)`, `α = (√3/2)σ`. -/
theorem diag_le {c χ G K Ξ b ξ₀ : ℝ} {ψ u : ℝ → ℝ} (M : ℕ) (hc : 0 < c)
    (hχ0 : 0 ≤ χ) (hχ : χ < c ^ 2) (h1ξ : 1 < ξ₀) (hξb : ξ₀ ≤ b) (hΞ : (M : ℝ) * b ≤ Ξ) (hb : b ≤ Ξ)
    (hψ : ∀ ξ ∈ Ioc 1 Ξ, HasDerivAt ψ (u ξ / pP ξ) ξ)
    (hu : ∀ ξ ∈ Ioc 1 Ξ, HasDerivAt u (-(qP c χ ξ * ψ ξ)) ξ)
    (hG : ∀ ξ ∈ Ioc 1 Ξ, energy (aP c χ) ψ u ξ ≤ G) (hG0 : 0 ≤ G)
    (hcont : ContinuousOn ψ (Icc 1 Ξ)) (hedge : ∀ ξ ∈ Icc 1 Ξ, |ψ ξ| ≤ |ψ 1|) (hedge1 : ψ 1 ^ 2 ≤ K * G)
    (hM : 1 ≤ M) :
    ∑ m ∈ Finset.Icc 1 M, ∫ θ in (1 : ℝ)..b, ψ (m * θ) * ψ (m * θ)
      ≤ (ξ₀ - 1) * (K * G) + G * (arccos (1 / b) - arccos (1 / ξ₀)) / (2 * √(c ^ 2 - χ))
        + G / (2 * qP c χ ξ₀) + G / (√3 / 2 * √(c ^ 2 - χ)) * (π ^ 2 / 6) := by
  set α := √3 / 2 * √(c ^ 2 - χ) with hα
  have hd : 0 < c ^ 2 - χ := by linarith
  have hα0 : 0 < α := by positivity
  have hb1 : (1 : ℝ) ≤ b := by linarith
  have h1mem : 1 ∈ Finset.Icc 1 M := Finset.mem_Icc.mpr ⟨le_rfl, hM⟩
  rw [← Finset.add_sum_erase _ _ h1mem]
  -- the first mode: Sonin on `[1, ξ₀]`, the arcsin law on `[ξ₀, b]`
  have hc1 : ContinuousOn (fun θ => ψ θ ^ 2) (Icc 1 b) := (hcont.mono (Icc_subset_Icc le_rfl hb)).pow 2
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    ((hc1.mono (Icc_subset_Icc le_rfl hξb)).intervalIntegrable_of_Icc (μ := volume) h1ξ.le)
    ((hc1.mono (Icc_subset_Icc h1ξ.le le_rfl)).intervalIntegrable_of_Icc (μ := volume) hξb)
  have hA : ∫ θ in (1 : ℝ)..ξ₀, ψ θ ^ 2 ≤ (ξ₀ - 1) * (K * G) := by
    calc ∫ θ in (1 : ℝ)..ξ₀, ψ θ ^ 2 ≤ ∫ θ in (1 : ℝ)..ξ₀, ψ 1 ^ 2 := by
          apply intervalIntegral.integral_mono_on h1ξ.le
            ((hc1.mono (Icc_subset_Icc le_rfl hξb)).intervalIntegrable_of_Icc h1ξ.le) intervalIntegrable_const
          intro θ hθ
          have := hedge θ ⟨hθ.1, by linarith [hθ.2]⟩
          rw [← sq_abs, ← sq_abs (ψ 1)]
          exact pow_le_pow_left₀ (abs_nonneg _) this 2
      _ = (ξ₀ - 1) * ψ 1 ^ 2 := by simp
      _ ≤ (ξ₀ - 1) * (K * G) := mul_le_mul_of_nonneg_left hedge1 (by linarith)
  have hB : ∫ θ in ξ₀..b, ψ θ ^ 2
      ≤ G * (arccos (1 / b) - arccos (1 / ξ₀)) / (2 * √(c ^ 2 - χ)) + G / (2 * qP c χ ξ₀) := by
    have hsub : ∀ t ∈ Icc ξ₀ b, t ∈ Ioc 1 Ξ := fun t ht => ⟨lt_of_lt_of_le h1ξ ht.1, ht.2.trans hb⟩
    exact (Cvs.Prolate.LiouvilleGreen.ProlateArcsinMassLaw.prolate_mass_bounds (c := c) (χ := χ) (ψ := ψ) (u := u) (Gm := 0) h1ξ hξb hc hχ0 hχ
      (fun t ht => hψ t (hsub t ht)) (fun t ht => hu t (hsub t ht))
      (fun t ht => by
        have ha := aP_pos (lt_of_lt_of_le h1ξ ht.1) (by positivity : (0 : ℝ) < c ^ 2) hχ
        have := two_mul_abs_le_energy (ψ := ψ) (u := u) ha
        linarith [abs_nonneg (ψ t * u t)])
      (fun t ht => hG t (hsub t ht)) le_rfl).2
  have hfirst : ∫ θ in (1 : ℝ)..b, ψ ((1 : ℕ) * θ) * ψ ((1 : ℕ) * θ)
      ≤ (ξ₀ - 1) * (K * G) + G * (arccos (1 / b) - arccos (1 / ξ₀)) / (2 * √(c ^ 2 - χ))
        + G / (2 * qP c χ ξ₀) := by
    have e : ∫ θ in (1 : ℝ)..b, ψ ((1 : ℕ) * θ) * ψ ((1 : ℕ) * θ) = ∫ θ in (1 : ℝ)..b, ψ θ ^ 2 := by
      congr 1; funext θ; simp only [Nat.cast_one, one_mul]; ring
    rw [e, ← hsplit]; linarith
  -- the higher modes
  have hmode : ∀ m ∈ (Finset.Icc 1 M).erase 1, ∫ θ in (1 : ℝ)..b, ψ (m * θ) * ψ (m * θ) ≤ G / α * (1 / (m : ℝ) ^ 2) :=
    fun m hm => by
    have hm2 : (2 : ℝ) ≤ m := by
      have := Finset.mem_erase.mp hm
      exact_mod_cast (show 2 ≤ m by have := (Finset.mem_Icc.mp this.2).1; omega)
    have hmM : (m : ℝ) ≤ M := by exact_mod_cast (Finset.mem_Icc.mp (Finset.mem_erase.mp hm).2).2
    have hmb : (m : ℝ) * b ≤ Ξ := le_trans (mul_le_mul_of_nonneg_right hmM (by linarith)) hΞ
    have h := Cvs.L2a.PrimeTermPairClassified.resonant_le (u := u) hχ0 hχ hm2 (by linarith : (1 : ℝ) ≤ b)
      (fun ξ hξ => hG ξ ⟨by linarith [hξ.1], hξ.2.trans hmb⟩) hG0
      (hcont.mono fun ξ hξ => ⟨by linarith [hξ.1], hξ.2.trans hmb⟩)
    refine (le_abs_self _).trans (h.trans (le_of_eq ?_))
    have : (0 : ℝ) < m := by linarith
    field_simp
    rw [hα]; ring
  have hrest : ∑ m ∈ (Finset.Icc 1 M).erase 1, ∫ θ in (1 : ℝ)..b, ψ (m * θ) * ψ (m * θ) ≤ G / α * (π ^ 2 / 6) := by
    calc _ ≤ ∑ m ∈ (Finset.Icc 1 M).erase 1, G / α * (1 / (m : ℝ) ^ 2) := Finset.sum_le_sum hmode
      _ ≤ ∑ m ∈ Finset.Icc 1 M, G / α * (1 / (m : ℝ) ^ 2) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) (fun _ _ _ => by positivity)
      _ = G / α * ∑ m ∈ Finset.Icc 1 M, 1 / (m : ℝ) ^ 2 := by rw [Finset.mul_sum]
      _ ≤ G / α * (π ^ 2 / 6) :=
          mul_le_mul_of_nonneg_left (Cvs.L2a.NonstationaryPairsOneShift.sum_inv_sq_le M) (by positivity)
  linarith

/-- **The norm of the tail of `M` modes, from above.** -/
theorem norm_le {c χ G K Ξ b s ξ₀ : ℝ} {ψ u : ℝ → ℝ} (M : ℕ)
    (hc : 1 ≤ c) (hχ0 : 0 ≤ χ) (hχ : χ < c ^ 2) (hχs : χ ≤ c * √c) (hs1 : 1 ≤ s) (hsc : s ^ 2 ≤ c)
    (hb3 : (3 : ℝ) ≤ b) (hΞ : (M : ℝ) * b ≤ Ξ) (h1ξ : 1 < ξ₀) (hξb : ξ₀ ≤ b)
    (hψ : ∀ ξ ∈ Ioc 1 Ξ, HasDerivAt ψ (u ξ / pP ξ) ξ)
    (hu : ∀ ξ ∈ Ioc 1 Ξ, HasDerivAt u (-(qP c χ ξ * ψ ξ)) ξ)
    (hG : ∀ ξ ∈ Ioc 1 Ξ, energy (aP c χ) ψ u ξ ≤ G) (hG0 : 0 ≤ G) (hK : 0 ≤ K)
    (hcont : ContinuousOn ψ (Icc 1 Ξ)) (hedge : ∀ ξ ∈ Icc 1 Ξ, |ψ ξ| ≤ |ψ 1|) (hedge1 : ψ 1 ^ 2 ≤ K * G)
    (hM : 1 ≤ M) :
    ∫ θ in Ioi 1, tailF ψ M b θ ^ 2
      ≤ (ξ₀ - 1) * (K * G) + G * (arccos (1 / b) - arccos (1 / ξ₀)) / (2 * √(c ^ 2 - χ))
        + G / (2 * qP c χ ξ₀) + G / (√3 / 2 * √(c ^ 2 - χ)) * (π ^ 2 / 6) + 2 * G * Cvs.L2a.FirstModeHigherModePair.Xbar c χ K s
        + 4 * G * √(2 * c / (√3 * √(c ^ 2 - χ))) / c ^ 2 * (3 * (π ^ 2 / 6 + 6)) := by
  have hb1 : (1 : ℝ) ≤ b := by linarith
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hbΞ : b ≤ Ξ := le_trans (by nlinarith) hΞ
  set I : ℕ → ℕ → ℝ := fun m m' => ∫ θ in (1 : ℝ)..b, ψ (m * θ) * ψ (m' * θ) with hI
  have hN : ∫ θ in Ioi 1, tailF ψ M b θ ^ 2 = ∑ m ∈ Finset.Icc 1 M, ∑ m' ∈ Finset.Icc 1 M, I m m' := by
    have e : (fun θ => tailF ψ M b θ ^ 2) = fun θ => tailF ψ M b θ * tailF ψ M b (1 * θ) := by
      funext θ; rw [one_mul]; ring
    rw [e, integral_tailF_pair ψ ψ M le_rfl hb1 (hcont.mono (Icc_subset_Icc le_rfl hΞ))
      (hcont.mono (Icc_subset_Icc le_rfl hΞ))]
    apply Finset.sum_congr rfl; intro m _; apply Finset.sum_congr rfl; intro m' _
    rw [hI]; simp only [div_one, one_mul]
  rw [hN]
  have hsplit : ∀ m ∈ Finset.Icc 1 M, ∑ m' ∈ Finset.Icc 1 M, I m m' = I m m + ∑ m' ∈ (Finset.Icc 1 M).erase m, I m m' :=
    fun m hm => (Finset.add_sum_erase _ _ hm).symm
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  have hd := diag_le (u := u) (K := K) M (by linarith) hχ0 hχ h1ξ hξb hΞ hbΞ hψ hu hG hG0 hcont hedge hedge1 hM
  have ho := offdiag_abs_le (u := u) M hc hχ0 hχ hχs hs1 hsc hb3 hΞ hψ hu hG hG0 hK hcont hedge hedge1 hM
  have := le_abs_self (∑ m ∈ Finset.Icc 1 M, ∑ m' ∈ (Finset.Icc 1 M).erase m, I m m')
  have hd' : ∑ m ∈ Finset.Icc 1 M, I m m ≤ (ξ₀ - 1) * (K * G)
      + G * (arccos (1 / b) - arccos (1 / ξ₀)) / (2 * √(c ^ 2 - χ))
      + G / (2 * qP c χ ξ₀) + G / (√3 / 2 * √(c ^ 2 - χ)) * (π ^ 2 / 6) := hd
  linarith

/-- **The norm of a difference, from below**: `∫(f − κg)² ≥ (1 − ε)∫f² − (1/ε − 1)κ²∫g²`, `ε > 0`. -/
theorem integral_sub_sq_ge {f g : ℝ → ℝ} {s : Set ℝ} {κ ε : ℝ} (hε : 0 < ε)
    (hf : IntegrableOn (fun θ => f θ ^ 2) s) (hg : IntegrableOn (fun θ => g θ ^ 2) s)
    (hfg : IntegrableOn (fun θ => (f θ - κ * g θ) ^ 2) s) :
    (1 - ε) * (∫ θ in s, f θ ^ 2) - (1 / ε - 1) * κ ^ 2 * ∫ θ in s, g θ ^ 2 ≤ ∫ θ in s, (f θ - κ * g θ) ^ 2 := by
  have hpt : ∀ θ, (1 - ε) * f θ ^ 2 - (1 / ε - 1) * κ ^ 2 * g θ ^ 2 ≤ (f θ - κ * g θ) ^ 2 := fun θ => by
    have key : ε * ((f θ - κ * g θ) ^ 2 - ((1 - ε) * f θ ^ 2 - (1 / ε - 1) * κ ^ 2 * g θ ^ 2))
        = (ε * f θ - κ * g θ) ^ 2 := by field_simp; ring
    have : 0 ≤ ε * ((f θ - κ * g θ) ^ 2 - ((1 - ε) * f θ ^ 2 - (1 / ε - 1) * κ ^ 2 * g θ ^ 2)) := by
      rw [key]; positivity
    have := (mul_nonneg_iff_of_pos_left hε).mp this
    linarith
  have hi : IntegrableOn (fun θ => (1 - ε) * f θ ^ 2 - (1 / ε - 1) * κ ^ 2 * g θ ^ 2) s := by
    have := (hf.const_mul (1 - ε)).sub (hg.const_mul ((1 / ε - 1) * κ ^ 2))
    exact this
  calc (1 - ε) * (∫ θ in s, f θ ^ 2) - (1 / ε - 1) * κ ^ 2 * ∫ θ in s, g θ ^ 2
      = ∫ θ in s, ((1 - ε) * f θ ^ 2 - (1 / ε - 1) * κ ^ 2 * g θ ^ 2) := by
        rw [integral_sub (hf.const_mul _) (hg.const_mul _), integral_const_mul, integral_const_mul]
    _ ≤ ∫ θ in s, (f θ - κ * g θ) ^ 2 :=
        setIntegral_mono hi hfg hpt

end Cvs.L2a.ModeTailNormUpperDifferenceLower
