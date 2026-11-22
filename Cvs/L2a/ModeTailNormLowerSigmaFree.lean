import Mathlib
import Cvs.L2a.NonstationaryPairsOneShift
import Cvs.L2a.SigmaFreeEdgePairMonomials
import Cvs.L2a.SigmaFreeStripPairMonomials
import Cvs.L2a.SigmaFreeWeightedPairTotal
import Cvs.L2a.TailCrossModeCounts
import Cvs.L2a.TailOfModes
import Cvs.Prolate.Envelope.EnvelopeBeyondTwoSigmaFree
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
# The norm of the tail of `M` modes from below, `σ`-free, for every `χ < c²`

With `L = (c² − χ)/c²`, `A_c = √(4K/(3c))`, `s' = (3/5)sL`: the first mode against the mode `n` is at most `G X_n`,
`X_n = (23/3)(A_c/s)[s' < 6n]/n² + (A_c/c + 2√(10/(3L))/(cs))[6n ≤ s']/n + (κ₁s/c² + (64√2/27)Ls√c/c²)/n²
+ (32√3/9)√(23/3)√s/(c² n√n)` (Cvs.L2a.SigmaFreeEdgePairMonomials, Cvs.L2a.SigmaFreeStripPairMonomials at `k = 1`); `Σ X_n ≤ X̄`; and `N ≥ G_mΔ/(2c) − G/(2q(ξ₀)) − 2GX̄ − (8G(2/√3)/c²)·3(π²/6+6)`.
-/

namespace Cvs.L2a.ModeTailNormLowerSigmaFree

open Real Set MeasureTheory Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.TailOfModes
open Cvs.L2a.SigmaFreeWeightedPairTotal (κ₁)

/-- `X_n`. -/
noncomputable def X (c χ K s n : ℝ) : ℝ :=
  23 / 3 * √(4 * K / (3 * c)) / s * (if 3 / 5 * (s * ((c ^ 2 - χ) / c ^ 2)) < 6 * n then 1 / n ^ 2 else 0)
    + (√(4 * K / (3 * c)) / c + 2 * √(10 / (3 * ((c ^ 2 - χ) / c ^ 2))) / (c * s))
      * (if 6 * n ≤ 3 / 5 * (s * ((c ^ 2 - χ) / c ^ 2)) then 1 / n else 0)
    + (κ₁ * s / c ^ 2 + 64 * √2 / 27 * ((c ^ 2 - χ) / c ^ 2) * s * √c / c ^ 2) * (1 / n ^ 2)
    + 32 * √3 / 9 * √(23 / 3) * √s / c ^ 2 * (1 / (n * √n))

theorem X_nonneg {c χ K s n : ℝ} (hc : 0 < c) (hχ : χ < c ^ 2) (hs : 0 < s) (hn : 0 < n) :
    0 ≤ X c χ K s n := by
  have hL : 0 ≤ (c ^ 2 - χ) / c ^ 2 := div_nonneg (by linarith) (by positivity)
  have hk : 0 ≤ κ₁ := by unfold κ₁; positivity
  have h1 : 0 ≤ (if 3 / 5 * (s * ((c ^ 2 - χ) / c ^ 2)) < 6 * n then 1 / n ^ 2 else 0) := by
    split_ifs <;> positivity
  have h2 : 0 ≤ (if 6 * n ≤ 3 / 5 * (s * ((c ^ 2 - χ) / c ^ 2)) then 1 / n else 0) := by split_ifs <;> positivity
  unfold X
  have t1 := mul_nonneg (by positivity : (0 : ℝ) ≤ 23 / 3 * √(4 * K / (3 * c)) / s) h1
  have t2 := mul_nonneg (by positivity : (0 : ℝ) ≤ √(4 * K / (3 * c)) / c
    + 2 * √(10 / (3 * ((c ^ 2 - χ) / c ^ 2))) / (c * s)) h2
  have t3 : 0 ≤ (κ₁ * s / c ^ 2 + 64 * √2 / 27 * ((c ^ 2 - χ) / c ^ 2) * s * √c / c ^ 2) * (1 / n ^ 2) :=
    mul_nonneg (add_nonneg (by positivity) (div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hL)
      hs.le) (sqrt_nonneg _)) (by positivity))) (by positivity)
  have t4 : 0 ≤ 32 * √3 / 9 * √(23 / 3) * √s / c ^ 2 * (1 / (n * √n)) := by positivity
  linarith

set_option maxHeartbeats 4000000 in
/-- **The first mode against the mode `n`, `σ`-free.** -/
theorem first_cross_le {c χ G K Ξ b s n : ℝ} {ψ u : ℝ → ℝ}
    (hc : 1 ≤ c) (hχ0 : 0 ≤ χ) (hχ : χ < c ^ 2) (hn : 2 ≤ n) (hs1 : 1 ≤ s) (hsc : s ^ 2 * ((c ^ 2 - χ) / c ^ 2) ≤ c)
    (hb : 3 ≤ b) (hhi : n * b ≤ Ξ)
    (hψ : ∀ ξ ∈ Ioc 1 Ξ, HasDerivAt ψ (u ξ / pP ξ) ξ)
    (hu : ∀ ξ ∈ Ioc 1 Ξ, HasDerivAt u (-(qP c χ ξ * ψ ξ)) ξ)
    (hG : ∀ ξ ∈ Ioc 1 Ξ, energy (aP c χ) ψ u ξ ≤ G) (hG0 : 0 ≤ G)
    (hcont : ContinuousOn ψ (Icc 1 Ξ)) (hedge : ∀ ξ ∈ Icc 1 Ξ, |ψ ξ| ≤ |ψ 1|) (hedge1 : ψ 1 ^ 2 ≤ K * G) :
    |∫ θ in (1 : ℝ)..b, ψ (n * θ) * ψ θ| ≤ G * X c χ K s n := by
  have hc0 : 0 < c := by linarith
  have hn0 : 0 < n := by linarith
  have hs0 : 0 < s := by linarith
  have hsn : 0 < √n := sqrt_pos.mpr hn0
  set L := (c ^ 2 - χ) / c ^ 2 with hLdef
  have hL0 : 0 ≤ L := div_nonneg (by linarith) (by positivity)
  have hL1 : L ≤ 1 := by rw [hLdef, div_le_one (by positivity)]; linarith
  set Ac := √(4 * K / (3 * c)) with hAc
  have hAc0 : 0 ≤ Ac := sqrt_nonneg _
  have hk : 0 ≤ κ₁ := by unfold κ₁; positivity
  have e : ∫ θ in (1 : ℝ)..b, ψ (n * θ) * ψ θ = ∫ t in (1 : ℝ)..b, ψ (n * t) * ψ (1 / 1 * t) := by
    congr 1; funext t; simp
  rw [e]
  have hkm : (2 : ℝ) ≤ 1 * n := by linarith
  unfold X
  rw [← hLdef, ← hAc]
  by_cases h : 10 * (1 * n) ≤ s * L
  · have key := Cvs.L2a.SigmaFreeStripPairMonomials.strip_mono (k := 1) (m := n) (s := s) (K := K) hc hχ0 hχ le_rfl hkm
      (by linarith) hs1 hsc h (by linarith) hhi hψ hu hG hG0 hcont hedge hedge1
    rw [← hLdef, ← hAc] at key
    refine key.trans (mul_le_mul_of_nonneg_left ?_ hG0)
    rw [if_neg (by linarith), if_pos (by linarith)]
    have hsL : √L ≤ 1 := (sqrt_le_sqrt hL1).trans_eq sqrt_one
    have hκ : 40 / (9 * √3) + 16 / 9 * (8 / √3 + 2 * √3 * √L) ≤ κ₁ := by
      unfold κ₁; have : 2 * √3 * √L ≤ 2 * √3 := by nlinarith [sqrt_nonneg 3]
      linarith
    have hn3 : 1 / (1 ^ 2 * n ^ 3) ≤ 1 / n ^ 2 := by
      rw [one_pow, one_mul]; apply one_div_le_one_div_of_le (by positivity); nlinarith
    have e1 : Ac / (c * n) + 2 * √(10 / (3 * L)) / (c * s * n) = (Ac / c + 2 * √(10 / (3 * L)) / (c * s)) * (1 / n) := by
      field_simp
    have t1 : (40 / (9 * √3) + 16 / 9 * (8 / √3 + 2 * √3 * √L)) * s / (c ^ 2 * 1 * n ^ 2)
        ≤ κ₁ * s / c ^ 2 * (1 / n ^ 2) := by
      calc (40 / (9 * √3) + 16 / 9 * (8 / √3 + 2 * √3 * √L)) * s / (c ^ 2 * 1 * n ^ 2)
          ≤ κ₁ * s / (c ^ 2 * 1 * n ^ 2) := by gcongr
        _ = κ₁ * s / c ^ 2 * (1 / n ^ 2) := by field_simp
    have t2 : 64 * √2 / 27 * L * s * √c / (c ^ 2 * 1 ^ 2 * n ^ 3)
        ≤ 64 * √2 / 27 * L * s * √c / c ^ 2 * (1 / n ^ 2) := by
      calc 64 * √2 / 27 * L * s * √c / (c ^ 2 * 1 ^ 2 * n ^ 3)
          = 64 * √2 / 27 * L * s * √c / c ^ 2 * (1 / (1 ^ 2 * n ^ 3)) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left hn3 (by positivity)
    have p0 : 0 ≤ 23 / 3 * Ac / s * 0 := by simp
    have p4 : 0 ≤ 32 * √3 / 9 * √(23 / 3) * √s / c ^ 2 * (1 / (n * √n)) := by positivity
    have e5 : (κ₁ * s / c ^ 2 + 64 * √2 / 27 * L * s * √c / c ^ 2) * (1 / n ^ 2)
        = κ₁ * s / c ^ 2 * (1 / n ^ 2) + 64 * √2 / 27 * L * s * √c / c ^ 2 * (1 / n ^ 2) := by ring
    rw [e1]
    linarith
  · have hlt : s * L < 10 * (1 * n) := lt_of_not_ge h
    have key := Cvs.L2a.SigmaFreeEdgePairMonomials.edge_mono (k := 1) (m := n) (s := s) (K := K) hc hχ0 hχ le_rfl hkm
      (by linarith) hs1 hlt (by linarith) hhi hψ hu hG hG0 hcont hedge hedge1
    rw [← hAc] at key
    refine key.trans (mul_le_mul_of_nonneg_left ?_ hG0)
    rw [if_pos (by linarith), if_neg (by linarith), sqrt_one]
    have t1 : 128 / (9 * √3) * s / (c ^ 2 * 1 * n ^ 2) ≤ κ₁ * s / c ^ 2 * (1 / n ^ 2) := by
      have : 128 / (9 * √3) ≤ κ₁ := by
        unfold κ₁
        have : 128 / (9 * √3) = 16 / 9 * (8 / √3) := by ring
        have : 0 ≤ 40 / (9 * √3) := by positivity
        have : 0 ≤ 16 / 9 * (2 * √3) := by positivity
        nlinarith
      calc 128 / (9 * √3) * s / (c ^ 2 * 1 * n ^ 2) ≤ κ₁ * s / (c ^ 2 * 1 * n ^ 2) := by gcongr
        _ = κ₁ * s / c ^ 2 * (1 / n ^ 2) := by field_simp
    have e1 : 23 / 3 * Ac / (s * 1 * n ^ 2) = 23 / 3 * Ac / s * (1 / n ^ 2) := by field_simp
    have e3 : 32 * √3 / 9 * √(23 / 3) * √s / (c ^ 2 * 1 * (n * √n))
        = 32 * √3 / 9 * √(23 / 3) * √s / c ^ 2 * (1 / (n * √n)) := by field_simp
    have p2 : 0 ≤ (Ac / c + 2 * √(10 / (3 * L)) / (c * s)) * 0 := by simp
    have p5 : 0 ≤ 64 * √2 / 27 * L * s * √c / c ^ 2 * (1 / n ^ 2) := by positivity
    have e5 : (κ₁ * s / c ^ 2 + 64 * √2 / 27 * L * s * √c / c ^ 2) * (1 / n ^ 2)
        = κ₁ * s / c ^ 2 * (1 / n ^ 2) + 64 * √2 / 27 * L * s * √c / c ^ 2 * (1 / n ^ 2) := by ring
    rw [e1, e3]
    linarith

/-- `X̄`. -/
noncomputable def Xbar (c χ K s : ℝ) : ℝ :=
  23 / 3 * √(4 * K / (3 * c)) / s * (3 * √(6 / (3 / 5 * (s * ((c ^ 2 - χ) / c ^ 2)))))
    + (√(4 * K / (3 * c)) / c + 2 * √(10 / (3 * ((c ^ 2 - χ) / c ^ 2))) / (c * s))
      * (1 + log (max (3 / 5 * (s * ((c ^ 2 - χ) / c ^ 2))) 1))
    + (κ₁ * s / c ^ 2 + 64 * √2 / 27 * ((c ^ 2 - χ) / c ^ 2) * s * √c / c ^ 2) * (π ^ 2 / 6)
    + 32 * √3 / 9 * √(23 / 3) * √s / c ^ 2 * 3

/-- **The modes summed**: `Σ_{n ≤ M} X_n ≤ X̄`, uniformly in `M`. -/
theorem X_sum_le {c χ K s : ℝ} (M : ℕ) (hc : 0 < c) (hχ : χ < c ^ 2) (hs : 1 ≤ s) :
    ∑ n ∈ Finset.Icc 1 M, X c χ K s n ≤ Xbar c χ K s := by
  have hs0 : 0 < s := by linarith
  set L := (c ^ 2 - χ) / c ^ 2 with hLdef
  have hd : 0 < c ^ 2 - χ := by linarith
  have hL0 : 0 < L := by rw [hLdef]; positivity
  have hk : 0 ≤ κ₁ := by unfold κ₁; positivity
  unfold X Xbar
  rw [← hLdef]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  have h1 := Cvs.L2a.TailCrossModeCounts.edge_count M (by positivity : (0 : ℝ) < 3 / 5 * (s * L))
  have h2 := Cvs.L2a.TailCrossModeCounts.strip_harm M (le_max_right (3 / 5 * (s * L)) 1)
  have h2' : ∑ n ∈ Finset.Icc 1 M, (if 6 * (n : ℝ) ≤ 3 / 5 * (s * L) then 1 / (n : ℝ) else 0)
      ≤ ∑ n ∈ Finset.Icc 1 M, (if 6 * (n : ℝ) ≤ max (3 / 5 * (s * L)) 1 then 1 / (n : ℝ) else 0) := by
    apply Finset.sum_le_sum; intro n hn
    have hn0 : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
    split_ifs with ha hb
    · exact le_rfl
    · exact absurd (ha.trans (le_max_left _ _)) hb
    · exact hn0
    · exact le_rfl
  have h3 := Cvs.L2a.NonstationaryPairsOneShift.sum_inv_sq_le M
  have h4 := Cvs.L2a.NonstationaryPairsOneShift.sum_inv_mul_sqrt_le M
  have g1 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 23 / 3 * √(4 * K / (3 * c)) / s)
  have g2 := mul_le_mul_of_nonneg_left (h2'.trans h2)
    (by positivity : (0 : ℝ) ≤ √(4 * K / (3 * c)) / c + 2 * √(10 / (3 * L)) / (c * s))
  have g3 := mul_le_mul_of_nonneg_left h3
    (by positivity : (0 : ℝ) ≤ κ₁ * s / c ^ 2 + 64 * √2 / 27 * L * s * √c / c ^ 2)
  have g4 := mul_le_mul_of_nonneg_left h4 (by positivity : (0 : ℝ) ≤ 32 * √3 / 9 * √(23 / 3) * √s / c ^ 2)
  linarith

set_option maxHeartbeats 4000000 in
/-- **The norm of the tail of `M` modes, from below, `σ`-free.** -/
theorem norm_ge {c χ G K Gm Ξ ξ₀ s : ℝ} {ψ u : ℝ → ℝ} (M J : ℕ)
    (hc : 1 ≤ c) (hχ0 : 0 ≤ χ) (hχ : χ < c ^ 2) (hs1 : 1 ≤ s) (hsc : s ^ 2 * ((c ^ 2 - χ) / c ^ 2) ≤ c)
    (hb3 : (3 : ℝ) ≤ 2 ^ (J + 1)) (hΞ : (M : ℝ) * 2 ^ (J + 1) ≤ Ξ)
    (hψ : ∀ ξ ∈ Ioc 1 Ξ, HasDerivAt ψ (u ξ / pP ξ) ξ)
    (hu : ∀ ξ ∈ Ioc 1 Ξ, HasDerivAt u (-(qP c χ ξ * ψ ξ)) ξ)
    (hG : ∀ ξ ∈ Ioc 1 Ξ, energy (aP c χ) ψ u ξ ≤ G) (hG0 : 0 ≤ G)
    (hcont : ContinuousOn ψ (Icc 1 Ξ)) (hedge : ∀ ξ ∈ Icc 1 Ξ, |ψ ξ| ≤ |ψ 1|) (hedge1 : ψ 1 ^ 2 ≤ K * G)
    (h1ξ : 1 < ξ₀) (hξb : ξ₀ ≤ 2 ^ (J + 1)) (hGm : ∀ t ∈ Icc ξ₀ (2 ^ (J + 1)), Gm ≤ energy (aP c χ) ψ u t)
    (hGm0 : 0 ≤ Gm) (hM : 1 ≤ M) :
    Gm * (arccos (1 / 2 ^ (J + 1)) - arccos (1 / ξ₀)) / (2 * c) - G / (2 * qP c χ ξ₀)
        - 2 * G * Xbar c χ K s
        - 8 * G * (2 / √3) / c ^ 2 * (3 * (π ^ 2 / 6 + 6))
      ≤ ∫ θ in Ioi 1, tailF ψ M (2 ^ (J + 1)) θ ^ 2 := by
  set b : ℝ := 2 ^ (J + 1) with hbdef
  have hc0 : 0 < c := by linarith
  have hs0 : 0 < s := by linarith
  have hb1 : (1 : ℝ) ≤ b := by linarith
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hbΞ : b ≤ Ξ := le_trans (by nlinarith) hΞ
  set κs := 2 / √3 with hκs
  have hκ0 : 0 ≤ κs := by positivity
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
      -((if m = 1 then G * X c χ K s m' else 0)
        + (if m' = 1 then G * X c χ K s m else 0)
        + 8 * G * κs / c ^ 2 * (1 / ((m : ℝ) * m' * |(m : ℝ) - m'|))) ≤ I m m' := by
    intro m hm m' hm'
    have hne : m' ≠ m := (Finset.mem_erase.mp hm').1
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    have hmM : (m : ℝ) ≤ M := by exact_mod_cast (Finset.mem_Icc.mp hm).2
    have hm1' : 1 ≤ m' := (Finset.mem_Icc.mp (Finset.mem_erase.mp hm').2).1
    have hmM' : (m' : ℝ) ≤ M := by exact_mod_cast (Finset.mem_Icc.mp (Finset.mem_erase.mp hm').2).2
    have hnb : ∀ n : ℕ, (n : ℝ) ≤ M → (n : ℝ) * b ≤ Ξ := fun n hn =>
      le_trans (mul_le_mul_of_nonneg_right hn (by linarith)) hΞ
    have hnr : 0 ≤ 8 * G * κs / c ^ 2 * (1 / ((m : ℝ) * m' * |(m : ℝ) - m'|)) := by positivity
    have hX : ∀ n : ℕ, 0 ≤ G * X c χ K s n := fun n => by
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · subst h0; unfold X; simp
      · exact mul_nonneg hG0 (X_nonneg hc0 hχ hs0 (by exact_mod_cast hpos))
    have hle : |I m m'| ≤ (if m = 1 then G * X c χ K s m' else 0)
        + (if m' = 1 then G * X c χ K s m else 0)
        + 8 * G * κs / c ^ 2 * (1 / ((m : ℝ) * m' * |(m : ℝ) - m'|)) := by
      by_cases h1 : m = 1
      · subst h1
        have hm2 : (2 : ℝ) ≤ m' := by exact_mod_cast (show 2 ≤ m' by omega)
        rw [if_pos rfl, if_neg (by omega)]
        have key := first_cross_le (n := (m' : ℝ)) hc hχ0 hχ hm2 hs1 hsc hb3 (hnb m' hmM')
          hψ hu hG hG0 hcont hedge hedge1
        have e : I 1 m' = ∫ θ in (1 : ℝ)..b, ψ ((m' : ℝ) * θ) * ψ θ := by
          rw [hI]; simp only [Nat.cast_one, one_mul]; congr 1; funext θ; ring
        rw [e]; linarith
      · by_cases h1' : m' = 1
        · subst h1'
          have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast (show 2 ≤ m by omega)
          rw [if_neg h1, if_pos rfl]
          have key := first_cross_le (n := (m : ℝ)) hc hχ0 hχ hm2 hs1 hsc hb3 (hnb m hmM)
            hψ hu hG hG0 hcont hedge hedge1
          have e : I m 1 = ∫ θ in (1 : ℝ)..b, ψ ((m : ℝ) * θ) * ψ θ := by
            rw [hI]; simp only [Nat.cast_one, one_mul]
          rw [e]; linarith
        · rw [if_neg h1, if_neg h1', zero_add, zero_add]
          have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast (show 2 ≤ m by omega)
          have hm2' : (2 : ℝ) ≤ m' := by exact_mod_cast (show 2 ≤ m' by omega)
          have hmn : (m : ℝ) ≠ m' := by intro h; apply hne; exact_mod_cast h.symm
          have hsub2 : Icc (2 : ℝ) Ξ ⊆ Ioc 1 Ξ := fun ξ h => ⟨by linarith [h.1], h.2⟩
          have hsep : (1 : ℝ) ≤ |(m : ℝ) - m'| := by
            rcases Nat.lt_or_gt_of_ne (Ne.symm hne) with h | h
            · have h' : m + 1 ≤ m' := h
              have : (m : ℝ) + 1 ≤ m' := by exact_mod_cast h'
              rw [abs_of_neg (by linarith)]; linarith
            · have h' : m' + 1 ≤ m := h
              have : (m' : ℝ) + 1 ≤ m := by exact_mod_cast h'
              rw [abs_of_pos (by linarith)]; linarith
          have key := Cvs.Prolate.Envelope.EnvelopeBeyondTwoSigmaFree.nonres_c_le (ua := u) (ub := u) hc0 hχ0 hχ hχ0 hχ hm2 hm2' hsep hb1
            (hnb m hmM) (hnb m' hmM')
            (fun ξ h => hψ ξ (hsub2 h)) (fun ξ h => hu ξ (hsub2 h)) (fun ξ h => hψ ξ (hsub2 h))
            (fun ξ h => hu ξ (hsub2 h)) (fun ξ h => hG ξ (hsub2 h)) (fun ξ h => hG ξ (hsub2 h))
          refine key.trans (le_of_eq ?_)
          rw [hκs]; field_simp
    have := neg_abs_le (I m m')
    linarith
  -- the cross terms summed
  have hXs := X_sum_le (c := c) (χ := χ) (K := K) (s := s) M hc0 hχ hs1
  have hXnn : ∀ n ∈ Finset.Icc 1 M, 0 ≤ X c χ K s n := fun n hn =>
    X_nonneg hc0 hχ hs0 (by exact_mod_cast (Finset.mem_Icc.mp hn).1)
  set Xf := fun n : ℕ => G * X c χ K s n with hXf
  have hXf0 : ∀ n ∈ Finset.Icc 1 M, 0 ≤ Xf n := fun n hn => mul_nonneg hG0 (hXnn n hn)
  have hXsum : ∑ n ∈ Finset.Icc 1 M, Xf n ≤ G * Xbar c χ K s := by
    rw [hXf]; simp only; rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left hXs hG0
  have hT1 : ∑ m ∈ Finset.Icc 1 M, ∑ m' ∈ (Finset.Icc 1 M).erase m, (if m = 1 then Xf m' else 0)
      ≤ G * Xbar c χ K s := by
    have e : ∀ m ∈ Finset.Icc 1 M, ∑ m' ∈ (Finset.Icc 1 M).erase m, (if m = 1 then Xf m' else 0)
        = if m = 1 then ∑ m' ∈ (Finset.Icc 1 M).erase m, Xf m' else 0 := by
      intro m _; split_ifs <;> simp
    rw [Finset.sum_congr rfl e, Finset.sum_ite_eq' _ 1, if_pos h1mem]
    refine le_trans ?_ hXsum
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) (fun n hn _ => hXf0 n hn)
  have hT2 : ∑ m ∈ Finset.Icc 1 M, ∑ m' ∈ (Finset.Icc 1 M).erase m, (if m' = 1 then Xf m else 0)
      ≤ G * Xbar c χ K s := by
    refine le_trans ?_ hXsum
    apply Finset.sum_le_sum; intro m hm
    rw [Finset.sum_ite_eq' _ 1]
    split_ifs
    · exact le_rfl
    · exact hXf0 m hm
  have hT3 : ∑ m ∈ Finset.Icc 1 M, ∑ m' ∈ (Finset.Icc 1 M).erase m,
      8 * G * κs / c ^ 2 * (1 / ((m : ℝ) * m' * |(m : ℝ) - m'|)) ≤ 8 * G * κs / c ^ 2 * (3 * (π ^ 2 / 6 + 6)) := by
    simp only [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (Cvs.L2a.TailCrossModeCounts.nonres_double M) (by positivity)
  have hoff : -(G * Xbar c χ K s + G * Xbar c χ K s
      + 8 * G * κs / c ^ 2 * (3 * (π ^ 2 / 6 + 6)))
      ≤ ∑ m ∈ Finset.Icc 1 M, ∑ m' ∈ (Finset.Icc 1 M).erase m, I m m' := by
    have hsum := Finset.sum_le_sum fun m hm => Finset.sum_le_sum fun m' hm' => hcross m hm m' hm'
    simp only [Finset.sum_neg_distrib, Finset.sum_add_distrib] at hsum
    linarith
  have hdiag' := hdiag
  linarith

end Cvs.L2a.ModeTailNormLowerSigmaFree
