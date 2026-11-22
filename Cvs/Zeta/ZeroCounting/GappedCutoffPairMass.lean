import Mathlib
import Cvs.StepA.Edge.DeepSetZeroSums
import Cvs.StepA.Edge.FiniteTopGap
import Cvs.StepA.Edge.GapRectangleBlaschke
import Cvs.Zeta.GaussKernel.DivisorWeightCoordinates
import Cvs.Zeta.GaussKernel.ZeroChain
import Cvs.Zeta.GaussKernel.ZetaZeroStatement
import Cvs.Zeta.ZeroCounting.WeightedLocalCountsCutoff

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Lemma P: a gapped cutoff with small pair mass

Among the candidate cutoffs `H_j = H₀ + 3j + 1`, `j < J = ⌊(H₀ − 1)/3⌋`, each of the `N` deep zeros below `4H₀`
blocks at most one, and summing the near pair mass over the unblocked ones counts each straddling pair at most
`Δ/3 + 1 ≤ Δ` times, so the total is at most `N·264 log(8H₀ + 5)(1 + log(4H₀ + 1))`. For `2N ≤ J` some gapped
`H ∈ [H₀, 2H₀]` has `phiNear ≤ 2N·264 log(8H₀ + 5)(1 + log(4H₀ + 1))/J` (caseinf-W Lemma P).
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology Finset
open Cvs.Zeta.GaussKernel.AdmissibleKernel (nonTrivialZeroSet)
open Cvs.StepA.Edge.FiniteTopGap (mult mult_nonneg)
open Cvs.StepA.Edge.DeepSetZeroSums (deepSet mem_deepSet)
open Cvs.StepA.Edge.GapRectangleBlaschke (phi Gap)
open Cvs.Zeta.ZeroCounting.WeightedLocalCountsCutoff (phiNear)

namespace Cvs.Zeta.ZeroCounting.GappedCutoffPairMass
open Cvs.ZeroCounting

open scoped Classical

/-- The candidate cutoff `H_j = H₀ + 3j + 1`. -/
def hc (H₀ : ℝ) (j : ℕ) : ℝ := H₀ + 3 * j + 1

/-- A candidate is unblocked when no deep ordinate below `4H₀` lies within `1` of it. -/
def Good (δD H₀ : ℝ) (j : ℕ) : Prop := ∀ ρ ∈ deepSet δD (4 * H₀), 1 ≤ |(|(ρ : ℂ).im| - hc H₀ j)|

/-- The number of candidates `J = ⌊(H₀ − 1)/3⌋`. -/
def nJ (H₀ : ℝ) : ℕ := ⌊(H₀ - 1) / 3⌋₊

theorem hc_le {H₀ : ℝ} (hH₀ : 1 ≤ H₀) {j : ℕ} (hj : j < nJ H₀) : hc H₀ j ≤ 2 * H₀ := by
  unfold hc
  have h1 : (j : ℝ) + 1 ≤ nJ H₀ := by exact_mod_cast hj
  have h2 : (nJ H₀ : ℝ) ≤ (H₀ - 1) / 3 := Nat.floor_le (by linarith)
  linarith

theorem le_hc (H₀ : ℝ) (j : ℕ) : H₀ ≤ hc H₀ j := by unfold hc; have := Nat.cast_nonneg (α := ℝ) j; linarith

/-- An unblocked candidate is a gapped cutoff. -/
theorem gap_of_good {δD H₀ : ℝ} (hH₀ : 1 ≤ H₀) {j : ℕ} (hj : j < nJ H₀) (hg : Good δD H₀ j) :
    Gap δD (hc H₀ j) := by
  intro ρ hρ
  by_cases h : |(ρ : ℂ).im| ≤ 4 * H₀
  · exact hg ρ (mem_deepSet.2 ⟨h, hρ⟩)
  · have := hc_le hH₀ hj
    rw [abs_of_nonneg (by linarith)]
    linarith

/-- **The blocked candidates**: at most `N = #{deep ρ : |γ_ρ| ≤ 4H₀}`. -/
theorem card_bad_le (δD H₀ : ℝ) :
    ((Finset.range (nJ H₀)).filter (fun j => ¬ Good δD H₀ j)).card ≤ (deepSet δD (4 * H₀)).card := by
  classical
  have hw : ∀ j ∈ (Finset.range (nJ H₀)).filter (fun j => ¬ Good δD H₀ j),
      ∃ ρ ∈ deepSet δD (4 * H₀), |(|(ρ : ℂ).im| - hc H₀ j)| < 1 := by
    intro j hj
    have := (Finset.mem_filter.1 hj).2
    unfold Good at this
    push Not at this
    exact this
  rcases ((Finset.range (nJ H₀)).filter (fun j => ¬ Good δD H₀ j)).eq_empty_or_nonempty with he | ⟨j₀, hj₀⟩
  · rw [he]; exact Nat.zero_le _
  have : Nonempty nonTrivialZeroSet := ⟨(hw j₀ hj₀).choose⟩
  choose! f hf using hw
  refine Finset.card_le_card_of_injOn f (fun j hj => (hf j hj).1) ?_
  intro j hj j' hj' he
  have h1 := (hf j hj).2
  have h2 := (hf j' hj').2
  rw [he] at h1
  have h3 : |hc H₀ j - hc H₀ j'| < 2 := by
    have := abs_sub_le (hc H₀ j) (|((f j' : nonTrivialZeroSet) : ℂ).im|) (hc H₀ j')
    rw [abs_sub_comm] at h1
    linarith
  unfold hc at h3
  have h4 : |(3 : ℝ) * ((j : ℝ) - j')| < 2 := by
    have : H₀ + 3 * (j : ℝ) + 1 - (H₀ + 3 * j' + 1) = 3 * ((j : ℝ) - j') := by ring
    rwa [this] at h3
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)] at h4
  have h5 : |(j : ℝ) - j'| < 1 := by linarith
  rcases lt_trichotomy j j' with h | h | h
  · have : (j : ℝ) + 1 ≤ j' := by exact_mod_cast h
    rw [abs_lt] at h5; linarith [h5.1]
  · exact h
  · have : (j' : ℝ) + 1 ≤ j := by exact_mod_cast h
    rw [abs_lt] at h5; linarith [h5.2]

/-- **Straddling candidates**: the candidates in `[t', t)` number at most `(t − t')/3 + 1`. -/
theorem card_straddle_le {H₀ t t' : ℝ} (S : Finset ℕ) (hne : S.Nonempty)
    (hS : ∀ j ∈ S, t' ≤ hc H₀ j ∧ hc H₀ j < t) : (S.card : ℝ) ≤ (t - t') / 3 + 1 := by
  obtain ⟨j₀, hj₀⟩ := hne
  set a := ⌈(t' - H₀ - 1) / 3⌉₊
  set b := ⌊(t - H₀ - 1) / 3⌋₊
  have hmem : ∀ j ∈ S, a ≤ j ∧ j ≤ b := by
    intro j hj
    obtain ⟨h1, h2⟩ := hS j hj
    unfold hc at h1 h2
    exact ⟨Nat.ceil_le.2 (by linarith), Nat.le_floor (by linarith)⟩
  have hsub : S ⊆ Finset.Icc a b := fun j hj => Finset.mem_Icc.2 (hmem j hj)
  have hcard := Finset.card_le_card hsub
  rw [Nat.card_Icc] at hcard
  have hab : a ≤ b := (hmem j₀ hj₀).1.trans (hmem j₀ hj₀).2
  have hb : (b : ℝ) ≤ (t - H₀ - 1) / 3 := by
    refine Nat.floor_le ?_
    obtain ⟨_, h2⟩ := hS j₀ hj₀
    unfold hc at h2
    have := Nat.cast_nonneg (α := ℝ) j₀
    linarith
  have ha : (t' - H₀ - 1) / 3 ≤ (a : ℝ) := Nat.le_ceil _
  have : (S.card : ℝ) ≤ ((b + 1 - a : ℕ) : ℝ) := by exact_mod_cast hcard
  rw [Nat.cast_sub (by omega)] at this
  push_cast at this
  linarith

/-- The near pair mass as a double sum over the deep zeros below `4H₀`. -/
theorem phiNear_eq {δD H₀ : ℝ} (hH₀ : 1 ≤ H₀) {j : ℕ} (hj : j < nJ H₀) :
    phiNear δD (hc H₀ j) (4 * H₀) = ∑ ρ ∈ deepSet δD (4 * H₀), ∑ ρ' ∈ deepSet δD (4 * H₀),
      if hc H₀ j < |(ρ : ℂ).im| ∧ |(ρ' : ℂ).im| ≤ hc H₀ j
      then mult ρ * (1 / (|(ρ : ℂ).im| - |(ρ' : ℂ).im|) ^ 2) else 0 := by
  have hle := hc_le hH₀ hj
  have hset : deepSet δD (hc H₀ j) = (deepSet δD (4 * H₀)).filter
      (fun ρ' : nonTrivialZeroSet => |(ρ' : ℂ).im| ≤ hc H₀ j) := by
    ext ρ'
    rw [Finset.mem_filter, mem_deepSet, mem_deepSet]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨⟨by linarith, h2⟩, h1⟩
    · rintro ⟨⟨_, h2⟩, h1⟩; exact ⟨h1, h2⟩
  unfold phiNear phi
  rw [hset, Finset.sum_filter]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [Finset.sum_filter, Finset.mul_sum]
  split_ifs with h1
  · refine Finset.sum_congr rfl fun ρ' _ => ?_
    split_ifs with h2 h3 h3 <;> simp_all
  · refine (Finset.sum_eq_zero fun ρ' _ => ?_).symm
    rw [if_neg (fun h => h1 h.1)]

/-- One straddling pair summed over the unblocked candidates: at most `m_ρ/Δ` when `Δ ≥ 2`, else `0`. -/
theorem sum_good_pair_le {δD H₀ : ℝ} {ρ ρ' : nonTrivialZeroSet} (hρ : ρ ∈ deepSet δD (4 * H₀))
    (hρ' : ρ' ∈ deepSet δD (4 * H₀)) :
    ∑ j ∈ (Finset.range (nJ H₀)).filter (Good δD H₀),
      (if hc H₀ j < |(ρ : ℂ).im| ∧ |(ρ' : ℂ).im| ≤ hc H₀ j
        then mult ρ * (1 / (|(ρ : ℂ).im| - |(ρ' : ℂ).im|) ^ 2) else 0)
      ≤ if 2 ≤ |(ρ : ℂ).im| - |(ρ' : ℂ).im| then mult ρ * (1 / (|(ρ : ℂ).im| - |(ρ' : ℂ).im|)) else 0 := by
  set Gd := (Finset.range (nJ H₀)).filter (Good δD H₀)
  set Δ := |(ρ : ℂ).im| - |(ρ' : ℂ).im|
  have hm := mult_nonneg ρ
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  set S := Gd.filter (fun j => hc H₀ j < |(ρ : ℂ).im| ∧ |(ρ' : ℂ).im| ≤ hc H₀ j)
  rcases S.eq_empty_or_nonempty with he | hne
  · rw [he, Finset.card_empty, Nat.cast_zero, zero_mul]
    split_ifs <;> [positivity; exact le_rfl]
  obtain ⟨j₀, hj₀⟩ := hne
  have hj₀' := Finset.mem_filter.1 hj₀
  have hgood := (Finset.mem_filter.1 hj₀'.1).2
  have g1 := hgood ρ hρ
  have g2 := hgood ρ' hρ'
  rw [abs_of_pos (by linarith [hj₀'.2.1])] at g1
  rw [abs_of_nonpos (by linarith [hj₀'.2.2])] at g2
  have hΔ : 2 ≤ Δ := by linarith [hj₀'.2.1, hj₀'.2.2]
  rw [if_pos hΔ]
  have hc := card_straddle_le S ⟨j₀, hj₀⟩ (t := |(ρ : ℂ).im|) (t' := |(ρ' : ℂ).im|)
    (fun j hj => ⟨(Finset.mem_filter.1 hj).2.2, (Finset.mem_filter.1 hj).2.1⟩)
  have hcΔ : (S.card : ℝ) ≤ Δ := by linarith
  have hΔ0 : 0 < Δ := by linarith
  calc (S.card : ℝ) * (mult ρ * (1 / Δ ^ 2)) ≤ Δ * (mult ρ * (1 / Δ ^ 2)) :=
        mul_le_mul_of_nonneg_right hcΔ (by positivity)
    _ = mult ρ * (1 / Δ) := by field_simp

/-- **The total near pair mass over the unblocked candidates**. -/
theorem sum_good_phiNear_le {δD H₀ : ℝ} (hH₀ : 1 ≤ H₀) :
    ∑ j ∈ (Finset.range (nJ H₀)).filter (Good δD H₀), phiNear δD (hc H₀ j) (4 * H₀)
      ≤ (deepSet δD (4 * H₀)).card * (264 * Real.log (8 * H₀ + 5) * (1 + Real.log (4 * H₀ + 1))) := by
  set D := deepSet δD (4 * H₀)
  set Gd := (Finset.range (nJ H₀)).filter (Good δD H₀)
  set B := 264 * Real.log (8 * H₀ + 5) * (1 + Real.log (4 * H₀ + 1))
  have h1 : ∑ j ∈ Gd, phiNear δD (hc H₀ j) (4 * H₀) = ∑ j ∈ Gd, ∑ ρ ∈ D, ∑ ρ' ∈ D,
      (if hc H₀ j < |(ρ : ℂ).im| ∧ |(ρ' : ℂ).im| ≤ hc H₀ j
        then mult ρ * (1 / (|(ρ : ℂ).im| - |(ρ' : ℂ).im|) ^ 2) else 0) :=
    Finset.sum_congr rfl fun j hj => phiNear_eq hH₀ (Finset.mem_range.1 (Finset.mem_filter.1 hj).1)
  rw [h1, Finset.sum_comm]
  have h2 : ∀ ρ ∈ D, ∑ j ∈ Gd, ∑ ρ' ∈ D,
      (if hc H₀ j < |(ρ : ℂ).im| ∧ |(ρ' : ℂ).im| ≤ hc H₀ j
        then mult ρ * (1 / (|(ρ : ℂ).im| - |(ρ' : ℂ).im|) ^ 2) else 0)
      ≤ ∑ ρ' ∈ D, if 2 ≤ |(ρ : ℂ).im| - |(ρ' : ℂ).im|
        then mult ρ * (1 / (|(ρ : ℂ).im| - |(ρ' : ℂ).im|)) else 0 := by
    intro ρ hρ
    rw [Finset.sum_comm]
    exact Finset.sum_le_sum fun ρ' hρ' => sum_good_pair_le hρ hρ'
  refine (Finset.sum_le_sum h2).trans ?_
  rw [Finset.sum_comm, ← nsmul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun ρ' hρ' => ?_
  rw [← Finset.sum_filter]
  set t' := |(ρ' : ℂ).im|
  have ht' : t' ≤ 4 * H₀ := (mem_deepSet.1 hρ').1
  set K := ⌈4 * H₀⌉₊
  have hK : (K : ℝ) ≤ 4 * H₀ + 1 := (Nat.ceil_lt_add_one (by linarith)).le
  refine (Cvs.Zeta.ZeroCounting.WeightedLocalCountsCutoff.sum_mult_mul_le _ (abs_nonneg _) K (g := fun y => 1 / y) (fun y hy => by positivity)
    (fun y y' hy hyy' => one_div_le_one_div_of_le (by linarith) hyy') fun ρ hρ => ?_).trans ?_
  · obtain ⟨hρD, hρ2⟩ := Finset.mem_filter.1 hρ
    have := (mem_deepSet.1 hρD).1
    have hK' : 4 * H₀ ≤ K := Nat.le_ceil _
    constructor <;> linarith [abs_nonneg ((ρ' : ℂ).im)]
  · calc ∑ k ∈ Finset.Icc 1 K, 264 * Real.log (t' + k + 4) * (1 / (k : ℝ))
        ≤ ∑ k ∈ Finset.Icc 1 K, 264 * Real.log (8 * H₀ + 5) * (1 / (k : ℝ)) := by
          refine Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_right ?_ (by positivity)
          have hk2 : (k : ℝ) ≤ K := by exact_mod_cast (Finset.mem_Icc.1 hk).2
          have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (Finset.mem_Icc.1 hk).1
          exact mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) (by linarith)) (by norm_num)
      _ = 264 * Real.log (8 * H₀ + 5) * ∑ k ∈ Finset.Icc 1 K, 1 / (k : ℝ) := by rw [Finset.mul_sum]
      _ ≤ 264 * Real.log (8 * H₀ + 5) * (1 + Real.log K) :=
          mul_le_mul_of_nonneg_left (Cvs.Zeta.ZeroCounting.WeightedLocalCountsCutoff.sum_Icc_inv_le K)
            (mul_nonneg (by norm_num) (Real.log_nonneg (by linarith)))
      _ ≤ B := by
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (by norm_num) (Real.log_nonneg (by linarith)))
          rcases Nat.eq_zero_or_pos K with h0 | hpos
          · rw [h0, Nat.cast_zero, Real.log_zero]; linarith [Real.log_nonneg (show (1 : ℝ) ≤ 4 * H₀ + 1 by linarith)]
          · have : (1 : ℝ) ≤ K := by exact_mod_cast hpos
            linarith [Real.log_le_log (by linarith) hK]

/-- **Lemma P** (caseinf-W §7): for `H₀ ≥ 1`, `J ≥ 1` and `2N ≤ J`, `N = #{deep ρ : |γ_ρ| ≤ 4H₀}`, some gapped
`H ∈ [H₀, 2H₀]` has `phiNear δ_D H (4H₀) ≤ 2N·264 log(8H₀ + 5)(1 + log(4H₀ + 1))/J`. -/
theorem lemmaP {δD H₀ : ℝ} (hH₀ : 1 ≤ H₀) (hJ : 1 ≤ nJ H₀)
    (hN : 2 * (deepSet δD (4 * H₀)).card ≤ nJ H₀) :
    ∃ H : ℝ, H₀ ≤ H ∧ H ≤ 2 * H₀ ∧ Gap δD H ∧ phiNear δD H (4 * H₀)
      ≤ 2 * (deepSet δD (4 * H₀)).card * (264 * Real.log (8 * H₀ + 5) * (1 + Real.log (4 * H₀ + 1)))
        / nJ H₀ := by
  set N := (deepSet δD (4 * H₀)).card
  set B := 264 * Real.log (8 * H₀ + 5) * (1 + Real.log (4 * H₀ + 1))
  set Gd := (Finset.range (nJ H₀)).filter (Good δD H₀)
  have hcard : Gd.card + ((Finset.range (nJ H₀)).filter (fun j => ¬ Good δD H₀ j)).card = nJ H₀ := by
    rw [Finset.card_filter_add_card_filter_not, Finset.card_range]
  have hbad := card_bad_le δD H₀
  have hGd : nJ H₀ ≤ 2 * Gd.card := by omega
  have hGd0 : 0 < Gd.card := by omega
  have hne : Gd.Nonempty := Finset.card_pos.1 hGd0
  have hB0 : 0 ≤ B := mul_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg (by linarith)))
    (by linarith [Real.log_nonneg (show (1 : ℝ) ≤ 4 * H₀ + 1 by linarith)])
  have hsum := sum_good_phiNear_le (δD := δD) hH₀
  have hconst : ∑ j ∈ Gd, phiNear δD (hc H₀ j) (4 * H₀) ≤ ∑ j ∈ Gd, (N * B / Gd.card) := by
    rw [Finset.sum_const, nsmul_eq_mul]
    have : (Gd.card : ℝ) * (N * B / Gd.card) = N * B := by
      field_simp
    rw [this]; exact hsum
  obtain ⟨j, hj, hjle⟩ := Finset.exists_le_of_sum_le hne hconst
  have hjJ : j < nJ H₀ := Finset.mem_range.1 (Finset.mem_filter.1 hj).1
  refine ⟨hc H₀ j, le_hc H₀ j, hc_le hH₀ hjJ, gap_of_good hH₀ hjJ (Finset.mem_filter.1 hj).2, ?_⟩
  refine hjle.trans ?_
  have hJr : (nJ H₀ : ℝ) ≤ 2 * Gd.card := by exact_mod_cast hGd
  have hGr : (0 : ℝ) < Gd.card := by exact_mod_cast hGd0
  have hJ0 : (0 : ℝ) < nJ H₀ := by exact_mod_cast hJ
  rw [div_le_div_iff₀ hGr hJ0]
  have hNB : 0 ≤ (N : ℝ) * B := mul_nonneg (Nat.cast_nonneg _) hB0
  nlinarith

end Cvs.Zeta.ZeroCounting.GappedCutoffPairMass

end
