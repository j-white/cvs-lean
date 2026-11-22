import Mathlib
import Cvs.Prolate.ConverseLevelCount
import Cvs.Prolate.EdgeCentreSign
import Cvs.Prolate.EvenLevelIndexLemma
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.Gram.PotentialFloorFromCounts
import Cvs.Prolate.Gram.ProlateCellGramHalfUnit
import Cvs.Prolate.Gram.RobinNodeLatticeDualFloor
import Cvs.Prolate.Gram.WeylCountsDiscretePotential
import Cvs.Prolate.LiouvilleGreen.WeylZeroCountLog
import Cvs.Prolate.RegularSolutionEdge
import Cvs.Prolate.TopRungZeroSplitHalf
import Cvs.Route.Visibility.LayerFloorDeepRemainderB

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The rung Weyl count `RungCount`

By the Sturm count (Cvs.Prolate.EvenLevelIndexLemma, Cvs.Prolate.ConverseLevelCount) the even levels below `c²u` number the zeros of `y_{c²u}` in `(0, 1)` up to one,
and the rungs are every second even level; Cvs.Prolate.LiouvilleGreen.WeylZeroCountLog counts those zeros as `2xW(u)` up to `O(log c)`.
-/

noncomputable section

open Real Set Filter Topology Finset
open Cvs.Prolate.RegularSolutionEdge (regSol sqC)
open Cvs.Prolate.TopRungZeroSplitHalf (ZerosOn)

namespace Cvs.Prolate.RungWeylCount
open Cvs.ZeroCounting

/-- `#{j < x : 2j < m} = min(x, ⌈m/2⌉)`. -/
theorem card_two_mul_lt (x m : ℕ) : (univ.filter fun j : Fin x => 2 * (j : ℕ) < m).card = min x ((m + 1) / 2) := by
  rw [show (univ.filter fun j : Fin x => 2 * (j : ℕ) < m) = univ.filter fun j : Fin x => (j : ℕ) < (m + 1) / 2 from
    Finset.filter_congr fun j _ => by omega]
  exact Fin.card_filter_val_lt

/-- `#{j < x : 2j ≤ k} ≤ k/2 + 1`. -/
theorem card_two_mul_le (x k : ℕ) : (univ.filter fun j : Fin x => 2 * (j : ℕ) ≤ k).card ≤ k / 2 + 1 := by
  rw [show (univ.filter fun j : Fin x => 2 * (j : ℕ) ≤ k) = univ.filter fun j : Fin x => (j : ℕ) < k / 2 + 1 from
    Finset.filter_congr fun j _ => by omega, Fin.card_filter_val_lt]
  exact min_le_right _ _

variable {x : ℕ}

/-- **Rungs below a level with `m` zeros**: if `y_Λ` has `m` zeros in `(0, 1)`, at least `min(x, ⌈m/2⌉)` rung
levels lie below `Λ`. -/
theorem le_card_of_hasZeros {Λ : ℝ} {m : ℕ}
    (hm : ZerosOn (regSol (sqC (2 * π * x)) Λ) (Ioo 0 1) m) :
    min x ((m + 1) / 2) ≤ (univ.filter fun j : Fin x => Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.chi x j ≤ Λ).card := by
  rw [← card_two_mul_lt]
  refine Finset.card_le_card fun j hj => ?_
  rw [Finset.mem_filter] at hj ⊢
  refine ⟨hj.1, ?_⟩
  have hN := Cvs.Prolate.EvenLevelIndexLemma.le_ncard_evenSpec ((Cvs.Prolate.TopRungZeroSplitHalf.hasZeros_iff).mpr hm)
  obtain ⟨χ', hχ', hidx⟩ := Cvs.Prolate.EvenRungsByIndex.exists_isLevelIdx_of_lt_ncard (c := 2 * π * x) (k := 2 * (j : ℕ))
    (lt_of_lt_of_le hj.2 hN)
  have : Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.chi x j = χ' := Cvs.Prolate.EvenRungsByIndex.lev_eq hidx
  rw [this]; exact hχ'.le

/-- **Rungs below a level without `k + 1` zeros**: if `y_Λ` has no `k + 1` zeros in `(0, 1)`, at most `k/2 + 2` rung
levels lie at or below `Λ`. -/
theorem card_le_of_not_hasZeros (hx : 80 ≤ 2 * π * x) {Λ : ℝ} {k : ℕ}
    (hk : ¬ZerosOn (regSol (sqC (2 * π * x)) Λ) (Ioo 0 1) (k + 1)) :
    (univ.filter fun j : Fin x => Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.chi x j ≤ Λ).card ≤ k / 2 + 2 := by
  classical
  have hsub : (univ.filter fun j : Fin x => Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.chi x j ≤ Λ) ⊆
      (univ.filter fun j : Fin x => 2 * (j : ℕ) ≤ k) ∪ (univ.filter fun j : Fin x => Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.chi x j = Λ) := by
    intro j hj
    rw [Finset.mem_filter] at hj
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    by_contra h
    push Not at h
    have hk' : k + 1 ≤ 2 * (j : ℕ) := by have := h.1 (mem_univ j); omega
    have hle := Cvs.Prolate.ConverseLevelCount.le_of_not_hasZeros ((Cvs.Prolate.TopRungZeroSplitHalf.hasZeros_iff).not.mpr hk) (Cvs.Prolate.Gram.PotentialFloorFromCounts.chi_mem hx j) hk'
    exact h.2 (mem_univ j) (le_antisymm hj.2 hle)
  have hone : (univ.filter fun j : Fin x => Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.chi x j = Λ).card ≤ 1 := by
    refine Finset.card_le_one.mpr fun a ha b hb => ?_
    rw [Finset.mem_filter] at ha hb
    exact (Cvs.Prolate.Gram.ProlateCellGramHalfUnit.lev_strictMono hx).injective (ha.2.trans hb.2.symm)
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_union_le _ _
    _ ≤ k / 2 + 1 + 1 := add_le_add (card_two_mul_le x k) hone

/-! ### The rung count -/

theorem rungWeyl_le_one (u : ℝ) : Cvs.Prolate.Gram.WeylCountsDiscretePotential.rungWeyl u ≤ 1 := by
  unfold Cvs.Prolate.Gram.WeylCountsDiscretePotential.rungWeyl
  have hb : ∀ t ∈ Icc (0 : ℝ) 1, √((min u 1 - t ^ 2) / (1 - t ^ 2)) ≤ 1 := fun t ht => by
    rw [Real.sqrt_le_one]
    rcases eq_or_lt_of_le ht.2 with h | h
    · rw [h]; simp
    · have hp : 0 < 1 - t ^ 2 := by nlinarith [ht.1]
      rw [div_le_one hp]; linarith [min_le_right u 1]
  have hi : IntervalIntegrable (fun t => √((min u 1 - t ^ 2) / (1 - t ^ 2))) MeasureTheory.volume 0 1 := by
    refine (intervalIntegrable_const (c := (1 : ℝ))).mono_fun' (Measurable.aestronglyMeasurable (by measurability)) ?_
    refine (MeasureTheory.ae_restrict_iff' measurableSet_uIoc).mpr (Eventually.of_forall fun t ht => ?_)
    rw [uIoc_of_le zero_le_one] at ht
    show ‖√((min u 1 - t ^ 2) / (1 - t ^ 2))‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact hb t ⟨ht.1.le, ht.2⟩
  calc ∫ t in (0 : ℝ)..1, √((min u 1 - t ^ 2) / (1 - t ^ 2)) ≤ ∫ t in (0 : ℝ)..1, (1 : ℝ) :=
        intervalIntegral.integral_mono_on zero_le_one hi intervalIntegrable_const hb
    _ = 1 := by simp

theorem weylI_eq_rungWeyl {u : ℝ} (hu : u ≤ 1) : Cvs.Prolate.LiouvilleGreen.WeylZeroCountLog.weylI 0 u = Cvs.Prolate.Gram.WeylCountsDiscretePotential.rungWeyl u := by
  unfold Cvs.Prolate.LiouvilleGreen.WeylZeroCountLog.weylI Cvs.Prolate.Gram.WeylCountsDiscretePotential.rungWeyl; rw [min_eq_left hu]

/-- The error of the rung count is `O(log c)`: `errUp + errLow + 5 ≤ 12 + 4 log c` at `V = 1`, `c ≥ 1`. -/
theorem err_le_log {c : ℝ} (hc : 1 ≤ c) : Cvs.Prolate.LiouvilleGreen.WeylZeroCountLog.errUp c 1 + Cvs.Prolate.LiouvilleGreen.WeylZeroCountLog.errLow c 1 + 5 ≤ 12 + 4 * log c := by
  have hc0 : 0 < c := by linarith
  have hL : 0 ≤ log c := Real.log_nonneg hc
  have h1 : log (c ^ 2 * 1) = 2 * log c := by rw [mul_one, Real.log_pow]; push_cast; ring
  have h2 : log (8 * c ^ 2 * 1) = log 8 + 2 * log c := by
    rw [mul_one, Real.log_mul (by norm_num) (by positivity), Real.log_pow]; push_cast; ring
  have h8 : log 8 < 3 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    have := Real.log_two_lt_d9; push_cast; linarith
  have h80 : 0 ≤ log 8 := Real.log_nonneg (by norm_num)
  have hπ : 3 < π := Real.pi_gt_three
  have hs2 : 1 ≤ √2 := by rw [Real.one_le_sqrt]; norm_num
  unfold Cvs.Prolate.LiouvilleGreen.WeylZeroCountLog.errUp Cvs.Prolate.LiouvilleGreen.WeylZeroCountLog.errLow
  rw [h1, h2]
  have t1 : 2 * log c / (4 * π) ≤ log c := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have t2 : (log 8 + 2 * log c) / (2 * √2) ≤ (log 8 + 2 * log c) / 2 :=
    div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
  have t3 : ((log 8 + 2 * log c) / 2 + 1 + 2 * log c / 4) / π ≤ (log 8 + 2 * log c) / 2 + 1 + 2 * log c / 4 :=
    div_le_self (by positivity) (by linarith)
  have e : (log 8 + 2 * log c) / 2 / 2 = (log 8 + 2 * log c) / 4 := by ring
  linarith

/-- The rung count error is eventually below `εc/log c`. -/
theorem eventually_log_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℕ in atTop, (12 + 4 * log (2 * π * x)) / 2 ≤ ε * (2 * π * x) / log (2 * π * x) := by
  have h2 : Tendsto (fun c : ℝ => log c ^ 2 / c) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero
  have h1 : Tendsto (fun c : ℝ => log c / c) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have h := (h1.const_mul 6).add (h2.const_mul 2)
  simp only [mul_zero, add_zero] at h
  have hev : ∀ᶠ c : ℝ in atTop, (12 + 4 * log c) / 2 ≤ ε * c / log c := by
    filter_upwards [h.eventually (gt_mem_nhds hε), eventually_gt_atTop (Real.exp 1)] with c hc hce
    have hc0 : 0 < c := (Real.exp_pos 1).trans hce
    have hL : 1 < log c := by rw [Real.lt_log_iff_exp_lt hc0]; exact hce
    rw [le_div_iff₀ (by linarith)]
    have e : 6 * (log c / c) + 2 * (log c ^ 2 / c) = (6 * log c + 2 * log c ^ 2) / c := by ring
    rw [e, div_lt_iff₀ hc0] at hc
    nlinarith
  exact Cvs.Prolate.Gram.PotentialFloorFromCounts.tendsto_scale.eventually hev

/-- **The rung Weyl count** (eq-cpb Lemma 10 for the rungs). -/
theorem rungCount : Cvs.Prolate.Gram.WeylCountsDiscretePotential.RungCount := by
  intro ε hε
  filter_upwards [Cvs.Route.Visibility.LayerFloorDeepRemainderB.eventually_scale, eventually_log_le hε] with x hx hlog
  intro u hu
  set c := 2 * π * (x : ℝ) with hc
  have hc1 : 1 ≤ c := by linarith
  have hc0 : 0 < c := by linarith
  have hπ : 0 < π := Real.pi_pos
  set R := (univ.filter fun j : Fin x => Cvs.Prolate.Gram.ProlateCellGramHalfUnit.levT x j ≤ u).card with hR
  have hR' : R = (univ.filter fun j : Fin x => Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.chi x j ≤ c ^ 2 * u).card := by
    rw [hR]; congr 1
    refine Finset.filter_congr fun j _ => ?_
    rw [Cvs.Prolate.Gram.PotentialFloorFromCounts.chi_eq, ← hc]
    exact (mul_le_mul_iff_of_pos_left (by positivity)).symm
  set A := c / π * Cvs.Prolate.LiouvilleGreen.WeylZeroCountLog.weylI 0 u with hA
  have hAx : A = 2 * x * Cvs.Prolate.Gram.WeylCountsDiscretePotential.rungWeyl u := by
    rw [hA, weylI_eq_rungWeyl hu.2, hc]; field_simp
  have hW1 := rungWeyl_le_one u
  have hW0 : 0 ≤ Cvs.Prolate.Gram.WeylCountsDiscretePotential.rungWeyl u := by rw [← weylI_eq_rungWeyl hu.2]; exact Cvs.Prolate.LiouvilleGreen.WeylZeroCountLog.weylI_nonneg zero_le_one
  have herr := err_le_log hc1
  have hlow0 : 0 ≤ Cvs.Prolate.LiouvilleGreen.WeylZeroCountLog.errLow c 1 := by
    unfold Cvs.Prolate.LiouvilleGreen.WeylZeroCountLog.errLow
    have : 0 ≤ log (8 * c ^ 2 * 1) := Real.log_nonneg (by nlinarith)
    have : 0 ≤ log (c ^ 2 * 1) := Real.log_nonneg (by nlinarith)
    positivity
  have hup0 : 0 ≤ Cvs.Prolate.LiouvilleGreen.WeylZeroCountLog.errUp c 1 := by
    unfold Cvs.Prolate.LiouvilleGreen.WeylZeroCountLog.errUp
    have : 0 ≤ log (8 * c ^ 2 * 1) := Real.log_nonneg (by nlinarith)
    have : 0 ≤ log (c ^ 2 * 1) := Real.log_nonneg (by nlinarith)
    positivity
  -- the lower bound
  have hlo : (x : ℝ) * Cvs.Prolate.Gram.WeylCountsDiscretePotential.rungWeyl u - (Cvs.Prolate.LiouvilleGreen.WeylZeroCountLog.errLow c 1 + 1) / 2 ≤ R := by
    by_cases hneg : A - Cvs.Prolate.LiouvilleGreen.WeylZeroCountLog.errLow c 1 < 0
    · have : (x : ℝ) * Cvs.Prolate.Gram.WeylCountsDiscretePotential.rungWeyl u ≤ Cvs.Prolate.LiouvilleGreen.WeylZeroCountLog.errLow c 1 / 2 := by linarith
      have : (0 : ℝ) ≤ R := Nat.cast_nonneg _
      linarith
    push Not at hneg
    set m := ⌊A - Cvs.Prolate.LiouvilleGreen.WeylZeroCountLog.errLow c 1⌋₊ with hm
    have hmle : (m : ℝ) ≤ A - Cvs.Prolate.LiouvilleGreen.WeylZeroCountLog.errLow c 1 := Nat.floor_le hneg
    have hmlt : A - Cvs.Prolate.LiouvilleGreen.WeylZeroCountLog.errLow c 1 < m + 1 := Nat.lt_floor_add_one _
    have hz := Cvs.Prolate.LiouvilleGreen.WeylZeroCountLog.zero_count_ge (V := 1) hc1 hu.1 hu.2 le_rfl le_rfl one_pos (m := m) hmle
    have hcard := le_card_of_hasZeros (x := x) hz
    rw [← hR'] at hcard
    rcases min_choice x ((m + 1) / 2) with h | h
    · rw [h] at hcard
      have : (x : ℝ) ≤ R := by exact_mod_cast hcard
      nlinarith
    · rw [h] at hcard
      have h2 : (m : ℝ) ≤ 2 * (((m + 1) / 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : m ≤ 2 * ((m + 1) / 2))
      have : (((m + 1) / 2 : ℕ) : ℝ) ≤ R := by exact_mod_cast hcard
      linarith
  -- the upper bound
  have hhi : (R : ℝ) ≤ x * Cvs.Prolate.Gram.WeylCountsDiscretePotential.rungWeyl u + Cvs.Prolate.LiouvilleGreen.WeylZeroCountLog.errUp c 1 / 2 + 2 := by
    set k := ⌊A + Cvs.Prolate.LiouvilleGreen.WeylZeroCountLog.errUp c 1⌋₊ with hk
    have hA0 : 0 ≤ A := by rw [hAx]; positivity
    have hklt : A + Cvs.Prolate.LiouvilleGreen.WeylZeroCountLog.errUp c 1 < k + 1 := Nat.lt_floor_add_one _
    have hkle : (k : ℝ) ≤ A + Cvs.Prolate.LiouvilleGreen.WeylZeroCountLog.errUp c 1 := Nat.floor_le (by linarith)
    have hnz : ¬ZerosOn (regSol (sqC c) (c ^ 2 * u)) (Ioo 0 1) (k + 1) := fun h => by
      have := Cvs.Prolate.LiouvilleGreen.WeylZeroCountLog.zero_count_le (V := 1) hc1 hu.1 hu.2 le_rfl le_rfl one_pos h
      push_cast at this
      linarith
    have hcard := card_le_of_not_hasZeros hx hnz
    rw [← hR'] at hcard
    have h2 : 2 * ((k / 2 : ℕ) : ℝ) ≤ k := by exact_mod_cast (by omega : 2 * (k / 2) ≤ k)
    have : (R : ℝ) ≤ (k / 2 : ℕ) + 2 := by exact_mod_cast hcard
    linarith
  rw [abs_le]
  constructor <;> linarith

end Cvs.Prolate.RungWeylCount

end
