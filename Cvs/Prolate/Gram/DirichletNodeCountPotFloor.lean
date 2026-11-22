import Mathlib
import Cvs.Prolate.Gram.DeepCellFloorAmplitude
import Cvs.Prolate.Gram.DeepRemainderCellFloors
import Cvs.Prolate.Gram.EndpointAmplitudeFloor
import Cvs.Prolate.Gram.PotentialFloorFromCounts
import Cvs.Prolate.Gram.WeylCountsDiscretePotential
import Cvs.Prolate.LiouvilleGreen.WeylZeroCountLog
import Cvs.Prolate.RegularSolutionEdge
import Cvs.Prolate.RungWeylCount
import Cvs.Prolate.SturmOscillationAtPoint
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
# The Dirichlet node count `DirCount`, and `PotFloor`

The nodes `σ < c²v` of `y_σ(a) = 0` number exactly the zeros of `y_{c²v}` in `(a, 1)` (Cvs.Prolate.SturmOscillationAtPoint), which Cvs.Prolate.LiouvilleGreen.WeylZeroCountLog counts as
`cΛ_a(v)` up to `O(log c)`; with the rung count (Cvs.Prolate.RungWeylCount) this gives `PotFloor` through Cvs.Prolate.Gram.PotentialFloorFromCounts.
-/

noncomputable section

open Real Set Filter Topology Finset
open Cvs.Prolate.RegularSolutionEdge (regSol sqC)
open Cvs.Prolate.TopRungZeroSplitHalf (ZerosOn)

namespace Cvs.Prolate.Gram.DirichletNodeCountPotFloor
open Cvs.ZeroCounting

/-- The error of the Weyl count is `O(log c)`: `errUp + errLow + 5 ≤ 12 + 4 log c + 2 log V` for `c, V ≥ 1`. -/
theorem err_le_log {c V : ℝ} (hc : 1 ≤ c) (hV : 1 ≤ V) :
    Cvs.Prolate.LiouvilleGreen.WeylZeroCountLog.errUp c V + Cvs.Prolate.LiouvilleGreen.WeylZeroCountLog.errLow c V + 5 ≤ 12 + 4 * log c + 2 * log V := by
  have hc0 : 0 < c := by linarith
  have hL : 0 ≤ log c := Real.log_nonneg hc
  have hLV : 0 ≤ log V := Real.log_nonneg hV
  have h1 : log (c ^ 2 * V) = 2 * log c + log V := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]; push_cast; ring
  have h2 : log (8 * c ^ 2 * V) = log 8 + 2 * log c + log V := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    push_cast; ring
  have h8 : log 8 < 3 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    have := Real.log_two_lt_d9; push_cast; linarith
  have h80 : 0 ≤ log 8 := Real.log_nonneg (by norm_num)
  have hπ : 3 < π := Real.pi_gt_three
  have hs2 : 1 ≤ √2 := by rw [Real.one_le_sqrt]; norm_num
  unfold Cvs.Prolate.LiouvilleGreen.WeylZeroCountLog.errUp Cvs.Prolate.LiouvilleGreen.WeylZeroCountLog.errLow
  rw [h1, h2]
  have t1 : (2 * log c + log V) / (4 * π) ≤ (2 * log c + log V) / 4 :=
    div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
  have t2 : (log 8 + 2 * log c + log V) / (2 * √2) ≤ (log 8 + 2 * log c + log V) / 2 :=
    div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
  have t3 : ((log 8 + 2 * log c + log V) / 2 + 1 + (2 * log c + log V) / 4) / π ≤
      (log 8 + 2 * log c + log V) / 2 + 1 + (2 * log c + log V) / 4 :=
    div_le_self (by positivity) (by linarith)
  linarith

/-- The count error is eventually below `εc/log c`. -/
theorem eventually_log_le {ε : ℝ} (K : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℕ in atTop, (K + 4 * log (2 * π * x)) / 2 ≤ ε * (2 * π * x) / log (2 * π * x) := by
  have h2 : Tendsto (fun c : ℝ => log c ^ 2 / c) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero
  have h1 : Tendsto (fun c : ℝ => log c / c) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have h := (h1.const_mul (K / 2)).add (h2.const_mul 2)
  simp only [mul_zero, add_zero] at h
  have hev : ∀ᶠ c : ℝ in atTop, (K + 4 * log c) / 2 ≤ ε * c / log c := by
    filter_upwards [h.eventually (gt_mem_nhds hε), eventually_gt_atTop (Real.exp 1)] with c hc hce
    have hc0 : 0 < c := (Real.exp_pos 1).trans hce
    have hL : 1 < log c := by rw [Real.lt_log_iff_exp_lt hc0]; exact hce
    rw [le_div_iff₀ (by linarith)]
    have e : K / 2 * (log c / c) + 2 * (log c ^ 2 / c) = (K / 2 * log c + 2 * log c ^ 2) / c := by ring
    rw [e, div_lt_iff₀ hc0] at hc
    nlinarith
  exact Cvs.Prolate.Gram.PotentialFloorFromCounts.tendsto_scale.eventually hev

theorem mul_dirWeyl (c a v : ℝ) : c * Cvs.Prolate.Gram.WeylCountsDiscretePotential.dirWeyl a v = c / π * Cvs.Prolate.LiouvilleGreen.WeylZeroCountLog.weylI a v := by
  unfold Cvs.Prolate.Gram.WeylCountsDiscretePotential.dirWeyl Cvs.Prolate.LiouvilleGreen.WeylZeroCountLog.weylI; ring

/-- **The Dirichlet node count** (eq-cpb Lemma 10 for the nodes at `a`). -/
theorem dirCount : Cvs.Prolate.Gram.WeylCountsDiscretePotential.DirCount := by
  intro ε hε V
  set W := max V 1 with hW
  have hW1 : 1 ≤ W := le_max_right _ _
  filter_upwards [Cvs.Route.Visibility.LayerFloorDeepRemainderB.eventually_scale, eventually_log_le (12 + 2 * log W) (half_pos hε)] with x hx hlog
  intro a ha v hv
  set c := 2 * π * (x : ℝ) with hc
  have hc1 : 1 ≤ c := by linarith
  have ha0 : 0 ≤ a := by linarith [ha.1]
  have ha1 : a < 1 := by linarith [ha.2]
  have hvW : v ≤ W := hv.2.trans (le_max_left _ _)
  set N := Cvs.Prolate.SturmOscillationAtPoint.nodeSpec (sqC c) a with hN
  have hset : Cvs.Prolate.Gram.WeylCountsDiscretePotential.dirNodes c a v = N ∩ Iic (c ^ 2 * v) := rfl
  have hfinIio := Cvs.Prolate.SturmOscillationAtPoint.finite_nodeSpec_Iio (sqC c) (a := a) (by linarith) ha1 (c ^ 2 * v)
  have hfinIic : (N ∩ Iic (c ^ 2 * v)).Finite :=
    (Cvs.Prolate.SturmOscillationAtPoint.finite_nodeSpec_Iio (sqC c) (a := a) (by linarith) ha1 (c ^ 2 * v + 1)).subset fun σ hσ =>
      ⟨hσ.1, mem_Iio.mpr (lt_of_le_of_lt (mem_Iic.mp hσ.2) (by linarith))⟩
  refine ⟨by rw [hset]; exact hfinIic, ?_⟩
  rw [hset]
  set n₀ := (N ∩ Iio (c ^ 2 * v)).ncard with hn₀
  set n := (N ∩ Iic (c ^ 2 * v)).ncard with hn
  have hn₀n : n₀ ≤ n := Set.ncard_le_ncard (inter_subset_inter_right _ Iio_subset_Iic_self) hfinIic
  have hnn₀ : n ≤ n₀ + 1 := by
    have hsub : N ∩ Iic (c ^ 2 * v) ⊆ insert (c ^ 2 * v) (N ∩ Iio (c ^ 2 * v)) := by
      intro σ hσ
      rcases eq_or_lt_of_le (mem_Iic.mp hσ.2) with h | h
      · exact Or.inl h
      · exact Or.inr ⟨hσ.1, h⟩
    exact (Set.ncard_le_ncard hsub (hfinIio.insert _)).trans (Set.ncard_insert_le _ _)
  set A := c / π * Cvs.Prolate.LiouvilleGreen.WeylZeroCountLog.weylI a v with hA
  rw [mul_dirWeyl, ← hA]
  have herr := err_le_log hc1 hW1
  have hlow0 : 0 ≤ Cvs.Prolate.LiouvilleGreen.WeylZeroCountLog.errLow c W := by
    unfold Cvs.Prolate.LiouvilleGreen.WeylZeroCountLog.errLow
    have : 0 ≤ log (8 * c ^ 2 * W) := Real.log_nonneg (by nlinarith)
    have : 0 ≤ log (c ^ 2 * W) := Real.log_nonneg (by nlinarith)
    positivity
  have hup0 : 0 ≤ Cvs.Prolate.LiouvilleGreen.WeylZeroCountLog.errUp c W := by
    unfold Cvs.Prolate.LiouvilleGreen.WeylZeroCountLog.errUp
    have : 0 ≤ log (8 * c ^ 2 * W) := Real.log_nonneg (by nlinarith)
    have : 0 ≤ log (c ^ 2 * W) := Real.log_nonneg (by nlinarith)
    positivity
  -- the upper bound
  have hup : (n₀ : ℝ) ≤ A + Cvs.Prolate.LiouvilleGreen.WeylZeroCountLog.errUp c W :=
    Cvs.Prolate.LiouvilleGreen.WeylZeroCountLog.zero_count_le hc1 hv.1 hvW hW1 ha0 ha1 (Cvs.Prolate.SturmOscillationAtPoint.zerosOn_ncard_nodeSpec (sqC c) (by linarith) ha1 _)
  -- the lower bound
  have hlo : A - Cvs.Prolate.LiouvilleGreen.WeylZeroCountLog.errLow c W - 1 ≤ n₀ := by
    by_cases hneg : A - Cvs.Prolate.LiouvilleGreen.WeylZeroCountLog.errLow c W < 0
    · have : (0 : ℝ) ≤ n₀ := Nat.cast_nonneg _
      linarith
    push Not at hneg
    set m := ⌊A - Cvs.Prolate.LiouvilleGreen.WeylZeroCountLog.errLow c W⌋₊ with hm
    have hmle : (m : ℝ) ≤ A - Cvs.Prolate.LiouvilleGreen.WeylZeroCountLog.errLow c W := Nat.floor_le hneg
    have hmlt : A - Cvs.Prolate.LiouvilleGreen.WeylZeroCountLog.errLow c W < m + 1 := Nat.lt_floor_add_one _
    have hz := Cvs.Prolate.LiouvilleGreen.WeylZeroCountLog.zero_count_ge hc1 hv.1 hvW hW1 ha0 ha1 (m := m) hmle
    have := Cvs.Prolate.SturmOscillationAtPoint.le_ncard_nodeSpec (sqC c) (a := a) (by linarith) ha1 m _ hz
    have : (m : ℝ) ≤ n₀ := by exact_mod_cast this
    linarith
  have hn₀n' : (n₀ : ℝ) ≤ n := by exact_mod_cast hn₀n
  have hnn₀' : (n : ℝ) ≤ n₀ + 1 := by exact_mod_cast hnn₀
  have hlog' : 12 + 2 * log W + 4 * log c ≤ ε * c / log c := by
    have e : ε / 2 * c / log c = ε * c / log c / 2 := by ring
    rw [e] at hlog; linarith
  rw [abs_le]
  constructor <;> linarith

/-- **The discrete potential** `PotFloor` (eq-cpb Lemmas 10, 11, Proposition 3 and §4). -/
theorem potFloor : Cvs.Prolate.Gram.DeepCellFloorAmplitude.PotFloor := Cvs.Prolate.Gram.PotentialFloorFromCounts.potFloor_of_counts Cvs.Prolate.RungWeylCount.rungCount dirCount

/-- **The deep cell floor** `DeepCellFloor`. -/
theorem deepCellFloor : Cvs.Prolate.Gram.DeepRemainderCellFloors.DeepCellFloor := Cvs.Prolate.Gram.EndpointAmplitudeFloor.deepCellFloor_of_potFloor potFloor

end Cvs.Prolate.Gram.DirichletNodeCountPotFloor

end
