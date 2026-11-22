import Mathlib
import Cvs.Prolate.Gram.PotentialFloorFromCounts
import Cvs.Prolate.Gram.ProlateCellGramHalfUnit
import Cvs.Prolate.Gram.RobinNodeLatticeDualFloor
import Cvs.Prolate.Gram.WeylCountsDiscretePotential
import Cvs.Prolate.LiouvilleGreen.WeylZeroCountLog
import Cvs.Prolate.RegularSolutionEdge
import Cvs.Prolate.RungWeylCount
import Cvs.Prolate.TopRungZeroSplitHalf
import Cvs.Prolate.TunnellingIntegralMargin

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The rungs above a level: `W(T) ≥ (1 − T)/2`, `1 − rungWeyl(1 − δ) ≤ δ(1 + ½ log(2/δ))` and the top count

At most `x(1 − rungWeyl u) + (errLow(c, 1) + 1)/2` rungs have `T_j > u`, from the lower Weyl zero count of Cvs.Prolate.LiouvilleGreen.WeylZeroCountLog.
-/

noncomputable section

open Real Set Filter Finset MeasureTheory
open Cvs.Prolate.RegularSolutionEdge (regSol sqC)
open Cvs.Prolate.TopRungZeroSplitHalf (ZerosOn)

namespace Cvs.Prolate.RungsAboveLevelCount
open Cvs.ZeroCounting

/-! ### The plunge exponent near `T = 1` -/

/-- **The plunge exponent is at least `(1 − T)/2`** on `[0, 1]`: `√(sin²φ − T) ≥ √((1 − T)/2)` on the last
`√((1 − T)/2)` of `[arcsin √T, π/2]`. -/
theorem half_one_sub_le_tunW {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T ≤ 1) : (1 - T) / 2 ≤ Cvs.Prolate.TunnellingIntegralMargin.tunW T := by
  set a := √((1 - T) / 2) with ha
  have ha0 : 0 ≤ a := sqrt_nonneg _
  have ha2 : a ^ 2 = (1 - T) / 2 := sq_sqrt (by linarith)
  have hpi := pi_gt_three
  have ha1 : a ≤ 1 := by nlinarith
  have hsT : √T ≤ 1 := by rw [← sqrt_one]; exact sqrt_le_sqrt hT1
  have hsT0 : 0 ≤ √T := sqrt_nonneg _
  have hsT2 : √T ^ 2 = T := sq_sqrt hT0
  -- the subinterval lies in the forbidden region
  have hlo : arcsin √T ≤ π / 2 - a := by
    rw [arcsin_le_iff_le_sin ⟨by linarith, hsT⟩ ⟨by linarith, by linarith⟩, sin_pi_div_two_sub]
    have hc := one_sub_sq_div_two_le_cos (x := a)
    nlinarith
  have hnn : ∀ φ, 0 ≤ Cvs.Prolate.TunnellingIntegralMargin.tunF T φ := fun φ => sqrt_nonneg _
  have h1 : (∫ φ in π / 2 - a..π / 2, Cvs.Prolate.TunnellingIntegralMargin.tunF T φ) ≤ ∫ φ in arcsin √T..π / 2, Cvs.Prolate.TunnellingIntegralMargin.tunF T φ :=
    intervalIntegral.integral_mono_interval hlo (by linarith) le_rfl (Eventually.of_forall hnn)
      ((Cvs.Prolate.TunnellingIntegralMargin.continuous_tunF _).intervalIntegrable _ _)
  have h2 : (∫ φ in π / 2 - a..π / 2, a) ≤ ∫ φ in π / 2 - a..π / 2, Cvs.Prolate.TunnellingIntegralMargin.tunF T φ := by
    refine intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const
      ((Cvs.Prolate.TunnellingIntegralMargin.continuous_tunF _).intervalIntegrable _ _) fun φ hφ => ?_
    have hs : sin φ = cos (π / 2 - φ) := by rw [cos_pi_div_two_sub]
    have hc := one_sub_sq_div_two_le_cos (x := π / 2 - φ)
    have hd0 : 0 ≤ π / 2 - φ := by linarith [hφ.2]
    have hd1 : π / 2 - φ ≤ a := by linarith [hφ.1]
    have hdd : (π / 2 - φ) ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ hd0 hd1 2
    have hs1 : 1 - a ^ 2 / 2 ≤ sin φ := by rw [hs]; linarith
    have hsq : (1 - a ^ 2 / 2) ^ 2 ≤ sin φ ^ 2 := pow_le_pow_left₀ (by nlinarith) hs1 2
    unfold Cvs.Prolate.TunnellingIntegralMargin.tunF
    rw [ha]
    exact sqrt_le_sqrt (by nlinarith)
  rw [intervalIntegral.integral_const, smul_eq_mul] at h2
  unfold Cvs.Prolate.TunnellingIntegralMargin.tunW
  nlinarith

/-! ### The Weyl integral near `u = 1` -/

/-- `1/(1 − t²)` is interval integrable on `[0, b]` for `b < 1`. -/
theorem intervalIntegrable_inv_one_sub_sq {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1) :
    IntervalIntegrable (fun t : ℝ => 1 / (1 - t ^ 2)) volume 0 b := by
  have hc : ContinuousOn (fun t : ℝ => 1 - t ^ 2) (uIcc 0 b) := by fun_prop
  refine ContinuousOn.intervalIntegrable (ContinuousOn.div₀ (f := fun _ : ℝ => (1 : ℝ)) (g := fun t : ℝ => 1 - t ^ 2)
    continuousOn_const hc fun t ht => ?_)
  rw [uIcc_of_le hb0] at ht
  exact (Cvs.Prolate.LiouvilleGreen.WeylZeroCountLog.one_sub_sq_pos ht.1 (ht.2.trans_lt hb1)).ne'

/-- The rung Weyl integrand is interval integrable on `[0, 1]`. -/
theorem intervalIntegrable_rungWeyl (u : ℝ) :
    IntervalIntegrable (fun t : ℝ => √((min u 1 - t ^ 2) / (1 - t ^ 2))) volume 0 1 := by
  refine (intervalIntegrable_const (c := (1 : ℝ))).mono_fun' (Measurable.aestronglyMeasurable (by measurability)) ?_
  refine (ae_restrict_iff' measurableSet_uIoc).mpr (Eventually.of_forall fun t ht => ?_)
  rw [uIoc_of_le zero_le_one] at ht
  show ‖√((min u 1 - t ^ 2) / (1 - t ^ 2))‖ ≤ 1
  rw [Real.norm_eq_abs, abs_of_nonneg (sqrt_nonneg _), sqrt_le_one]
  rcases eq_or_lt_of_le ht.2 with h | h
  · rw [h]; simp
  · have hp : 0 < 1 - t ^ 2 := Cvs.Prolate.LiouvilleGreen.WeylZeroCountLog.one_sub_sq_pos ht.1.le h
    rw [div_le_one hp]; linarith [min_le_right u 1]

/-- **The Weyl integral just below the top**: `1 − rungWeyl(1 − δ) ≤ δ(1 + ½ log(2/δ))` for `0 < δ ≤ 1`. -/
theorem one_sub_rungWeyl_le {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    1 - Cvs.Prolate.Gram.WeylCountsDiscretePotential.rungWeyl (1 - δ) ≤ δ * (1 + log (2 / δ) / 2) := by
  have hmin : min (1 - δ) 1 = 1 - δ := min_eq_left (by linarith)
  have hb0 : 0 ≤ 1 - δ := by linarith
  have hb1 : 1 - δ < 1 := by linarith
  have hI := intervalIntegrable_inv_one_sub_sq hb0 hb1
  have hlog := Cvs.Prolate.LiouvilleGreen.WeylZeroCountLog.integral_inv_p_le le_rfl hb0 le_rfl hδ0
  -- restrict to `[0, 1 − δ]`
  have h1 : (∫ t in (0 : ℝ)..1 - δ, √((min (1 - δ) 1 - t ^ 2) / (1 - t ^ 2))) ≤ Cvs.Prolate.Gram.WeylCountsDiscretePotential.rungWeyl (1 - δ) :=
    intervalIntegral.integral_mono_interval le_rfl hb0 (by linarith)
      (Eventually.of_forall fun t => sqrt_nonneg _) (intervalIntegrable_rungWeyl _)
  -- the pointwise bound `√a ≥ a` with `a = 1 − δ/(1 − t²)`
  have h2 : (∫ t in (0 : ℝ)..1 - δ, (1 - δ * (1 / (1 - t ^ 2))))
      ≤ ∫ t in (0 : ℝ)..1 - δ, √((min (1 - δ) 1 - t ^ 2) / (1 - t ^ 2)) := by
    refine intervalIntegral.integral_mono_on hb0 (intervalIntegrable_const.sub (hI.const_mul δ))
      ((intervalIntegrable_rungWeyl _).mono_set (by
        rw [Set.uIcc_of_le hb0, Set.uIcc_of_le zero_le_one]; exact Icc_subset_Icc le_rfl hb1.le)) fun t ht => ?_
    have hp : 0 < 1 - t ^ 2 := Cvs.Prolate.LiouvilleGreen.WeylZeroCountLog.one_sub_sq_pos ht.1 (ht.2.trans_lt hb1)
    have he : (min (1 - δ) 1 - t ^ 2) / (1 - t ^ 2) = 1 - δ * (1 / (1 - t ^ 2)) := by
      rw [hmin]; field_simp; ring
    rw [he]
    set a := 1 - δ * (1 / (1 - t ^ 2))
    by_cases ha : a ≤ 0
    · exact ha.trans (sqrt_nonneg _)
    · push Not at ha
      have ha1 : a ≤ 1 := by
        have : 0 ≤ δ * (1 / (1 - t ^ 2)) := by positivity
        linarith
      rw [le_sqrt ha.le ha.le]; nlinarith
  rw [intervalIntegral.integral_sub intervalIntegrable_const (hI.const_mul δ), intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul, smul_eq_mul, mul_one, sub_zero] at h2
  have := mul_le_mul_of_nonneg_left hlog hδ0.le
  nlinarith

/-! ### The rungs above a level -/

/-- **The lower rung count** at a level `u ∈ [0, 1]`: `x·rungWeyl u − (errLow(c, 1) + 1)/2 ≤ #{T_j ≤ u}`. -/
theorem rungWeyl_sub_le_card {x : ℕ} (hx : 80 ≤ 2 * π * x) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    (x : ℝ) * Cvs.Prolate.Gram.WeylCountsDiscretePotential.rungWeyl u - (Cvs.Prolate.LiouvilleGreen.WeylZeroCountLog.errLow (2 * π * x) 1 + 1) / 2
      ≤ (univ.filter fun j : Fin x => Cvs.Prolate.Gram.ProlateCellGramHalfUnit.levT x j ≤ u).card := by
  set c := 2 * π * (x : ℝ) with hc
  have hc1 : 1 ≤ c := by linarith
  have hπ : 0 < π := pi_pos
  set R := (univ.filter fun j : Fin x => Cvs.Prolate.Gram.ProlateCellGramHalfUnit.levT x j ≤ u).card with hR
  have hR' : R = (univ.filter fun j : Fin x => Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.chi x j ≤ c ^ 2 * u).card := by
    rw [hR]; congr 1
    refine Finset.filter_congr fun j _ => ?_
    rw [Cvs.Prolate.Gram.PotentialFloorFromCounts.chi_eq, ← hc]
    exact (mul_le_mul_iff_of_pos_left (by positivity)).symm
  set A := c / π * Cvs.Prolate.LiouvilleGreen.WeylZeroCountLog.weylI 0 u with hA
  have hAx : A = 2 * x * Cvs.Prolate.Gram.WeylCountsDiscretePotential.rungWeyl u := by
    rw [hA, Cvs.Prolate.RungWeylCount.weylI_eq_rungWeyl hu.2, hc]; field_simp
  have hlow0 : 0 ≤ Cvs.Prolate.LiouvilleGreen.WeylZeroCountLog.errLow c 1 := by
    unfold Cvs.Prolate.LiouvilleGreen.WeylZeroCountLog.errLow
    have : 0 ≤ log (8 * c ^ 2 * 1) := log_nonneg (by nlinarith)
    have : 0 ≤ log (c ^ 2 * 1) := log_nonneg (by nlinarith)
    positivity
  by_cases hneg : A - Cvs.Prolate.LiouvilleGreen.WeylZeroCountLog.errLow c 1 < 0
  · have : (x : ℝ) * Cvs.Prolate.Gram.WeylCountsDiscretePotential.rungWeyl u ≤ Cvs.Prolate.LiouvilleGreen.WeylZeroCountLog.errLow c 1 / 2 := by linarith
    have : (0 : ℝ) ≤ R := Nat.cast_nonneg _
    linarith
  push Not at hneg
  set m := ⌊A - Cvs.Prolate.LiouvilleGreen.WeylZeroCountLog.errLow c 1⌋₊ with hm
  have hmle : (m : ℝ) ≤ A - Cvs.Prolate.LiouvilleGreen.WeylZeroCountLog.errLow c 1 := Nat.floor_le hneg
  have hmlt : A - Cvs.Prolate.LiouvilleGreen.WeylZeroCountLog.errLow c 1 < m + 1 := Nat.lt_floor_add_one _
  have hz := Cvs.Prolate.LiouvilleGreen.WeylZeroCountLog.zero_count_ge (V := 1) hc1 hu.1 hu.2 le_rfl le_rfl one_pos (m := m) hmle
  have hcard := Cvs.Prolate.RungWeylCount.le_card_of_hasZeros (x := x) hz
  rw [← hR'] at hcard
  have hW1 := Cvs.Prolate.RungWeylCount.rungWeyl_le_one u
  rcases min_choice x ((m + 1) / 2) with h | h
  · rw [h] at hcard
    have : (x : ℝ) ≤ R := by exact_mod_cast hcard
    have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg x
    nlinarith
  · rw [h] at hcard
    have h2 : (m : ℝ) ≤ 2 * (((m + 1) / 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : m ≤ 2 * ((m + 1) / 2))
    have : (((m + 1) / 2 : ℕ) : ℝ) ≤ R := by exact_mod_cast hcard
    linarith

/-- **The rungs above a level**: `#{T_j > u} ≤ x(1 − rungWeyl u) + (errLow(c, 1) + 1)/2` for `u ∈ [0, 1]`. -/
theorem card_lt_levT_le {x : ℕ} (hx : 80 ≤ 2 * π * x) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    ((univ.filter fun j : Fin x => u < Cvs.Prolate.Gram.ProlateCellGramHalfUnit.levT x j).card : ℝ)
      ≤ x * (1 - Cvs.Prolate.Gram.WeylCountsDiscretePotential.rungWeyl u) + (Cvs.Prolate.LiouvilleGreen.WeylZeroCountLog.errLow (2 * π * x) 1 + 1) / 2 := by
  have hsplit := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin x)))
    (fun j : Fin x => Cvs.Prolate.Gram.ProlateCellGramHalfUnit.levT x j ≤ u)
  simp only [not_le, Finset.card_univ, Fintype.card_fin] at hsplit
  have hlo := rungWeyl_sub_le_card hx hu
  have : ((univ.filter fun j : Fin x => Cvs.Prolate.Gram.ProlateCellGramHalfUnit.levT x j ≤ u).card : ℝ)
      + (univ.filter fun j : Fin x => u < Cvs.Prolate.Gram.ProlateCellGramHalfUnit.levT x j).card = x := by exact_mod_cast hsplit
  linarith

/-- **The rungs within `δ` of the top**: `#{T_j > 1 − δ} ≤ xδ(1 + ½ log(2/δ)) + (errLow(c, 1) + 1)/2`. -/
theorem card_top_le {x : ℕ} (hx : 80 ≤ 2 * π * x) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    ((univ.filter fun j : Fin x => 1 - δ < Cvs.Prolate.Gram.ProlateCellGramHalfUnit.levT x j).card : ℝ)
      ≤ x * δ * (1 + log (2 / δ) / 2) + (Cvs.Prolate.LiouvilleGreen.WeylZeroCountLog.errLow (2 * π * x) 1 + 1) / 2 := by
  have h := card_lt_levT_le hx (u := 1 - δ) ⟨by linarith, by linarith⟩
  have hW := one_sub_rungWeyl_le hδ0 hδ1
  have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg x
  nlinarith [mul_le_mul_of_nonneg_left hW hx0]

end Cvs.Prolate.RungsAboveLevelCount

end
