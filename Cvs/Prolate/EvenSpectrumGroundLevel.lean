import Mathlib
import Cvs.Prolate.EdgeCentreSign
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.RegularSolutionEdge
import Cvs.Prolate.SlepianEvenOrdering

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The ground level of the even spectrum of `c²s²`

The flux ratio `r = regU / regSol` obeys `r' = (χ − Q) − pP (regV / regSol)² ≥ χ − c²ξ²` on `[0, 1]`,
so a level with `regSol > 0` on `[0, 1]` has `χ − c²/3 ≤ −r(0)`. Below every even level `r(0) > 0`; hence
the even spectrum is nonempty, its infimum `groundLevel c` is its least point, and `groundLevel c ≤ c²/3`.
-/

noncomputable section

open Real Set Filter Topology Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.Prolate.RegularSolutionEdge Cvs.Prolate.EdgeCentreSign Cvs.Prolate.SlepianEvenOrdering

namespace Cvs.Prolate.EvenSpectrumGroundLevel

/-! ### The Riccati inequality -/

/-- **The Riccati equation for the flux ratio**: `(regU / regSol)' = (χ − Q) − pP (regV / regSol)²`. -/
theorem hasDerivAt_fluxRatio (Q : C(ℝ, ℝ)) (χ : ℝ) {ξ : ℝ} (hξ : -1 < ξ) (hy : regSol Q χ ξ ≠ 0) :
    HasDerivAt (fun t => regU Q χ t / regSol Q χ t)
      ((χ - Q ξ) - pP ξ * (regV Q χ ξ / regSol Q χ ξ) ^ 2) ξ := by
  refine ((hasDerivAt_regU Q χ hξ).div (hasDerivAt_regSol Q χ hξ) hy).congr_deriv ?_
  rw [← pP_mul_regV Q χ hξ]
  field_simp
  ring

/-- **The Riccati bound with test function `1`**: where `regSol > 0` on `[0, 1]`, `χ − c²/3 ≤ −r(0)`. -/
theorem sub_third_le_neg_ratio (c χ : ℝ) (hpos : ∀ ξ ∈ Icc (0:ℝ) 1, 0 < regSol (sqC c) χ ξ) :
    χ - c ^ 2 / 3 ≤ -(regU (sqC c) χ 0 / regSol (sqC c) χ 0) := by
  set F : ℝ → ℝ := fun t => regU (sqC c) χ t / regSol (sqC c) χ t - (χ * t - c ^ 2 * t ^ 3 / 3) with hF
  have hd : ∀ ξ ∈ Icc (0:ℝ) 1,
      HasDerivAt F (-(pP ξ * (regV (sqC c) χ ξ / regSol (sqC c) χ ξ) ^ 2)) ξ := by
    intro ξ hξ
    have h1 := hasDerivAt_fluxRatio (sqC c) χ (by linarith [hξ.1] : (-1:ℝ) < ξ) (hpos ξ hξ).ne'
    have h2 : HasDerivAt (fun t : ℝ => χ * t - c ^ 2 * t ^ 3 / 3) (χ * 1 - c ^ 2 * (3 * ξ ^ 2) / 3) ξ := by
      have := ((hasDerivAt_id' ξ).const_mul χ).sub (((hasDerivAt_pow 3 ξ).const_mul (c ^ 2)).div_const 3)
      exact this.congr_deriv (by push_cast; ring)
    refine (h1.sub h2).congr_deriv ?_
    simp only [sqC, ContinuousMap.coe_mk]
    ring
  have hmono : MonotoneOn F (Icc 0 1) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg
      (f' := fun ξ => -(pP ξ * (regV (sqC c) χ ξ / regSol (sqC c) χ ξ) ^ 2)) (convex_Icc 0 1)
      (fun ξ hξ => (hd ξ hξ).continuousAt.continuousWithinAt) (fun ξ hξ => ?_) (fun ξ hξ => ?_)
    · rw [interior_Icc] at hξ
      exact (hd ξ (Ioo_subset_Icc_self hξ)).hasDerivWithinAt
    · rw [interior_Icc] at hξ
      have hp : pP ξ ≤ 0 := by unfold pP; nlinarith [hξ.1, hξ.2]
      have := sq_nonneg (regV (sqC c) χ ξ / regSol (sqC c) χ ξ)
      nlinarith
  have hmon := hmono ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ zero_le_one
  have hU1 : regU (sqC c) χ 1 = 0 := (regSol_system (sqC c) χ).2.2.1
  simp only [hF, regSol_one, hU1] at hmon
  norm_num at hmon
  linarith

/-- A level with `regSol > 0` on `[0, 1]` and positive centre flux lies strictly below `c²/3`. -/
theorem lt_third_of_pos {c χ : ℝ} (hpos : ∀ ξ ∈ Icc (0:ℝ) 1, 0 < regSol (sqC c) χ ξ)
    (hU : 0 < regU (sqC c) χ 0) : χ < c ^ 2 / 3 := by
  have h := sub_third_le_neg_ratio c χ hpos
  have hr : 0 < regU (sqC c) χ 0 / regSol (sqC c) χ 0 := div_pos hU (hpos 0 ⟨le_rfl, zero_le_one⟩)
  linarith

/-! ### Below the even spectrum -/

/-- **Below every even level the centre flux is positive.** -/
theorem regU_zero_pos_of_lt (Q : C(ℝ, ℝ)) {χ : ℝ} (hχ : ∀ χ' ∈ evenSpec Q, χ < χ') :
    0 < regU Q χ 0 := by
  obtain ⟨m, hm⟩ := exists_lt_potential Q
  set χ₁ := min χ (m - 1) with hχ₁
  have h1 : χ₁ ≤ χ := min_le_left _ _
  have hpos₁ : 0 < regU Q χ₁ 0 :=
    regU_pos_of_lt Q (by norm_num) (by norm_num)
      (fun s hs => hm _ (lt_of_le_of_lt (min_le_right _ _) (by linarith)) s hs)
  by_contra hle
  push Not at hle
  have hivt := intermediate_value_Icc' h1 (continuous_regU_zero Q).continuousOn
  obtain ⟨t, ht, ht0⟩ := hivt ⟨hle, hpos₁.le⟩
  have := hχ t ht0
  linarith [ht.2]

/-- **The even spectrum of `c²s²` is nonempty.** -/
theorem evenSpec_nonempty (c : ℝ) : (evenSpec (sqC c)).Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  have hpos := regSol_pos_of_le_evenSpec (sqC c) (χ := c ^ 2 / 3) (by simp [h])
  have hU := regU_zero_pos_of_lt (sqC c) (χ := c ^ 2 / 3) (by simp [h])
  exact lt_irrefl _ (lt_third_of_pos hpos hU)

/-! ### The ground level -/

/-- The even spectrum of `c²s²` is bounded below by `0`. -/
theorem bddBelow_evenSpec (c : ℝ) : BddBelow (evenSpec (sqC c)) :=
  ⟨0, fun _ h => nonneg_of_mem_evenSpec c h⟩

/-- The ground level: the least point of the even spectrum of `c²s²`. -/
def groundLevel (c : ℝ) : ℝ := sInf (evenSpec (sqC c))

/-- **The ground level is an even level.** -/
theorem groundLevel_mem (c : ℝ) : groundLevel c ∈ evenSpec (sqC c) :=
  (isClosed_evenSpec _).csInf_mem (evenSpec_nonempty c) (bddBelow_evenSpec c)

/-- The ground level lies at or below every even level. -/
theorem groundLevel_le_of_mem {c χ : ℝ} (h : χ ∈ evenSpec (sqC c)) : groundLevel c ≤ χ :=
  csInf_le (bddBelow_evenSpec c) h

/-- **No even level lies below the ground level.** -/
theorem ncard_groundLevel (c : ℝ) : (evenSpec (sqC c) ∩ Iio (groundLevel c)).ncard = 0 := by
  have h : evenSpec (sqC c) ∩ Iio (groundLevel c) = ∅ := by
    ext χ
    simp only [mem_inter_iff, mem_Iio, mem_empty_iff_false, iff_false, not_and, not_lt]
    exact fun h => groundLevel_le_of_mem h
  rw [h, Set.ncard_empty]

/-- **The ground level is at most `c²/3`.** -/
theorem groundLevel_le (c : ℝ) : groundLevel c ≤ c ^ 2 / 3 := by
  have hpos := regSol_pos_of_le_evenSpec (sqC c) (fun χ' h => groundLevel_le_of_mem (c := c) h)
  have h := sub_third_le_neg_ratio c _ hpos
  have hU : regU (sqC c) (groundLevel c) 0 = 0 := groundLevel_mem c
  rw [hU, zero_div, neg_zero] at h
  linarith

/-- **The ground level is deep**: `5c ≤ c² − groundLevel c` once `15/2 ≤ c`. -/
theorem five_mul_le_sub_groundLevel {c : ℝ} (hc : 15 / 2 ≤ c) : 5 * c ≤ c ^ 2 - groundLevel c := by
  have := groundLevel_le c
  nlinarith

end Cvs.Prolate.EvenSpectrumGroundLevel
