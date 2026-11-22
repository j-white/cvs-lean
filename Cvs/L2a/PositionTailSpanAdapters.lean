import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.PositionTruncatedTail
import Cvs.L2a.RungSpanFromLowMass
import Cvs.Prolate.Gram.RungGramFloorAtInfinity
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.SlepianCommutingRelation
import Cvs.WeilForm.PrimePowerIndexed

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Adapters for the position-truncated tail on the rung span

The tail of Cvs.L2a.PositionTruncatedTail is linear in `Φ`; two truncations differ by the modes `Φ(mθ)` on `(max(1, k/m), X/m]`; and
`∫_{(1,∞)} F_X w = Σ_m m⁻¹ ∫_m^X Φ(ξ) w(ξ/m)`. A combination of rungs is `C¹` (Cvs.L2a.RungSpanFromLowMass), every prime power `k ≤ X`
lies in `primePowIndex ⌊X⌋ ⌊X⌋` (Cvs.WeilForm.PrimePowerIndexed), `rungU` (Cvs.Prolate.Gram.RungGramFloorAtInfinity) vanishes at `1`, and a mass floor on `[1, X]` bounds the
window masses on `[3/2, 2]`.
-/

namespace Cvs.L2a.PositionTailSpanAdapters

open Real Set Finset MeasureTheory intervalIntegral Cvs.L2a.PositionTruncatedTail

/-- The position-truncated tail of a finite linear combination is the combination of the tails. -/
theorem posTail_sum {ι : Type*} (s : Finset ι) (a : ι → ℝ) (ψ : ι → ℝ → ℝ) (X θ : ℝ) :
    posTail (fun ξ => ∑ i ∈ s, a i * ψ i ξ) X θ = ∑ i ∈ s, a i * posTail (ψ i) X θ := by
  simp_rw [posTail_eq_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  by_cases h : θ ∈ Ioc 1 (X / m)
  · simp only [indicator_of_mem h]
  · simp only [indicator_of_notMem h, mul_zero, Finset.sum_const_zero]

/-- For `1 ≤ k ≤ X`, the difference of the truncations at `X` and at `k` is the mode sum over `m ≤ ⌊X⌋` of
`Φ(mθ)` restricted to `(max(1, k/m), X/m]`. -/
theorem posTail_sub_posTail (Φ : ℝ → ℝ) {k X : ℝ} (hk : 1 ≤ k) (hkX : k ≤ X) (θ : ℝ) :
    posTail Φ X θ - posTail Φ k θ
      = ∑ m ∈ Finset.Icc 1 ⌊X⌋₊, (Ioc (max 1 (k / m)) (X / m)).indicator (fun θ => Φ (m * θ)) θ := by
  have hext : posTail Φ k θ = ∑ m ∈ Finset.Icc 1 ⌊X⌋₊, (Ioc 1 (k / m)).indicator (fun θ => Φ (m * θ)) θ := by
    rw [posTail_eq_sum]
    refine Finset.sum_subset (Finset.Icc_subset_Icc le_rfl (Nat.floor_mono hkX)) fun m hm hmk => ?_
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    have hlt : k < (m : ℝ) := by
      refine (Nat.floor_lt (by linarith)).mp ?_
      by_contra h
      exact hmk (Finset.mem_Icc.mpr ⟨hm1, not_lt.mp h⟩)
    have hmpos : (0 : ℝ) < m := by linarith
    refine indicator_of_notMem (fun h' => ?_) _
    have h1 : k / m < 1 := (div_lt_one hmpos).mpr hlt
    linarith [h'.1, h'.2]
  rw [hext, posTail_eq_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
  have hkm : k / m ≤ X / m := div_le_div_of_nonneg_right hkX (by linarith)
  simp only [indicator_apply, Set.mem_Ioc, max_lt_iff]
  rcases lt_or_ge (k / m) θ with h2 | h2
  · by_cases h1 : 1 < θ <;> by_cases h3 : θ ≤ X / m <;> simp [h1, h2, h3, not_le.mpr h2]
  · by_cases h1 : 1 < θ <;> simp [h1, h2, not_lt.mpr h2, h2.trans hkm]

/-- For `1 ≤ X` and `ψ`, `w` continuous on `[1, X]`, `∫_{(1,∞)} F_X(θ) w(θ) = Σ_{m ≤ ⌊X⌋} m⁻¹ ∫_m^X ψ(ξ) w(ξ/m)`. -/
theorem integral_posTail_mul {ψ w : ℝ → ℝ} {X : ℝ} (hX : 1 ≤ X) (hψ : ContinuousOn ψ (Icc 1 X))
    (hw : ContinuousOn w (Icc 1 X)) :
    ∫ θ in Ioi 1, posTail ψ X θ * w θ
      = ∑ m ∈ Finset.Icc 1 ⌊X⌋₊, (m : ℝ)⁻¹ * ∫ ξ in (m : ℝ)..X, ψ ξ * w (ξ / m) := by
  have hpt : (fun θ => posTail ψ X θ * w θ)
      = fun θ => ∑ m ∈ Finset.Icc 1 ⌊X⌋₊, Set.indicator (Ioc 1 (X / m)) (fun θ => ψ (m * θ) * w θ) θ := by
    funext θ
    rw [posTail_eq_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    by_cases h : θ ∈ Ioc 1 (X / m)
    · rw [indicator_of_mem h, indicator_of_mem h]
    · rw [indicator_of_notMem h, indicator_of_notMem h, zero_mul]
  have hmap : ∀ m ∈ Finset.Icc 1 ⌊X⌋₊, ∀ θ ∈ Icc 1 (X / m), (m : ℝ) * θ ∈ Icc 1 X ∧ θ ∈ Icc 1 X := by
    intro m hm θ hθ
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
    have h := (le_div_iff₀ (by linarith : (0 : ℝ) < m)).mp hθ.2
    refine ⟨⟨by nlinarith [hθ.1], by linarith⟩, ⟨hθ.1, ?_⟩⟩
    nlinarith [hθ.1]
  have hc : ∀ m ∈ Finset.Icc 1 ⌊X⌋₊, ContinuousOn (fun θ => ψ (m * θ) * w θ) (Icc 1 (X / m)) := fun m hm =>
    ContinuousOn.mul (hψ.comp (continuousOn_const.mul continuousOn_id) fun θ hθ => (hmap m hm θ hθ).1)
      (hw.mono fun θ hθ => (hmap m hm θ hθ).2)
  have hint : ∀ m ∈ Finset.Icc 1 ⌊X⌋₊,
      Integrable (Set.indicator (Ioc 1 (X / m)) (fun θ => ψ (m * θ) * w θ)) := fun m hm =>
    (integrable_indicator_iff measurableSet_Ioc).mpr ((hc m hm).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
  rw [hpt, integral_finsetSum _ fun m hm => (hint m hm).integrableOn]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm' := Finset.mem_Icc.mp hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm'.1
  have hmpos : (0 : ℝ) < m := by linarith
  have hle : (1 : ℝ) ≤ X / m := by
    have : (m : ℝ) ≤ X := le_trans (by exact_mod_cast hm'.2) (Nat.floor_le (by linarith))
    rw [le_div_iff₀ hmpos]; linarith
  rw [setIntegral_indicator measurableSet_Ioc, Set.inter_eq_right.mpr Set.Ioc_subset_Ioi_self,
    ← intervalIntegral.integral_of_le hle]
  have hcv := intervalIntegral.integral_comp_mul_left (fun ξ => ψ ξ * w (ξ / m)) hmpos.ne' (a := 1) (b := X / m)
  simp only [mul_one, mul_div_cancel₀ X hmpos.ne', smul_eq_mul] at hcv
  rw [← hcv]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  simp only [mul_div_cancel_left₀ θ hmpos.ne']

/-- A finite combination of prolate rungs is `C¹` on `[1, X]`. -/
theorem contDiffOn_span {ι : Type*} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0) (X : ℝ) :
    ContDiffOn ℝ 1 (fun ξ => ∑ i, a i * Cvs.L2a.AngularProlateTailPositive.psi c (g i) ξ) (Icc 1 X) :=
  (ContDiff.sum fun i _ =>
    contDiff_const.mul (Cvs.L2a.RungSpanFromLowMass.contDiff_psi (hg i) (hg₁ i) (hg₂c i) (hang i))).contDiffOn

/-- Every prime power `k ≤ X` lies in `primePowIndex ⌊X⌋ ⌊X⌋`. -/
theorem mem_primePowIndex_floor {k : ℕ} {X : ℝ} (hk : IsPrimePow k) (hkX : (k : ℝ) ≤ X) :
    k ∈ Cvs.WeilForm.PrimePowerIndexed.primePowIndex ⌊X⌋₊ ⌊X⌋₊ := by
  obtain ⟨p, r, hp, hr, rfl⟩ := (isPrimePow_nat_iff k).mp hk
  have hkF : p ^ r ≤ ⌊X⌋₊ := Nat.le_floor hkX
  have hp1 : 1 ≤ p := hp.one_lt.le
  have hpk : p ≤ p ^ r := Nat.le_self_pow hr.ne' p
  have hrk : r ≤ p ^ r := (Nat.lt_pow_self hp.one_lt).le
  refine Finset.mem_image.mpr ⟨(p, r), Finset.mem_product.mpr ⟨?_, ?_⟩, rfl⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp⟩
  · exact Finset.mem_Icc.mpr ⟨hr, by omega⟩

/-- The rung's second component vanishes at `ξ = 1`. -/
theorem rungU_one (c : ℝ) (g : ℝ → ℝ) : Cvs.Prolate.Gram.RungGramFloorAtInfinity.rungU c g 1 = 0 := by
  unfold Cvs.Prolate.Gram.RungGramFloorAtInfinity.rungU Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval.pP; norm_num

/-- For `X ≥ 2` and `κ > 0`, a mass floor `κ Σ a_i² ∫₁^X ψ_i² ≤ N` bounds the window masses:
`Σ a_i² ∫_{3/2}^2 ψ_i² ≤ κ⁻¹ N`. -/
theorem FR_of_FF {ι : Type*} [Fintype ι] {a : ι → ℝ} {ψ : ι → ℝ → ℝ} {X κF N : ℝ} (hX : 2 ≤ X)
    (hψ : ∀ i, ContinuousOn (ψ i) (Icc 1 X)) (hκ : 0 < κF)
    (hFF : κF * ∑ i, a i ^ 2 * ∫ ξ in (1 : ℝ)..X, ψ i ξ ^ 2 ≤ N) :
    ∑ i, a i ^ 2 * ∫ ξ in (3 / 2 : ℝ)..2, ψ i ξ ^ 2 ≤ κF⁻¹ * N := by
  have hwin : ∑ i, a i ^ 2 * ∫ ξ in (3 / 2 : ℝ)..2, ψ i ξ ^ 2 ≤ ∑ i, a i ^ 2 * ∫ ξ in (1 : ℝ)..X, ψ i ξ ^ 2 := by
    refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    have hi : IntervalIntegrable (fun ξ => ψ i ξ ^ 2) volume 1 X :=
      ((hψ i).pow 2).intervalIntegrable_of_Icc (by linarith)
    exact intervalIntegral.integral_mono_interval (by norm_num) (by norm_num) hX
      (Filter.Eventually.of_forall fun ξ => sq_nonneg _) hi
  calc _ ≤ ∑ i, a i ^ 2 * ∫ ξ in (1 : ℝ)..X, ψ i ξ ^ 2 := hwin
    _ = κF⁻¹ * (κF * ∑ i, a i ^ 2 * ∫ ξ in (1 : ℝ)..X, ψ i ξ ^ 2) := by field_simp
    _ ≤ κF⁻¹ * N := mul_le_mul_of_nonneg_left hFF (inv_nonneg.mpr hκ.le)

end Cvs.L2a.PositionTailSpanAdapters
