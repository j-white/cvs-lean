import Mathlib
import Cvs.Prolate.EdgeCentreSign
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.RegularSolutionEdge
import Cvs.Prolate.RegularSolutionEnergyComparability
import Cvs.Prolate.TopRungDepthBound
import Cvs.Prolate.TopRungZeroSplitHalf

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Zeros in the turning layer, at the edge and in the forbidden region

Between two zeros of the regular solution, `(∫ dt/p)(∫|q|) ≥ 2` (Lyapunov), so where `p|q| ≤ 1` consecutive zeros are
`√2` apart in `∫ dt/p`; near `t = 1` with `|q| ≤ Q₀`, `Q₀η ≤ ¼`, the solution stays positive on `[1 − η, 1]`; and it
has no zero on the forbidden `[τ, 1]`.
-/

noncomputable section

open Real Set Filter Topology MeasureTheory
open Cvs.Prolate.RegularSolutionEdge (regSol regU regV sqC)
open Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval (pP)
open Cvs.Prolate.TopRungZeroSplitHalf (ZerosOn)

namespace Cvs.Prolate.LiouvilleGreen.TurningLayerZeros
open Cvs.ZeroCounting

variable {c χ : ℝ}

theorem hasDerivAt_y {t : ℝ} (ht : -1 < t) :
    HasDerivAt (regSol (sqC c) χ) (regV (sqC c) χ t) t := Cvs.Prolate.RegularSolutionEdge.hasDerivAt_regSol _ _ ht

theorem hasDerivAt_U {t : ℝ} (ht : -1 < t) :
    HasDerivAt (regU (sqC c) χ) ((χ - c ^ 2 * t ^ 2) * regSol (sqC c) χ t) t := by
  refine (Cvs.Prolate.RegularSolutionEdge.hasDerivAt_regU _ _ ht).congr_deriv ?_
  rw [Cvs.Prolate.TopRungDepthBound.sqC_apply]; ring

theorem regV_eq {t : ℝ} (ht : -1 < t) (ht1 : t < 1) :
    regV (sqC c) χ t = -(regU (sqC c) χ t / (1 - t ^ 2)) := by
  have h := Cvs.Prolate.RegularSolutionEdge.pP_mul_regV (sqC c) χ ht
  unfold pP at h
  have hp : (1 : ℝ) - t ^ 2 ≠ 0 := by nlinarith
  field_simp
  linarith

theorem continuousOn_regV {u v : ℝ} (hu : -1 < u) (hv : v < 1) : ContinuousOn (regV (sqC c) χ) (Icc u v) := by
  intro t ht
  have ht1 : -1 < t := by linarith [ht.1]
  have ht2 : t < 1 := by linarith [ht.2]
  have hp : (1 : ℝ) - t ^ 2 ≠ 0 := by nlinarith
  have hc : ContinuousAt (fun s => -(regU (sqC c) χ s / (1 - s ^ 2))) t :=
    ((hasDerivAt_U ht1).continuousAt.div (by fun_prop) hp).neg
  refine (hc.congr_of_eventuallyEq ?_).continuousWithinAt
  filter_upwards [Ioo_mem_nhds ht1 ht2] with s hs using regV_eq hs.1 hs.2

/-! ### Lyapunov's inequality -/

/-- `|∫_ν^t f| ≤ ∫_{t₁}^{t₂} |f|` for `ν, t ∈ [t₁, t₂]`. -/
theorem abs_integral_le_of_mem {f : ℝ → ℝ} {t₁ t₂ ν t : ℝ} (h12 : t₁ ≤ t₂) (hf : IntervalIntegrable f volume t₁ t₂)
    (hν : ν ∈ Icc t₁ t₂) (ht : t ∈ Icc t₁ t₂) : |∫ s in ν..t, f s| ≤ ∫ s in t₁..t₂, |f s| := by
  rw [← Real.norm_eq_abs, intervalIntegral.norm_integral_eq_norm_integral_uIoc]
  refine (norm_integral_le_integral_norm _).trans ?_
  rw [intervalIntegral.integral_of_le h12]
  refine setIntegral_mono_set ((intervalIntegrable_iff_integrableOn_Ioc_of_le h12).mp hf).norm
    (Eventually.of_forall fun s => norm_nonneg _) (Eventually.of_forall fun s (hs : s ∈ uIoc ν t) => ?_)
  rw [mem_uIoc] at hs
  show s ∈ Ioc t₁ t₂
  rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨hν.1.trans_lt h1, h2.trans ht.2⟩
  · exact ⟨ht.1.trans_lt h1, h2.trans hν.2⟩

private theorem continuousOn_inv_p {S : Set ℝ} (h : ∀ s ∈ S, 1 - s ^ 2 ≠ 0) :
    ContinuousOn (fun s : ℝ => 1 / (1 - s ^ 2)) S := by
  have hc : Continuous fun s : ℝ => 1 - s ^ 2 := by fun_prop
  exact ContinuousOn.div₀ (f := fun _ => (1 : ℝ)) (g := fun s => 1 - s ^ 2) continuousOn_const hc.continuousOn h

/-- **Lyapunov**: between zeros `t₁ < t₂` in `[0, 1)` of the regular solution, `2 ≤ (∫ dt/p)(∫ |q|)`. -/
theorem lyapunov {t₁ t₂ : ℝ} (h0 : 0 ≤ t₁) (h12 : t₁ < t₂) (h2 : t₂ < 1) (hz1 : regSol (sqC c) χ t₁ = 0)
    (hz2 : regSol (sqC c) χ t₂ = 0) :
    2 ≤ (∫ t in t₁..t₂, 1 / (1 - t ^ 2)) * ∫ t in t₁..t₂, |χ - c ^ 2 * t ^ 2| := by
  have hI : ∀ t ∈ Icc t₁ t₂, -1 < t ∧ t < 1 := fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hyc : ContinuousOn (regSol (sqC c) χ) (Icc t₁ t₂) := Cvs.Prolate.EdgeCentreSign.continuousOn_regSol_Icc _ _ (by linarith)
  obtain ⟨m, hm, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr h12.le) (hyc.norm)
  set M := ‖regSol (sqC c) χ m‖ with hM
  have hMb : ∀ t ∈ Icc t₁ t₂, |regSol (sqC c) χ t| ≤ M := fun t ht => hmax ht
  -- `M > 0`
  have hM0 : 0 < M := by
    by_contra hle
    push Not at hle
    have hy0 : ∀ t ∈ Icc t₁ t₂, regSol (sqC c) χ t = 0 := fun t ht => abs_nonpos_iff.mp ((hMb t ht).trans hle)
    have hU1 : regU (sqC c) χ t₁ ≠ 0 := Cvs.Prolate.EdgeCentreSign.regU_ne_zero_of_regSol_eq_zero _ _ (by linarith) (by linarith) hz1
    have hUz : ∀ t ∈ Ioo t₁ t₂, regU (sqC c) χ t = 0 := by
      intro t ht
      have hd : HasDerivAt (regSol (sqC c) χ) 0 t := by
        refine (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq ?_
        filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs using hy0 s ⟨hs.1.le, hs.2.le⟩
      have := (hasDerivAt_y (c := c) (χ := χ) (hI t ⟨ht.1.le, ht.2.le⟩).1).unique hd
      have hV := Cvs.Prolate.RegularSolutionEdge.pP_mul_regV (sqC c) χ (hI t ⟨ht.1.le, ht.2.le⟩).1
      rw [this, mul_zero] at hV; exact hV.symm
    have hlim : Tendsto (regU (sqC c) χ) (𝓝[>] t₁) (𝓝 (regU (sqC c) χ t₁)) :=
      ((hasDerivAt_U (by linarith : (-1 : ℝ) < t₁)).continuousAt.tendsto).mono_left nhdsWithin_le_nhds
    have hlim0 : Tendsto (regU (sqC c) χ) (𝓝[>] t₁) (𝓝 0) := tendsto_const_nhds.congr' (by
      filter_upwards [Ioo_mem_nhdsGT h12] with s hs using (hUz s hs).symm)
    exact hU1 (tendsto_nhds_unique hlim hlim0)
  -- a critical point
  obtain ⟨ν, hν, hνd⟩ := exists_hasDerivAt_eq_zero h12 hyc (by rw [hz1, hz2])
    (fun t ht => hasDerivAt_y (hI t ⟨ht.1.le, ht.2.le⟩).1)
  have hUν : regU (sqC c) χ ν = 0 := by
    have hV := Cvs.Prolate.RegularSolutionEdge.pP_mul_regV (sqC c) χ (hI ν ⟨hν.1.le, hν.2.le⟩).1
    rw [hνd, mul_zero] at hV; exact hV.symm
  set Q := ∫ t in t₁..t₂, |χ - c ^ 2 * t ^ 2| with hQ
  -- the flux bound
  have hUb : ∀ t ∈ Icc t₁ t₂, |regU (sqC c) χ t| ≤ M * Q := fun t ht => by
    have hsub : uIcc ν t ⊆ Icc t₁ t₂ := uIcc_subset_Icc ⟨hν.1.le, hν.2.le⟩ ht
    have hqq : Continuous fun s : ℝ => χ - c ^ 2 * s ^ 2 := by fun_prop
    have hfi : IntervalIntegrable (fun s => (χ - c ^ 2 * s ^ 2) * regSol (sqC c) χ s) volume ν t :=
      (hqq.continuousOn.mul (hyc.mono hsub)).intervalIntegrable
    have hft := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s hs => hasDerivAt_U (hI s (hsub hs)).1) hfi
    rw [hUν, sub_zero] at hft
    rw [← hft]
    have hfi' : IntervalIntegrable (fun s => (χ - c ^ 2 * s ^ 2) * regSol (sqC c) χ s) volume t₁ t₂ :=
      (hqq.continuousOn.mul hyc).intervalIntegrable_of_Icc h12.le
    refine (abs_integral_le_of_mem h12.le hfi' ⟨hν.1.le, hν.2.le⟩ ht).trans ?_
    rw [hQ, ← intervalIntegral.integral_const_mul]
    have hqc : Continuous fun s : ℝ => |χ - c ^ 2 * s ^ 2| := by fun_prop
    refine intervalIntegral.integral_mono_on h12.le hfi'.abs
      ((hqc.intervalIntegrable t₁ t₂).const_mul M) fun s hs => ?_
    rw [abs_mul, mul_comm M]
    exact mul_le_mul_of_nonneg_left (hMb s hs) (abs_nonneg _)
  -- the two halves
  have hP : ∀ u v : ℝ, t₁ ≤ u → u ≤ v → v ≤ t₂ → |regSol (sqC c) χ v - regSol (sqC c) χ u| ≤
      M * Q * ∫ s in u..v, 1 / (1 - s ^ 2) := fun u v hu huv hv => by
    have hsub : Icc u v ⊆ Icc t₁ t₂ := Icc_subset_Icc hu hv
    have hVc := continuousOn_regV (c := c) (χ := χ) (u := u) (v := v) (by linarith) (by linarith)
    have hft := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s hs => hasDerivAt_y (c := c) (χ := χ) (hI s (hsub (by rwa [uIcc_of_le huv] at hs))).1)
      (hVc.intervalIntegrable_of_Icc huv)
    rw [← hft, ← intervalIntegral.integral_const_mul]
    refine (intervalIntegral.abs_integral_le_integral_abs huv).trans
      (intervalIntegral.integral_mono_on huv (hVc.intervalIntegrable_of_Icc huv).abs ?_ fun s hs => ?_)
    · refine ContinuousOn.intervalIntegrable_of_Icc huv (continuousOn_const.mul (continuousOn_inv_p fun s hs => ?_))
      have := hI s (hsub hs); nlinarith
    · have hs' := hI s (hsub hs)
      have hp : 0 < 1 - s ^ 2 := by nlinarith
      rw [regV_eq hs'.1 hs'.2, abs_neg, abs_div, abs_of_pos hp, mul_one_div]
      exact div_le_div_of_nonneg_right (hUb s (hsub hs)) hp.le
  have hA := hP t₁ m le_rfl hm.1 hm.2
  have hB := hP m t₂ hm.1 hm.2 le_rfl
  rw [hz1, sub_zero, ← Real.norm_eq_abs, ← hM] at hA
  rw [hz2, zero_sub, abs_neg, ← Real.norm_eq_abs, ← hM] at hB
  have hpi : ∀ u v : ℝ, t₁ ≤ u → u ≤ v → v ≤ t₂ →
      IntervalIntegrable (fun s => 1 / (1 - s ^ 2)) volume u v := fun u v hu huv hv =>
    ContinuousOn.intervalIntegrable_of_Icc huv (continuousOn_inv_p fun s hs => by
      have := hI s ⟨hu.trans hs.1, hs.2.trans hv⟩; nlinarith)
  rw [← intervalIntegral.integral_add_adjacent_intervals (hpi t₁ m le_rfl hm.1 hm.2) (hpi m t₂ hm.1 hm.2 le_rfl)]
  have hsum : 2 * M ≤ M * (Q * ((∫ s in t₁..m, 1 / (1 - s ^ 2)) + ∫ s in m..t₂, 1 / (1 - s ^ 2))) := by
    nlinarith
  have := le_of_mul_le_mul_left (by linarith : M * 2 ≤ M * (Q * ((∫ s in t₁..m, 1 / (1 - s ^ 2)) +
    ∫ s in m..t₂, 1 / (1 - s ^ 2)))) hM0
  linarith

/-- **Zeros in a layer are spread**: where `p|q| ≤ 1`, two zeros `t₁ < t₂` in `[0, 1)` have `∫_{t₁}^{t₂} dt/p ≥ √2`. -/
theorem sqrt_two_le_of_layer {t₁ t₂ : ℝ} (h0 : 0 ≤ t₁) (h12 : t₁ < t₂) (h2 : t₂ < 1)
    (hz1 : regSol (sqC c) χ t₁ = 0) (hz2 : regSol (sqC c) χ t₂ = 0)
    (hlay : ∀ t ∈ Icc t₁ t₂, (1 - t ^ 2) * |χ - c ^ 2 * t ^ 2| ≤ 1) :
    √2 ≤ ∫ t in t₁..t₂, 1 / (1 - t ^ 2) := by
  have hL := lyapunov h0 h12 h2 hz1 hz2
  have hpi : IntervalIntegrable (fun s => 1 / (1 - s ^ 2)) volume t₁ t₂ :=
    ContinuousOn.intervalIntegrable_of_Icc h12.le (continuousOn_inv_p fun s hs => by
      nlinarith [hs.1, hs.2])
  have hqc : Continuous fun s : ℝ => |χ - c ^ 2 * s ^ 2| := by fun_prop
  have hQP : ∫ t in t₁..t₂, |χ - c ^ 2 * t ^ 2| ≤ ∫ t in t₁..t₂, 1 / (1 - t ^ 2) :=
    intervalIntegral.integral_mono_on h12.le (hqc.intervalIntegrable _ _) hpi fun t ht => by
      have hp : 0 < 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
      rw [le_div_iff₀ hp, mul_comm]; exact hlay t ht
  have hP0 : 0 ≤ ∫ t in t₁..t₂, 1 / (1 - t ^ 2) :=
    intervalIntegral.integral_nonneg h12.le fun t ht => by
      have hp : 0 < 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
      positivity
  have hsq : 2 ≤ (∫ t in t₁..t₂, 1 / (1 - t ^ 2)) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hQP hP0]
  rw [Real.sqrt_le_left hP0]; exact hsq

/-- **The layer count**: `k + 1` zeros in `[β, γ] ⊆ [0, 1)` where `p|q| ≤ 1` give `k√2 ≤ ∫_β^γ dt/p`. -/
theorem layer_count {β γ : ℝ} (hβ : 0 ≤ β) (hγ : γ < 1)
    (hlay : ∀ t ∈ Icc β γ, (1 - t ^ 2) * |χ - c ^ 2 * t ^ 2| ≤ 1) {k : ℕ}
    (hz : ZerosOn (regSol (sqC c) χ) (Icc β γ) (k + 1)) : k * √2 ≤ ∫ t in β..γ, 1 / (1 - t ^ 2) := by
  obtain ⟨w, hw, hwI, hw0⟩ := hz
  have hpi : ∀ u v : ℝ, β ≤ u → u ≤ v → v ≤ γ → IntervalIntegrable (fun s => 1 / (1 - s ^ 2)) volume u v :=
    fun u v hu huv hv => ContinuousOn.intervalIntegrable_of_Icc huv (continuousOn_inv_p fun s hs => by nlinarith [hs.1, hs.2, hu, hv])
  have hnn : ∀ u v : ℝ, β ≤ u → u ≤ v → v ≤ γ → 0 ≤ ∫ s in u..v, 1 / (1 - s ^ 2) := fun u v hu huv hv =>
    intervalIntegral.integral_nonneg huv fun s hs => by
      have hp : 0 < 1 - s ^ 2 := by nlinarith [hs.1, hs.2, hu, hv]
      positivity
  have key : ∀ n (hn : n < k + 1), n * √2 ≤ ∫ s in w ⟨0, by omega⟩..w ⟨n, hn⟩, 1 / (1 - s ^ 2) := by
    intro n
    induction n with
    | zero => intro hn; simp
    | succ n ih =>
      intro hn
      have h1 := ih (by omega)
      have hlt : w ⟨n, by omega⟩ < w ⟨n + 1, hn⟩ := hw (by simp [Fin.lt_def])
      have hA := hwI ⟨n, by omega⟩
      have hB := hwI ⟨n + 1, hn⟩
      have h0 := hwI ⟨0, by omega⟩
      have h0n : w ⟨0, by omega⟩ ≤ w ⟨n, by omega⟩ := hw.monotone (Fin.mk_le_mk.mpr (Nat.zero_le n))
      have h2 := sqrt_two_le_of_layer (hβ.trans hA.1) hlt (hB.2.trans_lt hγ) (hw0 _) (hw0 _)
        (fun t ht => hlay t ⟨hA.1.trans ht.1, ht.2.trans hB.2⟩)
      rw [← intervalIntegral.integral_add_adjacent_intervals (hpi _ _ h0.1 h0n hA.2) (hpi _ _ hA.1 hlt.le hB.2)]
      push_cast; linarith
  have hk := key k (Nat.lt_succ_self k)
  have h0 := hwI ⟨0, by omega⟩
  have hkI := hwI ⟨k, Nat.lt_succ_self k⟩
  have h0k : w ⟨0, by omega⟩ ≤ w ⟨k, Nat.lt_succ_self k⟩ := hw.monotone (Fin.mk_le_mk.mpr (Nat.zero_le k))
  have : ∫ s in w ⟨0, by omega⟩..w ⟨k, Nat.lt_succ_self k⟩, 1 / (1 - s ^ 2) ≤ ∫ s in β..γ, 1 / (1 - s ^ 2) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hpi β _ le_rfl h0.1 (h0.2)) (hpi _ γ h0.1
      (h0.2) le_rfl), ← intervalIntegral.integral_add_adjacent_intervals (hpi _ _ h0.1 h0k hkI.2)
      (hpi _ γ hkI.1 hkI.2 le_rfl)]
    linarith [hnn β _ le_rfl h0.1 h0.2, hnn _ γ hkI.1 hkI.2 le_rfl]
  linarith

/-! ### The edge and the forbidden region -/

/-- **No zero at the edge**: if `|q| ≤ Q₀` on `[1 − η, 1]`, `0 ≤ η ≤ 1`, `Q₀η ≤ ¼`, the regular solution is positive
there. -/
theorem regSol_pos_near_one {η Q₀ : ℝ} (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (hQ : ∀ t ∈ Icc (1 - η) 1, |χ - c ^ 2 * t ^ 2| ≤ Q₀) (hQη : Q₀ * η ≤ 1 / 4) :
    ∀ t ∈ Icc (1 - η) 1, 0 < regSol (sqC c) χ t := by
  have hI : ∀ t ∈ Icc (1 - η) 1, -1 < t := fun t ht => by linarith [ht.1]
  have hQ0 : 0 ≤ Q₀ := (abs_nonneg _).trans (hQ 1 ⟨by linarith, le_rfl⟩)
  have hyc : ContinuousOn (regSol (sqC c) χ) (Icc (1 - η) 1) := Cvs.Prolate.EdgeCentreSign.continuousOn_regSol_Icc _ _ (by linarith)
  obtain ⟨m, hm, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr (by linarith : 1 - η ≤ 1)) hyc.norm
  set M := ‖regSol (sqC c) χ m‖ with hM
  have hMb : ∀ t ∈ Icc (1 - η) 1, |regSol (sqC c) χ t| ≤ M := fun t ht => hmax ht
  have hM1 : 1 ≤ M := by
    have := hMb 1 ⟨by linarith, le_rfl⟩; rwa [Cvs.Prolate.RegularSolutionEdge.regSol_one, abs_one] at this
  -- the flux and the slope
  have hUb : ∀ t ∈ Icc (1 - η) 1, |regU (sqC c) χ t| ≤ Q₀ * M * (1 - t) := fun t ht => by
    have hsub : uIcc t 1 ⊆ Icc (1 - η) 1 := by rw [uIcc_of_le ht.2]; exact Icc_subset_Icc ht.1 le_rfl
    have hqq : Continuous fun s : ℝ => χ - c ^ 2 * s ^ 2 := by fun_prop
    have hfi : IntervalIntegrable (fun s => (χ - c ^ 2 * s ^ 2) * regSol (sqC c) χ s) volume t 1 :=
      (hqq.continuousOn.mul (hyc.mono hsub)).intervalIntegrable
    have hft := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s hs => hasDerivAt_U (hI s (hsub hs))) hfi
    have hU1 : regU (sqC c) χ 1 = 0 := by simp [regU]
    rw [hU1, zero_sub] at hft
    rw [← abs_neg, ← hft]
    refine (intervalIntegral.abs_integral_le_integral_abs ht.2).trans ?_
    calc ∫ s in t..1, |(χ - c ^ 2 * s ^ 2) * regSol (sqC c) χ s| ≤ ∫ s in t..1, Q₀ * M :=
          intervalIntegral.integral_mono_on ht.2 hfi.abs intervalIntegrable_const fun s hs => by
            rw [abs_mul]
            exact mul_le_mul (hQ s (hsub (by rwa [uIcc_of_le ht.2]))) (hMb s (hsub (by rwa [uIcc_of_le ht.2])))
              (abs_nonneg _) hQ0
      _ = Q₀ * M * (1 - t) := by rw [intervalIntegral.integral_const, smul_eq_mul]; ring
  have hVb : ∀ t ∈ Icc (1 - η) 1, |regV (sqC c) χ t| ≤ Q₀ * M := fun t ht => by
    rcases eq_or_lt_of_le ht.2 with h1 | h1
    · rw [h1, Cvs.Prolate.RegularSolutionEdge.regV_one, Cvs.Prolate.TopRungDepthBound.sqC_apply, one_pow, mul_one, abs_div, abs_two]
      have := hQ 1 ⟨by linarith, le_rfl⟩
      rw [one_pow, mul_one, abs_sub_comm] at this
      rw [abs_neg]
      have := mul_le_mul_of_nonneg_left hM1 hQ0
      linarith [abs_nonneg (c ^ 2 - χ)]
    · have ht0 : 0 ≤ t := by linarith [ht.1]
      rw [regV_eq (hI t ht) h1, abs_neg, abs_div, abs_of_pos (by nlinarith : (0 : ℝ) < 1 - t ^ 2),
        div_le_iff₀ (by nlinarith : (0 : ℝ) < 1 - t ^ 2)]
      have := hUb t ht
      have h2 : Q₀ * M * (1 - t) ≤ Q₀ * M * (1 - t ^ 2) :=
        mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
      linarith
  have hdev : ∀ t ∈ Icc (1 - η) 1, |regSol (sqC c) χ t - 1| ≤ Q₀ * M * η := fun t ht => by
    have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := regSol (sqC c) χ)
      (f' := regV (sqC c) χ) (s := Icc (1 - η) 1) (C := Q₀ * M)
      (fun x hx => (hasDerivAt_y (hI x hx)).hasDerivWithinAt) (fun x hx => by
        rw [Real.norm_eq_abs]; exact hVb x hx) (convex_Icc _ _) ht ⟨by linarith, le_rfl⟩
    rw [Cvs.Prolate.RegularSolutionEdge.regSol_one, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (show (0 : ℝ) ≤ 1 - t by linarith [ht.2]), abs_sub_comm] at h
    calc |regSol (sqC c) χ t - 1| ≤ Q₀ * M * (1 - t) := h
      _ ≤ Q₀ * M * η := mul_le_mul_of_nonneg_left (by linarith [ht.1]) (by positivity)
  have hMle : M ≤ 4 / 3 := by
    have h := hdev m hm
    have h1 : M ≤ 1 + Q₀ * M * η := by
      have e : M = |regSol (sqC c) χ m| := by rw [hM, Real.norm_eq_abs]
      have := abs_sub_abs_le_abs_sub (regSol (sqC c) χ m) 1; rw [abs_one] at this
      linarith
    nlinarith
  intro t ht
  have h := hdev t ht
  have : Q₀ * M * η ≤ 1 / 3 := by nlinarith
  rw [abs_le] at h
  linarith [h.1]

/-- **No zero in the forbidden region**: on `[τ, 1]` with `0 ≤ τ`, `χ ≤ c²τ²`, the regular solution has `y² ≥ 1`. -/
theorem regSol_ne_zero_forbidden {τ : ℝ} (hτ : 0 ≤ τ) (hτχ : χ ≤ c ^ 2 * τ ^ 2) :
    ∀ t ∈ Icc τ 1, regSol (sqC c) χ t ≠ 0 := fun t ht h => by
  have hτ1 : τ ≤ 1 := ht.1.trans ht.2
  have := Cvs.Prolate.RegularSolutionEnergyComparability.sq_anti_forbidden (c := c) (σ := χ) hτ hτχ ht ⟨hτ1, le_rfl⟩ ht.2
  simp [h, Cvs.Prolate.RegularSolutionEdge.regSol_one] at this
  linarith

end Cvs.Prolate.LiouvilleGreen.TurningLayerZeros

end
