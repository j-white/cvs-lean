import Mathlib
import Cvs.Finite.ModePairingTable
import Cvs.Finite.ShiftedModePairingTable
import Cvs.WeilForm.Archimedean.ArchDirichletEnergyPosition
import Cvs.Zeta.WeilPositivityStatement

/-!
# The windowed mode sum's deficit, priced against the circle's

    g 0 − g v  =  the circle's deficit  +  ∫ over the last `v` of the window

so the window's deficit exceeds the circle's by a term of size `v·‖M‖∞²` and no more.
-/

set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Real Filter Cvs.Zeta.Explicit.Weil

namespace Cvs.Finite.ModeSumDeficit

/-- **The windowed self-convolution is an integral over the overlap.** -/
theorem selfConvolution_indicator_eq {L v : ℝ} (hv0 : 0 ≤ v) (hvL : v ≤ L) (f : ℝ → ℝ) :
    selfConvolution (Set.indicator (Set.Ioc (0:ℝ) L) f) v
      = ∫ s in (0:ℝ)..(L - v), f s * f (s + v) := by
  have hfun : (fun s : ℝ => Set.indicator (Set.Ioc (0:ℝ) L) f s
      * Set.indicator (Set.Ioc (0:ℝ) L) f (s + v))
      = Set.indicator (Set.Ioc (0:ℝ) (L - v)) (fun s => f s * f (s + v)) := by
    funext s
    by_cases h : s ∈ Set.Ioc (0:ℝ) (L - v)
    · obtain ⟨ha, hb⟩ := h
      rw [Set.indicator_of_mem (Set.mem_Ioc.mpr ⟨ha, by linarith⟩),
        Set.indicator_of_mem (Set.mem_Ioc.mpr ⟨by linarith, by linarith⟩),
        Set.indicator_of_mem (Set.mem_Ioc.mpr ⟨ha, hb⟩)]
    · rw [Set.indicator_of_notMem h]
      rw [Set.mem_Ioc, not_and_or, not_lt, not_le] at h
      rcases h with hc | hc
      · rw [Set.indicator_of_notMem (fun (hmem : s ∈ Set.Ioc (0:ℝ) L) => absurd hmem.1 (not_lt.mpr hc))]
        ring
      · refine mul_eq_zero.mpr (Or.inr ?_)
        refine Set.indicator_of_notMem (fun (hmem : s + v ∈ Set.Ioc (0:ℝ) L) => ?_) f
        exact absurd hmem.2 (not_le.mpr (by linarith))
  unfold selfConvolution
  rw [hfun, integral_indicator measurableSet_Ioc,
    intervalIntegral.integral_of_le (by linarith : (0:ℝ) ≤ L - v)]

/-- **The mode sum is bounded by its coefficient mass.** -/
theorem abs_modeSum_le (L : ℝ) (s : Finset ℕ) (a : ℕ → ℝ) (x : ℝ) :
    |Cvs.WeilForm.Archimedean.ArchDirichletEnergyPosition.modeSum L s a x| ≤ ∑ n ∈ s, |a n| := by
  show |∑ n ∈ s, a n * Real.cos (2 * π * n / L * x)| ≤ _
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun n _ => ?_)
  rw [abs_mul]
  have := Real.abs_cos_le_one (2 * π * n / L * x)
  nlinarith [abs_nonneg (a n), abs_nonneg (Real.cos (2 * π * n / L * x))]

/-- **The window's deficit, split into the circle's and a boundary term.** -/
theorem deficit_split {L v : ℝ} (hL : 0 < L) (hv0 : 0 ≤ v) (hvL : v ≤ L)
    (s : Finset ℕ) (a : ℕ → ℝ) :
    selfConvolution (Set.indicator (Set.Ioc (0:ℝ) L) (Cvs.WeilForm.Archimedean.ArchDirichletEnergyPosition.modeSum L s a)) 0
        - selfConvolution
            (Set.indicator (Set.Ioc (0:ℝ) L) (Cvs.WeilForm.Archimedean.ArchDirichletEnergyPosition.modeSum L s a)) v
      = L / 2 * ∑ n ∈ s, (if n = 0 then 2 else 1) * a n ^ 2
            * (1 - Real.cos (2 * π * n / L * v))
        + ∫ s' in (L - v)..L, Cvs.WeilForm.Archimedean.ArchDirichletEnergyPosition.modeSum L s a s'
            * Cvs.WeilForm.Archimedean.ArchDirichletEnergyPosition.modeSum L s a (s' + v) := by
  classical
  set M : ℝ → ℝ := Cvs.WeilForm.Archimedean.ArchDirichletEnergyPosition.modeSum L s a with hM
  have hMc : Continuous M := by
    rw [hM]
    show Continuous fun x : ℝ => ∑ n ∈ s, a n * Real.cos (2 * π * n / L * x)
    exact continuous_finsetSum _ (fun n _ => by fun_prop)
  have h0 : selfConvolution (Set.indicator (Set.Ioc (0:ℝ) L) M) 0
      = ∫ x in (0:ℝ)..L, M x ^ 2 := by
    rw [selfConvolution_indicator_eq le_rfl (by linarith) M, sub_zero]
    exact intervalIntegral.integral_congr (fun x _ => by simp [sq])
  have hv : selfConvolution (Set.indicator (Set.Ioc (0:ℝ) L) M) v
      = ∫ x in (0:ℝ)..(L - v), M x * M (x + v) :=
    selfConvolution_indicator_eq hv0 hvL M
  have hsplit : (∫ x in (0:ℝ)..L, M x * M (x + v))
      = (∫ x in (0:ℝ)..(L - v), M x * M (x + v))
        + ∫ x in (L - v)..L, M x * M (x + v) := by
    refine (intervalIntegral.integral_add_adjacent_intervals ?_ ?_).symm
    · apply Continuous.intervalIntegrable
      exact hMc.mul (hMc.comp (continuous_id.add continuous_const))
    · apply Continuous.intervalIntegrable
      exact hMc.mul (hMc.comp (continuous_id.add continuous_const))
  rw [h0, hv, Cvs.Finite.ModePairingTable.integral_modeSum_sq hL s a]
  have hcirc := Cvs.Finite.ShiftedModePairingTable.integral_modeSum_shift hL s a v
  rw [← hM] at hcirc
  rw [Finset.mul_sum, Finset.mul_sum]
  have hrw : (∫ x in (0:ℝ)..(L - v), M x * M (x + v))
      = (∫ x in (0:ℝ)..L, M x * M (x + v)) - ∫ x in (L - v)..L, M x * M (x + v) := by
    rw [hsplit]; ring
  rw [hrw, hcirc, Finset.mul_sum]
  have hAB : (∑ i ∈ s, L / 2 * ((if i = 0 then 2 else 1) * a i ^ 2))
      - (∑ i ∈ s, L / 2 * ((if i = 0 then 2 else 1) * a i ^ 2
          * Real.cos (2 * π * i / L * v)))
      = ∑ i ∈ s, L / 2 * ((if i = 0 then 2 else 1) * a i ^ 2
          * (1 - Real.cos (2 * π * i / L * v))) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun n _ => by ring
  linarith [hAB]

/-- **The cosine's deficit is quadratic.** -/
theorem one_sub_cos_le (θ : ℝ) : 1 - Real.cos θ ≤ θ ^ 2 / 2 := by
  have hd : Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ 2 := by
    have h2 := Real.cos_two_mul (θ / 2)
    have hs := Real.sin_sq_add_cos_sq (θ / 2)
    rw [show 2 * (θ / 2) = θ by ring] at h2
    nlinarith [h2, hs]
  have habs : |Real.sin (θ / 2)| ≤ |θ / 2| := Real.abs_sin_le_abs
  have hsq : Real.sin (θ / 2) ^ 2 ≤ (θ / 2) ^ 2 := by
    nlinarith [habs, abs_nonneg (Real.sin (θ / 2)), abs_nonneg (θ / 2),
      sq_abs (Real.sin (θ / 2)), sq_abs (θ / 2)]
  rw [hd]
  nlinarith [hsq]

/-- **The windowed mode sum's deficit is quadratic in the displacement, up to a boundary
term linear in it.** -/
theorem deficit_le {L v : ℝ} (hL : 0 < L) (hv0 : 0 ≤ v) (hvL : v ≤ L)
    (s : Finset ℕ) (a : ℕ → ℝ) :
    selfConvolution (Set.indicator (Set.Ioc (0:ℝ) L) (Cvs.WeilForm.Archimedean.ArchDirichletEnergyPosition.modeSum L s a)) 0
        - selfConvolution
            (Set.indicator (Set.Ioc (0:ℝ) L) (Cvs.WeilForm.Archimedean.ArchDirichletEnergyPosition.modeSum L s a)) v
      ≤ v ^ 2 / 2 * (L / 2 * ∑ n ∈ s, (if n = 0 then 2 else 1)
            * (2 * π * n / L) ^ 2 * a n ^ 2)
        + v * (∑ n ∈ s, |a n|) ^ 2 := by
  classical
  set M : ℝ → ℝ := Cvs.WeilForm.Archimedean.ArchDirichletEnergyPosition.modeSum L s a with hM
  set B : ℝ := ∑ n ∈ s, |a n| with hB
  have hBnn : 0 ≤ B := Finset.sum_nonneg fun n _ => abs_nonneg _
  rw [deficit_split hL hv0 hvL s a]
  -- the circle term
  have hcirc : L / 2 * ∑ n ∈ s, (if n = 0 then 2 else 1) * a n ^ 2
        * (1 - Real.cos (2 * π * n / L * v))
      ≤ v ^ 2 / 2 * (L / 2 * ∑ n ∈ s, (if n = 0 then 2 else 1)
          * (2 * π * n / L) ^ 2 * a n ^ 2) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun n _ => ?_
    have hw : (0:ℝ) ≤ (if n = 0 then 2 else 1) := by
      by_cases h : n = 0 <;> simp [h]
    have hq := one_sub_cos_le (2 * π * n / L * v)
    have hLh : (0:ℝ) ≤ L / 2 := by linarith
    have hstep : L / 2 * ((if n = 0 then 2 else 1) * a n ^ 2
          * (1 - Real.cos (2 * π * n / L * v)))
        ≤ L / 2 * ((if n = 0 then 2 else 1) * a n ^ 2
          * ((2 * π * n / L * v) ^ 2 / 2)) := by
      refine mul_le_mul_of_nonneg_left ?_ hLh
      refine mul_le_mul_of_nonneg_left hq ?_
      exact mul_nonneg hw (sq_nonneg _)
    refine le_trans hstep (le_of_eq ?_)
    ring
  -- the boundary term
  have hMc : Continuous M := by
    rw [hM]
    show Continuous fun x : ℝ => ∑ n ∈ s, a n * Real.cos (2 * π * n / L * x)
    exact continuous_finsetSum _ (fun n _ => by fun_prop)
  have hbd : (∫ s' in (L - v)..L, M s' * M (s' + v)) ≤ v * B ^ 2 := by
    have hle : ∀ x ∈ Set.uIoc (L - v) L, ‖M x * M (x + v)‖ ≤ B ^ 2 := by
      intro x _
      rw [Real.norm_eq_abs, abs_mul]
      have h1 := abs_modeSum_le L s a x
      have h2 := abs_modeSum_le L s a (x + v)
      rw [← hM] at h1 h2
      nlinarith [h1, h2, abs_nonneg (M x), abs_nonneg (M (x + v)), hBnn]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hle
    have habs : |L - (L - v)| = v := by
      rw [show L - (L - v) = v by ring, abs_of_nonneg hv0]
    rw [habs] at h
    calc (∫ s' in (L - v)..L, M s' * M (s' + v))
        ≤ |∫ s' in (L - v)..L, M s' * M (s' + v)| := le_abs_self _
      _ ≤ B ^ 2 * v := by rwa [Real.norm_eq_abs] at h
      _ = v * B ^ 2 := by ring
  linarith [hcirc, hbd]

end Cvs.Finite.ModeSumDeficit
