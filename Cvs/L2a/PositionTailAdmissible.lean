import Mathlib
import Cvs.L2a.PositionTruncatedTail
import Cvs.L2a.TailLogScaleTest
import Cvs.Upstream.LevyConditionL1Modulus
import Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The position-truncated tail is an admissible Weil test function

A finite sum of cut functions `1_{(0, B_i]} h_i` with `h_i` `C¹` on `[0, B_i]` lies in `L¹ ∩ L²`, has integrable
shifted products and satisfies the Lévy condition; for `Φ` `C¹` on `[1, X]` this applies to `logScale (posTail Φ X)`.
-/

namespace Cvs.L2a.PositionTailAdmissible

open Real Set MeasureTheory Cvs.L2a.TailLogScaleTest Cvs.L2a.PositionTruncatedTail

/-- One cut function `1_{(0,B]} h` with `h` `C¹` on `[0, B]` is in `L²`, bounded, and has a linear `L¹` modulus. -/
theorem cut_piece {h : ℝ → ℝ} {B : ℝ} (hB : 0 ≤ B) (hC : ContDiffOn ℝ 1 h (Icc 0 B)) :
    ∃ H L : ℝ, MemLp (indicator (Ioc 0 B) h) 2 volume ∧ (∀ s, |indicator (Ioc 0 B) h s| ≤ H)
      ∧ ∀ v, 0 ≤ v → Integrable (fun s => indicator (Ioc 0 B) h s - indicator (Ioc 0 B) h (s + v)) volume
        ∧ ∫ s, |indicator (Ioc 0 B) h s - indicator (Ioc 0 B) h (s + v)| ≤ L * v := by
  have hcont : ContinuousOn h (Icc 0 B) := hC.continuousOn
  obtain ⟨K, hK⟩ := hC.exists_lipschitzOnWith one_ne_zero (convex_Icc _ _) isCompact_Icc
  obtain ⟨H, hH⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  have hIoc : Ioc 0 B ⊆ Icc 0 B := Ioc_subset_Icc_self
  have hint : IntegrableOn h (Ioc 0 B) volume := (hcont.integrableOn_Icc).mono_set hIoc
  have hH0 : 0 ≤ max H 0 := le_max_right _ _
  have hfb : ∀ s, |indicator (Ioc 0 B) h s| ≤ max H 0 := by
    intro s
    by_cases hs : s ∈ Ioc 0 B
    · rw [indicator_of_mem hs, ← Real.norm_eq_abs]; exact (hH s (hIoc hs)).trans (le_max_left _ _)
    · rw [indicator_of_notMem hs, abs_zero]; exact hH0
  have h2 : MemLp (indicator (Ioc 0 B) h) 2 volume := by
    rw [memLp_indicator_iff_restrict measurableSet_Ioc.nullMeasurableSet]
    have : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) B)) :=
      isFiniteMeasure_restrict.mpr measure_Ioc_lt_top.ne
    refine MemLp.of_bound ((hcont.mono hIoc).aestronglyMeasurable measurableSet_Ioc) (max H 0) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact (hH s (hIoc hs)).trans (le_max_left _ _)
  have hlip : ∀ s ∈ Ioc 0 B, ∀ t ∈ Ioc 0 B, |h s - h t| ≤ (K : ℝ) * |s - t| := by
    intro s hs t ht
    have := hK.dist_le_mul s (hIoc hs) t (hIoc ht)
    simpa [Real.dist_eq] using this
  refine ⟨max H 0, K * B + 2 * max H 0, h2, hfb, fun v hv => ?_⟩
  exact Cvs.Upstream.LevyConditionL1Modulus.modulus_cut hB hv K.2 hH0 hint (fun s hs => by
    rw [← Real.norm_eq_abs]; exact (hH s (hIoc hs)).trans (le_max_left _ _)) hlip

/-- A finite sum of cut functions `Σ_i 1_{(0, B_i]} h_i`, each `h_i` `C¹` on `[0, B_i]`, is an admissible Weil test
function: `L²`, `L¹`, square-integrable, with integrable shifted products and the Lévy condition. -/
theorem admissible_sum_cut {ι : Type*} (S : Finset ι) (B : ι → ℝ) (h : ι → ℝ → ℝ)
    (hB : ∀ i ∈ S, 0 ≤ B i) (hC : ∀ i ∈ S, ContDiffOn ℝ 1 (h i) (Icc 0 (B i))) {f : ℝ → ℝ}
    (hf : f = fun s => ∑ i ∈ S, indicator (Ioc 0 (B i)) (h i) s) :
    MemLp f 2 volume ∧ Integrable f volume
      ∧ Integrable (fun s => f s ^ 2) volume
      ∧ (∀ u : ℝ, Integrable (fun s => f s * f (s + u)) volume)
      ∧ IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy f) (Ioi 0) volume := by
  have hp : ∀ i ∈ S, ∃ H L : ℝ, MemLp (indicator (Ioc 0 (B i)) (h i)) 2 volume
      ∧ (∀ s, |indicator (Ioc 0 (B i)) (h i) s| ≤ H)
      ∧ ∀ v, 0 ≤ v → Integrable (fun s => indicator (Ioc 0 (B i)) (h i) s
          - indicator (Ioc 0 (B i)) (h i) (s + v)) volume
        ∧ ∫ s, |indicator (Ioc 0 (B i)) (h i) s - indicator (Ioc 0 (B i)) (h i) (s + v)| ≤ L * v :=
    fun i hi => cut_piece (hB i hi) (hC i hi)
  choose! H L hp using hp
  set g : ι → ℝ → ℝ := fun i => indicator (Ioc 0 (B i)) (h i) with hg
  have h2 : MemLp f 2 volume := by
    rw [hf]; exact memLp_finsetSum S fun i hi => (hp i hi).1
  have h1 : Integrable f volume := by
    rw [hf]
    exact integrable_finsetSum S fun i hi =>
      (integrable_indicator_iff measurableSet_Ioc).mpr
        (((hC i hi).continuousOn.integrableOn_Icc).mono_set Ioc_subset_Icc_self)
  have hfb : ∀ s, |f s| ≤ ∑ i ∈ S, H i := by
    intro s
    rw [hf]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => (hp i hi).2.1 s)
  have hdiff : ∀ v, (fun s => f s - f (s + v)) = fun s => ∑ i ∈ S, (g i s - g i (s + v)) := by
    intro v; funext s; rw [hf, hg]; simp only [Finset.sum_sub_distrib]
  have hdi : ∀ v, 0 ≤ v → Integrable (fun s => f s - f (s + v)) volume := by
    intro v hv
    rw [hdiff v]
    exact integrable_finsetSum S fun i hi => ((hp i hi).2.2 v hv).1
  have hmod : ∀ v, 0 ≤ v → ∫ s, |f s - f (s + v)| ≤ (∑ i ∈ S, L i) * v := by
    intro v hv
    have hint : ∀ i ∈ S, Integrable (fun s => g i s - g i (s + v)) volume := fun i hi =>
      ((hp i hi).2.2 v hv).1
    calc ∫ s, |f s - f (s + v)| = ∫ s, |∑ i ∈ S, (g i s - g i (s + v))| := by
          congr 1; funext s; exact congrArg abs (congrFun (hdiff v) s)
      _ ≤ ∫ s, ∑ i ∈ S, |g i s - g i (s + v)| := by
          refine integral_mono ?_ (integrable_finsetSum S fun i hi => (hint i hi).abs) ?_
          · exact (integrable_finsetSum S hint).abs
          · intro s; exact Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i ∈ S, ∫ s, |g i s - g i (s + v)| := integral_finsetSum S fun i hi => (hint i hi).abs
      _ ≤ ∑ i ∈ S, L i * v := Finset.sum_le_sum fun i hi => ((hp i hi).2.2 v hv).2
      _ = (∑ i ∈ S, L i) * v := (Finset.sum_mul _ _ _).symm
  refine ⟨h2, h1, h2.integrable_sq, fun u => h2.integrable_mul
    (h2.comp_measurePreserving (measurePreserving_add_right volume u)), ?_⟩
  exact Cvs.Upstream.LevyConditionL1Modulus.integrableOn_levy h2 hfb hdi hmod

/-- The log-scale profile of the position-truncated tail is the sum over `m ≤ ⌊X⌋` of the cut functions
`1_{(0, log(X/m)]} (Φ(m eˢ) e^{s/2})`. -/
theorem logScale_posTail (Φ : ℝ → ℝ) {X : ℝ} (hX : 0 < X) :
    logScale (posTail Φ X) = fun s => ∑ m ∈ Finset.Icc 1 ⌊X⌋₊,
      indicator (Ioc 0 (log (X / m))) (fun s => Φ (m * exp s) * exp (s / 2)) s := by
  funext s
  unfold logScale
  rw [posTail_eq_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
  have hb0 : 0 < X / m := div_pos hX (by linarith)
  by_cases hs : s ∈ Ioc 0 (log (X / m))
  · have h' : exp s ∈ Ioc 1 (X / m) :=
      ⟨one_lt_exp_iff.mpr hs.1, (le_log_iff_exp_le hb0).mp hs.2⟩
    rw [indicator_of_mem hs, indicator_of_mem h']
  · have h' : exp s ∉ Ioc 1 (X / m) := by
      intro h'; apply hs; exact ⟨one_lt_exp_iff.mp h'.1, (le_log_iff_exp_le hb0).mpr h'.2⟩
    rw [indicator_of_notMem hs, indicator_of_notMem h', zero_mul]

/-- **The position-truncated tail is admissible**: for `Φ` `C¹` on `[1, X]` and `1 ≤ X`, `logScale (posTail Φ X)` is in
`L² ∩ L¹`, square-integrable, has integrable shifted products, and satisfies the Lévy condition. -/
theorem admissible_posTail {Φ : ℝ → ℝ} {X : ℝ} (hX : 1 ≤ X) (hΦ : ContDiffOn ℝ 1 Φ (Icc 1 X)) :
    MemLp (logScale (posTail Φ X)) 2 volume ∧ Integrable (logScale (posTail Φ X)) volume
      ∧ Integrable (fun s => logScale (posTail Φ X) s ^ 2) volume
      ∧ (∀ u : ℝ, Integrable (fun s => logScale (posTail Φ X) s * logScale (posTail Φ X) (s + u)) volume)
      ∧ IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (logScale (posTail Φ X))) (Ioi 0) volume := by
  have hX0 : 0 < X := by linarith
  refine admissible_sum_cut (Finset.Icc 1 ⌊X⌋₊) (fun m : ℕ => log (X / m))
    (fun (m : ℕ) s => Φ (m * exp s) * exp (s / 2)) ?_ ?_ (logScale_posTail Φ hX0)
  · intro m hm
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
    have hmX : (m : ℝ) ≤ X := (Nat.le_floor_iff hX0.le).mp (Finset.mem_Icc.mp hm).2
    exact log_nonneg ((one_le_div (by linarith)).mpr hmX)
  · intro m hm
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
    have hm0 : (0 : ℝ) < m := by linarith
    have hb0 : 0 < X / m := div_pos hX0 hm0
    apply ContDiffOn.mul _ (contDiff_exp.comp (contDiff_id.div_const 2)).contDiffOn
    refine hΦ.comp (contDiff_const.mul contDiff_exp).contDiffOn ?_
    intro s hs
    have e1 : 1 ≤ exp s := one_le_exp hs.1
    have e2 : exp s ≤ X / m := by rw [← exp_log hb0]; exact exp_le_exp.mpr hs.2
    constructor
    · nlinarith
    · calc (m : ℝ) * exp s ≤ m * (X / m) := mul_le_mul_of_nonneg_left e2 hm0.le
        _ = X := by field_simp

end Cvs.L2a.PositionTailAdmissible
