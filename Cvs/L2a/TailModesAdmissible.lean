import Mathlib
import Cvs.L2a.TailLogScaleTest
import Cvs.L2a.TailOfModes
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
# The tail of `M` modes is an admissible Weil test function

If `ψ` is `C¹` on `[1, Ξ]` and `Mb ≤ Ξ`, then `f = logScale (tailF ψ M b) = 1_{(0, log b]} h` with `h` `C¹`, hence
bounded and Lipschitz there: `f ∈ L¹ ∩ L²`, its shifted products are integrable, and it satisfies the Lévy condition.
-/

namespace Cvs.L2a.TailModesAdmissible

open Real Set MeasureTheory Cvs.L2a.TailLogScaleTest Cvs.L2a.TailOfModes

/-- The log-scale profile of the tail on `(0, log b]`. -/
noncomputable def hh (ψ : ℝ → ℝ) (M : ℕ) (s : ℝ) : ℝ :=
  (∑ m ∈ Finset.Icc 1 M, ψ (m * exp s)) * exp (s / 2)

theorem logScale_tailF (ψ : ℝ → ℝ) (M : ℕ) {b : ℝ} (hb : 0 < b) :
    logScale (tailF ψ M b) = indicator (Ioc 0 (log b)) (hh ψ M) := by
  funext s
  unfold logScale tailF hh
  by_cases h : s ∈ Ioc 0 (log b)
  · have h' : exp s ∈ Ioc 1 b := ⟨one_lt_exp_iff.mpr h.1, (le_log_iff_exp_le hb).mp h.2⟩
    rw [indicator_of_mem h, indicator_of_mem h']
  · have h' : exp s ∉ Ioc 1 b := by
      intro h'; apply h; exact ⟨one_lt_exp_iff.mp h'.1, (le_log_iff_exp_le hb).mpr h'.2⟩
    rw [indicator_of_notMem h, indicator_of_notMem h', zero_mul]

theorem contDiffOn_hh {ψ : ℝ → ℝ} {M : ℕ} {b Ξ : ℝ} (hb : 1 ≤ b) (hΞ : (M : ℝ) * b ≤ Ξ)
    (hψ : ContDiffOn ℝ 1 ψ (Icc 1 Ξ)) : ContDiffOn ℝ 1 (hh ψ M) (Icc 0 (log b)) := by
  unfold hh
  apply ContDiffOn.mul _ (contDiff_exp.comp (contDiff_id.div_const 2)).contDiffOn
  apply ContDiffOn.sum
  intro m hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
  have hmM : (m : ℝ) ≤ M := by exact_mod_cast (Finset.mem_Icc.mp hm).2
  have hb0 : 0 < b := by linarith
  refine hψ.comp (contDiff_const.mul contDiff_exp).contDiffOn ?_
  intro s hs
  have e1 : 1 ≤ exp s := one_le_exp hs.1
  have e2 : exp s ≤ b := by rw [← exp_log hb0]; exact exp_le_exp.mpr hs.2
  constructor
  · nlinarith
  · calc (m : ℝ) * exp s ≤ M * b := mul_le_mul hmM e2 (by positivity) (by positivity)
      _ ≤ Ξ := hΞ

/-- **The tail is admissible.** -/
theorem admissible {ψ : ℝ → ℝ} {M : ℕ} {b Ξ : ℝ} (hb : 1 ≤ b) (hΞ : (M : ℝ) * b ≤ Ξ)
    (hψ : ContDiffOn ℝ 1 ψ (Icc 1 Ξ)) :
    MemLp (logScale (tailF ψ M b)) 2 volume ∧ Integrable (logScale (tailF ψ M b)) volume
      ∧ Integrable (fun s => logScale (tailF ψ M b) s ^ 2) volume
      ∧ (∀ u : ℝ, Integrable (fun s => logScale (tailF ψ M b) s * logScale (tailF ψ M b) (s + u)) volume)
      ∧ IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (logScale (tailF ψ M b))) (Ioi 0) volume := by
  have hb0 : 0 < b := by linarith
  have hlb : 0 ≤ log b := log_nonneg hb
  have hC := contDiffOn_hh hb hΞ hψ
  have hcont : ContinuousOn (hh ψ M) (Icc 0 (log b)) := hC.continuousOn
  obtain ⟨K, hK⟩ := hC.exists_lipschitzOnWith one_ne_zero (convex_Icc _ _) isCompact_Icc
  obtain ⟨H, hH⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  rw [logScale_tailF ψ M hb0]
  set f := indicator (Ioc 0 (log b)) (hh ψ M) with hf
  have hIoc : Ioc 0 (log b) ⊆ Icc 0 (log b) := Ioc_subset_Icc_self
  have hint : IntegrableOn (hh ψ M) (Ioc 0 (log b)) volume :=
    (hcont.integrableOn_Icc).mono_set hIoc
  have hH0 : 0 ≤ max H 0 := le_max_right _ _
  have hfb : ∀ s, |f s| ≤ max H 0 := by
    intro s
    by_cases h : s ∈ Ioc 0 (log b)
    · rw [hf, indicator_of_mem h, ← Real.norm_eq_abs]; exact (hH s (hIoc h)).trans (le_max_left _ _)
    · rw [hf, indicator_of_notMem h, abs_zero]; exact hH0
  have h1 : Integrable f volume := (integrable_indicator_iff measurableSet_Ioc).mpr hint
  have h2 : MemLp f 2 volume := by
    rw [hf, memLp_indicator_iff_restrict measurableSet_Ioc.nullMeasurableSet]
    have : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) (log b))) :=
      isFiniteMeasure_restrict.mpr measure_Ioc_lt_top.ne
    refine MemLp.of_bound ((hcont.mono hIoc).aestronglyMeasurable measurableSet_Ioc) (max H 0) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact (hH s (hIoc hs)).trans (le_max_left _ _)
  have hlip : ∀ s ∈ Ioc 0 (log b), ∀ t ∈ Ioc 0 (log b), |hh ψ M s - hh ψ M t| ≤ (K : ℝ) * |s - t| := by
    intro s hs t ht
    have := hK.dist_le_mul s (hIoc hs) t (hIoc ht)
    simpa [Real.dist_eq] using this
  have hmod := fun v (hv : 0 ≤ v) => Cvs.Upstream.LevyConditionL1Modulus.modulus_cut (h := hh ψ M) (B := log b) (H := max H 0)
    (Lh := K) (v := v) hlb hv K.2 hH0 hint (fun s hs => by
      rw [← Real.norm_eq_abs]; exact (hH s (hIoc hs)).trans (le_max_left _ _)) hlip
  refine ⟨h2, h1, h2.integrable_sq, fun u => h2.integrable_mul
    (h2.comp_measurePreserving (measurePreserving_add_right volume u)), ?_⟩
  exact Cvs.Upstream.LevyConditionL1Modulus.integrableOn_levy h2 hfb (fun v hv => (hmod v hv).1) (fun v hv => (hmod v hv).2)

end Cvs.L2a.TailModesAdmissible
