import Mathlib
import Cvs.L2a.LogPositionIdentity
import Cvs.L2a.PositionTruncatedTail

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The log-position sum in level form

For `1 ≤ X` and `Φ` continuous on `[1, X]`, `logPos Φ X = ∫_1^X (N(X) − N(k)) / k dk` with
`N(y) = ∫_{(1,∞)} posTail Φ y θ²` (Cvs.L2a.PositionTruncatedTail, Cvs.L2a.LogPositionIdentity): each pair `(a, n)` contributes `∫ Φ(aθ) Φ(nθ) 1_{k < max(a,n) θ}`
to `N(X) − N(k)`, and Fubini with `∫_1^{Mθ} dk/k = log(Mθ)` returns the log-position integral.
-/

namespace Cvs.L2a.LogPositionLevelForm

open Real Set Finset MeasureTheory intervalIntegral Cvs.L2a.PositionTruncatedTail Cvs.L2a.LogPositionIdentity

/-- The level-`k` cut of one pair: `∫_{(1, X/M]} g(θ) 1_{k < Mθ} dθ`. -/
noncomputable def cutI (g : ℝ → ℝ) (M X k : ℝ) : ℝ :=
  ∫ θ in Ioc 1 (X / M), if k < M * θ then g θ else 0

/-- **Fubini for one pair**: for `1 ≤ M` and `g` continuous on `[1, X/M]`, `k ↦ cutI g M X k / k` is integrable on
`(1, X]` and `∫_{(1,X]} cutI g M X k / k dk = ∫_{(1, X/M]} log(Mθ) g(θ) dθ`. -/
theorem integral_cutI_div {g : ℝ → ℝ} {M X : ℝ} (hM : 1 ≤ M) (hg : ContinuousOn g (Icc 1 (X / M))) :
    IntegrableOn (fun k => cutI g M X k / k) (Ioc 1 X) ∧
      ∫ k in Ioc 1 X, cutI g M X k / k = ∫ θ in Ioc 1 (X / M), Real.log (M * θ) * g θ := by
  have hM0 : 0 < M := lt_of_lt_of_le one_pos hM
  set μ : Measure ℝ := volume.restrict (Ioc 1 X)
  set ν : Measure ℝ := volume.restrict (Ioc 1 (X / M))
  set F : ℝ → ℝ → ℝ := fun k θ => if k < M * θ then g θ / k else 0 with hF
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hg
  have hmeas : AEStronglyMeasurable (Function.uncurry F) (μ.prod ν) := by
    have hgm : AEMeasurable g ν :=
      (hg.aemeasurable measurableSet_Icc).mono_measure (Measure.restrict_mono Set.Ioc_subset_Icc_self le_rfl)
    have h1 : AEMeasurable (fun p : ℝ × ℝ => g p.2 / p.1) (μ.prod ν) :=
      (hgm.comp_snd).div measurable_fst.aemeasurable
    have h2 : Function.uncurry F
        = Set.indicator {p : ℝ × ℝ | p.1 < M * p.2} (fun p : ℝ × ℝ => g p.2 / p.1) := by
      funext p
      simp only [Function.uncurry, hF, Set.indicator, Set.mem_ofPred_eq]
    rw [h2]
    exact (h1.indicator (measurableSet_lt measurable_fst (measurable_const.mul measurable_snd))).aestronglyMeasurable
  have hae : ∀ᵐ p ∂(μ.prod ν), p ∈ Ioc 1 X ×ˢ Ioc 1 (X / M) := by
    simp only [μ, ν]
    rw [Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)
  have hint : Integrable (Function.uncurry F) (μ.prod ν) := by
    refine Integrable.mono' (integrable_const C) hmeas ?_
    filter_upwards [hae] with p hp
    obtain ⟨hk, hθ⟩ := Set.mem_prod.mp hp
    have hgC : ‖g p.2‖ ≤ C := hC p.2 (Set.Ioc_subset_Icc_self hθ)
    simp only [Function.uncurry, hF]
    split_ifs
    · rw [norm_div, Real.norm_eq_abs p.1, abs_of_pos (by linarith [hk.1])]
      exact (div_le_self (norm_nonneg _) (by linarith [hk.1])).trans hgC
    · simpa using (norm_nonneg _).trans hgC
  have hcut : ∀ k, cutI g M X k / k = ∫ θ, F k θ ∂ν := by
    intro k
    rw [cutI, ← MeasureTheory.integral_div]
    refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    simp only [hF]
    split_ifs <;> simp
  have hinner : ∀ θ ∈ Ioc 1 (X / M), ∫ k, F k θ ∂μ = Real.log (M * θ) * g θ := by
    intro θ hθ
    have hMθ1 : 1 < M * θ := by nlinarith [hθ.1]
    have hMθX : M * θ ≤ X := by
      have := (le_div_iff₀ hM0).mp hθ.2; linarith
    have e : ∀ k, F k θ = g θ * Set.indicator (Iio (M * θ)) (fun k => k⁻¹) k := by
      intro k
      simp only [hF, Set.indicator, Set.mem_Iio]
      split_ifs <;> simp [div_eq_mul_inv]
    simp only [e, μ]
    rw [MeasureTheory.integral_const_mul, setIntegral_indicator measurableSet_Iio]
    have hset : Ioc 1 X ∩ Iio (M * θ) = Ioo 1 (M * θ) := by
      ext k
      simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Iio, Set.mem_Ioo]
      constructor
      · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩; exact ⟨⟨h1, by linarith⟩, h3⟩
    rw [hset, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hMθ1.le,
      integral_inv_of_pos one_pos (by linarith), div_one]
    ring
  refine ⟨?_, ?_⟩
  · have := hint.integral_prod_left
    refine this.congr (Filter.Eventually.of_forall fun k => ?_)
    simp only [Function.uncurry]
    rw [hcut k]
  · rw [setIntegral_congr_fun measurableSet_Ioc (fun k _ => hcut k)]
    show ∫ k, ∫ θ, F k θ ∂ν ∂μ = _
    rw [integral_integral_swap hint]
    exact setIntegral_congr_fun measurableSet_Ioc hinner

/-- The squared tail at level `k ∈ [1, X]` is the pair sum over `a, n ≤ ⌊X⌋` of `pairI Φ k a n` cut to
`max(a, n) ≤ ⌊k⌋`. -/
theorem integral_posTail_sq_level (Φ : ℝ → ℝ) {X k : ℝ} (hk : 1 ≤ k) (hkX : k ≤ X)
    (hcont : ContinuousOn Φ (Icc 1 X)) :
    ∫ θ in Ioi 1, posTail Φ k θ ^ 2
      = ∑ a ∈ Finset.Icc 1 ⌊X⌋₊, ∑ n ∈ Finset.Icc 1 ⌊X⌋₊,
          if max a n ≤ ⌊k⌋₊ then pairI Φ k a n else 0 := by
  have h := integral_posTail_mul_dilate Φ hk (hcont.mono (Icc_subset_Icc_right hkX)) (k := 1) le_rfl
  simp only [Nat.cast_one, one_mul] at h
  have hfilt : (Finset.Icc 1 ⌊k⌋₊).filter (fun m => m ≤ ⌊k⌋₊) = Finset.Icc 1 ⌊k⌋₊ :=
    Finset.filter_true_of_mem fun m hm => (Finset.mem_Icc.mp hm).2
  rw [hfilt] at h
  have hsq : (fun θ => posTail Φ k θ ^ 2) = fun θ => posTail Φ k θ * posTail Φ k θ := by
    funext θ; ring
  rw [hsq, h]
  have hsub : Finset.Icc 1 ⌊k⌋₊ = (Finset.Icc 1 ⌊X⌋₊).filter (fun n => n ≤ ⌊k⌋₊) := by
    have := Nat.floor_le_floor (R := ℝ) hkX
    ext n
    simp only [Finset.mem_Icc, Finset.mem_filter]
    omega
  rw [hsub, Finset.sum_filter]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_filter]
  split_ifs with ha
  · refine Finset.sum_congr rfl fun n _ => ?_
    by_cases hn : n ≤ ⌊k⌋₊
    · rw [if_pos hn, if_pos (max_le ha hn)]
    · rw [if_neg hn, if_neg fun h => hn (le_of_max_le_right h)]
  · symm
    exact Finset.sum_eq_zero fun n _ => if_neg fun h => ha (le_of_max_le_left h)

/-- For a pair `a, n ≤ ⌊X⌋` and a level `k ∈ [1, X]`, the full pair integral minus its level-`k` part is the cut
integral `cutI` with `M = max(a, n)`. -/
theorem pairI_sub_level {Φ : ℝ → ℝ} {X k : ℝ} (hX : 1 ≤ X) (hk : 1 ≤ k) (hkX : k ≤ X)
    (hcont : ContinuousOn Φ (Icc 1 X)) {a n : ℕ} (ha : a ∈ Finset.Icc 1 ⌊X⌋₊) (hn : n ∈ Finset.Icc 1 ⌊X⌋₊) :
    pairI Φ X a n - (if max a n ≤ ⌊k⌋₊ then pairI Φ k a n else 0)
      = cutI (fun θ => Φ (a * θ) * Φ (n * θ)) ((max a n : ℕ) : ℝ) X k := by
  set M : ℝ := ((max a n : ℕ) : ℝ) with hMdef
  set g : ℝ → ℝ := fun θ => Φ (a * θ) * Φ (n * θ) with hgdef
  have ha1 := (Finset.mem_Icc.mp ha).1
  have hn1 := (Finset.mem_Icc.mp hn).1
  have hM1 : (1 : ℝ) ≤ M := by
    have : 1 ≤ max a n := le_trans ha1 (le_max_left _ _)
    rw [hMdef]; exact_mod_cast this
  have hM0 : 0 < M := lt_of_lt_of_le one_pos hM1
  have hb := one_le_div_max hX ha hn
  have hgc : ContinuousOn g (Icc 1 (X / M)) := continuousOn_pair hcont ha1 hn1
  have hfull : pairI Φ X a n = ∫ θ in Ioc 1 (X / M), g θ := by
    rw [pairI, intervalIntegral.integral_of_le hb]
  rw [hfull, cutI]
  split_ifs with hK
  · have hMk : M ≤ k := by
      have : ((max a n : ℕ) : ℝ) ≤ (⌊k⌋₊ : ℝ) := by exact_mod_cast hK
      exact this.trans (Nat.floor_le (by linarith))
    have hkM1 : 1 ≤ k / M := (le_div_iff₀ hM0).mpr (by linarith)
    have hkMb : k / M ≤ X / M := div_le_div_of_nonneg_right hkX hM0.le
    have hII : ∀ u v, u ∈ Icc 1 (X / M) → v ∈ Icc 1 (X / M) → IntervalIntegrable g volume u v := by
      intro u v hu hv
      exact (hgc.mono (uIcc_subset_Icc hu hv)).intervalIntegrable
    have hlev : pairI Φ k a n = ∫ θ in (1 : ℝ)..(k / M), g θ := rfl
    rw [hlev, ← intervalIntegral.integral_of_le hb,
      intervalIntegral.integral_interval_sub_left (hII 1 (X / M) ⟨le_rfl, hb⟩ ⟨hb, le_rfl⟩)
        (hII 1 (k / M) ⟨le_rfl, hb⟩ ⟨hkM1, hkMb⟩),
      intervalIntegral.integral_of_le hkMb]
    have e : ∀ θ, (if k < M * θ then g θ else 0) = Set.indicator (Ioi (k / M)) g θ := by
      intro θ
      simp only [Set.indicator, Set.mem_Ioi, div_lt_iff₀ hM0, mul_comm θ M]
    rw [setIntegral_congr_fun measurableSet_Ioc (fun θ _ => e θ), setIntegral_indicator measurableSet_Ioi]
    have hset : Ioc 1 (X / M) ∩ Ioi (k / M) = Ioc (k / M) (X / M) := by
      ext θ
      simp only [Set.mem_Ioc, Set.mem_inter_iff, Set.mem_Ioi]
      constructor
      · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨by linarith, h2⟩, h1⟩
    rw [hset]
  · have hkM : k < M := by
      have h1 : ⌊k⌋₊ + 1 ≤ max a n := by omega
      have h2 : ((⌊k⌋₊ + 1 : ℕ) : ℝ) ≤ M := by rw [hMdef]; exact_mod_cast h1
      push_cast at h2
      linarith [Nat.lt_floor_add_one k]
    rw [sub_zero]
    refine setIntegral_congr_fun measurableSet_Ioc fun θ hθ => ?_
    have : k < M * θ := by nlinarith [hθ.1]
    simp only [if_pos this]

/-- **The log-position sum in level form**: for `1 ≤ X` and `Φ` continuous on `[1, X]`,
`logPos Φ X = ∫_1^X (N(X) − N(k)) / k dk` with `N(y) = ∫_{(1,∞)} posTail Φ y θ²`. -/
theorem logPos_eq_levels (Φ : ℝ → ℝ) {X : ℝ} (hX : 1 ≤ X) (hcont : ContinuousOn Φ (Icc 1 X)) :
    logPos Φ X = ∫ k in (1 : ℝ)..X,
      ((∫ θ in Ioi 1, posTail Φ X θ ^ 2) - ∫ θ in Ioi 1, posTail Φ k θ ^ 2) / k := by
  set s := Finset.Icc 1 ⌊X⌋₊
  have hpair : ∀ a ∈ s, ∀ n ∈ s,
      IntegrableOn (fun k => cutI (fun θ => Φ (a * θ) * Φ (n * θ)) ((max a n : ℕ) : ℝ) X k / k) (Ioc 1 X) ∧
      ∫ k in Ioc 1 X, cutI (fun θ => Φ (a * θ) * Φ (n * θ)) ((max a n : ℕ) : ℝ) X k / k
        = ∫ θ in Ioc 1 (X / ((max a n : ℕ) : ℝ)),
            Real.log (((max a n : ℕ) : ℝ) * θ) * (Φ (a * θ) * Φ (n * θ)) := by
    intro a ha n hn
    have ha1 := (Finset.mem_Icc.mp ha).1
    have hn1 := (Finset.mem_Icc.mp hn).1
    have hM1 : (1 : ℝ) ≤ ((max a n : ℕ) : ℝ) := by
      have : 1 ≤ max a n := le_trans ha1 (le_max_left _ _)
      exact_mod_cast this
    exact integral_cutI_div hM1 (continuousOn_pair hcont ha1 hn1)
  have hdiff : ∀ k ∈ Ioc 1 X,
      ((∫ θ in Ioi 1, posTail Φ X θ ^ 2) - ∫ θ in Ioi 1, posTail Φ k θ ^ 2) / k
        = ∑ a ∈ s, ∑ n ∈ s, cutI (fun θ => Φ (a * θ) * Φ (n * θ)) ((max a n : ℕ) : ℝ) X k / k := by
    intro k hk
    have hNX : ∫ θ in Ioi 1, posTail Φ X θ ^ 2 = ∑ a ∈ s, ∑ n ∈ s, pairI Φ X a n := by
      rw [integral_posTail_sq_level Φ hX le_rfl hcont]
      refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun n hn => ?_
      exact if_pos (max_le (Finset.mem_Icc.mp ha).2 (Finset.mem_Icc.mp hn).2)
    rw [hNX, integral_posTail_sq_level Φ hk.1.le hk.2 hcont, ← Finset.sum_sub_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [← Finset.sum_sub_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [pairI_sub_level hX hk.1.le hk.2 hcont ha hn]
  rw [intervalIntegral.integral_of_le hX, setIntegral_congr_fun measurableSet_Ioc hdiff,
    integral_finsetSum _ fun a ha => integrable_finsetSum _ fun n hn => (hpair a ha n hn).1]
  unfold logPos
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [integral_finsetSum _ fun n hn => (hpair a ha n hn).1]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [(hpair a ha n hn).2, intervalIntegral.integral_of_le (one_le_div_max hX ha hn)]

end Cvs.L2a.LogPositionLevelForm
