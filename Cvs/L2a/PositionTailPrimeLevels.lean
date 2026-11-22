import Mathlib
import Cvs.L2a.CutWeightResidual
import Cvs.L2a.LogPositionIdentity
import Cvs.L2a.LogPositionLevelForm
import Cvs.L2a.PositionTailPrimePairs
import Cvs.L2a.PositionTailSpanAdapters
import Cvs.L2a.PositionTruncatedTail
import Cvs.L2a.TailLogScaleTest
import Cvs.WeilForm.PrimePowerIndexed
import Cvs.Zeta.PrimePowerSideTruncated
import Cvs.Zeta.WeilPositivityStatement

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The prime side of the position-truncated tail in level form

For `1 ≤ X` the prime side of `F_X = posTail Φ X` is `2∫_1^X ⟨F_X, F_X − F_k⟩ dk/k − 2∫ log θ F_X²`: `LogPositionLevelForm`'s Fubini
with the cut `k < min(a, n)θ` gives the `log min(a, n)` part of `CutWeightResidual`'s min form, `LogPositionLevelForm`'s `logPos` levels the rest.
-/

namespace Cvs.L2a.PositionTailPrimeLevels

open Real Set Filter Topology MeasureTheory Cvs.L2a.PositionTruncatedTail

/-- The level-`k` cut of one pair with cut multiplier `m`: `∫_{(1, X/M]} g(θ) 1_{k < mθ} dθ`. -/
noncomputable def cutI2 (g : ℝ → ℝ) (m M X k : ℝ) : ℝ :=
  ∫ θ in Ioc 1 (X / M), if k < m * θ then g θ else 0

/-- **Fubini for one pair with cut multiplier `m ≤ M`**: `k ↦ cutI2 g m M X k / k` is integrable on `(1, X]` and
`∫_{(1,X]} cutI2 g m M X k / k dk = ∫_{(1, X/M]} log(mθ) g(θ) dθ`. -/
theorem integral_cutI2_div {g : ℝ → ℝ} {m M X : ℝ} (hm : 1 ≤ m) (hmM : m ≤ M)
    (hg : ContinuousOn g (Icc 1 (X / M))) :
    IntegrableOn (fun k => cutI2 g m M X k / k) (Ioc 1 X) ∧
      ∫ k in Ioc 1 X, cutI2 g m M X k / k = ∫ θ in Ioc 1 (X / M), Real.log (m * θ) * g θ := by
  have hM0 : 0 < M := lt_of_lt_of_le one_pos (hm.trans hmM)
  set μ : Measure ℝ := volume.restrict (Ioc 1 X)
  set ν : Measure ℝ := volume.restrict (Ioc 1 (X / M))
  set F : ℝ → ℝ → ℝ := fun k θ => if k < m * θ then g θ / k else 0 with hF
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hg
  have hmeas : AEStronglyMeasurable (Function.uncurry F) (μ.prod ν) := by
    have hgm : AEMeasurable g ν :=
      (hg.aemeasurable measurableSet_Icc).mono_measure (Measure.restrict_mono Set.Ioc_subset_Icc_self le_rfl)
    have h1 : AEMeasurable (fun p : ℝ × ℝ => g p.2 / p.1) (μ.prod ν) :=
      (hgm.comp_snd).div measurable_fst.aemeasurable
    have h2 : Function.uncurry F
        = Set.indicator {p : ℝ × ℝ | p.1 < m * p.2} (fun p : ℝ × ℝ => g p.2 / p.1) := by
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
  have hcut : ∀ k, cutI2 g m M X k / k = ∫ θ, F k θ ∂ν := by
    intro k
    rw [cutI2, ← MeasureTheory.integral_div]
    refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    simp only [hF]
    split_ifs <;> simp
  have hinner : ∀ θ ∈ Ioc 1 (X / M), ∫ k, F k θ ∂μ = Real.log (m * θ) * g θ := by
    intro θ hθ
    have hmθ1 : 1 < m * θ := by nlinarith [hθ.1]
    have hmθX : m * θ ≤ X := by
      have h1 := (le_div_iff₀ hM0).mp hθ.2
      nlinarith [hθ.1]
    have e : ∀ k, F k θ = g θ * Set.indicator (Iio (m * θ)) (fun k => k⁻¹) k := by
      intro k
      simp only [hF, Set.indicator, Set.mem_Iio]
      split_ifs <;> simp [div_eq_mul_inv]
    simp only [e, μ]
    rw [MeasureTheory.integral_const_mul, setIntegral_indicator measurableSet_Iio]
    have hset : Ioc 1 X ∩ Iio (m * θ) = Ioo 1 (m * θ) := by
      ext k
      simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Iio, Set.mem_Ioo]
      constructor
      · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩; exact ⟨⟨h1, by linarith⟩, h3⟩
    rw [hset, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hmθ1.le,
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

/-- For `m > 0`, `θ ∈ (max(1, k/m), X/m]` iff `1 < θ`, `k < mθ` and `mθ ≤ X`. -/
theorem mem_Ioc_cut {m k X θ : ℝ} (hm : 0 < m) :
    θ ∈ Ioc (max 1 (k / m)) (X / m) ↔ 1 < θ ∧ k < m * θ ∧ m * θ ≤ X := by
  rw [Set.mem_Ioc, max_lt_iff, div_lt_iff₀ hm, le_div_iff₀ hm, mul_comm θ m, and_assoc]

/-- The product of the cut modes of `a` and `n` is the pair product on `(1, X/max(a,n)]` cut to `k < min(a,n)θ`. -/
theorem cut_mul_cut (Φ : ℝ → ℝ) {X k θ : ℝ} {a n : ℕ} (ha : 1 ≤ a) (hn : 1 ≤ n) :
    (Ioc (max 1 (k / a)) (X / a)).indicator (fun θ => Φ (a * θ)) θ
        * (Ioc (max 1 (k / n)) (X / n)).indicator (fun θ => Φ (n * θ)) θ
      = (Ioc 1 (X / (max a n : ℕ))).indicator
          (fun θ => if k < ((min a n : ℕ) : ℝ) * θ then Φ (a * θ) * Φ (n * θ) else 0) θ := by
  have ha0 : (0 : ℝ) < a := lt_of_lt_of_le one_pos (by exact_mod_cast ha)
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le one_pos (by exact_mod_cast hn)
  have hM0 : (0 : ℝ) < ((max a n : ℕ) : ℝ) := by rw [Nat.cast_max]; exact lt_max_of_lt_left ha0
  have hiff : (θ ∈ Ioc (max 1 (k / a)) (X / a) ∧ θ ∈ Ioc (max 1 (k / n)) (X / n))
      ↔ (θ ∈ Ioc 1 (X / ((max a n : ℕ) : ℝ)) ∧ k < ((min a n : ℕ) : ℝ) * θ) := by
    rw [mem_Ioc_cut ha0, mem_Ioc_cut hn0, Set.mem_Ioc, le_div_iff₀ hM0, Nat.cast_max, Nat.cast_min]
    constructor
    · rintro ⟨⟨h1, ha1, ha2⟩, -, hn1, hn2⟩
      refine ⟨⟨h1, ?_⟩, ?_⟩
      · rw [mul_max_of_nonneg _ _ (by linarith)]; exact max_le (by linarith) (by linarith)
      · rw [min_mul_of_nonneg _ _ (by linarith)]; exact lt_min ha1 hn1
    · rintro ⟨⟨h1, h2⟩, h3⟩
      rw [mul_max_of_nonneg _ _ (by linarith), max_le_iff] at h2
      rw [min_mul_of_nonneg _ _ (by linarith), lt_min_iff] at h3
      exact ⟨⟨h1, h3.1, by linarith [h2.1]⟩, h1, h3.2, by linarith [h2.2]⟩
  simp only [Set.indicator_apply]
  split_ifs <;> first | (exfalso; tauto) | simp

/-- For `1 ≤ k ≤ X`, `(F_X − F_k)²` is the pair sum over `a, n ≤ ⌊X⌋` of the pair product on `(1, X/max(a,n)]`
cut to `k < min(a,n)θ`. -/
theorem sq_posTail_sub_eq (Φ : ℝ → ℝ) {X k : ℝ} (hk : 1 ≤ k) (hkX : k ≤ X) (θ : ℝ) :
    (posTail Φ X θ - posTail Φ k θ) ^ 2 = ∑ a ∈ Finset.Icc 1 ⌊X⌋₊, ∑ n ∈ Finset.Icc 1 ⌊X⌋₊,
      (Ioc 1 (X / (max a n : ℕ))).indicator
        (fun θ => if k < ((min a n : ℕ) : ℝ) * θ then Φ (a * θ) * Φ (n * θ) else 0) θ := by
  rw [Cvs.L2a.PositionTailSpanAdapters.posTail_sub_posTail Φ hk hkX θ, sq, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun n hn => ?_
  exact cut_mul_cut Φ (Finset.mem_Icc.mp ha).1 (Finset.mem_Icc.mp hn).1

/-- Each cut pair term is integrable for `Φ` continuous on `[1, X]`. -/
theorem integrable_cut_indicator {Φ : ℝ → ℝ} {X : ℝ} (hcont : ContinuousOn Φ (Icc 1 X)) {a n : ℕ}
    (ha : 1 ≤ a) (hn : 1 ≤ n) (k : ℝ) :
    Integrable ((Ioc 1 (X / (max a n : ℕ))).indicator
      (fun θ => if k < ((min a n : ℕ) : ℝ) * θ then Φ (a * θ) * Φ (n * θ) else 0)) := by
  refine (integrable_indicator_iff measurableSet_Ioc).mpr ?_
  have he : (fun θ => if k < ((min a n : ℕ) : ℝ) * θ then Φ (a * θ) * Φ (n * θ) else 0)
      = {θ : ℝ | k < ((min a n : ℕ) : ℝ) * θ}.indicator (fun θ => Φ (a * θ) * Φ (n * θ)) := by
    funext θ
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  rw [he]
  exact ((integrableOn_pair hcont ha hn).mono_set Ioc_subset_Icc_self).indicator
    (measurableSet_lt measurable_const (measurable_const.mul measurable_id))

/-- For `1 ≤ k ≤ X` and `Φ` continuous on `[1, X]`, `(F_X − F_k)²` is integrable on `(1, ∞)`. -/
theorem integrableOn_posTail_sub_sq (Φ : ℝ → ℝ) {X k : ℝ} (hk : 1 ≤ k) (hkX : k ≤ X)
    (hcont : ContinuousOn Φ (Icc 1 X)) :
    IntegrableOn (fun θ => (posTail Φ X θ - posTail Φ k θ) ^ 2) (Ioi 1) := by
  refine IntegrableOn.congr_fun ?_ (fun θ _ => (sq_posTail_sub_eq Φ hk hkX θ).symm) measurableSet_Ioi
  exact (integrable_finsetSum _ fun a ha => integrable_finsetSum _ fun n hn =>
    integrable_cut_indicator hcont (Finset.mem_Icc.mp ha).1 (Finset.mem_Icc.mp hn).1 k).integrableOn

/-- **The squared level difference as cut pairs**: for `1 ≤ k ≤ X` and `Φ` continuous on `[1, X]`,
`∫_{(1,∞)} (F_X − F_k)² = Σ_{a,n ≤ ⌊X⌋} cutI2 (Φ(a·)Φ(n·)) min(a,n) max(a,n) X k`. -/
theorem integral_posTail_sub_sq_eq (Φ : ℝ → ℝ) {X k : ℝ} (hk : 1 ≤ k) (hkX : k ≤ X)
    (hcont : ContinuousOn Φ (Icc 1 X)) :
    ∫ θ in Ioi 1, (posTail Φ X θ - posTail Φ k θ) ^ 2
      = ∑ a ∈ Finset.Icc 1 ⌊X⌋₊, ∑ n ∈ Finset.Icc 1 ⌊X⌋₊,
          cutI2 (fun θ => Φ (a * θ) * Φ (n * θ)) ((min a n : ℕ) : ℝ) ((max a n : ℕ) : ℝ) X k := by
  have hI : ∀ a ∈ Finset.Icc 1 ⌊X⌋₊, ∀ n ∈ Finset.Icc 1 ⌊X⌋₊,
      Integrable ((Ioc 1 (X / (max a n : ℕ))).indicator
        (fun θ => if k < ((min a n : ℕ) : ℝ) * θ then Φ (a * θ) * Φ (n * θ) else 0)) := fun a ha n hn =>
    integrable_cut_indicator hcont (Finset.mem_Icc.mp ha).1 (Finset.mem_Icc.mp hn).1 k
  rw [setIntegral_congr_fun measurableSet_Ioi (fun θ _ => sq_posTail_sub_eq Φ hk hkX θ),
    integral_finsetSum _ fun a ha => (integrable_finsetSum _ fun n hn => hI a ha n hn).integrableOn]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [integral_finsetSum _ fun n hn => (hI a ha n hn).integrableOn]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [setIntegral_indicator measurableSet_Ioc, Set.inter_eq_right.mpr Set.Ioc_subset_Ioi_self]
  rfl

/-- Fubini for one pair at `m = min(a, n)`, `M = max(a, n)`, for `a, n ∈ [1, ⌊X⌋]`. -/
theorem integral_cutI2_pair_div (Φ : ℝ → ℝ) {X : ℝ} (hcont : ContinuousOn Φ (Icc 1 X)) {a n : ℕ}
    (ha : a ∈ Finset.Icc 1 ⌊X⌋₊) (hn : n ∈ Finset.Icc 1 ⌊X⌋₊) :
    IntegrableOn (fun k => cutI2 (fun θ => Φ (a * θ) * Φ (n * θ)) ((min a n : ℕ) : ℝ) ((max a n : ℕ) : ℝ) X k / k)
        (Ioc 1 X) ∧
      ∫ k in Ioc 1 X, cutI2 (fun θ => Φ (a * θ) * Φ (n * θ)) ((min a n : ℕ) : ℝ) ((max a n : ℕ) : ℝ) X k / k
        = ∫ θ in Ioc 1 (X / ((max a n : ℕ) : ℝ)),
            Real.log (((min a n : ℕ) : ℝ) * θ) * (Φ (a * θ) * Φ (n * θ)) := by
  have ha1 := (Finset.mem_Icc.mp ha).1
  have hn1 := (Finset.mem_Icc.mp hn).1
  have hm1 : (1 : ℝ) ≤ ((min a n : ℕ) : ℝ) := by
    have : 1 ≤ min a n := le_min ha1 hn1
    exact_mod_cast this
  have hmM : ((min a n : ℕ) : ℝ) ≤ ((max a n : ℕ) : ℝ) := by exact_mod_cast min_le_max
  exact integral_cutI2_div hm1 hmM (Cvs.L2a.LogPositionIdentity.continuousOn_pair hcont ha1 hn1)

/-- On `(1, X]`, `∫(F_X − F_k)² / k` is the pair sum of `cutI2 / k`. -/
theorem levelD_eq (Φ : ℝ → ℝ) {X : ℝ} (hcont : ContinuousOn Φ (Icc 1 X)) {k : ℝ} (hk : k ∈ Ioc 1 X) :
    (∫ θ in Ioi 1, (posTail Φ X θ - posTail Φ k θ) ^ 2) / k
      = ∑ a ∈ Finset.Icc 1 ⌊X⌋₊, ∑ n ∈ Finset.Icc 1 ⌊X⌋₊,
          cutI2 (fun θ => Φ (a * θ) * Φ (n * θ)) ((min a n : ℕ) : ℝ) ((max a n : ℕ) : ℝ) X k / k := by
  rw [integral_posTail_sub_sq_eq Φ hk.1.le hk.2 hcont, Finset.sum_div]
  exact Finset.sum_congr rfl fun a _ => by rw [Finset.sum_div]

/-- `k ↦ ∫(F_X − F_k)² / k` is integrable on `(1, X]`. -/
theorem integrableOn_levelD (Φ : ℝ → ℝ) {X : ℝ} (hcont : ContinuousOn Φ (Icc 1 X)) :
    IntegrableOn (fun k => (∫ θ in Ioi 1, (posTail Φ X θ - posTail Φ k θ) ^ 2) / k) (Ioc 1 X) := by
  refine IntegrableOn.congr_fun ?_ (fun k hk => (levelD_eq Φ hcont hk).symm) measurableSet_Ioc
  exact integrable_finsetSum _ fun a ha => integrable_finsetSum _ fun n hn =>
    (integral_cutI2_pair_div Φ hcont ha hn).1

/-- On `(1, X]`, `(N_X − N_k) / k` is the pair sum of `LogPositionLevelForm`'s `cutI / k`, with `N_y = ∫ F_y²`. -/
theorem levelN_eq (Φ : ℝ → ℝ) {X : ℝ} (hX : 1 ≤ X) (hcont : ContinuousOn Φ (Icc 1 X)) {k : ℝ}
    (hk : k ∈ Ioc 1 X) :
    ((∫ θ in Ioi 1, posTail Φ X θ ^ 2) - ∫ θ in Ioi 1, posTail Φ k θ ^ 2) / k
      = ∑ a ∈ Finset.Icc 1 ⌊X⌋₊, ∑ n ∈ Finset.Icc 1 ⌊X⌋₊,
          Cvs.L2a.LogPositionLevelForm.cutI (fun θ => Φ (a * θ) * Φ (n * θ)) ((max a n : ℕ) : ℝ) X k / k := by
  have hNX : ∫ θ in Ioi 1, posTail Φ X θ ^ 2
      = ∑ a ∈ Finset.Icc 1 ⌊X⌋₊, ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, pairI Φ X a n := by
    rw [Cvs.L2a.LogPositionLevelForm.integral_posTail_sq_level Φ hX le_rfl hcont]
    refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun n hn => ?_
    exact if_pos (max_le (Finset.mem_Icc.mp ha).2 (Finset.mem_Icc.mp hn).2)
  rw [hNX, Cvs.L2a.LogPositionLevelForm.integral_posTail_sq_level Φ hk.1.le hk.2 hcont, ← Finset.sum_sub_distrib,
    Finset.sum_div]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [← Finset.sum_sub_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Cvs.L2a.LogPositionLevelForm.pairI_sub_level hX hk.1.le hk.2 hcont ha hn]

/-- `k ↦ (N_X − N_k) / k` is integrable on `(1, X]`. -/
theorem integrableOn_levelN (Φ : ℝ → ℝ) {X : ℝ} (hX : 1 ≤ X) (hcont : ContinuousOn Φ (Icc 1 X)) :
    IntegrableOn (fun k => ((∫ θ in Ioi 1, posTail Φ X θ ^ 2) - ∫ θ in Ioi 1, posTail Φ k θ ^ 2) / k)
      (Ioc 1 X) := by
  refine IntegrableOn.congr_fun ?_ (fun k hk => (levelN_eq Φ hX hcont hk).symm) measurableSet_Ioc
  refine integrable_finsetSum _ fun a ha => integrable_finsetSum _ fun n hn => ?_
  have ha1 := (Finset.mem_Icc.mp ha).1
  have hn1 := (Finset.mem_Icc.mp hn).1
  have hM1 : (1 : ℝ) ≤ ((max a n : ℕ) : ℝ) := by
    have : 1 ≤ max a n := le_trans ha1 (le_max_left _ _)
    exact_mod_cast this
  exact (Cvs.L2a.LogPositionLevelForm.integral_cutI_div hM1 (Cvs.L2a.LogPositionIdentity.continuousOn_pair hcont ha1 hn1)).1

/-- For `1 ≤ k ≤ X`, `2⟨F_X, F_X − F_k⟩ = (N_X − N_k) + ∫(F_X − F_k)²` on `(1, ∞)`. -/
theorem two_integral_mul_sub (Φ : ℝ → ℝ) {X k : ℝ} (hk : 1 ≤ k) (hkX : k ≤ X)
    (hcont : ContinuousOn Φ (Icc 1 X)) :
    2 * ∫ θ in Ioi 1, posTail Φ X θ * (posTail Φ X θ - posTail Φ k θ)
      = ((∫ θ in Ioi 1, posTail Φ X θ ^ 2) - ∫ θ in Ioi 1, posTail Φ k θ ^ 2)
        + ∫ θ in Ioi 1, (posTail Φ X θ - posTail Φ k θ) ^ 2 := by
  have h1 := integrableOn_posTail_sq Φ hcont
  have h2 := integrableOn_posTail_sq Φ (hcont.mono (Icc_subset_Icc_right hkX))
  have h3 := integrableOn_posTail_sub_sq Φ hk hkX hcont
  have h12 : IntegrableOn (fun θ => posTail Φ X θ ^ 2 - posTail Φ k θ ^ 2) (Ioi 1) := h1.sub h2
  rw [← integral_sub h1 h2, ← integral_add h12 h3,
    ← MeasureTheory.integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
  ring

/-- **The `log min` part in level form**: for `1 ≤ X` and `Φ` continuous on `[1, X]`,
`Σ_{a,n} ∫_1^{X/max(a,n)} log min(a,n) Φ(aθ)Φ(nθ) = ∫_1^X ∫(F_X − F_k)² dk/k − ∫ log θ F_X²`. -/
theorem min_levels (Φ : ℝ → ℝ) {X : ℝ} (hX : 1 ≤ X) (hcont : ContinuousOn Φ (Icc 1 X)) :
    ∑ a ∈ Finset.Icc 1 ⌊X⌋₊, ∑ n ∈ Finset.Icc 1 ⌊X⌋₊,
        ∫ θ in (1 : ℝ)..(X / (max a n : ℕ)), Real.log (min a n : ℕ) * (Φ (a * θ) * Φ (n * θ))
      = (∫ k in (1 : ℝ)..X, (∫ θ in Ioi 1, (posTail Φ X θ - posTail Φ k θ) ^ 2) / k)
        - ∫ θ in Ioi 1, Real.log θ * posTail Φ X θ ^ 2 := by
  have hpair := fun a (ha : a ∈ Finset.Icc 1 ⌊X⌋₊) n (hn : n ∈ Finset.Icc 1 ⌊X⌋₊) =>
    integral_cutI2_pair_div Φ hcont ha hn
  have hLHS : ∫ k in (1 : ℝ)..X, (∫ θ in Ioi 1, (posTail Φ X θ - posTail Φ k θ) ^ 2) / k
      = ∑ a ∈ Finset.Icc 1 ⌊X⌋₊, ∑ n ∈ Finset.Icc 1 ⌊X⌋₊,
          ((∫ θ in (1 : ℝ)..(X / (max a n : ℕ)), Real.log (min a n : ℕ) * (Φ (a * θ) * Φ (n * θ)))
            + ∫ θ in (1 : ℝ)..(X / (max a n : ℕ)), Real.log θ * (Φ (a * θ) * Φ (n * θ))) := by
    rw [intervalIntegral.integral_of_le hX, setIntegral_congr_fun measurableSet_Ioc
      (fun k hk => levelD_eq Φ hcont hk),
      integral_finsetSum _ fun a ha => integrable_finsetSum _ fun n hn => (hpair a ha n hn).1]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [integral_finsetSum _ fun n hn => (hpair a ha n hn).1]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hb := Cvs.L2a.LogPositionIdentity.one_le_div_max hX ha hn
    have hm0 : (0 : ℝ) < ((min a n : ℕ) : ℝ) := by
      have : 1 ≤ min a n := le_min (Finset.mem_Icc.mp ha).1 (Finset.mem_Icc.mp hn).1
      exact_mod_cast this
    have i1 := (Cvs.L2a.CutWeightResidual.continuousOn_weight_pair (g := fun _ => Real.log (min a n : ℕ)) hX
      hcont continuousOn_const ha hn).intervalIntegrable_of_Icc (μ := volume) hb
    have i2 := (Cvs.L2a.CutWeightResidual.continuousOn_weight_pair (g := Real.log) hX hcont
      (Cvs.L2a.CutWeightResidual.continuousOn_log_Icc X) ha hn).intervalIntegrable_of_Icc (μ := volume) hb
    rw [(hpair a ha n hn).2, ← intervalIntegral.integral_of_le hb, ← intervalIntegral.integral_add i1 i2]
    refine intervalIntegral.integral_congr fun θ hθ => ?_
    rw [uIcc_of_le hb] at hθ
    have hθ0 : (0 : ℝ) < θ := by linarith [hθ.1]
    rw [Real.log_mul hm0.ne' hθ0.ne']
    ring
  rw [hLHS, Cvs.L2a.CutWeightResidual.integral_mul_posTail_sq Φ hX hcont (Cvs.L2a.CutWeightResidual.continuousOn_log_Icc X)]
  simp only [Finset.sum_add_distrib]
  ring

/-- **The prime side in level form**: when the truncation reaches every prime power up to `X`, the prime side of
`F_X = posTail Φ X` is `2∫_1^X ⟨F_X, F_X − F_k⟩ dk/k − 2∫ log θ F_X²`. -/
theorem primeSide_posTail_levels (Φ : ℝ → ℝ) {X : ℝ} (hX : 1 ≤ X) (hcont : ContinuousOn Φ (Icc 1 X)) (P R : ℕ)
    (hPR : ∀ k : ℕ, IsPrimePow k → (k : ℝ) ≤ X → k ∈ Cvs.WeilForm.PrimePowerIndexed.primePowIndex P R) :
    Cvs.Zeta.Explicit.Weil.primePowerSideTruncated P R
        (Cvs.Zeta.Explicit.Weil.selfConvolution (Cvs.L2a.TailLogScaleTest.logScale (posTail Φ X)))
      = 2 * (∫ k in (1 : ℝ)..X, (∫ θ in Ioi 1, posTail Φ X θ * (posTail Φ X θ - posTail Φ k θ)) / k)
        - 2 * ∫ θ in Ioi 1, Real.log θ * posTail Φ X θ ^ 2 := by
  rw [Cvs.L2a.PositionTailPrimePairs.primeSide_posTail Φ hX hcont P R hPR, Cvs.L2a.LogPositionIdentity.pairs_eq Φ hX hcont]
  have hmin := Cvs.L2a.CutWeightResidual.min_form Φ hX
  have hlev := Cvs.L2a.LogPositionLevelForm.logPos_eq_levels Φ hX hcont
  have hL := Cvs.L2a.CutWeightResidual.integral_mul_posTail_sq Φ hX hcont (Cvs.L2a.CutWeightResidual.continuousOn_log_Icc X)
  have hML := min_levels Φ hX hcont
  have hsplit : ∑ a ∈ Finset.Icc 1 ⌊X⌋₊, ∑ n ∈ Finset.Icc 1 ⌊X⌋₊,
        ∫ θ in (1 : ℝ)..(X / (max a n : ℕ)), (Real.log (min a n : ℕ) - Real.log θ) * (Φ (a * θ) * Φ (n * θ))
      = (∑ a ∈ Finset.Icc 1 ⌊X⌋₊, ∑ n ∈ Finset.Icc 1 ⌊X⌋₊,
          ∫ θ in (1 : ℝ)..(X / (max a n : ℕ)), Real.log (min a n : ℕ) * (Φ (a * θ) * Φ (n * θ)))
        - ∑ a ∈ Finset.Icc 1 ⌊X⌋₊, ∑ n ∈ Finset.Icc 1 ⌊X⌋₊,
          ∫ θ in (1 : ℝ)..(X / (max a n : ℕ)), Real.log θ * (Φ (a * θ) * Φ (n * θ)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hb := Cvs.L2a.LogPositionIdentity.one_le_div_max hX ha hn
    have i1 := (Cvs.L2a.CutWeightResidual.continuousOn_weight_pair (g := fun _ => Real.log (min a n : ℕ)) hX
      hcont continuousOn_const ha hn).intervalIntegrable_of_Icc (μ := volume) hb
    have i2 := (Cvs.L2a.CutWeightResidual.continuousOn_weight_pair (g := Real.log) hX hcont
      (Cvs.L2a.CutWeightResidual.continuousOn_log_Icc X) ha hn).intervalIntegrable_of_Icc (μ := volume) hb
    rw [← intervalIntegral.integral_sub i1 i2]
    exact intervalIntegral.integral_congr fun θ _ => by ring
  have hk : (∫ k in (1 : ℝ)..X,
        ((∫ θ in Ioi 1, posTail Φ X θ ^ 2) - ∫ θ in Ioi 1, posTail Φ k θ ^ 2) / k)
      + (∫ k in (1 : ℝ)..X, (∫ θ in Ioi 1, (posTail Φ X θ - posTail Φ k θ) ^ 2) / k)
      = 2 * ∫ k in (1 : ℝ)..X, (∫ θ in Ioi 1, posTail Φ X θ * (posTail Φ X θ - posTail Φ k θ)) / k := by
    rw [intervalIntegral.integral_of_le hX, intervalIntegral.integral_of_le hX, intervalIntegral.integral_of_le hX,
      ← integral_add (integrableOn_levelN Φ hX hcont) (integrableOn_levelD Φ hcont),
      ← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioc fun k hk => ?_
    have h2 := two_integral_mul_sub Φ hk.1.le hk.2 hcont
    rw [← add_div, ← h2]
    ring
  rw [hlev, ← hk]
  linarith [hmin, hsplit, hL, hML]

end Cvs.L2a.PositionTailPrimeLevels
