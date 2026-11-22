import Mathlib

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The position-truncated tail and its pairing formula

The tail `Σ_{m ≤ ⌊X⌋} Φ(mθ)` on `(1, X]` with each mode cut at `mθ ≤ X` is the masked sum of Cvs.L2a.PlateauAssemblyTrivialGain with masks
`Iic (X/m)`; it is supported on `(1, X]`, its products with itself, its integer dilates and continuous weights are
integrable on `(1, ∞)`, and `∫ F(θ) F(kθ) = Σ_a Σ_{km ≤ ⌊X⌋} ∫_1^{X/max(a,km)} Φ(aθ) Φ(kmθ)`.
-/

namespace Cvs.L2a.PositionTruncatedTail

open Real Set Finset MeasureTheory intervalIntegral

/-- The position-truncated tail: on `(1, X]`, the sum over `m ≤ ⌊X⌋` of the modes `Φ(mθ)` cut at `θ ≤ X/m`. -/
noncomputable def posTail (Φ : ℝ → ℝ) (X θ : ℝ) : ℝ :=
  Set.indicator (Set.Ioc 1 X)
    (fun θ => ∑ m ∈ Finset.Icc 1 ⌊X⌋₊, Set.indicator (Set.Iic (X / m)) (fun θ => Φ (m * θ)) θ) θ

/-- The pair integral `∫_1^{X/max(a,n)} Φ(aθ) Φ(nθ)`. -/
noncomputable def pairI (Φ : ℝ → ℝ) (X : ℝ) (a n : ℕ) : ℝ :=
  ∫ θ in (1 : ℝ)..(X / (max a n : ℕ)), Φ (a * θ) * Φ (n * θ)

/-- The position-truncated tail vanishes for `θ ≤ 1`. -/
theorem posTail_zero (Φ : ℝ → ℝ) (X : ℝ) {θ : ℝ} (hθ : θ ≤ 1) : posTail Φ X θ = 0 :=
  indicator_of_notMem (fun h : θ ∈ Ioc 1 X => not_lt.mpr hθ h.1) _

/-- The position-truncated tail vanishes for `θ > X`. -/
theorem posTail_of_gt (Φ : ℝ → ℝ) {X θ : ℝ} (hθ : X < θ) : posTail Φ X θ = 0 :=
  indicator_of_notMem (fun h : θ ∈ Ioc 1 X => not_le.mpr hθ h.2) _

/-- The position-truncated tail is the sum of the modes `Φ(mθ)` restricted to `(1, X/m]`. -/
theorem posTail_eq_sum (Φ : ℝ → ℝ) (X θ : ℝ) :
    posTail Φ X θ = ∑ m ∈ Finset.Icc 1 ⌊X⌋₊, Set.indicator (Ioc 1 (X / m)) (fun θ => Φ (m * θ)) θ := by
  unfold posTail
  by_cases hθ : θ ∈ Ioc 1 X
  · rw [indicator_of_mem hθ]
    refine Finset.sum_congr rfl fun m _ => ?_
    by_cases h : θ ≤ X / m
    · rw [indicator_of_mem (show θ ∈ Iic (X / m) from h),
        indicator_of_mem (show θ ∈ Ioc 1 (X / m) from ⟨hθ.1, h⟩)]
    · rw [indicator_of_notMem (show θ ∉ Iic (X / m) from h), indicator_of_notMem (fun h' : θ ∈ Ioc 1 (X / m) => h h'.2)]
  · rw [indicator_of_notMem hθ]
    symm
    refine Finset.sum_eq_zero fun m hm => indicator_of_notMem (fun h' : θ ∈ Ioc 1 (X / m) => hθ ⟨h'.1, ?_⟩) _
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
    have hX : 0 ≤ X := by
      have h1 : 1 < X / m := lt_of_lt_of_le h'.1 h'.2
      have := (lt_div_iff₀ (by linarith : (0 : ℝ) < m)).mp h1
      linarith
    exact h'.2.trans (div_le_self hX hm1)

/-- For `1 ≤ a, n`, the pair product `Φ(aθ) Φ(nθ)` is integrable on `[1, X/max(a,n)]`. -/
theorem integrableOn_pair {Φ : ℝ → ℝ} {X : ℝ} (hcont : ContinuousOn Φ (Icc 1 X)) {a n : ℕ}
    (ha : 1 ≤ a) (hn : 1 ≤ n) :
    IntegrableOn (fun θ => Φ (a * θ) * Φ (n * θ)) (Icc 1 (X / (max a n : ℕ))) := by
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : (0 : ℝ) < ((max a n : ℕ) : ℝ) := by
    rw [Nat.cast_max]; exact lt_of_lt_of_le one_pos (ha1.trans (le_max_left _ _))
  have hmap : ∀ θ ∈ Icc 1 (X / (max a n : ℕ)), (a : ℝ) * θ ≤ X ∧ (n : ℝ) * θ ≤ X := by
    intro θ hθ
    have h := (le_div_iff₀ hpos).mp hθ.2
    rw [Nat.cast_max, mul_max_of_nonneg _ _ (by linarith [hθ.1]), max_le_iff] at h
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  refine ContinuousOn.integrableOn_Icc (ContinuousOn.mul ?_ ?_)
  · refine hcont.comp (continuousOn_const.mul continuousOn_id) fun θ hθ => ?_
    exact ⟨by nlinarith [hθ.1], (hmap θ hθ).1⟩
  · refine hcont.comp (continuousOn_const.mul continuousOn_id) fun θ hθ => ?_
    exact ⟨by nlinarith [hθ.1], (hmap θ hθ).2⟩

/-- For `θ > 1` and `k ≥ 1`, the product of the tail with its `k`-th dilate is the double sum over `a ≤ ⌊X⌋`
and `km ≤ ⌊X⌋` of `Φ(aθ) Φ(kmθ)` restricted to `(1, X/max(a, km)]`. -/
theorem posTail_mul_dilate_eq (Φ : ℝ → ℝ) {X θ : ℝ} {k : ℕ} (hk : 1 ≤ k) (hθ : 1 < θ) :
    posTail Φ X θ * posTail Φ X (k * θ)
      = ∑ a ∈ Finset.Icc 1 ⌊X⌋₊, ∑ m ∈ (Finset.Icc 1 ⌊X⌋₊).filter (fun m => k * m ≤ ⌊X⌋₊),
          Set.indicator (Ioc 1 (X / (max a (k * m) : ℕ)))
            (fun θ => Φ (a * θ) * Φ (((k * m : ℕ) : ℝ) * θ)) θ := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkθ : 1 < (k : ℝ) * θ := by nlinarith
  have hdil : posTail Φ X (k * θ) = ∑ m ∈ (Finset.Icc 1 ⌊X⌋₊).filter (fun m => k * m ≤ ⌊X⌋₊),
      Set.indicator (Ioc 1 (X / m)) (fun θ => Φ (m * θ)) (k * θ) := by
    rw [posTail_eq_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun m hm => ?_
    split_ifs with h
    · rfl
    · refine indicator_of_notMem (fun h' => ?_) _
      have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
      have h2 : (k : ℝ) * θ * m ≤ X := (le_div_iff₀ (by linarith)).mp h'.2
      have hX : X < ((k * m : ℕ) : ℝ) := by
        have h3 : ⌊X⌋₊ + 1 ≤ k * m := by omega
        have h4 : ((⌊X⌋₊ + 1 : ℕ) : ℝ) ≤ ((k * m : ℕ) : ℝ) := by exact_mod_cast h3
        push_cast at h4 ⊢
        linarith [Nat.lt_floor_add_one X]
      push_cast at hX
      have h6 : 0 ≤ (k : ℝ) * m * (θ - 1) := mul_nonneg (by positivity) (by linarith)
      have h5 : (k : ℝ) * m ≤ (k : ℝ) * θ * m := by nlinarith
      linarith
  rw [posTail_eq_sum, hdil, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun m hm => ?_
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast (Finset.mem_Icc.mp ha).1
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).1
  have hmax : (0 : ℝ) < ((max a (k * m) : ℕ) : ℝ) := by
    rw [Nat.cast_max]; exact lt_of_lt_of_le one_pos (ha1.trans (le_max_left _ _))
  have hiff : (θ ≤ X / a ∧ (k : ℝ) * θ ≤ X / m) ↔ θ ≤ X / ((max a (k * m) : ℕ) : ℝ) := by
    rw [le_div_iff₀ (by linarith), le_div_iff₀ (by linarith), le_div_iff₀ hmax, Nat.cast_max,
      mul_max_of_nonneg _ _ (by linarith), max_le_iff]
    push_cast
    have e : (k : ℝ) * θ * m = θ * (k * m) := by ring
    rw [e]
  by_cases h : θ ≤ X / ((max a (k * m) : ℕ) : ℝ)
  · obtain ⟨h1, h2⟩ := hiff.mpr h
    rw [indicator_of_mem (show θ ∈ Ioc 1 (X / a) from ⟨hθ, h1⟩),
      indicator_of_mem (show (k : ℝ) * θ ∈ Ioc 1 (X / m) from ⟨hkθ, h2⟩),
      indicator_of_mem (show θ ∈ Ioc 1 (X / ((max a (k * m) : ℕ) : ℝ)) from ⟨hθ, h⟩)]
    rw [show (m : ℝ) * (k * θ) = ((k * m : ℕ) : ℝ) * θ by push_cast; ring]
  · rw [indicator_of_notMem (show θ ∉ Ioc 1 (X / ((max a (k * m) : ℕ) : ℝ)) from fun h' => h h'.2)]
    by_cases h1 : θ ≤ X / a
    · have h2 : ¬ (k : ℝ) * θ ≤ X / m := fun h2 => h (hiff.mp ⟨h1, h2⟩)
      rw [indicator_of_notMem (show (k : ℝ) * θ ∉ Ioc 1 (X / m) from fun h' => h2 h'.2), mul_zero]
    · rw [indicator_of_notMem (show θ ∉ Ioc 1 (X / a) from fun h' => h1 h'.2), zero_mul]

/-- Each term of the double sum in `posTail_mul_dilate_eq` is integrable. -/
theorem integrable_pair_indicator {Φ : ℝ → ℝ} {X : ℝ} (hcont : ContinuousOn Φ (Icc 1 X)) {a n : ℕ}
    (ha : 1 ≤ a) (hn : 1 ≤ n) :
    Integrable (Set.indicator (Ioc 1 (X / (max a n : ℕ))) (fun θ => Φ (a * θ) * Φ (n * θ))) :=
  (integrable_indicator_iff measurableSet_Ioc).mpr ((integrableOn_pair hcont ha hn).mono_set Ioc_subset_Icc_self)

/-- **The product of the tail with its `k`-th dilate is integrable on `(1, ∞)`** for `Φ` continuous on `[1, X]`. -/
theorem integrableOn_posTail_mul_dilate (Φ : ℝ → ℝ) {X : ℝ} (hcont : ContinuousOn Φ (Icc 1 X)) {k : ℕ}
    (hk : 1 ≤ k) :
    IntegrableOn (fun θ => posTail Φ X θ * posTail Φ X (k * θ)) (Ioi 1) := by
  refine IntegrableOn.congr_fun ?_ (fun θ hθ => (posTail_mul_dilate_eq Φ hk hθ).symm) measurableSet_Ioi
  refine (integrable_finsetSum _ fun a ha => integrable_finsetSum _ fun m hm => ?_).integrableOn
  have ha1 := (Finset.mem_Icc.mp ha).1
  have hm1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).1
  exact integrable_pair_indicator hcont ha1 (Nat.one_le_iff_ne_zero.mpr (by positivity))

/-- **The square of the position-truncated tail is integrable on `(1, ∞)`** for `Φ` continuous on `[1, X]`. -/
theorem integrableOn_posTail_sq (Φ : ℝ → ℝ) {X : ℝ} (hcont : ContinuousOn Φ (Icc 1 X)) :
    IntegrableOn (fun θ => posTail Φ X θ ^ 2) (Ioi 1) := by
  simpa only [sq, Nat.cast_one, one_mul] using integrableOn_posTail_mul_dilate Φ hcont le_rfl

/-- **The tail times a weight continuous on `[1, X]` is integrable on `(1, ∞)`** for `Φ` continuous on `[1, X]`. -/
theorem integrableOn_posTail_mul (Φ : ℝ → ℝ) {X : ℝ} (hcont : ContinuousOn Φ (Icc 1 X)) {g : ℝ → ℝ}
    (hg : ContinuousOn g (Icc 1 X)) :
    IntegrableOn (fun θ => posTail Φ X θ * g θ) (Ioi 1) := by
  have hpt : (fun θ => posTail Φ X θ * g θ)
      = fun θ => ∑ m ∈ Finset.Icc 1 ⌊X⌋₊, Set.indicator (Ioc 1 (X / m)) (fun θ => Φ (m * θ) * g θ) θ := by
    funext θ
    rw [posTail_eq_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    by_cases h : θ ∈ Ioc 1 (X / m)
    · rw [indicator_of_mem h, indicator_of_mem h]
    · rw [indicator_of_notMem h, indicator_of_notMem h, zero_mul]
  rw [hpt]
  refine (integrable_finsetSum _ fun m hm => ?_).integrableOn
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
  have hmap : ∀ θ ∈ Icc 1 (X / m), (m : ℝ) * θ ∈ Icc 1 X ∧ θ ∈ Icc 1 X := by
    intro θ hθ
    have h := (le_div_iff₀ (by linarith : (0 : ℝ) < m)).mp hθ.2
    refine ⟨⟨by nlinarith [hθ.1], by linarith⟩, ⟨hθ.1, ?_⟩⟩
    nlinarith [hθ.1]
  have hc : ContinuousOn (fun θ => Φ (m * θ) * g θ) (Icc 1 (X / m)) :=
    ContinuousOn.mul (hcont.comp (continuousOn_const.mul continuousOn_id) fun θ hθ => (hmap θ hθ).1)
      (hg.mono fun θ hθ => (hmap θ hθ).2)
  exact (integrable_indicator_iff measurableSet_Ioc).mpr (hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self)

/-- **The pairing formula**: for `1 ≤ X`, `Φ` continuous on `[1, X]` and `k ≥ 1`,
`∫_{(1,∞)} F(θ) F(kθ) = Σ_{a ≤ ⌊X⌋} Σ_{m ≤ ⌊X⌋, km ≤ ⌊X⌋} ∫_1^{X/max(a,km)} Φ(aθ) Φ(kmθ)`. -/
theorem integral_posTail_mul_dilate (Φ : ℝ → ℝ) {X : ℝ} (hX : 1 ≤ X) (hcont : ContinuousOn Φ (Icc 1 X))
    {k : ℕ} (hk : 1 ≤ k) :
    ∫ θ in Ioi 1, posTail Φ X θ * posTail Φ X (k * θ)
      = ∑ a ∈ Finset.Icc 1 ⌊X⌋₊, ∑ m ∈ (Finset.Icc 1 ⌊X⌋₊).filter (fun m => k * m ≤ ⌊X⌋₊),
          pairI Φ X a (k * m) := by
  have hint : ∀ a ∈ Finset.Icc 1 ⌊X⌋₊, ∀ m ∈ (Finset.Icc 1 ⌊X⌋₊).filter (fun m => k * m ≤ ⌊X⌋₊),
      Integrable (Set.indicator (Ioc 1 (X / (max a (k * m) : ℕ)))
        (fun θ => Φ (a * θ) * Φ (((k * m : ℕ) : ℝ) * θ))) := by
    intro a ha m hm
    have ha1 := (Finset.mem_Icc.mp ha).1
    have hm1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).1
    exact integrable_pair_indicator hcont ha1 (Nat.one_le_iff_ne_zero.mpr (by positivity))
  rw [setIntegral_congr_fun measurableSet_Ioi (fun θ hθ => posTail_mul_dilate_eq Φ hk hθ),
    integral_finsetSum _ fun a ha => (integrable_finsetSum _ fun m hm => hint a ha m hm).integrableOn]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [integral_finsetSum _ fun m hm => (hint a ha m hm).integrableOn]
  refine Finset.sum_congr rfl fun m hm => ?_
  have ha' := Finset.mem_Icc.mp ha
  have hkm := (Finset.mem_filter.mp hm).2
  have hle : (1 : ℝ) ≤ X / ((max a (k * m) : ℕ) : ℝ) := by
    have hmaxle : ((max a (k * m) : ℕ) : ℝ) ≤ X :=
      le_trans (by exact_mod_cast max_le ha'.2 hkm) (Nat.floor_le (by linarith))
    have hpos : (0 : ℝ) < ((max a (k * m) : ℕ) : ℝ) := by
      have : 1 ≤ max a (k * m) := le_trans ha'.1 (le_max_left _ _)
      exact_mod_cast this
    rw [le_div_iff₀ hpos]; linarith
  rw [setIntegral_indicator measurableSet_Ioc, Set.inter_eq_right.mpr Set.Ioc_subset_Ioi_self, pairI,
    intervalIntegral.integral_of_le hle]

end Cvs.L2a.PositionTruncatedTail
