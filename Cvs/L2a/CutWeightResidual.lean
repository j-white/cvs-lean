import Mathlib
import Cvs.L2a.FarMassPlateau
import Cvs.L2a.LogPositionIdentity
import Cvs.L2a.PositionTruncatedTail
import Cvs.L2a.ResonantConstantClosedForm
import Cvs.Upstream.LogHarmonicWeightBound

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The residual through a cut weight

`diagD − logResid = cutW + cutNS − cutC` for any weight `ω`, with `cutC ≥ 0` when `ω ≤ log` and
`cutW = ∫_1^X cutWeight·Φ² ≤ 0` when `0 ≤ ω = log` on `[t₂, ∞)`, `t₂ ≤ 2`; so `cutNS ≤ ε(−cutW) + C∫F²`
with `ε ≤ 1` gives `diagD − logResid ≤ C∫F²`.
-/

namespace Cvs.L2a.CutWeightResidual

open Real Set Finset MeasureTheory intervalIntegral Cvs.L2a.PositionTruncatedTail Cvs.L2a.LogPositionIdentity Cvs.Upstream.LogHarmonicWeightBound Cvs.L2a.FarMassPlateau

/-- The diagonal through the weight: `Σ_{n ≤ ⌊X⌋} ∫_1^{X/n} (log n − ω θ) Φ(nθ)²`. -/
noncomputable def cutW (ω Φ : ℝ → ℝ) (X : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, ∫ θ in (1 : ℝ)..(X / n), (Real.log n - ω θ) * Φ (n * θ) ^ 2

/-- The off-diagonal through the weight: `Σ_{a ≠ n ≤ ⌊X⌋} ∫_1^{X/max(a,n)} (log min(a,n) − ω θ) Φ(aθ) Φ(nθ)`. -/
noncomputable def cutNS (ω Φ : ℝ → ℝ) (X : ℝ) : ℝ :=
  ∑ a ∈ Finset.Icc 1 ⌊X⌋₊, ∑ n ∈ (Finset.Icc 1 ⌊X⌋₊).erase a,
    ∫ θ in (1 : ℝ)..(X / (max a n : ℕ)), (Real.log (min a n : ℕ) - ω θ) * (Φ (a * θ) * Φ (n * θ))

/-- The cut: `∫_{(1,∞)} (log θ − ω θ) F(θ)²` for the position-truncated tail `F`. -/
noncomputable def cutC (ω Φ : ℝ → ℝ) (X : ℝ) : ℝ :=
  ∫ θ in Set.Ioi 1, (Real.log θ - ω θ) * posTail Φ X θ ^ 2

/-- The cut weight `Σ_{n ≤ ⌊ξ⌋} (log n − ω(ξ/n))/n`. -/
noncomputable def cutWeight (ω : ℝ → ℝ) (ξ : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊ξ⌋₊, (Real.log n - ω (ξ / n)) / n

/-- The partial sum `Σ_{n ≤ N} log n / n`. -/
noncomputable def logSum (N : ℕ) : ℝ := ∑ n ∈ Finset.Icc 1 N, Real.log n / n

/-! ### The min form and the cut identity -/

/-- **The min form**: `diagD − logResid = Σ_{a,n ≤ ⌊X⌋} ∫_1^{X/max(a,n)} (log min(a,n) − log θ) Φ(aθ) Φ(nθ)`. -/
theorem min_form (Φ : ℝ → ℝ) {X : ℝ} (hX : 1 ≤ X) :
    diagD Φ X - logResid Φ X = ∑ a ∈ Finset.Icc 1 ⌊X⌋₊, ∑ n ∈ Finset.Icc 1 ⌊X⌋₊,
      ∫ θ in (1 : ℝ)..(X / (max a n : ℕ)),
        (Real.log (min a n : ℕ) - Real.log θ) * (Φ (a * θ) * Φ (n * θ)) := by
  set s := Finset.Icc 1 ⌊X⌋₊ with hs
  have hres : logResid Φ X = ∑ a ∈ s, ∑ n ∈ s,
      ((if a < n then residI Φ X a n else 0) + (if n < a then residI Φ X n a else 0)) := by
    have e1 : logResid Φ X = ∑ a ∈ s, ∑ n ∈ s, (if a < n then residI Φ X a n else 0)
        + ∑ a ∈ s, ∑ n ∈ s, (if a < n then residI Φ X a n else 0) := by
      show ∑ a ∈ s, ∑ n ∈ s.filter (fun n => a < n), 2 * residI Φ X a n = _
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Finset.sum_add_distrib, Finset.sum_filter]
      refine Finset.sum_congr rfl fun n _ => ?_
      split_ifs <;> ring
    have e2 : ∑ a ∈ s, ∑ n ∈ s, (if a < n then residI Φ X a n else 0)
        = ∑ a ∈ s, ∑ n ∈ s, (if n < a then residI Φ X n a else 0) := Finset.sum_comm
    rw [e1]
    nth_rewrite 2 [e2]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => by rw [← Finset.sum_add_distrib]
  have hdiag : diagD Φ X = ∑ a ∈ s, ∑ n ∈ s, (if a = n then diagI Φ X n else 0) := by
    show ∑ n ∈ s, diagI Φ X n = _
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [Finset.sum_ite_eq, if_pos ha]
  rw [hres, hdiag, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hle := one_le_div_max hX ha hn
  have hpos : ∀ θ ∈ uIcc (1 : ℝ) (X / (max a n : ℕ)), 0 < θ := fun θ hθ => by
    rw [uIcc_of_le hle] at hθ; linarith [hθ.1]
  have ha0 : (0 : ℝ) < a := by exact_mod_cast (Finset.mem_Icc.mp ha).1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  unfold residI diagI
  rcases lt_trichotomy a n with h | h | h
  · rw [if_neg h.ne, if_pos h, if_neg (not_lt.mpr h.le), max_eq_right h.le, min_eq_left h.le]
    rw [max_eq_right h.le] at hpos
    simp only [zero_sub, add_zero]
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun θ hθ => ?_
    have hθ := hpos θ hθ
    rw [Real.log_div hθ.ne' ha0.ne']
    ring
  · subst h
    rw [if_pos rfl, if_neg (lt_irrefl _), add_zero, sub_zero, max_self, min_self]
    exact intervalIntegral.integral_congr fun θ _ => by ring
  · rw [if_neg h.ne', if_neg (not_lt.mpr h.le), if_pos h, max_eq_left h.le, min_eq_right h.le]
    rw [max_eq_left h.le] at hpos
    simp only [zero_sub, zero_add]
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun θ hθ => ?_
    have hθ := hpos θ hθ
    rw [Real.log_div hθ.ne' hn0.ne']
    ring

/-- `log` is continuous on `[1, b]`. -/
theorem continuousOn_log_Icc (b : ℝ) : ContinuousOn Real.log (Icc 1 b) :=
  Real.continuousOn_log.mono fun _ hθ =>
    Set.mem_compl_singleton_iff.mpr (lt_of_lt_of_le one_pos hθ.1).ne'

/-- For `a, n ∈ [1, ⌊X⌋]` and `g` continuous on `[1, X]`, `g θ · Φ(aθ) Φ(nθ)` is continuous on
`[1, X/max(a,n)]`. -/
theorem continuousOn_weight_pair {Φ g : ℝ → ℝ} {X : ℝ} (hX : 1 ≤ X) (hcont : ContinuousOn Φ (Icc 1 X))
    (hg : ContinuousOn g (Icc 1 X)) {a n : ℕ} (ha : a ∈ Finset.Icc 1 ⌊X⌋₊) (hn : n ∈ Finset.Icc 1 ⌊X⌋₊) :
    ContinuousOn (fun θ => g θ * (Φ (a * θ) * Φ (n * θ))) (Icc 1 (X / (max a n : ℕ))) := by
  have hm1 : (1 : ℝ) ≤ ((max a n : ℕ) : ℝ) := by
    have : 1 ≤ max a n := le_trans (Finset.mem_Icc.mp ha).1 (le_max_left _ _)
    exact_mod_cast this
  exact (hg.mono (Icc_subset_Icc_right (div_le_self (by linarith) hm1))).mul
    (continuousOn_pair hcont (Finset.mem_Icc.mp ha).1 (Finset.mem_Icc.mp hn).1)

/-- **The weighted pairing formula**: for `1 ≤ X`, `Φ` and `g` continuous on `[1, X]`,
`∫_{(1,∞)} g F² = Σ_{a,n ≤ ⌊X⌋} ∫_1^{X/max(a,n)} g(θ) Φ(aθ) Φ(nθ)`. -/
theorem integral_mul_posTail_sq (Φ : ℝ → ℝ) {X : ℝ} (hX : 1 ≤ X) (hcont : ContinuousOn Φ (Icc 1 X))
    {g : ℝ → ℝ} (hg : ContinuousOn g (Icc 1 X)) :
    ∫ θ in Ioi 1, g θ * posTail Φ X θ ^ 2 = ∑ a ∈ Finset.Icc 1 ⌊X⌋₊, ∑ n ∈ Finset.Icc 1 ⌊X⌋₊,
      ∫ θ in (1 : ℝ)..(X / (max a n : ℕ)), g θ * (Φ (a * θ) * Φ (n * θ)) := by
  have hX0 : 0 ≤ X := by linarith
  have hpt : ∀ θ, g θ * posTail Φ X θ ^ 2 = ∑ a ∈ Finset.Icc 1 ⌊X⌋₊, ∑ n ∈ Finset.Icc 1 ⌊X⌋₊,
      Set.indicator (Ioc 1 (X / (max a n : ℕ))) (fun θ => g θ * (Φ (a * θ) * Φ (n * θ))) θ := by
    intro θ
    rw [sq, posTail_eq_sum, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast (Finset.mem_Icc.mp ha).1
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have hset : Ioc 1 (X / a) ∩ Ioc 1 (X / n) = Ioc 1 (X / ((max a n : ℕ) : ℝ)) := by
      ext θ
      simp only [Set.mem_inter_iff, Set.mem_Ioc]
      constructor
      · rintro ⟨⟨h1, h2⟩, -, h3⟩
        refine ⟨h1, ?_⟩
        rcases le_total a n with h | h
        · rw [max_eq_right h]; exact h3
        · rw [max_eq_left h]; exact h2
      · rintro ⟨h1, h2⟩
        have hma : (a : ℝ) ≤ ((max a n : ℕ) : ℝ) := by exact_mod_cast le_max_left a n
        have hmn : (n : ℝ) ≤ ((max a n : ℕ) : ℝ) := by exact_mod_cast le_max_right a n
        refine ⟨⟨h1, h2.trans ?_⟩, h1, h2.trans ?_⟩
        · exact div_le_div_of_nonneg_left hX0 (by linarith) hma
        · exact div_le_div_of_nonneg_left hX0 (by linarith) hmn
    rw [Set.indicator_mul_right _ g (fun θ => Φ (a * θ) * Φ (n * θ)), ← hset,
      Set.inter_indicator_mul (fun θ => Φ (a * θ)) (fun θ => Φ (n * θ))]
  have hint : ∀ a ∈ Finset.Icc 1 ⌊X⌋₊, ∀ n ∈ Finset.Icc 1 ⌊X⌋₊,
      Integrable (Set.indicator (Ioc 1 (X / (max a n : ℕ)))
        (fun θ => g θ * (Φ (a * θ) * Φ (n * θ)))) := fun a ha n hn =>
    (integrable_indicator_iff measurableSet_Ioc).mpr
      ((continuousOn_weight_pair hX hcont hg ha hn).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
  rw [setIntegral_congr_fun measurableSet_Ioi (fun θ _ => hpt θ),
    integral_finsetSum _ fun a ha => (integrable_finsetSum _ fun n hn => hint a ha n hn).integrableOn]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [integral_finsetSum _ fun n hn => (hint a ha n hn).integrableOn]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [setIntegral_indicator measurableSet_Ioc, Set.inter_eq_right.mpr Set.Ioc_subset_Ioi_self,
    intervalIntegral.integral_of_le (one_le_div_max hX ha hn)]

/-- The cut as a pair sum: `cutC = Σ_{a,n ≤ ⌊X⌋} ∫_1^{X/max(a,n)} (log θ − ω θ) Φ(aθ) Φ(nθ)`. -/
theorem cutC_eq (ω Φ : ℝ → ℝ) {X : ℝ} (hX : 1 ≤ X) (hcont : ContinuousOn Φ (Icc 1 X))
    (hω : ContinuousOn ω (Icc 1 X)) :
    cutC ω Φ X = ∑ a ∈ Finset.Icc 1 ⌊X⌋₊, ∑ n ∈ Finset.Icc 1 ⌊X⌋₊,
      ∫ θ in (1 : ℝ)..(X / (max a n : ℕ)), (Real.log θ - ω θ) * (Φ (a * θ) * Φ (n * θ)) :=
  integral_mul_posTail_sq Φ hX hcont (g := fun θ => Real.log θ - ω θ) ((continuousOn_log_Icc X).sub hω)

/-- **The cut identity**: `diagD − logResid = cutW + cutNS − cutC` for `Φ`, `ω` continuous on `[1, X]`. -/
theorem cut_identity (ω Φ : ℝ → ℝ) {X : ℝ} (hX : 1 ≤ X) (hcont : ContinuousOn Φ (Icc 1 X))
    (hω : ContinuousOn ω (Icc 1 X)) :
    diagD Φ X - logResid Φ X = cutW ω Φ X + cutNS ω Φ X - cutC ω Φ X := by
  set s := Finset.Icc 1 ⌊X⌋₊ with hs
  have hsplit : ∀ a ∈ s, ∀ n ∈ s,
      (∫ θ in (1 : ℝ)..(X / (max a n : ℕ)),
        (Real.log (min a n : ℕ) - Real.log θ) * (Φ (a * θ) * Φ (n * θ)))
      = (∫ θ in (1 : ℝ)..(X / (max a n : ℕ)), (Real.log (min a n : ℕ) - ω θ) * (Φ (a * θ) * Φ (n * θ)))
        - ∫ θ in (1 : ℝ)..(X / (max a n : ℕ)), (Real.log θ - ω θ) * (Φ (a * θ) * Φ (n * θ)) := by
    intro a ha n hn
    have hle := one_le_div_max hX ha hn
    have h1 := (continuousOn_weight_pair (g := fun θ => Real.log (min a n : ℕ) - ω θ) hX hcont
      (continuousOn_const.sub hω) ha hn).intervalIntegrable_of_Icc (μ := volume) hle
    have h2 := (continuousOn_weight_pair (g := fun θ => Real.log θ - ω θ) hX hcont
      ((continuousOn_log_Icc X).sub hω) ha hn).intervalIntegrable_of_Icc (μ := volume) hle
    rw [← intervalIntegral.integral_sub h1 h2]
    exact intervalIntegral.integral_congr fun θ _ => by ring
  have hWNS : ∑ a ∈ s, ∑ n ∈ s,
      (∫ θ in (1 : ℝ)..(X / (max a n : ℕ)), (Real.log (min a n : ℕ) - ω θ) * (Φ (a * θ) * Φ (n * θ)))
      = cutW ω Φ X + cutNS ω Φ X := by
    unfold cutW cutNS
    rw [← hs, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [← Finset.add_sum_erase s (fun n => ∫ θ in (1 : ℝ)..(X / (max a n : ℕ)),
      (Real.log (min a n : ℕ) - ω θ) * (Φ (a * θ) * Φ (n * θ))) ha]
    congr 1
    simp only [max_self, min_self]
    exact intervalIntegral.integral_congr fun θ _ => by ring
  rw [min_form Φ hX, cutC_eq ω Φ hX hcont hω, ← hs, ← hWNS, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun n hn => hsplit a ha n hn

/-- **The cut is nonnegative** when `ω ≤ log` on `[1, ∞)`. -/
theorem cutC_nonneg (ω Φ : ℝ → ℝ) (X : ℝ) (hω : ∀ θ, 1 ≤ θ → ω θ ≤ Real.log θ) : 0 ≤ cutC ω Φ X :=
  setIntegral_nonneg measurableSet_Ioi fun θ hθ =>
    mul_nonneg (sub_nonneg.mpr (hω θ (le_of_lt hθ))) (sq_nonneg _)

/-! ### The diagonal as an integral against the cut weight -/

/-- **The cut diagonal against the cut weight**: for `1 ≤ X`, `Φ` and `ω` continuous on `[1, X]`,
`cutW = ∫_1^X cutWeight(ξ) Φ(ξ)² dξ`. -/
theorem cutW_eq_integral (ω Φ : ℝ → ℝ) {X : ℝ} (hX : 1 ≤ X) (hcont : ContinuousOn Φ (Icc 1 X))
    (hω : ContinuousOn ω (Icc 1 X)) :
    cutW ω Φ X = ∫ ξ in (1 : ℝ)..X, cutWeight ω ξ * Φ ξ ^ 2 := by
  have hterm : ∀ n ∈ Finset.Icc 1 ⌊X⌋₊,
      (∫ θ in (1 : ℝ)..(X / n), (Real.log n - ω θ) * Φ (n * θ) ^ 2) = ∫ ξ in Icc 1 X, (n : ℝ)⁻¹ *
        Set.indicator (Icc (n : ℝ) X) (fun ξ => (Real.log n - ω (ξ / n)) * Φ ξ ^ 2) ξ := by
    intro n hn
    have hn' := Finset.mem_Icc.mp hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn'.1
    have hn0 : (0 : ℝ) < n := by linarith
    have hnX : (n : ℝ) ≤ X := (Nat.cast_le.mpr hn'.2).trans (Nat.floor_le (by linarith))
    have e : ∀ θ ∈ uIcc (1 : ℝ) (X / n), (Real.log n - ω θ) * Φ (n * θ) ^ 2
        = (fun ξ => (Real.log n - ω (ξ / n)) * Φ ξ ^ 2) ((n : ℝ) * θ) := by
      intro θ _
      simp only
      rw [mul_div_cancel_left₀ θ hn0.ne']
    rw [intervalIntegral.integral_congr e,
      intervalIntegral.integral_comp_mul_left (f := fun ξ => (Real.log n - ω (ξ / n)) * Φ ξ ^ 2) hn0.ne',
      mul_one, mul_div_cancel₀ _ hn0.ne', smul_eq_mul, MeasureTheory.integral_const_mul,
      setIntegral_indicator measurableSet_Icc, Set.inter_eq_right.mpr (Set.Icc_subset_Icc_left hn1),
      integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hnX]
  have hint : ∀ n ∈ Finset.Icc 1 ⌊X⌋₊, Integrable (fun ξ => (n : ℝ)⁻¹ *
      Set.indicator (Icc (n : ℝ) X) (fun ξ => (Real.log n - ω (ξ / n)) * Φ ξ ^ 2) ξ)
      (volume.restrict (Icc 1 X)) := by
    intro n hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have hn0 : (0 : ℝ) < n := by linarith
    have hmap : Set.MapsTo (fun ξ : ℝ => ξ / n) (Icc (n : ℝ) X) (Icc 1 X) := fun ξ hξ =>
      ⟨(one_le_div hn0).mpr hξ.1, (div_le_self (by linarith [hξ.1]) hn1).trans hξ.2⟩
    have hgc : ContinuousOn (fun ξ => (Real.log n - ω (ξ / n)) * Φ ξ ^ 2) (Icc (n : ℝ) X) :=
      (continuousOn_const.sub (hω.comp (continuousOn_id.div_const _) hmap)).mul
        ((hcont.mono (Set.Icc_subset_Icc_left hn1)).pow 2)
    have hI : Integrable (Set.indicator (Icc (n : ℝ) X)
        (fun ξ => (Real.log n - ω (ξ / n)) * Φ ξ ^ 2)) :=
      (integrable_indicator_iff measurableSet_Icc).mpr hgc.integrableOn_Icc
    exact hI.integrableOn.const_mul _
  have hsum : cutW ω Φ X = ∫ ξ in Icc 1 X, ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, (n : ℝ)⁻¹ *
      Set.indicator (Icc (n : ℝ) X) (fun ξ => (Real.log n - ω (ξ / n)) * Φ ξ ^ 2) ξ := by
    rw [integral_finsetSum _ hint]
    exact Finset.sum_congr rfl hterm
  rw [hsum, intervalIntegral.integral_of_le hX, ← integral_Icc_eq_integral_Ioc]
  refine setIntegral_congr_fun measurableSet_Icc fun ξ hξ => ?_
  have hξ0 : 0 ≤ ξ := by linarith [hξ.1]
  show ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, (n : ℝ)⁻¹ *
      Set.indicator (Icc (n : ℝ) X) (fun ξ => (Real.log n - ω (ξ / n)) * Φ ξ ^ 2) ξ
    = cutWeight ω ξ * Φ ξ ^ 2
  rw [cutWeight, Finset.sum_mul]
  have hsub : Finset.Icc 1 ⌊ξ⌋₊ = (Finset.Icc 1 ⌊X⌋₊).filter (fun n => n ≤ ⌊ξ⌋₊) := by
    have := Nat.floor_le_floor (R := ℝ) hξ.2
    ext n
    simp only [Finset.mem_Icc, Finset.mem_filter]
    omega
  rw [hsub, Finset.sum_filter]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases h : n ≤ ⌊ξ⌋₊
  · have hmem : ξ ∈ Icc (n : ℝ) X := ⟨(Nat.le_floor_iff hξ0).mp h, hξ.2⟩
    rw [if_pos h, Set.indicator_of_mem hmem]
    ring
  · have hmem : ξ ∉ Icc (n : ℝ) X := fun hm => h ((Nat.le_floor_iff hξ0).mpr hm.1)
    rw [if_neg h, Set.indicator_of_notMem hmem, mul_zero]

/-! ### The sign of the cut weight -/

/-- `logSum (N + 1) = logSum N + log (N + 1) / (N + 1)`. -/
theorem logSum_succ (N : ℕ) : logSum (N + 1) = logSum N + Real.log ((N : ℝ) + 1) / ((N : ℝ) + 1) := by
  unfold logSum; rw [Finset.sum_Icc_succ_top (by omega)]; push_cast; ring

/-- `harm (N + 1) = harm N + 1 / (N + 1)`. -/
theorem harm_succ (N : ℕ) : harm (N + 1) = harm N + 1 / ((N : ℝ) + 1) := by
  unfold harm; rw [Finset.sum_Icc_succ_top (by omega)]; push_cast; ring

/-- `logSum` is monotone. -/
theorem logSum_mono {N N' : ℕ} (h : N ≤ N') : logSum N ≤ logSum N' :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right h) fun n hn _ => by
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    exact div_nonneg (Real.log_nonneg hn1) (by linarith)

/-- The first values of `logSum`. -/
theorem logSum_values :
    logSum 1 = 0 ∧ logSum 2 = Real.log 2 / 2 ∧ logSum 3 = Real.log 2 / 2 + Real.log 3 / 3 ∧
      logSum 4 = Real.log 2 + Real.log 3 / 3 ∧
      logSum 5 = Real.log 2 + Real.log 3 / 3 + Real.log 5 / 5 := by
  have h0 : logSum 0 = 0 := by simp [logSum]
  have h1 : logSum 1 = 0 := by rw [logSum_succ, h0]; norm_num
  have h2 : logSum 2 = Real.log 2 / 2 := by rw [logSum_succ, h1]; norm_num
  have h3 : logSum 3 = Real.log 2 / 2 + Real.log 3 / 3 := by rw [logSum_succ, h2]; norm_num
  have h4 : logSum 4 = Real.log 2 + Real.log 3 / 3 := by
    rw [logSum_succ, h3]
    have : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    norm_num [this]; ring
  refine ⟨h1, h2, h3, h4, ?_⟩
  rw [logSum_succ, h4]; norm_num

/-- The first values of `harm`. -/
theorem harm_values : harm 0 = 0 ∧ harm 1 = 1 ∧ harm 2 = 3 / 2 ∧ harm 3 = 11 / 6 := by
  have h0 : harm 0 = 0 := by simp [harm]
  have h1 : harm 1 = 1 := by rw [harm_succ, h0]; norm_num
  have h2 : harm 2 = 3 / 2 := by rw [harm_succ, h1]; norm_num
  refine ⟨h0, h1, h2, ?_⟩
  rw [harm_succ, h2]; norm_num

/-- The gap `2 logSum M − H_M log M` is nonincreasing from `M = 1` on. -/
theorem gap_succ_le {M : ℕ} (hM : 1 ≤ M) :
    2 * logSum (M + 1) - harm (M + 1) * Real.log ((M + 1 : ℕ) : ℝ)
      ≤ 2 * logSum M - harm M * Real.log M := by
  rw [logSum_succ, harm_succ]
  push_cast
  have hN : (0 : ℝ) < M := by exact_mod_cast hM
  have hN1 : (0 : ℝ) < (M : ℝ) + 1 := by linarith
  have hlog : 1 / ((M : ℝ) + 1) ≤ Real.log ((M : ℝ) + 1) - Real.log M := by
    rw [← Real.log_div hN1.ne' hN.ne']
    have := Real.one_sub_inv_le_log_of_pos (show 0 < ((M : ℝ) + 1) / M by positivity)
    rw [inv_div] at this
    have e : 1 - (M : ℝ) / (M + 1) = 1 / (M + 1) := by field_simp; ring
    linarith
  have hL := log_succ_le_harm M
  have hL0 : 0 ≤ Real.log ((M : ℝ) + 1) := Real.log_nonneg (by linarith)
  have key : Real.log ((M : ℝ) + 1) * (1 / ((M : ℝ) + 1))
      ≤ harm M * (Real.log ((M : ℝ) + 1) - Real.log M) :=
    mul_le_mul hL hlog (by positivity) (hL0.trans hL)
  have e1 : Real.log ((M : ℝ) + 1) / ((M : ℝ) + 1) = Real.log ((M : ℝ) + 1) * (1 / ((M : ℝ) + 1)) := by ring
  rw [e1]
  nlinarith [key]

/-- For `M ≥ 3`, `2 logSum M − H_M log M ≤ log 2 − (7/6) log 3`. -/
theorem gap_le_three {M : ℕ} (hM : 3 ≤ M) :
    2 * logSum M - harm M * Real.log M ≤ Real.log 2 - 7 / 6 * Real.log 3 := by
  induction M, hM using Nat.le_induction with
  | base =>
    obtain ⟨-, -, h3, -, -⟩ := logSum_values
    obtain ⟨-, -, -, g3⟩ := harm_values
    rw [h3, g3]; push_cast; linarith
  | succ k hk ih => exact (gap_succ_le (by omega)).trans ih

/-- For `M ≥ 1`, `logSum (2M+1) ≤ logSum M + H_M log 2 + (log 3/3 − log 2/2)`: pair `2m+1` with `2m`. -/
theorem logSum_odd_le {M : ℕ} (hM : 1 ≤ M) :
    logSum (2 * M + 1) ≤ logSum M + harm M * Real.log 2 + (Real.log 3 / 3 - Real.log 2 / 2) := by
  induction M, hM using Nat.le_induction with
  | base =>
    obtain ⟨h1, -, h3, -, -⟩ := logSum_values
    obtain ⟨-, g1, -, -⟩ := harm_values
    rw [h3, h1, g1]; linarith
  | succ k hk ih =>
    rw [show 2 * (k + 1) + 1 = (2 * k + 1 + 1) + 1 by ring, logSum_succ, logSum_succ, logSum_succ k,
      harm_succ]
    push_cast
    have hk0 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have he : Real.exp 1 ≤ 2 * ((k : ℝ) + 1) := by linarith [Real.exp_one_lt_d9]
    have hanti : Real.log (2 * ((k : ℝ) + 1) + 1) / (2 * ((k : ℝ) + 1) + 1)
        ≤ Real.log (2 * ((k : ℝ) + 1)) / (2 * ((k : ℝ) + 1)) :=
      Real.log_div_self_antitoneOn (Set.mem_Ici.mpr he) (Set.mem_Ici.mpr (by linarith)) (by linarith)
    have hsplit : Real.log (2 * ((k : ℝ) + 1)) / (2 * ((k : ℝ) + 1))
        = (Real.log 2 + Real.log ((k : ℝ) + 1)) / (2 * ((k : ℝ) + 1)) := by
      rw [Real.log_mul (by norm_num) hk0.ne']
    have e1 : (2 : ℝ) * k + 1 + 1 = 2 * ((k : ℝ) + 1) := by ring
    have e2 : (2 : ℝ) * k + 2 + 1 = 2 * ((k : ℝ) + 1) + 1 := by ring
    rw [e1, e2]
    have e3 : (Real.log 2 + Real.log ((k : ℝ) + 1)) / (2 * ((k : ℝ) + 1))
        = (Real.log ((k : ℝ) + 1) / ((k : ℝ) + 1) + 1 / ((k : ℝ) + 1) * Real.log 2) / 2 := by
      field_simp; ring
    linarith

/-- For `N ≥ 2` and `ξ ≥ N`, `logSum N + logSum (N/2) − H_{N/2} log ξ ≤ −(log 2)/2`. -/
theorem w2_le {N : ℕ} (hN : 2 ≤ N) {ξ : ℝ} (hNξ : (N : ℝ) ≤ ξ) :
    logSum N + logSum (N / 2) - harm (N / 2) * Real.log ξ ≤ -(Real.log 2 / 2) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := logSum_values
  obtain ⟨-, g1, g2, -⟩ := harm_values
  have p1 : 3 * Real.log 2 ≤ 2 * Real.log 3 := by
    have := Real.log_le_log (by norm_num) (show (2 : ℝ) ^ 3 ≤ 3 ^ 2 by norm_num)
    rw [Real.log_pow, Real.log_pow] at this; norm_num at this; linarith
  have p2 : Real.log 3 ≤ 3 * Real.log 2 := by
    have := Real.log_le_log (by norm_num) (show (3 : ℝ) ≤ 2 ^ 3 by norm_num)
    rw [Real.log_pow] at this; norm_num at this; linarith
  have p3 : 6 * Real.log 2 ≤ 5 * Real.log 3 := by
    have := Real.log_le_log (by norm_num) (show (2 : ℝ) ^ 6 ≤ 3 ^ 5 by norm_num)
    rw [Real.log_pow, Real.log_pow] at this; norm_num at this; linarith
  have p4 : 60 * Real.log 2 + 10 * Real.log 3 ≤ 39 * Real.log 5 := by
    have := Real.log_le_log (by positivity) (show (2 : ℝ) ^ 60 * 3 ^ 10 ≤ 5 ^ 39 by norm_num)
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow] at this
    norm_num at this; linarith
  have hlogξ : Real.log N ≤ Real.log ξ := Real.log_le_log (by positivity) hNξ
  rcases (show N = 2 ∨ N = 3 ∨ N = 4 ∨ N = 5 ∨ 6 ≤ N by omega) with rfl | rfl | rfl | rfl | h6
  · rw [show (2 : ℕ) / 2 = 1 from rfl, h2, h1, g1]; norm_num at hlogξ; linarith
  · rw [show (3 : ℕ) / 2 = 1 from rfl, h3, h1, g1]; norm_num at hlogξ; linarith
  · have e4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    rw [show (4 : ℕ) / 2 = 2 from rfl, h4, h2, g2]; norm_num [e4] at hlogξ; linarith
  · rw [show (5 : ℕ) / 2 = 2 from rfl, h5, h2, g2]; norm_num at hlogξ; linarith
  · obtain ⟨M, hM⟩ : ∃ M, M = N / 2 := ⟨_, rfl⟩
    rw [← hM]
    have hM3 : 3 ≤ M := by omega
    have hmono : logSum N ≤ logSum (2 * M + 1) := logSum_mono (by omega)
    have hE := logSum_odd_le (M := M) (by omega)
    have hgap := gap_le_three hM3
    have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
    have h2M : ((2 * M : ℕ) : ℝ) ≤ ξ := le_trans (by exact_mod_cast (show 2 * M ≤ N by omega)) hNξ
    push_cast at h2M
    have hl : Real.log 2 + Real.log M ≤ Real.log ξ := by
      rw [← Real.log_mul (by norm_num) hM0.ne']; exact Real.log_le_log (by positivity) h2M
    have hH : 0 ≤ harm M := Finset.sum_nonneg fun m _ => by positivity
    have hprod : harm M * Real.log 2 + harm M * Real.log M ≤ harm M * Real.log ξ := by
      rw [← mul_add]; exact mul_le_mul_of_nonneg_left hl hH
    linarith

/-- **The cut weight is below the two-cut weight**: for `0 ≤ ω` on `[1, ∞)`, `ω = log` on `[t₂, ∞)` with `t₂ ≤ 2`
and `ξ ≥ 1`, `cutWeight ω ξ ≤ logSum ⌊ξ⌋ + logSum (⌊ξ⌋/2) − H_{⌊ξ⌋/2} log ξ`. -/
theorem cutWeight_le_w2 {ω : ℝ → ℝ} {t2 : ℝ} (ht2' : t2 ≤ 2) (hω0 : ∀ θ, 1 ≤ θ → 0 ≤ ω θ)
    (hωeq : ∀ θ, t2 ≤ θ → ω θ = Real.log θ) {ξ : ℝ} (hξ : 1 ≤ ξ) :
    cutWeight ω ξ ≤ logSum ⌊ξ⌋₊ + logSum (⌊ξ⌋₊ / 2) - harm (⌊ξ⌋₊ / 2) * Real.log ξ := by
  have hξ0 : 0 < ξ := by linarith
  have hterm : ∀ n ∈ Finset.Icc 1 ⌊ξ⌋₊, (Real.log n - ω (ξ / n)) / n
      ≤ Real.log n / n - (if 2 * n ≤ ⌊ξ⌋₊ then Real.log (ξ / n) / n else 0) := by
    intro n hn
    have hn' := Finset.mem_Icc.mp hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn'.1
    have hnξ : (n : ℝ) ≤ ξ := (Nat.le_floor_iff hξ0.le).mp hn'.2
    have h1 : 1 ≤ ξ / n := (one_le_div hn0).mpr hnξ
    split_ifs with h
    · have h2n : ((2 * n : ℕ) : ℝ) ≤ ξ := (Nat.le_floor_iff hξ0.le).mp h
      push_cast at h2n
      have h2 : t2 ≤ ξ / n := ht2'.trans ((le_div_iff₀ hn0).mpr h2n)
      rw [hωeq _ h2, sub_div]
    · have := div_nonneg (hω0 _ h1) hn0.le
      rw [sub_div, sub_zero]; linarith
  have hfilt : (Finset.Icc 1 ⌊ξ⌋₊).filter (fun n => 2 * n ≤ ⌊ξ⌋₊) = Finset.Icc 1 (⌊ξ⌋₊ / 2) := by
    ext n; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
  have hres : ∑ n ∈ Finset.Icc 1 (⌊ξ⌋₊ / 2), Real.log (ξ / n) / n
      = harm (⌊ξ⌋₊ / 2) * Real.log ξ - logSum (⌊ξ⌋₊ / 2) := by
    rw [harm, logSum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    rw [Real.log_div hξ0.ne' hn0.ne']; ring
  calc cutWeight ω ξ ≤ ∑ n ∈ Finset.Icc 1 ⌊ξ⌋₊,
        (Real.log n / n - (if 2 * n ≤ ⌊ξ⌋₊ then Real.log (ξ / n) / n else 0)) := Finset.sum_le_sum hterm
    _ = logSum ⌊ξ⌋₊ - ∑ n ∈ Finset.Icc 1 (⌊ξ⌋₊ / 2), Real.log (ξ / n) / n := by
      rw [Finset.sum_sub_distrib, ← Finset.sum_filter, hfilt]; rfl
    _ = _ := by rw [hres]; ring

/-- **The cut weight from `ξ = 2` on**: under the weight hypotheses, `cutWeight ω ξ ≤ −(log 2)/2` for `ξ ≥ 2`. -/
theorem cutWeight_le_two {ω : ℝ → ℝ} {t2 : ℝ} (ht2' : t2 ≤ 2) (hω0 : ∀ θ, 1 ≤ θ → 0 ≤ ω θ)
    (hωeq : ∀ θ, t2 ≤ θ → ω θ = Real.log θ) {ξ : ℝ} (hξ : 2 ≤ ξ) :
    cutWeight ω ξ ≤ -(Real.log 2 / 2) :=
  (cutWeight_le_w2 ht2' hω0 hωeq (by linarith)).trans
    (w2_le (Nat.le_floor (by exact_mod_cast hξ)) (Nat.floor_le (by linarith)))

/-- **The cut weight is nonpositive**: for `0 ≤ ω` on `[1, ∞)`, `ω = log` on `[t₂, ∞)` with `t₂ ≤ 2`, and `ξ ≥ 1`,
`cutWeight ω ξ ≤ 0`. -/
theorem cutWeight_nonpos {ω : ℝ → ℝ} {t2 : ℝ} (ht2' : t2 ≤ 2) (hω0 : ∀ θ, 1 ≤ θ → 0 ≤ ω θ)
    (hωeq : ∀ θ, t2 ≤ θ → ω θ = Real.log θ) {ξ : ℝ} (hξ : 1 ≤ ξ) : cutWeight ω ξ ≤ 0 := by
  by_cases h2 : ξ < 2
  · have hfl : ⌊ξ⌋₊ = 1 := (Nat.floor_eq_iff (by linarith)).mpr ⟨by norm_num; linarith, by norm_num; linarith⟩
    rw [cutWeight, hfl]
    simp only [Finset.Icc_self, Finset.sum_singleton, Nat.cast_one, Real.log_one, div_one, zero_sub]
    linarith [hω0 ξ hξ]
  · have := cutWeight_le_two ht2' hω0 hωeq (not_lt.mp h2)
    have := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
    linarith

/-- **The cut diagonal is nonpositive** under the weight hypotheses, for `Φ`, `ω` continuous on `[1, X]`. -/
theorem cutW_nonpos (ω Φ : ℝ → ℝ) {X t2 : ℝ} (hX : 1 ≤ X) (hcont : ContinuousOn Φ (Icc 1 X))
    (hω : ContinuousOn ω (Icc 1 X)) (ht2' : t2 ≤ 2) (hω0 : ∀ θ, 1 ≤ θ → 0 ≤ ω θ)
    (hωeq : ∀ θ, t2 ≤ θ → ω θ = Real.log θ) : cutW ω Φ X ≤ 0 := by
  rw [cutW_eq_integral ω Φ hX hcont hω]
  have := intervalIntegral.integral_nonneg (μ := volume) hX
    (f := fun ξ => -(cutWeight ω ξ * Φ ξ ^ 2)) fun ξ hξ =>
      neg_nonneg.mpr (mul_nonpos_of_nonpos_of_nonneg (cutWeight_nonpos ht2' hω0 hωeq hξ.1) (sq_nonneg _))
  rw [intervalIntegral.integral_neg] at this
  linarith

/-- **The residual from the off-diagonal bound**: under the weight hypotheses, `ε ≤ 1` and
`cutNS ≤ ε(−cutW) + C ∫F²`, `diagD − logResid ≤ C ∫F²`. -/
theorem R_star_of_NS (ω Φ : ℝ → ℝ) {X t2 ε C : ℝ} (hX : 1 ≤ X) (hcont : ContinuousOn Φ (Icc 1 X))
    (hω : ContinuousOn ω (Icc 1 X)) (hε1 : ε ≤ 1) (ht2' : t2 ≤ 2) (hω0 : ∀ θ, 1 ≤ θ → 0 ≤ ω θ)
    (hωle : ∀ θ, 1 ≤ θ → ω θ ≤ Real.log θ) (hωeq : ∀ θ, t2 ≤ θ → ω θ = Real.log θ)
    (hNS : cutNS ω Φ X ≤ ε * (-(cutW ω Φ X)) + C * ∫ θ in Set.Ioi 1, posTail Φ X θ ^ 2) :
    diagD Φ X - logResid Φ X ≤ C * ∫ θ in Set.Ioi 1, posTail Φ X θ ^ 2 := by
  rw [cut_identity ω Φ hX hcont hω]
  have hW := cutW_nonpos ω Φ hX hcont hω ht2' hω0 hωeq
  have hC := cutC_nonneg ω Φ X hωle
  nlinarith [mul_nonneg (sub_nonneg.mpr hε1) (neg_nonneg.mpr hW)]

end Cvs.L2a.CutWeightResidual
