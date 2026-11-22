import Mathlib
import Cvs.L2a.PositionTruncatedTail

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The log-position identity and the sign of the diagonal

`Σ_{a,n ≤ ⌊X⌋} 2 log n · pairI a n = logPos + diagD − logResid`, and `diagD ≤ 0` by the weight lemma of Cvs.Upstream.LogHarmonicWeightBound,
so the pair sum is at most `logPos − logResid`.
-/

namespace Cvs.L2a.LogPositionIdentity

open Real Set Finset MeasureTheory intervalIntegral Cvs.L2a.PositionTruncatedTail

/-- The log-position sum `Σ_{a,n ≤ ⌊X⌋} ∫_1^{X/max(a,n)} log(max(a,n) θ) Φ(aθ) Φ(nθ)`. -/
noncomputable def logPos (Φ : ℝ → ℝ) (X : ℝ) : ℝ :=
  ∑ a ∈ Finset.Icc 1 ⌊X⌋₊, ∑ n ∈ Finset.Icc 1 ⌊X⌋₊,
    ∫ θ in (1 : ℝ)..(X / (max a n : ℕ)), Real.log ((max a n : ℕ) * θ) * (Φ (a * θ) * Φ (n * θ))

/-- The single residual integral `∫_1^{X/n} log(θ/a) Φ(aθ) Φ(nθ)`. -/
noncomputable def residI (Φ : ℝ → ℝ) (X : ℝ) (a n : ℕ) : ℝ :=
  ∫ θ in (1 : ℝ)..(X / n), Real.log (θ / a) * (Φ (a * θ) * Φ (n * θ))

/-- The off-diagonal residual `Σ_{a < n ≤ ⌊X⌋} 2 ∫_1^{X/n} log(θ/a) Φ(aθ) Φ(nθ)`. -/
noncomputable def logResid (Φ : ℝ → ℝ) (X : ℝ) : ℝ :=
  ∑ a ∈ Finset.Icc 1 ⌊X⌋₊, ∑ n ∈ (Finset.Icc 1 ⌊X⌋₊).filter (fun n => a < n),
    2 * ∫ θ in (1 : ℝ)..(X / n), Real.log (θ / a) * (Φ (a * θ) * Φ (n * θ))

/-- The single diagonal integral `∫_1^{X/n} (log n − log θ) Φ(nθ)²`. -/
noncomputable def diagI (Φ : ℝ → ℝ) (X : ℝ) (n : ℕ) : ℝ :=
  ∫ θ in (1 : ℝ)..(X / n), (Real.log n - Real.log θ) * Φ (n * θ) ^ 2

/-- The diagonal `Σ_{n ≤ ⌊X⌋} ∫_1^{X/n} (log n − log θ) Φ(nθ)²`. -/
noncomputable def diagD (Φ : ℝ → ℝ) (X : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, ∫ θ in (1 : ℝ)..(X / n), (Real.log n - Real.log θ) * Φ (n * θ) ^ 2

/-- The pair integral is symmetric: `pairI Φ X a n = pairI Φ X n a`. -/
theorem pairI_comm (Φ : ℝ → ℝ) (X : ℝ) (a n : ℕ) : pairI Φ X a n = pairI Φ X n a := by
  unfold pairI
  rw [max_comm]
  exact intervalIntegral.integral_congr fun θ _ => mul_comm _ _

/-- For `1 ≤ X` and `a, n ∈ [1, ⌊X⌋]`, the upper limit `X / max(a, n)` is at least `1`. -/
theorem one_le_div_max {X : ℝ} (hX : 1 ≤ X) {a n : ℕ} (ha : a ∈ Finset.Icc 1 ⌊X⌋₊)
    (hn : n ∈ Finset.Icc 1 ⌊X⌋₊) : 1 ≤ X / ((max a n : ℕ) : ℝ) := by
  have ha' := Finset.mem_Icc.mp ha
  have hn' := Finset.mem_Icc.mp hn
  have hmaxle : ((max a n : ℕ) : ℝ) ≤ X :=
    le_trans (by exact_mod_cast max_le ha'.2 hn'.2) (Nat.floor_le (by linarith))
  have hpos : (0 : ℝ) < ((max a n : ℕ) : ℝ) := by
    have : 1 ≤ max a n := le_trans ha'.1 (le_max_left _ _)
    exact_mod_cast this
  rw [le_div_iff₀ hpos]; linarith

/-- For `1 ≤ a, n`, the pair product `Φ(aθ) Φ(nθ)` is continuous on `[1, X/max(a,n)]`. -/
theorem continuousOn_pair {Φ : ℝ → ℝ} {X : ℝ} (hcont : ContinuousOn Φ (Icc 1 X)) {a n : ℕ}
    (ha : 1 ≤ a) (hn : 1 ≤ n) :
    ContinuousOn (fun θ => Φ (a * θ) * Φ (n * θ)) (Icc 1 (X / (max a n : ℕ))) := by
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : (0 : ℝ) < ((max a n : ℕ) : ℝ) := by
    rw [Nat.cast_max]; exact lt_of_lt_of_le one_pos (ha1.trans (le_max_left _ _))
  have hmap : ∀ θ ∈ Icc 1 (X / (max a n : ℕ)), (a : ℝ) * θ ≤ X ∧ (n : ℝ) * θ ≤ X := by
    intro θ hθ
    have h := (le_div_iff₀ hpos).mp hθ.2
    rw [Nat.cast_max, mul_max_of_nonneg _ _ (by linarith [hθ.1]), max_le_iff] at h
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  refine ContinuousOn.mul ?_ ?_
  · refine hcont.comp (continuousOn_const.mul continuousOn_id) fun θ hθ => ?_
    exact ⟨by nlinarith [hθ.1], (hmap θ hθ).1⟩
  · refine hcont.comp (continuousOn_const.mul continuousOn_id) fun θ hθ => ?_
    exact ⟨by nlinarith [hθ.1], (hmap θ hθ).2⟩

/-- `θ ↦ log (cθ)` is continuous on `[1, b]` for `c > 0`. -/
theorem continuousOn_log_mul {c : ℝ} (hc : 0 < c) (b : ℝ) :
    ContinuousOn (fun θ => Real.log (c * θ)) (Icc 1 b) :=
  (continuousOn_const.mul continuousOn_id).log fun _ hθ =>
    (mul_pos hc (lt_of_lt_of_le one_pos hθ.1)).ne'

/-- `θ ↦ log (θ/c)` is continuous on `[1, b]` for `c > 0`. -/
theorem continuousOn_log_div {c : ℝ} (hc : 0 < c) (b : ℝ) :
    ContinuousOn (fun θ => Real.log (θ / c)) (Icc 1 b) :=
  (continuousOn_id.div_const c).log fun _ hθ => (div_pos (lt_of_lt_of_le one_pos hθ.1) hc).ne'

/-- `θ ↦ log c − log θ` is continuous on `[1, b]`. -/
theorem continuousOn_const_sub_log (c b : ℝ) :
    ContinuousOn (fun θ => c - Real.log θ) (Icc 1 b) :=
  continuousOn_const.sub (Real.continuousOn_log.mono fun _ hθ =>
    Set.mem_compl_singleton_iff.mpr (lt_of_lt_of_le one_pos hθ.1).ne')

/-- **The pair identity for one ordered pair**: `(log a + log n) · pairI a n` equals the log-position integral plus
the diagonal integral (when `a = n`) minus the residual integral of the pair ordered by size (when `a ≠ n`). -/
theorem pair_term {Φ : ℝ → ℝ} {X : ℝ} (hX : 1 ≤ X) (hcont : ContinuousOn Φ (Icc 1 X)) {a n : ℕ}
    (ha : a ∈ Finset.Icc 1 ⌊X⌋₊) (hn : n ∈ Finset.Icc 1 ⌊X⌋₊) :
    (Real.log a + Real.log n) * pairI Φ X a n
      = (∫ θ in (1 : ℝ)..(X / (max a n : ℕ)), Real.log ((max a n : ℕ) * θ) * (Φ (a * θ) * Φ (n * θ)))
        + (if a = n then diagI Φ X n else 0)
        - (if a < n then residI Φ X a n else 0) - (if n < a then residI Φ X n a else 0) := by
  have ha1 : 1 ≤ a := (Finset.mem_Icc.mp ha).1
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hle := one_le_div_max hX ha hn
  have hII : ∀ g : ℝ → ℝ, ContinuousOn g (Icc 1 (X / (max a n : ℕ))) →
      IntervalIntegrable (fun θ => g θ * (Φ (a * θ) * Φ (n * θ))) volume 1 (X / (max a n : ℕ)) :=
    fun g hg => (hg.mul (continuousOn_pair hcont ha1 hn1)).intervalIntegrable_of_Icc hle
  have hmpos : (0 : ℝ) < ((max a n : ℕ) : ℝ) := by
    rw [Nat.cast_max]; exact lt_of_lt_of_le ha0 (le_max_left _ _)
  have hL := hII _ (continuousOn_log_mul hmpos _)
  have hpos : ∀ θ ∈ uIcc (1 : ℝ) (X / (max a n : ℕ)), 0 < θ := fun θ hθ => by
    rw [uIcc_of_le hle] at hθ; linarith [hθ.1]
  unfold pairI residI diagI
  rw [← intervalIntegral.integral_const_mul]
  rcases lt_trichotomy a n with h | h | h
  · have hm : ((max a n : ℕ) : ℝ) = n := by rw [max_eq_right h.le]
    have hR := hII _ (continuousOn_log_div ha0 _)
    rw [if_neg h.ne, if_pos h, if_neg (not_lt.mpr h.le), add_zero, sub_zero]
    rw [hm] at hL hR hpos ⊢
    rw [← intervalIntegral.integral_sub hL hR]
    refine intervalIntegral.integral_congr fun θ hθ => ?_
    have hθ := hpos θ hθ
    rw [Real.log_mul hn0.ne' hθ.ne', Real.log_div hθ.ne' ha0.ne']
    ring
  · subst h
    have hm : ((max a a : ℕ) : ℝ) = a := by rw [max_self]
    have hD := hII _ (continuousOn_const_sub_log (Real.log a) _)
    rw [if_pos rfl, if_neg (lt_irrefl _), sub_zero, sub_zero]
    rw [hm] at hL hD hpos ⊢
    have e : ∫ θ in (1 : ℝ)..(X / a), (Real.log a - Real.log θ) * Φ (a * θ) ^ 2
        = ∫ θ in (1 : ℝ)..(X / a), (Real.log a - Real.log θ) * (Φ (a * θ) * Φ (a * θ)) :=
      intervalIntegral.integral_congr fun _ _ => by ring
    rw [e, ← intervalIntegral.integral_add hL hD]
    refine intervalIntegral.integral_congr fun θ hθ => ?_
    have hθ := hpos θ hθ
    rw [Real.log_mul ha0.ne' hθ.ne']
    ring
  · have hm : ((max a n : ℕ) : ℝ) = a := by rw [max_eq_left h.le]
    have hR := hII _ (continuousOn_log_div hn0 _)
    rw [if_neg h.ne', if_neg (not_lt.mpr h.le), if_pos h, add_zero, sub_zero]
    rw [hm] at hL hR hpos ⊢
    have e : ∫ θ in (1 : ℝ)..(X / a), Real.log (θ / n) * (Φ (n * θ) * Φ (a * θ))
        = ∫ θ in (1 : ℝ)..(X / a), Real.log (θ / n) * (Φ (a * θ) * Φ (n * θ)) :=
      intervalIntegral.integral_congr fun _ _ => by ring
    rw [e, ← intervalIntegral.integral_sub hL hR]
    refine intervalIntegral.integral_congr fun θ hθ => ?_
    have hθ := hpos θ hθ
    rw [Real.log_mul ha0.ne' hθ.ne', Real.log_div hθ.ne' hn0.ne']
    ring

/-- **The log-position identity**: `Σ_{a,n ≤ ⌊X⌋} 2 log n · pairI a n = logPos + diagD − logResid`. -/
theorem pairs_eq (Φ : ℝ → ℝ) {X : ℝ} (hX : 1 ≤ X) (hcont : ContinuousOn Φ (Set.Icc 1 X)) :
    ∑ a ∈ Finset.Icc 1 ⌊X⌋₊, ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, 2 * Real.log n * pairI Φ X a n
      = logPos Φ X + diagD Φ X - logResid Φ X := by
  set s := Finset.Icc 1 ⌊X⌋₊ with hs
  have h1 : ∑ a ∈ s, ∑ n ∈ s, Real.log n * pairI Φ X a n
      = ∑ a ∈ s, ∑ n ∈ s, Real.log a * pairI Φ X a n := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun n _ => by rw [pairI_comm]
  have hsym : ∑ a ∈ s, ∑ n ∈ s, 2 * Real.log n * pairI Φ X a n
      = ∑ a ∈ s, ∑ n ∈ s, (Real.log a + Real.log n) * pairI Φ X a n := by
    have h2 : ∑ a ∈ s, ∑ n ∈ s, (Real.log a + Real.log n) * pairI Φ X a n
        = ∑ a ∈ s, ∑ n ∈ s, Real.log a * pairI Φ X a n
          + ∑ a ∈ s, ∑ n ∈ s, Real.log n * pairI Φ X a n := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun a _ => by
        rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun n _ => by ring
    have h3 : ∑ a ∈ s, ∑ n ∈ s, 2 * Real.log n * pairI Φ X a n
        = 2 * ∑ a ∈ s, ∑ n ∈ s, Real.log n * pairI Φ X a n := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun n _ => by ring
    rw [h2, h3, h1]; ring
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
  rw [hsym, hres, hdiag]
  show _ = ∑ a ∈ s, ∑ n ∈ s,
      (∫ θ in (1 : ℝ)..(X / (max a n : ℕ)), Real.log ((max a n : ℕ) * θ) * (Φ (a * θ) * Φ (n * θ))) + _ - _
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [pair_term hX hcont ha hn]
  ring

end Cvs.L2a.LogPositionIdentity
