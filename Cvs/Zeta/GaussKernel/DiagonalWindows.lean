import Mathlib

/-!
# The diagonal, and windows that need not be nested

`an earlier result` listed three things between the windowed formula and the `tsum`: the index change, the
multiplicity, and the interleaving of `ε` with `T`.
-/

namespace Cvs.Criterion

open scoped Real

/-- **Absorbing windows are cofinal**, nesting not required — each index eventually in. -/
theorem tendsto_finset_atTop_of_absorbing {ι : Type*} {S : ℕ → Finset ι}
    (h : ∀ i, ∀ᶠ n in Filter.atTop, i ∈ S n) :
    Filter.Tendsto S Filter.atTop Filter.atTop := by
  classical
  rw [Filter.tendsto_atTop]
  intro T
  have hall : ∀ᶠ n in Filter.atTop, ∀ i ∈ T, i ∈ S n :=
    (Filter.eventually_all_finset T).mpr fun i _ => h i
  filter_upwards [hall] with n hn
  exact fun i hi => hn i hi

/-- Window sums converge to the `tsum` for absorbing windows. -/
theorem tendsto_window_sums_absorbing {ι : Type*} {f : ι → ℝ} (hf : Summable f)
    {S : ℕ → Finset ι} (h : ∀ i, ∀ᶠ n in Filter.atTop, i ∈ S n) :
    Filter.Tendsto (fun n => ∑ i ∈ S n, f i) Filter.atTop (nhds (∑' i, f i)) :=
  hf.hasSum.comp (tendsto_finset_atTop_of_absorbing h)

/-- **The diagonal.**  The formula's `∀ε ∃T₀ ∀T` pattern yields one window sequence that both
absorbs and has vanishing error. -/
theorem exists_diagonal_windows {ι : Type*} {g : Finset ι → ℝ} {c : ℝ} (ht : ι → ℝ)
    (H : ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      ∃ T' : ℝ, T ≤ T' ∧ ∃ S : Finset ι, (∀ i, ht i < T' → i ∈ S) ∧ |g S - c| < ε) :
    ∃ S : ℕ → Finset ι, (∀ i, ∀ᶠ n in Filter.atTop, i ∈ S n) ∧
      Filter.Tendsto (fun n => g (S n)) Filter.atTop (nhds c) := by
  classical
  choose T₀ hT₀ using fun n : ℕ => H (1 / (n + 1)) (by positivity)
  choose T' hTle S hSmem hSerr using fun n : ℕ =>
    hT₀ n (max (T₀ n) ((n : ℝ) + 1)) (le_max_left _ _)
  have hTn : ∀ n : ℕ, ((n : ℝ) + 1) ≤ T' n := fun n =>
    le_trans (le_max_right _ _) (hTle n)
  refine ⟨S, fun i => ?_, ?_⟩
  · obtain ⟨N, hN⟩ := exists_nat_gt (ht i)
    refine Filter.eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
    refine hSmem n i (lt_of_lt_of_le hN ?_)
    have : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith [hTn n]
  · refine Metric.tendsto_atTop.mpr fun ε hε => ?_
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
    refine ⟨N, fun n hn => ?_⟩
    have hn' : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hlt : 1 / ((n : ℝ) + 1) < ε := by
      rw [div_lt_iff₀ hpos]
      have : 1 / ε < (n : ℝ) + 1 := by linarith [hN]
      rw [div_lt_iff₀ hε] at this
      linarith
    calc dist (g (S n)) c = |g (S n) - c| := Real.dist_eq _ _
      _ < 1 / ((n : ℝ) + 1) := hSerr n
      _ < ε := hlt

/-- **Composed.**  A summable family whose windows satisfy the formula's shape has
`Σ' f = c`. -/
theorem tsum_eq_of_formula_shape {ι : Type*} {f : ι → ℝ} {c : ℝ} (hf : Summable f)
    (ht : ι → ℝ)
    (H : ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      ∃ T' : ℝ, T ≤ T' ∧ ∃ S : Finset ι, (∀ i, ht i < T' → i ∈ S) ∧
        |(∑ i ∈ S, f i) - c| < ε) :
    ∑' i, f i = c := by
  obtain ⟨S, habs, htend⟩ := exists_diagonal_windows (g := fun S => ∑ i ∈ S, f i) ht H
  exact tendsto_nhds_unique (tendsto_window_sums_absorbing hf habs) htend

end Cvs.Criterion
