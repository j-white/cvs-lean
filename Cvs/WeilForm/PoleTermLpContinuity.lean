import Mathlib
import Cvs.Upstream.TightCoordinateConvergence

/-!
# The pole term is bounded and continuous along `ℓ²`

    |⟨v, a⟩|² ≤ ‖v‖²·‖a‖²,    aₖ → a in `ℓ²`  ⟹  ⟨v, aₖ⟩ → ⟨v, a⟩

which is what `Cvs.Upstream.TightCoordinateConvergence`'s direct method asks of the bounded part.  The pole term is a rank one
against `e^{x/2}`, so this is all it needs.
-/

set_option maxHeartbeats 1600000

noncomputable section

namespace Cvs.WeilForm.PoleTermLpContinuity

variable {ι : Type*} [Countable ι] [DecidableEq ι]

/-- Products of square-summable families are summable. -/
theorem summable_mul {v a : ι → ℝ} (hv : Summable fun n => (v n) ^ 2)
    (ha : Summable fun n => (a n) ^ 2) : Summable fun n => v n * a n := by
  refine Summable.of_abs ?_
  refine ((hv.add ha).mul_left (1/2)).of_nonneg_of_le (fun n => abs_nonneg _) fun n => ?_
  have h := sq_nonneg (|v n| - |a n|)
  have habs : |v n * a n| = |v n| * |a n| := abs_mul _ _
  nlinarith [sq_abs (v n), sq_abs (a n), habs]

/-- **Cauchy–Schwarz for series.** -/
theorem sq_tsum_mul_le {v a : ι → ℝ} (hv : Summable fun n => (v n) ^ 2)
    (ha : Summable fun n => (a n) ^ 2) :
    (∑' n : ι, v n * a n) ^ 2 ≤ (∑' n : ι, (v n) ^ 2) * ∑' n : ι, (a n) ^ 2 := by
  have hva := summable_mul hv ha
  have hlim : Filter.Tendsto (fun T : Finset ι => (∑ n ∈ T, v n * a n) ^ 2)
      Filter.atTop (nhds ((∑' n : ι, v n * a n) ^ 2)) := hva.hasSum.pow 2
  refine le_of_tendsto hlim ?_
  filter_upwards with T
  calc (∑ n ∈ T, v n * a n) ^ 2
      ≤ (∑ n ∈ T, (v n) ^ 2) * ∑ n ∈ T, (a n) ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq T v a
    _ ≤ (∑' n : ι, (v n) ^ 2) * ∑' n : ι, (a n) ^ 2 := by
      refine mul_le_mul (sum_le_hasSum T (fun n _ => sq_nonneg _) hv.hasSum)
        (sum_le_hasSum T (fun n _ => sq_nonneg _) ha.hasSum)
        (Finset.sum_nonneg fun n _ => sq_nonneg _)
        (tsum_nonneg fun n => sq_nonneg _)

/-- **The pairing is continuous along `ℓ²` convergence.** -/
theorem tendsto_tsum_mul {v : ι → ℝ} {x : ℕ → ι → ℝ} {y : ι → ℝ}
    (hv : Summable fun n => (v n) ^ 2)
    (hx : ∀ k, Summable fun n => (x k n) ^ 2) (hy : Summable fun n => (y n) ^ 2)
    (hconv : Filter.Tendsto (fun k => ∑' n : ι, (x k n - y n) ^ 2) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun k => ∑' n : ι, v n * x k n) Filter.atTop (nhds (∑' n : ι, v n * y n)) := by
  have hsub : ∀ k, Summable fun n => (x k n - y n) ^ 2 := fun k =>
    Cvs.Upstream.TightCoordinateConvergence.summable_sq_sub (hx k) hy
  have hdiff : ∀ k, (∑' n : ι, v n * x k n) - ∑' n : ι, v n * y n
      = ∑' n : ι, v n * (x k n - y n) := by
    intro k
    rw [← Summable.tsum_sub (summable_mul hv (hx k)) (summable_mul hv hy)]
    refine tsum_congr fun n => ?_
    ring
  have hsq : ∀ k, ((∑' n : ι, v n * x k n) - ∑' n : ι, v n * y n) ^ 2
      ≤ (∑' n : ι, (v n) ^ 2) * ∑' n : ι, (x k n - y n) ^ 2 := by
    intro k
    rw [hdiff k]
    exact sq_tsum_mul_le hv (hsub k)
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hVnn : 0 ≤ ∑' n : ι, (v n) ^ 2 := tsum_nonneg fun n => sq_nonneg _
  have hgoal : ∀ᶠ k in Filter.atTop,
      (∑' n : ι, (v n) ^ 2) * ∑' n : ι, (x k n - y n) ^ 2 < ε ^ 2 := by
    have hc : Filter.Tendsto
        (fun k => (∑' n : ι, (v n) ^ 2) * ∑' n : ι, (x k n - y n) ^ 2) Filter.atTop (nhds 0) := by
      have := hconv.const_mul (∑' n : ι, (v n) ^ 2)
      simpa using this
    exact hc.eventually_lt_const (by positivity)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hgoal
  refine ⟨N, fun k hk => ?_⟩
  have h1 := hsq k
  have h2 := hN k hk
  rw [Real.dist_eq]
  nlinarith [abs_nonneg ((∑' n : ι, v n * x k n) - ∑' n : ι, v n * y n),
    sq_abs ((∑' n : ι, v n * x k n) - ∑' n : ι, v n * y n), h1, h2, hε]

end Cvs.WeilForm.PoleTermLpContinuity
