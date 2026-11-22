import Mathlib
import Cvs.Upstream.TightCoordinateConvergence
import Cvs.WeilForm.PoleTermLpContinuity

/-!
# A diagonal form plus a rank one attains its minimum

    Q a = ∑ₙ σₙ aₙ² + c·⟨v, a⟩²

is exactly the shape the Weil form takes on the even modes: `Cvs.WeilForm.ShiftSumModeDiagonal` makes the prime side
diagonal, and the pole term is a rank one.  `Cvs.Upstream.TightCoordinateConvergence`'s hypotheses all hold for it.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Cvs.Upstream.TightCoordinateConvergence

namespace Cvs.Upstream.DiagonalRankOneMinimum

variable {ι : Type*} [Countable ι] [DecidableEq ι] [Nonempty ι]

/-- The rank-one part, as a function of the coefficient vector. -/
def rankOneVal (c : ℝ) (v : ι → ℝ) (a : ι → ℝ) : ℝ := c * (∑' n : ι, v n * a n) ^ 2

/-- **The unit sphere of a proper diagonal form is inhabited** — one mode will do. -/
theorem sphereDom_nonempty (σ : ι → ℝ) : (sphereDom σ).Nonempty := by
  classical
  obtain ⟨m⟩ := ‹Nonempty ι›
  refine ⟨fun n => if n = m then 1 else 0, ?_, ?_, ?_⟩
  · exact summable_of_ne_finset_zero (s := {m}) fun n hn => by
      simp [Finset.mem_singleton.not.mp hn]
  · rw [tsum_eq_sum (s := {m}) (fun n hn => by simp [Finset.mem_singleton.not.mp hn])]
    simp
  · exact summable_of_ne_finset_zero (s := {m}) fun n hn => by
      simp [Finset.mem_singleton.not.mp hn]

/-- **The rank one is bounded on the sphere.** -/
theorem abs_rankOneVal_le {c : ℝ} {v : ι → ℝ} (hv : Summable fun n => (v n) ^ 2)
    {a : ι → ℝ} (ha : a ∈ sphereDom (fun _ => (0:ℝ))) :
    |rankOneVal c v a| ≤ |c| * ∑' n : ι, (v n) ^ 2 := by
  obtain ⟨hsum, hunit, -⟩ := ha
  have hcs := Cvs.WeilForm.PoleTermLpContinuity.sq_tsum_mul_le hv hsum
  rw [hunit, mul_one] at hcs
  unfold rankOneVal
  rw [abs_mul, abs_of_nonneg (sq_nonneg (∑' n : ι, v n * a n))]
  exact mul_le_mul_of_nonneg_left hcs (abs_nonneg c)

/-- **The rank one is continuous along `ℓ²`.** -/
theorem tendsto_rankOneVal {c : ℝ} {v : ι → ℝ} (hv : Summable fun n => (v n) ^ 2)
    {x : ℕ → ι → ℝ} {y : ι → ℝ}
    (hx : ∀ k, Summable fun n => (x k n) ^ 2) (hy : Summable fun n => (y n) ^ 2)
    (hconv : Filter.Tendsto (fun k => ∑' n : ι, (x k n - y n) ^ 2) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun k => rankOneVal c v (x k)) Filter.atTop (nhds (rankOneVal c v y)) := by
  unfold rankOneVal
  exact ((Cvs.WeilForm.PoleTermLpContinuity.tendsto_tsum_mul hv hx hy hconv).pow 2).const_mul c

/-- **The ground state exists** for a proper nonnegative diagonal form perturbed by a rank
one — no hypothesis beyond the shape. -/
theorem exists_minimiser_rankOne {σ : ι → ℝ} {c : ℝ} {v : ι → ℝ}
    (hσ : ∀ n, 0 ≤ σ n) (hproper : ∀ M : ℝ, {n : ι | σ n < M}.Finite)
    (hv : Summable fun n => (v n) ^ 2) :
    ∃ η ∈ sphereDom σ, ∀ a ∈ sphereDom σ,
      formVal σ (rankOneVal c v) η ≤ formVal σ (rankOneVal c v) a := by
  refine exists_minimiser (σ := σ) (Bfun := rankOneVal c v)
    (CB := |c| * ∑' n : ι, (v n) ^ 2) hσ hproper ?bdd ?cont (sphereDom_nonempty σ)
  case bdd =>
    intro a ha
    exact abs_rankOneVal_le hv ⟨ha.1, ha.2.1, by simp⟩
  case cont =>
    intro x y hxdom hydom hconv
    exact tendsto_rankOneVal hv (fun k => (hxdom k).1) hydom.1 hconv

end Cvs.Upstream.DiagonalRankOneMinimum
