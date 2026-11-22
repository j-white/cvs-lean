import Mathlib
import Cvs.StepA.EvenSectorWins
import Cvs.Upstream.DiagonalRankOneMinimum
import Cvs.Upstream.TightCoordinateConvergence
import Cvs.WeilForm.EvenSectorMinimum
import Cvs.WeilForm.MinimiserEulerLagrange

/-!
# The odd sector's ground state is simple too

    c < 0  ⟹  λ_min < Dₙ for every n

A negative rank one drops the mode vector below its own level, so the minimum falls below the
whole diagonal spectrum and is separated from it for free.  Simplicity follows as before.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Cvs.Upstream.TightCoordinateConvergence Cvs.Upstream.DiagonalRankOneMinimum Cvs.WeilForm.EvenSectorMinimum Cvs.StepA.EvenSectorWins

namespace Cvs.StepA.OddGroundStateSimple

variable {ι : Type*} [Countable ι] [DecidableEq ι] [Nonempty ι]

/-- **A negative rank one puts the minimum below every level.** -/
theorem min_lt_diag_of_neg {D v : ι → ℝ} {K c : ℝ} {η : ι → ℝ} (hc : c < 0)
    (hmin : ∀ a ∈ sphereDom (fun n => D n - K), diagFormVal D c v η ≤ diagFormVal D c v a)
    (hv : ∀ n : ι, v n ≠ 0) (n : ι) :
    diagFormVal D c v η < D n := by
  have hval := hmin _ (modeVec_mem (fun m => D m - K) n)
  rw [diagFormVal_modeVec] at hval
  have hvsq : 0 < (v n) ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (hv n)))
  have hneg : c * (v n) ^ 2 < 0 := mul_neg_of_neg_of_pos hc hvsq
  linarith

/-- **So the minimum meets no diagonal level.** -/
theorem min_notMem_diag_of_neg {D v : ι → ℝ} {K c : ℝ} {η : ι → ℝ} (hc : c < 0)
    (hmin : ∀ a ∈ sphereDom (fun n => D n - K), diagFormVal D c v η ≤ diagFormVal D c v a)
    (hv : ∀ n : ι, v n ≠ 0) (n : ι) :
    diagFormVal D c v η ≠ D n :=
  ne_of_lt (min_lt_diag_of_neg hc hmin hv n)

/-- **And the odd-sector minimum is simple.**  The same Euler–Lagrange argument, on a
separation that a negative rank one supplies by itself. -/
theorem minimiser_unique_of_neg {D v : ι → ℝ} {K c : ℝ} {η η' : ι → ℝ} (hc : c < 0)
    (hη : η ∈ sphereDom (fun n => D n - K)) (hη' : η' ∈ sphereDom (fun n => D n - K))
    (hmin : ∀ a ∈ sphereDom (fun n => D n - K), diagFormVal D c v η ≤ diagFormVal D c v a)
    (hmin' : ∀ a ∈ sphereDom (fun n => D n - K), diagFormVal D c v η' ≤ diagFormVal D c v a)
    (hvsum : Summable fun n => (v n) ^ 2) (hv : ∀ n : ι, v n ≠ 0)
    (hne : ∃ n : ι, η n ≠ 0) :
    ∃ t : ℝ, ∀ n : ι, η' n = t * η n :=
  Cvs.WeilForm.MinimiserEulerLagrange.minimiser_unique hη hη' hmin hmin' hvsum
    (min_notMem_diag_of_neg hc hmin hv) hne

/-! ### The comparison, from the other side -/

/-- **A positive rank one keeps the form above the diagonal's floor.** -/
theorem diag_le_of_pos {D v : ι → ℝ} {c D₀ : ℝ} (hc : 0 ≤ c) (hD : ∀ n : ι, D₀ ≤ D n)
    {a : ι → ℝ} (ha1 : Summable fun n => (a n) ^ 2) (haunit : ∑' n : ι, (a n) ^ 2 = 1)
    (hDa : Summable fun n : ι => D n * (a n) ^ 2) :
    D₀ ≤ diagFormVal D c v a := by
  have hdiag : D₀ ≤ ∑' n : ι, D n * (a n) ^ 2 := by
    have hle : ∀ n : ι, D₀ * (a n) ^ 2 ≤ D n * (a n) ^ 2 := fun n =>
      mul_le_mul_of_nonneg_right (hD n) (sq_nonneg _)
    have := Summable.tsum_le_tsum hle (ha1.mul_left D₀) hDa
    rwa [tsum_mul_left, haunit, mul_one] at this
  have hrank : 0 ≤ rankOneVal c v a := by
    unfold rankOneVal
    positivity
  unfold diagFormVal
  linarith

/-- **The odd sector wins when the pole is strong enough.**  A mode of the negative rank one
already costs less than the even sector's floor. -/
theorem odd_lt_even {D v w : ι → ℝ} {K cE cO D₀ : ℝ} {ηE ηO : ι → ℝ} (hcE : 0 ≤ cE)
    (hD : ∀ n : ι, D₀ ≤ D n)
    (hEmem : ηE ∈ sphereDom (fun n => D n - K))
    (hOmin : ∀ a ∈ sphereDom (fun n => D n - K), diagFormVal D cO w ηO ≤ diagFormVal D cO w a)
    {m : ι} (hgap : D m + cO * (w m) ^ 2 < D₀) :
    diagFormVal D cO w ηO < diagFormVal D cE v ηE := by
  obtain ⟨hnorm, hunit, hshift⟩ := hEmem
  have hDsum : Summable fun n : ι => D n * (ηE n) ^ 2 := by
    have := hshift.add (hnorm.mul_left K)
    refine this.congr fun n => ?_
    ring
  have hlowE : D₀ ≤ diagFormVal D cE v ηE := diag_le_of_pos hcE hD hnorm hunit hDsum
  have hupO : diagFormVal D cO w ηO ≤ D m + cO * (w m) ^ 2 := by
    have := hOmin _ (modeVec_mem (fun n => D n - K) m)
    rwa [diagFormVal_modeVec] at this
  linarith

end Cvs.StepA.OddGroundStateSimple
