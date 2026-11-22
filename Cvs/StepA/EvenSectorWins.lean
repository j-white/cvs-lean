import Mathlib
import Cvs.Upstream.DiagonalRankOneMinimum
import Cvs.Upstream.TightCoordinateConvergence
import Cvs.WeilForm.EvenSectorMinimum
import Cvs.WeilForm.PoleTermLpContinuity

/-!
# When the even sector wins

    Q_odd a ≥ D₁ − c‖w‖²,     Q_even e₀ = D₀ + c v₀²

A negative rank one can lower the odd sector by at most `c‖w‖²`, and the zero mode bounds the
even minimum from above.  So a gap wider than the two pole strengths decides the parity.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Cvs.Upstream.TightCoordinateConvergence Cvs.Upstream.DiagonalRankOneMinimum Cvs.WeilForm.EvenSectorMinimum

namespace Cvs.StepA.EvenSectorWins

variable {ι : Type*} [Countable ι] [DecidableEq ι] [Nonempty ι]

/-- **A negative rank one lowers the form by at most its strength.** -/
theorem le_diagFormVal_neg {D w : ι → ℝ} {c D₁ : ℝ} (hc : 0 ≤ c)
    (hw : Summable fun n => (w n) ^ 2) (hD : ∀ n : ι, D₁ ≤ D n) {a : ι → ℝ}
    (ha1 : Summable fun n => (a n) ^ 2) (haunit : ∑' n : ι, (a n) ^ 2 = 1)
    (hDa : Summable fun n : ι => D n * (a n) ^ 2) :
    D₁ - c * (∑' n : ι, (w n) ^ 2) ≤ diagFormVal D (-c) w a := by
  have hdiag : D₁ ≤ ∑' n : ι, D n * (a n) ^ 2 := by
    have hle : ∀ n : ι, D₁ * (a n) ^ 2 ≤ D n * (a n) ^ 2 := fun n =>
      mul_le_mul_of_nonneg_right (hD n) (sq_nonneg _)
    have := Summable.tsum_le_tsum hle (ha1.mul_left D₁) hDa
    rwa [tsum_mul_left, haunit, mul_one] at this
  have hcs := Cvs.WeilForm.PoleTermLpContinuity.sq_tsum_mul_le hw ha1
  rw [haunit, mul_one] at hcs
  unfold diagFormVal rankOneVal
  have : -c * (∑' n : ι, w n * a n) ^ 2 ≥ -(c * ∑' n : ι, (w n) ^ 2) := by
    nlinarith [hcs, hc]
  linarith

/-- The vector concentrated at one mode. -/
def modeVec (n₀ : ι) : ι → ℝ := fun n => if n = n₀ then 1 else 0

theorem modeVec_mem (σ : ι → ℝ) (n₀ : ι) : modeVec n₀ ∈ sphereDom σ := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · exact summable_of_ne_finset_zero (s := {n₀}) fun n hn => by
      simp [modeVec, Finset.mem_singleton.not.mp hn]
  · rw [tsum_eq_sum (s := {n₀}) (fun n hn => by
      simp [modeVec, Finset.mem_singleton.not.mp hn])]
    simp [modeVec]
  · exact summable_of_ne_finset_zero (s := {n₀}) fun n hn => by
      simp [modeVec, Finset.mem_singleton.not.mp hn]

/-- **The zero mode's value**: the level there, lifted by the rank one. -/
theorem diagFormVal_modeVec (D v : ι → ℝ) (c : ℝ) (n₀ : ι) :
    diagFormVal D c v (modeVec n₀) = D n₀ + c * (v n₀) ^ 2 := by
  classical
  have h1 : ∑' n : ι, D n * (modeVec n₀ n) ^ 2 = D n₀ := by
    rw [tsum_eq_sum (s := {n₀}) (fun n hn => by
      simp [modeVec, Finset.mem_singleton.not.mp hn])]
    simp [modeVec]
  have h2 : ∑' n : ι, v n * modeVec n₀ n = v n₀ := by
    rw [tsum_eq_sum (s := {n₀}) (fun n hn => by
      simp [modeVec, Finset.mem_singleton.not.mp hn])]
    simp [modeVec]
  unfold diagFormVal rankOneVal
  rw [h1, h2]

/-- **The parity criterion.**  If the gap between the lowest level and the rest exceeds the
two pole strengths together, every odd unit vector costs more than the even minimum. -/
theorem even_lt_odd {D v w : ι → ℝ} {K c D₁ : ℝ} {η : ι → ℝ} (hc : 0 ≤ c)
    (hw : Summable fun n => (w n) ^ 2) (hD : ∀ n : ι, D₁ ≤ D n)
    (hmin : ∀ a ∈ sphereDom (fun n => D n - K), diagFormVal D c v η ≤ diagFormVal D c v a)
    {n₀ : ι} (hgap : D n₀ + c * (v n₀) ^ 2 < D₁ - c * (∑' n : ι, (w n) ^ 2))
    {a : ι → ℝ} (ha1 : Summable fun n => (a n) ^ 2) (haunit : ∑' n : ι, (a n) ^ 2 = 1)
    (hDa : Summable fun n : ι => D n * (a n) ^ 2) :
    diagFormVal D c v η < diagFormVal D (-c) w a := by
  have hup : diagFormVal D c v η ≤ D n₀ + c * (v n₀) ^ 2 := by
    have := hmin _ (modeVec_mem (fun n => D n - K) n₀)
    rwa [diagFormVal_modeVec] at this
  have hlow := le_diagFormVal_neg hc hw hD ha1 haunit hDa
  linarith

end Cvs.StepA.EvenSectorWins
