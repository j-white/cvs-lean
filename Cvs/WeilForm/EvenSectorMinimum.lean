import Mathlib
import Cvs.Upstream.DiagonalRankOneMinimum
import Cvs.Upstream.TightCoordinateConvergence
import Cvs.WeilForm.EvenDiagonalProper
import Cvs.Zeta.Digamma.ArchPairingLowerBound

/-!
# The even-sector form attains its minimum, in its own terms

    Q a = ∑ₙ Dₙ aₙ² + c·⟨v,a⟩²,    Dₙ = archSymbol(ωₙ) − ∑ⱼ wⱼ cos(ωₙ uⱼ)

`Cvs.Upstream.DiagonalRankOneMinimum` minimises the shifted form; shifting back costs a constant on the sphere, so the
minimiser is the same.  Nothing here assumes anything about the zeros.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Cvs.Upstream.TightCoordinateConvergence Cvs.Upstream.DiagonalRankOneMinimum

namespace Cvs.WeilForm.EvenSectorMinimum

variable {ι : Type*} [Countable ι] [DecidableEq ι] [Nonempty ι]

/-- The unshifted form: the diagonal against the vector, plus the rank one. -/
def diagFormVal (D : ι → ℝ) (c : ℝ) (v : ι → ℝ) (a : ι → ℝ) : ℝ :=
  (∑' n : ι, D n * (a n) ^ 2) + rankOneVal c v a

/-- **Shifting the diagonal shifts the form by a constant** on the unit sphere. -/
theorem diagFormVal_eq {D : ι → ℝ} {K c : ℝ} {v : ι → ℝ} {a : ι → ℝ}
    (ha : a ∈ sphereDom (fun n => D n - K)) :
    diagFormVal D c v a = formVal (fun n => D n - K) (rankOneVal c v) a + K := by
  obtain ⟨hnorm, hunit, hshift⟩ := ha
  have hsum : Summable fun n : ι => D n * (a n) ^ 2 := by
    have := hshift.add (hnorm.mul_left K)
    refine this.congr fun n => ?_
    ring
  have hsplit : ∑' n : ι, D n * (a n) ^ 2
      = (∑' n : ι, (D n - K) * (a n) ^ 2) + K * ∑' n : ι, (a n) ^ 2 := by
    rw [← tsum_mul_left, ← hshift.tsum_add (hnorm.mul_left K)]
    exact tsum_congr fun n => by ring
  unfold diagFormVal formVal
  rw [hsplit, hunit, mul_one]
  ring

/-- **The minimum is attained by the unshifted form too.** -/
theorem exists_minimiser_diag {D : ι → ℝ} {K c : ℝ} {v : ι → ℝ}
    (hK : ∀ n, K ≤ D n) (hproper : ∀ M : ℝ, {n : ι | D n - K < M}.Finite)
    (hv : Summable fun n => (v n) ^ 2) :
    ∃ η ∈ sphereDom (fun n => D n - K), ∀ a ∈ sphereDom (fun n => D n - K),
      diagFormVal D c v η ≤ diagFormVal D c v a := by
  obtain ⟨η, hη, hmin⟩ := exists_minimiser_rankOne (σ := fun n => D n - K) (c := c) (v := v)
    (fun n => by linarith [hK n]) hproper hv
  refine ⟨η, hη, fun a ha => ?_⟩
  rw [diagFormVal_eq hη, diagFormVal_eq ha]
  linarith [hmin a ha]

/-- **The even-sector Weil form has a ground state.**  The diagonal is `Cvs.WeilForm.EvenDiagonalProper`'s — the
archimedean symbol less the prime side's diagonal — and the rank one is the pole. -/
theorem exists_weil_minimiser {L : ℝ} (hL : 0 < L) {κ : Type*} (s : Finset κ) (w u : κ → ℝ)
    (c : ℝ) {v : ℕ → ℝ} (hv : Summable fun n => (v n) ^ 2) :
    ∃ η ∈ sphereDom (fun n : ℕ =>
        Cvs.WeilForm.EvenDiagonalProper.diagVal L s w u n
          - (2 * Cvs.Zeta.Digamma.ArchPairingLowerBound.archConst - ∑ j ∈ s, |w j|)),
      ∀ a ∈ sphereDom (fun n : ℕ =>
        Cvs.WeilForm.EvenDiagonalProper.diagVal L s w u n
          - (2 * Cvs.Zeta.Digamma.ArchPairingLowerBound.archConst - ∑ j ∈ s, |w j|)),
      diagFormVal (Cvs.WeilForm.EvenDiagonalProper.diagVal L s w u) c v η
        ≤ diagFormVal (Cvs.WeilForm.EvenDiagonalProper.diagVal L s w u) c v a := by
  refine exists_minimiser_diag (K := 2 * Cvs.Zeta.Digamma.ArchPairingLowerBound.archConst - ∑ j ∈ s, |w j|)
    (fun n => Cvs.WeilForm.EvenDiagonalProper.diag_ge L s w u n) (fun M => ?_) hv
  refine Set.Finite.subset (Cvs.WeilForm.EvenDiagonalProper.diag_finite_below hL s w u
    (M + (2 * Cvs.Zeta.Digamma.ArchPairingLowerBound.archConst - ∑ j ∈ s, |w j|))) ?_
  intro n hn
  simp only [Set.mem_ofPred_eq] at hn ⊢
  linarith

end Cvs.WeilForm.EvenSectorMinimum
