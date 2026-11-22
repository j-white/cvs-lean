import Mathlib
import Cvs.Upstream.TotallyBoundedDistPreserving
import Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous
import Cvs.WeilForm.EvennessSurvivesL2Limit
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.WeilForm.SelfConvolutionTransform
import Cvs.WeilForm.TransformFamiliesIsometric
import Cvs.WeilForm.WindowConstraintSet

/-!
# The constraint set is sequentially compact along form-bounded sequences

    F n ∈ D,  weilForm (F n) ≤ B   ⟹   a subsequence converges in L² to some g ∈ D

which is the hypothesis `Cvs.WeilForm.DirectMethodBottomAttained`'s direct method takes.
-/

set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Real Filter Cvs.Zeta.Explicit.Weil
open scoped FourierTransform

namespace Cvs.WeilForm.ConstraintSetSeqCompact

/-- **The classes of a form-bounded family are totally bounded.** -/
theorem totallyBounded_classes {L B : ℝ} (hL : 0 ≤ L) (P R : ℕ) {F : ℕ → ℝ → ℝ}
    (hFD : ∀ n, F n ∈ Cvs.WeilForm.WindowConstraintSet.windowSet L)
    (hFB : ∀ n, Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (F n) ≤ B) :
    TotallyBounded (Set.range fun n : ℕ => (hFD n).1.toLp (F n)) := by
  refine Cvs.Upstream.TotallyBoundedDistPreserving.totallyBounded_of_dist_eq
    (C := fun n : ℕ =>
      (Cvs.WeilForm.TransformFamiliesIsometric.memLp_fourier (hFD n).1
        (Cvs.WeilForm.WindowConstraintSet.integrable_of_mem hL (hFD n))).toLp
        (𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf (F n)))) ?_
    (Cvs.WeilForm.WindowConstraintSet.totallyBounded_transforms hL P R hFD hFB)
  intro i j
  exact Cvs.WeilForm.TransformFamiliesIsometric.dist_toLp_eq (hFD i).1 (hFD j).1
    (Cvs.WeilForm.WindowConstraintSet.integrable_of_mem hL (hFD i))
    (Cvs.WeilForm.WindowConstraintSet.integrable_of_mem hL (hFD j))
    ((hFD i).1.sub (hFD j).1)
    ((Cvs.WeilForm.WindowConstraintSet.integrable_of_mem hL (hFD i)).sub
      (Cvs.WeilForm.WindowConstraintSet.integrable_of_mem hL (hFD j)))

/-- **A convergent subsequence, on the space side.** -/
theorem exists_subseq_tendsto_integral {L B : ℝ} (hL : 0 ≤ L) (P R : ℕ) {F : ℕ → ℝ → ℝ}
    (hFD : ∀ n, F n ∈ Cvs.WeilForm.WindowConstraintSet.windowSet L)
    (hFB : ∀ n, Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (F n) ≤ B) :
    ∃ (φ : ℕ → ℕ) (g₀ : ℝ → ℝ), StrictMono φ ∧ MemLp g₀ 2 (volume : Measure ℝ) ∧
      Tendsto (fun k => ∫ x : ℝ, (F (φ k) x - g₀ x) ^ 2) atTop (nhds 0) := by
  have htb := totallyBounded_classes hL P R hFD hFB
  have hcpt : IsCompact (closure (Set.range fun n : ℕ => (hFD n).1.toLp (F n))) :=
    htb.closure.isCompact_of_isClosed isClosed_closure
  obtain ⟨G, _, φ, hφ, htend⟩ :=
    hcpt.tendsto_subseq (x := fun n : ℕ => (hFD n).1.toLp (F n))
      (fun n => subset_closure (Set.mem_range_self n))
  refine ⟨φ, (G : ℝ → ℝ), hφ, Lp.memLp G, ?_⟩
  have hGtoLp : (Lp.memLp G).toLp (G : ℝ → ℝ) = G := Lp.toLp_coeFn G (Lp.memLp G)
  have hrw : ∀ k, (∫ x : ℝ, (F (φ k) x - (G : ℝ → ℝ) x) ^ 2)
      = dist ((hFD (φ k)).1.toLp (F (φ k))) G ^ 2 := by
    intro k
    rw [dist_eq_norm, ← hGtoLp,
      Cvs.WeilForm.EvennessSurvivesL2Limit.norm_toLp_sub_sq_real (hFD (φ k)).1 (Lp.memLp G), hGtoLp]
  simp only [hrw]
  have hd : Tendsto (fun k => dist ((hFD (φ k)).1.toLp (F (φ k))) G) atTop (nhds 0) := by
    rw [← tendsto_iff_dist_tendsto_zero] at *
    simpa [Function.comp_def] using htend
  have := hd.pow 2
  simpa using this

end Cvs.WeilForm.ConstraintSetSeqCompact
