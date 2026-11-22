import Mathlib
import Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous
import Cvs.WeilForm.ConstraintLimitAdmissible
import Cvs.WeilForm.EvenBottomAttained
import Cvs.WeilForm.EvennessSurvivesL2Limit
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.WeilForm.WindowBottomAttainedUnconditional
import Cvs.WeilForm.WindowConstraintSet
import Cvs.WeilForm.WindowFormLowerSemicontinuous

/-!
# A minimising sequence converges to the minimiser, up to sign

    Ξ k in the even sector with weilForm (Ξ k) → lam
      ⟹ a subsequence converges in `L²` to `η` or to `−η`

the direct method again: compactness, semicontinuity, and uniqueness of the bottom.
-/

set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Real Filter Cvs.Zeta.Explicit.Weil

namespace Cvs.WeilForm.MinimisingSequenceConverges

variable {L : ℝ}

/-- **The Ritz step.**  A minimising sequence in the even sector converges, along a
subsequence, to the minimiser up to sign. -/
theorem exists_subseq_tendsto_minimiser {lam : ℝ} (hL : 0 ≤ L) (P R : ℕ)
    {η : ℝ → ℝ} {Ξ : ℕ → ℝ → ℝ}
    (hlam : IsGLB (Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R ''
      Cvs.WeilForm.EvenBottomAttained.evenWindowSet L) lam)
    (hΞ : ∀ k, Ξ k ∈ Cvs.WeilForm.EvenBottomAttained.evenWindowSet L)
    (hΞv : Tendsto (fun k => Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (Ξ k)) atTop (nhds lam))
    (H1 : ∀ g ∈ Cvs.WeilForm.EvenBottomAttained.evenWindowSet L,
      Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R g = lam →
        g =ᵐ[(volume : Measure ℝ)] η ∨ g =ᵐ[(volume : Measure ℝ)] (fun x => -η x)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (Tendsto (fun k => ∫ x : ℝ, (Ξ (φ k) x - η x) ^ 2) atTop (nhds 0)
        ∨ Tendsto (fun k => ∫ x : ℝ, (-(Ξ (φ k) x) - η x) ^ 2) atTop (nhds 0)) := by
  classical
  -- a uniform form bound on a tail
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hΞv 1 one_pos
  set Ψ : ℕ → ℝ → ℝ := fun k => Ξ (k + N) with hΨ
  have hΨD : ∀ k, Ψ k ∈ Cvs.WeilForm.WindowConstraintSet.windowSet L := fun k => (hΞ (k + N)).1
  have hΨB : ∀ k, Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (Ψ k) ≤ lam + 1 := by
    intro k
    have h := hN (k + N) (Nat.le_add_left N k)
    rw [Real.dist_eq, abs_lt] at h
    linarith [h.2]
  -- compactness
  obtain ⟨φ₀, g, hφ₀, hgD, htend⟩ := Cvs.WeilForm.ConstraintLimitAdmissible.hcpt hL P R hΨD hΨB
  -- the limit is even
  have hgeven : (fun x => g (L - x)) =ᵐ[(volume : Measure ℝ)] g :=
    Cvs.WeilForm.EvennessSurvivesL2Limit.even_of_tendsto (fun k => (hΨD (φ₀ k)).1) hgD.1
      (fun k => (hΞ (φ₀ k + N)).2) htend
  have hgE : g ∈ Cvs.WeilForm.EvenBottomAttained.evenWindowSet L := ⟨hgD, hgeven⟩
  -- the limit attains the bottom
  have hΨv : Tendsto (fun k => Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (Ψ (φ₀ k)))
      atTop (nhds lam) := by
    have hcomp : Tendsto (fun k : ℕ => φ₀ k + N) atTop atTop :=
      (Filter.tendsto_add_atTop_nat N).comp hφ₀.tendsto_atTop
    exact hΞv.comp hcomp
  have hge : lam ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R g := hlam.1 ⟨g, hgE, rfl⟩
  have hle : Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R g ≤ lam := by
    refine le_of_forall_pos_le_add (fun ε hε => ?_)
    have hlsc := Cvs.WeilForm.WindowFormLowerSemicontinuous.weilForm_le_eventually (L := L) (C := 1) P R
      hgD.1 (fun k => (hΨD (φ₀ k)).1) hgD.2.1 (fun k => (hΨD (φ₀ k)).2.1)
      (Cvs.WeilForm.WindowBottomAttainedUnconditional.aestronglyMeasurable_selfConvolution hL hgD)
      (fun k => Cvs.WeilForm.WindowBottomAttainedUnconditional.aestronglyMeasurable_selfConvolution hL (hΨD (φ₀ k)))
      hgD.2.2.2 (fun k => (hΨD (φ₀ k)).2.2.2) htend
      (fun k => le_of_eq (hΨD (φ₀ k)).2.2.1) hε
    have hge' := ge_of_tendsto hΨv hlsc
    linarith
  have hgv : Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R g = lam := le_antisymm hle hge
  have hmono : StrictMono (fun k : ℕ => φ₀ k + N) := by
    intro i j hij
    exact Nat.add_lt_add_right (hφ₀ hij) N
  rcases H1 g hgE hgv with hcase | hcase
  · refine ⟨fun k => φ₀ k + N, hmono, Or.inl ?_⟩
    refine htend.congr (fun k => ?_)
    refine integral_congr_ae ?_
    filter_upwards [hcase] with x hx
    rw [hx]
  · refine ⟨fun k => φ₀ k + N, hmono, Or.inr ?_⟩
    refine htend.congr (fun k => ?_)
    refine integral_congr_ae ?_
    filter_upwards [hcase] with x hx
    rw [hx]
    ring

end Cvs.WeilForm.MinimisingSequenceConverges
