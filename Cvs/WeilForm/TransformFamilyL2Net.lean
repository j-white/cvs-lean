import Mathlib
import Cvs.Upstream.BoundedEquicontinuousCompactClosure
import Cvs.Upstream.SupNetTailsL2Net

/-!
# The family has a finite `L²` net

Bounded, equicontinuous, and uniformly tight gives, for every `ε`, finitely many members
within `5ε` of everything.  That is total boundedness, and in a complete space it is
precompactness — the whole of node 1, with no subsequence extracted.
-/

set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Set Real Metric

namespace Cvs.WeilForm.TransformFamilyL2Net

/-- **A finite `L²` net.** -/
theorem exists_L2_net {ι : Type*} {F : ι → ℝ → ℂ} {M T ε : ℝ}
    (hcont : ∀ i, Continuous (F i)) (hbd : ∀ (i : ι) (x : ℝ), ‖F i x‖ ≤ M)
    (heq : Equicontinuous F) (hT : 0 < T) (hε : 0 < ε)
    (hsq : ∀ i, Integrable fun t => ‖F i t‖ ^ 2)
    (hdiff : ∀ i j, Integrable fun t => ‖F i t - F j t‖ ^ 2)
    (htail : ∀ i, (∫ t in (Icc (-T) T)ᶜ, ‖F i t‖ ^ 2) ≤ ε) :
    ∃ S : Set ι, S.Finite ∧
      ∀ i, ∃ j ∈ S, (∫ t : ℝ, ‖F i t - F j t‖ ^ 2) ≤ 5 * ε := by
  classical
  set δ : ℝ := Real.sqrt (ε / (2 * T)) with hδdef
  have hδpos : 0 < δ := Real.sqrt_pos.mpr (by positivity)
  have hδsq : δ ^ 2 * (2 * T) = ε := by
    rw [hδdef, Real.sq_sqrt (by positivity)]
    field_simp
  have hcpt := Cvs.Upstream.BoundedEquicontinuousCompactClosure.isCompact_closure_range T hcont hbd heq
  have htb : TotallyBounded (Set.range (Cvs.Upstream.BoundedEquicontinuousCompactClosure.restrictBCF T hcont)) :=
    hcpt.totallyBounded.subset subset_closure
  obtain ⟨u, hus, hufin, hucov⟩ := htb.exists_subset (Metric.dist_mem_uniformity hδpos)
  -- choose an index for each net centre
  have hchoice : ∀ y : ↥u, ∃ j : ι, Cvs.Upstream.BoundedEquicontinuousCompactClosure.restrictBCF T hcont j = (y : _) :=
    fun y => hus y.2
  choose idx hidx using hchoice
  haveI : Finite ↥u := hufin
  refine ⟨Set.range idx, Set.finite_range idx, ?_⟩
  intro i
  have hmem : Cvs.Upstream.BoundedEquicontinuousCompactClosure.restrictBCF T hcont i
      ∈ ⋃ y ∈ u, {x | dist x y < δ} := hucov (Set.mem_range_self i)
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop] at hmem
  obtain ⟨y, hyu, hdist⟩ := hmem
  refine ⟨idx ⟨y, hyu⟩, Set.mem_range_self _, ?_⟩
  have hidxy : Cvs.Upstream.BoundedEquicontinuousCompactClosure.restrictBCF T hcont (idx ⟨y, hyu⟩) = y :=
    hidx ⟨y, hyu⟩
  rw [← hidxy] at hdist
  have hsup : ∀ s ∈ Icc (-T) T, ‖F i s - F (idx ⟨y, hyu⟩) s‖ ≤ δ := by
    intro s hs
    have hpt := BoundedContinuousFunction.dist_coe_le_dist
      (f := Cvs.Upstream.BoundedEquicontinuousCompactClosure.restrictBCF T hcont i)
      (g := Cvs.Upstream.BoundedEquicontinuousCompactClosure.restrictBCF T hcont (idx ⟨y, hyu⟩)) ⟨s, hs⟩
    have hle : dist (F i s) (F (idx ⟨y, hyu⟩) s) ≤ δ := le_trans hpt hdist.le
    rwa [Complex.dist_eq] at hle
  exact Cvs.Upstream.SupNetTailsL2Net.integral_sq_le_of_sup_and_tails hT.le hδpos.le
    (hdiff i _) (hsq i) (hsq _) hsup hδsq.le (htail i) (htail _)

end Cvs.WeilForm.TransformFamilyL2Net
