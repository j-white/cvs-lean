import Mathlib

/-!
# Total boundedness transfers along a distance-preserving index map

    dist (A i) (A j) = dist (C i) (C j),  range C totally bounded  ⟹  range A totally bounded

so `Cvs.WeilForm.TransformClassesTotallyBounded`'s compactness on the frequency side is compactness on the space side, `Cvs.WeilForm.WindowTransformIsometry`
supplying the equality of distances.
-/

set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Metric

namespace Cvs.Upstream.TotallyBoundedDistPreserving

/-- **Total boundedness transfers.** -/
theorem totallyBounded_of_dist_eq {ι : Type*} {α β : Type*}
    [PseudoMetricSpace α] [PseudoMetricSpace β]
    {A : ι → α} {C : ι → β}
    (hiso : ∀ i j, dist (A i) (A j) = dist (C i) (C j))
    (h : TotallyBounded (Set.range C)) : TotallyBounded (Set.range A) := by
  classical
  rw [Metric.totallyBounded_iff]
  intro ε hε
  obtain ⟨u, hus, hufin, hucov⟩ := h.exists_subset (Metric.dist_mem_uniformity hε)
  have hchoice : ∀ y : ↥u, ∃ i : ι, C i = (y : β) := fun y => hus y.2
  choose idx hidx using hchoice
  haveI : Finite ↥u := hufin
  refine ⟨Set.range (fun y : ↥u => A (idx y)), Set.finite_range _, ?_⟩
  rintro _ ⟨i, rfl⟩
  have hmem : C i ∈ ⋃ y ∈ u, {x | dist x y < ε} := hucov (Set.mem_range_self i)
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop] at hmem
  obtain ⟨y, hyu, hdist⟩ := hmem
  refine Set.mem_iUnion₂.mpr ⟨A (idx ⟨y, hyu⟩), Set.mem_range_self _, ?_⟩
  rw [Metric.mem_ball, hiso i (idx ⟨y, hyu⟩), hidx ⟨y, hyu⟩]
  exact hdist

end Cvs.Upstream.TotallyBoundedDistPreserving
