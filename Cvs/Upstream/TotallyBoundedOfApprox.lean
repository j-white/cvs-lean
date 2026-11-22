import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Topology.UniformSpace.Cauchy

/-!
# Total boundedness from approximation by totally bounded sets

    for every `ε`, `S` lies within `ε` of a totally bounded set   ⟹   `S` is totally bounded

which is the step a compactness criterion ends on, once a compact approximation is in hand.
-/

noncomputable section

open Metric

namespace Cvs.Upstream.TotallyBoundedOfApprox

variable {E : Type*} [NormedAddCommGroup E]

/-- **Approximation gives total boundedness.**  Cover the approximant finitely at scale `ε`, and
those balls at scale `2ε` cover `S`. -/
theorem totallyBounded_of_approx {S : Set E}
    (h : ∀ ε > 0, ∃ K : Set E, TotallyBounded K ∧ ∀ f ∈ S, ∃ g ∈ K, ‖f - g‖ ≤ ε) :
    TotallyBounded S := by
  rw [Metric.totallyBounded_iff]
  intro δ hδ
  obtain ⟨K, hK, happ⟩ := h (δ / 3) (by linarith)
  rw [Metric.totallyBounded_iff] at hK
  obtain ⟨t, htfin, htcov⟩ := hK (δ / 3) (by linarith)
  refine ⟨t, htfin, fun f hf => ?_⟩
  obtain ⟨g, hgK, hfg⟩ := happ f hf
  obtain ⟨y, hyt, hgy⟩ := Set.mem_iUnion₂.mp (htcov hgK)
  refine Set.mem_iUnion₂.mpr ⟨y, hyt, ?_⟩
  rw [Metric.mem_ball] at hgy ⊢
  have h1 : dist f g ≤ δ / 3 := by rwa [dist_eq_norm]
  calc dist f y ≤ dist f g + dist g y := dist_triangle f g y
    _ < δ / 3 + δ / 3 := by linarith
    _ < δ := by linarith

end Cvs.Upstream.TotallyBoundedOfApprox
