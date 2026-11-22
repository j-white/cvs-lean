import Mathlib

/-!
# Equicontinuity survives restriction to a compact interval

Arzelà–Ascoli works on a compact domain, and the window's transforms are equicontinuous on
all of `ℝ`; this transports that to the restrictions, which is the form the compactness
argument consumes.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Set Metric Filter Topology

namespace Cvs.Upstream.EquicontinuousRestrictCompact

variable {ι X α : Type*} [TopologicalSpace X] [UniformSpace α]

/-- **The restricted family is equicontinuous on the subtype.**  `Mathlib` has both halves;
this is the composition the compactness argument uses. -/
theorem equicontinuous_restrict {F : ι → X → α} (h : Equicontinuous F) (S : Set X) :
    Equicontinuous (fun i => S.restrict (F i)) :=
  (equicontinuous_restrict_iff F).mpr (h.equicontinuousOn S)

end Cvs.Upstream.EquicontinuousRestrictCompact
