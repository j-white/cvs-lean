import Mathlib

/-!
# Equicontinuity passes from an indexed family to its range

    Equicontinuous (fun i => coe (F i))  ⟹  Equicontinuous (fun a : range F => coe a)

`arzela_ascoli` states its hypothesis about a *set* of functions; the estimates come as a
*family*.  Choosing a preimage for each member turns one into the other.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Set

namespace Cvs.Upstream.EquicontinuousRangeCoe

variable {ι X α β : Type*} [TopologicalSpace X] [UniformSpace α]

/-- **From a family to its range.**  Every member of the range is some `F i`, so the family's
modulus serves the whole set. -/
theorem equicontinuous_range_coe {F : ι → β} (coe : β → X → α)
    (h : Equicontinuous fun i => coe (F i)) :
    Equicontinuous fun a : ↥(Set.range F) => coe (a : β) := by
  classical
  have hchoice : ∀ a : ↥(Set.range F), ∃ i : ι, F i = (a : β) := fun a => a.2
  choose u hu using hchoice
  have hcomp := h.comp u
  have heq : ((fun i => coe (F i)) ∘ u)
      = fun a : ↥(Set.range F) => coe (a : β) := by
    funext a
    simp only [Function.comp_apply]
    rw [hu a]
  rwa [heq] at hcomp

end Cvs.Upstream.EquicontinuousRangeCoe
