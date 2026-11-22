import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Basic

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The edge limit

If `E ≤ S(x₀) + I` for every `x₀ ∈ (1, x₁)` and `S(x₀) → 0` as `x₀ → 1⁺`, then `E ≤ I`. With an earlier result (`S = √Z(x₀)`, the
error and flux vanishing at the edge, and the residual integral from `x₀` at most that from `1`) this gives the Olver
error bound from the edge itself: `|ψ − ψ(1)A J₀(ζ)|(x₁) ≤ ∫_1^{x₁} |F|/a`.
-/

namespace Cvs.Upstream.OneSidedEdgeLimit

open Filter Topology Set

/-- **The edge limit.** -/
theorem le_of_edge_limit {S : ℝ → ℝ} {E I x₁ : ℝ} (hx : 1 < x₁)
    (hle : ∀ x₀ ∈ Ioo 1 x₁, E ≤ S x₀ + I) (hS : Tendsto S (𝓝[>] 1) (𝓝 0)) : E ≤ I := by
  have hlim : Tendsto (fun x₀ => S x₀ + I) (𝓝[>] 1) (𝓝 (0 + I)) := hS.add tendsto_const_nhds
  rw [zero_add] at hlim
  have hev : ∀ᶠ x₀ in 𝓝[>] (1 : ℝ), E ≤ S x₀ + I := by
    filter_upwards [Ioo_mem_nhdsGT hx] with x₀ hx₀ using hle x₀ hx₀
  exact ge_of_tendsto hlim hev

end Cvs.Upstream.OneSidedEdgeLimit
