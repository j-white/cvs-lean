import Mathlib
import Cvs.WeilForm.WindowTransformsEquicontinuous

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# A bound on a larger ball makes a family of entire functions equicontinuous

Cauchy's estimate turns a bound on the ball of radius `r + δ` into the bound `M / δ` on every
derivative over the ball of radius `r`, and the mean value theorem on that convex ball turns one
derivative bound into one Lipschitz constant shared by the whole family, which is the modulus
`Metric.equicontinuous_of_continuity_modulus` asks for.
-/

noncomputable section

open Metric Set

namespace Cvs.Upstream.EntireFamilyEquicontinuous

variable {ι : Type*} {F : ι → ℂ → ℂ} {r δ M : ℝ}

/-- **Cauchy's estimate, uniformly over the family.**  A bound on the ball of radius `r + δ`
bounds every derivative on the ball of radius `r` by `M / δ`. -/
theorem norm_deriv_le_of_bounded (hd : ∀ i, Differentiable ℂ (F i)) (hδ : 0 < δ)
    (hbd : ∀ (i : ι) (z : ℂ), ‖z‖ ≤ r + δ → ‖F i z‖ ≤ M) (i : ι) {z : ℂ} (hz : ‖z‖ ≤ r) :
    ‖deriv (F i) z‖ ≤ M / δ := by
  refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hδ ((hd i).diffContOnCl) ?_
  intro w hw
  rw [mem_sphere_iff_norm] at hw
  refine hbd i w ?_
  calc ‖w‖ = ‖w - z + z‖ := by ring_nf
    _ ≤ ‖w - z‖ + ‖z‖ := norm_add_le _ _
    _ ≤ δ + r := by rw [hw]; linarith
    _ = r + δ := by ring

/-- **One Lipschitz constant for the whole family**, on the ball where the derivatives are
bounded. -/
theorem norm_sub_le_of_bounded (hd : ∀ i, Differentiable ℂ (F i)) (hδ : 0 < δ)
    (hbd : ∀ (i : ι) (z : ℂ), ‖z‖ ≤ r + δ → ‖F i z‖ ≤ M) (i : ι) {z w : ℂ}
    (hz : ‖z‖ ≤ r) (hw : ‖w‖ ≤ r) :
    ‖F i w - F i z‖ ≤ (M / δ) * ‖w - z‖ := by
  refine Convex.norm_image_sub_le_of_norm_deriv_le (s := closedBall (0 : ℂ) r)
    (fun x _ => (hd i) x) ?_ (convex_closedBall _ _) ?_ ?_
  · intro x hx
    exact norm_deriv_le_of_bounded hd hδ hbd i (mem_closedBall_zero_iff.mp hx)
  · exact mem_closedBall_zero_iff.mpr hz
  · exact mem_closedBall_zero_iff.mpr hw

/-- **The restricted family is equicontinuous**, which is what Arzelà–Ascoli asks for. -/
theorem equicontinuous_restrict (hd : ∀ i, Differentiable ℂ (F i)) (hδ : 0 < δ)
    (hbd : ∀ (i : ι) (z : ℂ), ‖z‖ ≤ r + δ → ‖F i z‖ ≤ M) :
    Equicontinuous (fun (i : ι) (z : closedBall (0 : ℂ) r) => F i z) := by
  refine Metric.equicontinuous_of_continuity_modulus (fun d => (M / δ) * d)
    (Cvs.WeilForm.WindowTransformsEquicontinuous.tendsto_linear_modulus _) _ ?_
  intro x y i
  rw [Complex.dist_eq, Subtype.dist_eq, Complex.dist_eq]
  exact norm_sub_le_of_bounded hd hδ hbd i
    (mem_closedBall_zero_iff.mp y.2) (mem_closedBall_zero_iff.mp x.2)

end Cvs.Upstream.EntireFamilyEquicontinuous
