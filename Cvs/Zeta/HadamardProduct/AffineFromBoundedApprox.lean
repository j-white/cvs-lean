import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Liouville
import Cvs.Zeta.HadamardProduct.AffineFromDerivConst

/-!
# The endgame of rung 3, as one abstract estimate

Rung 3 is: in `ξ = φ·e^h`, the entire `h` is affine.
-/

noncomputable section

open Complex Filter Topology Metric

namespace Cvs.ZeroFree

/-- **The endgame.** An entire `u` that is, on `ball 0 (r/4)`, within `B r` of the negative of
some holomorphic `G r` whose own derivative is within `ε r` of `0` on `ball 0 (r/8)`, has `u'
≡ 0` as soon as `8·B r/r → 0` and `ε r → 0`. -/
theorem deriv_eq_zero_of_bounded_approx {u : ℂ → ℂ} (hu : Differentiable ℂ u)
    {G : ℝ → ℂ → ℂ} {B ε : ℝ → ℝ}
    (hG : ∀ᶠ r : ℝ in atTop, DifferentiableOn ℂ (G r) (ball (0 : ℂ) (r / 4)))
    (hbd : ∀ᶠ r : ℝ in atTop, ∀ z ∈ ball (0 : ℂ) (r / 4), ‖u z + G r z‖ ≤ B r)
    (hGd : ∀ᶠ r : ℝ in atTop, ∀ z ∈ ball (0 : ℂ) (r / 8), ‖deriv (G r) z‖ ≤ ε r)
    (hB : Tendsto (fun r => 8 * B r / r) atTop (nhds 0))
    (hε : Tendsto ε atTop (nhds 0)) :
    ∀ z, deriv u z = 0 := by
  intro z
  have hlim : Tendsto (fun r => 8 * B r / r + ε r) atTop (nhds 0) := by
    simpa using hB.add hε
  refine norm_eq_zero.mp (le_antisymm (ge_of_tendsto hlim ?_) (norm_nonneg _))
  filter_upwards [eventually_ge_atTop (8 * ‖z‖ + 8), hG, hbd, hGd] with r hr hGr hbdr hGdr
  -- the geometry: `closedBall z (r/8) ⊆ ball 0 (r/4)`
  have hz8 : ‖z‖ + 1 ≤ r / 8 := by linarith
  have hrpos : (0 : ℝ) < r / 8 := by
    have : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
    linarith
  have hsub : closedBall z (r / 8) ⊆ ball (0 : ℂ) (r / 4) := by
    intro w hw
    rw [mem_closedBall, dist_eq_norm] at hw
    rw [mem_ball, dist_zero_right]
    have h1 : ‖w‖ ≤ ‖w - z‖ + ‖z‖ := by
      simpa using norm_add_le (w - z) z
    linarith
  -- the function Cauchy's estimate is applied to
  set H : ℂ → ℂ := fun w => u w + G r w with hH
  have hHat : ∀ w ∈ ball (0 : ℂ) (r / 4), DifferentiableAt ℂ H w := by
    intro w hw
    exact (hu w).add (hGr.differentiableAt (isOpen_ball.mem_nhds hw))
  have hdcc : DiffContOnCl ℂ H (ball z (r / 8)) := by
    constructor
    · intro w hw
      exact (hHat w (hsub (ball_subset_closedBall hw))).differentiableWithinAt
    · intro w hw
      rw [closure_ball z (ne_of_gt hrpos)] at hw
      exact (hHat w (hsub hw)).continuousAt.continuousWithinAt
  have hsph : ∀ w ∈ sphere z (r / 8), ‖H w‖ ≤ B r := by
    intro w hw
    exact hbdr w (hsub (sphere_subset_closedBall hw))
  have hcauchy : ‖deriv H z‖ ≤ B r / (r / 8) :=
    Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hrpos hdcc hsph
  -- split the derivative
  have hzin4 : z ∈ ball (0 : ℂ) (r / 4) := hsub (mem_closedBall_self hrpos.le)
  have hzin8 : z ∈ ball (0 : ℂ) (r / 8) := by
    rw [mem_ball, dist_zero_right]; linarith
  have hderiv : deriv H z = deriv u z + deriv (G r) z :=
    deriv_add (hu z) (hGr.differentiableAt (isOpen_ball.mem_nhds hzin4))
  have hsplit : ‖deriv u z‖ ≤ ‖deriv H z‖ + ‖deriv (G r) z‖ := by
    have : deriv u z = deriv H z - deriv (G r) z := by rw [hderiv]; ring
    rw [this]
    exact norm_sub_le _ _
  have hrpos' : (0 : ℝ) < r := by linarith
  have hval : B r / (r / 8) = 8 * B r / r := by
    field_simp
  calc ‖deriv u z‖ ≤ ‖deriv H z‖ + ‖deriv (G r) z‖ := hsplit
    _ ≤ B r / (r / 8) + ε r := add_le_add hcauchy (hGdr z hzin8)
    _ = 8 * B r / r + ε r := by rw [hval]

/-- **Rung 3's conclusion, from the same hypotheses.**  If `h` is entire and `h'` satisfies
the estimate above, then `h` is affine — which is exactly what `ξ = φ·e^h` needs. -/
theorem affine_of_bounded_approx {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    {G : ℝ → ℂ → ℂ} {B ε : ℝ → ℝ}
    (hG : ∀ᶠ r : ℝ in atTop, DifferentiableOn ℂ (G r) (ball (0 : ℂ) (r / 4)))
    (hbd : ∀ᶠ r : ℝ in atTop, ∀ z ∈ ball (0 : ℂ) (r / 4), ‖deriv h z + G r z‖ ≤ B r)
    (hGd : ∀ᶠ r : ℝ in atTop, ∀ z ∈ ball (0 : ℂ) (r / 8), ‖deriv (G r) z‖ ≤ ε r)
    (hB : Tendsto (fun r => 8 * B r / r) atTop (nhds 0))
    (hε : Tendsto ε atTop (nhds 0)) :
    ∃ a b : ℂ, ∀ z, h z = a * z + b := by
  have hderivDiff : Differentiable ℂ (deriv h) := by
    have hana : AnalyticOnNhd ℂ h Set.univ := hh.differentiableOn.analyticOnNhd isOpen_univ
    intro z
    exact ((hana.deriv_of_isOpen isOpen_univ) z (Set.mem_univ z)).differentiableAt
  exact Cvs.ZeroFree.exists_affine_of_deriv_deriv_eq_zero hh
    (deriv_eq_zero_of_bounded_approx hderivDiff hG hbd hGd hB hε)

end Cvs.ZeroFree
