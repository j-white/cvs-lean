import Mathlib
import Cvs.Upstream.ToLpNormSqIntegral

/-!
# Plancherel carries convergence between the two sides

    ‖𝓕 f − 𝓕 g‖ = ‖f − g‖

so a sequence converging in `L²` on the frequency side converges in `L²` on the space side,
and a compact family yields a convergent subsequence there.
-/

set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Filter

namespace Cvs.Upstream.PlancherelConvergenceTransfer

/-- **The `L²` distance of classes, as the integral node 2c is stated in.** -/
theorem integral_sub_sq_eq_norm_sq {f g : ℝ → ℂ}
    (hf : MemLp f 2 (volume : Measure ℝ)) (hg : MemLp g 2 (volume : Measure ℝ)) :
    (∫ x : ℝ, ‖f x - g x‖ ^ 2) = ‖hf.toLp f - hg.toLp g‖ ^ 2 := by
  have hsub : (hf.sub hg).toLp (f - g) = hf.toLp f - hg.toLp g := MemLp.toLp_sub hf hg
  rw [← hsub, Cvs.Upstream.ToLpNormSqIntegral.norm_toLp_sq (hf.sub hg)]
  rfl

end Cvs.Upstream.PlancherelConvergenceTransfer
