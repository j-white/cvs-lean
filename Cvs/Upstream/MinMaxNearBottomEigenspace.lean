import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The min-max estimates the truncations need

A vector whose Rayleigh quotient sits below `lam + del` is close to the bottom eigenspace, in
the quantitative form the truncation argument consumes.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Real

namespace Cvs.Upstream.MinMaxNearBottomEigenspace

-- `na2 = ‖α‖²`, `nb2 = ‖β‖²`, `Qb = Q(β)`, `lamN` the truncation's bottom.  The hypotheses
-- are CvS's: `η` a unit vector, bottom at least `lam`, the rest of the spectrum at least
-- `lam + del`, and `η`'s energy below `lam + eps`.
/-- **The mass off the ground state is at most `ε/δ`.** -/
theorem sq_norm_off_lt {lam del eps lamN na2 nb2 Qb : ℝ}
    (hdel : 0 < del) (hunit : na2 + nb2 = 1) (hna2 : 0 ≤ na2)
    (hlamN : lam ≤ lamN)
    (hQb : (lam + del) * nb2 ≤ Qb)
    (henergy : lamN * na2 + Qb < lam + eps) :
    nb2 < eps / del := by
  have hexp : (lam + del) * nb2 = lam * nb2 + del * nb2 := by ring
  rw [hexp] at hQb
  have hmul : lam * na2 ≤ lamN * na2 := mul_le_mul_of_nonneg_right hlamN hna2
  have hlam_eq : lam * na2 + lam * nb2 = lam := by linear_combination lam * hunit
  have : del * nb2 < eps := by linarith
  rwa [lt_div_iff₀ hdel, mul_comm]

/-- **So the truncation's ground state is close to `ξ`.**  Triangle inequality against the
trial vector, with `‖β‖ ≤ √(ε/δ)`. -/
theorem norm_sub_lt {E : Type*} [NormedAddCommGroup E] {xi eta xiN : E} {eps del : ℝ}
    (hdel : 0 < del) (heps : 0 ≤ eps)
    (happrox : ‖xi - eta‖ < eps)
    (hmass : ‖eta - xiN‖ ^ 2 < eps / del) :
    ‖xi - xiN‖ < eps + Real.sqrt (eps / del) := by
  have hb : ‖eta - xiN‖ < Real.sqrt (eps / del) := by
    have h0 : 0 ≤ ‖eta - xiN‖ := norm_nonneg _
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ eps / del by positivity),
      Real.sqrt_nonneg (eps / del), hmass, h0]
  calc ‖xi - xiN‖ = ‖(xi - eta) + (eta - xiN)‖ := by rw [sub_add_sub_cancel]
    _ ≤ ‖xi - eta‖ + ‖eta - xiN‖ := norm_add_le _ _
    _ < eps + Real.sqrt (eps / del) := by linarith

/-- **The bound tends to zero.**  So trial vectors with `ε → 0` produce truncation ground
states converging to `ξ` in norm — the hypothesis the transform bridge consumes. -/
theorem tendsto_bound {e : ℕ → ℝ} (he : Filter.Tendsto e Filter.atTop (nhds 0))
    (del : ℝ) :
    Filter.Tendsto (fun n => e n + Real.sqrt (e n / del)) Filter.atTop (nhds 0) := by
  have h1 : Filter.Tendsto (fun n => e n / del) Filter.atTop (nhds 0) := by
    simpa using he.div_const del
  have h2 : Filter.Tendsto (fun n => Real.sqrt (e n / del)) Filter.atTop (nhds 0) := by
    have := (Real.continuous_sqrt.tendsto (0:ℝ)).comp h1
    simpa [Function.comp_def] using this
  simpa using he.add h2

end Cvs.Upstream.MinMaxNearBottomEigenspace
