import Mathlib
import Cvs.Upstream.Hurwitz
import Cvs.Finite.EigenvectorFormRealSpectrum
import Cvs.Finite.SecularRootsReal
import Cvs.WeilForm.BottomAttained
import Cvs.Limit.ZeroFreeApproximantsRH
import Cvs.Finite.TruncationQuadraticForm
import Cvs.Finite.EvenBottomRealRoots
import Cvs.Limit.LimitSeesXiZeros
import Cvs.Limit.SpineWithoutSimplicity
import Cvs.Xi.RiemannPhiEven
import Cvs.Prolate.EvenRungsByIndex
import Cvs.WeilForm.PositivityOfRH
import Cvs.WeilForm.WindowWeilCriterion
import Cvs.WeilForm.ApproxWindowPositivityRH
import Cvs.Xi.XiOffRealLine
import Cvs.WeilForm.MatrixPSDCriterion
import Cvs.Xi.PoissonDualitySummationE
import Cvs.StepA.StepAAlongEveryBandwidth
import Cvs.TheoremSixOne.MinimiserTransformRealZeros
import Cvs.Approximant.FactSixFour
import Cvs.Composition.ConnesSectionSix
import Cvs.StepA.ConnesStepAOddAbove
import Cvs.StepA.ConnesStepAModeCount
import Cvs.StepA.ProlateOperatorStepA
import Cvs.Prolate.Envelope.RungDuhamelRemainder
import Cvs.Prolate.SincOperatorEigenCount
import Cvs.Prolate.GroundConcentrationStrict
import Cvs.WeilForm.WindowTestSelfAdjoint
import Cvs.WeilForm.WindowTestWeilCriterion
import Cvs.StepA.OddGroundStateSimple
import Cvs.StepA.MinimiserDefiniteParity
import Cvs.StepA.CircleEvenModesSimpleIsolated
import Cvs.Route.TerminalFloorAlongScales
import Cvs.StepA.EvenBottomZeroDepth

/-!
# Connes' §6, the statements

The headline results of the project, in the order of Connes, *The Riemann Hypothesis: past,
present and a letter through time* (arXiv:2602.04022), §6. Each is a one-line restatement
of the theorem that proves it, so this file is the map of the project: follow the name to the
proof.

| Connes | here |
|---|---|
| Theorem 6.1, finite matrices | `finite_real_spectrum`, `finite_secular_roots_real`, `even_sector_secular` |
| Theorem 6.1 for `QW_λ` | `ConnesStepA`, `theorem_6_1`, `theorem_6_1_uncentred` |
| Theorem 6.1 at `λ = √2` | `theorem_6_1_at_sqrt_two` |
| Fact 6.2 (Ξ, Φ, `E`, Poisson) | `Xi`, `xi_eq_fourierLaplace`, `riemannPhi_even`, `poisson_E` |
| Fact 6.3 (prolates) | `prolate_eigen`, `prolate_sinc_eigen`, `prolate_lam_lt_one`, `prolate_one_sub_lam_le`, `prolate_stepA` |
| §6.4 (`QW_λ`, bottom, positivity) | `bottom_attained`, `weil_matrix`, `rh_iff_weil_positivity`, `rh_iff_approx_weil_positivity`, `rh_iff_posSemidef` |
| Fact 6.4 (`k̂_λ → Ξ`) | `fact_6_4`, `fact_6_4_error` |
| §6.6 (remaining steps) | `stepA_finite_of_stepA`, `rh_of_connes`, `rh_iff_stepA_along_bandwidths` |
-/

noncomputable section

open Real Filter Topology

namespace Cvs

/-! ## §6.1 Theorem 6.1 for finite matrices -/

/-- **Theorem 6.1, finite form (spectrum).** For a positive semidefinite divided-difference matrix
whose kernel is the line through an even `ξ` with `Σ ξ = 1`, the rank-one perturbation `D′` has
no non-real eigenvalue. -/
alias finite_real_spectrum := Cvs.Finite.EigenvectorFormRealSpectrum.Dprime_real_spectrum

/-- **Theorem 6.1, finite form (secular roots).** Under the same hypotheses every root of the
secular sum `Σ ξ_j/(p_j − s)` is real. -/
alias finite_secular_roots_real := Cvs.Finite.SecularRootsReal.root_im_eq_zero

/-- **Theorem 6.1, even sector.** A simple even-sector bottom has a secular function
`Σ ξ_i/(ω_i² − w)` with no non-real zero; the odd sector plays no role. -/
alias even_sector_secular := Cvs.Finite.EvenBottomRealRoots.secular_ne_zero

/-- **Theorem 6.1, finite form (transform).** A divided-difference matrix with simple shifted
bottom has a truncation transform with no zero off the real axis. -/
alias finite_transform_zeroFree := Cvs.TheoremSixOne.MinimiserTransformRealZeros.zeroFree_nonReal

/-- **Theorem 6.1 for every truncation.** At every scale and mode count there is an even unit
ground state of the truncated Weil matrix whose transform has no zero off the two axes. -/
alias exists_zeroFree_even_ground := Cvs.Limit.SpineWithoutSimplicity.exists_zeroFree_even_ground

/-! ## §6.1 Theorem 6.1 for the Weil form `QW_λ` -/

/-- Connes' Step A (§6.6) for `QW_λ` at scale `L`: bottom attained at `η ≠ 0`, simple, even. -/
abbrev ConnesStepA := @Cvs.TheoremSixOne.MinimiserTransformRealZeros.ConnesStepA

/-- **Theorem 6.1 for `QW_λ`.** Under Step A every zero of the Fourier transform of the
minimiser, recentred to `[−L/2, L/2]`, is real. -/
alias theorem_6_1 := Cvs.TheoremSixOne.MinimiserTransformRealZeros.im_eq_zero_of_centred_eq_zero

/-- **Theorem 6.1 for `QW_λ`, uncentred.** -/
alias theorem_6_1_uncentred := Cvs.TheoremSixOne.MinimiserTransformRealZeros.im_eq_zero_of_transform_eq_zero

/-- **Theorem 6.1 at `λ = √2`, unconditionally.** At `L = log 2` Step A holds and `θ̂` has only
real zeros. -/
alias theorem_6_1_at_sqrt_two := Cvs.Composition.ConnesSectionSix.exists_connesStepA_x2

/-! ## §6.1 The limit -/

/-- **Hurwitz.** A locally uniform limit of zero-free holomorphic functions on a connected open
set is zero-free or identically zero. -/
alias hurwitz := Cvs.Upstream.Hurwitz.ne_zero_of_zeroFree_of_tendstoLocallyUniformlyOn

/-- **RH from Ξ on the strip.** If `Ξ` has no zero with `0 < |Im z| < 1/2`, RH holds. -/
alias rh_of_Xi_ne_zero := Cvs.Composition.ConnesSectionSix.riemannHypothesis_of_Xi_ne_zero

/-- **RH from a limit.** Zero-free entire functions converging to a function that sees Ξ's
off-line zeros give RH. -/
alias rh_of_limit := Cvs.Limit.LimitSeesXiZeros.riemannHypothesis_of_limit

/-- **RH from converging ground states.** -/
alias rh_of_ground := Cvs.Limit.SpineWithoutSimplicity.riemannHypothesis_of_ground

/-! ## §6.2 Fact 6.2 -/

/-- Riemann's `Ξ(z) = ξ(1/2 + iz)`. -/
abbrev Xi := Cvs.Limit.ZeroFreeApproximantsRH.Xi

/-- **Ξ is a Fourier–Laplace transform of Riemann's Φ** on `|Im z| < 1`. -/
alias xi_eq_fourierLaplace := Cvs.Xi.XiOffRealLine.Xi_eq_two_mul_fourierLaplace

/-- **Φ is even**: `k(u) = k(1/u)` in the logarithmic variable. -/
alias riemannPhi_even := Cvs.Xi.RiemannPhiEven.riemannPhi_neg

/-- **The Poisson formula (18)**: `E f(u) = E(𝓕 f)(1/u)` for even `f` with `f(0) = 𝓕f(0) = 0`. -/
alias poisson_E := Cvs.Xi.PoissonDualitySummationE.E_eq_E_fourier

/-! ## §6.3 Fact 6.3 -/

/-- **The finite Fourier transform fixes each prolate function up to its eigenvalue.** -/
alias prolate_eigen := Cvs.Prolate.EvenRungsByIndex.psi_rung

/-- **The prolate functions diagonalise time–band limiting** (the sinc kernel). -/
alias prolate_sinc_eigen := Cvs.Prolate.SincOperatorEigenCount.integral_sincKer_mul_rung

/-- **Every concentration eigenvalue is below one.** -/
alias prolate_lam_lt_one := Cvs.Prolate.GroundConcentrationStrict.lamR_lt_one

/-- **`1 − λ_k` is exponentially small** in the bandwidth. -/
alias prolate_one_sub_lam_le := Cvs.Prolate.Envelope.RungDuhamelRemainder.one_sub_lamR_le_exp

/-- **The prolate analogue of Step A**: the ground level of the prolate operator is below every
odd level, simple and even, on `[−1, 1]` and on Connes' `[−λ, λ]`. -/
alias prolate_stepA := Cvs.StepA.ProlateOperatorStepA.prolate_stepA

/-! ## §6.4 The truncated Weil form -/

/-- **The bottom of `QW_λ` is attained.** -/
alias bottom_attained := Cvs.WeilForm.BottomAttained.exists_bottom_attained

/-- **The trigonometric matrix is the Weil form** on trigonometric polynomials. -/
alias weil_matrix := Cvs.Finite.TruncationQuadraticForm.quadForm_eq_weil

/-- **RH ⟺ Weil positivity of `QW_λ`** at every integer scale `x ≥ x₀`. -/
alias rh_iff_weil_positivity := Cvs.WeilForm.WindowWeilCriterion.rh_iff_windowPos

/-- **RH ⟺ approximate Weil positivity.** -/
alias rh_iff_approx_weil_positivity := Cvs.WeilForm.ApproxWindowPositivityRH.rh_iff_approx_windowPos

/-- **RH ⇒ `QW_λ ≥ 0`.** -/
alias weil_nonneg_of_rh := Cvs.WeilForm.PositivityOfRH.Q_nonneg_of_RH

/-- **RH ⟺ every truncation matrix is positive semidefinite.** -/
alias rh_iff_posSemidef := Cvs.WeilForm.MatrixPSDCriterion.rh_iff_posSemidef

/-! ## §6.5 Fact 6.4 -/

/-- **Fact 6.4.** `(overlap(2πx)/16)·k̂_λ → Ξ` uniformly on every closed substrip `|Im z| ≤ a`,
`a < 1/2`. -/
alias fact_6_4 := Cvs.Approximant.FactSixFour.tendstoUniformlyOn_mellinHat_kLambda

/-- **Fact 6.4 with an explicit error** at each scale `x ≥ 16`. -/
alias fact_6_4_error := Cvs.Approximant.FactSixFour.norm_mellinHat_kLambda_sub_Xi_le

/-! ## §6.6 Remaining steps -/

/-- **Step A for `QW_λ` gives Step A for all fine enough truncations.** -/
alias stepA_finite_of_stepA := Cvs.StepA.ConnesStepAModeCount.eventually_connesStepAN_of_connesStepA

/-- **Step A gives a strict odd gap for all fine enough truncations.** -/
alias oddAbove_of_stepA := Cvs.StepA.ConnesStepAOddAbove.eventually_oddAbove_of_connesStepA

/-- **Connes' §6, assembled.** Along scales `x_n → ∞`: Step A at every scale, Fact 6.4 and
Step B give the Riemann Hypothesis. -/
alias rh_of_connes := Cvs.Composition.ConnesSectionSix.riemannHypothesis_of_connes

/-- **Step A plus convergence to Ξ gives RH.** -/
alias rh_of_stepA_of_tendsto := Cvs.Composition.ConnesSectionSix.riemannHypothesis_of_connesStepA_of_tendsto

/-- **RH ⟺ step (a) along every fixed bandwidth, and `DepthToZero`.** No other hypothesis. -/
alias rh_iff_stepA_along_bandwidths :=
  Cvs.Finite.OddDisplacementPencil.riemannHypothesis_iff_forall_stepAAlong_and_depthToZero

/-! ## Further results on §6.4 and §6.6

The Weil form on the window's smooth test functions `𝓓((0, log x), ℝ)`, where the operator
`1/4 − d²/du²` is self-adjoint; and ingredients of Step A for the even and odd sectors. -/

/-- **`d/du` is skew for the Weil form** on `𝓓((0, log x), ℝ)`, `x ≥ 2`. -/
alias weil_deriv_skew := Cvs.WeilForm.WindowTestSelfAdjoint.isSkewAdjoint_opD

/-- **`1/4 − d²/du²` is self-adjoint for the Weil form** on `𝓓((0, log x), ℝ)`, `x ≥ 2`.
No hypothesis. -/
alias weil_operator_selfAdjoint := Cvs.WeilForm.WindowTestSelfAdjoint.isSelfAdjoint_opT

/-- **RH ⟺ the Weil form is nonnegative on `𝓓((0, log x), ℝ)` at every `x ≥ x₀`.** -/
alias rh_iff_window_test_positivity := Cvs.WeilForm.WindowTestWeilCriterion.rh_iff_forall_weil_nonneg

/-- **RH ⟺ Parseval for the zero samples**: `W(f, f) = Σ_ρ m_ρ |f̂(ρ)|²` on `𝓓((0, log x), ℝ)`. -/
alias rh_iff_zero_sample_parseval := Cvs.WeilForm.WindowTestWeilCriterion.rh_iff_forall_hasSum_parseval

/-- **The odd sector's ground state is simple**: a diagonal form with a negative rank-one term has,
up to scale, one minimiser. -/
alias odd_ground_state_simple := Cvs.StepA.OddGroundStateSimple.minimiser_unique_of_neg

/-- **A minimiser has definite parity**: when the even floor is strictly lower, the minimiser is
purely even. -/
alias minimiser_even_of_lt := Cvs.StepA.MinimiserDefiniteParity.even_of_lt

/-- **Step (a) on the even modes of the circle**: the ground state exists, lies strictly between the
two lowest diagonal levels, is simple, and no other eigenvalue shares that interval. -/
alias stepA_circle_even := Cvs.StepA.CircleEvenModesSimpleIsolated.weil_even_circle_simple_isolated

/-- **RH ⟺ the even bulk floor at loss `x^ε` along any infinite set of scales.** -/
alias rh_iff_floor_along_scales := Cvs.Route.TerminalFloorAlongScales.rh_iff_hFAlong

/-- **The even bottom on an exponential band from a depth bound on the zeros off the line.** -/
alias even_bottom_of_zero_depth := Cvs.StepA.EvenBottomZeroDepth.eventually_neg_le_evLam_of_depth

end Cvs
