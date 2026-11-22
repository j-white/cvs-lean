import Mathlib
import Cvs.Finite.EvenMinimisers
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationQuadraticForm
import Cvs.Route.EigenvectorCoordinateCompression
import Cvs.StepA.BandLimitedEvenBottomZeroFree
import Cvs.StepA.Edge.CaseInfinityJointRates
import Cvs.StepA.Edge.FiniteTopGap
import Cvs.StepA.Edge.TopSetCriterion
import Cvs.StepA.EvenBottomNearZeroFrame
import Cvs.StepA.ModePolynomialFarEnvelope
import Cvs.StepA.OddBottomGapCriterion
import Cvs.StepA.OddTrialErrorBudget
import Cvs.StepA.TopQuadruple
import Cvs.Upstream.SymmetricMatrixBottom
import Cvs.Zeta.GaussKernel.ZeroChain
import Cvs.Zeta.GaussKernel.ZetaZeroStatement
import Cvs.Zeta.RiemannXi
import Cvs.Zeta.XiStripZetaHalfPlane
import Cvs.Zeta.ZeroSideMoments

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The even bottom on exponentially many modes from a bound on the depth of the zeros

If every zero off the line has `|Re ρ − 1/2| ≤ d`, then for `δ > d`, any `A` and `ε > 0`, eventually in `L`,
`evLam ≥ −ε e^{δL}` for all `N` with `(2N + 1)/L ≤ e^{AL}` (Cvs.StepA.EvenBottomNearZeroFrame); this holds at `d = θ − 1/2` under a zero-free
half-plane `Re s > θ`, at `d = topDepth` with no hypothesis, and at `L = log x` as an even floor `−ε x^δ` of `M_x`.
-/

noncomputable section

open Real Matrix Filter Topology Asymptotics

namespace Cvs.StepA.EvenBottomZeroDepth
open Cvs.ZeroCounting

open Cvs.Zeta.GaussKernel.AdmissibleKernel (nonTrivialZeroSet)
open Cvs.Finite.SymmetricModeSet (Idx mode negI)
open Cvs.StepA.TopQuadruple (offLine)
open Cvs.StepA.EvenBottomNearZeroFrame (frameHeight)

/-! ### The one-scale bound on an exponential band -/

/-- **The split height on an exponential band**: for `L > 0` and `(2N + 1)/L ≤ e^{AL}`,
`max(4πN/L, 1) ≤ 2π e^{|A| L}`. -/
theorem frameHeight_le {L : ℝ} (hL : 0 < L) {N : ℕ} {A : ℝ}
    (hN : (2 * (N : ℝ) + 1) / L ≤ Real.exp (A * L)) :
    frameHeight L N ≤ 2 * π * Real.exp (|A| * L) := by
  have hA : Real.exp (A * L) ≤ Real.exp (|A| * L) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (le_abs_self A) hL.le)
  have h1 : 1 ≤ Real.exp (|A| * L) := Real.one_le_exp (by positivity)
  refine max_le ?_ ?_
  · have : 2 * (2 * π * N / L) ≤ 2 * π * ((2 * N + 1) / L) := by
      rw [show 2 * (2 * π * (N : ℝ) / L) = 2 * π * (2 * N / L) by ring]
      gcongr; linarith
    calc _ ≤ _ := this
      _ ≤ 2 * π * Real.exp (|A| * L) := by gcongr; exact hN.trans hA
  · nlinarith [Real.pi_gt_three]

/-- **The one-scale bound on an exponential band**: for `0 ≤ d`, `L ≥ 1` and `(2N + 1)/L ≤ e^{AL}`, `EvenBottomNearZeroFrame`'s
bound is at most `K L² e^{dL}` with
`K = 8448 (3 e^{2d} (|A| + log(6π + 5)) + 2 (|A| + log(2π + 5) + 1))`. -/
theorem frameBound_le {d : ℝ} (hd : 0 ≤ d) {L : ℝ} (hL : 1 ≤ L) {N : ℕ} {A : ℝ}
    (hN : (2 * (N : ℝ) + 1) / L ≤ Real.exp (A * L)) :
    8448 * (L + 2) * Real.exp (d * (L + 2)) * Real.log (3 * frameHeight L N + 5)
        + 8448 * (1 / (2 * π) + 1 / L) * cosh (d * L / 2) ^ 2 * (Real.log (frameHeight L N + 5) + 1)
      ≤ 8448 * (3 * Real.exp (2 * d) * (|A| + Real.log (6 * π + 5))
          + 2 * (|A| + Real.log (2 * π + 5) + 1)) * L ^ 2 * Real.exp (d * L) := by
  have hL0 : 0 < L := by linarith
  set H := frameHeight L N with hHdef
  set a := |A| with ha
  have ha0 : 0 ≤ a := abs_nonneg A
  have hH := frameHeight_le hL0 hN
  rw [← hHdef] at hH
  have hH1 : 1 ≤ H := le_max_right _ _
  set E := Real.exp (a * L) with hE
  have hE1 : 1 ≤ E := Real.one_le_exp (by positivity)
  have hlog1 : Real.log (3 * H + 5) ≤ a * L + Real.log (6 * π + 5) := by
    have : 3 * H + 5 ≤ (6 * π + 5) * E := by nlinarith
    calc Real.log (3 * H + 5) ≤ Real.log ((6 * π + 5) * E) :=
          Real.log_le_log (by linarith) this
      _ = a * L + Real.log (6 * π + 5) := by
          rw [Real.log_mul (by positivity) (by positivity), hE, Real.log_exp]; ring
  have hlog2 : Real.log (H + 5) + 1 ≤ a * L + Real.log (2 * π + 5) + 1 := by
    have : H + 5 ≤ (2 * π + 5) * E := by nlinarith
    have h := Real.log_le_log (by linarith) this
    rw [Real.log_mul (by positivity) (by positivity), hE, Real.log_exp] at h
    linarith
  have hc1 : 0 ≤ Real.log (6 * π + 5) := Real.log_nonneg (by nlinarith [Real.pi_gt_three])
  have hc2 : 0 ≤ Real.log (2 * π + 5) := Real.log_nonneg (by nlinarith [Real.pi_gt_three])
  have hcosh : cosh (d * L / 2) ^ 2 ≤ Real.exp (d * L) := by
    have h := Cvs.StepA.OddTrialErrorBudget.cosh_le_exp_abs (d * L / 2)
    rw [abs_of_nonneg (by positivity)] at h
    calc cosh (d * L / 2) ^ 2 ≤ Real.exp (d * L / 2) ^ 2 :=
          pow_le_pow_left₀ (Real.cosh_pos _).le h 2
      _ = Real.exp (d * L) := by rw [← Real.exp_nat_mul]; ring_nf
  have hexp : Real.exp (d * (L + 2)) = Real.exp (2 * d) * Real.exp (d * L) := by
    rw [← Real.exp_add]; ring_nf
  have hinv : 1 / (2 * π) + 1 / L ≤ 2 := by
    have : 1 / (2 * π) ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith [Real.pi_gt_three]
    have : 1 / L ≤ 1 := by rw [div_le_one hL0]; exact hL
    linarith
  have hlog1' : Real.log (3 * H + 5) ≤ (a + Real.log (6 * π + 5)) * L := by nlinarith
  have hlog2' : Real.log (H + 5) + 1 ≤ (a + Real.log (2 * π + 5) + 1) * L := by nlinarith
  have hl1 : 0 ≤ Real.log (3 * H + 5) := Real.log_nonneg (by linarith)
  have hl2 : 0 ≤ Real.log (H + 5) + 1 := by linarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ H + 5)]
  have hdL : 0 < Real.exp (d * L) := Real.exp_pos _
  have hd2 : 0 < Real.exp (2 * d) := Real.exp_pos _
  have t1 : 8448 * (L + 2) * Real.exp (d * (L + 2)) * Real.log (3 * H + 5)
      ≤ 8448 * (3 * Real.exp (2 * d) * (a + Real.log (6 * π + 5))) * L ^ 2 * Real.exp (d * L) := by
    rw [hexp]
    have hL2 : L + 2 ≤ 3 * L := by linarith
    calc 8448 * (L + 2) * (Real.exp (2 * d) * Real.exp (d * L)) * Real.log (3 * H + 5)
        ≤ 8448 * (3 * L) * (Real.exp (2 * d) * Real.exp (d * L)) * ((a + Real.log (6 * π + 5)) * L) := by
          gcongr
      _ = _ := by ring
  have t2 : 8448 * (1 / (2 * π) + 1 / L) * cosh (d * L / 2) ^ 2 * (Real.log (H + 5) + 1)
      ≤ 8448 * (2 * (a + Real.log (2 * π + 5) + 1)) * L ^ 2 * Real.exp (d * L) := by
    have hpos : 0 ≤ 1 / (2 * π) + 1 / L := by positivity
    calc 8448 * (1 / (2 * π) + 1 / L) * cosh (d * L / 2) ^ 2 * (Real.log (H + 5) + 1)
        ≤ 8448 * 2 * Real.exp (d * L) * ((a + Real.log (2 * π + 5) + 1) * L) := by
          gcongr
      _ ≤ 8448 * 2 * Real.exp (d * L) * ((a + Real.log (2 * π + 5) + 1) * L ^ 2) := by
          gcongr
          nlinarith
      _ = _ := by ring
  linarith

/-! ### The even bottom on an exponential band -/

/-- **The even bottom on an exponential band from a depth bound**: if every zero off the line has
`|Re ρ − 1/2| ≤ d`, then for `δ > d`, every `A` and `ε > 0`, eventually in `L`, for every `N` with
`(2N + 1)/L ≤ e^{AL}`, `−ε e^{δL} ≤ evLam` at `(⌈e^L⌉₊, ⌈L/log 2⌉₊)` with `N` modes. -/
theorem eventually_neg_le_evLam_of_depth {d : ℝ}
    (hd : ∀ ρ ∈ offLine, |Cvs.GaussKernel.del ρ| ≤ d) {δ : ℝ} (hδ : d < δ) (A : ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ L in atTop, ∀ hL : 0 < L, ∀ N : ℕ, (2 * (N : ℝ) + 1) / L ≤ Real.exp (A * L) →
      -(ε * Real.exp (δ * L)) ≤ Cvs.Finite.EvenMinimisers.evLam ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊ L hL N := by
  by_cases hne : ∃ ρ, ρ ∈ offLine
  · obtain ⟨ρ₀, hρ₀⟩ := hne
    have hd0 : 0 ≤ d := (abs_nonneg _).trans (hd ρ₀ hρ₀)
    set K := 8448 * (3 * Real.exp (2 * d) * (|A| + Real.log (6 * π + 5))
          + 2 * (|A| + Real.log (2 * π + 5) + 1)) with hK
    have hK0 : 0 < K := by
      have : 0 ≤ Real.log (6 * π + 5) := Real.log_nonneg (by nlinarith [Real.pi_gt_three])
      have : 0 ≤ Real.log (2 * π + 5) := Real.log_nonneg (by nlinarith [Real.pi_gt_three])
      rw [hK]; positivity
    have ho := (isLittleO_pow_exp_pos_mul_atTop 2 (sub_pos.2 hδ)).bound (div_pos hε hK0)
    filter_upwards [ho, eventually_ge_atTop 1] with L hLo hL1 hL N hN
    have h1 := Cvs.StepA.EvenBottomNearZeroFrame.evLam_ge_neg_frame hL N hd
    have h2 := frameBound_le hd0 hL1 hN
    rw [← hK] at h2
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      abs_of_pos (Real.exp_pos _)] at hLo
    have h3 : K * L ^ 2 * Real.exp (d * L) ≤ ε * Real.exp (δ * L) := by
      have := mul_le_mul_of_nonneg_left hLo hK0.le
      have e : K * (ε / K * Real.exp ((δ - d) * L)) * Real.exp (d * L) = ε * Real.exp (δ * L) := by
        have hx : Real.exp ((δ - d) * L) * Real.exp (d * L) = Real.exp (δ * L) := by
          rw [← Real.exp_add]; ring_nf
        rw [show K * (ε / K * Real.exp ((δ - d) * L)) * Real.exp (d * L)
            = (K * (ε / K)) * (Real.exp ((δ - d) * L) * Real.exp (d * L)) by ring, hx,
          mul_div_cancel₀ ε hK0.ne']
      calc K * L ^ 2 * Real.exp (d * L) ≤ K * (ε / K * Real.exp ((δ - d) * L)) * Real.exp (d * L) :=
            mul_le_mul_of_nonneg_right this (Real.exp_pos _).le
        _ = _ := e
    linarith
  · refine Filter.Eventually.of_forall fun L hL N _ => ?_
    have h := Cvs.StepA.BandLimitedEvenBottomZeroFree.neg_restE_le_evLam hL N
    have h0 : Cvs.StepA.Edge.TopSetCriterion.restE L N ∅ = 0 := by
      unfold Cvs.StepA.Edge.TopSetCriterion.restE
      refine (tsum_congr fun ρ => ?_).trans tsum_zero
      exact absurd ⟨ρ.1, ρ.2.1⟩ hne
    rw [h0, neg_zero] at h
    have : 0 < ε * Real.exp (δ * L) := by positivity
    linarith

/-- **The even bottom on an exponential band from a zero-free half-plane**: if every zero of `ξ` has real part
at most `θ`, then for `δ > θ − 1/2`, every `A` and `ε > 0`, eventually in `L`, for every `N` with
`(2N + 1)/L ≤ e^{AL}`, `−ε e^{δL} ≤ evLam`. -/
theorem eventually_neg_le_evLam_frame {θ : ℝ} (h : ∀ ρ : ℂ, Cvs.Zeta.riemannXi ρ = 0 → ρ.re ≤ θ)
    {δ : ℝ} (hδ : θ - 1 / 2 < δ) (A : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ L in atTop, ∀ hL : 0 < L, ∀ N : ℕ, (2 * (N : ℝ) + 1) / L ≤ Real.exp (A * L) →
      -(ε * Real.exp (δ * L)) ≤ Cvs.Finite.EvenMinimisers.evLam ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊ L hL N :=
  eventually_neg_le_evLam_of_depth (fun ρ _ => Cvs.StepA.BandLimitedEvenBottomZeroFree.abs_del_le h ρ) hδ A hε

/-- **The even bottom on an exponential band at `7/8`**: with no zeros of `ζ` on `Re s > 7/8`, for every
`δ > 3/8`, every `A` and `ε > 0`, eventually in `L`, for every `N` with `(2N + 1)/L ≤ e^{AL}`,
`−ε e^{δL} ≤ evLam`. -/
theorem eventually_neg_le_evLam_frame_of_sevenEighths (hz : Cvs.Zeta.XiStripZetaHalfPlane.ZetaFreeAbove (7 / 8))
    {δ : ℝ} (hδ : 3 / 8 < δ) (A : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ L in atTop, ∀ hL : 0 < L, ∀ N : ℕ, (2 * (N : ℝ) + 1) / L ≤ Real.exp (A * L) →
      -(ε * Real.exp (δ * L)) ≤ Cvs.Finite.EvenMinimisers.evLam ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊ L hL N :=
  eventually_neg_le_evLam_frame
    ((Cvs.Zeta.XiStripZetaHalfPlane.re_le_iff_zeta_ne_zero (7 / 8)).2 fun s hs _ => hz s hs)
    (by norm_num; linarith) A hε

/-- **The even bottom on an exponential band above the top depth**: for every `δ > topDepth`, every `A` and
`ε > 0`, eventually in `L`, for every `N` with `(2N + 1)/L ≤ e^{AL}`, `−ε e^{δL} ≤ evLam`. -/
theorem eventually_neg_le_evLam_of_topDepth_lt {δ : ℝ} (hδ : Cvs.StepA.Edge.CaseInfinityJointRates.topDepth < δ) (A : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ L in atTop, ∀ hL : 0 < L, ∀ N : ℕ, (2 * (N : ℝ) + 1) / L ≤ Real.exp (A * L) →
      -(ε * Real.exp (δ * L)) ≤ Cvs.Finite.EvenMinimisers.evLam ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊ L hL N :=
  eventually_neg_le_evLam_of_depth (fun ρ _ => Cvs.StepA.Edge.CaseInfinityJointRates.abs_del_le_topDepth ρ) hδ A hε

/-! ### The floor of the window matrix on polynomial bands -/

/-- **The even floor on polynomial bands from a depth bound**: if every zero off the line has
`|Re ρ − 1/2| ≤ d`, then for `δ > d`, every `A` and `ε > 0`, eventually in `x : ℕ`, every even `ξ` on `N` modes
with `(2N + 1)/log x ≤ x^A` has `−ε x^δ ‖ξ‖² ≤ ξᵀ M(x, ⌈log₂ x⌉, log x) ξ`. -/
theorem eventually_even_floor_rpow_of_depth {d : ℝ}
    (hd : ∀ ρ ∈ offLine, |Cvs.GaussKernel.del ρ| ≤ d) {δ : ℝ} (hδ : d < δ) (A : ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ x : ℕ in atTop, ∀ N : ℕ, (2 * (N : ℝ) + 1) / Real.log x ≤ (x : ℝ) ^ A →
      ∀ ξ : Idx N → ℝ, (∀ i, ξ (negI N i) = ξ i) →
        -(ε * (x : ℝ) ^ δ) * (ξ ⬝ᵥ ξ)
          ≤ ξ ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M x (Nat.clog 2 x) (Real.log x) (mode N) *ᵥ ξ) := by
  have hlog : Tendsto (fun x : ℕ => Real.log x) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hev := hlog.eventually (eventually_neg_le_evLam_of_depth hd hδ A hε)
  filter_upwards [hev, hlog.eventually (eventually_gt_atTop 0)] with x hx hlx N hN ξ hξ
  have hx0 : (0 : ℝ) < x := by
    by_contra h
    have : (x : ℝ) = 0 := le_antisymm (not_lt.1 h) (Nat.cast_nonneg x)
    rw [this, Real.log_zero] at hlx; exact lt_irrefl _ hlx
  have hxpos : 0 < x := by exact_mod_cast hx0
  have hrA : (x : ℝ) ^ A = Real.exp (A * Real.log x) := by
    rw [Real.rpow_def_of_pos hx0]; ring_nf
  have hrδ : (x : ℝ) ^ δ = Real.exp (δ * Real.log x) := by
    rw [Real.rpow_def_of_pos hx0]; ring_nf
  have hb := hx hlx N (hrA ▸ hN)
  obtain ⟨-, -, hmin, -⟩ := Cvs.Finite.EvenMinimisers.evMin_spec ⌈Real.exp (Real.log x)⌉₊
    ⌈Real.log x / Real.log 2⌉₊ hlx N
  have hm := hmin ξ hξ
  rw [Cvs.StepA.OddBottomGapCriterion.ceil_exp_log_natCast hxpos,
    Cvs.Route.EigenvectorCoordinateCompression.natCeil_log_div_log_two_eq_clog] at hm hb
  rw [hrδ]
  have hdot : 0 ≤ ξ ⬝ᵥ ξ := Cvs.Upstream.SymmetricMatrixBottom.dotProduct_self_nonneg' ξ
  exact (mul_le_mul_of_nonneg_right hb hdot).trans hm

/-- **The even floor on polynomial bands above the top depth**: for every `δ > topDepth`, every `A` and
`ε > 0`, eventually in `x : ℕ`, every even `ξ` on `N` modes with `(2N + 1)/log x ≤ x^A` has
`−ε x^δ ‖ξ‖² ≤ ξᵀ M(x, ⌈log₂ x⌉, log x) ξ`. -/
theorem eventually_even_floor_rpow_of_topDepth_lt {δ : ℝ} (hδ : Cvs.StepA.Edge.CaseInfinityJointRates.topDepth < δ)
    (A : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℕ in atTop, ∀ N : ℕ, (2 * (N : ℝ) + 1) / Real.log x ≤ (x : ℝ) ^ A →
      ∀ ξ : Idx N → ℝ, (∀ i, ξ (negI N i) = ξ i) →
        -(ε * (x : ℝ) ^ δ) * (ξ ⬝ᵥ ξ)
          ≤ ξ ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M x (Nat.clog 2 x) (Real.log x) (mode N) *ᵥ ξ) :=
  eventually_even_floor_rpow_of_depth (fun ρ _ => Cvs.StepA.Edge.CaseInfinityJointRates.abs_del_le_topDepth ρ) hδ A hε

end Cvs.StepA.EvenBottomZeroDepth
