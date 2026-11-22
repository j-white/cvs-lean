import Mathlib
import Cvs.Approximant.CosineColumnTailPairing
import Cvs.Approximant.EvenConnesPartLower
import Cvs.Approximant.SpineSubspace
import Cvs.L2a.QSideConnesEndpointUnits
import Cvs.L2a.QSideConnesRelative
import Cvs.L2a.QSideOverFloorDecay
import Cvs.L2a.WindowChainInputsProlate
import Cvs.Limit.ZeroFreeApproximantsRH
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.GroundRungEndpoint
import Cvs.Prolate.SepticLevelComparison
import Cvs.Route.JointGapConnesFromL1
import Cvs.Route.JointGapRayleighExplicit
import Cvs.Route.L1GapConnesRH
import Cvs.Route.L1GapParametricRH
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.InfimumAttainedSphere
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowReflectionSymmetry
import Cvs.Xi.XiValueAtOrigin

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# RH from near-positivity and an even-hyperplane floor at a fixed fraction of the prolate scale

With `connesLrel x ≤ qFactor(x)h₄(1)²` (Cvs.L2a.QSideConnesEndpointUnits), `‖e‖² ≥ (4/25)‖Ξ(0)‖²/(x log x)` (Cvs.Approximant.EvenConnesPartLower) and `QSideOverFloorDecay`'s ladder,
`K connesLrel x/‖e‖² ≤ (ε/2)h₈(1)²/c` eventually, for every `ε > 0`. So `L1GapL connesLrel x` holds whenever
`Q ≥ −s‖·‖²`, the floor `μ ≥ εh₈(1)²/c` on an even hyperplane, and `sK(1 + R(x)) ≤ (ε/4)h₈(1)²/c`.
-/

noncomputable section

open Real Filter Topology
open scoped InnerProductSpace

namespace Cvs.Route.ProlateFloorNearPositivity
open Cvs.ZeroCounting

open Cvs.Prolate.EvenRungsByIndex (rung)
open Cvs.L2a.WindowChainInputsProlate (c0W)
open Cvs.Route.JointGapConnesFromL1 (connesEven connesOdd)
open Cvs.Prolate.GroundRungEndpoint (groundC)

/-- **The prolate floor at scale `x`**, at fraction `ε` of the prolate scale `h₈(1)²/c`, `c = 2πx`: near-positivity
`Q ≥ −s‖·‖²` on the whole window form domain, a floor `μ ≥ εh₈(1)²/c` on the even classes orthogonal to some `η`,
and `s·K(1 + R(x)) ≤ (ε/4)h₈(1)²/c` with `K = √x log x`, `R(x) = 25c⁵x log x/‖Ξ(0)‖²`. -/
def ProlateFloor (ε : ℝ) (x : ℕ) : Prop :=
  ∃ (s μ : ℝ) (η : Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x)),
    (∀ φ : Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x),
      -s * ‖φ‖ ^ 2 ≤ Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) x (Nat.clog 2 x) φ) ∧
    (∀ φ : Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x),
      Cvs.WeilForm.WindowReflectionSymmetry.reflD (Real.log_natCast_nonneg x) φ = φ → ⟪η, φ⟫_ℝ = 0 →
        μ * ‖φ‖ ^ 2 ≤ Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) x (Nat.clog 2 x) φ) ∧
    ε * rung (2 * π * x) 4 1 ^ 2 / (2 * π * x) ≤ μ ∧
    s * (√(x : ℝ) * Real.log x * (1 + Cvs.Route.JointGapRayleighExplicit.Rx x)) ≤ ε / 4 * rung (2 * π * x) 4 1 ^ 2 / (2 * π * x)

/-- `log³x/√x → 0` along the integers. -/
theorem tendsto_log_cube_div_sqrt :
    Tendsto (fun x : ℕ => Real.log x ^ 3 / √(x : ℝ)) atTop (𝓝 0) := by
  have h := ((isLittleO_log_rpow_rpow_atTop 3 (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero).comp
    tendsto_natCast_atTop_atTop
  refine h.congr' (Eventually.of_forall fun x => ?_)
  simp only [Function.comp, Real.sqrt_eq_rpow]
  norm_cast

set_option maxHeartbeats 1000000 in
/-- **The q-side under a fixed fraction of the floor scale**: for `ε > 0`, eventually, at every `x` with
`c₀^W ≤ 2πx`, `K·connesLrel x/‖e‖² ≤ (ε/2)h₈(1)²/c`. -/
theorem eventually_qside_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℕ in atTop, ∀ hx : c0W ≤ 2 * π * x,
      √(x : ℝ) * Real.log x * (Cvs.L2a.QSideConnesRelative.connesLrel x / ‖connesEven (Cvs.Approximant.SpineSubspace.scale80_of_c0W hx)‖ ^ 2)
        ≤ ε / 2 * rung (2 * π * x) 4 1 ^ 2 / (2 * π * x) := by
  have hXi : 0 < ‖Cvs.Limit.ZeroFreeApproximantsRH.Xi 0‖ := norm_pos_iff.mpr fun h => by
    have hp := Cvs.Xi.XiValueAtOrigin.Xi_zero_re_pos
    rw [h, Complex.zero_re] at hp
    exact lt_irrefl 0 hp
  set m₀ := 4 / 25 * ‖Cvs.Limit.ZeroFreeApproximantsRH.Xi 0‖ ^ 2 with hm₀
  have hm₀0 : 0 < m₀ := by positivity
  have hC4 := Cvs.L2a.QSideOverFloorDecay.C4_pos
  have hC0 := Cvs.Prolate.GroundRungEndpoint.groundC_pos
  set A := 4 * 10 ^ 6 / (π * groundC * m₀ * Cvs.L2a.QSideOverFloorDecay.C4) with hAd
  have hA : 0 < A := by positivity
  have hδ : 0 < ε / (2 * A) := by positivity
  filter_upwards [Cvs.Approximant.EvenConnesPartLower.eventually_norm_connesEven_sq_ge, eventually_ge_atTop 80,
    tendsto_log_cube_div_sqrt.eventually (ge_mem_nhds hδ)] with x he hx80 hl3 hx
  have h80 := Cvs.Approximant.SpineSubspace.scale80_of_c0W hx
  have hx' : (80 : ℝ) ≤ x := by exact_mod_cast hx80
  have hx0 : (0 : ℝ) < x := by linarith
  set c := 2 * π * (x : ℝ) with hcd
  have hpi := Real.pi_gt_three
  have hc0 : 0 < c := by positivity
  have hlx : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]; have := Real.exp_one_lt_d9; linarith
  have hsx : 0 < √(x : ℝ) := Real.sqrt_pos.2 hx0
  set K := √(x : ℝ) * Real.log x with hKd
  have hK0 : 0 < K := by positivity
  set E := ‖connesEven h80‖ ^ 2 with hEd
  set m := 4 / 25 * ‖Cvs.Limit.ZeroFreeApproximantsRH.Xi 0‖ ^ 2 / (x * Real.log x) with hm
  have hm0 : 0 < m := by positivity
  have hme : m ≤ E := he h80
  have hE : 0 < E := hm0.trans_le hme
  set h4 := rung c 2 1 ^ 2 with h4d
  set h8 := rung c 4 1 ^ 2 with h8d
  have hh8 : 0 < h8 := by
    have h4e : ∃ χ, Cvs.Prolate.EvenRungsByIndex.IsLevelIdx c 4 χ :=
      Cvs.Prolate.SepticLevelComparison.exists_isLevelIdx_of_le_four (by nlinarith [Real.pi_lt_d2]) le_rfl
    have := Cvs.Prolate.EvenRungsByIndex.rung_one_ne_zero h4e
    positivity
  set q := Cvs.L2a.QSideConnesEndpointUnits.qFactor x with hqd
  have hlc : 0 ≤ Real.log c := Real.log_nonneg (by nlinarith)
  have hq0 : 0 ≤ q := by rw [hqd]; unfold Cvs.L2a.QSideConnesEndpointUnits.qFactor; positivity
  have hL : Cvs.L2a.QSideConnesRelative.connesLrel x ≤ q * h4 := Cvs.L2a.QSideConnesEndpointUnits.connesLrel_le hx
  have hr := Cvs.L2a.QSideOverFloorDecay.ratio_le x hx80
  rw [← hcd] at hr
  -- `K h₄² ≤ (log x/(C₄(2π)³x²√x)) h₈²/c`
  set ρ := Real.log x / (Cvs.L2a.QSideOverFloorDecay.C4 * (2 * π) ^ 3 * ((x : ℝ) ^ 2 * √x)) with hρd
  have hKh : K * h4 ≤ ρ * (h8 / c) := by
    have h1 : c * K * h4 / h8 ≤ ρ := hr
    rw [div_le_iff₀ hh8] at h1
    rw [mul_div_assoc', le_div_iff₀ hc0]
    linarith
  -- the coefficient
  have hlog2π : Real.log c ≤ 2 + Real.log x := by
    rw [hcd, Real.log_mul (by positivity) hx0.ne']
    have : Real.log (2 * π) ≤ 2 := by
      rw [Real.log_le_iff_le_exp (by positivity)]
      have := Real.exp_one_gt_d9
      have h2 : exp 2 = exp 1 * exp 1 := by rw [← Real.exp_add]; norm_num
      nlinarith [Real.pi_lt_d2]
    linarith
  have hG : q * (x * Real.log x / m₀) * ρ ≤ ε / 2 := by
    have e : q * (x * Real.log x / m₀) * ρ
        = 10 ^ 6 * (1 + Real.log c) * Real.log x ^ 2 / (π * groundC * m₀ * Cvs.L2a.QSideOverFloorDecay.C4 * √x) := by
      rw [hqd, hρd]; unfold Cvs.L2a.QSideConnesEndpointUnits.qFactor; rw [← hcd, hcd]; field_simp
    rw [e]
    have h1 : 10 ^ 6 * (1 + Real.log c) * Real.log x ^ 2 ≤ 4 * 10 ^ 6 * Real.log x ^ 3 := by
      have : 1 + Real.log c ≤ 4 * Real.log x := by linarith
      have hl2 : 0 ≤ Real.log x ^ 2 := sq_nonneg _
      nlinarith
    have hD : 0 < π * groundC * m₀ * Cvs.L2a.QSideOverFloorDecay.C4 * √x := by positivity
    calc 10 ^ 6 * (1 + Real.log c) * Real.log x ^ 2 / (π * groundC * m₀ * Cvs.L2a.QSideOverFloorDecay.C4 * √x)
        ≤ 4 * 10 ^ 6 * Real.log x ^ 3 / (π * groundC * m₀ * Cvs.L2a.QSideOverFloorDecay.C4 * √x) :=
          div_le_div_of_nonneg_right h1 hD.le
      _ = A * (Real.log x ^ 3 / √x) := by rw [hAd]; field_simp
      _ ≤ A * (ε / (2 * A)) := mul_le_mul_of_nonneg_left hl3 hA.le
      _ = ε / 2 := by field_simp
  -- assemble
  have h1 : K * (Cvs.L2a.QSideConnesRelative.connesLrel x / E) ≤ K * (q * h4 / m) := by
    refine mul_le_mul_of_nonneg_left ?_ hK0.le
    calc Cvs.L2a.QSideConnesRelative.connesLrel x / E ≤ q * h4 / E := div_le_div_of_nonneg_right hL hE.le
      _ ≤ q * h4 / m := div_le_div_of_nonneg_left (by positivity) hm0 hme
  have e2 : K * (q * h4 / m) = q * (x * Real.log x / m₀) * (K * h4) := by
    rw [hm, hm₀]; field_simp
  have h2 : q * (x * Real.log x / m₀) * (K * h4) ≤ q * (x * Real.log x / m₀) * (ρ * (h8 / c)) :=
    mul_le_mul_of_nonneg_left hKh (by positivity)
  have h3 : q * (x * Real.log x / m₀) * (ρ * (h8 / c)) ≤ ε / 2 * (h8 / c) := by
    rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hG (by positivity)
  calc K * (Cvs.L2a.QSideConnesRelative.connesLrel x / E) ≤ ε / 2 * (h8 / c) := by linarith
    _ = ε / 2 * h8 / c := by ring

/-- **The prolate floor gives L1's gap against the proved q-side**, eventually in `x`. -/
theorem eventually_l1GapL_of_prolateFloor {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℕ in atTop, ProlateFloor ε x → Cvs.Route.L1GapParametricRH.L1GapL Cvs.L2a.QSideConnesRelative.connesLrel x := by
  have hc0W : ∀ᶠ x : ℕ in atTop, c0W ≤ 2 * π * x := by
    have h : Tendsto (fun x : ℕ => 2 * π * (x : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity)
    exact h.eventually (eventually_ge_atTop c0W)
  filter_upwards [hc0W, eventually_qside_le hε, Cvs.Approximant.EvenConnesPartLower.eventually_norm_connesEven_sq_ge, eventually_ge_atTop 3]
    with x hx hq he hx3 hP
  obtain ⟨s, μ, η, hneg, hfloor, hμ, hs⟩ := hP
  refine ⟨hx, s, μ, η, hneg, hfloor, ?_⟩
  have h80 := Cvs.Approximant.SpineSubspace.scale80_of_c0W hx
  have hx0 : (0 : ℝ) < x := by have := Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale h80; linarith
  set c := 2 * π * (x : ℝ) with hcd
  have hc0 : 0 < c := by positivity
  set K := √(x : ℝ) * Real.log x with hKd
  have hK1 : 1 ≤ K := Cvs.Route.L1GapConnesRH.one_le_K hx3
  have hXi : 0 < ‖Cvs.Limit.ZeroFreeApproximantsRH.Xi 0‖ := norm_pos_iff.mpr fun h => by
    have hp := Cvs.Xi.XiValueAtOrigin.Xi_zero_re_pos
    rw [h, Complex.zero_re] at hp
    exact lt_irrefl 0 hp
  have hlx : 0 < Real.log (x : ℝ) := Real.log_pos (Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale h80)
  set E := ‖connesEven h80‖ ^ 2 with hEd
  set m := 4 / 25 * ‖Cvs.Limit.ZeroFreeApproximantsRH.Xi 0‖ ^ 2 / (x * Real.log x) with hm
  have hm0 : 0 < m := by positivity
  have hme : m ≤ E := he h80
  have hE : 0 < E := hm0.trans_le hme
  set O := ‖connesOdd h80‖ ^ 2 with hOd
  have hO0 : 0 ≤ O := sq_nonneg _
  have hOR : O / E ≤ Cvs.Route.JointGapRayleighExplicit.Rx x := by
    have ho := Cvs.Route.JointGapRayleighExplicit.norm_connesOdd_sq_le x hx
    calc O / E ≤ 4 * (2 * π * x) ^ 5 / E := div_le_div_of_nonneg_right ho hE.le
      _ ≤ 4 * (2 * π * x) ^ 5 / m := div_le_div_of_nonneg_left (by positivity) hm0 hme
      _ = Cvs.Route.JointGapRayleighExplicit.Rx x := by rw [hm]; unfold Cvs.Route.JointGapRayleighExplicit.Rx; field_simp
  have hOE0 : 0 ≤ O / E := div_nonneg hO0 hE.le
  set h8 := rung c 4 1 ^ 2 with h8d
  have hh8 : 0 < h8 := by
    have h4e : ∃ χ, Cvs.Prolate.EvenRungsByIndex.IsLevelIdx c 4 χ :=
      Cvs.Prolate.SepticLevelComparison.exists_isLevelIdx_of_le_four (by
        have := Cvs.L2a.QSideConnesRelative.hundred_le hx; nlinarith [Real.pi_lt_d2, hcd]) le_rfl
    have := Cvs.Prolate.EvenRungsByIndex.rung_one_ne_zero h4e
    positivity
  -- the `s` part
  have hsT : s * (K * (O / E) + K - 1) ≤ ε / 4 * h8 / c := by
    have hb : 0 ≤ ε / 4 * h8 / c := by positivity
    rcases le_or_gt s 0 with hs0 | hs0
    · have : 0 ≤ K * (O / E) + K - 1 := by nlinarith
      nlinarith
    · have : K * (O / E) + K - 1 ≤ K * (1 + Cvs.Route.JointGapRayleighExplicit.Rx x) := by nlinarith
      calc s * (K * (O / E) + K - 1) ≤ s * (K * (1 + Cvs.Route.JointGapRayleighExplicit.Rx x)) :=
            mul_le_mul_of_nonneg_left this hs0.le
        _ ≤ _ := hs
  have hsplit : K * ((Cvs.L2a.QSideConnesRelative.connesLrel x + s * O) / E) + (K - 1) * s
      = K * (Cvs.L2a.QSideConnesRelative.connesLrel x / E) + s * (K * (O / E) + K - 1) := by
    field_simp; ring
  rw [hsplit]
  have hlt : ε / 2 * h8 / c + ε / 4 * h8 / c < ε * h8 / c := by
    have : 0 < ε * h8 / c := by positivity
    have e : ε / 2 * h8 / c + ε / 4 * h8 / c = 3 / 4 * (ε * h8 / c) := by ring
    linarith
  have := hq hx
  linarith

/-- **RH from the prolate floor**: if for some `ε > 0`, at infinitely many integers `x`, the Weil form is
`−s`-near-positive and has an even-hyperplane floor `μ ≥ εh₈(1)²/(2πx)` with `sK(1 + R(x)) ≤ (ε/4)h₈(1)²/(2πx)`,
then the Riemann hypothesis holds. -/
theorem riemannHypothesis_of_prolateFloor {ε : ℝ} (hε : 0 < ε) (h : ∃ᶠ x : ℕ in atTop, ProlateFloor ε x) :
    RiemannHypothesis :=
  Cvs.L2a.QSideConnesRelative.riemannHypothesis_of_L1GapRel
    ((h.and_eventually (eventually_l1GapL_of_prolateFloor hε)).mono fun _ ⟨hp, himp⟩ => himp hp)

/-- **RH from an exact floor**: `s = 0` (the Weil form is nonnegative on the window domain) and an even-hyperplane floor
`μ ≥ εh₈(1)²/(2πx)` at infinitely many integers `x`, for some `ε > 0`, give the Riemann hypothesis. -/
theorem riemannHypothesis_of_prolateFloor_nonneg {ε : ℝ} (hε : 0 < ε)
    (h : ∃ᶠ x : ℕ in atTop, ∃ (μ : ℝ) (η : Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x)),
      (∀ φ : Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x),
        0 ≤ Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) x (Nat.clog 2 x) φ) ∧
      (∀ φ : Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x),
        Cvs.WeilForm.WindowReflectionSymmetry.reflD (Real.log_natCast_nonneg x) φ = φ → ⟪η, φ⟫_ℝ = 0 →
          μ * ‖φ‖ ^ 2 ≤ Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) x (Nat.clog 2 x) φ) ∧
      ε * rung (2 * π * x) 4 1 ^ 2 / (2 * π * x) ≤ μ) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_prolateFloor hε (h.mono fun x ⟨μ, η, hpos, hfloor, hμ⟩ => ?_)
  refine ⟨0, μ, η, fun φ => by simpa using hpos φ, hfloor, hμ, ?_⟩
  have : 0 ≤ rung (2 * π * x) 4 1 ^ 2 := sq_nonneg _
  have : (0 : ℝ) ≤ 2 * π * x := by positivity
  rw [zero_mul]
  positivity

end Cvs.Route.ProlateFloorNearPositivity
