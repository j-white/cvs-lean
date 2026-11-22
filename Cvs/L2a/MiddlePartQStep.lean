import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.CleanBandDilation
import Cvs.L2a.CornerSplitSqrtFloor
import Cvs.L2a.CutKernels
import Cvs.L2a.DilationCornerSplit
import Cvs.L2a.FarFarBound
import Cvs.L2a.FarIntegrationByParts
import Cvs.L2a.OrbitGapGrowth
import Cvs.L2a.QIdentityComplexWeight
import Cvs.L2a.QIdentityCutPoint
import Cvs.L2a.QIdentityIterated
import Cvs.L2a.QIdentityRealWeight
import Cvs.L2a.RampTopQuadratic
import Cvs.L2a.SigmaSquareMultiplier
import Cvs.Prolate.Gram.RungGramFloorAtInfinity
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.RungExactOrthogonality
import Cvs.Upstream.CosineTransformHalfLine
import Cvs.Upstream.QuinticSmoothStep

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The middle part: one bulk-only Q-step on `wMid`

`wMid = 1 − w_b − w_t`, so the three Q-steps share their cut samples and `Dmid = D₁ − Γ_bot − R_top`, with `D₁` the
weight-one bulk; `Dbot + Dmid + Dtop` is the `δ`-free weight-one Q-step. Lemma PS bounds `D₁` on `t > M` (ratio `4/15`)
and on `t ∈ (1, 2)`, `m ≥ 3` (ratio `9/49`); Lemma LP with `1 − wF ≤ π²(2 − t)²` bounds the `m = 2` strip. Uniformly in
`M`, `|D₁| ≤ (r₁ + r_S)P` with `r₁ = O(c^{−1/2})` and `r_S(c, s₀c) = O(c^{−1/4})`.
-/

noncomputable section

namespace Cvs.L2a.MiddlePartQStep

open Real Set Filter Topology MeasureTheory Complex
open Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.AngularProlateTailPositive Cvs.Prolate.Gram.RungGramFloorAtInfinity Cvs.L2a.FarIntegrationByParts Cvs.L2a.CleanBandDilation Cvs.L2a.QIdentityComplexWeight Cvs.L2a.CutKernels

variable {ι : Type} [Fintype ι]

/-! ### The weight-one bulk -/

/-- The weight-one bulk `(κ/m)Re Σᵢ aᵢ∫_m^M eψᵢR[1]` at `y = t/m`. -/
def bulkOne (c : ℝ) (χ : ι → ℝ) (g : ι → ℝ → ℝ) (a : ι → ℝ) (M m : ℕ) (t : ℝ) : ℝ :=
  √(2 * c / π) / m * (∑ i, (a i : ℂ) * ∫ x in (m : ℝ)..M, eF c (t / m) x * (psi c (g i) x : ℂ)
    * rRc (fun _ => 1) (fun _ => 0) (fun _ => 0) c (χ i) (t / m) x).re

/-- `D₁ = −2Σ_m∫_{(1,∞)} ū·bulk₁_m`. -/
def DOne (c : ℝ) (χ : ι → ℝ) (g : ι → ℝ → ℝ) (a : ι → ℝ) (M : ℕ) : ℝ :=
  -2 * ∑ m ∈ Finset.Icc 2 (M - 1),
    ∫ t in Ioi 1, ubar (fun ξ => ∑ i, a i * psi c (g i) ξ) wF M t * bulkOne c χ g a M m t

/-- `wMid` is continuous for the quintic step. -/
theorem continuous_wMid (δ M m : ℝ) : Continuous fun x => Cvs.L2a.CornerSplitSqrtFloor.wMidG Cvs.Upstream.QuinticSmoothStep.S δ M m x := by
  unfold Cvs.L2a.CornerSplitSqrtFloor.wMidG
  exact (continuous_const.sub (continuous_wG_S δ m).1).sub (continuous_wG_S δ M).2

/-- The middle cut `wMid 1_(m,M]Φ` is `1_(m,M](wMid Φ)`. -/
theorem wMid_cut_eq (Φ : ℝ → ℝ) (δ m M : ℝ) :
    (fun x => Cvs.L2a.CornerSplitSqrtFloor.wMidG Cvs.Upstream.QuinticSmoothStep.S δ M m x * (Ioc m M).indicator Φ x)
      = (Ioc m M).indicator (fun x => Cvs.L2a.CornerSplitSqrtFloor.wMidG Cvs.Upstream.QuinticSmoothStep.S δ M m x * Φ x) := by
  funext x
  by_cases hx : x ∈ Ioc m M <;> simp [hx]

/-- **The three Q-steps on one rung**: `∫_m^M wMid ψe = ∫_m^M eψR[1] − ∫_m^{m+δ} eψR[w_b] − ∫_{M−δ}^M eψR[w_t]`;
the cut samples at `m` and `M` cancel. -/
theorem integral_wMid_eq {g g₁ g₂ : ℝ → ℝ} {c χ y : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hc : 0 < c) (hy : 0 < y) {m M δ : ℝ} (hm : 1 < m) (hδ0 : 0 < δ) (hmM : m + δ ≤ M - δ) :
    ∫ x in m..M, ((Cvs.L2a.CornerSplitSqrtFloor.wMidG Cvs.Upstream.QuinticSmoothStep.S δ M m x : ℝ) : ℂ) * (psi c g x : ℂ) * eF c y x
      = (∫ x in m..M, eF c y x * (psi c g x : ℂ) * rRc (fun _ => 1) (fun _ => 0) (fun _ => 0) c χ y x)
        - (∫ x in m..m + δ, eF c y x * (psi c g x : ℂ) * rRc (Cvs.L2a.CornerSplitSqrtFloor.wbC δ m) (Cvs.L2a.CornerSplitSqrtFloor.wbC₁ δ m) (Cvs.L2a.CornerSplitSqrtFloor.wbC₂ δ m) c χ y x)
        - ∫ x in M - δ..M, eF c y x * (psi c g x : ℂ) * rRc (Cvs.L2a.CornerSplitSqrtFloor.wtC δ M) (Cvs.L2a.CornerSplitSqrtFloor.wtC₁ δ M) (Cvs.L2a.CornerSplitSqrtFloor.wtC₂ δ M) c χ y x := by
  obtain ⟨-, -, hψc, -⟩ := rung_system hg hg₁ hg₂c hang
  have hψe : Continuous fun x => (psi c g x : ℂ) * eF c y x := (continuous_ofReal.comp hψc).mul (continuous_eF c y).1
  have hbc : Continuous fun x => ((Cvs.L2a.CornerSplitSqrtFloor.wBotG Cvs.Upstream.QuinticSmoothStep.S δ m x : ℝ) : ℂ) :=
    continuous_ofReal.comp (continuous_wG_S δ m).1
  have htc : Continuous fun x => ((Cvs.L2a.CornerSplitSqrtFloor.wTopG Cvs.Upstream.QuinticSmoothStep.S δ M x : ℝ) : ℂ) :=
    continuous_ofReal.comp (continuous_wG_S δ M).2
  have hii : ∀ (f : ℝ → ℂ), Continuous f → ∀ α β : ℝ,
      IntervalIntegrable (fun x => f x * (psi c g x : ℂ) * eF c y x) volume α β := fun f hf α β =>
    ((hf.mul (continuous_ofReal.comp hψc)).mul (continuous_eF c y).1).intervalIntegrable _ _
  -- the pointwise split `wMid = 1 − w_b − w_t`
  have hsplit : ∫ x in m..M, ((Cvs.L2a.CornerSplitSqrtFloor.wMidG Cvs.Upstream.QuinticSmoothStep.S δ M m x : ℝ) : ℂ) * (psi c g x : ℂ) * eF c y x
      = (∫ x in m..M, (fun _ => (1 : ℂ)) x * (psi c g x : ℂ) * eF c y x)
        - (∫ x in m..M, ((Cvs.L2a.CornerSplitSqrtFloor.wBotG Cvs.Upstream.QuinticSmoothStep.S δ m x : ℝ) : ℂ) * (psi c g x : ℂ) * eF c y x)
        - ∫ x in m..M, ((Cvs.L2a.CornerSplitSqrtFloor.wTopG Cvs.Upstream.QuinticSmoothStep.S δ M x : ℝ) : ℂ) * (psi c g x : ℂ) * eF c y x := by
    rw [← intervalIntegral.integral_sub (hii _ continuous_const m M) (hii _ hbc m M),
      ← intervalIntegral.integral_sub ((hii _ continuous_const m M).sub (hii _ hbc m M)) (hii _ htc m M)]
    refine intervalIntegral.integral_congr fun x _ => ?_
    simp only [Cvs.L2a.CornerSplitSqrtFloor.wMidG, Complex.ofReal_sub, Complex.ofReal_one]
    ring
  -- `w_b` lives on `[m, m + δ]`, `w_t` on `[M − δ, M]`
  have hbot : ∫ x in m..M, ((Cvs.L2a.CornerSplitSqrtFloor.wBotG Cvs.Upstream.QuinticSmoothStep.S δ m x : ℝ) : ℂ) * (psi c g x : ℂ) * eF c y x
      = ∫ x in m..m + δ, ((Cvs.L2a.CornerSplitSqrtFloor.wBotG Cvs.Upstream.QuinticSmoothStep.S δ m x : ℝ) : ℂ) * (psi c g x : ℂ) * eF c y x := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hii _ hbc m (m + δ)) (hii _ hbc (m + δ) M)]
    have h0 : ∫ x in m + δ..M, ((Cvs.L2a.CornerSplitSqrtFloor.wBotG Cvs.Upstream.QuinticSmoothStep.S δ m x : ℝ) : ℂ) * (psi c g x : ℂ) * eF c y x = 0 := by
      refine intervalIntegral.integral_zero_ae (Eventually.of_forall fun x hx => ?_)
      rw [uIoc_of_le (by linarith)] at hx
      rw [Cvs.L2a.CornerSplitSqrtFloor.wBotG_eq_zero Cvs.L2a.CornerSplitSqrtFloor.isStep_S hδ0 hx.1.le]
      simp
    rw [h0, add_zero]
  have htop : ∫ x in m..M, ((Cvs.L2a.CornerSplitSqrtFloor.wTopG Cvs.Upstream.QuinticSmoothStep.S δ M x : ℝ) : ℂ) * (psi c g x : ℂ) * eF c y x
      = ∫ x in M - δ..M, ((Cvs.L2a.CornerSplitSqrtFloor.wTopG Cvs.Upstream.QuinticSmoothStep.S δ M x : ℝ) : ℂ) * (psi c g x : ℂ) * eF c y x := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hii _ htc m (M - δ)) (hii _ htc (M - δ) M)]
    have h0 : ∫ x in m..M - δ, ((Cvs.L2a.CornerSplitSqrtFloor.wTopG Cvs.Upstream.QuinticSmoothStep.S δ M x : ℝ) : ℂ) * (psi c g x : ℂ) * eF c y x = 0 := by
      refine intervalIntegral.integral_zero_ae (Eventually.of_forall fun x hx => ?_)
      rw [uIoc_of_le (by linarith)] at hx
      rw [Cvs.L2a.CornerSplitSqrtFloor.wTopG_eq_zero Cvs.L2a.CornerSplitSqrtFloor.isStep_S hδ0 hx.2]
      simp
    rw [h0, zero_add]
  -- the three Q-steps
  have h1 := ibpC_Icc (w := fun _ => (1 : ℂ)) (w₁ := fun _ => 0) (w₂ := fun _ => 0) hg hg₁ hg₂c hang hc hy hm
    (by linarith : m ≤ M) (fun x _ => hasDerivAt_const x (1 : ℂ)) (fun x _ => hasDerivAt_const x (0 : ℂ))
    continuousOn_const
  have h2 := ibpC_Icc hg hg₁ hg₂c hang hc hy hm (by linarith : m ≤ m + δ)
    (fun x _ => Cvs.L2a.CornerSplitSqrtFloor.hasDerivAt_wbC δ m x) (fun x _ => Cvs.L2a.CornerSplitSqrtFloor.hasDerivAt_wbC₁ δ m x)
    (Cvs.L2a.CornerSplitSqrtFloor.continuous_wbC₂ δ m).continuousOn (χ := χ)
  have h3 := ibpC_Icc hg hg₁ hg₂c hang hc hy (by linarith : 1 < M - δ) (by linarith : M - δ ≤ M)
    (fun x _ => Cvs.L2a.CornerSplitSqrtFloor.hasDerivAt_wtC δ M x) (fun x _ => Cvs.L2a.CornerSplitSqrtFloor.hasDerivAt_wtC₁ δ M x)
    (Cvs.L2a.CornerSplitSqrtFloor.continuous_wtC₂ δ M).continuousOn (χ := χ)
  obtain ⟨b0, b1, b2, b3⟩ := Cvs.L2a.CornerSplitSqrtFloor.wbC_cut_far hδ0.ne' m
  obtain ⟨t0, t1, t2, t3⟩ := Cvs.L2a.CornerSplitSqrtFloor.wtC_cut_far hδ0.ne' M
  rw [bBc_eq_zero b2 b3, bBc_congr (v := fun _ => (1 : ℂ)) (v₁ := fun _ => (0 : ℂ)) b0 b1] at h2
  rw [bBc_eq_zero t2 t3, bBc_congr (v := fun _ => (1 : ℂ)) (v₁ := fun _ => (0 : ℂ)) t0 t1] at h3
  have e2 : ∫ x in m..m + δ, ((Cvs.L2a.CornerSplitSqrtFloor.wBotG Cvs.Upstream.QuinticSmoothStep.S δ m x : ℝ) : ℂ) * (psi c g x : ℂ) * eF c y x
      = ∫ x in m..m + δ, Cvs.L2a.CornerSplitSqrtFloor.wbC δ m x * (psi c g x : ℂ) * eF c y x := rfl
  have e3 : ∫ x in M - δ..M, ((Cvs.L2a.CornerSplitSqrtFloor.wTopG Cvs.Upstream.QuinticSmoothStep.S δ M x : ℝ) : ℂ) * (psi c g x : ℂ) * eF c y x
      = ∫ x in M - δ..M, Cvs.L2a.CornerSplitSqrtFloor.wtC δ M x * (psi c g x : ℂ) * eF c y x := rfl
  rw [hsplit, hbot, htop, e2, e3, h1, h2, h3]
  ring

/-- **The middle cut kernel at `m`**: `Re calK(wMid 1_(m,M]Φ(m·))(t) = bulk₁_m(t) − bulkBot_m(t) − bulkTop_m(t)`
for a.e. `t > 0`. -/
theorem reCalK_mid {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 0 < c) {M m : ℕ} (hm : 2 ≤ m) (hmM : m + 1 ≤ M) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2) :
    ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
      (Cvs.Upstream.CosineTransformHalfLine.calK c (fun s => ((Cvs.L2a.CornerSplitSqrtFloor.wMidG Cvs.Upstream.QuinticSmoothStep.S δ M m (m * s)
        * (Ioc (m : ℝ) M).indicator (fun ξ => ∑ i, a i * psi c (g i) ξ) (m * s) : ℝ) : ℂ)) t).re
        = bulkOne c χ g a M m t - bulkBot c δ χ g a m t - bulkTop c δ χ g a M m t := by
  have hψc : ∀ i, Continuous (psi c (g i)) := fun i =>
    (rung_system (hg i) (hg₁ i) (hg₂c i) (hang i)).2.2.1
  have hΦc : Continuous (fun ξ => ∑ i, a i * psi c (g i) ξ) :=
    continuous_finsetSum _ fun i _ => continuous_const.mul (hψc i)
  have hmr : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hMr : (m : ℝ) + 1 ≤ M := by exact_mod_cast hmM
  have hm0 : (0 : ℝ) < m := by linarith
  have hwc := continuous_wMid δ M m
  have hwΦc : Continuous fun x => Cvs.L2a.CornerSplitSqrtFloor.wMidG Cvs.Upstream.QuinticSmoothStep.S δ M m x * ∑ i, a i * psi c (g i) x := hwc.mul hΦc
  have hfun := wMid_cut_eq (fun ξ => ∑ i, a i * psi c (g i) ξ) δ (m : ℝ) (M : ℝ)
  have hfun' : (fun s => ((Cvs.L2a.CornerSplitSqrtFloor.wMidG Cvs.Upstream.QuinticSmoothStep.S δ M m (m * s)
        * (Ioc (m : ℝ) M).indicator (fun ξ => ∑ i, a i * psi c (g i) ξ) (m * s) : ℝ) : ℂ))
      = fun s => (((Ioc (m : ℝ) M).indicator
          (fun x => Cvs.L2a.CornerSplitSqrtFloor.wMidG Cvs.Upstream.QuinticSmoothStep.S δ M m x * ∑ i, a i * psi c (g i) x) (m * s) : ℝ) : ℂ) := by
    funext s; rw [← congrFun hfun]
  rw [hfun']
  filter_upwards [ae_restrict_of_ae (calK_dil_indicator hc hm0 (by linarith : (0 : ℝ) ≤ m)
    (by linarith : (m : ℝ) ≤ M) hwΦc), ae_restrict_mem measurableSet_Ioi] with t ht ht0
  rw [ht, Complex.ofReal_re, intervalIntegral_mul_cos_eq_re hwΦc, intervalIntegral_wΦ_eF a hψc hwc]
  have hy : 0 < t / m := div_pos ht0 hm0
  have hibp : ∀ i, ∫ ξ in (m : ℝ)..M, ((Cvs.L2a.CornerSplitSqrtFloor.wMidG Cvs.Upstream.QuinticSmoothStep.S δ M m ξ : ℝ) : ℂ) * (psi c (g i) ξ : ℂ)
        * eF c (t / m) ξ
      = (∫ x in (m : ℝ)..M, eF c (t / m) x * (psi c (g i) x : ℂ)
          * rRc (fun _ => 1) (fun _ => 0) (fun _ => 0) c (χ i) (t / m) x)
        - (∫ x in (m : ℝ)..m + δ, eF c (t / m) x * (psi c (g i) x : ℂ)
          * rRc (Cvs.L2a.CornerSplitSqrtFloor.wbC δ m) (Cvs.L2a.CornerSplitSqrtFloor.wbC₁ δ m) (Cvs.L2a.CornerSplitSqrtFloor.wbC₂ δ m) c (χ i) (t / m) x)
        - ∫ x in (M : ℝ) - δ..M, eF c (t / m) x * (psi c (g i) x : ℂ)
          * rRc (Cvs.L2a.CornerSplitSqrtFloor.wtC δ M) (Cvs.L2a.CornerSplitSqrtFloor.wtC₁ δ M) (Cvs.L2a.CornerSplitSqrtFloor.wtC₂ δ M) c (χ i) (t / m) x := fun i =>
    integral_wMid_eq (hg i) (hg₁ i) (hg₂c i) (hang i) hc hy (by linarith) hδ0 (by linarith)
  simp_rw [hibp]
  unfold bulkOne bulkBot bulkTop
  simp only [mul_sub, Finset.sum_sub_distrib, Complex.sub_re]

/-- **The middle split at `m`**: `bulk₁_m ∈ L²(1, ∞)` and the `m`-th term of `Dmid` is
`∫ū·bulk₁_m − ∫ū·bulkBot_m − ∫ū·bulkTop_m`. -/
theorem dil_split_mid {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 0 < c) (hχc : ∀ i, χ i < c ^ 2) {M m : ℕ} (hm : 2 ≤ m) (hmM : m + 1 ≤ M) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1 / 2) :
    MemLp (bulkOne c χ g a M m) 2 (volume.restrict (Ioi 1))
      ∧ ∫ x in Ioi 1, (Cvs.Upstream.CosineTransformHalfLine.calK c (fun t => ((ubar (fun ξ => ∑ i, a i * psi c (g i) ξ) wF M (m * t) : ℝ) : ℂ))
          x).re * (Cvs.L2a.CornerSplitSqrtFloor.wMidG Cvs.Upstream.QuinticSmoothStep.S δ M m x * (Ioc (m : ℝ) M).indicator (fun ξ => ∑ i, a i * psi c (g i) ξ) x)
        = (∫ t in Ioi 1, ubar (fun ξ => ∑ i, a i * psi c (g i) ξ) wF M t * bulkOne c χ g a M m t)
          - (∫ t in Ioi 1, ubar (fun ξ => ∑ i, a i * psi c (g i) ξ) wF M t * bulkBot c δ χ g a m t)
          - ∫ t in Ioi 1, ubar (fun ξ => ∑ i, a i * psi c (g i) ξ) wF M t * bulkTop c δ χ g a M m t := by
  have hψc : ∀ i, Continuous (psi c (g i)) := fun i =>
    (rung_system (hg i) (hg₁ i) (hg₂c i) (hang i)).2.2.1
  have hΦc : Continuous (fun ξ => ∑ i, a i * psi c (g i) ξ) :=
    continuous_finsetSum _ fun i _ => continuous_const.mul (hψc i)
  have hΦ2 : MemLp (fun ξ => ∑ i, a i * psi c (g i) ξ) 2 (volume.restrict (Ioi 1)) :=
    memLp_finsetSum _ fun i _ =>
      (Cvs.Prolate.RungExactOrthogonality.memLp_psi (hg i) (hg₁ i) (hg₂c i) (hang i) hc).const_mul (a i)
  have hmr : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hδ1' : δ ≤ 1 := by linarith
  have hfun := wMid_cut_eq (fun ξ => ∑ i, a i * psi c (g i) ξ) δ (m : ℝ) (M : ℝ)
  have hgm : MemLp (fun x => ((Cvs.L2a.CornerSplitSqrtFloor.wMidG Cvs.Upstream.QuinticSmoothStep.S δ M m x
      * (Ioc (m : ℝ) M).indicator (fun ξ => ∑ i, a i * psi c (g i) ξ) x : ℝ) : ℂ)) 2 (volume.restrict (Ioi 0)) := by
    have hwΦc : Continuous fun x => Cvs.L2a.CornerSplitSqrtFloor.wMidG Cvs.Upstream.QuinticSmoothStep.S δ M m x * ∑ i, a i * psi c (g i) x :=
      (continuous_wMid δ M m).mul hΦc
    have h := ((memLp_indicator_Ioc hwΦc (m : ℝ) M).1.restrict (Ioi (0 : ℝ))).ofReal (K := ℂ)
    rw [← hfun] at h
    exact h
  have hgm1 : ∀ x : ℝ, x ≤ 1 →
      Cvs.L2a.CornerSplitSqrtFloor.wMidG Cvs.Upstream.QuinticSmoothStep.S δ M m x * (Ioc (m : ℝ) M).indicator (fun ξ => ∑ i, a i * psi c (g i) ξ) x = 0 :=
    fun x hx => by rw [indicator_of_notMem (fun h => by linarith [h.1]), mul_zero]
  have hB := (dil_split_bot (M := M) a hg hg₁ hg₂c hang hc hχc hm hmM hδ0 hδ1').1
  have hT := (dil_split_top (M := M) a hg hg₁ hg₂c hang hc hχc hm hmM hδ0 hδ1').1
  have hA : MemLp (fun t => -bulkBot c δ χ g a m t - bulkTop c δ χ g a M m t) 2 (volume.restrict (Ioi 1)) :=
    hB.neg.sub hT
  have hid : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
      (Cvs.Upstream.CosineTransformHalfLine.calK c (fun s => ((Cvs.L2a.CornerSplitSqrtFloor.wMidG Cvs.Upstream.QuinticSmoothStep.S δ M m (m * s)
        * (Ioc (m : ℝ) M).indicator (fun ξ => ∑ i, a i * psi c (g i) ξ) (m * s) : ℝ) : ℂ)) t).re
        = (-bulkBot c δ χ g a m t - bulkTop c δ χ g a M m t) + bulkOne c χ g a M m t := by
    filter_upwards [reCalK_mid a hg hg₁ hg₂c hang hc hm hmM hδ0 hδ1] with t ht
    rw [ht]; ring
  obtain ⟨hO, hsplit⟩ := integral_dil_split (u := ubar (fun ξ => ∑ i, a i * psi c (g i) ξ) wF M)
    (gm := fun x => Cvs.L2a.CornerSplitSqrtFloor.wMidG Cvs.Upstream.QuinticSmoothStep.S δ M m x * (Ioc (m : ℝ) M).indicator (fun ξ => ∑ i, a i * psi c (g i) ξ) x)
    (A := fun t => -bulkBot c δ χ g a m t - bulkTop c δ χ g a M m t) (B := bulkOne c χ g a M m)
    hc hm0 (memLp_ubar hΦ2 _) (fun x hx => ubar_of_le_one hx) hgm hgm1 hA hid
  refine ⟨hO, ?_⟩
  rw [hsplit]
  have hu := memLp_ubar hΦ2 (M : ℝ)
  have i1 : Integrable (fun t => ubar (fun ξ => ∑ i, a i * psi c (g i) ξ) wF M t * bulkBot c δ χ g a m t)
      (volume.restrict (Ioi 1)) := hu.integrable_mul hB
  have i2 : Integrable (fun t => ubar (fun ξ => ∑ i, a i * psi c (g i) ξ) wF M t * bulkTop c δ χ g a M m t)
      (volume.restrict (Ioi 1)) := hu.integrable_mul hT
  have e : (fun t => ubar (fun ξ => ∑ i, a i * psi c (g i) ξ) wF M t
        * (-bulkBot c δ χ g a m t - bulkTop c δ χ g a M m t))
      = fun t => -(ubar (fun ξ => ∑ i, a i * psi c (g i) ξ) wF M t * bulkBot c δ χ g a m t)
        - ubar (fun ξ => ∑ i, a i * psi c (g i) ξ) wF M t * bulkTop c δ χ g a M m t := by
    funext t; ring
  rw [e, integral_sub (f := fun t => -(ubar (fun ξ => ∑ i, a i * psi c (g i) ξ) wF M t * bulkBot c δ χ g a m t))
    i1.neg i2, integral_neg]
  ring

/-! ### `Dmid` and the sum of the three parts -/

/-- **`Dmid = D₁ − Γ_bot − R_top`**: the window bulks of `Dmid` are those of the two corners. -/
theorem Dmid_eq {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 0 < c) (hχc : ∀ i, χ i < c ^ 2) {M : ℕ} (hM : 3 ≤ M) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2) :
    Cvs.L2a.CornerSplitSqrtFloor.DmidG Cvs.Upstream.QuinticSmoothStep.S c (fun ξ => ∑ i, a i * psi c (g i) ξ) wF M δ
      = DOne c χ g a M - GammaBot c δ χ g a M - Rtop c δ χ g a M := by
  unfold Cvs.L2a.CornerSplitSqrtFloor.DmidG Cvs.L2a.DilationCornerSplit.dilPart DOne GammaBot Rtop
  rw [Nat.floor_natCast]
  have hsplitI : Finset.Icc 2 M = Finset.Icc 2 (M - 1 + 1) := by rw [Nat.sub_add_cancel (by omega)]
  have hMM : ((M - 1 + 1 : ℕ) : ℝ) = M := by rw [Nat.sub_add_cancel (by omega)]
  rw [hsplitI, Finset.sum_Icc_succ_top (by omega), hMM]
  simp only [Set.Ioc_self, Set.indicator_empty, mul_zero, integral_zero, add_zero]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun m hm => ?_
  obtain ⟨hm2, hmM⟩ := Finset.mem_Icc.1 hm
  rw [(dil_split_mid a hg hg₁ hg₂c hang hc hχc hm2 (by omega) hδ0 hδ1).2]
  ring

/-- **The three parts sum to the weight-one Q-step**: `Dbot + Dmid + Dtop = −2Σ_m∫ū𝔅_m + Σ_m C_m + 𝒞_a + D₁`;
`Γ_bot` and `R_top` cancel. -/
theorem corners_add_mid_eq {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 0 < c) (hχc : ∀ i, χ i < c ^ 2) {M : ℕ} (hM : 3 ≤ M) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2) :
    Cvs.L2a.CornerSplitSqrtFloor.DbotG Cvs.Upstream.QuinticSmoothStep.S c (fun ξ => ∑ i, a i * psi c (g i) ξ) wF M δ
        + Cvs.L2a.CornerSplitSqrtFloor.DmidG Cvs.Upstream.QuinticSmoothStep.S c (fun ξ => ∑ i, a i * psi c (g i) ξ) wF M δ
        + Cvs.L2a.CornerSplitSqrtFloor.DtopG Cvs.Upstream.QuinticSmoothStep.S c (fun ξ => ∑ i, a i * psi c (g i) ξ) wF M δ
      = -2 * ∑ m ∈ Finset.Icc 2 (M - 1),
          (∫ t in Ioi 1, ubar (fun ξ => ∑ i, a i * psi c (g i) ξ) wF M t * frakB c χ g a m t)
        + ∑ m ∈ Finset.Icc 2 (M - 1), cTop c χ g a M m + calCa c χ g a M + DOne c χ g a M := by
  have hδ1' : δ ≤ 1 := by linarith
  rw [Dbot_eq_kernel a hg hg₁ hg₂c hang hc hχc hM hδ0 hδ1', Dmid_eq a hg hg₁ hg₂c hang hc hχc hM hδ0 hδ1,
    Dtop_eq_kernel a hg hg₁ hg₂c hang hc hχc hM hδ0 hδ1']
  ring

/-- The near (`t ∈ (1, 2)`) and far (`t > M`) parts of the weight-one bulk at `m`. -/
def DOneNear (c : ℝ) (χ : ι → ℝ) (g : ι → ℝ → ℝ) (a : ι → ℝ) (M m : ℕ) : ℝ :=
  -2 * ∫ t in Ioo 1 2, (1 - wF t) * (∑ i, a i * psi c (g i) t) * bulkOne c χ g a M m t

/-- The far part of the weight-one bulk at `m`. -/
def DOneFar (c : ℝ) (χ : ι → ℝ) (g : ι → ℝ → ℝ) (a : ι → ℝ) (M m : ℕ) : ℝ :=
  -2 * ∫ t in Ioi (M : ℝ), (∑ i, a i * psi c (g i) t) * bulkOne c χ g a M m t

/-- `D₁ = Σ_m (near_m + far_m)`. -/
theorem DOne_eq_sum {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 0 < c) (hχc : ∀ i, χ i < c ^ 2) {M : ℕ} (hM : 3 ≤ M) :
    DOne c χ g a M = ∑ m ∈ Finset.Icc 2 (M - 1), (DOneNear c χ g a M m + DOneFar c χ g a M m) := by
  have hΦ2 : MemLp (fun ξ => ∑ i, a i * psi c (g i) ξ) 2 (volume.restrict (Ioi 1)) :=
    memLp_finsetSum _ fun i _ =>
      (Cvs.Prolate.RungExactOrthogonality.memLp_psi (hg i) (hg₁ i) (hg₂c i) (hang i) hc).const_mul (a i)
  have hM2 : (2 : ℝ) ≤ M := by exact_mod_cast (show 2 ≤ M by omega)
  unfold DOne DOneNear DOneFar
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  obtain ⟨hm2, hmM⟩ := Finset.mem_Icc.1 hm
  rw [integral_ubar_mul hΦ2 (dil_split_mid (M := M) (δ := 1 / 2) a hg hg₁ hg₂c hang hc hχc hm2 (by omega)
    (by norm_num) le_rfl).1 hM2]
  ring

/-! ### Atom profiles of the weight one -/

/-- The far constant of `A₂`: `K₂ = 16/3 + (364/45)/c + (64/45)/c²`. -/
def K2far (c : ℝ) : ℝ := 16 / 3 + 364 / 45 / c + 64 / 45 / c ^ 2

/-- The far constant of `A₃`: `K₃ = 128/9 + (256/75)/c²`. -/
def K3far (c : ℝ) : ℝ := 128 / 9 + 256 / 75 / c ^ 2

/-- The near constant of `A₂` (`m ≥ 3`): `27/5 + (2619/400)/c + (243/200)/c²`. -/
def K2near (c : ℝ) : ℝ := 27 / 5 + 2619 / 400 / c + 243 / 200 / c ^ 2

/-- The near constant of `A₃` (`m ≥ 3`): `243/20 + (243/125)/c²`. -/
def K3near (c : ℝ) : ℝ := 243 / 20 + 243 / 125 / c ^ 2

/-- The first atom of the weight one vanishes. -/
theorem pr₁_one (c χ₀ y x : ℝ) : Cvs.L2a.SigmaSquareMultiplier.pr₁ (fun _ => (0 : ℂ)) (fun _ => 0) c χ₀ y x = 0 := by
  simp [Cvs.L2a.SigmaSquareMultiplier.pr₁, aC₁]

/-- **Far profile of `A₂`**: for `x ≥ 2`, `y > 1`, `(x² − 1)(y² − 1) ≥ 15/4` and `y/((x² − 1)(y² − 1)) ≤ 4/(5x)`,
`|A₂|/|Q_{c²}|² ≤ (K₂/c)(1/x)(y/(y² − 1))`. -/
theorem pr₂_one_far {c y x : ℝ} (hc : 0 < c) (hx : 2 ≤ x) (hy : 1 < y)
    (hG : 15 / 4 ≤ (x ^ 2 - 1) * (y ^ 2 - 1)) (hW : y / ((x ^ 2 - 1) * (y ^ 2 - 1)) ≤ 4 / (5 * x)) :
    Cvs.L2a.SigmaSquareMultiplier.pr₂ (fun _ => (1 : ℂ)) (fun _ => 0) c (c ^ 2) y x ≤ K2far c / c * (1 / x) * (y / (y ^ 2 - 1)) := by
  set p := x ^ 2 - 1 with hpdef
  set q := y ^ 2 - 1 with hqdef
  have hp : 3 ≤ p := by nlinarith
  have hq : 0 < q := by nlinarith
  have hx0 : 0 < x := by linarith
  have hD : 0 < c ^ 2 * (p * q) := by positivity
  have hQ : c ^ 2 * (p * q) ≤ ‖qQ c (c ^ 2) y x‖ := by
    have := Cvs.L2a.QIdentityComplexWeight.norm_qQ_ge_re c (c ^ 2) y x
    rw [sub_self, sub_zero, abs_of_pos (by positivity)] at this
    linarith [show c ^ 2 * (x ^ 2 - 1) * (y ^ 2 - 1) = c ^ 2 * (p * q) by ring]
  have hQ1 : ‖qQ₁ c y x‖ ≤ 2 * c ^ 2 * x * q + 2 * c * y := Cvs.L2a.QIdentityIterated.norm_qQ₁_le_far hx0.le hy.le hc.le
  have hQ2 : ‖qQ₂ c y‖ = 2 * c ^ 2 * q := Cvs.L2a.QIdentityComplexWeight.norm_qQ₂_eq hy.le
  have hA2 := Cvs.L2a.QIdentityComplexWeight.norm_aC₂_le (w := fun _ => (1 : ℂ)) (w₁ := fun _ => 0) hc.le (by linarith : (0 : ℝ) ≤ y)
    (by linarith : (1 : ℝ) ≤ x)
  simp only [norm_one, mul_one, norm_zero, mul_zero, add_zero] at hA2
  unfold Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval.pP at hA2
  rw [hQ2, ← hpdef] at hA2
  have hcy0 : 0 ≤ c * y := by positivity
  have hk : 0 ≤ 2 * x + 2 * (c * y) * p := by positivity
  set S := (2 * x + 2 * (c * y) * p) * (2 * c ^ 2 * x * q + 2 * c * y) + p * (2 * c ^ 2 * q) with hS
  have hA2' : ‖aC₂ (fun _ => (1 : ℂ)) (fun _ => 0) c y x‖ ≤ S :=
    hA2.trans (by rw [hS]; gcongr)
  have hpr : Cvs.L2a.SigmaSquareMultiplier.pr₂ (fun _ => (1 : ℂ)) (fun _ => 0) c (c ^ 2) y x ≤ S / (c ^ 2 * (p * q)) ^ 2 := by
    unfold Cvs.L2a.SigmaSquareMultiplier.pr₂
    exact div_le_div₀ (by positivity) hA2' (by positivity) (pow_le_pow_left₀ hD.le hQ 2)
  refine hpr.trans ?_
  -- the five terms
  have hW' : 4 * x * y ≤ 16 / 5 * (p * q) := by
    have := (div_le_div_iff₀ (by positivity) (by positivity)).1 hW
    nlinarith
  have hp34 : 3 / 4 * x ^ 2 ≤ p := by rw [hpdef]; nlinarith
  have t1 : x ^ 2 ≤ 4 / 3 * p := by linarith
  have t2 : x ^ 3 ≤ 8 / 9 * p ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) hp34 2
    nlinarith
  have t4 : 2 * x ≤ 4 / 3 * p := by rw [hpdef]; nlinarith
  have t5 : x ^ 2 ≤ 16 / 45 * (p * (p * q)) := by
    have := mul_le_mul_of_nonneg_left hG (show 0 ≤ 16 / 45 * p by positivity)
    nlinarith
  have hcy : 0 ≤ c * y := by positivity
  rw [div_le_iff₀ (by positivity)]
  have e : K2far c / c * (1 / x) * (y / q) * (c ^ 2 * (p * q)) ^ 2
      = (16 / 3 * c ^ 3 + 364 / 45 * c ^ 2 + 64 / 45 * c) * y * p ^ 2 * q / x := by
    unfold K2far; field_simp
  rw [e, le_div_iff₀ hx0, hS]
  have hy1 : 1 ≤ y := hy.le
  have hc0 := hc.le
  have hq0 := hq.le
  have hp0 : 0 ≤ p := by linarith
  have h1 : 4 * c ^ 3 * x ^ 2 * y * p * q ≤ 16 / 3 * c ^ 3 * y * p ^ 2 * q :=
    calc 4 * c ^ 3 * x ^ 2 * y * p * q = (4 * c ^ 3 * y * p * q) * x ^ 2 := by ring
      _ ≤ (4 * c ^ 3 * y * p * q) * (4 / 3 * p) := by gcongr
      _ = _ := by ring
  have h2 : 4 * c ^ 2 * x ^ 3 * q ≤ 32 / 9 * c ^ 2 * y * p ^ 2 * q :=
    calc 4 * c ^ 2 * x ^ 3 * q = (4 * c ^ 2 * q) * x ^ 3 * 1 := by ring
      _ ≤ (4 * c ^ 2 * q) * (8 / 9 * p ^ 2) * y := by gcongr
      _ = _ := by ring
  have h3 : 4 * c ^ 2 * x * y ^ 2 * p ≤ 16 / 5 * c ^ 2 * y * p ^ 2 * q :=
    calc 4 * c ^ 2 * x * y ^ 2 * p = (c ^ 2 * y * p) * (4 * x * y) := by ring
      _ ≤ (c ^ 2 * y * p) * (16 / 5 * (p * q)) := by gcongr
      _ = _ := by ring
  have h4 : 2 * c ^ 2 * x * p * q ≤ 4 / 3 * c ^ 2 * y * p ^ 2 * q :=
    calc 2 * c ^ 2 * x * p * q = (c ^ 2 * p * q) * (2 * x) * 1 := by ring
      _ ≤ (c ^ 2 * p * q) * (4 / 3 * p) * y := by gcongr
      _ = _ := by ring
  have h5 : 4 * c * x ^ 2 * y ≤ 64 / 45 * c * y * p ^ 2 * q :=
    calc 4 * c * x ^ 2 * y = (4 * c * y) * x ^ 2 := by ring
      _ ≤ (4 * c * y) * (16 / 45 * (p * (p * q))) := by gcongr
      _ = _ := by ring
  have eL : ((2 * x + 2 * (c * y) * p) * (2 * c ^ 2 * x * q + 2 * c * y) + p * (2 * c ^ 2 * q)) * x
      = 4 * c ^ 3 * x ^ 2 * y * p * q + 4 * c ^ 2 * x ^ 3 * q + 4 * c ^ 2 * x * y ^ 2 * p
        + 2 * c ^ 2 * x * p * q + 4 * c * x ^ 2 * y := by ring
  have eR : (16 / 3 * c ^ 3 + 364 / 45 * c ^ 2 + 64 / 45 * c) * y * p ^ 2 * q
      = 16 / 3 * c ^ 3 * y * p ^ 2 * q + 32 / 9 * c ^ 2 * y * p ^ 2 * q + 16 / 5 * c ^ 2 * y * p ^ 2 * q
        + 4 / 3 * c ^ 2 * y * p ^ 2 * q + 64 / 45 * c * y * p ^ 2 * q := by ring
  rw [eL, eR]
  linarith

/-- **Far profile of `A₃`**: under the same hypotheses, `|A₃|/|Q_{c²}|³ ≤ (K₃/c²)(1/x)(y/(y² − 1))`. -/
theorem pr₃_one_far {c y x : ℝ} (hc : 0 < c) (hx : 2 ≤ x) (hy : 1 < y)
    (hG : 15 / 4 ≤ (x ^ 2 - 1) * (y ^ 2 - 1)) (hW : y / ((x ^ 2 - 1) * (y ^ 2 - 1)) ≤ 4 / (5 * x)) :
    Cvs.L2a.SigmaSquareMultiplier.pr₃ (fun _ => (1 : ℂ)) c (c ^ 2) y x ≤ K3far c / c ^ 2 * (1 / x) * (y / (y ^ 2 - 1)) := by
  set p := x ^ 2 - 1 with hpdef
  set q := y ^ 2 - 1 with hqdef
  have hp : 3 ≤ p := by nlinarith
  have hq : 0 < q := by nlinarith
  have hx0 : 0 < x := by linarith
  have hD : 0 < c ^ 2 * (p * q) := by positivity
  have hQ : c ^ 2 * (p * q) ≤ ‖qQ c (c ^ 2) y x‖ := by
    have := Cvs.L2a.QIdentityComplexWeight.norm_qQ_ge_re c (c ^ 2) y x
    rw [sub_self, sub_zero, abs_of_pos (by positivity)] at this
    linarith [show c ^ 2 * (x ^ 2 - 1) * (y ^ 2 - 1) = c ^ 2 * (p * q) by ring]
  have hQ1 : ‖qQ₁ c y x‖ ≤ 2 * c ^ 2 * x * q + 2 * c * y := Cvs.L2a.QIdentityIterated.norm_qQ₁_le_far hx0.le hy.le hc.le
  have hA3 := Cvs.L2a.QIdentityComplexWeight.norm_aC₃_eq (w := fun _ => (1 : ℂ)) (c := c) (y := y) (by linarith : (1 : ℝ) ≤ x)
  simp only [norm_one, mul_one] at hA3
  unfold Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval.pP at hA3
  rw [← hpdef] at hA3
  set S := 2 * p * (8 * c ^ 4 * x ^ 2 * q ^ 2 + 8 * c ^ 2 * y ^ 2) with hS
  have hA3' : ‖aC₃ (fun _ => (1 : ℂ)) c y x‖ ≤ S := by
    rw [hA3, hS]
    have h0 : 0 ≤ ‖qQ₁ c y x‖ := norm_nonneg _
    have hsq : ‖qQ₁ c y x‖ ^ 2 ≤ 8 * c ^ 4 * x ^ 2 * q ^ 2 + 8 * c ^ 2 * y ^ 2 := by
      have := pow_le_pow_left₀ h0 hQ1 2
      nlinarith [sq_nonneg (2 * c ^ 2 * x * q - 2 * c * y)]
    have : 0 ≤ 2 * p := by positivity
    nlinarith
  have hpr : Cvs.L2a.SigmaSquareMultiplier.pr₃ (fun _ => (1 : ℂ)) c (c ^ 2) y x ≤ S / (c ^ 2 * (p * q)) ^ 3 := by
    unfold Cvs.L2a.SigmaSquareMultiplier.pr₃
    exact div_le_div₀ (by positivity) hA3' (by positivity) (pow_le_pow_left₀ hD.le hQ 3)
  refine hpr.trans ?_
  have hW' : 4 * x * y ≤ 16 / 5 * (p * q) := by
    have := (div_le_div_iff₀ (by positivity) (by positivity)).1 hW
    nlinarith
  have hp34 : 3 / 4 * x ^ 2 ≤ p := by rw [hpdef]; nlinarith
  have t2 : x ^ 3 ≤ 8 / 9 * p ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) hp34 2
    nlinarith
  rw [div_le_iff₀ (by positivity)]
  have e : K3far c / c ^ 2 * (1 / x) * (y / q) * (c ^ 2 * (p * q)) ^ 3
      = (128 / 9 * c ^ 4 + 256 / 75 * c ^ 2) * y * p ^ 3 * q ^ 2 / x := by
    unfold K3far; field_simp
  rw [e, le_div_iff₀ hx0, hS]
  have hy1 : 1 ≤ y := hy.le
  have hc0 := hc.le
  have hq0 := hq.le
  have hp0 : 0 ≤ p := by linarith
  have h1 : 16 * c ^ 4 * p * x ^ 3 * q ^ 2 ≤ 128 / 9 * c ^ 4 * y * p ^ 3 * q ^ 2 :=
    calc 16 * c ^ 4 * p * x ^ 3 * q ^ 2 = (16 * c ^ 4 * p * q ^ 2) * x ^ 3 * 1 := by ring
      _ ≤ (16 * c ^ 4 * p * q ^ 2) * (8 / 9 * p ^ 2) * y := by gcongr
      _ = _ := by ring
  have hpq : 15 / 4 ≤ p * q := hG
  have k1 : 16 * x * y ≤ 64 / 5 * (p * q) := by linarith
  have k2 : 64 / 5 * (p * q) ≤ 256 / 75 * (p * q) ^ 2 := by nlinarith
  have h2 : 16 * c ^ 2 * p * x * y ^ 2 ≤ 256 / 75 * c ^ 2 * y * p ^ 3 * q ^ 2 :=
    calc 16 * c ^ 2 * p * x * y ^ 2 = (c ^ 2 * p * y) * (16 * x * y) := by ring
      _ ≤ (c ^ 2 * p * y) * (256 / 75 * (p * q) ^ 2) :=
          mul_le_mul_of_nonneg_left (k1.trans k2) (by positivity)
      _ = _ := by ring
  have eL : 2 * p * (8 * c ^ 4 * x ^ 2 * q ^ 2 + 8 * c ^ 2 * y ^ 2) * x
      = 16 * c ^ 4 * p * x ^ 3 * q ^ 2 + 16 * c ^ 2 * p * x * y ^ 2 := by ring
  have eR : (128 / 9 * c ^ 4 + 256 / 75 * c ^ 2) * y * p ^ 3 * q ^ 2
      = 128 / 9 * c ^ 4 * y * p ^ 3 * q ^ 2 + 256 / 75 * c ^ 2 * y * p ^ 3 * q ^ 2 := by ring
  rw [eL, eR]
  linarith

/-- Powers for `x ≥ 3`. -/
theorem three_le_pow_facts {x : ℝ} (hx : 3 ≤ x) :
    3 * x ≤ x ^ 2 ∧ 9 * x ^ 2 ≤ x ^ 4 ∧ 3 * x ^ 3 ≤ x ^ 4 ∧ 27 * x ≤ x ^ 4 := by
  have h0 : 0 ≤ x := by linarith
  have a : 3 * x ≤ x ^ 2 := by nlinarith
  have b : 9 ≤ x ^ 2 := by nlinarith
  have c : 9 * x ^ 2 ≤ x ^ 4 := by nlinarith
  have d : 3 * x ^ 3 ≤ x ^ 4 := by
    have := mul_le_mul_of_nonneg_left hx (pow_nonneg h0 3)
    nlinarith
  refine ⟨a, c, d, ?_⟩
  nlinarith

/-- **Near profile of `A₂`** (`χ₀ = 0`): for `x ≥ 3`, `0 ≤ y ≤ 2/3`, `|A₂|/|Q₀|² ≤ (K₂ⁿ/c)(1/x)`. -/
theorem pr₂_one_near {c y x : ℝ} (hc : 0 < c) (hx : 3 ≤ x) (hy0 : 0 ≤ y) (hy : y ≤ 2 / 3) :
    Cvs.L2a.SigmaSquareMultiplier.pr₂ (fun _ => (1 : ℂ)) (fun _ => 0) c 0 y x ≤ K2near c / c * (1 / x) := by
  set p := x ^ 2 - 1 with hpdef
  set r := 1 - y ^ 2 with hrdef
  have hp89 : 8 / 9 * x ^ 2 ≤ p := by rw [hpdef]; nlinarith
  have hp0 : 0 < p := by nlinarith
  have hr : 5 / 9 ≤ r := by rw [hrdef]; nlinarith
  have hr0 : 0 < r := by linarith
  have hx0 : 0 < x := by linarith
  have hD : 0 < c ^ 2 * (p * r) := by positivity
  have hQ : c ^ 2 * (p * r) ≤ ‖qQ c 0 y x‖ := by
    have := Cvs.L2a.QIdentityComplexWeight.norm_qQ_ge_re c 0 y x
    have e : c ^ 2 * (x ^ 2 - 1) * (y ^ 2 - 1) - (c ^ 2 - 0) = -(c ^ 2 * (p * r) + c ^ 2) := by
      rw [hpdef, hrdef]; ring
    rw [e, abs_neg, abs_of_pos (by positivity)] at this
    nlinarith
  have hQ1 : ‖qQ₁ c y x‖ ≤ 2 * c ^ 2 * x * r + 2 * c * y :=
    Cvs.L2a.QIdentityIterated.norm_qQ₁_le_near hx0.le hy0 (by linarith) hc.le
  have hQ2 : ‖qQ₂ c y‖ = 2 * c ^ 2 * r := Cvs.L2a.QIdentityIterated.norm_qQ₂_eq_near (by rw [abs_of_nonneg hy0]; linarith)
  have hA2 := Cvs.L2a.QIdentityComplexWeight.norm_aC₂_le (w := fun _ => (1 : ℂ)) (w₁ := fun _ => 0) hc.le hy0 (by linarith : (1 : ℝ) ≤ x)
  simp only [norm_one, mul_one, norm_zero, mul_zero, add_zero] at hA2
  unfold Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval.pP at hA2
  rw [hQ2, ← hpdef] at hA2
  have hcy0 : 0 ≤ c * y := by positivity
  have hk : 0 ≤ 2 * x + 2 * (c * y) * p := by positivity
  set S := (2 * x + 2 * (c * y) * p) * (2 * c ^ 2 * x * r + 2 * c * y) + p * (2 * c ^ 2 * r) with hS
  have hA2' : ‖aC₂ (fun _ => (1 : ℂ)) (fun _ => 0) c y x‖ ≤ S :=
    hA2.trans (by rw [hS]; gcongr)
  have hpr : Cvs.L2a.SigmaSquareMultiplier.pr₂ (fun _ => (1 : ℂ)) (fun _ => 0) c 0 y x ≤ S / (c ^ 2 * (p * r)) ^ 2 := by
    unfold Cvs.L2a.SigmaSquareMultiplier.pr₂
    exact div_le_div₀ (by positivity) hA2' (by positivity) (pow_le_pow_left₀ hD.le hQ 2)
  refine hpr.trans ?_
  rw [div_le_iff₀ (by positivity)]
  have e : K2near c / c * (1 / x) * (c ^ 2 * (p * r)) ^ 2
      = (27 / 5 * c ^ 3 + 2619 / 400 * c ^ 2 + 243 / 200 * c) * p ^ 2 * r ^ 2 / x := by
    unfold K2near; field_simp
  rw [e, le_div_iff₀ hx0, hS]
  have hc0 := hc.le
  have hx2 : x ^ 2 ≤ 9 / 8 * p := by linarith
  have hpr2 : 64 / 81 * x ^ 4 ≤ p ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) hp89 2
    nlinarith
  have hr2 : 25 / 81 ≤ r ^ 2 := by
    have := pow_le_pow_left₀ (by norm_num) hr 2
    linarith
  have hy2 : y ^ 2 ≤ 4 / 9 := by
    have := pow_le_pow_left₀ hy0 hy 2
    linarith
  obtain ⟨f1, f2, f3, f4⟩ := three_le_pow_facts hx
  have h1 : 4 * c ^ 3 * x ^ 2 * y * p * r ≤ 27 / 5 * c ^ 3 * p ^ 2 * r ^ 2 := by
    have k : x ^ 2 * y ≤ 9 / 8 * p * (2 / 3) := mul_le_mul hx2 hy hy0 (by positivity)
    have k' : 3 * p ≤ 27 / 5 * p * r := by
      have := mul_le_mul_of_nonneg_left hr (show 0 ≤ 27 / 5 * p by positivity)
      linarith
    calc 4 * c ^ 3 * x ^ 2 * y * p * r = (4 * c ^ 3 * p * r) * (x ^ 2 * y) := by ring
      _ ≤ (4 * c ^ 3 * p * r) * (9 / 8 * p * (2 / 3)) := by gcongr
      _ = (c ^ 3 * r) * (3 * p) * p := by ring
      _ ≤ (c ^ 3 * r) * (27 / 5 * p * r) * p := by gcongr
      _ = _ := by ring
  have h2 : 4 * c ^ 2 * x ^ 3 * r ≤ 243 / 80 * c ^ 2 * p ^ 2 * r ^ 2 := by
    have k : 4 * x ^ 3 ≤ 243 / 80 * (64 / 81 * x ^ 4) * (5 / 9) := by linarith
    calc 4 * c ^ 2 * x ^ 3 * r = (c ^ 2 * r) * (4 * x ^ 3) := by ring
      _ ≤ (c ^ 2 * r) * (243 / 80 * (64 / 81 * x ^ 4) * (5 / 9)) := by gcongr
      _ ≤ (c ^ 2 * r) * (243 / 80 * p ^ 2 * r) := by gcongr
      _ = _ := by ring
  have h3 : 4 * c ^ 2 * x * y ^ 2 * p ≤ 54 / 25 * c ^ 2 * p ^ 2 * r ^ 2 := by
    have k : 4 * x * (4 / 9) ≤ 54 / 25 * (8 / 9 * x ^ 2) * (25 / 81) := by linarith
    calc 4 * c ^ 2 * x * y ^ 2 * p = (c ^ 2 * p) * (4 * x * y ^ 2) := by ring
      _ ≤ (c ^ 2 * p) * (4 * x * (4 / 9)) := by gcongr
      _ ≤ (c ^ 2 * p) * (54 / 25 * (8 / 9 * x ^ 2) * (25 / 81)) := by gcongr
      _ ≤ (c ^ 2 * p) * (54 / 25 * p * r ^ 2) := by gcongr
      _ = _ := by ring
  have h4 : 2 * c ^ 2 * x * p * r ≤ 27 / 20 * c ^ 2 * p ^ 2 * r ^ 2 := by
    have k : 2 * x ≤ 27 / 20 * (8 / 9 * x ^ 2) * (5 / 9) := by linarith
    calc 2 * c ^ 2 * x * p * r = (c ^ 2 * p * r) * (2 * x) := by ring
      _ ≤ (c ^ 2 * p * r) * (27 / 20 * (8 / 9 * x ^ 2) * (5 / 9)) := by gcongr
      _ ≤ (c ^ 2 * p * r) * (27 / 20 * p * r) := by gcongr
      _ = _ := by ring
  have h5 : 4 * c * x ^ 2 * y ≤ 243 / 200 * c * p ^ 2 * r ^ 2 := by
    have k : 4 * x ^ 2 * (2 / 3) ≤ 243 / 200 * (64 / 81 * x ^ 4) * (25 / 81) := by linarith
    calc 4 * c * x ^ 2 * y = c * (4 * x ^ 2 * y) := by ring
      _ ≤ c * (4 * x ^ 2 * (2 / 3)) := by gcongr
      _ ≤ c * (243 / 200 * (64 / 81 * x ^ 4) * (25 / 81)) := by gcongr
      _ ≤ c * (243 / 200 * p ^ 2 * r ^ 2) := by gcongr
      _ = _ := by ring
  have eL : ((2 * x + 2 * (c * y) * p) * (2 * c ^ 2 * x * r + 2 * c * y) + p * (2 * c ^ 2 * r)) * x
      = 4 * c ^ 3 * x ^ 2 * y * p * r + 4 * c ^ 2 * x ^ 3 * r + 4 * c ^ 2 * x * y ^ 2 * p
        + 2 * c ^ 2 * x * p * r + 4 * c * x ^ 2 * y := by ring
  have eR : (27 / 5 * c ^ 3 + 2619 / 400 * c ^ 2 + 243 / 200 * c) * p ^ 2 * r ^ 2
      = 27 / 5 * c ^ 3 * p ^ 2 * r ^ 2 + 243 / 80 * c ^ 2 * p ^ 2 * r ^ 2 + 54 / 25 * c ^ 2 * p ^ 2 * r ^ 2
        + 27 / 20 * c ^ 2 * p ^ 2 * r ^ 2 + 243 / 200 * c * p ^ 2 * r ^ 2 := by ring
  rw [eL, eR]
  linarith

/-- **Near profile of `A₃`** (`χ₀ = 0`): for `x ≥ 3`, `0 ≤ y ≤ 2/3`, `|A₃|/|Q₀|³ ≤ (K₃ⁿ/c²)(1/x)`. -/
theorem pr₃_one_near {c y x : ℝ} (hc : 0 < c) (hx : 3 ≤ x) (hy0 : 0 ≤ y) (hy : y ≤ 2 / 3) :
    Cvs.L2a.SigmaSquareMultiplier.pr₃ (fun _ => (1 : ℂ)) c 0 y x ≤ K3near c / c ^ 2 * (1 / x) := by
  set p := x ^ 2 - 1 with hpdef
  set r := 1 - y ^ 2 with hrdef
  have hp89 : 8 / 9 * x ^ 2 ≤ p := by rw [hpdef]; nlinarith
  have hp0 : 0 < p := by nlinarith
  have hr : 5 / 9 ≤ r := by rw [hrdef]; nlinarith
  have hr0 : 0 < r := by linarith
  have hx0 : 0 < x := by linarith
  have hD : 0 < c ^ 2 * (p * r) := by positivity
  have hQ : c ^ 2 * (p * r) ≤ ‖qQ c 0 y x‖ := by
    have := Cvs.L2a.QIdentityComplexWeight.norm_qQ_ge_re c 0 y x
    have e : c ^ 2 * (x ^ 2 - 1) * (y ^ 2 - 1) - (c ^ 2 - 0) = -(c ^ 2 * (p * r) + c ^ 2) := by
      rw [hpdef, hrdef]; ring
    rw [e, abs_neg, abs_of_pos (by positivity)] at this
    nlinarith
  have hQ1 : ‖qQ₁ c y x‖ ≤ 2 * c ^ 2 * x * r + 2 * c * y :=
    Cvs.L2a.QIdentityIterated.norm_qQ₁_le_near hx0.le hy0 (by linarith) hc.le
  have hA3 := Cvs.L2a.QIdentityComplexWeight.norm_aC₃_eq (w := fun _ => (1 : ℂ)) (c := c) (y := y) (by linarith : (1 : ℝ) ≤ x)
  simp only [norm_one, mul_one] at hA3
  unfold Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval.pP at hA3
  rw [← hpdef] at hA3
  set S := 2 * p * (8 * c ^ 4 * x ^ 2 * r ^ 2 + 8 * c ^ 2 * y ^ 2) with hS
  have hA3' : ‖aC₃ (fun _ => (1 : ℂ)) c y x‖ ≤ S := by
    rw [hA3, hS]
    have h0 : 0 ≤ ‖qQ₁ c y x‖ := norm_nonneg _
    have hsq : ‖qQ₁ c y x‖ ^ 2 ≤ 8 * c ^ 4 * x ^ 2 * r ^ 2 + 8 * c ^ 2 * y ^ 2 := by
      have := pow_le_pow_left₀ h0 hQ1 2
      nlinarith [sq_nonneg (2 * c ^ 2 * x * r - 2 * c * y)]
    have : 0 ≤ 2 * p := by positivity
    nlinarith
  have hpr : Cvs.L2a.SigmaSquareMultiplier.pr₃ (fun _ => (1 : ℂ)) c 0 y x ≤ S / (c ^ 2 * (p * r)) ^ 3 := by
    unfold Cvs.L2a.SigmaSquareMultiplier.pr₃
    exact div_le_div₀ (by positivity) hA3' (by positivity) (pow_le_pow_left₀ hD.le hQ 3)
  refine hpr.trans ?_
  rw [div_le_iff₀ (by positivity)]
  have e : K3near c / c ^ 2 * (1 / x) * (c ^ 2 * (p * r)) ^ 3
      = (243 / 20 * c ^ 4 + 243 / 125 * c ^ 2) * p ^ 3 * r ^ 3 / x := by
    unfold K3near; field_simp
  rw [e, le_div_iff₀ hx0, hS]
  have hc0 := hc.le
  have hpr2 : 64 / 81 * x ^ 4 ≤ p ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) hp89 2
    nlinarith
  have hr3 : 125 / 729 ≤ r ^ 3 := by
    have := pow_le_pow_left₀ (by norm_num) hr 3
    linarith
  have hy2 : y ^ 2 ≤ 4 / 9 := by
    have := pow_le_pow_left₀ hy0 hy 2
    linarith
  obtain ⟨f1, f2, f3, f4⟩ := three_le_pow_facts hx
  have h1 : 16 * c ^ 4 * p * x ^ 3 * r ^ 2 ≤ 243 / 20 * c ^ 4 * p ^ 3 * r ^ 3 := by
    have k : 16 * x ^ 3 ≤ 243 / 20 * (64 / 81 * x ^ 4) * (5 / 9) := by linarith
    calc 16 * c ^ 4 * p * x ^ 3 * r ^ 2 = (c ^ 4 * p * r ^ 2) * (16 * x ^ 3) := by ring
      _ ≤ (c ^ 4 * p * r ^ 2) * (243 / 20 * (64 / 81 * x ^ 4) * (5 / 9)) := by gcongr
      _ ≤ (c ^ 4 * p * r ^ 2) * (243 / 20 * p ^ 2 * r) := by gcongr
      _ = _ := by ring
  have h2 : 16 * c ^ 2 * p * x * y ^ 2 ≤ 243 / 125 * c ^ 2 * p ^ 3 * r ^ 3 := by
    have k : 16 * x * (4 / 9) ≤ 243 / 125 * (64 / 81 * x ^ 4) * (125 / 729) := by linarith
    calc 16 * c ^ 2 * p * x * y ^ 2 = (c ^ 2 * p) * (16 * x * y ^ 2) := by ring
      _ ≤ (c ^ 2 * p) * (16 * x * (4 / 9)) := by gcongr
      _ ≤ (c ^ 2 * p) * (243 / 125 * (64 / 81 * x ^ 4) * (125 / 729)) := by gcongr
      _ ≤ (c ^ 2 * p) * (243 / 125 * p ^ 2 * r ^ 3) := by gcongr
      _ = _ := by ring
  have eL : 2 * p * (8 * c ^ 4 * x ^ 2 * r ^ 2 + 8 * c ^ 2 * y ^ 2) * x
      = 16 * c ^ 4 * p * x ^ 3 * r ^ 2 + 16 * c ^ 2 * p * x * y ^ 2 := by ring
  have eR : (243 / 20 * c ^ 4 + 243 / 125 * c ^ 2) * p ^ 3 * r ^ 3
      = 243 / 20 * c ^ 4 * p ^ 3 * r ^ 3 + 243 / 125 * c ^ 2 * p ^ 3 * r ^ 3 := by ring
  rw [eL, eR]
  linarith

/-! ### Elementary integrals and sums -/

/-- `∫_{(m,M]} x⁻² ≤ 1/m`. -/
theorem integral_Ioc_inv_sq_le {m M : ℝ} (hm : 0 < m) (hmM : m ≤ M) :
    ∫ x in Ioc m M, 1 / x ^ 2 ≤ 1 / m := by
  rw [← intervalIntegral.integral_of_le hmM]
  have hderiv : ∀ x ∈ uIcc m M, HasDerivAt (fun x : ℝ => -x⁻¹) (1 / x ^ 2) x := by
    intro x hx
    rw [uIcc_of_le hmM] at hx
    have hx0 : x ≠ 0 := by linarith [hx.1]
    have h := (hasDerivAt_inv hx0).neg
    rw [neg_neg, ← one_div] at h
    exact h
  have hint : IntervalIntegrable (fun x : ℝ => 1 / x ^ 2) volume m M := by
    refine ContinuousOn.intervalIntegrable fun x hx => ?_
    rw [uIcc_of_le hmM] at hx
    have hx1 : 0 < x := by linarith [hx.1]
    have hx0 : x ^ 2 ≠ 0 := by positivity
    exact (continuousAt_const.div (continuousAt_id.pow 2) hx0).continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have : 0 < M := by linarith
  have : 0 ≤ M⁻¹ := by positivity
  rw [one_div]
  linarith

/-- **The far square**: `(t/(t² − m²))²` is integrable on `(M, ∞)` with integral at most `M/(M² − m²)`,
by the antiderivative `−t/(t² − m²)` of `(t² + m²)/(t² − m²)²`. -/
theorem integral_Ioi_far_sq_le {m M : ℝ} (hm : 0 < m) (hmM : m < M) :
    IntegrableOn (fun t => (t / (t ^ 2 - m ^ 2)) ^ 2) (Ioi M)
      ∧ ∫ t in Ioi M, (t / (t ^ 2 - m ^ 2)) ^ 2 ≤ M / (M ^ 2 - m ^ 2) := by
  have hpos : ∀ t, M ≤ t → 0 < t ^ 2 - m ^ 2 := fun t ht => by nlinarith
  let g' : ℝ → ℝ := fun t => (t ^ 2 + m ^ 2) / (t ^ 2 - m ^ 2) ^ 2
  have hderiv : ∀ x ∈ Ici M, HasDerivAt (fun t => -(t / (t ^ 2 - m ^ 2))) (g' x) x := by
    intro x hx
    have hne : x ^ 2 - m ^ 2 ≠ 0 := (hpos x hx).ne'
    have h := ((hasDerivAt_id x).div ((hasDerivAt_pow 2 x).sub_const (m ^ 2)) hne).neg
    have h2 : HasDerivAt (fun t => -(t / (t ^ 2 - m ^ 2)))
        (-((1 * (x ^ 2 - m ^ 2) - id x * (((2 : ℕ) : ℝ) * x ^ (2 - 1))) / (x ^ 2 - m ^ 2) ^ 2)) x :=
      h.congr_of_eventuallyEq (Eventually.of_forall fun t => rfl)
    refine h2.congr_deriv ?_
    show _ = (x ^ 2 + m ^ 2) / (x ^ 2 - m ^ 2) ^ 2
    simp only [id]
    norm_num
    field_simp
    ring
  have hlim : Tendsto (fun t => -(t / (t ^ 2 - m ^ 2))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => t⁻¹ * (1 - m ^ 2 * (t⁻¹) ^ 2)⁻¹) atTop (𝓝 (0 * (1 - m ^ 2 * 0 ^ 2)⁻¹)) :=
      tendsto_inv_atTop_zero.mul ((tendsto_const_nhds.sub
        (tendsto_const_nhds.mul (tendsto_inv_atTop_zero.pow 2))).inv₀ (by norm_num))
    rw [zero_mul] at h1
    have h2 := h1.neg
    rw [neg_zero] at h2
    refine h2.congr' ?_
    filter_upwards [eventually_gt_atTop M] with t ht
    have ht0 : t ≠ 0 := by linarith
    have hne : t ^ 2 - m ^ 2 ≠ 0 := (hpos t ht.le).ne'
    field_simp
  have g'pos : ∀ x ∈ Ioi M, 0 ≤ g' x := fun x _ => by positivity
  have hI := integrableOn_Ioi_deriv_of_nonneg' hderiv g'pos hlim
  have hE := integral_Ioi_of_hasDerivAt_of_nonneg' hderiv g'pos hlim
  have hle : ∀ t ∈ Ioi M, (t / (t ^ 2 - m ^ 2)) ^ 2 ≤ g' t := fun t ht => by
    show _ ≤ (t ^ 2 + m ^ 2) / (t ^ 2 - m ^ 2) ^ 2
    rw [div_pow]
    have : 0 < (t ^ 2 - m ^ 2) ^ 2 := by have := hpos t (le_of_lt ht); positivity
    exact div_le_div_of_nonneg_right (by nlinarith) this.le
  have hmeas : AEStronglyMeasurable (fun t => (t / (t ^ 2 - m ^ 2)) ^ 2) (volume.restrict (Ioi M)) := by
    refine (Measurable.aestronglyMeasurable ?_)
    fun_prop
  have hint : IntegrableOn (fun t => (t / (t ^ 2 - m ^ 2)) ^ 2) (Ioi M) :=
    hI.mono' hmeas ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hle t ht))
  refine ⟨hint, ?_⟩
  calc ∫ t in Ioi M, (t / (t ^ 2 - m ^ 2)) ^ 2 ≤ ∫ t in Ioi M, g' t :=
        setIntegral_mono_on hint hI measurableSet_Ioi hle
    _ = M / (M ^ 2 - m ^ 2) := by rw [hE]; ring

/-- `√(a + b) ≤ √a + √b`. -/
theorem sqrt_add_le_add {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : √(a + b) ≤ √a + √b := by
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb, mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)]

/-- `Σ_{k=1}^n 1/√k ≤ 2√n`. -/
theorem sum_inv_sqrt_le (n : ℕ) : ∑ k ∈ Finset.Icc 1 n, 1 / √(k : ℝ) ≤ 2 * √(n : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    set a := √(n : ℝ) with ha
    set b := √((n + 1 : ℕ) : ℝ) with hb
    have ha0 : 0 ≤ a := Real.sqrt_nonneg _
    have hb0 : 0 < b := Real.sqrt_pos.2 (by positivity)
    have hab : b ^ 2 = a ^ 2 + 1 := by
      rw [ha, hb, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]; push_cast; ring
    have key : 1 / b ≤ 2 * b - 2 * a := by
      rw [div_le_iff₀ hb0]; nlinarith [sq_nonneg (a - b)]
    linarith

/-- **The far sum**: `Σ_{m=2}^{M−1} √(M/(m(M² − m²))) ≤ 4`. -/
theorem sum_far_le {M : ℕ} (hM : 3 ≤ M) :
    ∑ m ∈ Finset.Icc 2 (M - 1), 1 / √(m : ℝ) * √((M : ℝ) / ((M : ℝ) ^ 2 - (m : ℝ) ^ 2)) ≤ 4 := by
  have hMr : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith
  have hterm : ∀ m ∈ Finset.Icc 2 (M - 1), 1 / √(m : ℝ) * √((M : ℝ) / ((M : ℝ) ^ 2 - (m : ℝ) ^ 2))
      ≤ 1 / √(M : ℝ) * (1 / √(m : ℝ) + 1 / √((M - m : ℕ) : ℝ)) := by
    intro m hm
    obtain ⟨hm2, hmM⟩ := Finset.mem_Icc.1 hm
    have hmr : (2 : ℝ) ≤ m := by exact_mod_cast hm2
    have hmM' : (m : ℝ) + 1 ≤ M := by exact_mod_cast (show m + 1 ≤ M by omega)
    have hcast : ((M - m : ℕ) : ℝ) = (M : ℝ) - m := by rw [Nat.cast_sub (by omega)]
    rw [hcast]
    have hm0 : (0 : ℝ) < m := by linarith
    have hd : (0 : ℝ) < M - m := by linarith
    have e1 : 1 / √(m : ℝ) * √((M : ℝ) / ((M : ℝ) ^ 2 - (m : ℝ) ^ 2))
        = √((M : ℝ) / (m * ((M : ℝ) ^ 2 - (m : ℝ) ^ 2))) := by
      rw [one_div, ← Real.sqrt_inv, ← Real.sqrt_mul (by positivity)]
      congr 1; field_simp
    have e2 : 1 / √(M : ℝ) * (1 / √(m : ℝ) + 1 / √((M : ℝ) - m))
        = √(((M : ℝ) * m)⁻¹) + √(((M : ℝ) * (M - m))⁻¹) := by
      rw [mul_add]
      congr 1
      · rw [one_div_mul_one_div, ← Real.sqrt_mul hM0.le, one_div, ← Real.sqrt_inv]
      · rw [one_div_mul_one_div, ← Real.sqrt_mul hM0.le, one_div, ← Real.sqrt_inv]
    rw [e1, e2]
    calc √((M : ℝ) / (m * ((M : ℝ) ^ 2 - (m : ℝ) ^ 2)))
        ≤ √(((M : ℝ) * m)⁻¹ + ((M : ℝ) * (M - m))⁻¹) := by
          apply Real.sqrt_le_sqrt
          have e : ((M : ℝ) * m)⁻¹ + ((M : ℝ) * (M - m))⁻¹ = 1 / (m * (M - m)) := by
            field_simp; ring
          have hMm : 0 < (M : ℝ) ^ 2 - (m : ℝ) ^ 2 := by nlinarith
          rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
      _ ≤ √(((M : ℝ) * m)⁻¹) + √(((M : ℝ) * (M - m))⁻¹) :=
          sqrt_add_le_add (by positivity) (by positivity)
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum, Finset.sum_add_distrib]
  have h1 : ∑ m ∈ Finset.Icc 2 (M - 1), 1 / √(m : ℝ) ≤ 2 * √(M : ℝ) := by
    calc ∑ m ∈ Finset.Icc 2 (M - 1), 1 / √(m : ℝ) ≤ ∑ m ∈ Finset.Icc 1 M, 1 / √(m : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg (fun m hm => by
            simp only [Finset.mem_Icc] at hm ⊢; omega) (fun _ _ _ => by positivity)
      _ ≤ 2 * √(M : ℝ) := sum_inv_sqrt_le M
  have h2 : ∑ m ∈ Finset.Icc 2 (M - 1), 1 / √((M - m : ℕ) : ℝ) ≤ 2 * √(M : ℝ) := by
    have e : ∑ m ∈ Finset.Icc 2 (M - 1), 1 / √((M - m : ℕ) : ℝ)
        = ∑ k ∈ Finset.Icc 1 (M - 2), 1 / √(k : ℝ) := by
      refine Finset.sum_nbij' (fun m => M - m) (fun k => M - k) ?_ ?_ ?_ ?_ ?_
      · intro m hm; simp only [Finset.mem_Icc] at hm ⊢; omega
      · intro k hk; simp only [Finset.mem_Icc] at hk ⊢; omega
      · intro m hm; simp only [Finset.mem_Icc] at hm; omega
      · intro k hk; simp only [Finset.mem_Icc] at hk; omega
      · intro m _; rfl
    rw [e]
    refine (sum_inv_sqrt_le (M - 2)).trans ?_
    gcongr
    exact_mod_cast Nat.sub_le M 2
  have hsM : 0 < √(M : ℝ) := Real.sqrt_pos.2 hM0
  calc 1 / √(M : ℝ) * (∑ m ∈ Finset.Icc 2 (M - 1), 1 / √(m : ℝ)
        + ∑ m ∈ Finset.Icc 2 (M - 1), 1 / √((M - m : ℕ) : ℝ))
      ≤ 1 / √(M : ℝ) * (2 * √(M : ℝ) + 2 * √(M : ℝ)) := by gcongr
    _ = 4 := by field_simp; ring

/-- **The near sum**: `Σ_{m=3}^{n} m^{−3/2} ≤ √2 − 2/√n` for `n ≥ 2`. -/
theorem sum_near_le {n : ℕ} (hn : 2 ≤ n) :
    ∑ m ∈ Finset.Icc 3 n, 1 / ((m : ℝ) * √(m : ℝ)) ≤ √2 - 2 / √(n : ℝ) := by
  induction n, hn using Nat.le_induction with
  | base =>
    have : Finset.Icc 3 2 = ∅ := by decide
    rw [this, Finset.sum_empty]
    have : √2 - 2 / √((2 : ℕ) : ℝ) = 0 := by
      push_cast
      rw [sub_eq_zero, eq_div_iff (by positivity), Real.mul_self_sqrt (by norm_num)]
    rw [this]
  | succ n hn ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    set a := √(n : ℝ) with ha
    set b := √((n + 1 : ℕ) : ℝ) with hb
    have ha0 : 0 < a := Real.sqrt_pos.2 (by exact_mod_cast (show 0 < n by omega))
    have hb0 : 0 < b := Real.sqrt_pos.2 (by positivity)
    have hab : b ^ 2 = a ^ 2 + 1 := by
      rw [ha, hb, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]; push_cast; ring
    have hba : a ≤ b := by nlinarith
    have hnb : (((n + 1 : ℕ) : ℝ)) = b ^ 2 := by rw [hb, Real.sq_sqrt (by positivity)]
    have key : 1 / (b ^ 2 * b) ≤ 2 / a - 2 / b := by
      rw [div_sub_div _ _ ha0.ne' hb0.ne', div_le_div_iff₀ (by positivity) (by positivity)]
      have hprod : (b - a) * (b + a) = 1 := by nlinarith
      nlinarith [mul_pos ha0 hb0, sq_nonneg (b - a)]
    rw [hnb]
    linarith

/-! ### Lemma PS for the weight one -/

/-- The weight-one profiles are measurable. -/
theorem measurable_pr_one (c χ₀ y : ℝ) :
    Measurable (fun x => Cvs.L2a.SigmaSquareMultiplier.pr₂ (fun _ => (1 : ℂ)) (fun _ => 0) c χ₀ y x)
      ∧ Measurable (fun x => Cvs.L2a.SigmaSquareMultiplier.pr₃ (fun _ => (1 : ℂ)) c χ₀ y x) := by
  obtain ⟨hq, hq1⟩ := continuous_qQ c χ₀ y
  have hp : Continuous fun x => ((pP x : ℝ) : ℂ) := by unfold pP; fun_prop
  have hk : Continuous fun x => kK c y x := by unfold kK; fun_prop
  have h2 : Continuous fun x => aC₂ (fun _ => (1 : ℂ)) (fun _ => 0) c y x := by unfold aC₂; fun_prop
  have h3 : Continuous fun x => aC₃ (fun _ => (1 : ℂ)) c y x := by unfold aC₃; fun_prop
  refine ⟨?_, ?_⟩
  · unfold Cvs.L2a.SigmaSquareMultiplier.pr₂; exact h2.norm.measurable.div (hq.norm.pow 2).measurable
  · unfold Cvs.L2a.SigmaSquareMultiplier.pr₃; exact h3.norm.measurable.div (hq.norm.pow 3).measurable

/-- A nonnegative `f ≤ A/x` on `(m, M]` has `‖f‖_{L²(m,M]} ≤ A/√m`, and is in `L²(m, M]`. -/
theorem sqrt_integral_sq_le {f : ℝ → ℝ} {m M A : ℝ} (hm : 0 < m) (hmM : m ≤ M) (hA : 0 ≤ A)
    (hfm : Measurable f) (hf0 : ∀ x ∈ Ioc m M, 0 ≤ f x) (hfA : ∀ x ∈ Ioc m M, f x ≤ A * (1 / x)) :
    MemLp f 2 (volume.restrict (Ioc m M)) ∧ √(∫ x in Ioc m M, f x ^ 2) ≤ A / √m := by
  have : IsFiniteMeasure (volume.restrict (Ioc m M)) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Ioc]; exact ENNReal.ofReal_lt_top⟩
  have hbd : ∀ x ∈ Ioc m M, ‖f x‖ ≤ A / m := fun x hx => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hf0 x hx)]
    refine (hfA x hx).trans ?_
    rw [mul_one_div]
    exact div_le_div_of_nonneg_left hA hm hx.1.le
  have hmem : MemLp f 2 (volume.restrict (Ioc m M)) :=
    MemLp.of_bound hfm.aestronglyMeasurable (A / m) ((ae_restrict_iff' measurableSet_Ioc).2
      (Eventually.of_forall hbd))
  refine ⟨hmem, ?_⟩
  have hi1 : IntegrableOn (fun x => f x ^ 2) (Ioc m M) :=
    (memLp_two_iff_integrable_sq hmem.aestronglyMeasurable).1 hmem
  have hcont : ContinuousOn (fun x : ℝ => A ^ 2 * (1 / x ^ 2)) (Icc m M) := fun x hx => by
    have hx0 : x ^ 2 ≠ 0 := by have : 0 < x := by linarith [hx.1]
                               positivity
    exact (continuousAt_const.mul (continuousAt_const.div (continuousAt_id.pow 2) hx0)).continuousWithinAt
  have hi2 : IntegrableOn (fun x : ℝ => A ^ 2 * (1 / x ^ 2)) (Ioc m M) :=
    (hcont.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hle : ∫ x in Ioc m M, f x ^ 2 ≤ ∫ x in Ioc m M, A ^ 2 * (1 / x ^ 2) := by
    refine setIntegral_mono_on hi1 hi2 measurableSet_Ioc fun x hx => ?_
    have := pow_le_pow_left₀ (hf0 x hx) (hfA x hx) 2
    rw [mul_pow, div_pow, one_pow] at this
    exact this
  rw [integral_const_mul] at hle
  have h2 := integral_Ioc_inv_sq_le hm hmM
  have h3 : ∫ x in Ioc m M, f x ^ 2 ≤ A ^ 2 * (1 / m) :=
    hle.trans (mul_le_mul_of_nonneg_left h2 (sq_nonneg A))
  calc √(∫ x in Ioc m M, f x ^ 2) ≤ √(A ^ 2 * (1 / m)) := Real.sqrt_le_sqrt h3
    _ = A / √m := by rw [Real.sqrt_mul (sq_nonneg A), Real.sqrt_sq hA, Real.sqrt_div' 1 hm.le, Real.sqrt_one]; ring

/-- The far constant `K_F = (15/11)²K₂/c + (15/11)³K₃/c²`. -/
def KF (c : ℝ) : ℝ := (15 / 11) ^ 2 * (K2far c / c) + (15 / 11) ^ 3 * (K3far c / c ^ 2)

/-- The near constant `K_N = (49/40)²K₂ⁿ/c + (49/40)³K₃ⁿ/c²`. -/
def KN (c : ℝ) : ℝ := (49 / 40) ^ 2 * (K2near c / c) + (49 / 40) ^ 3 * (K3near c / c ^ 2)

theorem K_nonneg {c : ℝ} (hc : 0 < c) :
    0 ≤ K2far c ∧ 0 ≤ K3far c ∧ 0 ≤ K2near c ∧ 0 ≤ K3near c ∧ 0 ≤ KF c ∧ 0 ≤ KN c := by
  unfold KF KN K2far K3far K2near K3near
  refine ⟨by positivity, by positivity, by positivity, by positivity, by positivity, by positivity⟩

/-- `y/((x² − 1)(y² − 1)) ≤ 4/(5x)` for `x ≥ m`, `y ≥ M/m`, `2 ≤ m ≤ M − 1`, `M ≥ 3`. -/
theorem far_ratio {M m x y : ℝ} (hM : 3 ≤ M) (hm : 2 ≤ m) (hmM : m + 1 ≤ M) (hx : m ≤ x) (hy : M / m ≤ y) :
    y / ((x ^ 2 - 1) * (y ^ 2 - 1)) ≤ 4 / (5 * x) := by
  have hm0 : 0 < m := by linarith
  have hy0 : 1 < M / m := by rw [lt_div_iff₀ hm0]; linarith
  set y₀ := M / m with hy₀
  have hy1 : 1 < y := by linarith
  have hq : 0 < y ^ 2 - 1 := by nlinarith
  have hq₀ : 0 < y₀ ^ 2 - 1 := by nlinarith
  have hx0 : 0 < x := by linarith
  have hp : 0 < x ^ 2 - 1 := by nlinarith
  have h1 : y / (y ^ 2 - 1) ≤ y₀ / (y₀ ^ 2 - 1) := by
    rw [div_le_div_iff₀ hq hq₀]
    nlinarith [mul_nonneg (sub_nonneg.2 hy) (show 0 ≤ y * y₀ + 1 by positivity)]
  have h2 : y₀ / (y₀ ^ 2 - 1) = M * m / (M ^ 2 - m ^ 2) := by
    rw [hy₀]
    have : M ^ 2 - m ^ 2 ≠ 0 := by nlinarith
    field_simp
  have hMm : 0 < M ^ 2 - m ^ 2 := by nlinarith
  have h3 : M / (M ^ 2 - m ^ 2) ≤ 3 / 5 := by rw [div_le_div_iff₀ hMm (by norm_num)]; nlinarith
  have h4 : 1 / (x ^ 2 - 1) ≤ 4 / (3 * x ^ 2) := by rw [div_le_div_iff₀ hp (by positivity)]; nlinarith
  calc y / ((x ^ 2 - 1) * (y ^ 2 - 1)) = 1 / (x ^ 2 - 1) * (y / (y ^ 2 - 1)) := by field_simp
    _ ≤ 4 / (3 * x ^ 2) * (M * m / (M ^ 2 - m ^ 2)) := by
        rw [← h2]; exact mul_le_mul h4 h1 (by positivity) (by positivity)
    _ = 4 / (3 * x) * (m / x) * (M / (M ^ 2 - m ^ 2)) := by field_simp
    _ ≤ 4 / (3 * x) * 1 * (3 / 5) := by
        have : m / x ≤ 1 := by rw [div_le_one hx0]; exact hx
        gcongr
    _ = 4 / (5 * x) := by field_simp

/-- **Lemma PS on the far side for the weight one** (`χ₀ = c²`, ratio `4/15`): for `y ≥ M/m`,
`|Σᵢaᵢ∫_m^M eψᵢR[1]| ≤ (K_F/√m)(y/(y² − 1))√P`. -/
theorem span_one_far {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 0 < c) (hχ : Function.Injective χ) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i ≤ c ^ 2)
    {M m : ℕ} (hM : 3 ≤ M) (hm : 2 ≤ m) (hmM : m ≤ M - 1) {y : ℝ} (hy : (M : ℝ) / m ≤ y) :
    ‖∑ i, (a i : ℂ) * ∫ x in Ioc (m : ℝ) M, eF c y x * (psi c (g i) x : ℂ)
        * rRc (fun _ => 1) (fun _ => 0) (fun _ => 0) c (χ i) y x‖
      ≤ KF c / √(m : ℝ) * (y / (y ^ 2 - 1)) * √(∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2) := by
  have hmr : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hMr : (m : ℝ) + 1 ≤ M := by exact_mod_cast (show m + 1 ≤ M by omega)
  have hM3 : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hm0 : (0 : ℝ) < m := by linarith
  have hy1 : 1 < y := by
    have : 1 < (M : ℝ) / m := by rw [lt_div_iff₀ hm0]; linarith
    linarith
  have hq : 0 < y ^ 2 - 1 := by nlinarith
  have hyq : 0 ≤ y / (y ^ 2 - 1) := by positivity
  obtain ⟨hK2, hK3, -, -, hKF, -⟩ := K_nonneg hc
  have hG : ∀ x ∈ Ioc (m : ℝ) M, 15 / 4 ≤ (x ^ 2 - 1) * (y ^ 2 - 1) := fun x hx =>
    (Cvs.L2a.OrbitGapGrowth.fifteen_fourths_le_gapM hM3).trans
      (Cvs.L2a.OrbitGapGrowth.far_gap M m hm hmM hx.1.le hy)
  have hW : ∀ x ∈ Ioc (m : ℝ) M, y / ((x ^ 2 - 1) * (y ^ 2 - 1)) ≤ 4 / (5 * x) := fun x hx =>
    far_ratio hM3 hmr hMr hx.1.le hy
  have hQ : ∀ x ∈ Ioc (m : ℝ) M, c ^ 2 ≤ 4 / 15 * ‖qQ c (c ^ 2) y x‖ := fun x hx => by
    have h := Cvs.L2a.QIdentityComplexWeight.norm_qQ_ge_re c (c ^ 2) y x
    rw [sub_self, sub_zero] at h
    have hpq := hG x hx
    have : c ^ 2 * (15 / 4) ≤ |c ^ 2 * (x ^ 2 - 1) * (y ^ 2 - 1)| := by
      rw [abs_of_nonneg (by nlinarith [sq_nonneg c]), mul_assoc]
      exact mul_le_mul_of_nonneg_left hpq (sq_nonneg c)
    nlinarith
  have hQ0 : ∀ x ∈ Ioc (m : ℝ) M, qQ c (c ^ 2) y x ≠ 0 := fun x hx =>
    Cvs.L2a.QIdentityRealWeight.qQ_ne_zero_of_pos hc (by linarith [hx.1]) (by linarith)
  obtain ⟨hm2, hm3⟩ := measurable_pr_one c (c ^ 2) y
  have hb2 : ∀ x ∈ Ioc (m : ℝ) M, Cvs.L2a.SigmaSquareMultiplier.pr₂ (fun _ => (1 : ℂ)) (fun _ => 0) c (c ^ 2) y x
      ≤ K2far c / c * (y / (y ^ 2 - 1)) * (1 / x) := fun x hx => by
    have := pr₂_one_far hc (by linarith [hx.1]) hy1 (hG x hx) (hW x hx)
    linarith [show K2far c / c * (1 / x) * (y / (y ^ 2 - 1)) = K2far c / c * (y / (y ^ 2 - 1)) * (1 / x) by ring]
  have hb3 : ∀ x ∈ Ioc (m : ℝ) M, Cvs.L2a.SigmaSquareMultiplier.pr₃ (fun _ => (1 : ℂ)) c (c ^ 2) y x
      ≤ K3far c / c ^ 2 * (y / (y ^ 2 - 1)) * (1 / x) := fun x hx => by
    have := pr₃_one_far hc (by linarith [hx.1]) hy1 (hG x hx) (hW x hx)
    linarith [show K3far c / c ^ 2 * (1 / x) * (y / (y ^ 2 - 1)) = K3far c / c ^ 2 * (y / (y ^ 2 - 1)) * (1 / x) by
      ring]
  have hmM' : (m : ℝ) ≤ M := by linarith
  obtain ⟨hL2, hN2⟩ := sqrt_integral_sq_le hm0 hmM' (by positivity) hm2
    (fun x _ => by unfold Cvs.L2a.SigmaSquareMultiplier.pr₂; positivity) hb2
  obtain ⟨hL3, hN3⟩ := sqrt_integral_sq_le hm0 hmM' (by positivity) hm3
    (fun x _ => by unfold Cvs.L2a.SigmaSquareMultiplier.pr₃; positivity) hb3
  have hp1 : (fun x => Cvs.L2a.SigmaSquareMultiplier.pr₁ (fun _ => (0 : ℂ)) (fun _ => 0) c (c ^ 2) y x) = fun _ => 0 := by
    funext x; exact pr₁_one c (c ^ 2) y x
  have h := Cvs.L2a.SigmaSquareMultiplier.span_bulk_le a hg hg₁ hg₂c hang hc hχ (W := Ioc (m : ℝ) M) measurableSet_Ioc
    (fun x hx => lt_of_lt_of_le (by linarith : (1 : ℝ) < m) hx.1.le)
    (w := fun _ => (1 : ℂ)) (w₁ := fun _ => 0) (w₂ := fun _ => 0) (y := y) (χ₀ := c ^ 2) (D := c ^ 2)
    (ρ := 4 / 15) (fun i => by rw [abs_of_nonpos (by linarith [hχc i])]; linarith [hχ0 i]) (by norm_num)
    (by norm_num) hQ hQ0 (by rw [hp1]; exact MemLp.zero) hL2 hL3 aemeasurable_const aemeasurable_const
    aemeasurable_const
  refine h.trans ?_
  simp only [pr₁_one, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, integral_zero, Real.sqrt_zero,
    zero_div, zero_add]
  have hP := Real.sqrt_nonneg (∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2)
  have hsm : 0 < √(m : ℝ) := Real.sqrt_pos.2 hm0
  have e1 : (1 : ℝ) - 4 / 15 = 11 / 15 := by norm_num
  rw [e1]
  have k2 : √(∫ x in Ioc (m : ℝ) M, Cvs.L2a.SigmaSquareMultiplier.pr₂ (fun _ => (1 : ℂ)) (fun _ => 0) c (c ^ 2) y x ^ 2) / (11 / 15) ^ 2
      ≤ (15 / 11) ^ 2 * (K2far c / c) * (y / (y ^ 2 - 1)) / √(m : ℝ) := by
    rw [div_le_iff₀ (by norm_num)]
    refine hN2.trans (le_of_eq ?_)
    field_simp
  have k3 : √(∫ x in Ioc (m : ℝ) M, Cvs.L2a.SigmaSquareMultiplier.pr₃ (fun _ => (1 : ℂ)) c (c ^ 2) y x ^ 2) / (11 / 15) ^ 3
      ≤ (15 / 11) ^ 3 * (K3far c / c ^ 2) * (y / (y ^ 2 - 1)) / √(m : ℝ) := by
    rw [div_le_iff₀ (by norm_num)]
    refine hN3.trans (le_of_eq ?_)
    field_simp
  calc (√(∫ x in Ioc (m : ℝ) M, Cvs.L2a.SigmaSquareMultiplier.pr₂ (fun _ => (1 : ℂ)) (fun _ => 0) c (c ^ 2) y x ^ 2) / (11 / 15) ^ 2
        + √(∫ x in Ioc (m : ℝ) M, Cvs.L2a.SigmaSquareMultiplier.pr₃ (fun _ => (1 : ℂ)) c (c ^ 2) y x ^ 2) / (11 / 15) ^ 3)
          * √(∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2)
      ≤ ((15 / 11) ^ 2 * (K2far c / c) * (y / (y ^ 2 - 1)) / √(m : ℝ)
          + (15 / 11) ^ 3 * (K3far c / c ^ 2) * (y / (y ^ 2 - 1)) / √(m : ℝ))
          * √(∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2) := by gcongr
    _ = KF c / √(m : ℝ) * (y / (y ^ 2 - 1)) * √(∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2) := by
        unfold KF; ring

/-- **Lemma PS on the near side for the weight one** (`χ₀ = 0`, ratio `9/49`): for `m ≥ 3`, `0 ≤ y ≤ 2/m`,
`|Σᵢaᵢ∫_m^M eψᵢR[1]| ≤ (K_N/√m)√P`. -/
theorem span_one_near {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 0 < c) (hχ : Function.Injective χ) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i ≤ c ^ 2)
    {M m : ℕ} (hm : 3 ≤ m) (hmM : m ≤ M) {y : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ 2 / m) :
    ‖∑ i, (a i : ℂ) * ∫ x in Ioc (m : ℝ) M, eF c y x * (psi c (g i) x : ℂ)
        * rRc (fun _ => 1) (fun _ => 0) (fun _ => 0) c (χ i) y x‖
      ≤ KN c / √(m : ℝ) * √(∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2) := by
  have hmr : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hmM' : (m : ℝ) ≤ M := by exact_mod_cast hmM
  have hm0 : (0 : ℝ) < m := by linarith
  have hy23 : y ≤ 2 / 3 := hy.trans (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hmr)
  obtain ⟨-, -, hK2, hK3, -, hKN⟩ := K_nonneg hc
  have hQ : ∀ x ∈ Ioc (m : ℝ) M, c ^ 2 ≤ 9 / 49 * ‖qQ c 0 y x‖ := fun x hx => by
    have h := Cvs.L2a.QIdentityComplexWeight.norm_qQ_ge_re c 0 y x
    have hng := Cvs.L2a.OrbitGapGrowth.near_gap (b := 2) (by linarith) (by linarith) hx.1.le hy0 hy
    have hnr := Cvs.L2a.QIdentityCutPoint.near_ratio hmr
    have e : c ^ 2 * (x ^ 2 - 1) * (y ^ 2 - 1) - (c ^ 2 - 0)
        = -(c ^ 2 * ((x ^ 2 - 1) * (1 - y ^ 2) + 1)) := by ring
    have hpos : 0 ≤ c ^ 2 * ((x ^ 2 - 1) * (1 - y ^ 2) + 1) :=
      mul_nonneg (sq_nonneg c) (by linarith)
    rw [e, abs_neg, abs_of_nonneg hpos] at h
    have : c ^ 2 * (49 / 9) ≤ c ^ 2 * ((x ^ 2 - 1) * (1 - y ^ 2) + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg c)
    nlinarith
  have hQ0 : ∀ x ∈ Ioc (m : ℝ) M, qQ c 0 y x ≠ 0 := fun x hx => by
    intro h0
    have := hQ x hx
    rw [h0, norm_zero, mul_zero] at this
    nlinarith
  obtain ⟨hm2, hm3⟩ := measurable_pr_one c 0 y
  have hb2 : ∀ x ∈ Ioc (m : ℝ) M, Cvs.L2a.SigmaSquareMultiplier.pr₂ (fun _ => (1 : ℂ)) (fun _ => 0) c 0 y x ≤ K2near c / c * (1 / x) :=
    fun x hx => pr₂_one_near hc (by linarith [hx.1]) hy0 hy23
  have hb3 : ∀ x ∈ Ioc (m : ℝ) M, Cvs.L2a.SigmaSquareMultiplier.pr₃ (fun _ => (1 : ℂ)) c 0 y x ≤ K3near c / c ^ 2 * (1 / x) :=
    fun x hx => pr₃_one_near hc (by linarith [hx.1]) hy0 hy23
  obtain ⟨hL2, hN2⟩ := sqrt_integral_sq_le hm0 hmM' (by positivity) hm2
    (fun x _ => by unfold Cvs.L2a.SigmaSquareMultiplier.pr₂; positivity) hb2
  obtain ⟨hL3, hN3⟩ := sqrt_integral_sq_le hm0 hmM' (by positivity) hm3
    (fun x _ => by unfold Cvs.L2a.SigmaSquareMultiplier.pr₃; positivity) hb3
  have hp1 : (fun x => Cvs.L2a.SigmaSquareMultiplier.pr₁ (fun _ => (0 : ℂ)) (fun _ => 0) c 0 y x) = fun _ => 0 := by
    funext x; exact pr₁_one c 0 y x
  have h := Cvs.L2a.SigmaSquareMultiplier.span_bulk_le a hg hg₁ hg₂c hang hc hχ (W := Ioc (m : ℝ) M) measurableSet_Ioc
    (fun x hx => lt_of_lt_of_le (by linarith : (1 : ℝ) < m) hx.1.le)
    (w := fun _ => (1 : ℂ)) (w₁ := fun _ => 0) (w₂ := fun _ => 0) (y := y) (χ₀ := 0) (D := c ^ 2)
    (ρ := 9 / 49) (fun i => by rw [sub_zero, abs_of_nonneg (hχ0 i)]; exact hχc i) (by norm_num)
    (by norm_num) hQ hQ0 (by rw [hp1]; exact MemLp.zero) hL2 hL3 aemeasurable_const aemeasurable_const
    aemeasurable_const
  refine h.trans ?_
  simp only [pr₁_one, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, integral_zero, Real.sqrt_zero,
    zero_div, zero_add]
  have hP := Real.sqrt_nonneg (∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2)
  have hsm : 0 < √(m : ℝ) := Real.sqrt_pos.2 hm0
  have e1 : (1 : ℝ) - 9 / 49 = 40 / 49 := by norm_num
  rw [e1]
  have k2 : √(∫ x in Ioc (m : ℝ) M, Cvs.L2a.SigmaSquareMultiplier.pr₂ (fun _ => (1 : ℂ)) (fun _ => 0) c 0 y x ^ 2) / (40 / 49) ^ 2
      ≤ (49 / 40) ^ 2 * (K2near c / c) / √(m : ℝ) := by
    rw [div_le_iff₀ (by norm_num)]
    refine hN2.trans (le_of_eq ?_)
    field_simp
  have k3 : √(∫ x in Ioc (m : ℝ) M, Cvs.L2a.SigmaSquareMultiplier.pr₃ (fun _ => (1 : ℂ)) c 0 y x ^ 2) / (40 / 49) ^ 3
      ≤ (49 / 40) ^ 3 * (K3near c / c ^ 2) / √(m : ℝ) := by
    rw [div_le_iff₀ (by norm_num)]
    refine hN3.trans (le_of_eq ?_)
    field_simp
  calc (√(∫ x in Ioc (m : ℝ) M, Cvs.L2a.SigmaSquareMultiplier.pr₂ (fun _ => (1 : ℂ)) (fun _ => 0) c 0 y x ^ 2) / (40 / 49) ^ 2
        + √(∫ x in Ioc (m : ℝ) M, Cvs.L2a.SigmaSquareMultiplier.pr₃ (fun _ => (1 : ℂ)) c 0 y x ^ 2) / (40 / 49) ^ 3)
          * √(∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2)
      ≤ ((49 / 40) ^ 2 * (K2near c / c) / √(m : ℝ) + (49 / 40) ^ 3 * (K3near c / c ^ 2) / √(m : ℝ))
          * √(∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2) := by gcongr
    _ = KN c / √(m : ℝ) * √(∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2) := by unfold KN; ring

/-! ### The weight-one bulk, pointwise -/

/-- **Far pointwise bound**: for `t ≥ M`, `|bulk₁_m(t)| ≤ κ(K_F/√m)(t/(t² − m²))√P`. -/
theorem abs_bulkOne_far_le {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 0 < c) (hχ : Function.Injective χ) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i ≤ c ^ 2)
    {M m : ℕ} (hM : 3 ≤ M) (hm : 2 ≤ m) (hmM : m ≤ M - 1) {t : ℝ} (ht : (M : ℝ) ≤ t) :
    |bulkOne c χ g a M m t|
      ≤ √(2 * c / π) * KF c / √(m : ℝ) * (t / (t ^ 2 - (m : ℝ) ^ 2))
        * √(∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2) := by
  have hmr : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hMr : (m : ℝ) + 1 ≤ M := by exact_mod_cast (show m + 1 ≤ M by omega)
  have hm0 : (0 : ℝ) < m := by linarith
  have hy : (M : ℝ) / m ≤ t / m := div_le_div_of_nonneg_right ht hm0.le
  have h := span_one_far a hg hg₁ hg₂c hang hc hχ hχ0 hχc hM hm hmM hy
  unfold bulkOne
  simp_rw [intervalIntegral.integral_of_le (by linarith : (m : ℝ) ≤ M)]
  rw [abs_mul, abs_of_nonneg (by positivity)]
  refine (mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans h) (by positivity)).trans (le_of_eq ?_)
  have ht0 : 0 < t ^ 2 - (m : ℝ) ^ 2 := by nlinarith
  have hy2 : (t / m) ^ 2 - 1 = (t ^ 2 - (m : ℝ) ^ 2) / (m : ℝ) ^ 2 := by field_simp
  rw [hy2]
  field_simp

/-- **Near pointwise bound** (`m ≥ 3`): for `t ∈ (1, 2)`, `|bulk₁_m(t)| ≤ κK_N/(m√m)·√P`. -/
theorem abs_bulkOne_near_le {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 0 < c) (hχ : Function.Injective χ) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i ≤ c ^ 2)
    {M m : ℕ} (hm : 3 ≤ m) (hmM : m ≤ M) {t : ℝ} (ht : t ∈ Ioo 1 2) :
    |bulkOne c χ g a M m t|
      ≤ √(2 * c / π) * KN c / ((m : ℝ) * √(m : ℝ)) * √(∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2) := by
  have hmr : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hmM' : (m : ℝ) ≤ M := by exact_mod_cast hmM
  have hm0 : (0 : ℝ) < m := by linarith
  have h := span_one_near a hg hg₁ hg₂c hang hc hχ hχ0 hχc hm hmM (y := t / m)
    (div_nonneg (by linarith [ht.1]) hm0.le) (div_le_div_of_nonneg_right ht.2.le hm0.le)
  unfold bulkOne
  simp_rw [intervalIntegral.integral_of_le hmM']
  rw [abs_mul, abs_of_nonneg (by positivity)]
  refine (mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans h) (by positivity)).trans (le_of_eq ?_)
  field_simp

/-! ### The `t`-integrals and the sums over `m` -/

/-- **The far part at `m`**: `|far_m| ≤ 2κ(K_F/√m)√(M/(M² − m²))·P`. -/
theorem abs_DOneFar_le {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 0 < c) (hχ : Function.Injective χ) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2)
    {M m : ℕ} (hM : 3 ≤ M) (hm : 2 ≤ m) (hmM : m ≤ M - 1) :
    |DOneFar c χ g a M m|
      ≤ 2 * √(2 * c / π) * KF c * (1 / √(m : ℝ) * √((M : ℝ) / ((M : ℝ) ^ 2 - (m : ℝ) ^ 2)))
        * ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2 := by
  set Φ : ℝ → ℝ := fun ξ => ∑ i, a i * psi c (g i) ξ with hΦdef
  set P := ∫ x in Ioi 1, Φ x ^ 2 with hPdef
  have hmr : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hMr : (m : ℝ) + 1 ≤ M := by exact_mod_cast (show m + 1 ≤ M by omega)
  have hm0 : (0 : ℝ) < m := by linarith
  have hM1 : (1 : ℝ) ≤ M := by linarith
  have hΦ2 : MemLp Φ 2 (volume.restrict (Ioi 1)) :=
    memLp_finsetSum _ fun i _ =>
      (Cvs.Prolate.RungExactOrthogonality.memLp_psi (hg i) (hg₁ i) (hg₂c i) (hang i) hc).const_mul (a i)
  have hsub : volume.restrict (Ioi (M : ℝ)) ≤ volume.restrict (Ioi 1) :=
    Measure.restrict_mono (Ioi_subset_Ioi hM1) le_rfl
  have hΦM := hΦ2.mono_measure hsub
  have hBM := (dil_split_mid (M := M) (δ := 1 / 2) a hg hg₁ hg₂c hang hc hχc hm (by omega) (by norm_num)
    le_rfl).1.mono_measure hsub
  obtain ⟨hfI, hfE⟩ := integral_Ioi_far_sq_le hm0 (by linarith : (m : ℝ) < M)
  set f : ℝ → ℝ := fun t => |t / (t ^ 2 - (m : ℝ) ^ 2)| with hfdef
  have hfm : AEStronglyMeasurable f (volume.restrict (Ioi (M : ℝ))) := by
    refine Measurable.aestronglyMeasurable ?_
    simp only [hfdef]; fun_prop
  have hf2 : MemLp f 2 (volume.restrict (Ioi (M : ℝ))) := by
    refine (memLp_two_iff_integrable_sq hfm).2 ?_
    refine hfI.congr (Eventually.of_forall fun t => ?_)
    simp only [hfdef, sq_abs]
  have hfsq : ∫ t in Ioi (M : ℝ), f t ^ 2 ≤ (M : ℝ) / ((M : ℝ) ^ 2 - (m : ℝ) ^ 2) := by
    simp only [hfdef, sq_abs]; exact hfE
  set C := √(2 * c / π) * KF c / √(m : ℝ) * √P with hC
  have hC0 : 0 ≤ C := by obtain ⟨-, -, -, -, h, -⟩ := K_nonneg hc; positivity
  have hpt : ∀ t ∈ Ioi (M : ℝ), |Φ t * bulkOne c χ g a M m t| ≤ C * (f t * |Φ t|) := fun t ht => by
    have hb := abs_bulkOne_far_le a hg hg₁ hg₂c hang hc hχ hχ0 (fun i => (hχc i).le) hM hm hmM
      (le_of_lt (mem_Ioi.1 ht))
    have ht0 : 0 ≤ t / (t ^ 2 - (m : ℝ) ^ 2) := by
      have : (m : ℝ) < t := by linarith [mem_Ioi.1 ht]
      have : 0 < t ^ 2 - (m : ℝ) ^ 2 := by nlinarith
      exact div_nonneg (by linarith) this.le
    rw [abs_mul, hfdef]
    simp only [abs_of_nonneg ht0]
    calc |Φ t| * |bulkOne c χ g a M m t|
        ≤ |Φ t| * (√(2 * c / π) * KF c / √(m : ℝ) * (t / (t ^ 2 - (m : ℝ) ^ 2)) * √P) :=
          mul_le_mul_of_nonneg_left hb (abs_nonneg _)
      _ = C * (t / (t ^ 2 - (m : ℝ) ^ 2) * |Φ t|) := by rw [hC]; ring
  have hint1 : Integrable (fun t => |Φ t * bulkOne c χ g a M m t|) (volume.restrict (Ioi (M : ℝ))) :=
    (hΦM.integrable_mul hBM).abs
  have hint2 : Integrable (fun t => C * (f t * |Φ t|)) (volume.restrict (Ioi (M : ℝ))) :=
    (hf2.integrable_mul hΦM.abs).const_mul C
  have hCS := Cvs.L2a.FarFarBound.integral_mul_abs_le (μ := volume.restrict (Ioi (M : ℝ))) (fun t => abs_nonneg _) hf2 hΦM
  have hPM : ∫ t in Ioi (M : ℝ), Φ t ^ 2 ≤ P :=
    setIntegral_mono_set ((memLp_two_iff_integrable_sq hΦ2.aestronglyMeasurable).1 hΦ2)
      (Eventually.of_forall fun t => sq_nonneg _) (Eventually.of_forall (Ioi_subset_Ioi hM1))
  have hP0 : 0 ≤ P := integral_nonneg fun _ => sq_nonneg _
  unfold DOneFar
  rw [abs_mul, abs_neg, abs_two]
  have key : |∫ t in Ioi (M : ℝ), Φ t * bulkOne c χ g a M m t|
      ≤ √(2 * c / π) * KF c * (1 / √(m : ℝ) * √((M : ℝ) / ((M : ℝ) ^ 2 - (m : ℝ) ^ 2))) * P := by
    calc |∫ t in Ioi (M : ℝ), Φ t * bulkOne c χ g a M m t|
        ≤ ∫ t in Ioi (M : ℝ), |Φ t * bulkOne c χ g a M m t| := abs_integral_le_integral_abs
      _ ≤ ∫ t in Ioi (M : ℝ), C * (f t * |Φ t|) :=
          setIntegral_mono_on hint1 hint2 measurableSet_Ioi hpt
      _ = C * ∫ t in Ioi (M : ℝ), f t * |Φ t| := integral_const_mul _ _
      _ ≤ C * (√(∫ t in Ioi (M : ℝ), f t ^ 2) * √(∫ t in Ioi (M : ℝ), Φ t ^ 2)) :=
          mul_le_mul_of_nonneg_left hCS hC0
      _ ≤ C * (√((M : ℝ) / ((M : ℝ) ^ 2 - (m : ℝ) ^ 2)) * √P) := by
          gcongr
      _ = √(2 * c / π) * KF c * (1 / √(m : ℝ) * √((M : ℝ) / ((M : ℝ) ^ 2 - (m : ℝ) ^ 2))) * (√P * √P) := by
          rw [hC]; ring
      _ = _ := by rw [Real.mul_self_sqrt hP0]
  linarith

/-- **The near part at `m ≥ 3`**: `|near_m| ≤ 2κK_N/(m√m)·P`. -/
theorem abs_DOneNear_le {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 0 < c) (hχ : Function.Injective χ) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2)
    {M m : ℕ} (hm : 3 ≤ m) (hmM : m ≤ M - 1) :
    |DOneNear c χ g a M m|
      ≤ 2 * √(2 * c / π) * KN c * (1 / ((m : ℝ) * √(m : ℝ))) * ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2 := by
  set Φ : ℝ → ℝ := fun ξ => ∑ i, a i * psi c (g i) ξ with hΦdef
  set P := ∫ x in Ioi 1, Φ x ^ 2 with hPdef
  have hmr : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hΦ2 : MemLp Φ 2 (volume.restrict (Ioi 1)) :=
    memLp_finsetSum _ fun i _ =>
      (Cvs.Prolate.RungExactOrthogonality.memLp_psi (hg i) (hg₁ i) (hg₂c i) (hang i) hc).const_mul (a i)
  have hsub : volume.restrict (Ioo (1 : ℝ) 2) ≤ volume.restrict (Ioi 1) :=
    Measure.restrict_mono Ioo_subset_Ioi_self le_rfl
  have hΦN := hΦ2.mono_measure hsub
  have hBN := (dil_split_mid (M := M) (δ := 1 / 2) a hg hg₁ hg₂c hang hc hχc (by omega : 2 ≤ m) (by omega)
    (by norm_num) le_rfl).1.mono_measure hsub
  have : IsFiniteMeasure (volume.restrict (Ioo (1 : ℝ) 2)) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Ioo]; exact ENNReal.ofReal_lt_top⟩
  have hw : MemLp (fun t => 1 - wF t) 2 (volume.restrict (Ioo (1 : ℝ) 2)) :=
    MemLp.of_bound (continuous_const.sub continuous_wF.1).aestronglyMeasurable 1
      (Eventually.of_forall fun t => by
        obtain ⟨h0, h1, -, -⟩ := Cvs.L2a.FarFarBound.wF_bounds t
        rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith)
  set C := √(2 * c / π) * KN c / ((m : ℝ) * √(m : ℝ)) * √P with hC
  have hC0 : 0 ≤ C := by obtain ⟨-, -, -, -, -, h⟩ := K_nonneg hc; positivity
  have hpt : ∀ t ∈ Ioo (1 : ℝ) 2, |(1 - wF t) * Φ t * bulkOne c χ g a M m t| ≤ C * (1 * |Φ t|) := fun t ht => by
    have hb := abs_bulkOne_near_le a hg hg₁ hg₂c hang hc hχ hχ0 (fun i => (hχc i).le) hm (by omega : m ≤ M) ht
    obtain ⟨h0, h1, -, -⟩ := Cvs.L2a.FarFarBound.wF_bounds t
    rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1 - wF t)]
    calc (1 - wF t) * |Φ t| * |bulkOne c χ g a M m t| ≤ 1 * |Φ t| * |bulkOne c χ g a M m t| := by
          gcongr; linarith
      _ ≤ 1 * |Φ t| * (√(2 * c / π) * KN c / ((m : ℝ) * √(m : ℝ)) * √P) := by gcongr
      _ = C * (1 * |Φ t|) := by rw [hC]; ring
  have hint1 : Integrable (fun t => |(1 - wF t) * Φ t * bulkOne c χ g a M m t|)
      (volume.restrict (Ioo (1 : ℝ) 2)) := by
    have : Integrable (fun t => (1 - wF t) * (Φ t * bulkOne c χ g a M m t)) (volume.restrict (Ioo (1 : ℝ) 2)) :=
      (hΦN.integrable_mul hBN).bdd_mul (c := 1) (continuous_const.sub continuous_wF.1).aestronglyMeasurable
        (Eventually.of_forall fun t => by
          obtain ⟨h0, h1, -, -⟩ := Cvs.L2a.FarFarBound.wF_bounds t
          rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith)
    refine this.abs.congr (Eventually.of_forall fun t => ?_)
    simp only; ring_nf
  have hone : MemLp (fun _ : ℝ => (1 : ℝ)) 2 (volume.restrict (Ioo (1 : ℝ) 2)) := memLp_const 1
  have hint2 : Integrable (fun t => C * (1 * |Φ t|)) (volume.restrict (Ioo (1 : ℝ) 2)) :=
    (hone.integrable_mul hΦN.abs).const_mul C
  have hCS := Cvs.L2a.FarFarBound.integral_mul_abs_le (μ := volume.restrict (Ioo (1 : ℝ) 2)) (f := fun _ => (1 : ℝ))
    (fun _ => zero_le_one) hone hΦN
  have hPN : ∫ t in Ioo (1 : ℝ) 2, Φ t ^ 2 ≤ P :=
    setIntegral_mono_set ((memLp_two_iff_integrable_sq hΦ2.aestronglyMeasurable).1 hΦ2)
      (Eventually.of_forall fun t => sq_nonneg _) (Eventually.of_forall Ioo_subset_Ioi_self)
  have hone1 : ∫ _ in Ioo (1 : ℝ) 2, (1 : ℝ) ^ 2 = 1 := by
    simp; norm_num
  have hP0 : 0 ≤ P := integral_nonneg fun _ => sq_nonneg _
  unfold DOneNear
  rw [abs_mul, abs_neg, abs_two]
  have key : |∫ t in Ioo (1 : ℝ) 2, (1 - wF t) * Φ t * bulkOne c χ g a M m t|
      ≤ √(2 * c / π) * KN c * (1 / ((m : ℝ) * √(m : ℝ))) * P := by
    calc |∫ t in Ioo (1 : ℝ) 2, (1 - wF t) * Φ t * bulkOne c χ g a M m t|
        ≤ ∫ t in Ioo (1 : ℝ) 2, |(1 - wF t) * Φ t * bulkOne c χ g a M m t| := abs_integral_le_integral_abs
      _ ≤ ∫ t in Ioo (1 : ℝ) 2, C * (1 * |Φ t|) := setIntegral_mono_on hint1 hint2 measurableSet_Ioo hpt
      _ = C * ∫ t in Ioo (1 : ℝ) 2, 1 * |Φ t| := integral_const_mul _ _
      _ ≤ C * (√(∫ _ in Ioo (1 : ℝ) 2, (1 : ℝ) ^ 2) * √(∫ t in Ioo (1 : ℝ) 2, Φ t ^ 2)) :=
          mul_le_mul_of_nonneg_left hCS hC0
      _ ≤ C * (1 * √P) := by rw [hone1, Real.sqrt_one]; gcongr
      _ = √(2 * c / π) * KN c * (1 / ((m : ℝ) * √(m : ℝ))) * (√P * √P) := by rw [hC]; ring
      _ = _ := by rw [Real.mul_self_sqrt hP0]
  linarith

/-! ### Prop B -/

/-- `r₁(c) = κ(8K_F + 2√2K_N)`, `κ = √(2c/π)`. -/
def rOne (c : ℝ) : ℝ := √(2 * c / π) * (8 * KF c + 2 * √2 * KN c)

/-- **The weight-one bulk off the `m = 2` strip**: `|D₁ − near₂| ≤ r₁(c)·P`, uniformly in `M`. -/
theorem abs_DOne_sub_le {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 0 < c) (hχ : Function.Injective χ) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2)
    {M : ℕ} (hM : 3 ≤ M) :
    |DOne c χ g a M - DOneNear c χ g a M 2| ≤ rOne c * ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2 := by
  set P := ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2 with hPdef
  have hP0 : 0 ≤ P := integral_nonneg fun _ => sq_nonneg _
  obtain ⟨-, -, -, -, hKF, hKN⟩ := K_nonneg hc
  have hIcc : Finset.Icc 2 (M - 1) = insert 2 (Finset.Icc 3 (M - 1)) :=
    (Finset.insert_Icc_add_one_left_eq_Icc (by omega)).symm
  have h2 : 2 ∉ Finset.Icc 3 (M - 1) := by simp
  have e : DOne c χ g a M - DOneNear c χ g a M 2
      = ∑ m ∈ Finset.Icc 3 (M - 1), DOneNear c χ g a M m + ∑ m ∈ Finset.Icc 2 (M - 1), DOneFar c χ g a M m := by
    rw [DOne_eq_sum a hg hg₁ hg₂c hang hc hχc hM, Finset.sum_add_distrib, hIcc, Finset.sum_insert h2]
    ring
  rw [e]
  have hN : |∑ m ∈ Finset.Icc 3 (M - 1), DOneNear c χ g a M m| ≤ 2 * √(2 * c / π) * KN c * √2 * P := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun m hm => abs_DOneNear_le a hg hg₁ hg₂c hang hc hχ hχ0 hχc
      (Finset.mem_Icc.1 hm).1 (Finset.mem_Icc.1 hm).2).trans ?_
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    have hs := sum_near_le (n := M - 1) (by omega)
    have hs' : ∑ m ∈ Finset.Icc 3 (M - 1), 1 / ((m : ℝ) * √(m : ℝ)) ≤ √2 := by
      have : 0 ≤ 2 / √((M - 1 : ℕ) : ℝ) := by positivity
      linarith
    have : 0 ≤ 2 * √(2 * c / π) * KN c := by positivity
    gcongr
  have hF : |∑ m ∈ Finset.Icc 2 (M - 1), DOneFar c χ g a M m| ≤ 2 * √(2 * c / π) * KF c * 4 * P := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun m hm => abs_DOneFar_le a hg hg₁ hg₂c hang hc hχ hχ0 hχc hM
      (Finset.mem_Icc.1 hm).1 (Finset.mem_Icc.1 hm).2).trans ?_
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    have : 0 ≤ 2 * √(2 * c / π) * KF c := by positivity
    gcongr
    exact sum_far_le hM
  calc |∑ m ∈ Finset.Icc 3 (M - 1), DOneNear c χ g a M m + ∑ m ∈ Finset.Icc 2 (M - 1), DOneFar c χ g a M m|
      ≤ |∑ m ∈ Finset.Icc 3 (M - 1), DOneNear c χ g a M m| + |∑ m ∈ Finset.Icc 2 (M - 1), DOneFar c χ g a M m| :=
        abs_add_le _ _
    _ ≤ 2 * √(2 * c / π) * KN c * √2 * P + 2 * √(2 * c / π) * KF c * 4 * P := add_le_add hN hF
    _ = rOne c * P := by unfold rOne; ring

/-- **The three parts of `Dil` together**: `Dbot + Dmid + Dtop ≥ (−2Σ_m∫ū𝔅_m + Σ_m C_m + 𝒞_a) − r₁(c)P − |near₂|`,
with no window remainder. -/
theorem corners_add_mid_ge {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 0 < c) (hχ : Function.Injective χ) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2)
    {M : ℕ} (hM : 3 ≤ M) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2) :
    (-2 * ∑ m ∈ Finset.Icc 2 (M - 1),
          (∫ t in Ioi 1, ubar (fun ξ => ∑ i, a i * psi c (g i) ξ) wF M t * frakB c χ g a m t)
        + ∑ m ∈ Finset.Icc 2 (M - 1), cTop c χ g a M m + calCa c χ g a M)
        - rOne c * (∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2) - |DOneNear c χ g a M 2|
      ≤ Cvs.L2a.CornerSplitSqrtFloor.DbotG Cvs.Upstream.QuinticSmoothStep.S c (fun ξ => ∑ i, a i * psi c (g i) ξ) wF M δ
        + Cvs.L2a.CornerSplitSqrtFloor.DmidG Cvs.Upstream.QuinticSmoothStep.S c (fun ξ => ∑ i, a i * psi c (g i) ξ) wF M δ
        + Cvs.L2a.CornerSplitSqrtFloor.DtopG Cvs.Upstream.QuinticSmoothStep.S c (fun ξ => ∑ i, a i * psi c (g i) ξ) wF M δ := by
  rw [corners_add_mid_eq a hg hg₁ hg₂c hang hc hχc hM hδ0 hδ1]
  have h := abs_DOne_sub_le a hg hg₁ hg₂c hang hc hχ hχ0 hχc hM
  have k1 := neg_abs_le (DOne c χ g a M - DOneNear c χ g a M 2)
  have k2 := neg_abs_le (DOneNear c χ g a M 2)
  linarith

/-! ### `r₁(c) = O(c^{−1/2})` -/

/-- `c·K_F(c)` and `c·K_N(c)` are at most their values at `c = 1`, for `c ≥ 1`. -/
theorem mul_KF_KN_le {c : ℝ} (hc : 1 ≤ c) : c * KF c ≤ KF 1 ∧ c * KN c ≤ KN 1 := by
  have hc0 : 0 < c := by linarith
  have i1 : 1 / c ≤ 1 := by rw [div_le_one hc0]; exact hc
  have i2 : 1 / c ^ 2 ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith
  have i3 : 1 / c ^ 3 ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith
  have i1' : 0 ≤ 1 / c := by positivity
  have i2' : 0 ≤ 1 / c ^ 2 := by positivity
  have i3' : 0 ≤ 1 / c ^ 3 := by positivity
  have eF' : c * KF c = (15 / 11) ^ 2 * (16 / 3 + 364 / 45 * (1 / c) + 64 / 45 * (1 / c ^ 2))
      + (15 / 11) ^ 3 * (128 / 9 * (1 / c) + 256 / 75 * (1 / c ^ 3)) := by
    unfold KF K2far K3far; field_simp
  have eN' : c * KN c = (49 / 40) ^ 2 * (27 / 5 + 2619 / 400 * (1 / c) + 243 / 200 * (1 / c ^ 2))
      + (49 / 40) ^ 3 * (243 / 20 * (1 / c) + 243 / 125 * (1 / c ^ 3)) := by
    unfold KN K2near K3near; field_simp
  have eF1 : KF 1 = (15 / 11) ^ 2 * (16 / 3 + 364 / 45 + 64 / 45) + (15 / 11) ^ 3 * (128 / 9 + 256 / 75) := by
    unfold KF K2far K3far; norm_num
  have eN1 : KN 1 = (49 / 40) ^ 2 * (27 / 5 + 2619 / 400 + 243 / 200) + (49 / 40) ^ 3 * (243 / 20 + 243 / 125) := by
    unfold KN K2near K3near; norm_num
  rw [eF', eN', eF1, eN1]
  constructor <;> nlinarith

/-- **`r₁(c) ≤ r₁⁰/√c`** for `c ≥ 1`, with `r₁⁰ = √(2/π)(8K_F(1) + 2√2K_N(1))`. -/
theorem rOne_le {c : ℝ} (hc : 1 ≤ c) : rOne c ≤ √(2 / π) * (8 * KF 1 + 2 * √2 * KN 1) / √c := by
  have hc0 : 0 < c := by linarith
  obtain ⟨hF, hN⟩ := mul_KF_KN_le hc
  have hsc : 0 < √c := Real.sqrt_pos.2 hc0
  unfold rOne
  rw [le_div_iff₀ hsc]
  have e : √(2 * c / π) = √(2 / π) * √c := by
    rw [← Real.sqrt_mul (by positivity)]; congr 1; ring
  rw [e]
  have hcc : √c * √c = c := Real.mul_self_sqrt hc0.le
  calc √(2 / π) * √c * (8 * KF c + 2 * √2 * KN c) * √c
        = √(2 / π) * (√c * √c) * (8 * KF c + 2 * √2 * KN c) := by ring
    _ = √(2 / π) * (8 * (c * KF c) + 2 * √2 * (c * KN c)) := by rw [hcc]; ring
    _ ≤ √(2 / π) * (8 * KF 1 + 2 * √2 * KN 1) := by gcongr

/-! ### The `m = 2` strip: Lemma LP -/

/-- The strip Laplace form `(1/k!)∫_0^∞ s^k e^{−sσ₀}‖A e^{sQ_{c²}(·, y)}‖_{L²(2,M]} ds`. -/
def lapStrip (c σ₀ y : ℝ) (M k : ℕ) (A : ℝ → ℂ) : ℝ :=
  1 / (k.factorial : ℝ) * ∫ s in Ioi (0 : ℝ), s ^ k * Real.exp (-(s * σ₀))
    * √(∫ x in Ioc (2 : ℝ) M, ‖A x‖ ^ 2 * Real.exp (2 * s * (qQ c (c ^ 2) y x).re))

/-- **Lemma LP on the strip**: for `t ∈ (1, 2)` and `σᵢ² ≥ σ₀ > 0`, `|bulk₁_2(t)|` is at most `(κ/2)` times the
two strip Laplace forms of `A₂` (`k = 1`) and `A₃` (`k = 2`) at `y = t/2`, times `√P`. -/
theorem abs_bulkOne_strip_le {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 0 < c) (hχ : Function.Injective χ) {σ₀ : ℝ} (hσ₀ : 0 < σ₀) (hσ : ∀ i, σ₀ ≤ c ^ 2 - χ i)
    {M : ℕ} (hM : 3 ≤ M) {t : ℝ} (ht : t ∈ Ioo 1 2) :
    |bulkOne c χ g a M 2 t|
      ≤ √(2 * c / π) / 2 * (lapStrip c σ₀ (t / 2) M 1 (fun x => aC₂ (fun _ => (1 : ℂ)) (fun _ => 0) c (t / 2) x)
          + lapStrip c σ₀ (t / 2) M 2 (fun x => aC₃ (fun _ => (1 : ℂ)) c (t / 2) x))
        * √(∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2) := by
  set y := t / 2 with hydef
  have hy0 : 0 < y := by rw [hydef]; linarith [ht.1]
  have hy1 : y < 1 := by rw [hydef]; linarith [ht.2]
  have hM2 : (2 : ℝ) ≤ M := by exact_mod_cast (show 2 ≤ M by omega)
  have hψc : ∀ i, Continuous (psi c (g i)) := fun i => (rung_system (hg i) (hg₁ i) (hg₂c i) (hang i)).2.2.1
  obtain ⟨hq, hq1⟩ := continuous_qQ c (c ^ 2) y
  have hp : Continuous fun x => ((pP x : ℝ) : ℂ) := by unfold pP; fun_prop
  have hk : Continuous fun x => kK c y x := by unfold kK; fun_prop
  have h2c : Continuous fun x => aC₂ (fun _ => (1 : ℂ)) (fun _ => 0) c y x := by unfold aC₂; fun_prop
  have h3c : Continuous fun x => aC₃ (fun _ => (1 : ℂ)) c y x := by unfold aC₃; fun_prop
  have hQne : ∀ (χ' x : ℝ), x ∈ Icc (2 : ℝ) M → qQ c χ' y x ≠ 0 := fun χ' x hx =>
    Cvs.L2a.QIdentityRealWeight.qQ_ne_zero_of_pos hc (by linarith [hx.1]) hy0
  have : IsFiniteMeasure (volume.restrict (Ioc (2 : ℝ) M)) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Ioc]; exact ENNReal.ofReal_lt_top⟩
  have hmemA : ∀ A : ℝ → ℂ, Continuous A → MemLp A 2 (volume.restrict (Ioc (2 : ℝ) M)) := fun A hA => by
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hA.continuousOn (s := Icc (2 : ℝ) M))
    exact MemLp.of_bound hA.aestronglyMeasurable C ((ae_restrict_iff' measurableSet_Ioc).2
      (Eventually.of_forall fun x hx => hC x (Ioc_subset_Icc_self hx)))
  have hre : ∀ x ∈ Ioc (2 : ℝ) M, (qQ c (c ^ 2) y x).re ≤ 0 := fun x hx => by
    rw [qQ_re, sub_self, sub_zero]
    have : 0 ≤ x ^ 2 - 1 := by nlinarith [hx.1]
    have : y ^ 2 - 1 ≤ 0 := by nlinarith
    have : 0 ≤ c ^ 2 := sq_nonneg c
    nlinarith [mul_nonneg (mul_nonneg this ‹0 ≤ x ^ 2 - 1›) (neg_nonneg.2 ‹y ^ 2 - 1 ≤ 0›)]
  -- the weight one has `R = A₂/Q² + A₃/Q³`
  have hsplit : ∀ i, ∫ x in Ioc (2 : ℝ) M, eF c y x * (psi c (g i) x : ℂ)
        * rRc (fun _ => 1) (fun _ => 0) (fun _ => 0) c (χ i) y x
      = (∫ x in Ioc (2 : ℝ) M, eF c y x * (psi c (g i) x : ℂ)
          * (aC₂ (fun _ => (1 : ℂ)) (fun _ => 0) c y x / qQ c (χ i) y x ^ (1 + 1)))
        + ∫ x in Ioc (2 : ℝ) M, eF c y x * (psi c (g i) x : ℂ)
          * (aC₃ (fun _ => (1 : ℂ)) c y x / qQ c (χ i) y x ^ (2 + 1)) := by
    intro i
    obtain ⟨hqi, -⟩ := continuous_qQ c (χ i) y
    have hcont : ∀ (A : ℝ → ℂ) (n : ℕ), Continuous A →
        IntegrableOn (fun x => eF c y x * (psi c (g i) x : ℂ) * (A x / qQ c (χ i) y x ^ n)) (Ioc (2 : ℝ) M) :=
      fun A n hA => (((((continuous_eF c y).1.mul (continuous_ofReal.comp (hψc i))).continuousOn).mul
        (hA.continuousOn.div (hqi.pow n).continuousOn fun x hx => pow_ne_zero n (hQne _ x hx))).integrableOn_Icc
        (μ := volume)).mono_set Ioc_subset_Icc_self
    rw [← integral_add (hcont _ _ h2c) (hcont _ _ h3c)]
    refine setIntegral_congr_fun measurableSet_Ioc fun x hx => ?_
    have hQ := hQne (χ i) x (Ioc_subset_Icc_self hx)
    rw [rRc_eq hQ]
    simp only [aC₁, mul_zero, add_zero, zero_div, zero_add]
    ring
  have hL1 := Cvs.L2a.SigmaSquareMultiplier.span_bulk_laplace_le a hg hg₁ hg₂c hang hc hχ 1 (W := Ioc (2 : ℝ) M) (y := y) measurableSet_Ioc
    (fun x hx => lt_trans (by norm_num : (1 : ℝ) < 2) hx.1) (hmemA _ h2c) hre hσ₀ hσ
  have hL2 := Cvs.L2a.SigmaSquareMultiplier.span_bulk_laplace_le a hg hg₁ hg₂c hang hc hχ 2 (W := Ioc (2 : ℝ) M) (y := y) measurableSet_Ioc
    (fun x hx => lt_trans (by norm_num : (1 : ℝ) < 2) hx.1) (hmemA _ h3c) hre hσ₀ hσ
  unfold bulkOne
  have h2r : ((2 : ℕ) : ℝ) = 2 := by norm_num
  simp only [h2r]
  rw [← hydef]
  simp_rw [intervalIntegral.integral_of_le hM2, hsplit, mul_add, Finset.sum_add_distrib]
  rw [abs_mul, abs_of_nonneg (by positivity)]
  have hP := Real.sqrt_nonneg (∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2)
  calc √(2 * c / π) / 2 * |((∑ i, (a i : ℂ) * ∫ x in Ioc (2 : ℝ) M, eF c y x * (psi c (g i) x : ℂ)
          * (aC₂ (fun _ => (1 : ℂ)) (fun _ => 0) c y x / qQ c (χ i) y x ^ (1 + 1)))
        + ∑ i, (a i : ℂ) * ∫ x in Ioc (2 : ℝ) M, eF c y x * (psi c (g i) x : ℂ)
          * (aC₃ (fun _ => (1 : ℂ)) c y x / qQ c (χ i) y x ^ (2 + 1))).re|
      ≤ √(2 * c / π) / 2 * (‖∑ i, (a i : ℂ) * ∫ x in Ioc (2 : ℝ) M, eF c y x * (psi c (g i) x : ℂ)
          * (aC₂ (fun _ => (1 : ℂ)) (fun _ => 0) c y x / qQ c (χ i) y x ^ (1 + 1))‖
        + ‖∑ i, (a i : ℂ) * ∫ x in Ioc (2 : ℝ) M, eF c y x * (psi c (g i) x : ℂ)
          * (aC₃ (fun _ => (1 : ℂ)) c y x / qQ c (χ i) y x ^ (2 + 1))‖) := by
        gcongr
        exact (Complex.abs_re_le_norm _).trans (norm_add_le _ _)
    _ ≤ √(2 * c / π) / 2 * (lapStrip c σ₀ y M 1 (fun x => aC₂ (fun _ => (1 : ℂ)) (fun _ => 0) c y x)
          * √(∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2)
        + lapStrip c σ₀ y M 2 (fun x => aC₃ (fun _ => (1 : ℂ)) c y x)
          * √(∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2)) := by
        gcongr
        · exact hL1.trans (le_of_eq (by unfold lapStrip; ring))
        · exact hL2.trans (le_of_eq (by unfold lapStrip; ring))
    _ = _ := by ring

/-! ### The `m = 2` strip in closed form -/

/-- Gaussian moments: `∫_0^∞ x^q e^{−bx²} = b^{−(q+1)/2}·Γ((q + 1)/2)/2` for `q > −1`. -/
theorem gauss_moment {b q : ℝ} (hb : 0 < b) (hq : -1 < q) :
    IntegrableOn (fun x : ℝ => x ^ q * Real.exp (-b * x ^ 2)) (Ioi 0)
      ∧ ∫ x in Ioi (0 : ℝ), x ^ q * Real.exp (-b * x ^ 2)
        = b ^ (-(q + 1) / 2) * (1 / 2) * Real.Gamma ((q + 1) / 2) := by
  have e : (fun x : ℝ => x ^ q * Real.exp (-b * x ^ 2)) = fun x => x ^ q * Real.exp (-b * x ^ (2 : ℝ)) := by
    funext x; rw [Real.rpow_two]
  rw [e]
  exact ⟨integrableOn_rpow_mul_exp_neg_mul_rpow hq two_pos hb, integral_rpow_mul_exp_neg_mul_rpow two_pos hq hb⟩

/-- The Laplace integral `∫_0^∞ s^{a−1}e^{−σs} = σ^{−a}Γ(a)`, `a, σ > 0`. -/
theorem laplace_rpow {a σ : ℝ} (ha : 0 < a) (hσ : 0 < σ) :
    IntegrableOn (fun s : ℝ => s ^ (a - 1) * Real.exp (-(σ * s))) (Ioi 0)
      ∧ ∫ s in Ioi (0 : ℝ), s ^ (a - 1) * Real.exp (-(σ * s)) = (1 / σ) ^ a * Real.Gamma a := by
  refine ⟨?_, integral_rpow_mul_exp_neg_mul_Ioi ha hσ⟩
  have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := a - 1) (b := σ) (by linarith) one_pos hσ
  refine this.congr_fun (fun s _ => ?_) measurableSet_Ioi
  simp only [Real.rpow_one, neg_mul]

/-- **Two Gaussian terms**: if `0 ≤ f ≤ 2α²x^{2a}e^{−bx²} + 2β²x^{2d}e^{−bx²}` on `(2, M]`, then
`‖f‖_{L¹}^{1/2} ≤ α√Γ(a + 1/2)·b^{−(2a+1)/4} + β√Γ(d + 1/2)·b^{−(2d+1)/4}`. -/
theorem sqrt_integral_gauss_le {M b α β : ℝ} (hb : 0 < b) (hα : 0 ≤ α) (hβ : 0 ≤ β) (a d : ℕ) {f : ℝ → ℝ}
    (hf0 : ∀ x ∈ Ioc (2 : ℝ) M, 0 ≤ f x)
    (hf : ∀ x ∈ Ioc (2 : ℝ) M,
      f x ≤ 2 * α ^ 2 * (x ^ ((2 * a : ℕ) : ℝ) * Real.exp (-b * x ^ 2))
        + 2 * β ^ 2 * (x ^ ((2 * d : ℕ) : ℝ) * Real.exp (-b * x ^ 2))) :
    √(∫ x in Ioc (2 : ℝ) M, f x)
      ≤ α * √(Real.Gamma ((((2 * a : ℕ) : ℝ) + 1) / 2)) * b ^ (-(((2 * a : ℕ) : ℝ) + 1) / 4)
        + β * √(Real.Gamma ((((2 * d : ℕ) : ℝ) + 1) / 2)) * b ^ (-(((2 * d : ℕ) : ℝ) + 1) / 4) := by
  set qa : ℝ := ((2 * a : ℕ) : ℝ) with hqa
  set qd : ℝ := ((2 * d : ℕ) : ℝ) with hqd
  have hqa1 : -1 < qa := by rw [hqa]; have : (0 : ℝ) ≤ ((2 * a : ℕ) : ℝ) := Nat.cast_nonneg _; linarith
  have hqd1 : -1 < qd := by rw [hqd]; have : (0 : ℝ) ≤ ((2 * d : ℕ) : ℝ) := Nat.cast_nonneg _; linarith
  obtain ⟨ia, ea⟩ := gauss_moment hb hqa1
  obtain ⟨id, ed⟩ := gauss_moment hb hqd1
  set g : ℝ → ℝ := fun x => 2 * α ^ 2 * (x ^ qa * Real.exp (-b * x ^ 2)) + 2 * β ^ 2 * (x ^ qd * Real.exp (-b * x ^ 2))
    with hg
  have hgi : IntegrableOn g (Ioi 0) := (ia.const_mul _).add (id.const_mul _)
  have hg0 : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ g x := fun x hx => by
    have := Real.rpow_nonneg (le_of_lt hx) qa
    have := Real.rpow_nonneg (le_of_lt hx) qd
    simp only [hg]; positivity
  have hsub : Ioc (2 : ℝ) M ⊆ Ioi 0 := fun x hx => lt_trans (by norm_num : (0 : ℝ) < 2) hx.1
  have h1 : ∫ x in Ioc (2 : ℝ) M, f x ≤ ∫ x in Ioc (2 : ℝ) M, g x :=
    integral_mono_of_nonneg ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall hf0))
      (hgi.mono_set hsub) ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall hf))
  have h2 : ∫ x in Ioc (2 : ℝ) M, g x ≤ ∫ x in Ioi (0 : ℝ), g x :=
    setIntegral_mono_set hgi ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall hg0))
      (Eventually.of_forall hsub)
  have h3 : ∫ x in Ioi (0 : ℝ), g x
      = α ^ 2 * Real.Gamma ((qa + 1) / 2) * b ^ (-(qa + 1) / 2)
        + β ^ 2 * Real.Gamma ((qd + 1) / 2) * b ^ (-(qd + 1) / 2) := by
    simp only [hg]
    rw [integral_add (ia.const_mul _) (id.const_mul _), integral_const_mul, integral_const_mul, ea, ed]
    ring
  have hsq : ∀ q : ℝ, b ^ (-(q + 1) / 2) = (b ^ (-(q + 1) / 4)) ^ 2 := fun q => by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hb.le]; congr 1; push_cast; ring
  have hGa : 0 ≤ Real.Gamma ((qa + 1) / 2) := Real.Gamma_nonneg_of_nonneg (by linarith)
  have hGd : 0 ≤ Real.Gamma ((qd + 1) / 2) := Real.Gamma_nonneg_of_nonneg (by linarith)
  have hba := Real.rpow_nonneg hb.le (-(qa + 1) / 4)
  have hbd := Real.rpow_nonneg hb.le (-(qd + 1) / 4)
  calc √(∫ x in Ioc (2 : ℝ) M, f x) ≤ √(α ^ 2 * Real.Gamma ((qa + 1) / 2) * b ^ (-(qa + 1) / 2)
        + β ^ 2 * Real.Gamma ((qd + 1) / 2) * b ^ (-(qd + 1) / 2)) := by
        rw [← h3]; exact Real.sqrt_le_sqrt (h1.trans h2)
    _ ≤ √(α ^ 2 * Real.Gamma ((qa + 1) / 2) * b ^ (-(qa + 1) / 2))
        + √(β ^ 2 * Real.Gamma ((qd + 1) / 2) * b ^ (-(qd + 1) / 2)) :=
        sqrt_add_le_add (by positivity) (by positivity)
    _ = _ := by
        rw [hsq qa, hsq qd]
        rw [show α ^ 2 * Real.Gamma ((qa + 1) / 2) * (b ^ (-(qa + 1) / 4)) ^ 2
            = (α * b ^ (-(qa + 1) / 4)) ^ 2 * Real.Gamma ((qa + 1) / 2) by ring,
          show β ^ 2 * Real.Gamma ((qd + 1) / 2) * (b ^ (-(qd + 1) / 4)) ^ 2
            = (β * b ^ (-(qd + 1) / 4)) ^ 2 * Real.Gamma ((qd + 1) / 2) by ring,
          Real.sqrt_mul (sq_nonneg _), Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity),
          Real.sqrt_sq (by positivity)]
        ring

/-- `(u + v)² ≤ 2u² + 2v²`. -/
theorem add_sq_le_two (u v : ℝ) : (u + v) ^ 2 ≤ 2 * u ^ 2 + 2 * v ^ 2 := by nlinarith [sq_nonneg (u - v)]

/-- **Strip atoms**: for `x ≥ 2`, `0 ≤ y ≤ 1`, `r = 1 − y²`, `s ≥ 0`, `b = (3/2)c²rs`:
`|A₂|²e^{2s Re Q_{c²}} ≤ 2(4c³r)²x⁶e^{−bx²} + 2(10c² + 2c)²x⁴e^{−bx²}` and
`|A₃|²e^{2s Re Q_{c²}} ≤ 2(16c⁴r²)²x⁸e^{−bx²} + 2(16c²)²x⁴e^{−bx²}`. -/
theorem strip_atoms {c y s x : ℝ} (hc : 0 < c) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (hs : 0 ≤ s) (hx : 2 ≤ x) :
    ‖aC₂ (fun _ => (1 : ℂ)) (fun _ => 0) c y x‖ ^ 2 * Real.exp (2 * s * (qQ c (c ^ 2) y x).re)
        ≤ 2 * (4 * c ^ 3 * (1 - y ^ 2)) ^ 2
            * (x ^ ((2 * 3 : ℕ) : ℝ) * Real.exp (-(3 / 2 * c ^ 2 * (1 - y ^ 2) * s) * x ^ 2))
          + 2 * (10 * c ^ 2 + 2 * c) ^ 2
            * (x ^ ((2 * 2 : ℕ) : ℝ) * Real.exp (-(3 / 2 * c ^ 2 * (1 - y ^ 2) * s) * x ^ 2))
      ∧ ‖aC₃ (fun _ => (1 : ℂ)) c y x‖ ^ 2 * Real.exp (2 * s * (qQ c (c ^ 2) y x).re)
        ≤ 2 * (16 * c ^ 4 * (1 - y ^ 2) ^ 2) ^ 2
            * (x ^ ((2 * 4 : ℕ) : ℝ) * Real.exp (-(3 / 2 * c ^ 2 * (1 - y ^ 2) * s) * x ^ 2))
          + 2 * (16 * c ^ 2) ^ 2
            * (x ^ ((2 * 2 : ℕ) : ℝ) * Real.exp (-(3 / 2 * c ^ 2 * (1 - y ^ 2) * s) * x ^ 2)) := by
  set r := 1 - y ^ 2 with hrdef
  set p := x ^ 2 - 1 with hpdef
  have hr0 : 0 ≤ r := by rw [hrdef]; nlinarith
  have hr1 : r ≤ 1 := by rw [hrdef]; nlinarith
  have hx0 : 0 ≤ x := by linarith
  have hp0 : 0 ≤ p := by rw [hpdef]; nlinarith
  have hpx : p ≤ x ^ 2 := by rw [hpdef]; linarith
  have hp34 : 3 / 4 * x ^ 2 ≤ p := by rw [hpdef]; nlinarith
  -- the exponential
  have hE : Real.exp (2 * s * (qQ c (c ^ 2) y x).re) ≤ Real.exp (-(3 / 2 * c ^ 2 * r * s) * x ^ 2) := by
    apply Real.exp_le_exp.2
    rw [qQ_re, sub_self, sub_zero]
    have e : c ^ 2 * (x ^ 2 - 1) * (y ^ 2 - 1) = -(c ^ 2 * p * r) := by rw [hpdef, hrdef]; ring
    rw [e]
    have : 3 / 4 * x ^ 2 * (c ^ 2 * r * s) ≤ p * (c ^ 2 * r * s) :=
      mul_le_mul_of_nonneg_right hp34 (by positivity)
    nlinarith
  have hE0 : 0 ≤ Real.exp (2 * s * (qQ c (c ^ 2) y x).re) := (Real.exp_pos _).le
  have hcast : ∀ n : ℕ, x ^ ((n : ℕ) : ℝ) = x ^ n := fun n => Real.rpow_natCast x n
  rw [hcast, hcast, hcast]
  have hQ1 : ‖qQ₁ c y x‖ ≤ 2 * c ^ 2 * x * r + 2 * c * y := Cvs.L2a.QIdentityIterated.norm_qQ₁_le_near hx0 hy0 hy1 hc.le
  have hQ2 : ‖qQ₂ c y‖ = 2 * c ^ 2 * r := Cvs.L2a.QIdentityIterated.norm_qQ₂_eq_near (by rw [abs_of_nonneg hy0]; exact hy1)
  have hcy : c * y ≤ c := by nlinarith
  have hcy0 : 0 ≤ c * y := by positivity
  constructor
  · have hA2 := Cvs.L2a.QIdentityComplexWeight.norm_aC₂_le (w := fun _ => (1 : ℂ)) (w₁ := fun _ => 0) hc.le hy0 (by linarith : (1 : ℝ) ≤ x)
    simp only [norm_one, mul_one, norm_zero, mul_zero, add_zero] at hA2
    unfold Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval.pP at hA2
    rw [hQ2, ← hpdef] at hA2
    have hk : 0 ≤ 2 * x + 2 * (c * y) * p := by positivity
    have hA : ‖aC₂ (fun _ => (1 : ℂ)) (fun _ => 0) c y x‖ ≤ 4 * c ^ 3 * r * x ^ 3 + (10 * c ^ 2 + 2 * c) * x ^ 2 := by
      refine hA2.trans ?_
      have h1 : (2 * x + 2 * (c * y) * p) * ‖qQ₁ c y x‖
          ≤ (2 * x + 2 * (c * y) * p) * (2 * c ^ 2 * x * r + 2 * c * y) := by gcongr
      have hy2 : y ^ 2 ≤ 1 := by nlinarith
      have hc0 := hc.le
      have k1 : 4 * c ^ 2 * x ^ 2 * r ≤ 4 * c ^ 2 * x ^ 2 :=
        calc 4 * c ^ 2 * x ^ 2 * r ≤ 4 * c ^ 2 * x ^ 2 * 1 := by gcongr
          _ = _ := by ring
      have k2 : 4 * c * x * y ≤ 2 * c * x ^ 2 :=
        calc 4 * c * x * y ≤ 4 * c * x * 1 := by gcongr
          _ ≤ 4 * c * x * (x / 2) := by gcongr; linarith
          _ = _ := by ring
      have k3 : 4 * c ^ 3 * x * y * p * r ≤ 4 * c ^ 3 * r * x ^ 3 :=
        calc 4 * c ^ 3 * x * y * p * r = (4 * c ^ 3 * r * x) * (y * p) := by ring
          _ ≤ (4 * c ^ 3 * r * x) * (1 * x ^ 2) := by gcongr
          _ = _ := by ring
      have k4 : 4 * c ^ 2 * y ^ 2 * p ≤ 4 * c ^ 2 * x ^ 2 :=
        calc 4 * c ^ 2 * y ^ 2 * p = (4 * c ^ 2) * (y ^ 2 * p) := by ring
          _ ≤ (4 * c ^ 2) * (1 * x ^ 2) := by gcongr
          _ = _ := by ring
      have k5 : p * (2 * c ^ 2 * r) ≤ 2 * c ^ 2 * x ^ 2 :=
        calc p * (2 * c ^ 2 * r) = (2 * c ^ 2) * (p * r) := by ring
          _ ≤ (2 * c ^ 2) * (x ^ 2 * 1) := by gcongr
          _ = _ := by ring
      have e : (2 * x + 2 * (c * y) * p) * (2 * c ^ 2 * x * r + 2 * c * y)
          = 4 * c ^ 2 * x ^ 2 * r + 4 * c * x * y + 4 * c ^ 3 * x * y * p * r + 4 * c ^ 2 * y ^ 2 * p := by ring
      have e2 : 4 * c ^ 3 * r * x ^ 3 + (10 * c ^ 2 + 2 * c) * x ^ 2
          = 4 * c ^ 2 * x ^ 2 + 2 * c * x ^ 2 + 4 * c ^ 3 * r * x ^ 3 + 4 * c ^ 2 * x ^ 2 + 2 * c ^ 2 * x ^ 2 := by
        ring
      rw [e2]
      linarith
    have hA0 : 0 ≤ ‖aC₂ (fun _ => (1 : ℂ)) (fun _ => 0) c y x‖ := norm_nonneg _
    have hsq : ‖aC₂ (fun _ => (1 : ℂ)) (fun _ => 0) c y x‖ ^ 2
        ≤ 2 * (4 * c ^ 3 * r) ^ 2 * x ^ (2 * 3) + 2 * (10 * c ^ 2 + 2 * c) ^ 2 * x ^ (2 * 2) :=
      calc ‖aC₂ (fun _ => (1 : ℂ)) (fun _ => 0) c y x‖ ^ 2
          ≤ (4 * c ^ 3 * r * x ^ 3 + (10 * c ^ 2 + 2 * c) * x ^ 2) ^ 2 := pow_le_pow_left₀ hA0 hA 2
        _ ≤ 2 * (4 * c ^ 3 * r * x ^ 3) ^ 2 + 2 * ((10 * c ^ 2 + 2 * c) * x ^ 2) ^ 2 := add_sq_le_two _ _
        _ = _ := by ring
    calc ‖aC₂ (fun _ => (1 : ℂ)) (fun _ => 0) c y x‖ ^ 2 * Real.exp (2 * s * (qQ c (c ^ 2) y x).re)
        ≤ (2 * (4 * c ^ 3 * r) ^ 2 * x ^ (2 * 3) + 2 * (10 * c ^ 2 + 2 * c) ^ 2 * x ^ (2 * 2))
            * Real.exp (-(3 / 2 * c ^ 2 * r * s) * x ^ 2) := mul_le_mul hsq hE hE0 (by positivity)
      _ = _ := by ring
  · have hA3 := Cvs.L2a.QIdentityComplexWeight.norm_aC₃_eq (w := fun _ => (1 : ℂ)) (c := c) (y := y) (by linarith : (1 : ℝ) ≤ x)
    simp only [norm_one, mul_one] at hA3
    unfold Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval.pP at hA3
    rw [← hpdef] at hA3
    have hy2 : y ^ 2 ≤ 1 := by nlinarith
    have hQ1sq : ‖qQ₁ c y x‖ ^ 2 ≤ 8 * c ^ 4 * x ^ 2 * r ^ 2 + 8 * c ^ 2 :=
      calc ‖qQ₁ c y x‖ ^ 2 ≤ (2 * c ^ 2 * x * r + 2 * c * y) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hQ1 2
        _ ≤ 2 * (2 * c ^ 2 * x * r) ^ 2 + 2 * (2 * c * y) ^ 2 := add_sq_le_two _ _
        _ = 8 * c ^ 4 * x ^ 2 * r ^ 2 + 8 * c ^ 2 * y ^ 2 := by ring
        _ ≤ 8 * c ^ 4 * x ^ 2 * r ^ 2 + 8 * c ^ 2 * 1 := by gcongr
        _ = _ := by ring
    have hA : ‖aC₃ (fun _ => (1 : ℂ)) c y x‖ ≤ 16 * c ^ 4 * r ^ 2 * x ^ 4 + 16 * c ^ 2 * x ^ 2 := by
      rw [hA3]
      calc 2 * p * ‖qQ₁ c y x‖ ^ 2 ≤ 2 * p * (8 * c ^ 4 * x ^ 2 * r ^ 2 + 8 * c ^ 2) := by gcongr
        _ ≤ 2 * x ^ 2 * (8 * c ^ 4 * x ^ 2 * r ^ 2 + 8 * c ^ 2) := by gcongr
        _ = _ := by ring
    have hA0 : 0 ≤ ‖aC₃ (fun _ => (1 : ℂ)) c y x‖ := norm_nonneg _
    have hsq : ‖aC₃ (fun _ => (1 : ℂ)) c y x‖ ^ 2
        ≤ 2 * (16 * c ^ 4 * r ^ 2) ^ 2 * x ^ (2 * 4) + 2 * (16 * c ^ 2) ^ 2 * x ^ (2 * 2) :=
      calc ‖aC₃ (fun _ => (1 : ℂ)) c y x‖ ^ 2 ≤ (16 * c ^ 4 * r ^ 2 * x ^ 4 + 16 * c ^ 2 * x ^ 2) ^ 2 :=
            pow_le_pow_left₀ hA0 hA 2
        _ ≤ 2 * (16 * c ^ 4 * r ^ 2 * x ^ 4) ^ 2 + 2 * (16 * c ^ 2 * x ^ 2) ^ 2 := add_sq_le_two _ _
        _ = _ := by ring
    calc ‖aC₃ (fun _ => (1 : ℂ)) c y x‖ ^ 2 * Real.exp (2 * s * (qQ c (c ^ 2) y x).re)
        ≤ (2 * (16 * c ^ 4 * r ^ 2) ^ 2 * x ^ (2 * 4) + 2 * (16 * c ^ 2) ^ 2 * x ^ (2 * 2))
            * Real.exp (-(3 / 2 * c ^ 2 * r * s) * x ^ 2) := mul_le_mul hsq hE hE0 (by positivity)
      _ = _ := by ring

/-- **The strip Laplace form in closed form**: if `√(∫‖A‖²e^{2sReQ}) ≤ C₁(Bs)^{−e₁} + C₂(Bs)^{−e₂}` for `s > 0`, with
`e_i < k + 1`, then `lapStrip ≤ (1/k!)Σᵢ Cᵢ B^{−eᵢ}σ₀^{−(k+1−eᵢ)}Γ(k + 1 − eᵢ)`. -/
theorem lapStrip_le {c σ₀ y B C₁ C₂ e₁ e₂ : ℝ} {M k : ℕ} {A : ℝ → ℂ} (hσ₀ : 0 < σ₀) (hB : 0 < B)
    (he₁ : e₁ < k + 1) (he₂ : e₂ < k + 1)
    (hA : ∀ s, 0 < s → √(∫ x in Ioc (2 : ℝ) M, ‖A x‖ ^ 2 * Real.exp (2 * s * (qQ c (c ^ 2) y x).re))
      ≤ C₁ * (B * s) ^ (-e₁) + C₂ * (B * s) ^ (-e₂)) :
    lapStrip c σ₀ y M k A
      ≤ 1 / (k.factorial : ℝ) * (C₁ * B ^ (-e₁) * ((1 / σ₀) ^ ((k : ℝ) + 1 - e₁) * Real.Gamma ((k : ℝ) + 1 - e₁))
        + C₂ * B ^ (-e₂) * ((1 / σ₀) ^ ((k : ℝ) + 1 - e₂) * Real.Gamma ((k : ℝ) + 1 - e₂))) := by
  obtain ⟨i₁, v₁⟩ := laplace_rpow (a := (k : ℝ) + 1 - e₁) (by linarith) hσ₀
  obtain ⟨i₂, v₂⟩ := laplace_rpow (a := (k : ℝ) + 1 - e₂) (by linarith) hσ₀
  unfold lapStrip
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  set G : ℝ → ℝ := fun s => C₁ * B ^ (-e₁) * (s ^ ((k : ℝ) + 1 - e₁ - 1) * Real.exp (-(σ₀ * s)))
    + C₂ * B ^ (-e₂) * (s ^ ((k : ℝ) + 1 - e₂ - 1) * Real.exp (-(σ₀ * s))) with hG
  have hGi : IntegrableOn G (Ioi 0) := (i₁.const_mul _).add (i₂.const_mul _)
  have hpt : ∀ s ∈ Ioi (0 : ℝ), s ^ k * Real.exp (-(s * σ₀))
      * √(∫ x in Ioc (2 : ℝ) M, ‖A x‖ ^ 2 * Real.exp (2 * s * (qQ c (c ^ 2) y x).re)) ≤ G s := by
    intro s hs
    have hs0 : 0 < s := hs
    have hpos : 0 ≤ s ^ k * Real.exp (-(s * σ₀)) := by positivity
    refine (mul_le_mul_of_nonneg_left (hA s hs0) hpos).trans (le_of_eq ?_)
    have hsk : s ^ k = s ^ (k : ℝ) := (Real.rpow_natCast s k).symm
    have m1 : (B * s) ^ (-e₁) = B ^ (-e₁) * s ^ (-e₁) := Real.mul_rpow hB.le hs0.le
    have m2 : (B * s) ^ (-e₂) = B ^ (-e₂) * s ^ (-e₂) := Real.mul_rpow hB.le hs0.le
    have a1 : s ^ (k : ℝ) * s ^ (-e₁) = s ^ ((k : ℝ) + 1 - e₁ - 1) := by
      rw [← Real.rpow_add hs0]; congr 1; ring
    have a2 : s ^ (k : ℝ) * s ^ (-e₂) = s ^ ((k : ℝ) + 1 - e₂ - 1) := by
      rw [← Real.rpow_add hs0]; congr 1; ring
    show _ = C₁ * B ^ (-e₁) * (s ^ ((k : ℝ) + 1 - e₁ - 1) * Real.exp (-(σ₀ * s)))
      + C₂ * B ^ (-e₂) * (s ^ ((k : ℝ) + 1 - e₂ - 1) * Real.exp (-(σ₀ * s)))
    rw [← a1, ← a2, hsk, m1, m2, mul_comm s σ₀]
    ring
  calc ∫ s in Ioi (0 : ℝ), s ^ k * Real.exp (-(s * σ₀))
        * √(∫ x in Ioc (2 : ℝ) M, ‖A x‖ ^ 2 * Real.exp (2 * s * (qQ c (c ^ 2) y x).re))
      ≤ ∫ s in Ioi (0 : ℝ), G s :=
        integral_mono_of_nonneg ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun s hs => by
          have : (0 : ℝ) < s := hs; positivity)) hGi ((ae_restrict_iff' measurableSet_Ioi).2
          (Eventually.of_forall hpt))
    _ = _ := by
        rw [hG, integral_add (i₁.const_mul _) (i₂.const_mul _), integral_const_mul, integral_const_mul, v₁, v₂]

/-- The `A₂` strip form: `lapStrip₁(A₂) ≤ C₁B^{−7/4}σ₀^{−1/4}Γ(1/4) + C₂B^{−5/4}σ₀^{−3/4}Γ(3/4)`,
`B = (3/2)c²r`, `C₁ = 4c³r√Γ(7/2)`, `C₂ = (10c² + 2c)√Γ(5/2)`. -/
theorem lapStrip_A₂_le {c σ₀ y : ℝ} (hc : 0 < c) (hσ₀ : 0 < σ₀) (hy0 : 0 ≤ y) (hy1 : y < 1) (M : ℕ) :
    lapStrip c σ₀ y M 1 (fun x => aC₂ (fun _ => (1 : ℂ)) (fun _ => 0) c y x)
      ≤ 4 * c ^ 3 * (1 - y ^ 2) * √(Real.Gamma (7 / 2)) * (3 / 2 * c ^ 2 * (1 - y ^ 2)) ^ (-(7 / 4 : ℝ))
          * ((1 / σ₀) ^ (1 / 4 : ℝ) * Real.Gamma (1 / 4))
        + (10 * c ^ 2 + 2 * c) * √(Real.Gamma (5 / 2)) * (3 / 2 * c ^ 2 * (1 - y ^ 2)) ^ (-(5 / 4 : ℝ))
          * ((1 / σ₀) ^ (3 / 4 : ℝ) * Real.Gamma (3 / 4)) := by
  have hr : 0 < 1 - y ^ 2 := by nlinarith
  have hB : 0 < 3 / 2 * c ^ 2 * (1 - y ^ 2) := by positivity
  have h := lapStrip_le (c := c) (σ₀ := σ₀) (y := y) (M := M) (k := 1)
    (A := fun x => aC₂ (fun _ => (1 : ℂ)) (fun _ => 0) c y x) (B := 3 / 2 * c ^ 2 * (1 - y ^ 2))
    (C₁ := 4 * c ^ 3 * (1 - y ^ 2) * √(Real.Gamma (7 / 2))) (C₂ := (10 * c ^ 2 + 2 * c) * √(Real.Gamma (5 / 2)))
    (e₁ := 7 / 4) (e₂ := 5 / 4) hσ₀ hB (by norm_num) (by norm_num) ?_
  · exact h.trans (le_of_eq (by norm_num))
  · intro s hs
    have hb : 0 < 3 / 2 * c ^ 2 * (1 - y ^ 2) * s := by positivity
    have hg := sqrt_integral_gauss_le (M := (M : ℝ)) hb (α := 4 * c ^ 3 * (1 - y ^ 2)) (β := 10 * c ^ 2 + 2 * c)
      (by positivity) (by positivity) 3 2
      (f := fun x => ‖aC₂ (fun _ => (1 : ℂ)) (fun _ => 0) c y x‖ ^ 2 * Real.exp (2 * s * (qQ c (c ^ 2) y x).re))
      (fun x _ => by positivity)
      (fun x hx => (strip_atoms hc hy0 hy1.le hs.le (by linarith [hx.1] : (2 : ℝ) ≤ x)).1)
    refine hg.trans (le_of_eq ?_)
    norm_num

/-- The `A₃` strip form: `lapStrip₂(A₃) ≤ (1/2)(C₃B^{−9/4}σ₀^{−3/4}Γ(3/4) + C₄B^{−5/4}σ₀^{−7/4}Γ(7/4))`,
`C₃ = 16c⁴r²√Γ(9/2)`, `C₄ = 16c²√Γ(5/2)`. -/
theorem lapStrip_A₃_le {c σ₀ y : ℝ} (hc : 0 < c) (hσ₀ : 0 < σ₀) (hy0 : 0 ≤ y) (hy1 : y < 1) (M : ℕ) :
    lapStrip c σ₀ y M 2 (fun x => aC₃ (fun _ => (1 : ℂ)) c y x)
      ≤ 1 / 2 * (16 * c ^ 4 * (1 - y ^ 2) ^ 2 * √(Real.Gamma (9 / 2))
            * (3 / 2 * c ^ 2 * (1 - y ^ 2)) ^ (-(9 / 4 : ℝ)) * ((1 / σ₀) ^ (3 / 4 : ℝ) * Real.Gamma (3 / 4))
          + 16 * c ^ 2 * √(Real.Gamma (5 / 2)) * (3 / 2 * c ^ 2 * (1 - y ^ 2)) ^ (-(5 / 4 : ℝ))
            * ((1 / σ₀) ^ (7 / 4 : ℝ) * Real.Gamma (7 / 4))) := by
  have hr : 0 < 1 - y ^ 2 := by nlinarith
  have hB : 0 < 3 / 2 * c ^ 2 * (1 - y ^ 2) := by positivity
  have h := lapStrip_le (c := c) (σ₀ := σ₀) (y := y) (M := M) (k := 2)
    (A := fun x => aC₃ (fun _ => (1 : ℂ)) c y x) (B := 3 / 2 * c ^ 2 * (1 - y ^ 2))
    (C₁ := 16 * c ^ 4 * (1 - y ^ 2) ^ 2 * √(Real.Gamma (9 / 2))) (C₂ := 16 * c ^ 2 * √(Real.Gamma (5 / 2)))
    (e₁ := 9 / 4) (e₂ := 5 / 4) hσ₀ hB (by norm_num) (by norm_num) ?_
  · exact h.trans (le_of_eq (by norm_num))
  · intro s hs
    have hb : 0 < 3 / 2 * c ^ 2 * (1 - y ^ 2) * s := by positivity
    have hg := sqrt_integral_gauss_le (M := (M : ℝ)) hb (α := 16 * c ^ 4 * (1 - y ^ 2) ^ 2) (β := 16 * c ^ 2)
      (by positivity) (by positivity) 4 2
      (f := fun x => ‖aC₃ (fun _ => (1 : ℂ)) c y x‖ ^ 2 * Real.exp (2 * s * (qQ c (c ^ 2) y x).re))
      (fun x _ => by positivity)
      (fun x hx => (strip_atoms hc hy0 hy1.le hs.le (by linarith [hx.1] : (2 : ℝ) ≤ x)).2)
    refine hg.trans (le_of_eq ?_)
    norm_num

/-- The `r`-free strip constant `Λ(c, σ₀)`, `B₀ = (3/2)c²`. -/
def LamStrip (c σ₀ : ℝ) : ℝ :=
  4 * c ^ 3 * √(Real.Gamma (7 / 2)) * (3 / 2 * c ^ 2) ^ (-(7 / 4 : ℝ)) * ((1 / σ₀) ^ (1 / 4 : ℝ) * Real.Gamma (1 / 4))
    + (10 * c ^ 2 + 2 * c) * √(Real.Gamma (5 / 2)) * (3 / 2 * c ^ 2) ^ (-(5 / 4 : ℝ))
      * ((1 / σ₀) ^ (3 / 4 : ℝ) * Real.Gamma (3 / 4))
    + 1 / 2 * (16 * c ^ 4 * √(Real.Gamma (9 / 2)) * (3 / 2 * c ^ 2) ^ (-(9 / 4 : ℝ))
        * ((1 / σ₀) ^ (3 / 4 : ℝ) * Real.Gamma (3 / 4))
      + 16 * c ^ 2 * √(Real.Gamma (5 / 2)) * (3 / 2 * c ^ 2) ^ (-(5 / 4 : ℝ))
        * ((1 / σ₀) ^ (7 / 4 : ℝ) * Real.Gamma (7 / 4)))

/-- The strip rate `r_S(c, σ₀) = κ(16π²/9)Λ(c, σ₀)`. -/
def rStrip (c σ₀ : ℝ) : ℝ := √(2 * c / π) * (16 * π ^ 2 / 9) * LamStrip c σ₀

/-- `rⁿ(B₀r)^{−e} ≤ B₀^{−e}` for `0 < r ≤ 1`, `e ≤ n`. -/
theorem rpow_absorb {r B₀ e : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) (hB : 0 < B₀) (n : ℕ) (he : e ≤ n) :
    r ^ n * (B₀ * r) ^ (-e) ≤ B₀ ^ (-e) := by
  rw [Real.mul_rpow hB.le hr0.le, ← Real.rpow_natCast, mul_comm (B₀ ^ (-e)), ← mul_assoc, ← Real.rpow_add hr0]
  have : r ^ ((n : ℝ) + -e) ≤ 1 := Real.rpow_le_one hr0.le hr1 (by linarith)
  have hB' : 0 ≤ B₀ ^ (-e) := Real.rpow_nonneg hB.le _
  nlinarith

/-- **The strip weight absorbs the singularity**: for `t ∈ (1, 2)`,
`(1 − wF(t))|bulk₁_2(t)| ≤ (κ/2)(16π²/9)Λ(c, σ₀)√P`. -/
theorem weight_bulkOne_strip_le {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 0 < c) (hχ : Function.Injective χ) {σ₀ : ℝ} (hσ₀ : 0 < σ₀) (hσ : ∀ i, σ₀ ≤ c ^ 2 - χ i)
    {M : ℕ} (hM : 3 ≤ M) {t : ℝ} (ht : t ∈ Ioo 1 2) :
    (1 - wF t) * |bulkOne c χ g a M 2 t|
      ≤ √(2 * c / π) / 2 * (16 * π ^ 2 / 9) * LamStrip c σ₀ * √(∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2) := by
  set y := t / 2 with hydef
  set r := 1 - y ^ 2 with hrdef
  have hy0 : 0 ≤ y := by rw [hydef]; linarith [ht.1]
  have hy1 : y < 1 := by rw [hydef]; linarith [ht.2]
  have hr0 : 0 < r := by rw [hrdef]; nlinarith
  have hr1 : r ≤ 1 := by rw [hrdef]; nlinarith
  have hB₀ : 0 < 3 / 2 * c ^ 2 := by positivity
  have hW0 : 0 ≤ 1 - wF t := by linarith [(Cvs.L2a.FarFarBound.wF_bounds t).2.1]
  have hW : 1 - wF t ≤ 16 * π ^ 2 / 9 * r ^ 2 := by
    have h1 := Cvs.L2a.RampTopQuadratic.one_sub_wF_le t
    have h2 : 2 - t ≤ 4 / 3 * r := by rw [hrdef, hydef]; nlinarith [ht.1, ht.2]
    have h3 : (2 - t) ^ 2 ≤ (4 / 3 * r) ^ 2 := pow_le_pow_left₀ (by linarith [ht.2]) h2 2
    have hπ : 0 ≤ π ^ 2 := sq_nonneg π
    nlinarith
  have hbulk := abs_bulkOne_strip_le a hg hg₁ hg₂c hang hc hχ hσ₀ hσ hM ht
  rw [← hydef] at hbulk
  have l1 := lapStrip_A₂_le hc hσ₀ hy0 hy1 M
  have l2 := lapStrip_A₃_le hc hσ₀ hy0 hy1 M
  rw [← hrdef] at l1 l2
  have hP := Real.sqrt_nonneg (∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2)
  have hκ : 0 ≤ √(2 * c / π) / 2 := by positivity
  have hl1 : 0 ≤ lapStrip c σ₀ y M 1 (fun x => aC₂ (fun _ => (1 : ℂ)) (fun _ => 0) c y x) := by
    unfold lapStrip
    refine mul_nonneg (by positivity) (setIntegral_nonneg measurableSet_Ioi fun s hs => ?_)
    have : (0 : ℝ) < s := hs
    positivity
  have hl2 : 0 ≤ lapStrip c σ₀ y M 2 (fun x => aC₃ (fun _ => (1 : ℂ)) c y x) := by
    unfold lapStrip
    refine mul_nonneg (by positivity) (setIntegral_nonneg measurableSet_Ioi fun s hs => ?_)
    have : (0 : ℝ) < s := hs
    positivity
  set L1 := (1 / σ₀) ^ (1 / 4 : ℝ) * Real.Gamma (1 / 4)
  set L2 := (1 / σ₀) ^ (3 / 4 : ℝ) * Real.Gamma (3 / 4)
  set L4 := (1 / σ₀) ^ (7 / 4 : ℝ) * Real.Gamma (7 / 4)
  have hL1 : 0 ≤ L1 := by positivity
  have hL2 : 0 ≤ L2 := by positivity
  have hL4 : 0 ≤ L4 := by positivity
  have a1 := rpow_absorb hr0 hr1 hB₀ 3 (e := 7 / 4) (by norm_num)
  have a2 := rpow_absorb hr0 hr1 hB₀ 2 (e := 5 / 4) (by norm_num)
  have a3 := rpow_absorb hr0 hr1 hB₀ 4 (e := 9 / 4) (by norm_num)
  have key : r ^ 2 * (lapStrip c σ₀ y M 1 (fun x => aC₂ (fun _ => (1 : ℂ)) (fun _ => 0) c y x)
      + lapStrip c σ₀ y M 2 (fun x => aC₃ (fun _ => (1 : ℂ)) c y x)) ≤ LamStrip c σ₀ := by
    have hr2 : 0 ≤ r ^ 2 := sq_nonneg r
    calc r ^ 2 * (lapStrip c σ₀ y M 1 (fun x => aC₂ (fun _ => (1 : ℂ)) (fun _ => 0) c y x)
          + lapStrip c σ₀ y M 2 (fun x => aC₃ (fun _ => (1 : ℂ)) c y x))
        ≤ r ^ 2 * ((4 * c ^ 3 * r * √(Real.Gamma (7 / 2)) * (3 / 2 * c ^ 2 * r) ^ (-(7 / 4 : ℝ)) * L1
            + (10 * c ^ 2 + 2 * c) * √(Real.Gamma (5 / 2)) * (3 / 2 * c ^ 2 * r) ^ (-(5 / 4 : ℝ)) * L2)
          + 1 / 2 * (16 * c ^ 4 * r ^ 2 * √(Real.Gamma (9 / 2)) * (3 / 2 * c ^ 2 * r) ^ (-(9 / 4 : ℝ)) * L2
            + 16 * c ^ 2 * √(Real.Gamma (5 / 2)) * (3 / 2 * c ^ 2 * r) ^ (-(5 / 4 : ℝ)) * L4)) :=
          mul_le_mul_of_nonneg_left (add_le_add l1 l2) hr2
      _ = 4 * c ^ 3 * √(Real.Gamma (7 / 2)) * L1 * (r ^ 3 * (3 / 2 * c ^ 2 * r) ^ (-(7 / 4 : ℝ)))
          + (10 * c ^ 2 + 2 * c) * √(Real.Gamma (5 / 2)) * L2 * (r ^ 2 * (3 / 2 * c ^ 2 * r) ^ (-(5 / 4 : ℝ)))
          + 1 / 2 * (16 * c ^ 4 * √(Real.Gamma (9 / 2)) * L2 * (r ^ 4 * (3 / 2 * c ^ 2 * r) ^ (-(9 / 4 : ℝ)))
            + 16 * c ^ 2 * √(Real.Gamma (5 / 2)) * L4 * (r ^ 2 * (3 / 2 * c ^ 2 * r) ^ (-(5 / 4 : ℝ)))) := by ring
      _ ≤ 4 * c ^ 3 * √(Real.Gamma (7 / 2)) * L1 * (3 / 2 * c ^ 2) ^ (-(7 / 4 : ℝ))
          + (10 * c ^ 2 + 2 * c) * √(Real.Gamma (5 / 2)) * L2 * (3 / 2 * c ^ 2) ^ (-(5 / 4 : ℝ))
          + 1 / 2 * (16 * c ^ 4 * √(Real.Gamma (9 / 2)) * L2 * (3 / 2 * c ^ 2) ^ (-(9 / 4 : ℝ))
            + 16 * c ^ 2 * √(Real.Gamma (5 / 2)) * L4 * (3 / 2 * c ^ 2) ^ (-(5 / 4 : ℝ))) := by
          gcongr
      _ = LamStrip c σ₀ := by unfold LamStrip; ring
  calc (1 - wF t) * |bulkOne c χ g a M 2 t|
      ≤ (16 * π ^ 2 / 9 * r ^ 2) * (√(2 * c / π) / 2
          * (lapStrip c σ₀ y M 1 (fun x => aC₂ (fun _ => (1 : ℂ)) (fun _ => 0) c y x)
            + lapStrip c σ₀ y M 2 (fun x => aC₃ (fun _ => (1 : ℂ)) c y x))
          * √(∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2)) :=
        mul_le_mul hW hbulk (abs_nonneg _) (by positivity)
    _ = √(2 * c / π) / 2 * (16 * π ^ 2 / 9) * (r ^ 2
          * (lapStrip c σ₀ y M 1 (fun x => aC₂ (fun _ => (1 : ℂ)) (fun _ => 0) c y x)
            + lapStrip c σ₀ y M 2 (fun x => aC₃ (fun _ => (1 : ℂ)) c y x)))
          * √(∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2) := by ring
    _ ≤ _ := by gcongr

/-- **The `m = 2` strip**: `|near₂| ≤ r_S(c, σ₀)·P`, uniformly in `M`, for `σᵢ² ≥ σ₀ > 0`. -/
theorem abs_DOneNear_two_le {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 0 < c) (hχ : Function.Injective χ) (hχc : ∀ i, χ i < c ^ 2) {σ₀ : ℝ} (hσ₀ : 0 < σ₀)
    (hσ : ∀ i, σ₀ ≤ c ^ 2 - χ i) {M : ℕ} (hM : 3 ≤ M) :
    |DOneNear c χ g a M 2| ≤ rStrip c σ₀ * ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2 := by
  set Φ : ℝ → ℝ := fun ξ => ∑ i, a i * psi c (g i) ξ with hΦdef
  set P := ∫ x in Ioi 1, Φ x ^ 2 with hPdef
  have hΦ2 : MemLp Φ 2 (volume.restrict (Ioi 1)) :=
    memLp_finsetSum _ fun i _ =>
      (Cvs.Prolate.RungExactOrthogonality.memLp_psi (hg i) (hg₁ i) (hg₂c i) (hang i) hc).const_mul (a i)
  have hsub : volume.restrict (Ioo (1 : ℝ) 2) ≤ volume.restrict (Ioi 1) :=
    Measure.restrict_mono Ioo_subset_Ioi_self le_rfl
  have hΦN := hΦ2.mono_measure hsub
  have hBN := (dil_split_mid (M := M) (m := 2) (δ := 1 / 2) a hg hg₁ hg₂c hang hc hχc le_rfl (by omega)
    (by norm_num) le_rfl).1.mono_measure hsub
  have : IsFiniteMeasure (volume.restrict (Ioo (1 : ℝ) 2)) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Ioo]; exact ENNReal.ofReal_lt_top⟩
  set C := √(2 * c / π) / 2 * (16 * π ^ 2 / 9) * LamStrip c σ₀ * √P with hC
  have hLam : 0 ≤ LamStrip c σ₀ := by unfold LamStrip; positivity
  have hC0 : 0 ≤ C := by positivity
  have hpt : ∀ t ∈ Ioo (1 : ℝ) 2, |(1 - wF t) * Φ t * bulkOne c χ g a M 2 t| ≤ C * (1 * |Φ t|) := fun t ht => by
    have hb := weight_bulkOne_strip_le a hg hg₁ hg₂c hang hc hχ hσ₀ hσ hM ht
    have hW0 : 0 ≤ 1 - wF t := by linarith [(Cvs.L2a.FarFarBound.wF_bounds t).2.1]
    rw [abs_mul, abs_mul, abs_of_nonneg hW0]
    calc (1 - wF t) * |Φ t| * |bulkOne c χ g a M 2 t| = |Φ t| * ((1 - wF t) * |bulkOne c χ g a M 2 t|) := by ring
      _ ≤ |Φ t| * C := mul_le_mul_of_nonneg_left hb (abs_nonneg _)
      _ = C * (1 * |Φ t|) := by ring
  have hint1 : Integrable (fun t => |(1 - wF t) * Φ t * bulkOne c χ g a M 2 t|)
      (volume.restrict (Ioo (1 : ℝ) 2)) := by
    have : Integrable (fun t => (1 - wF t) * (Φ t * bulkOne c χ g a M 2 t)) (volume.restrict (Ioo (1 : ℝ) 2)) :=
      (hΦN.integrable_mul hBN).bdd_mul (c := 1) (continuous_const.sub continuous_wF.1).aestronglyMeasurable
        (Eventually.of_forall fun t => by
          obtain ⟨h0, h1, -, -⟩ := Cvs.L2a.FarFarBound.wF_bounds t
          rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith)
    refine this.abs.congr (Eventually.of_forall fun t => ?_)
    simp only; ring_nf
  have hone : MemLp (fun _ : ℝ => (1 : ℝ)) 2 (volume.restrict (Ioo (1 : ℝ) 2)) := memLp_const 1
  have hint2 : Integrable (fun t => C * (1 * |Φ t|)) (volume.restrict (Ioo (1 : ℝ) 2)) :=
    (hone.integrable_mul hΦN.abs).const_mul C
  have hCS := Cvs.L2a.FarFarBound.integral_mul_abs_le (μ := volume.restrict (Ioo (1 : ℝ) 2)) (f := fun _ => (1 : ℝ))
    (fun _ => zero_le_one) hone hΦN
  have hPN : ∫ t in Ioo (1 : ℝ) 2, Φ t ^ 2 ≤ P :=
    setIntegral_mono_set ((memLp_two_iff_integrable_sq hΦ2.aestronglyMeasurable).1 hΦ2)
      (Eventually.of_forall fun t => sq_nonneg _) (Eventually.of_forall Ioo_subset_Ioi_self)
  have hone1 : ∫ _ in Ioo (1 : ℝ) 2, (1 : ℝ) ^ 2 = 1 := by
    simp; norm_num
  have hP0 : 0 ≤ P := integral_nonneg fun _ => sq_nonneg _
  unfold DOneNear
  rw [abs_mul, abs_neg, abs_two]
  have key : |∫ t in Ioo (1 : ℝ) 2, (1 - wF t) * Φ t * bulkOne c χ g a M 2 t| ≤ rStrip c σ₀ / 2 * P := by
    calc |∫ t in Ioo (1 : ℝ) 2, (1 - wF t) * Φ t * bulkOne c χ g a M 2 t|
        ≤ ∫ t in Ioo (1 : ℝ) 2, |(1 - wF t) * Φ t * bulkOne c χ g a M 2 t| := abs_integral_le_integral_abs
      _ ≤ ∫ t in Ioo (1 : ℝ) 2, C * (1 * |Φ t|) := setIntegral_mono_on hint1 hint2 measurableSet_Ioo hpt
      _ = C * ∫ t in Ioo (1 : ℝ) 2, 1 * |Φ t| := integral_const_mul _ _
      _ ≤ C * (√(∫ _ in Ioo (1 : ℝ) 2, (1 : ℝ) ^ 2) * √(∫ t in Ioo (1 : ℝ) 2, Φ t ^ 2)) :=
          mul_le_mul_of_nonneg_left hCS hC0
      _ ≤ C * (1 * √P) := by rw [hone1, Real.sqrt_one]; gcongr
      _ = √(2 * c / π) / 2 * (16 * π ^ 2 / 9) * LamStrip c σ₀ * (√P * √P) := by rw [hC]; ring
      _ = rStrip c σ₀ / 2 * P := by rw [Real.mul_self_sqrt hP0]; unfold rStrip; ring
  linarith

/-- **The three parts of `Dil`, closed**: `Dbot + Dmid + Dtop ≥ (−2Σ_m∫ū𝔅_m + Σ_m C_m + 𝒞_a) − (r₁ + r_S)P`. -/
theorem corners_add_mid_ge_closed {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 0 < c) (hχ : Function.Injective χ) (hχ0 : ∀ i, 0 ≤ χ i) {σ₀ : ℝ} (hσ₀ : 0 < σ₀)
    (hσ : ∀ i, σ₀ ≤ c ^ 2 - χ i) {M : ℕ} (hM : 3 ≤ M) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2) :
    (-2 * ∑ m ∈ Finset.Icc 2 (M - 1),
          (∫ t in Ioi 1, ubar (fun ξ => ∑ i, a i * psi c (g i) ξ) wF M t * frakB c χ g a m t)
        + ∑ m ∈ Finset.Icc 2 (M - 1), cTop c χ g a M m + calCa c χ g a M)
        - (rOne c + rStrip c σ₀) * (∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2)
      ≤ Cvs.L2a.CornerSplitSqrtFloor.DbotG Cvs.Upstream.QuinticSmoothStep.S c (fun ξ => ∑ i, a i * psi c (g i) ξ) wF M δ
        + Cvs.L2a.CornerSplitSqrtFloor.DmidG Cvs.Upstream.QuinticSmoothStep.S c (fun ξ => ∑ i, a i * psi c (g i) ξ) wF M δ
        + Cvs.L2a.CornerSplitSqrtFloor.DtopG Cvs.Upstream.QuinticSmoothStep.S c (fun ξ => ∑ i, a i * psi c (g i) ξ) wF M δ := by
  have hχc : ∀ i, χ i < c ^ 2 := fun i => by linarith [hσ i]
  have h := corners_add_mid_ge a hg hg₁ hg₂c hang hc hχ hχ0 hχc hM hδ0 hδ1
  have hs := abs_DOneNear_two_le a hg hg₁ hg₂c hang hc hχ hχc hσ₀ hσ hM
  linarith

/-! ### `r_S(c, s₀c) = O(c^{−1/4})` -/

/-- The rate constants of the strip at `σ₀ = s₀c`. -/
def KS₁ (s₀ : ℝ) : ℝ :=
  √(2 / π) * (16 * π ^ 2 / 9) * (4 * √(Real.Gamma (7 / 2)) * (3 / 2 : ℝ) ^ (-(7 / 4 : ℝ))
    * ((1 / s₀) ^ (1 / 4 : ℝ) * Real.Gamma (1 / 4)))

def KS₂ (s₀ : ℝ) : ℝ :=
  √(2 / π) * (16 * π ^ 2 / 9) * (10 * √(Real.Gamma (5 / 2)) * (3 / 2 : ℝ) ^ (-(5 / 4 : ℝ))
    * ((1 / s₀) ^ (3 / 4 : ℝ) * Real.Gamma (3 / 4))
    + 8 * √(Real.Gamma (9 / 2)) * (3 / 2 : ℝ) ^ (-(9 / 4 : ℝ)) * ((1 / s₀) ^ (3 / 4 : ℝ) * Real.Gamma (3 / 4)))

def KS₃ (s₀ : ℝ) : ℝ :=
  √(2 / π) * (16 * π ^ 2 / 9) * (2 * √(Real.Gamma (5 / 2)) * (3 / 2 : ℝ) ^ (-(5 / 4 : ℝ))
    * ((1 / s₀) ^ (3 / 4 : ℝ) * Real.Gamma (3 / 4))
    + 8 * √(Real.Gamma (5 / 2)) * (3 / 2 : ℝ) ^ (-(5 / 4 : ℝ)) * ((1 / s₀) ^ (7 / 4 : ℝ) * Real.Gamma (7 / 4)))

/-- **The strip rate in powers of `c`**: `r_S(c, s₀c) = K₁c^{−1/4} + K₂c^{−3/4} + K₃c^{−7/4}`. -/
theorem rStrip_eq {c s₀ : ℝ} (hc : 0 < c) (hs₀ : 0 < s₀) :
    rStrip c (s₀ * c) = KS₁ s₀ * c ^ (-(1 / 4 : ℝ)) + KS₂ s₀ * c ^ (-(3 / 4 : ℝ)) + KS₃ s₀ * c ^ (-(7 / 4 : ℝ)) := by
  have hsq : √(2 * c / π) = √(2 / π) * c ^ (1 / 2 : ℝ) := by
    rw [show 2 * c / π = 2 / π * c by ring, Real.sqrt_mul (by positivity), Real.sqrt_eq_rpow c]
  have hB : ∀ e : ℝ, (3 / 2 * c ^ 2) ^ (-e) = (3 / 2 : ℝ) ^ (-e) * c ^ (-(2 * e)) := fun e => by
    rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hc.le]
    congr 2; push_cast; ring
  have hσ : ∀ e : ℝ, (1 / (s₀ * c)) ^ e = (1 / s₀) ^ e * c ^ (-e) := fun e => by
    rw [show 1 / (s₀ * c) = 1 / s₀ * (1 / c) by field_simp, Real.mul_rpow (by positivity) (by positivity),
      one_div c, Real.inv_rpow hc.le, Real.rpow_neg hc.le]
  have hn : ∀ n : ℕ, c ^ n = c ^ (n : ℝ) := fun n => (Real.rpow_natCast c n).symm
  have hadd : ∀ a b : ℝ, c ^ a * c ^ b = c ^ (a + b) := fun a b => (Real.rpow_add hc a b).symm
  unfold rStrip LamStrip KS₁ KS₂ KS₃
  rw [hsq, hB, hB, hB, hσ, hσ, hσ, hn 3, hn 2, hn 4]
  have e1 : c ^ (1 / 2 : ℝ) * c ^ ((3 : ℕ) : ℝ) * c ^ (-(2 * (7 / 4 : ℝ))) * c ^ (-(1 / 4 : ℝ))
      = c ^ (-(1 / 4 : ℝ)) := by
    rw [hadd, hadd, hadd]; congr 1; push_cast; ring
  have e2 : c ^ (1 / 2 : ℝ) * c ^ ((2 : ℕ) : ℝ) * c ^ (-(2 * (5 / 4 : ℝ))) * c ^ (-(3 / 4 : ℝ))
      = c ^ (-(3 / 4 : ℝ)) := by
    rw [hadd, hadd, hadd]; congr 1; push_cast; ring
  have e2' : c ^ (1 / 2 : ℝ) * c * c ^ (-(2 * (5 / 4 : ℝ))) * c ^ (-(3 / 4 : ℝ)) = c ^ (-(7 / 4 : ℝ)) := by
    have h1 : c = c ^ (1 : ℝ) := (Real.rpow_one c).symm
    calc c ^ (1 / 2 : ℝ) * c * c ^ (-(2 * (5 / 4 : ℝ))) * c ^ (-(3 / 4 : ℝ))
        = c ^ (1 / 2 : ℝ) * c ^ (1 : ℝ) * c ^ (-(2 * (5 / 4 : ℝ))) * c ^ (-(3 / 4 : ℝ)) := by
          rw [Real.rpow_one]
      _ = c ^ (-(7 / 4 : ℝ)) := by rw [hadd, hadd, hadd]; congr 1; ring
  have e3 : c ^ (1 / 2 : ℝ) * c ^ ((4 : ℕ) : ℝ) * c ^ (-(2 * (9 / 4 : ℝ))) * c ^ (-(3 / 4 : ℝ))
      = c ^ (-(3 / 4 : ℝ)) := by
    rw [hadd, hadd, hadd]; congr 1; push_cast; ring
  have e4 : c ^ (1 / 2 : ℝ) * c ^ ((2 : ℕ) : ℝ) * c ^ (-(2 * (5 / 4 : ℝ))) * c ^ (-(7 / 4 : ℝ))
      = c ^ (-(7 / 4 : ℝ)) := by
    rw [hadd, hadd, hadd]; congr 1; push_cast; ring
  linear_combination
    (√(2 / π) * (16 * π ^ 2 / 9) * (4 * √(Real.Gamma (7 / 2)) * (3 / 2 : ℝ) ^ (-(7 / 4 : ℝ))
      * ((1 / s₀) ^ (1 / 4 : ℝ) * Real.Gamma (1 / 4)))) * e1
    + (√(2 / π) * (16 * π ^ 2 / 9) * (10 * √(Real.Gamma (5 / 2)) * (3 / 2 : ℝ) ^ (-(5 / 4 : ℝ))
      * ((1 / s₀) ^ (3 / 4 : ℝ) * Real.Gamma (3 / 4)))) * e2
    + (√(2 / π) * (16 * π ^ 2 / 9) * (2 * √(Real.Gamma (5 / 2)) * (3 / 2 : ℝ) ^ (-(5 / 4 : ℝ))
      * ((1 / s₀) ^ (3 / 4 : ℝ) * Real.Gamma (3 / 4)))) * e2'
    + (√(2 / π) * (16 * π ^ 2 / 9) * (8 * √(Real.Gamma (9 / 2)) * (3 / 2 : ℝ) ^ (-(9 / 4 : ℝ))
      * ((1 / s₀) ^ (3 / 4 : ℝ) * Real.Gamma (3 / 4)))) * e3
    + (√(2 / π) * (16 * π ^ 2 / 9) * (8 * √(Real.Gamma (5 / 2)) * (3 / 2 : ℝ) ^ (-(5 / 4 : ℝ))
      * ((1 / s₀) ^ (7 / 4 : ℝ) * Real.Gamma (7 / 4)))) * e4

end Cvs.L2a.MiddlePartQStep
