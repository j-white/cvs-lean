import Mathlib
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.Approximant.SpineCouplingTailPairing
import Cvs.Approximant.SpineSubspace
import Cvs.Prolate.EntireRungProlateEquation
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.Mellin.FrozenRootResidual
import Cvs.Prolate.Mellin.RayTransformEdgeSum
import Cvs.Prolate.Mellin.RightEdgeIntegralPart
import Cvs.Prolate.Mellin.RightEdgePoissonSplit
import Cvs.Prolate.Mellin.RungTransformUnitCircle
import Cvs.Prolate.Mellin.RungUnitCircleLaw
import Cvs.Prolate.Mellin.RungWindowLawRightEdge
import Cvs.Prolate.Mellin.UnitCircleMellinEdgeBound
import Cvs.Prolate.Mellin.UnitCircleMellinSolution
import Cvs.Prolate.RungProfileEntireExtension
import Cvs.Prolate.RungWindowProfileCells
import Cvs.Route.Visibility.ExtPairingRatesSubpoly
import Cvs.Route.Visibility.ExteriorFactorMTwo

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The right-edge law is the alias law, and the dual profile meets it

With `Q = H − F − G_j/(2x)` the Euler–Maclaurin remainder of the right-edge sum (Cvs.Prolate.Mellin.RightEdgePoissonSplit: `Q = −G_j(0)/(2x) + Σ W_m`),
`T_H = T_Q + T_F + A/(2x)` and Cvs.Prolate.Mellin.RightEdgeIntegralPart, Cvs.Prolate.Mellin.RungUnitCircleLaw bound the last two by `4e⁶E_j/√x`, so `EdgeLawSum ↔ AliasLaw`.
The dual profile `Ĝ = ψ_{G_j} = μ_{4j}H_{4j} − α_jμ₀H₀` solves the prolate equation rung by rung, so Cvs.Prolate.Mellin.UnitCircleMellinEdgeBound gives
`g‖T_{ζ⁻¹Ĝ(ζ⁻¹)}(σ + ig)‖ ≤ 4e⁶(|μ_{4j}h_{4j}(1)| + |α_jμ₀h₀(1)|) ≤ 4e⁶E_j/√x`: the bound `AliasLaw` asks of `T_Q`.
-/

noncomputable section

open Real Set MeasureTheory Filter Complex Topology ComplexConjugate
open Cvs.Prolate.RungProfileEntireExtension (GC psiC)
open Cvs.Prolate.RungWindowProfileCells (Gr)
open Cvs.Prolate.Mellin.RungTransformUnitCircle (Aw Bw)
open Cvs.Prolate.Mellin.RayTransformEdgeSum (edgeSum rayT)
open Cvs.Prolate.Mellin.RightEdgeIntegralPart (intG)
open Cvs.Prolate.EvenRungsByIndex (rung muR lamR lev IsLevelIdx)
open Cvs.Prolate.EntireRungProlateEquation (Hk)
open Cvs.Prolate.Mellin.FrozenRootResidual (pm)
open Cvs.Route.Visibility.ExtPairingRatesSubpoly (SubPoly)

namespace Cvs.Prolate.Mellin.RightEdgeAliasLaw
open Cvs.ZeroCounting

/-! ### The alias law -/

/-- The Euler–Maclaurin remainder `Q(ζ) = H(ζ) − F(ζ) − G_j(ζ)/(2x)` of the right-edge sum. -/
def aliasQ (x j : ℕ) (ζ : ℂ) : ℂ := edgeSum x j ζ - intG x j ζ - GC x j ζ / (2 * x)

/-- `Q = −G_j(0)/(2x) + Σ_{m ≥ 0} W_m`. -/
theorem hasSum_aliasQ {x j : ℕ} (hx : 80 ≤ 2 * π * x) (hj : j < x) (ζ : ℂ) :
    HasSum (fun m => Cvs.Prolate.Mellin.RightEdgePoissonSplit.aliasW x j m ζ) (aliasQ x j ζ + GC x j 0 / (2 * x)) := by
  have h := Cvs.Prolate.Mellin.RightEdgePoissonSplit.hasSum_aliasW hx hj ζ
  convert h using 1
  unfold aliasQ; ring

/-- **The alias law**: some subpolynomial `C` has, at all large `x`, for every rung, `|σ| ≤ 1` and `g ≥ 8πx`,
`g‖T_Q(σ + ig)‖ ≤ C(x)E_j/√x`. -/
def AliasLaw : Prop :=
  ∃ C : ℕ → ℝ, SubPoly C ∧ ∀ᶠ x : ℕ in atTop, ∀ j : Cvs.Approximant.SpineSubspace.SF x, ∀ σ : ℝ, |σ| ≤ 1 → ∀ g : ℝ, 8 * π * x ≤ g →
    g * ‖rayT (aliasQ x j) (σ + g * I)‖ ≤ C x * Cvs.Prolate.Mellin.RungWindowLawRightEdge.edgeE x j / √(x : ℝ)

/-- `T_H = T_Q + T_F + A/(2x)` on `Im w > 0`. -/
theorem rayT_edgeSum_eq {x j : ℕ} (hx : 80 ≤ 2 * π * x) (hj : j < x) {w : ℂ} (hw : 0 < w.im) :
    rayT (edgeSum x j) w = rayT (aliasQ x j) w + rayT (intG x j) w + Aw x j w / (2 * x) := by
  have hH := (Cvs.Prolate.Mellin.RayTransformEdgeSum.differentiable_edgeSum hx hj).continuous
  have hF := (Cvs.Prolate.Mellin.RightEdgeIntegralPart.differentiable_intG hx hj).continuous
  have hG := (Cvs.Prolate.RungProfileEntireExtension.differentiable_GC hx hj).continuous
  have hQ : Continuous (aliasQ x j) := by unfold aliasQ; fun_prop
  have hG2 : Continuous fun ζ => GC x j ζ / (2 * x) := by fun_prop
  rw [Cvs.Prolate.Mellin.RayTransformEdgeSum.Aw_eq_rayT]
  unfold rayT
  have hQi := Cvs.Prolate.Mellin.RayTransformEdgeSum.integrableOn_integrand hQ hw
  have hFi := Cvs.Prolate.Mellin.RayTransformEdgeSum.integrableOn_integrand hF hw
  have hGi := (Cvs.Prolate.Mellin.RayTransformEdgeSum.integrableOn_integrand hG hw).div_const (2 * (x : ℂ))
  calc ∫ s in Ioi (0 : ℝ), edgeSum x j (Complex.exp (-(s * I))) * Complex.exp (-(s * I / 2))
        * Complex.exp (w * (s * I))
      = ∫ s in Ioi (0 : ℝ), (aliasQ x j (Complex.exp (-(s * I))) * Complex.exp (-(s * I / 2))
          * Complex.exp (w * (s * I)) + intG x j (Complex.exp (-(s * I))) * Complex.exp (-(s * I / 2))
          * Complex.exp (w * (s * I))) + GC x j (Complex.exp (-(s * I))) * Complex.exp (-(s * I / 2))
          * Complex.exp (w * (s * I)) / (2 * x) := by
        refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
        simp only [aliasQ]
        ring
    _ = _ := (integral_add (hQi.add hFi) hGi).trans (by
        congr 1
        · exact integral_add hQi hFi
        · exact integral_div _ _)

/-- `|g‖T_H‖ − g‖T_Q‖| ≤ 4e⁶E_j/√x` beyond `8πx`. -/
theorem abs_sub_le {x j : ℕ} (hx : 80 ≤ 2 * π * x) (hj : j < x) {σ : ℝ} (hσ : |σ| ≤ 1) {g : ℝ}
    (hg : 8 * π * x ≤ g) :
    |g * ‖Bw x j (σ + g * I)‖ - g * ‖rayT (aliasQ x j) (σ + g * I)‖|
      ≤ 4 * Real.exp 6 * Cvs.Prolate.Mellin.RungWindowLawRightEdge.edgeE x j / √(x : ℝ) := by
  have hx0 : (0 : ℝ) < x := Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx
  have hx1 : (1 : ℝ) ≤ x := by
    have : (1 : ℕ) ≤ x := by exact_mod_cast hx0
    exact_mod_cast this
  have hg0 : 0 < g := lt_of_lt_of_le (by positivity) hg
  have hwi : 0 < ((σ : ℂ) + g * I).im := by simp [hg0]
  have hF := Cvs.Prolate.Mellin.RightEdgeIntegralPart.g_norm_rayT_intG_le hx hj hσ hg
  have hA := Cvs.Prolate.Mellin.RungUnitCircleLaw.g_norm_Aw_le hx hj hσ hg
  have hE0 := Cvs.Prolate.Mellin.RungWindowLawRightEdge.edgeE_nonneg x j
  set E := Cvs.Prolate.Mellin.RungWindowLawRightEdge.edgeE x j
  have hAE : g * ‖Aw x j (σ + g * I)‖ ≤ 4 * Real.exp 6 * E := by unfold E Cvs.Prolate.Mellin.RungWindowLawRightEdge.edgeE; linarith
  rw [Cvs.Prolate.Mellin.RayTransformEdgeSum.Bw_eq_rayT, rayT_edgeSum_eq hx hj hwi]
  set Q := rayT (aliasQ x j) (σ + g * I)
  set Fv := rayT (intG x j) (σ + g * I)
  set Av := Aw x j (σ + g * I)
  have htri : |g * ‖Q + Fv + Av / (2 * x)‖ - g * ‖Q‖| ≤ g * ‖Fv‖ + g * ‖Av‖ / (2 * x) := by
    rw [← mul_sub, abs_mul, abs_of_pos hg0]
    have : |‖Q + Fv + Av / (2 * x)‖ - ‖Q‖| ≤ ‖Fv + Av / (2 * x)‖ := by
      rw [add_assoc]
      have := abs_norm_sub_norm_le (Q + (Fv + Av / (2 * x))) Q
      rwa [add_sub_cancel_left] at this
    have h2 : ‖Fv + Av / (2 * x)‖ ≤ ‖Fv‖ + ‖Av‖ / (2 * x) := by
      refine (norm_add_le _ _).trans (le_of_eq ?_)
      rw [norm_div, show ‖(2 * (x : ℂ))‖ = 2 * x by
        rw [norm_mul, Complex.norm_ofNat, Complex.norm_natCast]]
    calc g * |‖Q + Fv + Av / (2 * x)‖ - ‖Q‖| ≤ g * (‖Fv‖ + ‖Av‖ / (2 * x)) :=
          mul_le_mul_of_nonneg_left (this.trans h2) hg0.le
      _ = g * ‖Fv‖ + g * ‖Av‖ / (2 * x) := by ring
  refine htri.trans ?_
  have hT : 8 * π * x ≤ g := hg
  have hgx : 4 * Real.exp 6 * E / g ≤ 4 * Real.exp 6 * E / (8 * x) := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    nlinarith [Real.pi_gt_three]
  have hsq : √(x : ℝ) ≤ x := by
    rw [Real.sqrt_le_left (by positivity)]; nlinarith
  have hs0 : 0 < √(x : ℝ) := Real.sqrt_pos.2 hx0
  have hk : 4 * Real.exp 6 * E / (8 * x) + 4 * Real.exp 6 * E / (2 * x) ≤ 4 * Real.exp 6 * E / √(x : ℝ) := by
    have hK : 0 ≤ 4 * Real.exp 6 * E := by positivity
    have e : 4 * Real.exp 6 * E / (8 * x) + 4 * Real.exp 6 * E / (2 * x) = 4 * Real.exp 6 * E * (5 / 8) / x := by
      field_simp; ring
    rw [e, div_le_div_iff₀ hx0 hs0]
    nlinarith
  have hA2 : g * ‖Av‖ / (2 * x) ≤ 4 * Real.exp 6 * E / (2 * x) :=
    div_le_div_of_nonneg_right hAE (by positivity)
  linarith

/-- **The right-edge law is the alias law**. -/
theorem edgeLawSum_iff_aliasLaw : Cvs.Prolate.Mellin.RungWindowLawRightEdge.EdgeLawSum ↔ AliasLaw := by
  constructor
  · rintro ⟨C, hC, hB⟩
    refine ⟨fun x => C x + 4 * Real.exp 6, hC.add (Cvs.Route.Visibility.ExtPairingRatesSubpoly.subPoly_const _), ?_⟩
    filter_upwards [hB, Cvs.Route.Visibility.ExteriorFactorMTwo.eventually_scale] with x hBx hx j σ hσ g hg
    have hj : (j : ℕ) < x := Cvs.Approximant.SpineSubspace.SF_lt x j j.2
    have h1 := hBx j σ hσ g hg
    have h2 := (abs_le.1 (abs_sub_le hx hj hσ hg)).1
    have e : (C x + 4 * Real.exp 6) * Cvs.Prolate.Mellin.RungWindowLawRightEdge.edgeE x j / √(x : ℝ)
        = C x * Cvs.Prolate.Mellin.RungWindowLawRightEdge.edgeE x j / √(x : ℝ) + 4 * Real.exp 6 * Cvs.Prolate.Mellin.RungWindowLawRightEdge.edgeE x j / √(x : ℝ) := by ring
    rw [e]; linarith
  · rintro ⟨C, hC, hQ⟩
    refine ⟨fun x => C x + 4 * Real.exp 6, hC.add (Cvs.Route.Visibility.ExtPairingRatesSubpoly.subPoly_const _), ?_⟩
    filter_upwards [hQ, Cvs.Route.Visibility.ExteriorFactorMTwo.eventually_scale] with x hQx hx j σ hσ g hg
    have hj : (j : ℕ) < x := Cvs.Approximant.SpineSubspace.SF_lt x j j.2
    have h1 := hQx j σ hσ g hg
    have h2 := (abs_le.1 (abs_sub_le hx hj hσ hg)).2
    have e : (C x + 4 * Real.exp 6) * Cvs.Prolate.Mellin.RungWindowLawRightEdge.edgeE x j / √(x : ℝ)
        = C x * Cvs.Prolate.Mellin.RungWindowLawRightEdge.edgeE x j / √(x : ℝ) + 4 * Real.exp 6 * Cvs.Prolate.Mellin.RungWindowLawRightEdge.edgeE x j / √(x : ℝ) := by ring
    rw [e]; linarith

/-! ### The dual profile -/

/-- `ψ_g(z̄) = conj ψ_g(z)`. -/
theorem psiC_conj (c : ℝ) (g : ℝ → ℝ) (z : ℂ) : psiC c g (conj z) = conj (psiC c g z) := by
  unfold psiC
  rw [intervalIntegral.integral_of_le (by norm_num), intervalIntegral.integral_of_le (by norm_num),
    ← integral_conj]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only
  rw [map_mul, Complex.conj_ofReal, ← Complex.cos_conj, map_mul, map_mul, Complex.conj_ofReal,
    Complex.conj_ofReal]

/-- The dual profile `Ĝ = ψ_{G_j}` as an entire function. -/
def dualG (x j : ℕ) (z : ℂ) : ℂ := psiC (2 * π * x) (Gr x j) z

/-- `Ĝ = μ_{4j}H_{4j} − α_jμ₀H₀`. -/
theorem dualG_eq {x j : ℕ} (hx : 80 ≤ 2 * π * x) (hj : j < x) :
    dualG x j = fun z => (muR (2 * π * x) (2 * j) : ℂ) * Hk (2 * π * x) (2 * j) z
      - ((Cvs.Approximant.DeepIndexSpineSpan.alpha (2 * π * x) j * muR (2 * π * x) 0 : ℝ) : ℂ) * Hk (2 * π * x) 0 z := by
  obtain ⟨hA1, hμ1, -⟩ := Cvs.Prolate.Mellin.RungUnitCircleLaw.rung_data hx hj
  obtain ⟨hA0, hμ0, -⟩ := Cvs.Prolate.Mellin.RungUnitCircleLaw.rung_data (j := 0) hx (by omega)
  simp only [mul_zero] at hA0 hμ0
  have e1 : ((muR (2 * π * x) (2 * j) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hμ1
  have e0 : ((muR (2 * π * x) 0 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hμ0
  funext z
  unfold dualG Hk psiC Gr
  have i1 := Cvs.Prolate.RungProfileEntireExtension.intervalIntegrable_rung hA1
  have i0 := Cvs.Prolate.RungProfileEntireExtension.intervalIntegrable_rung hA0
  have hc : ∀ g : ℝ → ℝ, IntervalIntegrable g volume (-1) 1 →
      IntervalIntegrable (fun u : ℝ => (g u : ℂ) * Complex.cos ((2 * π * x : ℝ) * z * u)) volume (-1) 1 :=
    fun g hg => (show IntervalIntegrable (fun u => (g u : ℂ)) volume (-1) 1 from
      ⟨hg.1.ofReal, hg.2.ofReal⟩).mul_continuousOn (by fun_prop)
  rw [mul_div_cancel₀ _ e1]
  rw [show ((Cvs.Approximant.DeepIndexSpineSpan.alpha (2 * π * x) j * muR (2 * π * x) 0 : ℝ) : ℂ)
      * ((∫ u in (-1 : ℝ)..1, ((rung (2 * π * x) 0 u : ℝ) : ℂ) * Complex.cos ((2 * π * x : ℝ) * z * u))
        / (muR (2 * π * x) 0 : ℂ))
      = (Cvs.Approximant.DeepIndexSpineSpan.alpha (2 * π * x) j : ℂ)
        * ∫ u in (-1 : ℝ)..1, ((rung (2 * π * x) 0 u : ℝ) : ℂ) * Complex.cos ((2 * π * x : ℝ) * z * u) by
    push_cast; field_simp]
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub (hc _ i1) ((hc _ i0).const_mul _)]
  refine intervalIntegral.integral_congr fun u _ => ?_
  push_cast; ring

/-- `T_F(w) = −iM_F(1/2 − w)`. -/
theorem rayT_eq_circM (F : ℂ → ℂ) (w : ℂ) : rayT F w = -I * Cvs.Prolate.Mellin.UnitCircleMellinSolution.circM F (1 / 2 - w) := by
  unfold rayT Cvs.Prolate.Mellin.UnitCircleMellinSolution.circM Cvs.Prolate.Mellin.UnitCircleMellinSolution.lap Cvs.Prolate.Mellin.UnitCircleMellinSolution.Φ0 Cvs.Prolate.Mellin.UnitCircleMellinSolution.zc
  rw [← mul_assoc, show -I * I = 1 by rw [neg_mul, Complex.I_mul_I, neg_neg], one_mul]
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  dsimp only
  rw [mul_assoc, ← Complex.exp_add]
  congr 2; ring

/-- **The ray transform of a two-rung combination**: for `|σ| ≤ 1`, `g ≥ 8πx`,
`g‖T_{aH_{4j} + bH₀}(σ + ig)‖ ≤ 4e⁶(|a||h_{4j}(1)| + |b||h₀(1)|)`. -/
theorem g_norm_rayT_comb_le {x j : ℕ} (hx : 80 ≤ 2 * π * x) (hj : j < x) (a b : ℂ) {σ : ℝ} (hσ : |σ| ≤ 1)
    {g : ℝ} (hg : 8 * π * x ≤ g) :
    g * ‖rayT (fun z => a * Hk (2 * π * x) (2 * j) z + b * Hk (2 * π * x) 0 z) (σ + g * I)‖
      ≤ 4 * Real.exp 6 * (‖a‖ * |rung (2 * π * x) (2 * j) 1| + ‖b‖ * |rung (2 * π * x) 0 1|) := by
  have hc : 10 ≤ 2 * π * (x : ℝ) := by linarith
  have hgc : 4 * (2 * π * (x : ℝ)) ≤ g := by linarith
  obtain ⟨hA1, hμ1, hχ1⟩ := Cvs.Prolate.Mellin.RungUnitCircleLaw.rung_data hx hj
  obtain ⟨hA0, hμ0, hχ0⟩ := Cvs.Prolate.Mellin.RungUnitCircleLaw.rung_data (j := 0) hx (by omega)
  simp only [mul_zero] at hA0 hμ0 hχ0
  have hd1 := Cvs.Prolate.EntireRungProlateEquation.differentiable_Hk hA1
  have hd0 := Cvs.Prolate.EntireRungProlateEquation.differentiable_Hk hA0
  have ho1 := Cvs.Prolate.EntireRungProlateEquation.ode_Hk hA1 hμ1
  have ho0 := Cvs.Prolate.EntireRungProlateEquation.ode_Hk hA0 hμ0
  set τ := 1 / 2 - σ with hτd
  have hτ1 : -1 / 2 ≤ τ := by rw [hτd]; linarith [(abs_le.1 hσ).2]
  have hτ2 : τ ≤ 3 / 2 := by rw [hτd]; linarith [(abs_le.1 hσ).1]
  have hp : 1 / 2 - ((σ : ℂ) + g * I) = pm τ g 0 := by unfold Cvs.Prolate.Mellin.FrozenRootResidual.pm; rw [hτd]; push_cast; ring
  have hpim : (pm τ g 0).im < 0 := by rw [Cvs.Prolate.Mellin.UnitCircleMellinEdgeBound.im_pm]; linarith
  have L1 := Cvs.Prolate.Mellin.UnitCircleMellinEdgeBound.norm_mul_circM_le hd1 hc hχ1 ho1 hτ1 hτ2 hgc
  have L0 := Cvs.Prolate.Mellin.UnitCircleMellinEdgeBound.norm_mul_circM_le hd0 hc hχ0 ho0 hτ1 hτ2 hgc
  have hH1 : Hk (2 * π * x) (2 * j) 1 = (rung (2 * π * x) (2 * j) 1 : ℂ) := by
    have := Cvs.Prolate.EntireRungProlateEquation.Hk_ofReal hA1 hμ1 (s := 1) ⟨by norm_num, le_rfl⟩; simpa using this
  have hH0 : Hk (2 * π * x) 0 1 = (rung (2 * π * x) 0 1 : ℂ) := by
    have := Cvs.Prolate.EntireRungProlateEquation.Hk_ofReal hA0 hμ0 (s := 1) ⟨by norm_num, le_rfl⟩; simpa using this
  rw [hH1, Complex.norm_real, Real.norm_eq_abs] at L1
  rw [hH0, Complex.norm_real, Real.norm_eq_abs] at L0
  have hlin : Cvs.Prolate.Mellin.UnitCircleMellinSolution.circM (fun z => a * Hk (2 * π * x) (2 * j) z + b * Hk (2 * π * x) 0 z) (pm τ g 0)
      = a * Cvs.Prolate.Mellin.UnitCircleMellinSolution.circM (Hk (2 * π * x) (2 * j)) (pm τ g 0) + b * Cvs.Prolate.Mellin.UnitCircleMellinSolution.circM (Hk (2 * π * x) 0) (pm τ g 0) := by
    have h := Cvs.Prolate.Mellin.RungUnitCircleLaw.circM_sub_smul ((hd1.const_mul a)) hd0 (-b) hpim
    simp only [neg_mul, sub_neg_eq_add] at h
    rw [h]
    unfold Cvs.Prolate.Mellin.UnitCircleMellinSolution.circM Cvs.Prolate.Mellin.UnitCircleMellinSolution.Φ0
    rw [Cvs.Prolate.Mellin.UnitCircleMellinSolution.lap_const_mul a (fun s => Hk (2 * π * x) (2 * j) (Cvs.Prolate.Mellin.UnitCircleMellinSolution.zc s))]
    ring
  rw [rayT_eq_circM, hp, hlin, norm_mul, norm_neg, Complex.norm_I, one_mul]
  have hgp : g ≤ ‖pm τ g 0‖ := Cvs.Prolate.Mellin.UnitCircleMellinEdgeBound.norm_pm_ge τ g 0
  set M1 := Cvs.Prolate.Mellin.UnitCircleMellinSolution.circM (Hk (2 * π * x) (2 * j)) (pm τ g 0)
  set M0 := Cvs.Prolate.Mellin.UnitCircleMellinSolution.circM (Hk (2 * π * x) 0) (pm τ g 0)
  calc g * ‖a * M1 + b * M0‖ ≤ ‖pm τ g 0‖ * ‖a * M1 + b * M0‖ := mul_le_mul_of_nonneg_right hgp (norm_nonneg _)
    _ = ‖a * (pm τ g 0 * M1) + b * (pm τ g 0 * M0)‖ := by rw [← norm_mul]; ring_nf
    _ ≤ ‖a‖ * ‖pm τ g 0 * M1‖ + ‖b‖ * ‖pm τ g 0 * M0‖ := by
        refine (norm_add_le _ _).trans ?_; rw [norm_mul a, norm_mul b]
    _ ≤ ‖a‖ * (4 * Real.exp 6 * |rung (2 * π * x) (2 * j) 1|) + ‖b‖ * (4 * Real.exp 6 * |rung (2 * π * x) 0 1|) := by
        gcongr
    _ = _ := by ring

/-- The dual profile on the reflected circle, `ζ ↦ ζ⁻¹Ĝ(ζ⁻¹)`. -/
def dualQ (x j : ℕ) (ζ : ℂ) : ℂ := ζ⁻¹ * dualG x j ζ⁻¹

/-- `T_{ζ⁻¹Ĝ(ζ⁻¹)}(w) = conj T_Ĝ(−w̄)`. -/
theorem rayT_dualQ (x j : ℕ) (w : ℂ) : rayT (dualQ x j) w = conj (rayT (dualG x j) (-conj w)) := by
  unfold rayT dualQ
  rw [← integral_conj]
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  dsimp only
  have h1 : (Complex.exp (-(s * I)))⁻¹ = Complex.exp (s * I) := by rw [← Complex.exp_neg, neg_neg]
  have h2 : Complex.exp (s * I) = conj (Complex.exp (-(s * I))) := by
    rw [← Complex.exp_conj]; congr 1; simp [Complex.conj_ofReal]
  have hG' : dualG x j (Complex.exp (s * I)) = conj (dualG x j (Complex.exp (-(s * I)))) := by
    rw [h2]; exact psiC_conj _ _ _
  have h3 : conj (Complex.exp (-(s * I / 2))) = Complex.exp (s * I / 2) := by
    rw [← Complex.exp_conj]; congr 1
    rw [map_neg, map_div₀, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]; ring
  have h4 : conj (Complex.exp (-conj w * (s * I))) = Complex.exp (w * (s * I)) := by
    rw [← Complex.exp_conj]; congr 1; simp [Complex.conj_ofReal]
  rw [h1, hG', map_mul, map_mul, h3, h4]
  have h5 : Complex.exp (s * I) * Complex.exp (-(s * I / 2)) = Complex.exp (s * I / 2) := by
    rw [← Complex.exp_add]; congr 1; ring
  calc Complex.exp (s * I) * conj (dualG x j (Complex.exp (-(s * I)))) * Complex.exp (-(s * I / 2))
        * Complex.exp (w * (s * I))
      = conj (dualG x j (Complex.exp (-(s * I)))) * (Complex.exp (s * I) * Complex.exp (-(s * I / 2)))
        * Complex.exp (w * (s * I)) := by ring
    _ = _ := by rw [h5]

/-- **The dual profile meets the alias bound**: for `|σ| ≤ 1` and `g ≥ 8πx`,
`g‖T_{ζ⁻¹Ĝ(ζ⁻¹)}(σ + ig)‖ ≤ 4e⁶E_j/√x`. -/
theorem g_norm_rayT_dualQ_le {x j : ℕ} (hx : 80 ≤ 2 * π * x) (hj : j < x) {σ : ℝ} (hσ : |σ| ≤ 1) {g : ℝ}
    (hg : 8 * π * x ≤ g) :
    g * ‖rayT (dualQ x j) (σ + g * I)‖ ≤ 4 * Real.exp 6 * Cvs.Prolate.Mellin.RungWindowLawRightEdge.edgeE x j / √(x : ℝ) := by
  set c := 2 * π * (x : ℝ) with hcdef
  have hσ' : |-σ| ≤ 1 := by rwa [abs_neg]
  rw [rayT_dualQ, Complex.norm_conj]
  have hw : -conj ((σ : ℂ) + g * I) = ((-σ : ℝ) : ℂ) + g * I := by
    simp [Complex.conj_ofReal]; ring
  rw [hw, dualG_eq hx hj]
  have hb := g_norm_rayT_comb_le hx hj (muR c (2 * j) : ℂ) (-((Cvs.Approximant.DeepIndexSpineSpan.alpha c j * muR c 0 : ℝ) : ℂ)) hσ' hg
  have e : (fun z => (muR c (2 * j) : ℂ) * Hk c (2 * j) z - ((Cvs.Approximant.DeepIndexSpineSpan.alpha c j * muR c 0 : ℝ) : ℂ) * Hk c 0 z)
      = fun z => (muR c (2 * j) : ℂ) * Hk c (2 * j) z + -((Cvs.Approximant.DeepIndexSpineSpan.alpha c j * muR c 0 : ℝ) : ℂ) * Hk c 0 z := by
    funext z; ring
  rw [e]
  refine hb.trans ?_
  obtain ⟨hA1, -, -⟩ := Cvs.Prolate.Mellin.RungUnitCircleLaw.rung_data hx hj
  have h0 := Cvs.Prolate.EvenRungsByIndex.exists_isLevelIdx_zero c
  have m1 := Cvs.Prolate.Mellin.RightEdgePoissonSplit.abs_muR_le hx hA1
  have m0 := Cvs.Prolate.Mellin.RightEdgePoissonSplit.abs_muR_le (k := 0) hx h0
  rw [Complex.norm_real, Real.norm_eq_abs, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_mul]
  unfold Cvs.Prolate.Mellin.RungWindowLawRightEdge.edgeE
  rw [← hcdef]
  have hs : 0 < √(x : ℝ) := Real.sqrt_pos.2 (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx)
  calc 4 * Real.exp 6 * (|muR c (2 * j)| * |rung c (2 * j) 1| + |Cvs.Approximant.DeepIndexSpineSpan.alpha c j| * |muR c 0| * |rung c 0 1|)
      ≤ 4 * Real.exp 6 * (1 / √(x : ℝ) * |rung c (2 * j) 1| + |Cvs.Approximant.DeepIndexSpineSpan.alpha c j| * (1 / √(x : ℝ)) * |rung c 0 1|) := by
        gcongr
    _ = _ := by ring

end Cvs.Prolate.Mellin.RightEdgeAliasLaw

end
