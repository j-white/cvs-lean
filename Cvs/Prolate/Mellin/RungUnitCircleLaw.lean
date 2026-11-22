import Mathlib
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.Approximant.SpineSubspace
import Cvs.L2a.FullSpanIndexFloor
import Cvs.L2a.WindowChainInputsProlate
import Cvs.Prolate.EntireRungProlateEquation
import Cvs.Prolate.EvenLevelIndexLemma
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.GroundRungEndpoint
import Cvs.Prolate.Mellin.FrozenRootResidual
import Cvs.Prolate.Mellin.RungTransformUnitCircle
import Cvs.Prolate.Mellin.RungWindowLawCircleEdge
import Cvs.Prolate.Mellin.UnitCircleMellinEdgeBound
import Cvs.Prolate.Mellin.UnitCircleMellinSolution
import Cvs.Prolate.RungProfileEntireExtension
import Cvs.Prolate.RungWindowProfileCells
import Cvs.Route.Visibility.ExtPairingRatesSubpoly

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The unit-circle law for the rung profiles

`A(w) = −iM_G(1/2 − w)` for the unit-circle Mellin transform `M_G` of `G_j = H_{4j} − α_jH₀`, and each `H_k` solves
the prolate equation with `0 < χ_k < c²` (Cvs.Prolate.EntireRungProlateEquation), so Cvs.Prolate.Mellin.UnitCircleMellinEdgeBound gives `g|A(σ + ig)| ≤ 4e⁶(|h_{4j}(1)| + |α_j||h₀(1)|)`
beyond `8πx` for `|σ| ≤ 1`. The edge dominance `|α_jh₀(1)| ≤ |h_{4j}(1)|/2` turns this into `CircleLaw`.
-/

noncomputable section

open Real Set MeasureTheory Complex Filter Topology
open Cvs.Prolate.EvenRungsByIndex (rung muR lev IsLevelIdx)
open Cvs.Prolate.EntireRungProlateEquation (Hk)
open Cvs.Prolate.Mellin.FrozenRootResidual (pm)

namespace Cvs.Prolate.Mellin.RungUnitCircleLaw
open Cvs.ZeroCounting

/-- `G_j = H_{4j} − α_jH₀` as entire functions. -/
theorem GC_eq (x j : ℕ) : Cvs.Prolate.RungProfileEntireExtension.GC x j = fun z => Hk (2 * π * x) (2 * j) z
    - Cvs.Approximant.DeepIndexSpineSpan.alpha (2 * π * x) j * Hk (2 * π * x) 0 z := rfl

/-- **`A` is the unit-circle Mellin transform**: `A(w) = −iM_G(1/2 − w)`. -/
theorem Aw_eq (x j : ℕ) (w : ℂ) : Cvs.Prolate.Mellin.RungTransformUnitCircle.Aw x j w = -I * Cvs.Prolate.Mellin.UnitCircleMellinSolution.circM (Cvs.Prolate.RungProfileEntireExtension.GC x j) (1 / 2 - w) := by
  unfold Cvs.Prolate.Mellin.RungTransformUnitCircle.Aw Cvs.Prolate.Mellin.UnitCircleMellinSolution.circM Cvs.Prolate.Mellin.UnitCircleMellinSolution.lap Cvs.Prolate.Mellin.UnitCircleMellinSolution.Φ0 Cvs.Prolate.Mellin.UnitCircleMellinSolution.zc
  rw [← mul_assoc, show -I * I = 1 by rw [neg_mul, Complex.I_mul_I, neg_neg], one_mul]
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  simp only
  rw [mul_assoc, ← Complex.exp_add]
  congr 2; ring

/-- The unit-circle Mellin transform is linear in the profile. -/
theorem circM_sub_smul {H₁ H₂ : ℂ → ℂ} (h₁ : Differentiable ℂ H₁) (h₂ : Differentiable ℂ H₂) (α : ℂ) {p : ℂ}
    (hp : p.im < 0) :
    Cvs.Prolate.Mellin.UnitCircleMellinSolution.circM (fun z => H₁ z - α * H₂ z) p = Cvs.Prolate.Mellin.UnitCircleMellinSolution.circM H₁ p - α * Cvs.Prolate.Mellin.UnitCircleMellinSolution.circM H₂ p := by
  obtain ⟨M₁, hM₁⟩ := Cvs.Prolate.Mellin.UnitCircleMellinSolution.exists_bound_Φ0 h₁
  obtain ⟨M₂, hM₂⟩ := Cvs.Prolate.Mellin.UnitCircleMellinSolution.exists_bound_Φ0 h₂
  have c₁ := Cvs.Prolate.Mellin.UnitCircleMellinSolution.continuous_Φ0 h₁
  have c₂ := Cvs.Prolate.Mellin.UnitCircleMellinSolution.continuous_Φ0 h₂
  have e : Cvs.Prolate.Mellin.UnitCircleMellinSolution.Φ0 (fun z => H₁ z - α * H₂ z) = fun s => Cvs.Prolate.Mellin.UnitCircleMellinSolution.Φ0 H₁ s + (-α) * Cvs.Prolate.Mellin.UnitCircleMellinSolution.Φ0 H₂ s := by
    funext s; simp only [Cvs.Prolate.Mellin.UnitCircleMellinSolution.Φ0]; ring
  have hb : ∀ s, ‖(-α) * Cvs.Prolate.Mellin.UnitCircleMellinSolution.Φ0 H₂ s‖ ≤ ‖α‖ * M₂ := fun s => by
    rw [norm_mul, norm_neg]; exact mul_le_mul_of_nonneg_left (hM₂ s) (norm_nonneg _)
  have hl := Cvs.Prolate.Mellin.UnitCircleMellinSolution.lap_add (f := Cvs.Prolate.Mellin.UnitCircleMellinSolution.Φ0 H₁) (g := fun s => -α * Cvs.Prolate.Mellin.UnitCircleMellinSolution.Φ0 H₂ s) c₁ (continuous_const.mul c₂)
    hM₁ hb hp
  unfold Cvs.Prolate.Mellin.UnitCircleMellinSolution.circM
  rw [e, hl, Cvs.Prolate.Mellin.UnitCircleMellinSolution.lap_const_mul]
  ring

/-- The rung data at `c = 2πx`: a level with `|χ| ≤ c²`, `μ ≠ 0`, and the equation for `H_{2k}`. -/
theorem rung_data {x j : ℕ} (hx : 80 ≤ 2 * π * x) (hj : j < x) :
    (∃ χ, IsLevelIdx (2 * π * x) (2 * j) χ) ∧ muR (2 * π * x) (2 * j) ≠ 0
      ∧ |lev (2 * π * x) (2 * j)| ≤ (2 * π * x) ^ 2 := by
  have h1 := Cvs.L2a.FullSpanIndexFloor.full_index x hx hj
  have hc0 : 0 < 2 * π * (x : ℝ) := by linarith
  have hsl := Cvs.L2a.FullSpanIndexFloor.sigmaLow_pos (by linarith : 1 < 2 * π * (x : ℝ))
  have h0 := Cvs.Prolate.EvenRungsByIndex.exists_isLevelIdx_zero (2 * π * x)
  have hl0 := Cvs.Prolate.GroundRungEndpoint.lev_zero_pos hc0.ne'
  have hle := Cvs.Prolate.EvenRungsByIndex.lev_le h1.1 (Nat.zero_le (2 * j))
  refine ⟨h1.1, Cvs.Prolate.RungProfileEntireExtension.muR_ne_zero (Cvs.L2a.WindowChainInputsProlate.half_le_lamR hx hj), ?_⟩
  rw [abs_of_pos (by linarith)]
  linarith [h1.2]

/-- **The unit-circle law with the two edge values**: for `2πx ≥ 80`, `j < x`, `|σ| ≤ 1`, `g ≥ 8πx`,
`g|A(σ + ig)| ≤ 4e⁶(|h_{4j}(1)| + |α_j||h₀(1)|)`. -/
theorem g_norm_Aw_le {x j : ℕ} (hx : 80 ≤ 2 * π * x) (hj : j < x) {σ : ℝ} (hσ : |σ| ≤ 1) {g : ℝ}
    (hg : 8 * π * x ≤ g) :
    g * ‖Cvs.Prolate.Mellin.RungTransformUnitCircle.Aw x j (σ + g * I)‖ ≤ 4 * Real.exp 6 * (|rung (2 * π * x) (2 * j) 1|
      + |Cvs.Approximant.DeepIndexSpineSpan.alpha (2 * π * x) j| * |rung (2 * π * x) 0 1|) := by
  have hc : 10 ≤ 2 * π * (x : ℝ) := by linarith
  have hgc : 4 * (2 * π * (x : ℝ)) ≤ g := by linarith
  have hg0 : 0 < g := by linarith
  obtain ⟨hA1, hμ1, hχ1⟩ := rung_data hx hj
  obtain ⟨hA0, hμ0, hχ0⟩ := rung_data (j := 0) hx (by omega)
  simp only [mul_zero] at hA0 hμ0 hχ0
  have hd1 := Cvs.Prolate.EntireRungProlateEquation.differentiable_Hk hA1
  have hd0 := Cvs.Prolate.EntireRungProlateEquation.differentiable_Hk hA0
  have ho1 := Cvs.Prolate.EntireRungProlateEquation.ode_Hk hA1 hμ1
  have ho0 := Cvs.Prolate.EntireRungProlateEquation.ode_Hk hA0 hμ0
  set τ := 1 / 2 - σ with hτd
  have hτ1 : -1 / 2 ≤ τ := by rw [hτd]; linarith [(abs_le.1 hσ).2]
  have hτ2 : τ ≤ 3 / 2 := by rw [hτd]; linarith [(abs_le.1 hσ).1]
  have hp : 1 / 2 - ((σ : ℂ) + g * I) = pm τ g 0 := by unfold pm; rw [hτd]; push_cast; ring
  have hpim : (pm τ g 0).im < 0 := by rw [Cvs.Prolate.Mellin.UnitCircleMellinEdgeBound.im_pm]; linarith
  have L1 := Cvs.Prolate.Mellin.UnitCircleMellinEdgeBound.norm_mul_circM_le hd1 hc hχ1 ho1 hτ1 hτ2 hgc
  have L0 := Cvs.Prolate.Mellin.UnitCircleMellinEdgeBound.norm_mul_circM_le hd0 hc hχ0 ho0 hτ1 hτ2 hgc
  have hH1 : Hk (2 * π * x) (2 * j) 1 = (rung (2 * π * x) (2 * j) 1 : ℂ) := by
    have := Cvs.Prolate.EntireRungProlateEquation.Hk_ofReal hA1 hμ1 (s := 1) ⟨by norm_num, le_rfl⟩; simpa using this
  have hH0 : Hk (2 * π * x) 0 1 = (rung (2 * π * x) 0 1 : ℂ) := by
    have := Cvs.Prolate.EntireRungProlateEquation.Hk_ofReal hA0 hμ0 (s := 1) ⟨by norm_num, le_rfl⟩; simpa using this
  rw [hH1, Complex.norm_real, Real.norm_eq_abs] at L1
  rw [hH0, Complex.norm_real, Real.norm_eq_abs] at L0
  rw [Aw_eq, hp, GC_eq, circM_sub_smul hd1 hd0 _ hpim, norm_mul, norm_neg, Complex.norm_I, one_mul]
  have hgp : g ≤ ‖pm τ g 0‖ := Cvs.Prolate.Mellin.UnitCircleMellinEdgeBound.norm_pm_ge τ g 0
  set M1 := Cvs.Prolate.Mellin.UnitCircleMellinSolution.circM (Hk (2 * π * x) (2 * j)) (pm τ g 0)
  set M0 := Cvs.Prolate.Mellin.UnitCircleMellinSolution.circM (Hk (2 * π * x) 0) (pm τ g 0)
  set α := Cvs.Approximant.DeepIndexSpineSpan.alpha (2 * π * x) j
  calc g * ‖M1 - (α : ℂ) * M0‖ ≤ ‖pm τ g 0‖ * ‖M1 - (α : ℂ) * M0‖ :=
        mul_le_mul_of_nonneg_right hgp (norm_nonneg _)
    _ = ‖pm τ g 0 * M1 - (α : ℂ) * (pm τ g 0 * M0)‖ := by rw [← norm_mul]; ring_nf
    _ ≤ ‖pm τ g 0 * M1‖ + |α| * ‖pm τ g 0 * M0‖ := by
        refine (norm_sub_le _ _).trans ?_
        rw [norm_mul (α : ℂ), Complex.norm_real, Real.norm_eq_abs]
    _ ≤ 4 * Real.exp 6 * |rung (2 * π * x) (2 * j) 1| + |α| * (4 * Real.exp 6 * |rung (2 * π * x) 0 1|) := by
        gcongr
    _ = 4 * Real.exp 6 * (|rung (2 * π * x) (2 * j) 1| + |α| * |rung (2 * π * x) 0 1|) := by ring

/-- **The edge dominance**: eventually, for every rung, `|α_jh₀(1)| ≤ |h_{4j}(1)|/2` at `c = 2πx`. -/
def EdgeDominance : Prop :=
  ∀ᶠ x : ℕ in atTop, ∀ j : Cvs.Approximant.SpineSubspace.SF x,
    |Cvs.Approximant.DeepIndexSpineSpan.alpha (2 * π * x) j * rung (2 * π * x) 0 1| ≤ 1 / 2 * |rung (2 * π * x) (2 * j) 1|

/-- **The unit-circle law from the edge dominance**, with the constant `C = 12e⁶`. -/
theorem circleLaw_of_edgeDominance (h : EdgeDominance) : Cvs.Prolate.Mellin.RungWindowLawCircleEdge.CircleLaw := by
  refine ⟨fun _ => 12 * Real.exp 6, Cvs.Route.Visibility.ExtPairingRatesSubpoly.subPoly_const _, ?_⟩
  filter_upwards [h, eventually_ge_atTop 13] with x hx hx13 j σ hσ g hg
  have hx80 : 80 ≤ 2 * π * (x : ℝ) := by
    have : (13 : ℝ) ≤ x := by exact_mod_cast hx13
    nlinarith [Real.pi_gt_d2]
  have hj : (j : ℕ) < x := Cvs.Approximant.SpineSubspace.SF_lt x j j.2
  have hA := g_norm_Aw_le hx80 hj hσ hg
  have hd := hx j
  set a := rung (2 * π * x) (2 * (j : ℕ)) 1
  set b := Cvs.Approximant.DeepIndexSpineSpan.alpha (2 * π * x) j * rung (2 * π * x) 0 1
  have hG : Cvs.Prolate.RungWindowProfileCells.Gr x j 1 = a - b := rfl
  have hb : |b| ≤ 1 / 2 * |a| := hd
  rw [abs_mul] at hd
  have hlow : |a| ≤ 2 * |a - b| := by
    have := abs_sub_abs_le_abs_sub a b
    linarith
  rw [hG]
  calc g * ‖Cvs.Prolate.Mellin.RungTransformUnitCircle.Aw x j (σ + g * I)‖ ≤ 4 * Real.exp 6 * (|a| + |Cvs.Approximant.DeepIndexSpineSpan.alpha (2 * π * x) j|
        * |rung (2 * π * x) 0 1|) := hA
    _ ≤ 4 * Real.exp 6 * (3 / 2 * |a|) := by gcongr; linarith
    _ ≤ 12 * Real.exp 6 * |a - b| := by nlinarith [Real.exp_pos 6, abs_nonneg a]

end Cvs.Prolate.Mellin.RungUnitCircleLaw

end
