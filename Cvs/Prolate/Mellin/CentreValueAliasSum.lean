import Mathlib
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.Approximant.SpineCouplingTailPairing
import Cvs.Approximant.SpineSubspace
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.FullSpanIndexFloor
import Cvs.L2a.WindowChainInputsProlate
import Cvs.Prolate.EdgeBesselCount
import Cvs.Prolate.Envelope.RungCentreBound
import Cvs.Prolate.Envelope.RungEdgePlungeLower
import Cvs.Prolate.Envelope.RungExteriorLaw
import Cvs.Prolate.Envelope.RungPlungeEdgeUpper
import Cvs.Prolate.EvenLevelIndexLemma
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.Mellin.RayTransformEdgeSum
import Cvs.Prolate.Mellin.RightEdgeAliasLaw
import Cvs.Prolate.Mellin.RightEdgeIntegralPart
import Cvs.Prolate.Mellin.RungWindowLawRightEdge
import Cvs.Prolate.RungFarMassFloor
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
# The centre value of a rung profile is at the edge scale, and the alias law is the pure alias sum law

Cvs.Prolate.Envelope.RungCentreBound gives `G_j(0)² ≤ (16/π²)(1 − λ_{4j})`, and Cvs.Prolate.Envelope.RungPlungeEdgeUpper gives `1 − λ_{4j} ≤ P♯(2πx)E_j²`, so
`G_j(0)² ≤ (16/π²)P♯(2πx)E_j²` with `P♯ ≤ 30`. The constant term `−G_j(0)/(2x)` of the Euler–Maclaurin remainder
`Q` therefore contributes at most `7E_j/(2x)` to `g‖T_Q‖`, and `AliasLaw` is equivalent to the same law for the
alias sum `Q + G_j(0)/(2x) = Σ_{m ≥ 1} W_m`.
-/

noncomputable section

open Real Set MeasureTheory Filter Complex
open Cvs.Prolate.RungProfileEntireExtension (GC)
open Cvs.Prolate.RungWindowProfileCells (Gr)
open Cvs.Prolate.Mellin.RayTransformEdgeSum (rayT)
open Cvs.Prolate.Mellin.RightEdgeAliasLaw (aliasQ AliasLaw)
open Cvs.Prolate.EvenRungsByIndex (rung lamR lev)
open Cvs.Route.Visibility.ExtPairingRatesSubpoly (SubPoly)

namespace Cvs.Prolate.Mellin.CentreValueAliasSum
open Cvs.ZeroCounting

/-- **The sharp edge floor of a rung**: for `2πx ≥ 80` and `j < x`, `1 − λ_{4j} ≤ P♯(2πx)·E_j²`. -/
theorem one_sub_lamR_le_sharp_edgeE {x j : ℕ} (hx : 80 ≤ 2 * π * x) (hj : j < x) :
    1 - lamR (2 * π * x) (2 * j) ≤ Cvs.Prolate.Envelope.RungPlungeEdgeUpper.sharpP (2 * π * x) * Cvs.Prolate.Mellin.RungWindowLawRightEdge.edgeE x j ^ 2 := by
  have hc0 : 0 < 2 * π * (x : ℝ) := by linarith
  have h1 := (Cvs.L2a.FullSpanIndexFloor.full_index x hx hj).1
  have hDl := (Cvs.Prolate.RungFarMassFloor.rung_edge_mass hx hj).1
  have hs := Cvs.Prolate.Envelope.RungPlungeEdgeUpper.one_sub_lamR_le_sharp hx h1 hDl
  have hl1 := Cvs.Prolate.Envelope.RungExteriorLaw.lamR_le_one hc0 h1
  have hl0 : 0 ≤ lamR (2 * π * x) (2 * j) := by unfold lamR; positivity
  have hP : 0 ≤ Cvs.Prolate.Envelope.RungPlungeEdgeUpper.sharpP (2 * π * x) := by
    have := Cvs.Prolate.Envelope.RungEdgePlungeLower.Kbar_nonneg hx
    have := Cvs.Prolate.Envelope.RungPlungeEdgeUpper.topP_nonneg hx
    unfold Cvs.Prolate.Envelope.RungPlungeEdgeUpper.sharpP; positivity
  have hE : rung (2 * π * x) (2 * j) 1 ^ 2 ≤ Cvs.Prolate.Mellin.RungWindowLawRightEdge.edgeE x j ^ 2 := by
    have : |rung (2 * π * x) (2 * j) 1| ≤ Cvs.Prolate.Mellin.RungWindowLawRightEdge.edgeE x j := by
      unfold Cvs.Prolate.Mellin.RungWindowLawRightEdge.edgeE
      have : 0 ≤ |Cvs.Approximant.DeepIndexSpineSpan.alpha (2 * π * x) j| * |rung (2 * π * x) 0 1| := by positivity
      linarith
    calc rung (2 * π * x) (2 * j) 1 ^ 2 = |rung (2 * π * x) (2 * j) 1| ^ 2 := (sq_abs _).symm
      _ ≤ _ := pow_le_pow_left₀ (abs_nonneg _) this 2
  have hlh : lamR (2 * π * x) (2 * j) * rung (2 * π * x) (2 * j) 1 ^ 2 ≤ Cvs.Prolate.Mellin.RungWindowLawRightEdge.edgeE x j ^ 2 := by
    have : lamR (2 * π * x) (2 * j) * rung (2 * π * x) (2 * j) 1 ^ 2 ≤ 1 * rung (2 * π * x) (2 * j) 1 ^ 2 :=
      mul_le_mul_of_nonneg_right hl1 (sq_nonneg _)
    linarith
  exact hs.trans (mul_le_mul_of_nonneg_left hlh hP)

/-- **The centre value of a rung profile**: for `2πx ≥ 80` and `j < x`, `G_j(0)² ≤ (16/π²)P♯(2πx)E_j²`. -/
theorem Gr_zero_sq_le {x j : ℕ} (hx : 80 ≤ 2 * π * x) (hj : j < x) :
    Gr x j 0 ^ 2 ≤ 16 / π ^ 2 * Cvs.Prolate.Envelope.RungPlungeEdgeUpper.sharpP (2 * π * x) * Cvs.Prolate.Mellin.RungWindowLawRightEdge.edgeE x j ^ 2 := by
  have hc0 : 0 < 2 * π * (x : ℝ) := by linarith
  have h1 := (Cvs.L2a.FullSpanIndexFloor.full_index x hx hj).1
  have hl := Cvs.L2a.WindowChainInputsProlate.half_le_lamR hx hj
  have hl0 := Cvs.Prolate.EvenRungsByIndex.lamR_anti hc0 h1 (Nat.zero_le (2 * j))
  have hG := Cvs.Prolate.Envelope.RungCentreBound.profile_zero_sq_le hc0 h1 hl (hl.trans hl0)
  have hs := one_sub_lamR_le_sharp_edgeE hx hj
  unfold Gr
  calc _ ≤ 16 / π ^ 2 * (1 - lamR (2 * π * x) (2 * j)) := hG
    _ ≤ 16 / π ^ 2 * (Cvs.Prolate.Envelope.RungPlungeEdgeUpper.sharpP (2 * π * x) * Cvs.Prolate.Mellin.RungWindowLawRightEdge.edgeE x j ^ 2) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by ring

/-- `|G_j(0)| ≤ 7E_j` for `2πx ≥ 80` and `j < x`. -/
theorem abs_Gr_zero_le {x j : ℕ} (hx : 80 ≤ 2 * π * x) (hj : j < x) : |Gr x j 0| ≤ 7 * Cvs.Prolate.Mellin.RungWindowLawRightEdge.edgeE x j := by
  have h := Gr_zero_sq_le hx hj
  have hP := Cvs.Prolate.Envelope.RungPlungeEdgeUpper.sharpP_le hx
  have hE0 := Cvs.Prolate.Mellin.RungWindowLawRightEdge.edgeE_nonneg x j
  have hpi : 16 / π ^ 2 * 30 ≤ 49 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [Real.pi_gt_d2]
  have hsq : Gr x j 0 ^ 2 ≤ (7 * Cvs.Prolate.Mellin.RungWindowLawRightEdge.edgeE x j) ^ 2 := by
    have hP0 : 0 ≤ Cvs.Prolate.Envelope.RungPlungeEdgeUpper.sharpP (2 * π * x) := by
      have := Cvs.Prolate.Envelope.RungEdgePlungeLower.Kbar_nonneg hx
      have := Cvs.Prolate.Envelope.RungPlungeEdgeUpper.topP_nonneg hx
      unfold Cvs.Prolate.Envelope.RungPlungeEdgeUpper.sharpP; positivity
    calc Gr x j 0 ^ 2 ≤ 16 / π ^ 2 * Cvs.Prolate.Envelope.RungPlungeEdgeUpper.sharpP (2 * π * x) * Cvs.Prolate.Mellin.RungWindowLawRightEdge.edgeE x j ^ 2 := h
      _ ≤ 16 / π ^ 2 * 30 * Cvs.Prolate.Mellin.RungWindowLawRightEdge.edgeE x j ^ 2 := by gcongr
      _ ≤ 49 * Cvs.Prolate.Mellin.RungWindowLawRightEdge.edgeE x j ^ 2 := by gcongr
      _ = (7 * Cvs.Prolate.Mellin.RungWindowLawRightEdge.edgeE x j) ^ 2 := by ring
  exact abs_le.2 (abs_le_of_sq_le_sq' hsq (by positivity))

/-- The alias sum `Q(ζ) + G_j(0)/(2x) = Σ_{m ≥ 1} W_m(ζ)`. -/
def aliasSum (x j : ℕ) (ζ : ℂ) : ℂ := aliasQ x j ζ + GC x j 0 / (2 * x)

/-- **The alias sum law**: some subpolynomial `C` has, at all large `x`, for every rung, `|σ| ≤ 1` and `g ≥ 8πx`,
`g‖T_{ΣW}(σ + ig)‖ ≤ C(x)E_j/√x`. -/
def AliasSumLaw : Prop :=
  ∃ C : ℕ → ℝ, SubPoly C ∧ ∀ᶠ x : ℕ in atTop, ∀ j : Cvs.Approximant.SpineSubspace.SF x, ∀ σ : ℝ, |σ| ≤ 1 → ∀ g : ℝ, 8 * π * x ≤ g →
    g * ‖rayT (aliasSum x j) (σ + g * I)‖ ≤ C x * Cvs.Prolate.Mellin.RungWindowLawRightEdge.edgeE x j / √(x : ℝ)

/-- The ray transform of a constant: `g‖T_K(σ + ig)‖ ≤ ‖K‖` for `g > 0`. -/
theorem g_norm_rayT_const_le (K : ℂ) (σ : ℝ) {g : ℝ} (hg : 0 < g) :
    g * ‖rayT (fun _ => K) (σ + g * I)‖ ≤ ‖K‖ := by
  have hwi : ((σ : ℂ) + g * I).im = g := by simp
  have h := Cvs.Prolate.Mellin.RayTransformEdgeSum.norm_rayT_le (F := fun _ => K) (w := σ + g * I) (by rw [hwi]; exact hg) (M := ‖K‖)
    (fun _ => le_rfl)
  rw [hwi] at h
  rw [le_div_iff₀ hg] at h
  linarith

/-- `T_{ΣW} = T_Q + T_{G_j(0)/(2x)}` on `Im w > 0`. -/
theorem rayT_aliasSum_eq {x j : ℕ} (hx : 80 ≤ 2 * π * x) (hj : j < x) {w : ℂ} (hw : 0 < w.im) :
    rayT (aliasSum x j) w = rayT (aliasQ x j) w + rayT (fun _ => GC x j 0 / (2 * x)) w := by
  have hH := (Cvs.Prolate.Mellin.RayTransformEdgeSum.differentiable_edgeSum hx hj).continuous
  have hF := (Cvs.Prolate.Mellin.RightEdgeIntegralPart.differentiable_intG hx hj).continuous
  have hG := (Cvs.Prolate.RungProfileEntireExtension.differentiable_GC hx hj).continuous
  have hQ : Continuous (aliasQ x j) := by unfold aliasQ; fun_prop
  have hQi := Cvs.Prolate.Mellin.RayTransformEdgeSum.integrableOn_integrand hQ hw
  have hKi := Cvs.Prolate.Mellin.RayTransformEdgeSum.integrableOn_integrand (continuous_const (y := GC x j 0 / (2 * x))) hw
  unfold rayT
  rw [← integral_add hQi hKi]
  refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  simp only [aliasSum]
  ring

/-- `|g‖T_{ΣW}‖ − g‖T_Q‖| ≤ 4E_j/√x` beyond `8πx`. -/
theorem abs_sub_le {x j : ℕ} (hx : 80 ≤ 2 * π * x) (hj : j < x) (σ : ℝ) {g : ℝ} (hg : 8 * π * x ≤ g) :
    |g * ‖rayT (aliasSum x j) (σ + g * I)‖ - g * ‖rayT (aliasQ x j) (σ + g * I)‖|
      ≤ 4 * Cvs.Prolate.Mellin.RungWindowLawRightEdge.edgeE x j / √(x : ℝ) := by
  have hx0 : (0 : ℝ) < x := Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx
  have hx1 : (1 : ℝ) ≤ x := by
    have : (1 : ℕ) ≤ x := by exact_mod_cast hx0
    exact_mod_cast this
  have hg0 : 0 < g := lt_of_lt_of_le (by positivity) hg
  have hwi : 0 < ((σ : ℂ) + g * I).im := by simp [hg0]
  rw [rayT_aliasSum_eq hx hj hwi]
  set Q := rayT (aliasQ x j) (σ + g * I)
  set K := rayT (fun _ => GC x j 0 / (2 * x)) (σ + g * I)
  have htri : |g * ‖Q + K‖ - g * ‖Q‖| ≤ g * ‖K‖ := by
    rw [← mul_sub, abs_mul, abs_of_pos hg0]
    refine mul_le_mul_of_nonneg_left ?_ hg0.le
    have := abs_norm_sub_norm_le (Q + K) Q
    rwa [add_sub_cancel_left] at this
  refine htri.trans ?_
  have hK := g_norm_rayT_const_le (GC x j 0 / (2 * x)) σ hg0
  have hG0 : GC x j 0 = ((Gr x j 0 : ℝ) : ℂ) := Cvs.Prolate.RungProfileEntireExtension.GC_ofReal hx hj ⟨by norm_num, by norm_num⟩
  have hnorm : ‖GC x j 0 / (2 * x)‖ = |Gr x j 0| / (2 * x) := by
    rw [hG0, norm_div, Complex.norm_real, Real.norm_eq_abs,
      show ‖(2 * (x : ℂ))‖ = 2 * x by rw [norm_mul, Complex.norm_ofNat, Complex.norm_natCast]]
  rw [hnorm] at hK
  have hA := abs_Gr_zero_le hx hj
  have hE0 := Cvs.Prolate.Mellin.RungWindowLawRightEdge.edgeE_nonneg x j
  have hsq : √(x : ℝ) ≤ x := by
    rw [Real.sqrt_le_left (by positivity)]; nlinarith
  have hs0 : 0 < √(x : ℝ) := Real.sqrt_pos.2 hx0
  calc g * ‖K‖ ≤ |Gr x j 0| / (2 * x) := hK
    _ ≤ 7 * Cvs.Prolate.Mellin.RungWindowLawRightEdge.edgeE x j / (2 * x) := div_le_div_of_nonneg_right hA (by positivity)
    _ ≤ 4 * Cvs.Prolate.Mellin.RungWindowLawRightEdge.edgeE x j / √(x : ℝ) := by
        rw [div_le_div_iff₀ (by positivity) hs0]
        nlinarith

/-- **The alias law is the alias sum law**. -/
theorem aliasLaw_iff_aliasSumLaw : AliasLaw ↔ AliasSumLaw := by
  constructor
  · rintro ⟨C, hC, hQ⟩
    refine ⟨fun x => C x + 4, hC.add (Cvs.Route.Visibility.ExtPairingRatesSubpoly.subPoly_const _), ?_⟩
    filter_upwards [hQ, Cvs.Route.Visibility.ExteriorFactorMTwo.eventually_scale] with x hQx hx j σ hσ g hg
    have hj : (j : ℕ) < x := Cvs.Approximant.SpineSubspace.SF_lt x j j.2
    have h1 := hQx j σ hσ g hg
    have h2 := (abs_le.1 (abs_sub_le hx hj σ hg)).2
    have e : (C x + 4) * Cvs.Prolate.Mellin.RungWindowLawRightEdge.edgeE x j / √(x : ℝ)
        = C x * Cvs.Prolate.Mellin.RungWindowLawRightEdge.edgeE x j / √(x : ℝ) + 4 * Cvs.Prolate.Mellin.RungWindowLawRightEdge.edgeE x j / √(x : ℝ) := by ring
    rw [e]; linarith
  · rintro ⟨C, hC, hS⟩
    refine ⟨fun x => C x + 4, hC.add (Cvs.Route.Visibility.ExtPairingRatesSubpoly.subPoly_const _), ?_⟩
    filter_upwards [hS, Cvs.Route.Visibility.ExteriorFactorMTwo.eventually_scale] with x hSx hx j σ hσ g hg
    have hj : (j : ℕ) < x := Cvs.Approximant.SpineSubspace.SF_lt x j j.2
    have h1 := hSx j σ hσ g hg
    have h2 := (abs_le.1 (abs_sub_le hx hj σ hg)).1
    have e : (C x + 4) * Cvs.Prolate.Mellin.RungWindowLawRightEdge.edgeE x j / √(x : ℝ)
        = C x * Cvs.Prolate.Mellin.RungWindowLawRightEdge.edgeE x j / √(x : ℝ) + 4 * Cvs.Prolate.Mellin.RungWindowLawRightEdge.edgeE x j / √(x : ℝ) := by ring
    rw [e]; linarith

/-- **The right-edge law is the alias sum law**. -/
theorem edgeLawSum_iff_aliasSumLaw : Cvs.Prolate.Mellin.RungWindowLawRightEdge.EdgeLawSum ↔ AliasSumLaw :=
  Cvs.Prolate.Mellin.RightEdgeAliasLaw.edgeLawSum_iff_aliasLaw.trans aliasLaw_iff_aliasSumLaw

end Cvs.Prolate.Mellin.CentreValueAliasSum

end
