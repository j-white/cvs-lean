import Mathlib
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.Approximant.SpineCouplingTailPairing
import Cvs.L2a.FullSpanIndexFloor
import Cvs.Prolate.EvenLevelIndexLemma
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.Mellin.RayTransformEdgeSum
import Cvs.Prolate.Mellin.RungTransformUnitCircle
import Cvs.Prolate.Mellin.RungUnitCircleLaw
import Cvs.Prolate.Mellin.RungWindowLawRightEdge
import Cvs.Prolate.RungProfileEntireExtension
import Cvs.Prolate.RungWindowProfileCells

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The integral part of the right-edge sum and its ray transform

The mean `F(ζ) = ∫_0^1 G_j(tζ) dt` is the limit of the right-edge sum `(1/x)Σ_{n ≤ x} G_j((n/x)ζ)` as the
spacing goes to zero. It is `dslope P 0` for a primitive `P` of `G_j`, hence entire, with `ζF′ = G_j − F`, and
`F(1) = ∫_0^1 G_j = 0` because `α_j = ∫h_{4j}/∫h₀`. `RayTransformEdgeSum`'s integration by parts then gives
`(w + ½) T_F(w) = A(w)`, so Cvs.Prolate.Mellin.RungUnitCircleLaw bounds `g‖T_F(σ + ig)‖ ≤ 4e⁶E_j/g` beyond `8πx`.
-/

noncomputable section

open Real Set MeasureTheory Filter Complex Topology
open Cvs.Prolate.RungProfileEntireExtension (GC)
open Cvs.Prolate.RungWindowProfileCells (Gr)
open Cvs.Prolate.Mellin.RungTransformUnitCircle (Aw Bw)
open Cvs.Prolate.Mellin.RayTransformEdgeSum (rayT)

namespace Cvs.Prolate.Mellin.RightEdgeIntegralPart
open Cvs.ZeroCounting

/-- The mean `F(ζ) = ∫_0^1 G_j(tζ) dt` of the rung profile along the segment `[0, ζ]`. -/
def intG (x j : ℕ) (ζ : ℂ) : ℂ := ∫ t in (0 : ℝ)..1, GC x j (t * ζ)

section primitive

variable {x j : ℕ} (hx : 80 ≤ 2 * π * x) (hj : j < x)
include hx hj

/-- `ζF(ζ) = P(ζ) − P(0)` for any primitive `P` of `G_j`. -/
theorem mul_intG {P : ℂ → ℂ} (hP : ∀ z, HasDerivAt P (GC x j z) z) (ζ : ℂ) :
    ζ * intG x j ζ = P ζ - P 0 := by
  have hGc := (Cvs.Prolate.RungProfileEntireExtension.differentiable_GC hx hj).continuous
  have hd : ∀ t : ℝ, HasDerivAt (fun y : ℝ => P (y * ζ)) (GC x j (t * ζ) * ζ) t := fun t => by
    have hl : HasDerivAt (fun y : ℝ => (y : ℂ) * ζ) ζ t := by
      simpa using ((hasDerivAt_id (t : ℂ)).mul_const ζ).comp_ofReal
    exact (hP _).comp t hl
  have hint : IntervalIntegrable (fun t : ℝ => GC x j (t * ζ) * ζ) volume 0 1 :=
    (by fun_prop : Continuous fun t : ℝ => GC x j (t * ζ) * ζ).intervalIntegrable _ _
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) hint
  rw [intervalIntegral.integral_mul_const] at h
  simp only [Complex.ofReal_one, one_mul, Complex.ofReal_zero, zero_mul] at h
  rw [intG, mul_comm, h]

/-- `F = dslope P 0`. -/
theorem intG_eq_dslope {P : ℂ → ℂ} (hP : ∀ z, HasDerivAt P (GC x j z) z) : intG x j = dslope P 0 := by
  funext ζ
  rcases eq_or_ne ζ 0 with h0 | h0
  · subst h0
    rw [dslope_same, (hP 0).deriv, intG]
    simp
  · rw [dslope_of_ne _ h0, slope_def_module, sub_zero, ← mul_intG hx hj hP ζ, smul_eq_mul, ← mul_assoc,
      inv_mul_cancel₀ h0, one_mul]

/-- **The mean is entire**. -/
theorem differentiable_intG : Differentiable ℂ (intG x j) := by
  obtain ⟨P, hP⟩ := (Cvs.Prolate.RungProfileEntireExtension.differentiable_GC hx hj).isExactOn_univ
  have hP' : ∀ z, HasDerivAt P (GC x j z) z := fun z => hP z (mem_univ z)
  rw [intG_eq_dslope hx hj hP']
  have hd : DifferentiableOn ℂ P univ := fun z _ => (hP' z).differentiableAt.differentiableWithinAt
  have := (differentiableOn_dslope (c := (0 : ℂ)) (s := univ) Filter.univ_mem).2 hd
  exact fun z => (this z (mem_univ z)).differentiableAt Filter.univ_mem

/-- **The Euler relation of the mean**: `ζF′(ζ) = G_j(ζ) − F(ζ)`. -/
theorem mul_deriv_intG (ζ : ℂ) : ζ * deriv (intG x j) ζ = GC x j ζ - intG x j ζ := by
  obtain ⟨P, hP⟩ := (Cvs.Prolate.RungProfileEntireExtension.differentiable_GC hx hj).isExactOn_univ
  have hP' : ∀ z, HasDerivAt P (GC x j z) z := fun z => hP z (mem_univ z)
  have he : (fun z => z * intG x j z) = fun z => P z - P 0 := funext (mul_intG hx hj hP')
  have h1 : HasDerivAt (fun z => z * intG x j z) (GC x j ζ) ζ := by
    rw [he]; exact (hP' ζ).sub_const _
  have h2 : HasDerivAt (fun z => z * intG x j z) (1 * intG x j ζ + ζ * deriv (intG x j) ζ) ζ :=
    (hasDerivAt_id ζ).mul (differentiable_intG hx hj ζ).hasDerivAt
  have := h2.unique h1
  linear_combination this

end primitive

/-- **The rung profile has mean zero on `[0, 1]`**: `∫_0^1 G_j = 0`. -/
theorem integral_Gr_zero_one {x j : ℕ} (hx : 80 ≤ 2 * π * x) (hj : j < x) : ∫ t in (0 : ℝ)..1, Gr x j t = 0 := by
  have h1 := (Cvs.L2a.FullSpanIndexFloor.full_index x hx hj).1
  have h0 := Cvs.Prolate.EvenRungsByIndex.exists_isLevelIdx_zero (2 * π * x)
  have hc0 : 0 < 2 * π * (x : ℝ) := by linarith
  have hi1 := Cvs.Prolate.RungProfileEntireExtension.intervalIntegrable_rung h1
  have hi0 := Cvs.Prolate.RungProfileEntireExtension.intervalIntegrable_rung h0
  have hne := Cvs.Prolate.EvenRungsByIndex.integral_rung_zero_ne hc0
  have hfull : ∫ t in (-1 : ℝ)..1, Gr x j t = 0 := by
    unfold Gr
    rw [intervalIntegral.integral_sub hi1 (hi0.const_mul _), intervalIntegral.integral_const_mul]
    unfold Cvs.Approximant.DeepIndexSpineSpan.alpha
    rw [div_mul_cancel₀ _ hne, sub_self]
  have hev : ∀ t ∈ Icc (-1 : ℝ) 1, Gr x j (-t) = Gr x j t := fun t ht => by
    unfold Gr
    rw [(Cvs.Prolate.EvenRungsByIndex.rung_spec h1).2.2.2.2.1 t ht, (Cvs.Prolate.EvenRungsByIndex.rung_spec h0).2.2.2.2.1 t ht]
  have hGi : IntervalIntegrable (Gr x j) volume (-1) 1 := hi1.sub (hi0.const_mul _)
  have hA : IntervalIntegrable (Gr x j) volume (-1) 0 := hGi.mono_set (by
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 0), uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    exact Icc_subset_Icc le_rfl (by norm_num))
  have hB : IntervalIntegrable (Gr x j) volume 0 1 := hGi.mono_set (by
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1), uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    exact Icc_subset_Icc (by norm_num) le_rfl)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hA hB
  have hneg : ∫ t in (-1 : ℝ)..0, Gr x j t = ∫ t in (0 : ℝ)..1, Gr x j t := by
    have := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := 1) (Gr x j)
    simp only [neg_zero] at this
    rw [← this]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le (by norm_num)] at ht
    exact hev t ⟨by linarith [ht.1], ht.2⟩
  rw [hneg, hfull] at hsplit
  linarith

/-- `F(1) = 0`. -/
theorem intG_one {x j : ℕ} (hx : 80 ≤ 2 * π * x) (hj : j < x) : intG x j 1 = 0 := by
  unfold intG
  have : ∫ t in (0 : ℝ)..1, GC x j (t * 1) = ∫ t in (0 : ℝ)..1, ((Gr x j t : ℝ) : ℂ) := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le (by norm_num)] at ht
    simp only [mul_one]
    rw [Cvs.Prolate.RungProfileEntireExtension.GC_ofReal hx hj ⟨by linarith [ht.1], ht.2⟩]
    rfl
  rw [this, intervalIntegral.integral_ofReal, integral_Gr_zero_one hx hj, Complex.ofReal_zero]

/-- **The ray transform of the mean**: `(w + ½) T_F(w) = A(w)` for `Im w > 0`. -/
theorem rayT_intG {x j : ℕ} (hx : 80 ≤ 2 * π * x) (hj : j < x) {w : ℂ} (hw : 0 < w.im) :
    (w + 1 / 2) * rayT (intG x j) w = Aw x j w := by
  have hF := differentiable_intG hx hj
  have h := Cvs.Prolate.Mellin.RayTransformEdgeSum.rayT_ibp hF hw
  rw [intG_one hx hj, mul_zero, zero_add] at h
  have hsub : rayT (fun ζ => ζ * deriv (intG x j) ζ) w = Aw x j w - rayT (intG x j) w := by
    have e : (fun ζ => ζ * deriv (intG x j) ζ) = fun ζ => GC x j ζ - intG x j ζ :=
      funext (mul_deriv_intG hx hj)
    rw [e, Cvs.Prolate.Mellin.RayTransformEdgeSum.Aw_eq_rayT]
    unfold rayT
    rw [← integral_sub (Cvs.Prolate.Mellin.RayTransformEdgeSum.integrableOn_integrand (Cvs.Prolate.RungProfileEntireExtension.differentiable_GC hx hj).continuous hw)
      (Cvs.Prolate.Mellin.RayTransformEdgeSum.integrableOn_integrand hF.continuous hw)]
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    ring
  rw [hsub] at h
  linear_combination h

/-- **The integral part is below the edge quantity**: beyond `8πx`, for `|σ| ≤ 1`,
`g‖T_F(σ + ig)‖ ≤ 4e⁶E_j/g`. -/
theorem g_norm_rayT_intG_le {x j : ℕ} (hx : 80 ≤ 2 * π * x) (hj : j < x) {σ : ℝ} (hσ : |σ| ≤ 1) {g : ℝ}
    (hg : 8 * π * x ≤ g) :
    g * ‖rayT (intG x j) (σ + g * I)‖ ≤ 4 * Real.exp 6 * Cvs.Prolate.Mellin.RungWindowLawRightEdge.edgeE x j / g := by
  have hg0 : 0 < g := lt_of_lt_of_le (by have := Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx; positivity) hg
  have hwi : 0 < ((σ : ℂ) + g * I).im := by simp [hg0]
  have h := rayT_intG hx hj hwi
  have hA := Cvs.Prolate.Mellin.RungUnitCircleLaw.g_norm_Aw_le hx hj hσ hg
  have hn : g ≤ ‖(σ : ℂ) + g * I + 1 / 2‖ := by
    have := Complex.abs_im_le_norm ((σ : ℂ) + g * I + 1 / 2)
    simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero,
      zero_add] at this
    have h12 : ((1 : ℂ) / 2).im = 0 := by norm_num
    rw [h12, add_zero, abs_of_pos hg0] at this
    exact this
  have hn0 : 0 < ‖(σ : ℂ) + g * I + 1 / 2‖ := lt_of_lt_of_le hg0 hn
  have hT : ‖rayT (intG x j) (σ + g * I)‖ = ‖Aw x j (σ + g * I)‖ / ‖(σ : ℂ) + g * I + 1 / 2‖ := by
    rw [← h, norm_mul, mul_div_cancel_left₀ _ hn0.ne']
  rw [hT, le_div_iff₀ hg0]
  have hE : 0 ≤ 4 * Real.exp 6 * Cvs.Prolate.Mellin.RungWindowLawRightEdge.edgeE x j := by have := Cvs.Prolate.Mellin.RungWindowLawRightEdge.edgeE_nonneg x j; positivity
  calc g * (‖Aw x j (σ + g * I)‖ / ‖(σ : ℂ) + g * I + 1 / 2‖) * g
      = g * ‖Aw x j (σ + g * I)‖ * (g / ‖(σ : ℂ) + g * I + 1 / 2‖) := by ring
    _ ≤ 4 * Real.exp 6 * Cvs.Prolate.Mellin.RungWindowLawRightEdge.edgeE x j * 1 := by
        refine mul_le_mul ?_ ((div_le_one hn0).2 hn) (by positivity) hE
        unfold Cvs.Prolate.Mellin.RungWindowLawRightEdge.edgeE; linarith
    _ = _ := mul_one _

end Cvs.Prolate.Mellin.RightEdgeIntegralPart

end
