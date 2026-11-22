import Mathlib
import Cvs.WeilForm.EImageRadical
import Cvs.WeilForm.MellinProfileStrips
import Cvs.WeilForm.ThetaSpaceParseval
import Cvs.Xi.EImageMellin
import Cvs.Xi.EImageWindowPoisson
import Cvs.Xi.WindowImageMellinClosed

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The window transform is the E-image transform minus the exterior transform

`E_G = k_G + 1_{(1,∞)}E_G` for `a > 0`. For `G` `C¹` on `[0, 1]` with `∫₀¹ G = 0` (no condition on `G(0)`) and
`Re w < 1`: `M[E_G](w) = a^w ζ₁(1 − w)(dslope Ĝ 1)(1 − w)`, so `M[k_G](w) = a^w ζ₁(1 − w)(dslope Ĝ 1)(1 − w)
− M[1_{(1,∞)}E_G](w)`. At a zero `ρ` of `ζ` with `0 < Re ρ < 1`, `M[k_G] = −M[1_{(1,∞)}E_G]` at `ρ` and `1 − ρ`.
-/

noncomputable section

open Real Set Filter Topology MeasureTheory Asymptotics
open Cvs.Xi.EImageWindowPoisson (eimage window eimage_of_lt)
open Cvs.WeilForm.ThetaSpaceParseval (mellinR)
open Cvs.WeilForm.MellinProfileStrips (gM gM_one)

namespace Cvs.Xi.WindowTransformExterior

/-- The exterior part `1_{(1,∞)}E_G` of the E-image. -/
def ext (a : ℝ) (G : ℝ → ℝ) : ℝ → ℝ := (Ioi (1 : ℝ)).indicator (eimage a G)

/-- **`E_G = k_G + 1_{(1,∞)}E_G`** pointwise, for `a > 0`. -/
theorem eimage_eq_window_add_ext {a : ℝ} (ha : 0 < a) (G : ℝ → ℝ) (θ : ℝ) :
    eimage a G θ = window a G θ + ext a G θ := by
  unfold window ext
  by_cases h1 : 1 < θ
  · rw [indicator_of_notMem (fun h => by linarith [h.2]), indicator_of_mem (show θ ∈ Ioi 1 from h1),
      zero_add]
  · rw [indicator_of_notMem (show θ ∉ Ioi 1 from h1), add_zero]
    by_cases h : θ ∈ Icc a 1
    · rw [indicator_of_mem h]
    · rw [indicator_of_notMem h]
      exact eimage_of_lt ha (lt_of_not_ge fun h' => h ⟨h', not_lt.1 h1⟩) G

/-- `Ĝ` is holomorphic on `Re z > 0` for `G` continuous on `[0, 1]`. -/
theorem differentiableOn_gM {G : ℝ → ℝ} (hGc : ContinuousOn G (Icc 0 1)) :
    DifferentiableOn ℂ (gM G) {z : ℂ | 0 < z.re} := by
  intro z (hz : 0 < z.re)
  refine DifferentiableAt.differentiableWithinAt ?_
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hGc
  have e : (fun u : ℝ => (((Ioc (0 : ℝ) 1).indicator G u : ℝ) : ℂ))
      = (Ioc (0 : ℝ) 1).indicator (fun u => (G u : ℂ)) := by
    funext u; by_cases h : u ∈ Ioc (0 : ℝ) 1 <;> simp [h]
  refine mellin_differentiableAt_of_isBigO_rpow (a := z.re + 1) (b := 0) ?_ ?_ (by linarith) ?_ hz
  · refine (Integrable.integrableOn ?_).locallyIntegrableOn
    rw [e]
    exact (integrable_indicator_iff measurableSet_Ioc).2
      ((Complex.continuous_ofReal.comp_continuousOn hGc).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
  · refine EventuallyEq.trans_isBigO ?_ (isBigO_zero _ _)
    filter_upwards [eventually_gt_atTop 1] with θ hθ
    have : θ ∉ Ioc (0 : ℝ) 1 := fun h => (not_le.2 hθ) h.2
    simp [this]
  · refine IsBigO.of_bound M ?_
    filter_upwards [self_mem_nhdsWithin] with θ (hθ : 0 < θ)
    rw [neg_zero, Real.rpow_zero, norm_one, mul_one, Complex.norm_real, Real.norm_eq_abs]
    by_cases h : θ ∈ Ioc (0 : ℝ) 1
    · rw [indicator_of_mem h]; simpa [Real.norm_eq_abs] using hM θ (Ioc_subset_Icc_self h)
    · rw [indicator_of_notMem h, abs_zero]
      exact (norm_nonneg _).trans (hM 0 (left_mem_Icc.2 zero_le_one))

/-- **The Mellin factorisation of the E-image without `G(0) = 0`**: for `G` `C¹` on `[0, 1]` with
`∫₀¹ G = 0` and `Re w < 1`, `M[E_G](w) = a^w ζ₁(1 − w)(dslope Ĝ 1)(1 − w)`, and `E_G` is Mellin-convergent. -/
theorem mellinR_eimage {a : ℝ} (ha : 0 < a) {G G₁ : ℝ → ℝ}
    (hG : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt G (G₁ u) u) (hG₁ : ContinuousOn G₁ (Icc 0 1))
    (hGi : ∫ u in (0 : ℝ)..1, G u = 0) {w : ℂ} (hw : w.re < 1) :
    MellinConvergent (fun θ => (eimage a G θ : ℂ)) w ∧
      mellinR (eimage a G) w = (a : ℂ) ^ w * riemannZeta₁ (1 - w) * dslope (gM G) 1 (1 - w) := by
  have hGc : ContinuousOn G (Icc 0 1) := fun u hu => (hG u hu).continuousAt.continuousWithinAt
  obtain ⟨K, -, hK⟩ := Cvs.Xi.EImageMellin.abs_eimage_le ha hG hG₁ hGi
  have hEm := Cvs.Xi.EImageMellin.measurable_eimage_of_continuousOn ha hGc
  have hloc := Cvs.Xi.EImageMellin.locallyIntegrableOn_of_le_div hEm hK
  have htop : ∀ z : ℂ, (fun θ => (eimage a G θ : ℂ)) =O[atTop] (· ^ (-(1 : ℝ))) := fun z => by
    refine IsBigO.of_bound K ?_
    filter_upwards [eventually_gt_atTop 0] with θ hθ
    rw [Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, Real.rpow_neg_one,
      abs_of_pos (inv_pos.2 hθ), ← div_eq_mul_inv]
    exact hK θ hθ
  have hbot : ∀ b : ℝ, (fun θ => (eimage a G θ : ℂ)) =O[𝓝[>] 0] (· ^ (-b)) := fun b => by
    refine EventuallyEq.trans_isBigO ?_ (isBigO_zero _ _)
    filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds ha)] with θ (hθ : θ < a)
    simp [eimage_of_lt ha hθ]
  refine ⟨mellinConvergent_of_isBigO_rpow hloc (htop w) hw (hbot (w.re - 1)) (by linarith), ?_⟩
  set U : Set ℂ := {w | w.re < 1}
  have hU : IsOpen U := isOpen_lt Complex.continuous_re continuous_const
  have hL : DifferentiableOn ℂ (mellinR (eimage a G)) U := fun z (hz : z.re < 1) =>
    (mellin_differentiableAt_of_isBigO_rpow hloc (htop z) hz (hbot (z.re - 1))
      (by linarith)).differentiableWithinAt
  have hopen0 : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hd : DifferentiableOn ℂ (dslope (gM G) 1) {s | 0 < s.re} :=
    (Complex.differentiableOn_dslope (hopen0.mem_nhds (by show (0 : ℝ) < (1 : ℂ).re; norm_num))).2
      (differentiableOn_gM hGc)
  have hR : DifferentiableOn ℂ
      (fun w : ℂ => (a : ℂ) ^ w * riemannZeta₁ (1 - w) * dslope (gM G) 1 (1 - w)) U := by
    intro z (hz : z.re < 1)
    refine DifferentiableAt.differentiableWithinAt ?_
    have h1 : DifferentiableAt ℂ (fun w : ℂ => (a : ℂ) ^ w) z :=
      differentiableAt_id.const_cpow (Or.inl (by exact_mod_cast ha.ne'))
    have h2 : DifferentiableAt ℂ (fun w : ℂ => riemannZeta₁ (1 - w)) z :=
      differentiable_riemannZeta₁.differentiableAt.comp z
        ((differentiableAt_const _).sub differentiableAt_id)
    have h3 : DifferentiableAt ℂ (fun w : ℂ => dslope (gM G) 1 (1 - w)) z := by
      have hz' : (1 - z) ∈ {s : ℂ | 0 < s.re} := by show 0 < (1 - z).re; simp; linarith
      exact ((hd.differentiableAt (hopen0.mem_nhds hz'))).comp z
        ((differentiableAt_const _).sub differentiableAt_id)
    exact (h1.mul h2).mul h3
  have hconv : Convex ℝ U := convex_halfSpace_re_lt 1
  have hmem : (-1 : ℂ) ∈ U := by show (-1 : ℂ).re < 1; norm_num
  have hev : mellinR (eimage a G) =ᶠ[𝓝 (-1 : ℂ)]
      fun w : ℂ => (a : ℂ) ^ w * riemannZeta₁ (1 - w) * dslope (gM G) 1 (1 - w) := by
    have hopen : IsOpen {w : ℂ | w.re < 0} := isOpen_lt Complex.continuous_re continuous_const
    filter_upwards [hopen.mem_nhds (show (-1 : ℂ).re < 0 by norm_num)] with z (hz : z.re < 0)
    rw [Cvs.Xi.EImageMellin.mellinR_eimage_of_re_neg ha hGc hz]
    have hz1 : 1 - z ≠ 1 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    rw [riemannZeta_eq_inv_sub_mul hz1, dslope_of_ne _ hz1, slope_def_module, gM_one hGi, sub_zero,
      smul_eq_mul]
    ring
  exact (hL.analyticOnNhd hU).eqOn_of_preconnected_of_eventuallyEq (hR.analyticOnNhd hU)
    hconv.isPreconnected hmem hev hw

/-- **The window transform as the E-image transform minus the exterior transform**: for `a > 0`, `G` `C¹` on
`[0, 1]` with `∫₀¹ G = 0` and `Re w < 1`, `M[k_G](w) = a^w ζ₁(1 − w)(dslope Ĝ 1)(1 − w) − M[1_{(1,∞)}E_G](w)`. -/
theorem mellinR_window_eq_sub {a : ℝ} (ha : 0 < a) {G G₁ : ℝ → ℝ}
    (hG : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt G (G₁ u) u) (hG₁ : ContinuousOn G₁ (Icc 0 1))
    (hGi : ∫ u in (0 : ℝ)..1, G u = 0) {w : ℂ} (hw : w.re < 1) :
    mellinR (window a G) w
      = (a : ℂ) ^ w * riemannZeta₁ (1 - w) * dslope (gM G) 1 (1 - w) - mellinR (ext a G) w := by
  have hGc : ContinuousOn G (Icc 0 1) := fun u hu => (hG u hu).continuousAt.continuousWithinAt
  obtain ⟨hEc, hE⟩ := mellinR_eimage ha hG hG₁ hGi hw
  have hWc := Cvs.Xi.WindowImageMellinClosed.mellinConvergent_window ha
    ((hGc.mono (Icc_subset_Icc ha.le le_rfl)).integrableOn_Icc) w
  rw [← hE]
  have e : mellinR (ext a G) w = mellinR (eimage a G) w - mellinR (window a G) w := by
    unfold mellinR mellin
    rw [← integral_sub hEc hWc]
    refine setIntegral_congr_fun measurableSet_Ioi fun θ _ => ?_
    simp only [smul_eq_mul]
    rw [eimage_eq_window_add_ext ha G θ]
    push_cast; ring
  rw [e]; ring

/-- `ζ₁` vanishes at the zeros of `ζ` other than `1`. -/
theorem riemannZeta₁_eq_zero {z : ℂ} (hz1 : z ≠ 1) (hz : riemannZeta z = 0) : riemannZeta₁ z = 0 := by
  rw [Cvs.WeilForm.EImageRadical.riemannZeta₁_eq hz1, hz, mul_zero]

/-- A zero of `ζ` in the critical strip reflects: `ζ(1 − ρ) = 0`. -/
theorem riemannZeta_one_sub_eq_zero {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) (hz : riemannZeta ρ = 0) :
    riemannZeta (1 - ρ) = 0 := by
  rw [riemannZeta_one_sub (fun n h => by
      have := congrArg Complex.re h; simp at this; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
    (fun h => by rw [h] at hρ1; simp at hρ1), hz, mul_zero]

/-- **At a zero, the window transform is minus the exterior transform**: if `ζ(1 − w) = 0`, `w ≠ 0` and
`Re w < 1`, then `M[k_G](w) = −M[1_{(1,∞)}E_G](w)`. -/
theorem mellinR_window_eq_neg_ext {a : ℝ} (ha : 0 < a) {G G₁ : ℝ → ℝ}
    (hG : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt G (G₁ u) u) (hG₁ : ContinuousOn G₁ (Icc 0 1))
    (hGi : ∫ u in (0 : ℝ)..1, G u = 0) {w : ℂ} (hw : w.re < 1) (hw0 : w ≠ 0)
    (hz : riemannZeta (1 - w) = 0) :
    mellinR (window a G) w = -mellinR (ext a G) w := by
  rw [mellinR_window_eq_sub ha hG hG₁ hGi hw,
    riemannZeta₁_eq_zero (fun h => hw0 (by linear_combination -h)) hz]
  ring

/-- **At a zero in the critical strip, on or off the line**: for `ζ(ρ) = 0` with `0 < Re ρ < 1`,
`M[k_G] = −M[1_{(1,∞)}E_G]` at `ρ` and at `1 − ρ`. -/
theorem mellinR_window_eq_neg_ext_of_zero {a : ℝ} (ha : 0 < a) {G G₁ : ℝ → ℝ}
    (hG : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt G (G₁ u) u) (hG₁ : ContinuousOn G₁ (Icc 0 1))
    (hGi : ∫ u in (0 : ℝ)..1, G u = 0) {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1)
    (hz : riemannZeta ρ = 0) :
    mellinR (window a G) ρ = -mellinR (ext a G) ρ ∧
      mellinR (window a G) (1 - ρ) = -mellinR (ext a G) (1 - ρ) := by
  refine ⟨mellinR_window_eq_neg_ext ha hG hG₁ hGi hρ1 (fun h => by rw [h] at hρ0; simp at hρ0)
    (riemannZeta_one_sub_eq_zero hρ0 hρ1 hz), mellinR_window_eq_neg_ext ha hG hG₁ hGi
    (by simp; linarith) (fun h => ?_) (by rw [sub_sub_cancel]; exact hz)⟩
  have := congrArg Complex.re h; simp at this; linarith

end Cvs.Xi.WindowTransformExterior
