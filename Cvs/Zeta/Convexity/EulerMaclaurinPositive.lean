import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Cvs.Zeta.Convexity.EulerMaclaurinKernel
import Cvs.Zeta.Convexity.EulerMaclaurinRightHalf

/-!
# The Euler–Maclaurin identity on `σ > 0`, and the polynomial bound

ζ₀(s) = 1 - s·∫₁^∞ {x}·x^{-s-1} dx for `0 < Re s` .
-/

open Complex MeasureTheory Set Filter Topology

namespace Cvs.ZetaGrowth

/-- The Euler–Maclaurin integrand as a Mellin weight: `{x}` cut off below `1`. -/
noncomputable def emF (x : ℝ) : ℂ :=
  Set.indicator (Set.Ici (1 : ℝ)) (fun y : ℝ => ((Int.fract y : ℝ) : ℂ)) x

theorem norm_emF_le (x : ℝ) : ‖emF x‖ ≤ 1 := by
  rw [emF]
  by_cases hx : x ∈ Set.Ici (1 : ℝ)
  · rw [Set.indicator_of_mem hx, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Int.fract_nonneg x)]
    exact le_of_lt (Int.fract_lt_one x)
  · rw [Set.indicator_of_notMem hx, norm_zero]; norm_num

theorem measurable_emF : Measurable emF := by
  refine (Complex.measurable_ofReal.comp measurable_fract).indicator measurableSet_Ici

theorem emF_eq_zero {x : ℝ} (hx : x < 1) : emF x = 0 := by
  rw [emF, Set.indicator_of_notMem (by simpa using hx)]

/-- **The Euler–Maclaurin integral is a Mellin transform.** -/
theorem em_eq_mellin (s : ℂ) :
    (∫ x in Ioi (1 : ℝ), Cvs.ZetaGrowth.emKernel s x) = mellin emF (-s) := by
  rw [mellin]
  have hstep : ∀ x : ℝ, (x : ℂ) ^ (-s - 1) • emF x
      = Set.indicator (Set.Ici (1 : ℝ)) (fun y : ℝ => Cvs.ZetaGrowth.emKernel s y) x := by
    intro x
    by_cases hx : x ∈ Set.Ici (1 : ℝ)
    · rw [emF, Set.indicator_of_mem hx, Set.indicator_of_mem hx, Cvs.ZetaGrowth.emKernel,
        smul_eq_mul, mul_comm]
    · rw [emF, Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, smul_zero]
  have harg : ∀ x : ℝ, (x : ℂ) ^ ((-s) - 1) • emF x
      = Set.indicator (Set.Ici (1 : ℝ)) (fun y : ℝ => Cvs.ZetaGrowth.emKernel s y) x := hstep
  simp_rw [harg]
  rw [MeasureTheory.setIntegral_indicator measurableSet_Ici]
  have hset : Ioi (0 : ℝ) ∩ Ici (1 : ℝ) = Ici (1 : ℝ) := by
    rw [Set.inter_eq_right]
    intro x hx
    exact lt_of_lt_of_le zero_lt_one (Set.mem_Ici.mp hx)
  rw [hset, MeasureTheory.integral_Ici_eq_integral_Ioi]

theorem locallyIntegrableOn_emF : LocallyIntegrableOn emF (Ioi (0 : ℝ)) := by
  intro x hx
  refine ⟨Ioo (x - 1) (x + 1), ?_, ?_⟩
  · exact nhdsWithin_le_nhds (Ioo_mem_nhds (by linarith) (by linarith))
  · refine Measure.integrableOn_of_bounded (M := 1) ?_ measurable_emF.aestronglyMeasurable ?_
    · rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top
    · exact Filter.Eventually.of_forall (fun y => norm_emF_le y)

theorem isBigO_emF_top : emF =O[atTop] (fun x : ℝ => x ^ (-(0 : ℝ))) := by
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
  rw [Real.rpow_neg (le_of_lt hx), Real.rpow_zero]
  simpa using norm_emF_le x

theorem isBigO_emF_bot (b : ℝ) : emF =O[𝓝[>] (0 : ℝ)] (fun x : ℝ => x ^ (-b)) := by
  refine Asymptotics.IsBigO.of_bound 0 ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with x hx
  rw [emF_eq_zero hx.2, norm_zero, zero_mul]

/-- **The Euler–Maclaurin integral is differentiable on `σ > 0`.**  It is a Mellin transform of
a bounded function supported on `[1,∞)`, so Mathlib's Mellin differentiability applies with
`a = 0` (the function is bounded at `∞`) and any `b` (it vanishes near `0`). -/
theorem differentiableAt_em {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (fun z : ℂ => ∫ x in Ioi (1 : ℝ), Cvs.ZetaGrowth.emKernel z x) s := by
  have hmel : DifferentiableAt ℂ (mellin emF) (-s) :=
    mellin_differentiableAt_of_isBigO_rpow (a := 0) (b := -s.re - 1)
      locallyIntegrableOn_emF isBigO_emF_top (by simp only [Complex.neg_re]; linarith)
      (isBigO_emF_bot _) (by simp only [Complex.neg_re]; linarith)
  have hneg : DifferentiableAt ℂ (fun z : ℂ => -z) s := (differentiable_id.neg).differentiableAt
  have hcomp := hmel.comp s hneg
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards with z
  exact em_eq_mellin z

/-- **The Euler–Maclaurin identity on the whole half-plane `σ > 0`.** ζ₀(s) = 1 - s·∫₁^∞
{x}·x^{-s-1} dx for `0 < Re s`. -/
theorem zeta₀_em {s : ℂ} (hs : 0 < s.re) :
    riemannZeta₀ s = 1 - s * ∫ x in Ioi (1 : ℝ), Cvs.ZetaGrowth.emKernel s x := by
  set U : Set ℂ := {z : ℂ | 0 < z.re} with hU
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUconn : IsPreconnected U := (convex_halfSpace_re_gt 0).isPreconnected
  set g : ℂ → ℂ := fun z => 1 - z * ∫ x in Ioi (1 : ℝ), Cvs.ZetaGrowth.emKernel z x with hg
  have hfA : AnalyticOnNhd ℂ riemannZeta₀ U :=
    (differentiable_riemannZeta₀.differentiableOn).analyticOnNhd hUopen
  have hgA : AnalyticOnNhd ℂ g U := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hUopen
    exact ((differentiableAt_const (1 : ℂ)).sub
      (differentiableAt_id.mul (differentiableAt_em hz))).differentiableWithinAt
  have h2 : (2 : ℂ) ∈ U := by
    rw [hU]; simp only [Set.mem_setOf_eq]; norm_num
  have heq : riemannZeta₀ =ᶠ[𝓝 (2 : ℂ)] g := by
    have hV : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by
        simp only [Set.mem_setOf_eq]; norm_num)
    filter_upwards [hV] with z hz
    have hzre : (1 : ℝ) < z.re := hz
    have hz1 : z ≠ 1 := by
      intro hc; rw [hc] at hzre; simp at hzre
    have hzne : z - 1 ≠ 0 := sub_ne_zero_of_ne hz1
    have hem := Cvs.ZetaGrowth.euler_maclaurin hzre
    rw [riemannZeta_eq_inv_sub_add hz1] at hem
    rw [hg]
    simp only
    field_simp at hem
    have hkey : (z - 1) * (riemannZeta₀ z
        - (1 - z * ∫ x in Ioi (1 : ℝ), Cvs.ZetaGrowth.emKernel z x)) = 0 := by
      linear_combination hem
    rcases mul_eq_zero.mp hkey with h | h
    · exact absurd h hzne
    · exact sub_eq_zero.mp h
  exact hfA.eqOn_of_preconnected_of_eventuallyEq hgA hUconn h2 heq hs

end Cvs.ZetaGrowth
