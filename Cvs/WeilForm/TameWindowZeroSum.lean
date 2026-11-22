import Mathlib
import Cvs.Approximant.ApproximantTransformFactors
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.Approximant.SpineCouplingTailPairing
import Cvs.Approximant.SpineSubspace
import Cvs.L2a.TailLogScaleTest
import Cvs.L2a.WindowFormTailLimit
import Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous
import Cvs.WeilForm.InfimumAttainedSphere
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.WeilForm.SelfConvolutionTransform
import Cvs.WeilForm.ThetaSpaceParseval
import Cvs.WeilForm.WeilFormAeClass
import Cvs.WeilForm.ZeroSideSampleMellin
import Cvs.Zeta.ExplicitFormula.CompactTestAdmissibility
import Cvs.Zeta.ExplicitFormula.EdgeJumpWindowTests
import Cvs.Zeta.ExplicitFormula.HannWindowShifts
import Cvs.Zeta.ExplicitFormula.WindowTransformCubicDecay
import Cvs.Zeta.GaussKernel.DivisorWeightCoordinates
import Cvs.Zeta.GaussKernel.ZetaZeroStatement
import Cvs.Zeta.ZeroSideMoments

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The window form of a tame window test is its zero sum; the spine bridge

For `2 ≤ x` and `v` tame on `[1/x, 1]`, `Q(w_v) = Σ_ρ m_ρ Re sqTransform_{log x}(fv x v)(zPoint ρ)` at
`P = x`, `R = ⌈log₂ x⌉`, the family summable. For `80 ≤ 2πx` and the spine vector of `a`, with `G` its profile:
`Q(spineMap x a) = Σ_ρ m_ρ Re(M[1_{(1,∞)}E_G](1 − ρ) M[1_{(1,∞)}E_G](ρ))`, the family summable.
-/

noncomputable section

open MeasureTheory Real Set Filter Complex

namespace Cvs.WeilForm.TameWindowZeroSum
open Cvs.ZeroCounting

open Cvs.WeilForm.SelfConvolutionTransform (cf)
open Cvs.L2a.WindowFormTailLimit (Tame)
open Cvs.WeilForm.ThetaSpaceParseval (mellinR)
open Cvs.Xi.EImageWindowPoisson (window)
open Cvs.WeilForm.ZeroSideSampleMellin (logWin)

/-! ### The envelope of a tame window test -/

/-- **A tame window test has a linear envelope on `|Im ξ| ≤ ½`**: for `v` tame on `[e^{−L}, 1]`,
`‖W_L(logWin L v)(ξ)‖ ≤ C/(1 + |Re ξ|)`. -/
theorem exists_envelope_logWin {L : ℝ} (hL : 0 ≤ L) {v : ℝ → ℝ} (hv : Tame v (Real.exp (-L)) 1) :
    ∃ C : ℝ, ∀ ξ : ℂ, |ξ.im| ≤ 1 / 2 →
      ‖Cvs.Detection.windowTransform L (cf (logWin L v)) ξ‖ ≤ C / (1 + |ξ.re|) := by
  obtain ⟨M, hM⟩ := hv.bdd
  obtain ⟨Cd, hCd⟩ := hv.dec
  refine ⟨2 * Real.exp (L / 2) * |Cd| + 2 * L * Real.exp (L / 2) * |M|, fun ξ hξ => ?_⟩
  have hr0 : 0 ≤ |ξ.re| := abs_nonneg _
  have he0 : 0 < Real.exp (L / 2) := Real.exp_pos _
  have hbig : 0 ≤ 2 * Real.exp (L / 2) * |Cd| := by positivity
  have hsmall : 0 ≤ 2 * L * Real.exp (L / 2) * |M| := by positivity
  rcases lt_or_ge |ξ.re| 1 with hr | hr
  · -- the crude bound
    have hsup : ∀ s ∈ Set.uIoc (0 : ℝ) L, ‖cf (logWin L v) s‖ ≤ |M| := by
      intro s hs
      rw [Set.uIoc_of_le hL] at hs
      simp only [cf, Complex.norm_real, Real.norm_eq_abs, logWin, Cvs.L2a.TailLogScaleTest.logScale,
        abs_mul, abs_of_pos (Real.exp_pos _)]
      have h1 : Real.exp ((s - L) / 2) ≤ 1 := Real.exp_le_one_iff.2 (by linarith [hs.2])
      calc |v (Real.exp (s - L))| * Real.exp ((s - L) / 2) ≤ |M| * 1 :=
            mul_le_mul ((hM _).trans (le_abs_self M)) h1 (Real.exp_pos _).le (abs_nonneg _)
        _ = |M| := mul_one _
    have hcr := Cvs.Detection.norm_windowTransform_le hL hsup ξ
    have hexp : Real.exp (L * |ξ.im|) ≤ Real.exp (L / 2) :=
      Real.exp_le_exp.2 (by nlinarith)
    have h1 : ‖Cvs.Detection.windowTransform L (cf (logWin L v)) ξ‖
        ≤ L * Real.exp (L / 2) * |M| := by
      refine hcr.trans ?_
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hexp (abs_nonneg M)) hL
    refine h1.trans ?_
    rw [le_div_iff₀ (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg hL he0.le) (abs_nonneg M)]
  · -- the Mellin decay
    rw [Cvs.WeilForm.ZeroSideSampleMellin.windowTransform_logWin hL hv.supp, norm_mul,
      Cvs.Approximant.ApproximantTransformFactors.norm_char]
    set s : ℂ := 1 / 2 - ξ * I with hs
    have hsre : s.re = 1 / 2 + ξ.im := by simp [hs]
    have hsim : s.im = -ξ.re := by simp [hs]
    have habs := abs_le.1 hξ
    have hd := hCd s (by rw [hsre]; linarith) (by rw [hsre]; linarith)
      (by rw [hsim, abs_neg]; exact hr)
    rw [hsim, abs_neg] at hd
    have hpos : 0 < |ξ.re| := by linarith
    have hd' : ‖mellinR v s‖ ≤ 2 * |Cd| / (1 + |ξ.re|) := by
      refine hd.trans ?_
      rw [div_le_div_iff₀ hpos (by positivity)]
      nlinarith [le_abs_self Cd, abs_nonneg Cd]
    have hexp : Real.exp (L * ξ.im) ≤ Real.exp (L / 2) :=
      Real.exp_le_exp.2 (by nlinarith)
    calc Real.exp (L * ξ.im) * ‖mellinR v s‖
        ≤ Real.exp (L / 2) * (2 * |Cd| / (1 + |ξ.re|)) :=
          mul_le_mul hexp hd' (norm_nonneg _) he0.le
      _ = (2 * Real.exp (L / 2) * |Cd|) / (1 + |ξ.re|) := by ring
      _ ≤ _ := div_le_div_of_nonneg_right (by linarith) (by positivity)

/-! ### Cutting a test to the window -/

/-- The window transform only sees `(0, L]`: `W_L(1_{(0,L]} f) = W_L f`. -/
theorem windowTransform_indicator {L : ℝ} (hL : 0 ≤ L) (f : ℝ → ℝ) (ξ : ℂ) :
    Cvs.Detection.windowTransform L (cf ((Ioc (0 : ℝ) L).indicator f)) ξ
      = Cvs.Detection.windowTransform L (cf f) ξ := by
  unfold Cvs.Detection.windowTransform
  rw [intervalIntegral.integral_of_le hL, intervalIntegral.integral_of_le hL]
  refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
  simp [cf, indicator_of_mem hs]

theorem sqTransform_indicator {L : ℝ} (hL : 0 ≤ L) (f : ℝ → ℝ) :
    Cvs.Detection.sqTransform L (cf ((Ioc (0 : ℝ) L).indicator f))
      = Cvs.Detection.sqTransform L (cf f) := by
  funext ξ
  unfold Cvs.Detection.sqTransform
  rw [windowTransform_indicator hL, windowTransform_indicator hL]

/-! ### The general bridge for tame window tests -/

/-- **The window form of a tame window test is its zero sum**: for `2 ≤ x` and `v` tame on `[1/x, 1]`,
at `P = x`, `R = ⌈log₂ x⌉`, `Q(w_v) = kernelZeroSide(sqTransform_{log x}(fv x v))`, the zero family summable. -/
theorem Q_wv_eq_kernelZeroSide {x : ℕ} (hx : 2 ≤ x) {v : ℝ → ℝ} (hv : Tame v (1 / x) 1)
    (lam a : ℝ) :
    Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) x (Nat.clog 2 x)
        (Cvs.Approximant.SpineCouplingTailPairing.wv (Nat.cast_pos.mpr (by omega)) hv)
      = kernelZeroSide (Cvs.Detection.sqTransform (Real.log x) (cf (Cvs.Approximant.SpineCouplingTailPairing.fv x v))) lam a
    ∧ Summable fun rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet =>
        (Cvs.Criterion.divisorWeight rho : ℝ)
          * (Cvs.Detection.sqTransform (Real.log x) (cf (Cvs.Approximant.SpineCouplingTailPairing.fv x v)) (zPoint rho)).re := by
  have hx0 : (0 : ℝ) < x := Nat.cast_pos.mpr (by omega)
  obtain ⟨hL, hP, hR⟩ := Cvs.Approximant.SpineSubspace.sizes x hx
  set L := Real.log x with hLdef
  have hα : (1 : ℝ) / x = Real.exp (-L) := by rw [Real.exp_neg, Real.exp_log hx0, one_div]
  have hv' : Tame v (Real.exp (-L)) 1 := hα ▸ hv
  set g : ℝ → ℝ := (Ioc (0 : ℝ) L).indicator (Cvs.Approximant.SpineCouplingTailPairing.fv x v) with hg
  have hfm : Measurable (Cvs.Approximant.SpineCouplingTailPairing.fv x v) := by
    unfold Cvs.Approximant.SpineCouplingTailPairing.fv Cvs.L2a.TailLogScaleTest.logScale
    exact (hv.meas.comp (by fun_prop)).mul (by fun_prop)
  have hgae : g =ᵐ[volume] Cvs.Approximant.SpineCouplingTailPairing.fv x v := by
    filter_upwards [Cvs.Approximant.SpineCouplingTailPairing.fv_ae_supp hx0 hv] with s hs
    by_cases h : s ∈ Ioc (0 : ℝ) L
    · simp [hg, indicator_of_mem h]
    · rw [hg, indicator_of_notMem h, hs h]
  have hgmem : MemLp g 2 volume := (Cvs.Approximant.SpineCouplingTailPairing.fv_memLp hv).indicator measurableSet_Ioc.nullMeasurableSet
  have hgm : Measurable g := hfm.indicator measurableSet_Ioc
  have hgs : ∀ s ∉ Ioc (0 : ℝ) L, g s = 0 := fun s hs => indicator_of_notMem hs _
  have hglevy : IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy g) (Ioi 0) volume := by
    rw [Cvs.Approximant.SpineSubspace.levy_congr_ae hgae]; exact Cvs.Approximant.SpineCouplingTailPairing.fv_levy hv
  obtain ⟨C, hC⟩ := exists_envelope_logWin hL.le hv'
  have henv : ∀ ξ : ℂ, |ξ.im| ≤ 1 / 2 →
      ‖Cvs.Detection.windowTransform L (cf g) ξ‖ ≤ C / (1 + |ξ.re|) := by
    intro ξ hξ
    rw [hg, windowTransform_indicator hL.le]
    exact hC ξ hξ
  have hmain := Cvs.Zeta.ExplicitFormula.EdgeJumpWindowTests.kernelZeroSide_eq_weilForm_of_envelope hL hgmem hgm hgs
    hglevy henv lam a hP hR
  rw [hg, sqTransform_indicator hL.le] at hmain
  refine ⟨?_, hmain.2⟩
  rw [hmain.1, ← hg, Cvs.WeilForm.WeilFormAeClass.weilForm_congr_ae _ _ hgae]
  exact Cvs.Approximant.SpineSubspace.Q_ofFun _ _ _ _ _ _

/-! ### The spine bridge -/

/-- The spine profile is `C¹` on `[0, 1]` with mean zero there. -/
theorem spineG_std {x : ℕ} (hx : 80 ≤ 2 * π * x) (a : Cvs.Approximant.SpineSubspace.SF x → ℝ) :
    ∃ G₁ : ℝ → ℝ, (∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a) (G₁ u) u)
      ∧ ContinuousOn G₁ (Icc 0 1) ∧ ∫ u in (0 : ℝ)..1, Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a u = 0 := by
  obtain ⟨G₁, G₂, hG, hG₁, -, heven, hGi⟩ := Cvs.Approximant.SpineCouplingTailPairing.spine_profile_data hx (Cvs.Approximant.SpineSubspace.SF_lt x) a
  exact ⟨G₁, Cvs.L2a.WindowFormTailLimit.std_of_even hG hG₁ heven hGi⟩

end Cvs.WeilForm.TameWindowZeroSum
