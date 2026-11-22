import Mathlib
import Cvs.Approximant.SpineCouplingTailPairing
import Cvs.L2a.TailLogScaleTest
import Cvs.L2a.WindowFormTailLimit
import Cvs.Route.L1FloorFromBulkD0
import Cvs.Route.WindowPositivityBulkCoupling
import Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous
import Cvs.WeilForm.CouplingFromTameDensity
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.FormLscDomainClosed
import Cvs.WeilForm.InfimumAttainedSphere
import Cvs.WeilForm.Mollify.ComposedApproximant
import Cvs.WeilForm.Mollify.ContinuousApproximation
import Cvs.WeilForm.Mollify.MollifySmooth
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.WeilForm.SymmetricBilinearForm
import Cvs.WeilForm.ThetaSpaceParseval
import Cvs.WeilForm.WeilFormAeClass
import Cvs.WeilForm.WeilFormHomogeneous
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowConstraintSet
import Cvs.WeilForm.WindowFormNormFloor
import Cvs.WeilForm.WindowRepresentative
import Cvs.Zeta.WeilPositivityStatement

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The tame classes are form-norm dense in the form domain

For symmetric `B` with `c‖u‖² ≤ B(u, u)`, lower semicontinuous along norm limits, `s_n → w` and `B(s_n) → B(w)`
give `B(s_n − w) → 0`, by `B(s − w) = 2B(s) + 2B(w) − B(s + w)`. `ContinuousApproximation`'s smooth window approximants
`g_n` of `w` have `g_n → w` in `L²` and `Q(g_n) → Q(w)`, and `θ ↦ 1_{[1/x,1)}(θ) g_n(log θ + log x)/√θ` is tame
with class `g_n`, so the tame classes are dense for `‖·‖` and `Q` jointly: `TameDense` holds.
-/

noncomputable section

open MeasureTheory Real Filter Topology Set

namespace Cvs.WeilForm.TameClassesFormDense
open Cvs.ZeroCounting

section Generic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Value convergence is form convergence under lower semicontinuity**: for symmetric `B` with
`c‖u‖² ≤ B(u, u)` and `B(y₀) ≤ liminf B(y_n)` along every norm limit, `s_n → w` and `B(s_n) → B(w)` give
`B(s_n − w) → 0`. -/
theorem tendsto_sub_of_lsc {B : LinearMap.BilinForm ℝ E} (hB : B.IsSymm) {c : ℝ}
    (hc : ∀ u, c * ‖u‖ ^ 2 ≤ B u u)
    (hlsc : ∀ (y : ℕ → E) (y₀ : E), Tendsto y atTop (𝓝 y₀) → ∀ ε > 0,
      ∀ᶠ n in atTop, B y₀ y₀ - ε ≤ B (y n) (y n))
    {s : ℕ → E} {w : E} (hs : Tendsto s atTop (𝓝 w))
    (hQ : Tendsto (fun n => B (s n) (s n)) atTop (𝓝 (B w w))) :
    Tendsto (fun n => B (s n - w) (s n - w)) atTop (𝓝 0) := by
  have hpar : ∀ n, B (s n - w) (s n - w) = 2 * B (s n) (s n) + 2 * B w w - B (s n + w) (s n + w) :=
    fun n => by
      simp only [map_sub, map_add, LinearMap.sub_apply, LinearMap.add_apply]
      rw [hB.eq w (s n)]; ring
  have h2w : B (w + w) (w + w) = 4 * B w w := by
    simp only [map_add, LinearMap.add_apply]; ring
  have hsw : Tendsto (fun n => s n + w) atTop (𝓝 (w + w)) := hs.add tendsto_const_nhds
  have hnorm : Tendsto (fun n => ‖s n - w‖) atTop (𝓝 0) := (tendsto_iff_norm_sub_tendsto_zero).1 hs
  have hlow : Tendsto (fun n => c * ‖s n - w‖ ^ 2) atTop (𝓝 0) := by
    simpa using (hnorm.pow 2).const_mul c
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · filter_upwards [hlow.eventually (lt_mem_nhds ha)] with n hn
    exact hn.trans_le (hc _)
  · have hε : 0 < b / 2 := by linarith
    have hup : Tendsto (fun n => 2 * B (s n) (s n) + 2 * B w w) atTop (𝓝 (4 * B w w)) := by
      have := (hQ.const_mul 2).add_const (2 * B w w); convert this using 2; ring
    filter_upwards [hlsc _ _ hsw (b / 2) hε, hup.eventually (gt_mem_nhds (by linarith :
      4 * B w w < 4 * B w w + b / 2))] with n h1 h2
    rw [hpar n]; rw [h2w] at h1; linarith

end Generic

/-! ### Lower semicontinuity of the window form at `x` -/

open Cvs.L2a.WindowFormTailLimit (Tame)
open Cvs.Route.L1FloorFromBulkD0 (Dom Bx)

/-- **The window form is lower semicontinuous along norm limits** in the form domain at `x`. -/
theorem lsc_Qx {x : ℕ} (y : ℕ → Dom x) (y₀ : Dom x) (hy : Tendsto y atTop (𝓝 y₀)) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, Cvs.Route.WindowPositivityBulkCoupling.Qx x y₀ - ε ≤ Cvs.Route.WindowPositivityBulkCoupling.Qx x (y n) := by
  by_contra hne
  rw [Filter.not_eventually] at hne
  obtain ⟨φ, hφ, hlt⟩ := Filter.extraction_of_frequently_atTop hne
  have hcont : Continuous fun z : Dom x =>
      (((z : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)) : Lp ℝ 2 (volume : Measure ℝ))) :=
    continuous_subtype_val.comp continuous_subtype_val
  have hlim : Tendsto (fun k => (((y (φ k) : Dom x) : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)) :
      Lp ℝ 2 (volume : Measure ℝ))) atTop
      (𝓝 (((y₀ : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)) : Lp ℝ 2 (volume : Measure ℝ)))) :=
    (hcont.tendsto y₀).comp (hy.comp hφ.tendsto_atTop)
  have h := Cvs.WeilForm.FormLscDomainClosed.lsc (Real.log_natCast_nonneg x) x (Nat.clog 2 x) (c := Cvs.Route.WindowPositivityBulkCoupling.Qx x y₀ - ε)
    (fun k => y (φ k)) (fun k => (not_le.1 (hlt k)).le) hlim
  have : Cvs.Route.WindowPositivityBulkCoupling.Qx x y₀ ≤ Cvs.Route.WindowPositivityBulkCoupling.Qx x y₀ - ε := h.2
  linarith

/-! ### A smooth window function as a tame test -/

/-- The test `θ ↦ 1_{[1/x, 1)}(θ) g(log θ + log x)/√θ`, whose class at `x` is `g`. -/
def ofWin (x : ℕ) (g : ℝ → ℝ) : ℝ → ℝ :=
  (Ico (1 / (x : ℝ)) 1).indicator fun θ => g (Real.log θ + Real.log x) / √θ

/-- The profile `θ ↦ g(log θ + log x)/√θ` is continuous at every `θ > 0`. -/
theorem continuousAt_prof (x : ℕ) {g : ℝ → ℝ} (hg : Continuous g) {θ : ℝ} (hθ : 0 < θ) :
    ContinuousAt (fun θ => g (Real.log θ + Real.log x) / √θ) θ :=
  (hg.continuousAt.comp ((Real.continuousAt_log hθ.ne').add continuousAt_const)).div
    Real.continuous_sqrt.continuousAt (Real.sqrt_pos.2 hθ).ne'

/-- **A `C¹` function is a tame test after the change of variable**: `ofWin x g` is tame on `[1/x, 1]`. -/
theorem tame_ofWin {x : ℕ} (hx0 : (0 : ℝ) < x) {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) :
    Tame (ofWin x g) (1 / x) 1 := by
  have ha : (0 : ℝ) < 1 / x := one_div_pos.2 hx0
  set h : ℝ → ℝ := fun θ => g (Real.log θ + Real.log x) / √θ with hh
  have hgc : Continuous g := hg.continuous
  have hcon : ContinuousOn h (Icc (1 / x) 1) := fun θ hθ =>
    (continuousAt_prof x hgc (ha.trans_le hθ.1)).continuousWithinAt
  refine ⟨ha, fun θ hθ => ?_, ?_, ?_, ?_⟩
  · exact indicator_of_notMem (fun h' => hθ (Ico_subset_Icc_self h')) _
  · refine Measurable.indicator ?_ measurableSet_Ico
    exact (hgc.measurable.comp (Real.measurable_log.add_const _)).div
      Real.continuous_sqrt.measurable
  · obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcon
    refine ⟨max M 0, fun θ => ?_⟩
    by_cases hθ : θ ∈ Ico (1 / (x : ℝ)) 1
    · rw [ofWin, indicator_of_mem hθ]
      exact (hM θ (Ico_subset_Icc_self hθ)).trans (le_max_left _ _)
    · rw [ofWin, indicator_of_notMem hθ, abs_zero]; exact le_max_right _ _
  · -- one `C¹` piece on `[1/x, 1)`
    set g₁ : ℝ → ℝ := deriv g
    have hg₁ : Continuous g₁ := hg.continuous_deriv le_rfl
    set h₁ : ℝ → ℝ := fun θ =>
      (g₁ (Real.log θ + Real.log x) * θ⁻¹ * √θ - g (Real.log θ + Real.log x) * (1 / (2 * √θ)))
        / √θ ^ 2
    have hder : ∀ θ, 0 < θ → HasDerivAt h (h₁ θ) θ := fun θ hθ => by
      have hl : HasDerivAt (fun θ => Real.log θ + Real.log x) θ⁻¹ θ := by
        simpa using (Real.hasDerivAt_log hθ.ne').add_const (Real.log x)
      have hgd : HasDerivAt (fun θ => g (Real.log θ + Real.log x))
          (g₁ (Real.log θ + Real.log x) * θ⁻¹) θ :=
        ((hg.differentiable one_ne_zero).differentiableAt.hasDerivAt).comp θ hl
      exact hgd.div (Real.hasDerivAt_sqrt hθ.ne') (Real.sqrt_pos.2 hθ).ne'
    have hcon₁ : ContinuousOn h₁ (uIcc (1 / x) 1) := by
      intro θ hθ
      have hθ0 : 0 < θ := by
        rcases le_total (1 / (x : ℝ)) 1 with hle | hle
        · rw [uIcc_of_le hle] at hθ; exact ha.trans_le hθ.1
        · rw [uIcc_of_ge hle] at hθ; linarith [hθ.1]
      have hs : 0 < √θ := Real.sqrt_pos.2 hθ0
      have hlog : ContinuousAt (fun θ => Real.log θ + Real.log x) θ :=
        (Real.continuousAt_log hθ0.ne').add continuousAt_const
      have hs2 : √θ ^ 2 ≠ 0 := pow_ne_zero 2 hs.ne'
      have hs3 : (2 : ℝ) * √θ ≠ 0 := mul_ne_zero two_ne_zero hs.ne'
      refine ContinuousAt.continuousWithinAt ?_
      refine ContinuousAt.div ?_ (Real.continuous_sqrt.continuousAt.pow 2) hs2
      refine ContinuousAt.sub ?_ ?_
      · exact ((hg₁.continuousAt.comp hlog).mul (continuousAt_inv₀ hθ0.ne')).mul
          Real.continuous_sqrt.continuousAt
      · exact (hgc.continuousAt.comp hlog).mul (continuousAt_const.div
          (continuousAt_const.mul Real.continuous_sqrt.continuousAt) hs3)
    obtain ⟨C, hC⟩ := Cvs.L2a.WindowFormTailLimit.dec_of_pieces (v := ofWin x g) (Finset.univ : Finset Unit) (fun _ => 1 / (x : ℝ))
      (fun _ => 1) (fun _ => h) (fun _ => h₁) (fun _ _ => ha) (fun _ _ => hcon)
      (fun _ _ θ hθ => hder θ (ha.trans hθ.1)) (fun _ _ => hcon₁.intervalIntegrable)
      (Filter.Eventually.of_forall fun θ => by simp [ofWin, h])
    exact ⟨C, hC⟩

/-- **The class of `ofWin x g` is `g`**: `fv x (ofWin x g) = g` off `log x`, for `g` vanishing off `(0, log x]`. -/
theorem fv_ofWin_ae {x : ℕ} (hx0 : (0 : ℝ) < x) {g : ℝ → ℝ}
    (hgs : ∀ s ∉ Ioc (0 : ℝ) (Real.log x), g s = 0) : Cvs.Approximant.SpineCouplingTailPairing.fv x (ofWin x g) =ᵐ[volume] g := by
  have hne : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ Real.log x := by
    simp [ae_iff, measure_singleton]
  filter_upwards [hne] with s hs
  have hθ : 0 < Real.exp (s - Real.log x) := Real.exp_pos _
  simp only [Cvs.Approximant.SpineCouplingTailPairing.fv, Cvs.L2a.TailLogScaleTest.logScale, ofWin]
  by_cases hmem : Real.exp (s - Real.log x) ∈ Ico (1 / (x : ℝ)) 1
  · rw [indicator_of_mem hmem, Real.log_exp, sub_add_cancel, ← Real.exp_half, div_mul_cancel₀]
    exact (Real.exp_pos _).ne'
  · rw [indicator_of_notMem hmem, zero_mul]
    refine (hgs s fun hs' => hmem ⟨?_, ?_⟩).symm
    · have h1 : 1 / (x : ℝ) = Real.exp (-Real.log x) := by
        rw [Real.exp_neg, Real.exp_log hx0, one_div]
      rw [h1, Real.exp_le_exp]; linarith [hs'.1]
    · rw [← Real.exp_zero, Real.exp_lt_exp]; exact sub_neg.2 (lt_of_le_of_ne hs'.2 hs)

/-! ### Density -/

/-- The window norm of a class is the square root of its self-convolution at `0`. -/
theorem norm_sq_eq {L : ℝ} (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) {f : ℝ → ℝ}
    (h : ((φ : Lp ℝ 2 (volume : Measure ℝ)) : ℝ → ℝ) =ᵐ[volume] f) :
    ‖φ‖ ^ 2 = ∫ t, f t ^ 2 := by
  rw [← (Cvs.WeilForm.WindowRepresentative.weilQW_rep 0 0 φ).2, Cvs.WeilForm.WeilFormAeClass.selfConvolution_congr_ae ((Cvs.WeilForm.WindowRepresentative.ae_eq_rep φ).symm.trans h)]
  simp only [Cvs.Zeta.Explicit.Weil.selfConvolution, add_zero, sq]

/-- **Smooth window approximants with their windows**: every `w` in the form domain at `x` is the limit in norm
and form of the classes of `ofWin x g_n` with `g_n ∈ C¹` vanishing off `(0, log x]`. -/
theorem exists_ofWin_approx {x : ℕ} (hx0 : (0 : ℝ) < x) (w : Dom x) :
    ∃ (g : ℕ → ℝ → ℝ) (hg : ∀ n, ContDiff ℝ 1 (g n)), (∀ n, ∀ s ∉ Ioc (0 : ℝ) (Real.log x), g n s = 0) ∧
      Tendsto (fun n => ‖Cvs.Approximant.SpineCouplingTailPairing.wv hx0 (tame_ofWin hx0 (hg n)) - w‖) atTop (𝓝 0) ∧
      Tendsto (fun n => Cvs.Route.WindowPositivityBulkCoupling.Qx x (Cvs.Approximant.SpineCouplingTailPairing.wv hx0 (tame_ofWin hx0 (hg n)) - w)) atTop (𝓝 0) := by
  set L := Real.log x with hLdef
  by_cases hw0 : w = 0
  · -- the zero class: `g = 0`
    subst hw0
    have h0 : Cvs.Approximant.SpineCouplingTailPairing.wv hx0 (tame_ofWin hx0 (g := fun _ => (0 : ℝ)) contDiff_const) = 0 := by
      apply Subtype.ext; apply Subtype.ext; apply Lp.ext
      refine (Cvs.Approximant.SpineCouplingTailPairing.coe_wv_ae hx0 _).trans ((fv_ofWin_ae hx0 fun _ _ => rfl).trans ?_)
      exact (Lp.coeFn_zero ℝ 2 volume).symm
    refine ⟨fun _ _ => 0, fun _ => contDiff_const, fun _ _ _ => rfl, ?_, ?_⟩
    · refine tendsto_const_nhds.congr' (Filter.Eventually.of_forall fun n => ?_)
      show (0 : ℝ) = ‖Cvs.Approximant.SpineCouplingTailPairing.wv hx0 (tame_ofWin hx0 (g := fun _ => (0 : ℝ)) contDiff_const) - 0‖
      rw [h0, sub_self]; simp
    · refine tendsto_const_nhds.congr' (Filter.Eventually.of_forall fun n => ?_)
      show (0 : ℝ) = Cvs.Route.WindowPositivityBulkCoupling.Qx x (Cvs.Approximant.SpineCouplingTailPairing.wv hx0 (tame_ofWin hx0 (g := fun _ => (0 : ℝ)) contDiff_const) - 0)
      rw [h0, sub_self]; exact (Cvs.WeilForm.SymmetricBilinearForm.Q_zero _ _ _).symm
  set N := ‖w‖ with hN
  have hN0 : 0 < N := norm_pos_iff.2 hw0
  set w' : Dom x := N⁻¹ • w with hw'
  set η : ℝ → ℝ := Cvs.WeilForm.WindowRepresentative.rep (w' : Cvs.WeilForm.WeilFormOnWindowL2.window L) with hη
  have hw'n : ‖w'‖ = 1 := by
    have h1 : ‖w'‖ = ‖N⁻¹ • (((w : Dom x) : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ))‖ := rfl
    have h2 : ‖(((w : Dom x) : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ))‖ = N := rfl
    rw [h1, norm_smul, h2, norm_inv, Real.norm_eq_abs, abs_of_pos hN0, inv_mul_cancel₀ hN0.ne']
  have hηwin : η ∈ Cvs.WeilForm.WindowConstraintSet.windowSet L := by
    refine ⟨Cvs.WeilForm.WindowRepresentative.memLp_rep _, Cvs.WeilForm.WindowRepresentative.rep_supp _, ?_, Cvs.WeilForm.FormDomain.hdom_of_mem w'⟩
    have h := norm_sq_eq (w' : Cvs.WeilForm.WeilFormOnWindowL2.window L) (Cvs.WeilForm.WindowRepresentative.ae_eq_rep _)
    rw [← h]; exact (by rw [show ‖(w' : Cvs.WeilForm.WeilFormOnWindowL2.window L)‖ = ‖w'‖ from rfl, hw'n]; norm_num)
  -- a nonzero class forces `log x > 0`: at `log x = 0` the window `(0, log x]` is empty
  have hL : 0 < L := by
    have hL0 : 0 ≤ L := Real.log_natCast_nonneg x
    rcases hL0.lt_or_eq with h | h
    · exact h
    · have h0 : ∀ s, η s = 0 := fun s => hηwin.2.1 s fun hs => by linarith [hs.1, hs.2]
      have h1 := hηwin.2.2.1
      simp only [h0] at h1
      norm_num at h1
  have hηm : Measurable η :=
    (Lp.stronglyMeasurable _).measurable.indicator measurableSet_Ioc
  obtain ⟨Ξ, hΞwin, -, hΞL2, hΞform, hΞeq⟩ :=
    Cvs.WeilForm.Mollify.ContinuousApproximation.exists_windowApprox hL x (Nat.clog 2 x) hηwin hηm
  set g : ℕ → ℝ → ℝ := fun n s => N * Ξ n s with hg
  have hgC : ∀ n, ContDiff ℝ 1 (g n) := fun n => by
    obtain ⟨c, m, hcm⟩ := hΞeq n
    have hpre : ContDiff ℝ 1 (Cvs.WeilForm.Mollify.ComposedApproximant.pre hL η m) :=
      Cvs.WeilForm.Mollify.MollifySmooth.contDiff_conv (Cvs.WeilForm.Mollify.ComposedApproximant.memLp_shifted hηwin.1 L m) (Cvs.WeilForm.Mollify.ComposedApproximant.shift_pos hL m)
    simp only [hg, hcm]
    exact contDiff_const.mul (contDiff_const.mul hpre)
  have hgs : ∀ n, ∀ s ∉ Ioc (0 : ℝ) L, g n s = 0 := fun n s hs => by
    simp only [hg, (hΞwin n).2.1 s hs, mul_zero]
  set S : ℕ → Dom x := fun n => Cvs.Approximant.SpineCouplingTailPairing.wv hx0 (tame_ofWin hx0 (hgC n)) with hS
  have hSae : ∀ n, (((S n : Dom x) : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ)) =ᵐ[volume] g n :=
    fun n => (Cvs.Approximant.SpineCouplingTailPairing.coe_wv_ae hx0 _).trans (fv_ofWin_ae hx0 (hgs n))
  have hwae : (((w : Dom x) : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ))
      =ᵐ[volume] fun t => N * η t := by
    have hww : w = N • w' := by rw [hw', smul_smul, mul_inv_cancel₀ hN0.ne', one_smul]
    have h1 : (((N • w' : Dom x) : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ))
        = N • (((w' : Dom x) : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ)) := rfl
    rw [hww, h1]
    filter_upwards [Lp.coeFn_smul N (((w' : Dom x) : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ)),
      Cvs.WeilForm.WindowRepresentative.ae_eq_rep (w' : Cvs.WeilForm.WeilFormOnWindowL2.window L)] with t ht1 ht2
    rw [ht1, Pi.smul_apply, smul_eq_mul]
    exact congrArg _ ht2
  -- the norm
  have hnorm_sq : ∀ n, ‖S n - w‖ ^ 2 = N ^ 2 * ∫ t, (Ξ n t - η t) ^ 2 := fun n => by
    have hae : ((((S n - w : Dom x) : Cvs.WeilForm.WeilFormOnWindowL2.window L)) : Lp ℝ 2 (volume : Measure ℝ))
        =ᵐ[volume] fun t => N * (Ξ n t - η t) := by
      have hc : ((((S n - w : Dom x) : Cvs.WeilForm.WeilFormOnWindowL2.window L)) : Lp ℝ 2 (volume : Measure ℝ))
          = (((S n : Dom x) : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ))
            - (((w : Dom x) : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ)) := rfl
      rw [hc]
      filter_upwards [Lp.coeFn_sub (((S n : Dom x) : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ))
        (((w : Dom x) : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ)), hSae n, hwae]
        with t h1 h2 h3
      rw [h1, Pi.sub_apply, h2, h3, hg]; ring
    rw [show ‖S n - w‖ = ‖((S n - w : Dom x) : Cvs.WeilForm.WeilFormOnWindowL2.window L)‖ from rfl, norm_sq_eq _ hae,
      ← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun t => by ring)
  have hnorm : Tendsto (fun n => ‖S n - w‖) atTop (𝓝 0) := by
    have h2 : Tendsto (fun n => ‖S n - w‖ ^ 2) atTop (𝓝 0) := by
      simp_rw [hnorm_sq]; simpa using hΞL2.const_mul (N ^ 2)
    have := h2.sqrt
    simpa [Real.sqrt_sq (norm_nonneg _)] using this
  -- the form values
  have hQS : ∀ n, Cvs.Route.WindowPositivityBulkCoupling.Qx x (S n) = N ^ 2 * Cvs.WeilForm.SelfConvolutionFunctional.weilForm x (Nat.clog 2 x) (Ξ n) := fun n => by
    show Cvs.WeilForm.WindowRepresentative.weilQW x (Nat.clog 2 x) ((S n : Dom x) : Cvs.WeilForm.WeilFormOnWindowL2.window L) = _
    rw [Cvs.WeilForm.WindowRepresentative.weilQW, Cvs.WeilForm.WeilFormOnWindowL2.weilQ_eq (hSae n), hg, Cvs.WeilForm.WeilFormHomogeneous.weilForm_smul]
  have hQw : Cvs.Route.WindowPositivityBulkCoupling.Qx x w = N ^ 2 * Cvs.WeilForm.SelfConvolutionFunctional.weilForm x (Nat.clog 2 x) η := by
    have hww : w = N • w' := by rw [hw', smul_smul, mul_inv_cancel₀ hN0.ne', one_smul]
    rw [hww, Cvs.Route.WindowPositivityBulkCoupling.Qx, Cvs.WeilForm.SymmetricBilinearForm.Q_smul, ← (Cvs.WeilForm.WindowRepresentative.weilQW_rep x (Nat.clog 2 x) _).1]
    ring
  have hQ : Tendsto (fun n => Bx x (S n) (S n)) atTop (𝓝 (Bx x w w)) := by
    simp only [Bx, Cvs.WeilForm.SymmetricBilinearForm.QWbil_self]
    show Tendsto (fun n => Cvs.Route.WindowPositivityBulkCoupling.Qx x (S n)) atTop (𝓝 (Cvs.Route.WindowPositivityBulkCoupling.Qx x w))
    simp_rw [hQS, hQw]
    exact hΞform.const_mul _
  have hSw : Tendsto S atTop (𝓝 w) := (tendsto_iff_norm_sub_tendsto_zero).2 hnorm
  have hlsc : ∀ (y : ℕ → Dom x) (y₀ : Dom x), Tendsto y atTop (𝓝 y₀) → ∀ ε > 0,
      ∀ᶠ n in atTop, Bx x y₀ y₀ - ε ≤ Bx x (y n) (y n) := fun y y₀ hy ε hε => by
    simp only [Bx, Cvs.WeilForm.SymmetricBilinearForm.QWbil_self]
    exact lsc_Qx y y₀ hy ε hε
  have hfin := tendsto_sub_of_lsc (Cvs.WeilForm.SymmetricBilinearForm.QWbil_isSymm _ _ _) (Cvs.WeilForm.CouplingFromTameDensity.floor_Bx x) hlsc hSw hQ
  refine ⟨g, hgC, hgs, hnorm, ?_⟩
  simpa only [Bx, Cvs.WeilForm.SymmetricBilinearForm.QWbil_self] using hfin

end Cvs.WeilForm.TameClassesFormDense
