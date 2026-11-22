import Mathlib
import Cvs.Route.OneCellBoxWindowForm
import Cvs.Route.OneCellLaplaceTransform
import Cvs.Upstream.LandauLaplaceNonneg
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.Zeta.AllZerosOnLine
import Cvs.Zeta.GaussKernel.ZetaZeroStatement
import Cvs.Zeta.RiemannXi
import Cvs.Zeta.XiConj
import Cvs.Zeta.XiVertical
import Cvs.Zeta.ZeroFreeHeightFive

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The one-cell criterion: RH ⟺ `G(L) ≥ 0` for every `L > 0`

On the half-plane where the Laplace transform `Φ = lap G` converges, `ξ'(½+z) = ξ(½+z)·Φ(z)z²/2` by the identity
principle from the real ray (Cvs.Route.OneCellLaplaceTransform), so at a zero of `ξ` there every derivative of `ξ` vanishes and `ξ ≡ 0`: no zero lies
right of the abscissa. If `G ≥ 0`, Landau (Cvs.Upstream.LandauLaplaceNonneg) pushes the abscissa below any `β − ½ > 0`, since `ξ` has no real
zeros (`ZeroFreeHeightFive`): every zero has `Re ρ ≤ ½`, and by `ξ(1−s) = ξ(s)` all lie on the line. With Cvs.Route.OneCellBoxWindowForm, RH ⟺ G ≥ 0.
-/

noncomputable section

open MeasureTheory Real Set Filter Topology Cvs.Zeta

namespace Cvs.Route.OneCellCriterion
open Cvs.ZeroCounting

open Cvs.Route.OneCellLaplaceTransform (G ladder primeSide xi laplace_pole laplace_ladder laplace_primeSide integrableOn_ramp laplace_G_xi)
open Cvs.Upstream.LandauLaplaceNonneg (Conv ConvAbove lap lapn differentiableOn_lap isOpen_halfPlane conv_of_analytic)

/-! ### `G` is measurable and its transform converges above `½` -/

theorem integrableOn_G_mul_exp {s : ℝ} (hs : 1 / 2 < s) :
    IntegrableOn (fun L => G L * Real.exp (-(s * L))) (Ioi 0) := by
  have hs0 : 0 < s := by linarith
  have hP := (laplace_pole hs).1
  have hLd := (laplace_ladder hs0).1
  have hPr := (laplace_primeSide hs).1
  have hA : IntegrableOn (fun L => Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 * ((L - 0) * Real.exp (-(s * L))))
      (Ioi 0) := (integrableOn_ramp (c := 0) hs0).const_mul _
  have hfun : (fun L => G L * Real.exp (-(s * L))) = fun L =>
      ((16 * (Real.cosh (L / 2) - 1) * Real.exp (-(s * L))
        + Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 * ((L - 0) * Real.exp (-(s * L))))
        + 2 * (ladder L * Real.exp (-(s * L)))) - 2 * (primeSide L * Real.exp (-(s * L))) := by
    funext L; simp only [G]; ring
  rw [hfun]
  exact ((hP.add hA).add (hLd.const_mul 2)).sub (hPr.const_mul 2)

theorem aestronglyMeasurable_G : AEStronglyMeasurable G (volume.restrict (Ioi 0)) := by
  have h := (integrableOn_G_mul_exp (s := 1) (by norm_num)).aestronglyMeasurable
  have h2 := h.mul (Continuous.aestronglyMeasurable (f := fun L : ℝ => Real.exp (1 * L)) (by fun_prop))
  refine h2.congr (ae_of_all _ fun L => ?_)
  show G L * Real.exp (-(1 * L)) * Real.exp (1 * L) = G L
  rw [mul_assoc, ← Real.exp_add]; simp

theorem convAbove_G_half : ConvAbove G (1 / 2) := fun _ hτ => integrableOn_G_mul_exp hτ

/-! ### The identity on the real ray -/

/-- `ξ` is real on the real axis, so its logarithmic derivative is real there. -/
theorem logDeriv_riemannXi_real (x : ℝ) :
    (((logDeriv riemannXi (x : ℂ)).re : ℝ) : ℂ) = logDeriv riemannXi (x : ℂ) := by
  have h := logDeriv_riemannXi_conj (x : ℂ)
  rw [Complex.conj_ofReal] at h
  have him : (logDeriv riemannXi (x : ℂ)).im = 0 := Complex.conj_eq_iff_im.1 h.symm
  apply Complex.ext <;> simp [him]

/-- `OneCellLaplaceTransform`'s `xi` is `2ξ` away from `0, 1`, so the logarithmic derivatives agree there. -/
theorem logDeriv_xi_eq {w : ℂ} (hw0 : w ≠ 0) (hw1 : w ≠ 1) :
    logDeriv xi w = logDeriv riemannXi w := by
  have hev : xi =ᶠ[𝓝 w] fun z => 2 * riemannXi z := by
    filter_upwards [isOpen_ne.mem_nhds hw0, isOpen_ne.mem_nhds hw1] with z hz0 hz1
    rw [riemannXi_eq hz0 hz1]
    unfold xi; ring
  rw [(logDeriv_congr_nhds hev).eq_of_nhds, logDeriv_const_mul _ _ two_ne_zero]

/-- The Laplace transform of `G` at a real point `s > ½` is `(2/s²)·(ξ'/ξ)(½+s)`. -/
theorem lap_G_real {s : ℝ} (hs : 1 / 2 < s) :
    lap G (s : ℂ) = (2 / (s : ℂ) ^ 2) * logDeriv riemannXi ((1 / 2 : ℂ) + s) := by
  have hfun : (fun L : ℝ => (G L : ℂ) * Complex.exp (-((s : ℂ) * L)))
      = fun L => ((G L * Real.exp (-(s * L)) : ℝ) : ℂ) := by
    funext L; push_cast; ring_nf
  have h1 : lap G (s : ℂ) = ((∫ L in Ioi (0:ℝ), G L * Real.exp (-(s * L)) : ℝ) : ℂ) := by
    unfold lap; rw [hfun, integral_complex_ofReal]
  rw [h1, laplace_G_xi hs]
  have hw0 : ((1 / 2 + s : ℝ) : ℂ) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hw1 : ((1 / 2 + s : ℝ) : ℂ) ≠ 1 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  rw [Complex.ofReal_mul, logDeriv_xi_eq hw0 hw1, logDeriv_riemannXi_real]
  push_cast
  ring

/-! ### The identity on the half-plane -/

/-- The shifted `ξ`, `φ(z) = ξ(½ + z)`. -/
def φ (z : ℂ) : ℂ := riemannXi ((1 / 2 : ℂ) + z)

theorem differentiable_φ : Differentiable ℂ φ :=
  differentiable_riemannXi.comp ((differentiable_const _).add differentiable_id)

theorem analyticOnNhd_φ (U : Set ℂ) : AnalyticOnNhd ℂ φ U :=
  fun z _ => differentiable_φ.analyticAt z

theorem deriv_φ (z : ℂ) : deriv φ z = deriv riemannXi ((1 / 2 : ℂ) + z) := by
  have h := ((differentiable_riemannXi _).hasDerivAt.comp z ((hasDerivAt_id z).const_add (1 / 2 : ℂ)))
  show deriv (fun z => riemannXi ((1 / 2 : ℂ) + z)) z = _
  simpa [Function.comp_def] using h.deriv

/-- `ξ(½ + s) ≠ 0` for real `s > ½`. -/
theorem φ_ne_zero {s : ℝ} (hs : 1 / 2 < s) : φ (s : ℂ) ≠ 0 := by
  unfold φ
  rw [Ne, riemannXi_eq_zero_iff_riemannZeta (by simp; linarith)
    (by intro h; have := congrArg Complex.re h; simp at this; linarith)]
  exact riemannZeta_ne_zero_of_one_lt_re (by simp; linarith)

/-- The identity on the real ray: `ξ'(½+s) = ξ(½+s)·Φ(s)s²/2`. -/
theorem real_identity {s : ℝ} (hs : 1 / 2 < s) :
    deriv φ (s : ℂ) = φ (s : ℂ) * (lap G (s : ℂ) * (s : ℂ) ^ 2 / 2) := by
  have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast (show s ≠ 0 by linarith)
  have hξ := φ_ne_zero hs
  rw [deriv_φ, lap_G_real hs]
  unfold φ at hξ ⊢
  rw [logDeriv_apply]
  have hs2 : (s : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 hs0
  rw [show riemannXi ((1 / 2 : ℂ) + s) * (2 / (s : ℂ) ^ 2 * (deriv riemannXi ((1 / 2 : ℂ) + s)
      / riemannXi ((1 / 2 : ℂ) + s)) * (s : ℂ) ^ 2 / 2)
      = deriv riemannXi ((1 / 2 : ℂ) + s) * (riemannXi ((1 / 2 : ℂ) + s) / riemannXi ((1 / 2 : ℂ) + s))
        * ((s : ℂ) ^ 2 / (s : ℂ) ^ 2) by ring, div_self hξ, div_self hs2]
  ring

/-- **`ξ' = ξ·Φ z²/2` on the half-plane of convergence**: both sides are holomorphic there and agree on the
real ray `s > ½`. -/
theorem deriv_φ_eq (hG : ∀ L, 0 < L → 0 ≤ G L) {σ : ℝ} (hσ : ConvAbove G σ) {z : ℂ} (hz : σ < z.re) :
    deriv φ z = φ z * (lap G z * z ^ 2 / 2) := by
  set U : Set ℂ := {z | σ < z.re} with hU
  have hUo : IsOpen U := isOpen_halfPlane σ
  have hUc : IsPreconnected U := (convex_halfSpace_re_gt σ).isPreconnected
  have hlap : AnalyticOnNhd ℂ (lap G) U :=
    (differentiableOn_lap hG aestronglyMeasurable_G hσ).analyticOnNhd hUo
  have hf : AnalyticOnNhd ℂ (deriv φ) U := ((analyticOnNhd_φ univ).deriv).mono (subset_univ _)
  have hh : AnalyticOnNhd ℂ (fun z => φ z * (lap G z * z ^ 2 / 2)) U :=
    (analyticOnNhd_φ U).mul ((hlap.mul (analyticOnNhd_id.pow 2)).div analyticOnNhd_const
      fun _ _ => two_ne_zero)
  set b : ℝ := max σ (1 / 2) + 1 with hb
  have hbU : (b : ℂ) ∈ U := by
    show σ < (b : ℂ).re
    rw [Complex.ofReal_re, hb]; linarith [le_max_left σ (1 / 2)]
  have hten : Tendsto (fun j : ℕ => (((b + 1 / ((j : ℝ) + 1)) : ℝ) : ℂ)) atTop (𝓝[≠] (b : ℂ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h0 : Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have hr : Tendsto (fun j : ℕ => b + 1 / ((j : ℝ) + 1)) atTop (𝓝 (b + 0)) :=
        tendsto_const_nhds.add h0
      have hc := (Complex.continuous_ofReal.tendsto (b + 0)).comp hr
      have hc' : Tendsto (fun j : ℕ => (((b + 1 / ((j : ℝ) + 1)) : ℝ) : ℂ)) atTop
          (𝓝 (((b + 0 : ℝ)) : ℂ)) := hc
      simpa using hc'
    · filter_upwards with j
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro hc
      have : b + 1 / ((j : ℝ) + 1) = b := by exact_mod_cast congrArg Complex.re hc
      have hj : (0:ℝ) < 1 / ((j : ℝ) + 1) := by positivity
      linarith
  have hfreq : ∃ᶠ w in 𝓝[≠] (b : ℂ), deriv φ w = φ w * (lap G w * w ^ 2 / 2) := by
    refine hten.frequently (Filter.Eventually.frequently ?_)
    filter_upwards with j
    have hj : (0:ℝ) < 1 / ((j : ℝ) + 1) := by positivity
    exact real_identity (by rw [hb]; linarith [le_max_right σ (1 / 2)])
  exact hf.eqOn_of_preconnected_of_frequently_eq hh hUc hbU hfreq hz

/-! ### No zero right of the abscissa -/

/-- **A zero of `ξ` right of `½ + σ` kills `ξ`**: `φ' = φΨ` on the half-plane makes every derivative of `φ`
vanish at the zero, and `φ` is entire. -/
theorem re_le_of_convAbove (hG : ∀ L, 0 < L → 0 ≤ G L) {σ : ℝ} (hσ : ConvAbove G σ)
    {ρ : ℂ} (hρ : riemannXi ρ = 0) : ρ.re ≤ 1 / 2 + σ := by
  by_contra hlt
  rw [not_le] at hlt
  set z₀ : ℂ := ρ - 1 / 2 with hz₀def
  have hz₀ : σ < z₀.re := by rw [hz₀def]; simp; linarith
  have hφ0 : φ z₀ = 0 := by
    unfold φ; rw [hz₀def, show (1 / 2 : ℂ) + (ρ - 1 / 2) = ρ by ring]; exact hρ
  set U : Set ℂ := {z | σ < z.re} with hU
  have hUo : IsOpen U := isOpen_halfPlane σ
  set Ψ : ℂ → ℂ := fun z => lap G z * z ^ 2 / 2 with hΨdef
  have hΨ : DifferentiableOn ℂ Ψ U :=
    ((differentiableOn_lap hG aestronglyMeasurable_G hσ).mul (differentiableOn_id.pow 2)).div_const 2
  have key : ∀ n : ℕ, ∃ Ψn : ℂ → ℂ, DifferentiableOn ℂ Ψn U ∧ ∀ z ∈ U, iteratedDeriv n φ z = φ z * Ψn z := by
    intro n
    induction n with
    | zero => exact ⟨fun _ => 1, differentiableOn_const _, fun z _ => by simp⟩
    | succ n ih =>
      obtain ⟨Ψn, hΨn, hn⟩ := ih
      refine ⟨fun z => Ψ z * Ψn z + deriv Ψn z, ?_, fun z hz => ?_⟩
      · exact (hΨ.mul hΨn).add ((hΨn.analyticOnNhd hUo).deriv.differentiableOn)
      · have hz' : σ < z.re := hz
        rw [iteratedDeriv_succ]
        have hev : iteratedDeriv n φ =ᶠ[𝓝 z] fun w => φ w * Ψn w :=
          Filter.eventually_of_mem (hUo.mem_nhds hz) hn
        rw [hev.deriv_eq, show (fun w => φ w * Ψn w) = φ * Ψn from rfl,
          deriv_mul (differentiable_φ z) (hΨn.differentiableAt (hUo.mem_nhds hz)), deriv_φ_eq hG hσ hz']
        simp only [hΨdef]
        ring
  have hall : ∀ n, iteratedDeriv n φ z₀ = 0 := fun n => by
    obtain ⟨Ψn, -, hn⟩ := key n
    rw [hn z₀ hz₀, hφ0, zero_mul]
  have hzero : ∀ z, φ z = 0 := by
    intro z
    rw [← Complex.taylorSeries_eq_of_entire' (c := z₀) (z := z) differentiable_φ]
    simp [hall]
  have h := hzero (-(1 / 2))
  unfold φ at h
  rw [show (1 / 2 : ℂ) + -(1 / 2) = 0 by ring] at h
  exact riemannXi_zero_ne_zero h

/-! ### Landau at the abscissa, and RH -/

theorem ne_zero_of_mem_ball {σ₁ r : ℝ} (hσ₁ : 0 < σ₁) (hr : r ≤ σ₁) {z : ℂ}
    (hz : z ∈ Metric.ball (σ₁ : ℂ) r) : z ≠ 0 := by
  intro h
  rw [h, Metric.mem_ball, Complex.dist_eq, zero_sub, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hσ₁] at hz
  linarith

/-- **`G ≥ 0` on `(0, ∞)` implies RH.** -/
theorem riemannHypothesis_of_G_nonneg (hG : ∀ L, 0 < L → 0 ≤ G L) : RiemannHypothesis := by
  rw [← Cvs.Operator.allZerosOnLine_iff_rh]
  by_contra hnot
  obtain ⟨ρ, hre⟩ := Cvs.Zeta.GaussKernel.AdmissibleKernel.exists_offLine_of_not_allZerosOnLine hnot
  obtain ⟨hz, h0, h1⟩ := ρ.2
  have hρ1 : (ρ : ℂ) ≠ 1 := fun h => by rw [h] at h1; simp at h1
  have hξ : riemannXi ρ = 0 := (riemannXi_eq_zero_iff_riemannZeta h0 hρ1).2 hz
  obtain ⟨ρ', hξ', hre'⟩ : ∃ ρ' : ℂ, riemannXi ρ' = 0 ∧ 1 / 2 < ρ'.re := by
    rcases lt_or_gt_of_ne hre with h | h
    · exact ⟨1 - ρ, by rw [riemannXi_one_sub]; exact hξ, by simp; linarith⟩
    · exact ⟨ρ, hξ, h⟩
  set δ : ℝ := ρ'.re - 1 / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  set S : Set ℝ := {σ | ConvAbove G σ} with hS
  have hhalf : (1 / 2 : ℝ) ∈ S := convAbove_G_half
  have hlow : ∀ σ ∈ S, δ ≤ σ := fun σ hσ => by
    have := re_le_of_convAbove hG hσ hξ'
    rw [hδ]; linarith
  have hbdd : BddBelow S := ⟨δ, hlow⟩
  have hne : S.Nonempty := ⟨_, hhalf⟩
  set σ₁ : ℝ := sInf S with hσ₁def
  have hσ₁δ : δ ≤ σ₁ := le_csInf hne hlow
  have hσ₁pos : 0 < σ₁ := lt_of_lt_of_le hδ0 hσ₁δ
  have hconv : ConvAbove G σ₁ := by
    intro τ hτ
    obtain ⟨σ, hσS, hστ⟩ := exists_lt_of_csInf_lt hne hτ
    exact hσS τ hστ
  -- `ξ` has no real zero, so `φ ≠ 0` near the real point `σ₁`
  have hφσ : φ (σ₁ : ℂ) ≠ 0 := by
    intro h
    have := Cvs.ZeroFree.abs_im_gt_five_of_riemannXi_eq_zero h
    simp at this
    linarith
  obtain ⟨r₁, hr₁, hball⟩ :=
    Metric.eventually_nhds_iff.1 (differentiable_φ.continuous.continuousAt.eventually_ne hφσ)
  set r : ℝ := min r₁ σ₁ with hr
  have hr0 : 0 < r := lt_min hr₁ hσ₁pos
  have hrσ : r ≤ σ₁ := min_le_right _ _
  have hrr : r ≤ r₁ := min_le_left _ _
  set Ft : ℂ → ℂ := fun z => 2 / z ^ 2 * (deriv φ z / φ z) with hFt
  have hFd : DifferentiableOn ℂ Ft (Metric.ball (σ₁ : ℂ) r) := by
    intro z hz
    have hz0 : z ≠ 0 := ne_zero_of_mem_ball hσ₁pos hrσ hz
    have hφz : φ z ≠ 0 := hball (lt_of_lt_of_le (Metric.mem_ball.1 hz) hrr)
    have h1 : DifferentiableAt ℂ (fun z : ℂ => 2 / z ^ 2) z :=
      (differentiableAt_const _).fun_div (differentiableAt_pow 2) (pow_ne_zero 2 hz0)
    have h2 : DifferentiableAt ℂ (fun z => deriv φ z / φ z) z :=
      (((analyticOnNhd_φ univ).deriv z trivial).differentiableAt).fun_div (differentiable_φ z) hφz
    exact (h1.fun_mul h2).differentiableWithinAt
  have hFeq : ∀ z ∈ Metric.ball (σ₁ : ℂ) r, σ₁ < z.re → Ft z = lap G z := by
    intro z hz hzre
    have hz0 : z ≠ 0 := ne_zero_of_mem_ball hσ₁pos hrσ hz
    have hφz : φ z ≠ 0 := hball (lt_of_lt_of_le (Metric.mem_ball.1 hz) hrr)
    simp only [hFt]
    rw [deriv_φ_eq hG hconv hzre]
    field_simp
  have hnew : Conv G (σ₁ - r / 4) := conv_of_analytic hG aestronglyMeasurable_G hconv hr0 hFd hFeq
  have hmem : σ₁ - r / 4 ∈ S := hnew.convAbove hG aestronglyMeasurable_G
  have := csInf_le hbdd hmem
  linarith

/-- **The one-cell criterion**: RH ⟺ the window form of every box is nonnegative, `0 ≤ G L` for all `L > 0`. -/
theorem riemannHypothesis_iff_G_nonneg : RiemannHypothesis ↔ ∀ L : ℝ, 0 < L → 0 ≤ G L :=
  ⟨fun h _ hL => Cvs.Route.OneCellBoxWindowForm.G_nonneg_of_RH h hL, riemannHypothesis_of_G_nonneg⟩

end Cvs.Route.OneCellCriterion
