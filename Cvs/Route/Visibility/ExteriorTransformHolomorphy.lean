import Mathlib
import Cvs.Prolate.Mellin.TailMellinPlancherel
import Cvs.Upstream.PlancherelL1L2SpectralDensity
import Cvs.WeilForm.ThetaSpaceParseval
import Cvs.Xi.EImageMellin
import Cvs.Xi.EImageWindowPoisson
import Cvs.Xi.WindowTransformExterior

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The exterior transform: holomorphy, disc sub-mean value, Plancherel

`X = M[1_{(1,∞)}E_G]` is holomorphic on `Re s < 1`. For `f` holomorphic on a disc,
`|f(c)|² ≤ ⨍_{|z−c|=R} |f|²` and `|f(c)|² ≤ (πr²)⁻¹∫_{D(c,r)} |f|²`, via
`∫_{D(c,r)} F = 2π ∫₀^r ρ ⨍_{|z−c|=ρ} F dρ`. For `σ < 1`, `∫_ℝ |X(σ + ig)|² dg = 2π ∫₁^∞ E_G(θ)² θ^{2σ−1} dθ`.
-/

noncomputable section

open Complex Set MeasureTheory Filter Topology Asymptotics Metric
open Cvs.Xi.EImageWindowPoisson (eimage)
open Cvs.WeilForm.ThetaSpaceParseval (mellinR)
open Cvs.Prolate.Mellin.TailMellinPlancherel (logTail)
open scoped FourierTransform

namespace Cvs.Route.Visibility.ExteriorTransformHolomorphy

/-! ### (a) holomorphy -/

/-- `|1_{(1,∞)}E_G(θ)| ≤ K/θ` on `θ > 0`. -/
theorem abs_ext_le {a : ℝ} (ha : 0 < a) {G G₁ : ℝ → ℝ}
    (hG : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt G (G₁ u) u) (hG₁ : ContinuousOn G₁ (Icc 0 1))
    (hGi : ∫ u in (0 : ℝ)..1, G u = 0) :
    ∃ K, 0 ≤ K ∧ ∀ θ, 0 < θ → |Cvs.Xi.WindowTransformExterior.ext a G θ| ≤ K / θ := by
  obtain ⟨K, hK0, hK⟩ := Cvs.Xi.EImageMellin.abs_eimage_le ha hG hG₁ hGi
  refine ⟨K, hK0, fun θ hθ => ?_⟩
  unfold Cvs.Xi.WindowTransformExterior.ext
  by_cases h : θ ∈ Ioi (1 : ℝ)
  · rw [indicator_of_mem h]; exact hK θ hθ
  · rw [indicator_of_notMem h, abs_zero]; positivity

/-- **The exterior transform is holomorphic on `Re s < 1`** and Mellin-convergent there. -/
theorem mellinR_ext_holo {a : ℝ} (ha : 0 < a) {G G₁ : ℝ → ℝ}
    (hG : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt G (G₁ u) u) (hG₁ : ContinuousOn G₁ (Icc 0 1))
    (hGi : ∫ u in (0 : ℝ)..1, G u = 0) :
    DifferentiableOn ℂ (mellinR (Cvs.Xi.WindowTransformExterior.ext a G)) {s : ℂ | s.re < 1} ∧
      ∀ s : ℂ, s.re < 1 → MellinConvergent (fun θ => (Cvs.Xi.WindowTransformExterior.ext a G θ : ℂ)) s := by
  have hGc : ContinuousOn G (Icc 0 1) := fun u hu => (hG u hu).continuousAt.continuousWithinAt
  obtain ⟨K, -, hK⟩ := abs_ext_le ha hG hG₁ hGi
  have hEm : Measurable (Cvs.Xi.WindowTransformExterior.ext a G) :=
    (Cvs.Xi.EImageMellin.measurable_eimage_of_continuousOn ha hGc).indicator measurableSet_Ioi
  have hloc := Cvs.Xi.EImageMellin.locallyIntegrableOn_of_le_div hEm hK
  have htop : (fun θ => (Cvs.Xi.WindowTransformExterior.ext a G θ : ℂ)) =O[atTop] (· ^ (-(1 : ℝ))) := by
    refine IsBigO.of_bound K ?_
    filter_upwards [eventually_gt_atTop 0] with θ hθ
    rw [Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, Real.rpow_neg_one,
      abs_of_pos (inv_pos.2 hθ), ← div_eq_mul_inv]
    exact hK θ hθ
  have hbot : ∀ b : ℝ, (fun θ => (Cvs.Xi.WindowTransformExterior.ext a G θ : ℂ)) =O[𝓝[>] 0] (· ^ (-b)) := fun b => by
    refine EventuallyEq.trans_isBigO ?_ (isBigO_zero _ _)
    filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds one_pos)] with θ (hθ : θ < 1)
    have : θ ∉ Ioi (1 : ℝ) := fun h => (lt_asymm hθ) h
    simp [Cvs.Xi.WindowTransformExterior.ext, this]
  refine ⟨fun z (hz : z.re < 1) => ?_, fun s hs => ?_⟩
  · exact (mellin_differentiableAt_of_isBigO_rpow hloc htop hz (hbot (z.re - 1))
      (by linarith)).differentiableWithinAt
  · exact mellinConvergent_of_isBigO_rpow hloc htop hs (hbot (s.re - 1)) (by linarith)

/-! ### (b) disc sub-mean value -/

/-- The norm of a circle average is at most the circle average of the norm. -/
theorem norm_circleAverage_le (g : ℂ → ℂ) (c : ℂ) (R : ℝ) :
    ‖Real.circleAverage g c R‖ ≤ Real.circleAverage (fun z => ‖g z‖) c R := by
  rw [Real.circleAverage_def, Real.circleAverage_def, norm_smul, smul_eq_mul, Real.norm_eq_abs,
    abs_of_pos (by positivity)]
  exact mul_le_mul_of_nonneg_left
    (intervalIntegral.norm_integral_le_integral_norm (by positivity)) (by positivity)

/-- **Sub-mean value on a circle**: `|f(c)|² ≤ ⨍_{|z−c|=R} |f|²` for `f` holomorphic on the disc. -/
theorem norm_sq_le_circleAverage {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hf : DiffContOnCl ℂ f (ball c |R|)) :
    ‖f c‖ ^ 2 ≤ Real.circleAverage (fun z => ‖f z‖ ^ 2) c R := by
  have h2 : DiffContOnCl ℂ (fun z => f z • f z) (ball c |R|) := hf.smul hf
  have hmv := h2.circleAverage
  calc ‖f c‖ ^ 2 = ‖f c • f c‖ := by rw [norm_smul, sq]
    _ = ‖Real.circleAverage (fun z => f z • f z) c R‖ := by rw [hmv]
    _ ≤ Real.circleAverage (fun z => ‖f z • f z‖) c R := norm_circleAverage_le _ c R
    _ = Real.circleAverage (fun z => ‖f z‖ ^ 2) c R := by simp only [norm_smul, sq]

/-- **Sub-mean value on a disc, polar form**: for `0 < r` and `f` holomorphic on `D(c, r)`,
`|f(c)|² ≤ (2/r²) ∫₀^r ρ ⨍_{|z−c|=ρ} |f|² dρ`. -/
theorem norm_sq_le_polar {f : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hf : DiffContOnCl ℂ f (ball c r)) :
    ‖f c‖ ^ 2 ≤ 2 / r ^ 2 *
      ∫ ρ in (0 : ℝ)..r, ρ * Real.circleAverage (fun z => ‖f z‖ ^ 2) c ρ := by
  have hcont : ContinuousOn (Real.circleAverage (fun z => ‖f z‖ ^ 2) c) (Icc 0 r) := by
    refine Real.ContinuousOn.circleAverage ?_ (fun ρ hρ => hρ.1)
    refine (hf.continuousOn.norm.pow 2).mono fun z hz => ?_
    rw [closure_ball c hr.ne']
    simpa [mem_closedBall, dist_eq_norm] using (show ‖z - c‖ ∈ Icc 0 r from hz).2
  have hint : IntervalIntegrable (fun ρ => ρ * Real.circleAverage (fun z => ‖f z‖ ^ 2) c ρ)
      volume 0 r :=
    (continuousOn_id.mul hcont).intervalIntegrable_of_Icc hr.le
  have hmono : ∫ ρ in (0 : ℝ)..r, ρ * ‖f c‖ ^ 2
      ≤ ∫ ρ in (0 : ℝ)..r, ρ * Real.circleAverage (fun z => ‖f z‖ ^ 2) c ρ := by
    refine intervalIntegral.integral_mono_on hr.le
      ((by fun_prop : Continuous fun ρ : ℝ => ρ * ‖f c‖ ^ 2).intervalIntegrable 0 r) hint fun ρ hρ => ?_
    refine mul_le_mul_of_nonneg_left (norm_sq_le_circleAverage (hf.mono ?_)) hρ.1
    exact ball_subset_ball (by rw [abs_of_nonneg hρ.1]; exact hρ.2)
  rw [intervalIntegral.integral_mul_const, integral_id] at hmono
  have hr2 : 0 < r ^ 2 := by positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ hr2]
  nlinarith [hmono]

/-- **Polar coordinates on a disc**: for `F` continuous on `D̄(c, r)`,
`∫_{D(c,r)} F = 2π ∫₀^r ρ ⨍_{|z−c|=ρ} F dρ`. -/
theorem integral_ball_eq_polar {F : ℂ → ℝ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hF : ContinuousOn F (closedBall c r)) :
    ∫ z in ball c r, F z = 2 * Real.pi * ∫ ρ in (0 : ℝ)..r, ρ * Real.circleAverage F c ρ := by
  set H : ℂ → ℝ := (ball (0 : ℂ) r).indicator fun z => F (c + z) with hH
  have htr : ∫ z in ball c r, F z = ∫ z, H z := by
    rw [← integral_indicator measurableSet_ball,
      ← integral_add_left_eq_self (fun z => (ball c r).indicator F z) c]
    congr 1; funext z
    simp only [hH, indicator, mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero]
  set g : ℝ × ℝ → ℝ := fun p => p.1 * F (circleMap c p.1 p.2) with hg
  have hpol : ∫ z, H z = ∫ p in Ioo 0 r ×ˢ Ioo (-Real.pi) Real.pi, g p := by
    rw [← Complex.integral_comp_polarCoord_symm, polarCoord_target]
    have e : ∀ p ∈ Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
        p.1 • H (Complex.polarCoord.symm p) = (Iio r ×ˢ (univ : Set ℝ)).indicator g p := by
      intro p hp
      have hp0 : 0 < p.1 := hp.1
      have hc : c + Complex.polarCoord.symm p = circleMap c p.1 p.2 := by
        rw [Complex.polarCoord_symm_apply, circleMap, Complex.exp_mul_I]; push_cast; ring
      have hn : ‖Complex.polarCoord.symm p‖ < r ↔ p.1 < r := by
        rw [Complex.norm_polarCoord_symm, abs_of_pos hp0]
      rw [smul_eq_mul, hH]
      by_cases h : p.1 < r
      · rw [indicator_of_mem (show Complex.polarCoord.symm p ∈ ball (0 : ℂ) r by
            rw [mem_ball, dist_zero_right]; exact hn.2 h),
          indicator_of_mem (show p ∈ Iio r ×ˢ (univ : Set ℝ) from ⟨h, mem_univ _⟩), hc]
      · rw [indicator_of_notMem (show Complex.polarCoord.symm p ∉ ball (0 : ℂ) r by
            rw [mem_ball, dist_zero_right]; exact fun h' => h (hn.1 h')),
          indicator_of_notMem (show p ∉ Iio r ×ˢ (univ : Set ℝ) from fun h' => h h'.1), mul_zero]
    rw [setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) e,
      setIntegral_indicator (measurableSet_Iio.prod MeasurableSet.univ)]
    have hs : (Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi) ∩ (Iio r ×ˢ (univ : Set ℝ))
        = Ioo 0 r ×ˢ Ioo (-Real.pi) Real.pi := by
      ext p
      simp only [mem_inter_iff, mem_prod, mem_Ioi, mem_Ioo, mem_Iio, mem_univ, and_true]
      tauto
    rw [hs]
  have hgc : ContinuousOn g (Icc 0 r ×ˢ Icc (-Real.pi) Real.pi) := by
    refine continuous_fst.continuousOn.mul (hF.comp (by unfold circleMap; fun_prop) ?_)
    intro p hp
    exact closedBall_subset_closedBall hp.1.2 (circleMap_mem_closedBall c hp.1.1 p.2)
  have hint : IntegrableOn g (Ioo 0 r ×ˢ Ioo (-Real.pi) Real.pi) (volume.prod volume) :=
    (hgc.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
  have hin : ∀ ρ : ℝ, ∫ θ in Ioo (-Real.pi) Real.pi, g (ρ, θ)
      = 2 * Real.pi * (ρ * Real.circleAverage F c ρ) := fun ρ => by
    simp only [hg]
    rw [integral_const_mul, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
      Real.circleAverage_eq_integral_add (-Real.pi),
      intervalIntegral.integral_comp_add_right (fun θ => F (circleMap c ρ θ)), smul_eq_mul]
    rw [show (0 : ℝ) + -Real.pi = -Real.pi by ring, show 2 * Real.pi + -Real.pi = Real.pi by ring]
    field_simp
  rw [htr, hpol, Measure.volume_eq_prod, setIntegral_prod g hint]
  simp only [hin]
  rw [integral_const_mul, intervalIntegral.integral_of_le hr.le, integral_Ioc_eq_integral_Ioo]

/-- **Sub-mean value on a disc, area form**: for `0 < r` and `f` holomorphic on `D(c, r)`,
`|f(c)|² ≤ (πr²)⁻¹ ∫_{D(c,r)} |f|²`. -/
theorem norm_sq_le_ball {f : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hf : DiffContOnCl ℂ f (ball c r)) :
    ‖f c‖ ^ 2 ≤ (Real.pi * r ^ 2)⁻¹ * ∫ z in ball c r, ‖f z‖ ^ 2 := by
  have hc : ContinuousOn (fun z => ‖f z‖ ^ 2) (closedBall c r) := by
    rw [← closure_ball c hr.ne']; exact hf.continuousOn.norm.pow 2
  rw [integral_ball_eq_polar hr hc]
  have h := norm_sq_le_polar hr hf
  have e : (Real.pi * r ^ 2)⁻¹ * (2 * Real.pi * ∫ ρ in (0 : ℝ)..r,
      ρ * Real.circleAverage (fun z => ‖f z‖ ^ 2) c ρ)
      = 2 / r ^ 2 * ∫ ρ in (0 : ℝ)..r, ρ * Real.circleAverage (fun z => ‖f z‖ ^ 2) c ρ := by
    have := Real.pi_pos.ne'; field_simp
  rw [e]; exact h

/-- **Disc sub-mean value for the exterior transform**: for `0 < r` and `Re s₀ + r < 1`,
`|X(s₀)|² ≤ (πr²)⁻¹ ∫_{D(s₀,r)} |X|²` with `X = M[1_{(1,∞)}E_G]`. -/
theorem norm_sq_mellinR_ext_le_ball {a : ℝ} (ha : 0 < a) {G G₁ : ℝ → ℝ}
    (hG : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt G (G₁ u) u) (hG₁ : ContinuousOn G₁ (Icc 0 1))
    (hGi : ∫ u in (0 : ℝ)..1, G u = 0) {s₀ : ℂ} {r : ℝ} (hr : 0 < r) (hs : s₀.re + r < 1) :
    ‖mellinR (Cvs.Xi.WindowTransformExterior.ext a G) s₀‖ ^ 2
      ≤ (Real.pi * r ^ 2)⁻¹ * ∫ z in ball s₀ r, ‖mellinR (Cvs.Xi.WindowTransformExterior.ext a G) z‖ ^ 2 := by
  refine norm_sq_le_ball hr ((mellinR_ext_holo ha hG hG₁ hGi).1.diffContOnCl_ball fun z hz => ?_)
  have h1 : z.re - s₀.re ≤ r := by
    have := Complex.re_le_norm (z - s₀)
    rw [Complex.sub_re] at this
    exact this.trans (by simpa [dist_eq_norm] using hz)
  show z.re < 1
  linarith

/-! ### (c) Plancherel in `log θ` -/

/-- The weighted log-scale tail is dominated by `K e^{(σ−1)u}` on `u > 0`. -/
theorem norm_logTail_le {F : ℝ → ℝ} {K σ : ℝ} (hK : ∀ w, 1 < w → |F w| ≤ K / w) (u : ℝ) :
    ‖logTail (fun w => F w * w ^ (σ - 1 / 2)) u‖
      ≤ (Ioi (0 : ℝ)).indicator (fun u => K * Real.exp ((σ - 1) * u)) u := by
  unfold logTail
  by_cases hu : u ∈ Ioi (0 : ℝ)
  · rw [indicator_of_mem hu, indicator_of_mem hu, Complex.norm_real, Real.norm_eq_abs]
    have he : 1 < Real.exp u := Real.one_lt_exp_iff.2 hu
    have h1 := hK _ he
    dsimp only
    rw [← Real.exp_mul, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _),
      abs_of_pos (Real.exp_pos _)]
    calc Real.exp (u / 2) * (|F (Real.exp u)| * Real.exp (u * (σ - 1 / 2)))
        ≤ Real.exp (u / 2) * (K / Real.exp u * Real.exp (u * (σ - 1 / 2))) := by gcongr
      _ = K * Real.exp ((σ - 1) * u) := by
        rw [show K / Real.exp u = K * Real.exp (-u) by rw [Real.exp_neg, div_eq_mul_inv]]
        calc _ = K * (Real.exp (u / 2) * Real.exp (-u) * Real.exp (u * (σ - 1 / 2))) := by ring
          _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 2; ring
  · rw [indicator_of_notMem hu, indicator_of_notMem hu, norm_zero]

/-- `u ↦ 1_{u>0} K e^{−bu}` is integrable for `b > 0`. -/
theorem integrable_indicator_exp {K b : ℝ} (hb : 0 < b) :
    Integrable ((Ioi (0 : ℝ)).indicator fun u => K * Real.exp (-b * u)) := by
  rw [integrable_indicator_iff measurableSet_Ioi]
  exact (exp_neg_integrableOn_Ioi 0 hb).const_mul K

/-- **The Mellin transform on `Re s = σ` is a critical-line transform of `F θ^{σ−1/2}`.** -/
theorem mellinR_indicator_eq (F : ℝ → ℝ) (σ g : ℝ) :
    mellinR ((Ioi (1 : ℝ)).indicator F) (σ + g * I)
      = ∫ w : ℝ in Ioi 1, (w : ℂ) ^ (1 / 2 + g * I - 1) * ((F w * w ^ (σ - 1 / 2) : ℝ) : ℂ) := by
  unfold mellinR mellin
  have e : ∀ t : ℝ, (t : ℂ) ^ ((σ : ℂ) + g * I - 1) • ((((Ioi (1 : ℝ)).indicator F t : ℝ)) : ℂ)
      = (Ioi (1 : ℝ)).indicator (fun t => (t : ℂ) ^ ((σ : ℂ) + g * I - 1) * (F t : ℂ)) t :=
    fun t => by by_cases h : t ∈ Ioi (1 : ℝ) <;> simp [h]
  simp only [e]
  rw [setIntegral_indicator measurableSet_Ioi,
    show Ioi (0 : ℝ) ∩ Ioi 1 = Ioi 1 from Ioi_inter_Ioi.trans (by rw [max_eq_right zero_le_one])]
  refine setIntegral_congr_fun measurableSet_Ioi fun w (hw : 1 < w) => ?_
  have hw0 : (0 : ℝ) < w := lt_trans one_pos hw
  push_cast
  rw [Complex.ofReal_cpow hw0.le]
  have hne : (w : ℂ) ≠ 0 := by exact_mod_cast hw0.ne'
  rw [show (w : ℂ) ^ ((σ : ℂ) + g * I - 1) = (w : ℂ) ^ ((1 : ℂ) / 2 + g * I - 1) * (w : ℂ) ^ (((σ - 1 / 2 : ℝ)) : ℂ) by
    rw [← Complex.cpow_add _ _ hne]; congr 1; push_cast; ring]
  ring

/-- **Mellin–Plancherel on `Re s = σ`**: for measurable `F` with `|F(θ)| ≤ K/θ` on `θ > 1` and
`σ < 1`, `∫_ℝ |M[1_{(1,∞)}F](σ + ig)|² dg = 2π ∫₁^∞ F(θ)² θ^{2σ−1} dθ`. -/
theorem integral_norm_sq_mellinR_indicator {F : ℝ → ℝ} (hF : Measurable F) {K : ℝ}
    (hK : ∀ w, 1 < w → |F w| ≤ K / w) {σ : ℝ} (hσ : σ < 1) :
    ∫ g : ℝ, ‖mellinR ((Ioi (1 : ℝ)).indicator F) (σ + g * I)‖ ^ 2
      = 2 * Real.pi * ∫ θ in Ioi 1, F θ ^ 2 * θ ^ (2 * σ - 1) := by
  set f : ℝ → ℝ := fun w => F w * w ^ (σ - 1 / 2) with hfdef
  have hfm : Measurable f := hF.mul (measurable_id.pow_const _)
  have hb : 0 < 1 - σ := by linarith
  have hdom : ∀ u, ‖logTail f u‖
      ≤ (Ioi (0 : ℝ)).indicator (fun u => K * Real.exp (-(1 - σ) * u)) u := fun u => by
    have := norm_logTail_le (F := F) (σ := σ) hK u
    rw [show (fun u : ℝ => K * Real.exp ((σ - 1) * u)) = fun u => K * Real.exp (-(1 - σ) * u) from
      funext fun u => by ring_nf] at this
    exact this
  have hint : Integrable (logTail f) :=
    (integrable_indicator_exp hb).mono' (Cvs.Prolate.Mellin.TailMellinPlancherel.measurable_logTail hfm).aestronglyMeasurable
      (ae_of_all _ hdom)
  have hL2 : MemLp (logTail f) 2 volume := by
    refine (memLp_two_iff_integrable_sq_norm
      (Cvs.Prolate.Mellin.TailMellinPlancherel.measurable_logTail hfm).aestronglyMeasurable).2 ?_
    refine (integrable_indicator_exp (K := K ^ 2) (by linarith : 0 < 2 * (1 - σ))).mono'
      ((Cvs.Prolate.Mellin.TailMellinPlancherel.measurable_logTail hfm).norm.pow_const 2).aestronglyMeasurable
      (ae_of_all _ fun u => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h := hdom u
    by_cases hu : u ∈ Ioi (0 : ℝ)
    · rw [indicator_of_mem hu] at h ⊢
      calc ‖logTail f u‖ ^ 2 ≤ (K * Real.exp (-(1 - σ) * u)) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) h 2
        _ = K ^ 2 * Real.exp (-(2 * (1 - σ)) * u) := by
            rw [mul_pow, ← Real.exp_nat_mul]; congr 2; push_cast; ring
    · rw [indicator_of_notMem hu] at h ⊢
      have : ‖logTail f u‖ = 0 := le_antisymm h (norm_nonneg _)
      rw [this]; norm_num
  simp only [mellinR_indicator_eq, Cvs.Prolate.Mellin.TailMellinPlancherel.mellin_eq_fourier_logTail]
  have e : ∀ t : ℝ, -(t / (2 * Real.pi)) = (-(2 * Real.pi)⁻¹) * t := fun t => by ring
  simp only [e]
  rw [Measure.integral_comp_mul_left (fun ξ => ‖𝓕 (logTail f) ξ‖ ^ 2),
    Cvs.Upstream.PlancherelL1L2SpectralDensity.integral_norm_sq_fourier hint hL2,
    Cvs.Prolate.Mellin.TailMellinPlancherel.integral_norm_sq_logTail, smul_eq_mul,
    inv_neg, inv_inv, abs_neg, abs_of_pos (by positivity)]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun w (hw : 1 < w) => ?_
  have hw0 : (0 : ℝ) ≤ w := (lt_trans one_pos hw).le
  simp only [hfdef]
  rw [mul_pow, ← Real.rpow_natCast (w ^ (σ - 1 / 2)), ← Real.rpow_mul hw0]
  congr 2; push_cast; ring

/-- **Plancherel for the exterior transform**: for `σ < 1`,
`∫_ℝ |X(σ + ig)|² dg = 2π ∫₁^∞ E_G(θ)² θ^{2σ−1} dθ` with `X = M[1_{(1,∞)}E_G]`. -/
theorem integral_norm_sq_mellinR_ext {a : ℝ} (ha : 0 < a) {G G₁ : ℝ → ℝ}
    (hG : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt G (G₁ u) u) (hG₁ : ContinuousOn G₁ (Icc 0 1))
    (hGi : ∫ u in (0 : ℝ)..1, G u = 0) {σ : ℝ} (hσ : σ < 1) :
    ∫ g : ℝ, ‖mellinR (Cvs.Xi.WindowTransformExterior.ext a G) (σ + g * I)‖ ^ 2
      = 2 * Real.pi * ∫ θ in Ioi 1, eimage a G θ ^ 2 * θ ^ (2 * σ - 1) := by
  have hGc : ContinuousOn G (Icc 0 1) := fun u hu => (hG u hu).continuousAt.continuousWithinAt
  obtain ⟨K, -, hK⟩ := Cvs.Xi.EImageMellin.abs_eimage_le ha hG hG₁ hGi
  exact integral_norm_sq_mellinR_indicator
    (Cvs.Xi.EImageMellin.measurable_eimage_of_continuousOn ha hGc)
    (fun w hw => hK w (lt_trans one_pos hw)) hσ

end Cvs.Route.Visibility.ExteriorTransformHolomorphy
