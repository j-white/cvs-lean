import Mathlib
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.Approximant.SpineCouplingTailPairing
import Cvs.Approximant.SpineSubspace
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.FullTailConvergence
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.Mellin.ExteriorSeriesBox
import Cvs.Prolate.Mellin.ModeExteriorRepresentation
import Cvs.Prolate.Mellin.ModeExteriorTerms
import Cvs.Prolate.Mellin.UnitRungBandExtension
import Cvs.Prolate.RungSpanBernsteinNikolskii
import Cvs.Route.Visibility.ExteriorTransformHolomorphy
import Cvs.Route.Visibility.RungBoxTunnellingSum
import Cvs.Route.Visibility.RungXBoxExplicit
import Cvs.StepA.Edge.TransplantAngleHighZeros
import Cvs.Upstream.TrigMellinIntegralsContinuation
import Cvs.WeilForm.TameWindowZeroSum
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
# `RungLemmaX`: the explicit per-rung exterior bound on the box

On `Re s < 0`, `X_j(s) + g0_j/(2(1 − s)) = ∫₁^∞ θ^{s−1} F_∞(θ) dθ` with `F_∞ = Σ_k ψ_{G_j}(k·)` the Poisson tail
(Cvs.Xi.EImageWindowPoisson, Cvs.L2a.FullTailConvergence; dominated convergence with the uniform `O(1/θ)` bound on partial sums), and each mode is
`M_k(s)` (Cvs.Prolate.Mellin.ModeExteriorRepresentation, Cvs.Prolate.Mellin.ModeExteriorTerms). So the exterior series of Cvs.Prolate.Mellin.ExteriorSeriesBox continues `X⁰_j` to the box, where its bound
`(2P/c)(3 + log(1 + B/(2cP)))` with `P ≤ P̄_j`, `B/(2c) ≤ 2√(1 + α_j²)` (Cvs.Prolate.Mellin.UnitRungBandExtension) is at most `lemXBound x j`.
-/

noncomputable section

open MeasureTheory Set Real Filter Topology Complex
open Cvs.L2a.AngularProlateTailPositive (psi)
open Cvs.WeilForm.ThetaSpaceParseval (mellinR)
open Cvs.Xi.WindowTransformExterior (ext)
open Cvs.StepA.Edge.TransplantAngleHighZeros (sbox g0)
open Cvs.Prolate.RungSpanBernsteinNikolskii (psiD)
open Cvs.Prolate.Mellin.UnitRungBandExtension (gSrc RungData)

namespace Cvs.Prolate.Mellin.RungExteriorBoxBound
open Cvs.ZeroCounting

variable {x : ℕ} {j : Cvs.Approximant.SpineSubspace.SF x}

/-! ### The Mellin transform of the Poisson tail -/

/-- `M[1_{(1,∞)}F](s) = ∫₁^∞ θ^{s−1}F(θ) dθ`. -/
theorem mellinR_ext_eq (a : ℝ) (G : ℝ → ℝ) (s : ℂ) :
    mellinR (ext a G) s = ∫ θ in Ioi (1 : ℝ), (θ : ℂ) ^ (s - 1) * ((Cvs.Xi.EImageWindowPoisson.eimage a G θ : ℝ) : ℂ) := by
  unfold mellinR mellin Cvs.Xi.WindowTransformExterior.ext
  have e : ∀ t : ℝ, (t : ℂ) ^ (s - 1) • ((((Ioi (1 : ℝ)).indicator (Cvs.Xi.EImageWindowPoisson.eimage a G) t : ℝ)) : ℂ)
      = (Ioi (1 : ℝ)).indicator (fun t => (t : ℂ) ^ (s - 1) * ((Cvs.Xi.EImageWindowPoisson.eimage a G t : ℝ) : ℂ)) t :=
    fun t => by by_cases h : t ∈ Ioi (1 : ℝ) <;> simp [h]
  simp only [e]
  rw [setIntegral_indicator measurableSet_Ioi,
    show Ioi (0 : ℝ) ∩ Ioi 1 = Ioi 1 from Ioi_inter_Ioi.trans (by rw [max_eq_right zero_le_one])]

/-- `∫₁^∞ θ^{s−1}·(b/θ) dθ = b/(1 − s)` for `Re s < 1`. -/
theorem integral_cpow_mul_inv {s : ℂ} (hs : s.re < 1) (b : ℂ) :
    ∫ θ in Ioi (1 : ℝ), (θ : ℂ) ^ (s - 1) * (b / θ) = b / (1 - s) := by
  have e : ∀ θ ∈ Ioi (1 : ℝ), (θ : ℂ) ^ (s - 1) * (b / θ) = b * (θ : ℂ) ^ (s - 2) := fun θ hθ => by
    have hθ0 : (θ : ℂ) ≠ 0 := by exact_mod_cast (lt_trans one_pos hθ).ne'
    have h2 : (θ : ℂ) ^ (s - 2) = (θ : ℂ) ^ (s - 1) / θ := by
      rw [show s - 2 = (s - 1) - 1 by ring, Complex.cpow_sub _ _ hθ0, Complex.cpow_one]
    rw [h2]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi e, integral_const_mul,
    integral_Ioi_cpow_of_lt (by simp; linarith) one_pos]
  simp only [Complex.ofReal_one, Complex.one_cpow]
  have h1 : s - 2 + 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have h2 : 1 - s ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  field_simp
  ring

/-- The mode transform `N_k(s) = ∫₁^∞ θ^{s−1} ψ_G(kθ) dθ`. -/
def nMode (c : ℝ) (G : ℝ → ℝ) (k : ℕ) (s : ℂ) : ℂ :=
  ∫ θ in Ioi (1 : ℝ), (θ : ℂ) ^ (s - 1) * ((psi c G ((k : ℝ) * θ) : ℝ) : ℂ)

/-- **The Poisson tail in Mellin form**: on `Re s < 0`, `X_j(s) + g0_j/(2(1 − s)) = Σ_{k≥1} N_k(s)`, the modes being
summable. -/
theorem xZero_eq_tsum (D : RungData x j) {s : ℂ} (hs : s.re < 0)
    (hsum : Summable fun n : ℕ => nMode (2 * π * x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) (Pi.single j 1)) (n + 1) s) :
    mellinR (ext (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) (Pi.single j 1))) s
        + (g0 x (Pi.single j 1) : ℂ) / (2 * (1 - s))
      = ∑' n : ℕ, nMode (2 * π * x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) (Pi.single j 1)) (n + 1) s := by
  set c := 2 * π * (x : ℝ) with hc
  set G := Cvs.Approximant.DeepIndexSpineSpan.spineG c (Pi.single j 1) with hGdef
  have hc0 : 0 < c := by linarith [D.hc]
  have hx0 := Cvs.Prolate.Mellin.UnitRungBandExtension.x_pos D
  obtain ⟨G₁, G₂, hG, hG₁, hG₂c, heven, hGi⟩ := Cvs.Approximant.SpineCouplingTailPairing.spine_profile_data D.hc (Cvs.Approximant.SpineSubspace.SF_lt x) (Pi.single j 1)
  have hGc : ContinuousOn G (uIcc (-1) 1) := fun u hu => (hG u hu).continuousAt.continuousWithinAt
  have ha : 2 * π / c = 1 / x := by rw [hc]; field_simp
  -- `ψ_G` is bounded
  obtain ⟨Mp, hMp⟩ : ∃ M, ∀ t, |psi c G t| ≤ M :=
    ⟨√(2 * ∫ s in (-1 : ℝ)..1, G s ^ 2), fun t => by
      rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (Cvs.Prolate.RungSpanBernsteinNikolskii.psi_sq_le hGc t)⟩
  have hψc : Continuous (psi c G) := Cvs.Prolate.RungSpanBernsteinNikolskii.continuous_psi hGc
  -- the E-image is bounded on `(1, ∞)`
  obtain ⟨H₁, hH, hH₁, hHi⟩ := Cvs.WeilForm.TameWindowZeroSum.spineG_std D.hc (Pi.single j 1)
  obtain ⟨K, hK0, hK⟩ := Cvs.Xi.EImageMellin.abs_eimage_le (a := 1 / x) (by positivity) hH hH₁ hHi
  have hEm : Measurable (Cvs.Xi.EImageWindowPoisson.eimage (1 / x) G) :=
    Cvs.Xi.EImageMellin.measurable_eimage_of_continuousOn (by positivity) (hGc.mono (by
      rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]; exact Icc_subset_Icc (by norm_num) le_rfl))
  have hcpow : ContinuousOn (fun θ : ℝ => (θ : ℂ) ^ (s - 1)) (Ioi 1) :=
    (Cvs.Upstream.TrigMellinIntegralsContinuation.continuousOn_cpow_sub_one s).mono (Ioi_subset_Ioi zero_le_one)
  have hnorm : ∀ θ ∈ Ioi (1 : ℝ), ∀ z : ℂ, ‖(θ : ℂ) ^ (s - 1) * z‖ = θ ^ (s.re - 1) * ‖z‖ := fun θ hθ z => by
    rw [norm_mul, Cvs.Upstream.TrigMellinIntegralsContinuation.norm_cpow_sub_one (lt_trans one_pos hθ)]
  -- the two pieces of the left side
  have i1 : IntegrableOn (fun θ : ℝ => (θ : ℂ) ^ (s - 1) * ((Cvs.Xi.EImageWindowPoisson.eimage (1 / x) G θ : ℝ) : ℂ))
      (Ioi 1) := by
    refine ((Cvs.Upstream.TrigMellinIntegralsContinuation.integrableOn_rpow_re hs).mul_const K).mono'
      ((hcpow.aestronglyMeasurable measurableSet_Ioi).mul
        (Complex.continuous_ofReal.measurable.comp hEm).aestronglyMeasurable)
      ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun θ hθ => ?_))
    have hθ1 : 1 < θ := hθ
    rw [hnorm θ hθ, Complex.norm_real, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_left ((hK θ (lt_trans one_pos hθ1)).trans ?_) (Real.rpow_nonneg (by linarith) _)
    exact div_le_self hK0 hθ1.le
  set g0c : ℂ := ((1 / x * G 0 : ℝ) : ℂ) / 2 with hg0c
  have i2 : IntegrableOn (fun θ : ℝ => (θ : ℂ) ^ (s - 1) * (g0c / θ)) (Ioi 1) := by
    have hm : ContinuousOn (fun θ : ℝ => (θ : ℂ) ^ (s - 1) * (g0c / θ)) (Ioi 1) :=
      hcpow.mul (continuousOn_const.div Complex.continuous_ofReal.continuousOn fun θ hθ =>
        Complex.ofReal_ne_zero.2 (lt_trans one_pos hθ).ne')
    refine ((Cvs.Upstream.TrigMellinIntegralsContinuation.integrableOn_rpow_re hs).mul_const ‖g0c‖).mono' (hm.aestronglyMeasurable measurableSet_Ioi)
      ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun θ hθ => ?_))
    have hθ1 : 1 < θ := hθ
    rw [hnorm θ hθ, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (lt_trans one_pos hθ1)]
    exact mul_le_mul_of_nonneg_left (div_le_self (norm_nonneg _) hθ1.le) (Real.rpow_nonneg (by linarith) _)
  -- the left side as one Mellin integral of `E + g0/(2θ)`
  have hL : mellinR (ext (1 / x) G) s + (g0 x (Pi.single j 1) : ℂ) / (2 * (1 - s))
      = ∫ θ in Ioi (1 : ℝ), (θ : ℂ) ^ (s - 1)
          * ((Cvs.Xi.EImageWindowPoisson.eimage (1 / x) G θ + 1 / x * G 0 / (2 * θ) : ℝ) : ℂ) := by
    have e2 : (g0 x (Pi.single j 1) : ℂ) / (2 * (1 - s)) = g0c / (1 - s) := by
      have h1s : (1 : ℂ) - s ≠ 0 := by
        intro h; have := congrArg Complex.re h; simp at this; linarith
      rw [hg0c, g0, ← hGdef]; push_cast; field_simp
    rw [mellinR_ext_eq, e2, ← integral_cpow_mul_inv (by linarith) g0c, ← integral_add i1 i2]
    refine setIntegral_congr_fun measurableSet_Ioi fun θ hθ => ?_
    have hθ0 : (θ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (lt_trans one_pos hθ).ne'
    rw [hg0c]
    push_cast
    field_simp
  -- the Poisson tail, almost everywhere on `(1, ∞)`
  have hF : ∀ᵐ θ : ℝ ∂(volume.restrict (Ioi (1 : ℝ))),
      (θ : ℂ) ^ (s - 1) * ((Cvs.Xi.EImageWindowPoisson.eimage (1 / x) G θ + 1 / x * G 0 / (2 * θ) : ℝ) : ℂ)
        = (θ : ℂ) ^ (s - 1) * ((Cvs.L2a.FullTailConvergence.fullTail (psi c G) θ : ℝ) : ℂ) := by
    have hlat := ae_restrict_of_ae (s := Ioi (1 : ℝ)) (Cvs.Xi.EImageWindowPoisson.ae_notMem_lattice (2 * π / c))
    filter_upwards [hlat, ae_restrict_mem measurableSet_Ioi] with θ hθl hθ
    rw [Cvs.Xi.EImageWindowPoisson.fullTail_eq_eimage hG hG₁ hG₂c heven hc0 hθ hθl, ha, hGi]
    congr 2
    ring
  -- dominated convergence for the partial sums
  set BGc := Cvs.L2a.FullTailConvergence.BG c (G 1 + G (-1)) (|G₁ 1 - G₁ (-1)| + ∫ s in (-1 : ℝ)..1, |G₂ s|) with hBGc
  have hBG0 : 0 ≤ BGc := Cvs.L2a.FullTailConvergence.BG_nonneg hc0 _ (Cvs.L2a.FullTailConvergence.C1_nonneg G₁ G₂)
  have hpsum_c : ∀ M : ℕ, Continuous fun θ : ℝ => ∑ m ∈ Finset.Icc 1 M, psi c G (m * θ) := fun M =>
    continuous_finsetSum _ fun m _ => hψc.comp (continuous_const.mul continuous_id)
  have hDCT : Tendsto (fun M : ℕ => ∫ θ in Ioi (1 : ℝ), (θ : ℂ) ^ (s - 1)
        * ((∑ m ∈ Finset.Icc 1 M, psi c G (m * θ) : ℝ) : ℂ)) atTop
      (𝓝 (∫ θ in Ioi (1 : ℝ), (θ : ℂ) ^ (s - 1) * ((Cvs.L2a.FullTailConvergence.fullTail (psi c G) θ : ℝ) : ℂ))) := by
    refine tendsto_integral_of_dominated_convergence (fun θ => θ ^ (s.re - 1) * BGc)
      (fun M => (hcpow.mul (Complex.continuous_ofReal.comp (hpsum_c M)).continuousOn).aestronglyMeasurable
        measurableSet_Ioi) ((Cvs.Upstream.TrigMellinIntegralsContinuation.integrableOn_rpow_re hs).mul_const BGc)
      (fun M => (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun θ hθ => ?_))
      ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun θ hθ => ?_))
    · have hθ1 : 1 < θ := hθ
      rw [hnorm θ hθ, Complex.norm_real, Real.norm_eq_abs]
      refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (by linarith) _)
      exact (Cvs.L2a.FullTailConvergence.abs_partial_le hG hG₁ hG₂c hc0 hθ1.le M).trans (div_le_self hBG0 hθ1.le)
    · have hθ1 : 1 < θ := hθ
      have h := Cvs.L2a.FullTailConvergence.tendsto_partial hG hG₁ hG₂c hc0 hθ1
      exact ((Complex.continuous_ofReal.tendsto _).comp h).const_mul _
  -- the partial integrals are the partial sums of the modes
  have hpart : ∀ M : ℕ, ∫ θ in Ioi (1 : ℝ), (θ : ℂ) ^ (s - 1) * ((∑ m ∈ Finset.Icc 1 M, psi c G (m * θ) : ℝ) : ℂ)
      = ∑ n ∈ Finset.range M, nMode c G (n + 1) s := by
    intro M
    have hint : ∀ m ∈ Finset.Icc 1 M, IntegrableOn (fun θ : ℝ => (θ : ℂ) ^ (s - 1) * ((psi c G (m * θ) : ℝ) : ℂ))
        (Ioi 1) := fun m _ =>
      Cvs.Upstream.TrigMellinIntegralsContinuation.integrableOn_cpow_mul hs (Complex.continuous_ofReal.comp (hψc.comp
        (continuous_const.mul continuous_id))).measurable fun θ => by
          rw [Complex.norm_real, Real.norm_eq_abs]; exact hMp _
    push_cast
    simp only [Finset.mul_sum]
    rw [integral_finsetSum _ hint]
    have hI : Finset.Icc 1 M = Finset.Ico (0 + 1) (M + 1) := by ext m; simp
    rw [hI, ← Finset.sum_Ico_add' (c := 1), ← Finset.range_eq_Ico]
    refine Finset.sum_congr rfl fun n _ => ?_
    unfold nMode
    push_cast
    rfl
  have hlim := hsum.hasSum.tendsto_sum_nat
  rw [hL, integral_congr_ae hF]
  exact tendsto_nhds_unique (hDCT.congr hpart) hlim

/-! ### `RungLemmaX` -/

/-- Each mode transform is the exterior term: `N_k(s) = M_k(s)` on `Re s < 0`. -/
theorem nMode_eq_mTerm (D : RungData x j) {k : ℕ} (hk : 1 ≤ k) {s : ℂ} (hs : s.re < 0) :
    nMode (2 * π * x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) (Pi.single j 1)) k s
      = Cvs.Prolate.Mellin.ModeExteriorTerms.mTerm (psi (2 * π * x) (gSrc (2 * π * x) j)) (2 * π * x) k s := by
  have hc0 : (0 : ℝ) < 2 * π * x := by linarith [D.hc]
  have hψm : Measurable (psi (2 * π * x) (gSrc (2 * π * x) j)) :=
    (Cvs.Prolate.RungSpanBernsteinNikolskii.continuous_psi (Cvs.Prolate.Mellin.UnitRungBandExtension.continuousOn_gSrc D)).measurable
  unfold nMode
  rw [Cvs.Prolate.Mellin.ModeExteriorRepresentation.integral_cpow_psi_eq hc0 (Cvs.Prolate.Mellin.UnitRungBandExtension.continuousOn_gSrc D) (Cvs.Prolate.Mellin.UnitRungBandExtension.gSrc_even D) (Cvs.Prolate.Mellin.UnitRungBandExtension.psi_gSrc_eq D) hk hs]
  exact Cvs.Prolate.Mellin.ModeExteriorTerms.neg_two_integral_cosM_eq hψm (Cvs.Prolate.Mellin.UnitRungBandExtension.integral_psi_gSrc_sq_le D).1 hc0 hk hs

/-- **`RungLemmaX`** (caseinf-W Lemma 2_j with explicit constants): eventually every rung's
`X_{e_j} + g0_j/(2(1 − s))` continues holomorphically to the box of height `x` with sup at most `lemXBound x j`. -/
theorem rungLemmaX : Cvs.Route.Visibility.RungXBoxExplicit.RungLemmaX := by
  unfold Cvs.Route.Visibility.RungXBoxExplicit.RungLemmaX
  filter_upwards [eventually_ge_atTop 14] with x hx j
  have hx14 : (14 : ℝ) ≤ x := by exact_mod_cast hx
  have hsc : 80 ≤ 2 * π * (x : ℝ) := by nlinarith [Real.pi_gt_three]
  have D := Cvs.Prolate.Mellin.UnitRungBandExtension.rungData hsc j
  have hx1 : 1 ≤ x := by omega
  set c := 2 * π * (x : ℝ) with hc
  set ψ := psi c (gSrc c j) with hψdef
  have hψ : ∀ t, HasDerivAt ψ (psiD c (gSrc c j) t) t := fun t =>
    Cvs.Prolate.RungSpanBernsteinNikolskii.hasDerivAt_psi' (Cvs.Prolate.Mellin.UnitRungBandExtension.continuousOn_gSrc D) t
  have hψ'c : Continuous (psiD c (gSrc c j)) := Cvs.Prolate.RungSpanBernsteinNikolskii.continuous_psiD (Cvs.Prolate.Mellin.UnitRungBandExtension.continuousOn_gSrc D)
  have spec := Cvs.Prolate.Mellin.ExteriorSeriesBox.extSeries_spec hψ hψ'c (Cvs.Prolate.Mellin.UnitRungBandExtension.abs_psi_gSrc_le D) (Cvs.Prolate.Mellin.UnitRungBandExtension.integral_psi_gSrc_sq_le D).1
    (Cvs.Prolate.Mellin.UnitRungBandExtension.integral_psiD_gSrc_sq_le D).1 hx1
  refine ⟨Cvs.Prolate.Mellin.ExteriorSeriesBox.extSeries ψ c, spec.1, ?_, ?_⟩
  · -- agreement on `Re s < 1`, by the identity theorem from `Re s < 0`
    set G := Cvs.Approximant.DeepIndexSpineSpan.spineG c (Pi.single j 1) with hGdef
    set X0 : ℂ → ℂ := fun s => mellinR (ext (1 / x) G) s + (g0 x (Pi.single j 1) : ℂ) / (2 * (1 - s)) with hX0
    set U := sbox x ∩ {s : ℂ | s.re < 1} with hU
    have hUo : IsOpen U :=
      (Cvs.StepA.Edge.TransplantAngleHighZeros.isOpen_sbox _).inter (isOpen_lt Complex.continuous_re continuous_const)
    have hUc : IsPreconnected U :=
      ((Cvs.Route.Visibility.RungBoxTunnellingSum.convex_sbox _).inter (convex_halfSpace_re_lt (r := 1))).isPreconnected
    obtain ⟨H₁, hH, hH₁, hHi⟩ := Cvs.WeilForm.TameWindowZeroSum.spineG_std hsc (Pi.single j 1)
    have hxa : (0 : ℝ) < 1 / x := by positivity
    have hX0d : DifferentiableOn ℂ X0 U := by
      have h1 := (Cvs.Route.Visibility.ExteriorTransformHolomorphy.mellinR_ext_holo hxa hH hH₁ hHi).1
      have h1' : DifferentiableOn ℂ (fun s => mellinR (ext (1 / x) G) s) U := h1.mono fun s (hs : s ∈ U) => hs.2
      have hden : DifferentiableOn ℂ (fun s : ℂ => 2 * (1 - s)) U :=
        (differentiableOn_const _).mul ((differentiableOn_const _).sub differentiableOn_id)
      have h3 : DifferentiableOn ℂ (fun s : ℂ => (g0 x (Pi.single j 1) : ℂ) / (2 * (1 - s))) U := by
        refine DifferentiableOn.div (c := fun _ : ℂ => (g0 x (Pi.single j 1) : ℂ)) (d := fun s : ℂ => 2 * (1 - s))
          (differentiableOn_const _) hden fun s hs => ?_
        have h2 : s.re < 1 := hs.2
        have : (1 : ℂ) - s ≠ 0 := fun h => by
          have := congrArg Complex.re h; simp at this; linarith
        exact mul_ne_zero two_ne_zero this
      exact DifferentiableOn.add (f := fun s => mellinR (ext (1 / x) G) s)
        (g := fun s : ℂ => (g0 x (Pi.single j 1) : ℂ) / (2 * (1 - s))) h1' h3
    have hFd : DifferentiableOn ℂ (Cvs.Prolate.Mellin.ExteriorSeriesBox.extSeries ψ c) U := spec.1.mono inter_subset_left
    have hz0 : (-1 : ℂ) ∈ U := ⟨⟨by norm_num, by norm_num, by simp; linarith⟩, by norm_num⟩
    have hev : ∀ᶠ s in 𝓝 (-1 : ℂ), Cvs.Prolate.Mellin.ExteriorSeriesBox.extSeries ψ c s = X0 s := by
      have hV : IsOpen (sbox x ∩ {s : ℂ | s.re < 0}) :=
        (Cvs.StepA.Edge.TransplantAngleHighZeros.isOpen_sbox _).inter (isOpen_lt Complex.continuous_re continuous_const)
      filter_upwards [hV.mem_nhds ⟨hz0.1, by norm_num⟩] with s hs
      have hmode : ∀ n : ℕ, nMode c G (n + 1) s = Cvs.Prolate.Mellin.ModeExteriorTerms.mTerm ψ c (n + 1) s := fun n =>
        nMode_eq_mTerm D (by omega) hs.2
      have hsum : Summable fun n : ℕ => nMode c G (n + 1) s := by
        simp only [hmode]; exact spec.2.1 s hs.1
      rw [hX0]
      simp only
      rw [xZero_eq_tsum D hs.2 hsum, Cvs.Prolate.Mellin.ExteriorSeriesBox.extSeries]
      exact tsum_congr fun n => (hmode n).symm
    have heq := (hFd.analyticOnNhd hUo).eqOn_of_preconnected_of_eventuallyEq (hX0d.analyticOnNhd hUo) hUc hz0 hev
    intro s hs hs1
    exact heq ⟨hs, hs1⟩
  · -- the bound against `lemXBound`
    intro s hs
    refine (spec.2.2 s hs).trans ?_
    set P := Cvs.Prolate.Mellin.ExteriorSeriesBox.pNorm ψ with hP
    set β := Cvs.Prolate.Mellin.ExteriorSeriesBox.bConst ψ (psiD c (gSrc c j)) / (2 * c) with hβ
    have hP0 : 0 ≤ P := Cvs.Prolate.Mellin.ExteriorSeriesBox.pNorm_nonneg ψ
    have hβ0 : 0 ≤ β := div_nonneg (Cvs.Prolate.Mellin.ExteriorSeriesBox.bConst_nonneg _ _) (by positivity)
    have hlem0 : 0 ≤ Cvs.Route.Visibility.RungXBoxExplicit.lemXBound x j := by
      unfold Cvs.Route.Visibility.RungXBoxExplicit.lemXBound
      have : 0 ≤ Cvs.Route.Visibility.RungXBoxExplicit.pBar x j := Real.sqrt_nonneg _
      have : 0 ≤ Real.log (1 + 2 * √(1 + Cvs.Approximant.DeepIndexSpineSpan.alpha (2 * π * x) j ^ 2) / Cvs.Route.Visibility.RungXBoxExplicit.pBar x j) :=
        Real.log_nonneg (by have : 0 ≤ 2 * √(1 + Cvs.Approximant.DeepIndexSpineSpan.alpha (2 * π * x) j ^ 2) / Cvs.Route.Visibility.RungXBoxExplicit.pBar x j := by positivity
                            linarith)
      positivity
    rcases hP0.eq_or_lt with hPz | hPpos
    · rw [← hPz, mul_zero, zero_div, zero_mul]; exact hlem0
    have hmono := Cvs.Prolate.Mellin.ModeExteriorTerms.mul_add_log_le hPpos (Cvs.Prolate.Mellin.UnitRungBandExtension.pNorm_le_pBar D) hβ0 (Cvs.Prolate.Mellin.UnitRungBandExtension.bConst_div_le D hx)
      (by norm_num : (0 : ℝ) ≤ 3)
    unfold Cvs.Route.Visibility.RungXBoxExplicit.lemXBound
    have e1 : 2 * P / c * (3 + Real.log (1 + Cvs.Prolate.Mellin.ExteriorSeriesBox.bConst ψ (psiD c (gSrc c j)) / (2 * c * P)))
        = 2 / c * (P * (3 + Real.log (1 + β / P))) := by
      rw [hβ, div_div]; ring
    have e2 : 2 * Cvs.Route.Visibility.RungXBoxExplicit.pBar x j / (2 * π * x) * (3 + Real.log (1 + 2 * √(1 + Cvs.Approximant.DeepIndexSpineSpan.alpha (2 * π * x) j ^ 2)
        / Cvs.Route.Visibility.RungXBoxExplicit.pBar x j)) = 2 / c * (Cvs.Route.Visibility.RungXBoxExplicit.pBar x j * (3 + Real.log (1 + 2 * √(1 + Cvs.Approximant.DeepIndexSpineSpan.alpha (2 * π * x) j ^ 2)
          / Cvs.Route.Visibility.RungXBoxExplicit.pBar x j))) := by rw [hc]; ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_left hmono (by positivity)

/-! ### The route with both per-rung laws discharged -/

end Cvs.Prolate.Mellin.RungExteriorBoxBound

end
