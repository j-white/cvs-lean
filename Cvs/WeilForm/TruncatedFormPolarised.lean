import Mathlib
import Cvs.Finite.ExponentialKernelLocalises
import Cvs.StepA.OddSectorBaseBudget
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.OffWindowDefect
import Cvs.WeilForm.Archimedean.TruncatedLevyDensityBelow
import Cvs.WeilForm.Archimedean.TruncatedSymbolConstant
import Cvs.WeilForm.CentredWindowTranslate
import Cvs.WeilForm.ChannelFunctionalL2
import Cvs.WeilForm.PoleTermOperator
import Cvs.WeilForm.SelfConvolutionContinuous
import Cvs.WeilForm.SimplicityCriterionWindow
import Cvs.WeilForm.TruncOperatorQuadForm
import Cvs.WeilForm.TruncatedArchChannelSum
import Cvs.WeilForm.TruncatedFormL2Below
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowRepresentative
import Cvs.Zeta.PrimePowerSideTruncated
import Cvs.Zeta.WeilPositivityStatement

/-!
# The truncated form polarised, and its minimisers as eigenfunctions

    weilQWTrunc N P R (φ + t•ψ) = weilQWTrunc N P R φ + 2t·cross (rep φ) (rep ψ) + t²·weilQWTrunc N P R ψ

`cross` is the operator `an earlier result.truncOp` paired against the second function, less the polarised prime
side; a minimiser on a subspace's unit sphere is an eigenfunction of the operator on the window.
-/

noncomputable section

open MeasureTheory Set Cvs.Zeta.Explicit.Weil
open Cvs.Finite.ExponentialKernelLocalises Cvs.WeilForm.PoleTermOperator Cvs.WeilForm.Archimedean.OffWindowDefect

namespace Cvs.WeilForm.TruncatedFormPolarised

variable {L : ℝ}

/-! ### Integrability of the representatives -/

/-- The window representative is integrable. -/
theorem integrable_rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) :
    Integrable (Cvs.WeilForm.WindowRepresentative.rep φ) := by
  have hind : MemLp ((Ioc (0:ℝ) L).indicator fun _ => (1:ℝ)) 2 (volume : Measure ℝ) :=
    memLp_indicator_const 2 measurableSet_Ioc.nullMeasurableSet (1:ℝ) (Or.inr measure_Ioc_lt_top.ne)
  have h := (Cvs.WeilForm.WindowRepresentative.memLp_rep φ).integrable_mul hind
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [Pi.mul_apply]
  by_cases hx : x ∈ Ioc (0:ℝ) L
  · rw [indicator_of_mem hx, mul_one]
  · rw [indicator_of_notMem hx, mul_zero, Cvs.WeilForm.WindowRepresentative.rep_supp φ x hx]

/-- The representative times a continuous function is integrable. -/
theorem integrable_rep_mul (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) {c : ℝ → ℝ}
    (hc : Continuous c) : Integrable (fun x => Cvs.WeilForm.WindowRepresentative.rep φ x * c x) := by
  obtain ⟨M, hM⟩ : ∃ M, ∀ x ∈ Icc (0:ℝ) L, |c x| ≤ M := by
    obtain ⟨M, hM⟩ := (isCompact_Icc.image hc).isBounded.exists_norm_le
    exact ⟨M, fun x hx => hM _ ⟨x, hx, rfl⟩⟩
  have h := (integrable_rep φ).bdd_mul (c := |M|)
    (hc.aestronglyMeasurable.indicator measurableSet_Icc)
    (Filter.Eventually.of_forall fun x => by
      by_cases hx : x ∈ Icc (0:ℝ) L
      · rw [indicator_of_mem hx, Real.norm_eq_abs]; exact (hM x hx).trans (le_abs_self M)
      · rw [indicator_of_notMem hx]; simp)
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only []
  by_cases hx : x ∈ Ioc (0:ℝ) L
  · rw [indicator_of_mem (Ioc_subset_Icc_self hx), mul_comm]
  · rw [Cvs.WeilForm.WindowRepresentative.rep_supp φ x hx, zero_mul, mul_zero]

/-- The representative of a combination is the combination of the representatives. -/
theorem rep_add_smul_ae (φ ψ : Cvs.WeilForm.WeilFormOnWindowL2.window L) (t : ℝ) :
    Cvs.WeilForm.WindowRepresentative.rep (φ + t • ψ)
      =ᵐ[volume] fun x => Cvs.WeilForm.WindowRepresentative.rep φ x + t * Cvs.WeilForm.WindowRepresentative.rep ψ x := by
  have h1 := Cvs.WeilForm.WindowRepresentative.ae_eq_rep (φ + t • ψ)
  have h2 := Cvs.WeilForm.WindowRepresentative.ae_eq_rep φ
  have h3 := Cvs.WeilForm.WindowRepresentative.ae_eq_rep ψ
  have hcoe : ((φ + t • ψ : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ))
      = (φ : Lp ℝ 2 (volume : Measure ℝ)) + t • (ψ : Lp ℝ 2 (volume : Measure ℝ)) := by simp
  have hadd := Lp.coeFn_add (φ : Lp ℝ 2 (volume : Measure ℝ))
    (t • (ψ : Lp ℝ 2 (volume : Measure ℝ)))
  have hsmul := Lp.coeFn_smul t (ψ : Lp ℝ 2 (volume : Measure ℝ))
  filter_upwards [h1, h2, h3, hadd, hsmul] with x hx1 hx2 hx3 hx4 hx5
  rw [← hx1, ← hx2, ← hx3]
  show ((φ + t • ψ : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 volume) x
    = (φ : Lp ℝ 2 volume) x + t * (ψ : Lp ℝ 2 volume) x
  rw [hcoe, hx4, Pi.add_apply, hx5, Pi.smul_apply, smul_eq_mul]

/-! ### The polarised self-convolution -/

/-- The cross-convolution `∫ f(x) g(x+v) dx`. -/
def crossConv (f g : ℝ → ℝ) (v : ℝ) : ℝ := ∫ x : ℝ, f x * g (x + v)

/-- The polarisation of the self-convolution. -/
def polar (f g : ℝ → ℝ) (v : ℝ) : ℝ := crossConv f g v + crossConv g f v

theorem selfConvolution_eq_crossConv (f : ℝ → ℝ) (v : ℝ) :
    selfConvolution f v = crossConv f f v := rfl

/-- Shifted products of square-integrable functions are integrable. -/
theorem integrable_cross {f g : ℝ → ℝ} (hf : MemLp f 2 (volume : Measure ℝ))
    (hg : MemLp g 2 (volume : Measure ℝ)) (v : ℝ) :
    Integrable (fun x => f x * g (x + v)) :=
  hf.integrable_mul (Cvs.WeilForm.CentredWindowTranslate.memLp_translate v hg)

/-- **The self-convolution of a combination**, polarised. -/
theorem selfConvolution_add_smul {f g : ℝ → ℝ} (hf : MemLp f 2 (volume : Measure ℝ))
    (hg : MemLp g 2 (volume : Measure ℝ)) (t v : ℝ) :
    selfConvolution (fun x => f x + t * g x) v
      = selfConvolution f v + t * polar f g v + t ^ 2 * selfConvolution g v := by
  unfold selfConvolution polar crossConv
  have h1 := integrable_cross hf hf v
  have h2 := integrable_cross hf hg v
  have h3 := integrable_cross hg hf v
  have h4 := integrable_cross hg hg v
  have : (∫ x, (f x + t * g x) * (f (x + v) + t * g (x + v)))
      = ∫ x, (f x * f (x + v) + t * (f x * g (x + v) + g x * f (x + v)))
          + t ^ 2 * (g x * g (x + v)) :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  have e1 : (∫ x, (f x * f (x + v) + t * (f x * g (x + v) + g x * f (x + v)))
        + t ^ 2 * (g x * g (x + v)))
      = (∫ x, f x * f (x + v) + t * (f x * g (x + v) + g x * f (x + v)))
        + ∫ x, t ^ 2 * (g x * g (x + v)) :=
    integral_add (h1.add ((h2.add h3).const_mul t)) (h4.const_mul _)
  have e2 : (∫ x, f x * f (x + v) + t * (f x * g (x + v) + g x * f (x + v)))
      = (∫ x, f x * f (x + v)) + ∫ x, t * (f x * g (x + v) + g x * f (x + v)) :=
    integral_add h1 ((h2.add h3).const_mul t)
  have e3 : (∫ x, f x * g (x + v) + g x * f (x + v))
      = (∫ x, f x * g (x + v)) + ∫ x, g x * f (x + v) := integral_add h2 h3
  rw [this, e1, e2, integral_const_mul, integral_const_mul, e3]

/-- The channel cross term `∫₀^∞ e^{−bv} polar f g v dv`. -/
def chanCross (b : ℝ) (f g : ℝ → ℝ) : ℝ :=
  ∫ v in Ioi (0:ℝ), Real.exp (-(b * v)) * polar f g v

/-- The polarisation is a difference of self-convolutions. -/
theorem polar_eq_selfConvolution {f g : ℝ → ℝ} (hf : MemLp f 2 (volume : Measure ℝ))
    (hg : MemLp g 2 (volume : Measure ℝ)) (v : ℝ) :
    polar f g v = selfConvolution (fun x => f x + g x) v - selfConvolution f v
      - selfConvolution g v := by
  have h := selfConvolution_add_smul hf hg 1 v
  simp only [one_mul, one_pow] at h
  rw [h]; ring

/-- The polarisation is continuous. -/
theorem continuous_polar {f g : ℝ → ℝ} (hf : MemLp f 2 (volume : Measure ℝ))
    (hg : MemLp g 2 (volume : Measure ℝ)) : Continuous (polar f g) := by
  have h : polar f g = fun v => selfConvolution (fun x => f x + g x) v - selfConvolution f v
      - selfConvolution g v := funext (polar_eq_selfConvolution hf hg)
  rw [h]
  exact ((Cvs.WeilForm.SelfConvolutionContinuous.continuous_selfConvolution (hf.add hg)).sub
    (Cvs.WeilForm.SelfConvolutionContinuous.continuous_selfConvolution hf)).sub
    (Cvs.WeilForm.SelfConvolutionContinuous.continuous_selfConvolution hg)

/-! ### The polarised form -/

/-- The forward pole functional `∫ f e^{x/2}`. -/
def poleF (f : ℝ → ℝ) : ℝ := ∫ x : ℝ, f x * Real.exp (x / 2)

/-- The backward pole functional `∫ f e^{−x/2}`. -/
def poleG (f : ℝ → ℝ) : ℝ := ∫ x : ℝ, f x * Real.exp (-(x / 2))

/-- **The truncated form as pole, constant, channels and prime side**, on the representative. -/
theorem weilQWTrunc_channel (N P R : ℕ) (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) :
    Cvs.WeilForm.SimplicityCriterionWindow.weilQWTrunc N P R φ
      = 2 * poleF (Cvs.WeilForm.WindowRepresentative.rep φ) * poleG (Cvs.WeilForm.WindowRepresentative.rep φ)
        + Cvs.WeilForm.Archimedean.TruncatedSymbolConstant.truncConst N * selfConvolution (Cvs.WeilForm.WindowRepresentative.rep φ) 0
        - ∑ k ∈ Finset.range N, Cvs.WeilForm.ChannelFunctionalL2.chanInt (bIdx k)
            (Cvs.WeilForm.WindowRepresentative.rep φ)
        - primePowerSideTruncated P R (selfConvolution (Cvs.WeilForm.WindowRepresentative.rep φ)) := by
  rw [Cvs.StepA.OddSectorBaseBudget.weilQWTrunc_rep, Cvs.WeilForm.TruncatedFormL2Below.weilFormTrunc,
    Cvs.WeilForm.TruncatedArchChannelSum.archLevy_eq_channelSum φ N]
  unfold poleF poleG
  ring

/-- The prime side is linear in its argument. -/
theorem primePowerSideTruncated_add (P R : ℕ) (h₁ h₂ : ℝ → ℝ) :
    primePowerSideTruncated P R (fun v => h₁ v + h₂ v)
      = primePowerSideTruncated P R h₁ + primePowerSideTruncated P R h₂ := by
  unfold primePowerSideTruncated
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  ring

theorem primePowerSideTruncated_smul (P R : ℕ) (c : ℝ) (h : ℝ → ℝ) :
    primePowerSideTruncated P R (fun v => c * h v) = c * primePowerSideTruncated P R h := by
  unfold primePowerSideTruncated
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  ring

/-! ### The polarised form is the operator's cross form -/

/-- The joint kernel integrand of two integrable functions is integrable, by the shear. -/
theorem joint_integrable {f g : ℝ → ℝ} (hf : Integrable f) (hg : Integrable g) {b : ℝ}
    (hb : 0 ≤ b) :
    Integrable (fun p : ℝ × ℝ => g p.1 * f (p.1 + p.2) * Real.exp (-(b * |p.2|)))
      ((volume : Measure ℝ).prod volume) := by
  have hF : Integrable (fun p : ℝ × ℝ => g p.1 * f p.2 * Real.exp (-(b * |p.1 - p.2|)))
      ((volume : Measure ℝ).prod volume) := by
    have hprod : Integrable (fun p : ℝ × ℝ => g p.1 * f p.2) ((volume : Measure ℝ).prod volume) :=
      hg.mul_prod hf
    refine hprod.norm.mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
    · exact ((hg.aestronglyMeasurable.comp_quasiMeasurePreserving
        Measure.quasiMeasurePreserving_fst).mul
        (hf.aestronglyMeasurable.comp_quasiMeasurePreserving
          Measure.quasiMeasurePreserving_snd)).mul
        (by fun_prop : Continuous fun p : ℝ × ℝ => Real.exp (-(b * |p.1 - p.2|))).aestronglyMeasurable
    · rw [norm_mul]
      refine mul_le_of_le_one_right (norm_nonneg _) ?_
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
      exact neg_nonpos.mpr (mul_nonneg hb (abs_nonneg _))
  have hT : MeasurePreserving (fun z : ℝ × ℝ => (z.1, z.1 + z.2))
      ((volume : Measure ℝ).prod volume) ((volume : Measure ℝ).prod volume) :=
    measurePreserving_prod_add volume volume
  have h := (memLp_one_iff_integrable.mpr hF).comp_measurePreserving hT
  refine (memLp_one_iff_integrable.mp h).congr (Filter.Eventually.of_forall fun p => ?_)
  simp only [Function.comp]
  rw [show p.1 - (p.1 + p.2) = -p.2 by ring, abs_neg]

/-- The reflected cross-convolution is the cross-convolution with the arguments swapped. -/
theorem crossConv_neg (f g : ℝ → ℝ) (v : ℝ) : crossConv g f (-v) = crossConv f g v := by
  unfold crossConv
  rw [← integral_add_right_eq_self (fun x => g x * f (x + -v)) v]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only []
  rw [show x + v + -v = x by ring, mul_comm]

/-- **The kernel double integral of two functions is the half-line integral of their
polarisation.** -/
theorem kernel_cross_eq_half_line {f g : ℝ → ℝ} {b : ℝ}
    (hjoint : Integrable (fun p : ℝ × ℝ => g p.1 * f (p.1 + p.2) * Real.exp (-(b * |p.2|)))
      ((volume : Measure ℝ).prod volume)) :
    (∫ s, g s * ∫ u, f u * Real.exp (-(b * |s - u|)))
      = ∫ v in Ioi (0:ℝ), Real.exp (-(b * v)) * polar f g v := by
  have step1 : (∫ s, g s * ∫ u, f u * Real.exp (-(b * |s - u|)))
      = ∫ s, ∫ t, g s * f (s + t) * Real.exp (-(b * |t|)) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    simp only []
    rw [← integral_const_mul (g s) (fun u => f u * Real.exp (-(b * |s - u|)))]
    rw [← integral_add_left_eq_self (fun u => g s * (f u * Real.exp (-(b * |s - u|)))) s]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only []
    rw [show s - (s + t) = -t by ring, abs_neg]
    ring
  have hswap : (∫ s, ∫ t, g s * f (s + t) * Real.exp (-(b * |t|)))
      = ∫ t, ∫ s, g s * f (s + t) * Real.exp (-(b * |t|)) :=
    integral_integral_swap hjoint
  have step2 : (∫ s, ∫ t, g s * f (s + t) * Real.exp (-(b * |t|)))
      = ∫ t, Real.exp (-(b * |t|)) * crossConv g f t := by
    rw [hswap]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only []
    unfold crossConv
    rw [integral_mul_const (Real.exp (-(b * |t|))) (fun s => g s * f (s + t))]
    ring
  have hint : Integrable (fun t => Real.exp (-(b * |t|)) * crossConv g f t) := by
    have := hjoint.integral_prod_right
    refine this.congr (Filter.Eventually.of_forall fun t => ?_)
    simp only []
    unfold crossConv
    rw [integral_mul_const (Real.exp (-(b * |t|))) (fun s => g s * f (s + t)), mul_comm]
  have hsplit : (∫ t, Real.exp (-(b * |t|)) * crossConv g f t)
      = (∫ t in Ioi (0:ℝ), Real.exp (-(b * |t|)) * crossConv g f t)
        + ∫ t in (Ioi (0:ℝ))ᶜ, Real.exp (-(b * |t|)) * crossConv g f t :=
    (integral_add_compl (s := Ioi (0:ℝ)) measurableSet_Ioi hint).symm
  have hIic : (∫ t in (Ioi (0:ℝ))ᶜ, Real.exp (-(b * |t|)) * crossConv g f t)
      = ∫ t in Ioi (0:ℝ), Real.exp (-(b * t)) * crossConv f g t := by
    rw [show (Ioi (0:ℝ))ᶜ = Iic 0 from by simp]
    have hmp : MeasurePreserving (fun t : ℝ => -t) (volume.restrict (Iic 0))
        (volume.restrict (Ici 0)) := by
      have he : (Iic (0:ℝ)) = (fun t => -t) ⁻¹' (Ici 0) := by ext t; simp
      rw [he]
      exact (Measure.measurePreserving_neg volume).restrict_preimage measurableSet_Ici
    have hemb : MeasurableEmbedding (fun t : ℝ => -t) := (MeasurableEquiv.neg ℝ).measurableEmbedding
    have h := hmp.integral_comp hemb
      (fun t => Real.exp (-(b * |(-t)|)) * crossConv g f (-t))
    simp only [neg_neg] at h
    rw [h, integral_Ici_eq_integral_Ioi]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    rw [abs_neg, abs_of_pos ht, crossConv_neg]
  have hIoi : (∫ t in Ioi (0:ℝ), Real.exp (-(b * |t|)) * crossConv g f t)
      = ∫ t in Ioi (0:ℝ), Real.exp (-(b * t)) * crossConv g f t := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    rw [abs_of_pos ht]
  have hi1 : IntegrableOn (fun t => Real.exp (-(b * t)) * crossConv g f t) (Ioi 0) := by
    have := hint.integrableOn (s := Ioi 0)
    exact this.congr_fun (fun t ht => by simp only [abs_of_pos (mem_Ioi.mp ht)]) measurableSet_Ioi
  have hi2 : IntegrableOn (fun t => Real.exp (-(b * t)) * crossConv f g t) (Ioi 0) := by
    have := (hint.comp_neg).integrableOn (s := Ioi 0)
    refine this.congr_fun (fun t ht => ?_) measurableSet_Ioi
    simp only [abs_neg, abs_of_pos (mem_Ioi.mp ht), crossConv_neg]
  rw [step1, step2, hsplit, hIic, hIoi]
  unfold polar
  rw [← integral_add hi1 hi2]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  ring

/-- The convolution of an integrable function on the window, as the kernel integral. -/
theorem convSplit_eq_of_integrable {f : ℝ → ℝ} (hf : Integrable f) {b L s : ℝ} (h0 : 0 ≤ s)
    (hs : s ≤ L) :
    convSplit b L f s = ∫ u in (0:ℝ)..L, Real.exp (-b * |s - u|) * f u := by
  have hi : ∀ a c : ℝ, IntervalIntegrable (fun u => Real.exp (-b * |s - u|) * f u) volume a c :=
    fun a c => hf.intervalIntegrable.continuousOn_mul (by fun_prop : Continuous fun u =>
      Real.exp (-b * |s - u|)).continuousOn
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi 0 s) (hi s L)]
  have hleft : (∫ u in (0:ℝ)..s, Real.exp (-b * |s - u|) * f u)
      = Real.exp (-b * s) * leftMoment b f s := by
    rw [leftMoment, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [Set.uIcc_of_le h0] at hu
    rw [abs_of_nonneg (by linarith [hu.2] : (0:ℝ) ≤ s - u),
      show -b * (s - u) = -b * s + b * u by ring, Real.exp_add, mul_assoc]
  have hright : (∫ u in s..L, Real.exp (-b * |s - u|) * f u)
      = Real.exp (b * s) * rightMoment b L f s := by
    rw [rightMoment, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [Set.uIcc_of_le hs] at hu
    rw [abs_of_nonpos (by linarith [hu.1] : s - u ≤ (0:ℝ)),
      show -b * -(s - u) = b * s + -b * u by ring, Real.exp_add, mul_assoc]
  rw [hleft, hright, convSplit]

/-- The convolution of an integrable function is continuous. -/
theorem continuous_convSplit_of_integrable {f : ℝ → ℝ} (hf : Integrable f) (b L : ℝ) :
    Continuous (convSplit b L f) := by
  have hl : Continuous (leftMoment b f) :=
    intervalIntegral.continuous_primitive (fun a c => hf.intervalIntegrable.continuousOn_mul
      (by fun_prop : Continuous fun u => Real.exp (b * u)).continuousOn) 0
  have hr : Continuous (rightMoment b L f) := by
    have h := intervalIntegral.continuous_primitive (fun a c => hf.intervalIntegrable.continuousOn_mul
      (by fun_prop : Continuous fun u => Real.exp (-b * u)).continuousOn) L
    have : rightMoment b L f = fun s => -(∫ u in L..s, Real.exp (-b * u) * f u) := by
      funext s; rw [rightMoment, intervalIntegral.integral_symm]
    rw [this]
    exact h.neg
  unfold convSplit
  fun_prop

/-- The kernel double integral restricted to the window is the convolution paired. -/
theorem kernel_cross_window (hL : 0 ≤ L) {f g : ℝ → ℝ} (hf : Integrable f)
    (hfs : ∀ x, x ∉ Ioc (0:ℝ) L → f x = 0) (hgs : ∀ x, x ∉ Ioc (0:ℝ) L → g x = 0) (b : ℝ) :
    (∫ s, g s * ∫ u, f u * Real.exp (-(b * |s - u|)))
      = ∫ s in (0:ℝ)..L, g s * convSplit b L f s := by
  rw [Cvs.WeilForm.TruncOperatorQuadForm.integral_eq_interval hL (fun x hx => by rw [hgs x hx, zero_mul])]
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [Set.uIcc_of_le hL] at hs
  rw [convSplit_eq_of_integrable hf hs.1 hs.2,
    Cvs.WeilForm.TruncOperatorQuadForm.integral_eq_interval hL (fun x hx => by rw [hfs x hx, zero_mul])]
  congr 1
  refine intervalIntegral.integral_congr fun u _ => ?_
  rw [mul_comm, neg_mul]

/-- **The channel cross term is the convolution paired against the second function.** -/
theorem chanCross_eq (hL : 0 ≤ L) (φ ψ : Cvs.WeilForm.WeilFormOnWindowL2.window L) {b : ℝ} (hb : 0 ≤ b) :
    chanCross b (Cvs.WeilForm.WindowRepresentative.rep φ) (Cvs.WeilForm.WindowRepresentative.rep ψ)
      = ∫ s in (0:ℝ)..L, Cvs.WeilForm.WindowRepresentative.rep ψ s
          * convSplit b L (Cvs.WeilForm.WindowRepresentative.rep φ) s := by
  unfold chanCross
  rw [← kernel_cross_eq_half_line (joint_integrable (integrable_rep φ) (integrable_rep ψ) hb),
    kernel_cross_window hL (integrable_rep φ) (Cvs.WeilForm.WindowRepresentative.rep_supp φ)
      (Cvs.WeilForm.WindowRepresentative.rep_supp ψ)]

/-- **The pole cross term is the pole operator paired against the second function.** -/
theorem pole_cross (hL : 0 ≤ L) (φ ψ : Cvs.WeilForm.WeilFormOnWindowL2.window L) :
    poleF (Cvs.WeilForm.WindowRepresentative.rep φ) * poleG (Cvs.WeilForm.WindowRepresentative.rep ψ)
      + poleF (Cvs.WeilForm.WindowRepresentative.rep ψ) * poleG (Cvs.WeilForm.WindowRepresentative.rep φ)
      = ∫ s in (0:ℝ)..L, poleOp L (Cvs.WeilForm.WindowRepresentative.rep φ) s
          * Cvs.WeilForm.WindowRepresentative.rep ψ s := by
  have h1 : IntervalIntegrable (fun s : ℝ => poleA L (Cvs.WeilForm.WindowRepresentative.rep φ) * (Real.exp (-(s / 2)) * Cvs.WeilForm.WindowRepresentative.rep ψ s)) volume 0 L :=
    ((integrable_rep ψ).intervalIntegrable.continuousOn_mul
      (by fun_prop : Continuous fun s => Real.exp (-(s / 2))).continuousOn).const_mul _
  have h2 : IntervalIntegrable (fun s : ℝ => poleB L (Cvs.WeilForm.WindowRepresentative.rep φ) * (Real.exp (s / 2) * Cvs.WeilForm.WindowRepresentative.rep ψ s)) volume 0 L :=
    ((integrable_rep ψ).intervalIntegrable.continuousOn_mul
      (by fun_prop : Continuous fun s => Real.exp (s / 2)).continuousOn).const_mul _
  have hsplit : (∫ s in (0:ℝ)..L, poleOp L (Cvs.WeilForm.WindowRepresentative.rep φ) s * Cvs.WeilForm.WindowRepresentative.rep ψ s)
      = (∫ s in (0:ℝ)..L, poleA L (Cvs.WeilForm.WindowRepresentative.rep φ) * (Real.exp (-(s / 2)) * Cvs.WeilForm.WindowRepresentative.rep ψ s))
        + ∫ s in (0:ℝ)..L, poleB L (Cvs.WeilForm.WindowRepresentative.rep φ) * (Real.exp (s / 2) * Cvs.WeilForm.WindowRepresentative.rep ψ s) := by
    rw [← intervalIntegral.integral_add h1 h2]
    exact intervalIntegral.integral_congr fun s _ => by unfold poleOp; ring
  rw [hsplit, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    ← poleA, ← poleB]
  unfold poleF poleG
  rw [Cvs.WeilForm.TruncOperatorQuadForm.integral_exp_half_eq_poleA hL (Cvs.WeilForm.WindowRepresentative.rep_supp φ),
    Cvs.WeilForm.TruncOperatorQuadForm.integral_exp_half_eq_poleA hL (Cvs.WeilForm.WindowRepresentative.rep_supp ψ),
    Cvs.WeilForm.TruncOperatorQuadForm.integral_exp_neg_half_eq_poleB hL (Cvs.WeilForm.WindowRepresentative.rep_supp φ),
    Cvs.WeilForm.TruncOperatorQuadForm.integral_exp_neg_half_eq_poleB hL (Cvs.WeilForm.WindowRepresentative.rep_supp ψ)]
  ring

/-! ### Euler–Lagrange: a minimiser pairs to `λ` against the whole subspace -/

/-! ### From the pairing to the eigen-equation -/

/-- The inner product of two window classes is the window integral of the representatives. -/
theorem inner_eq_integral (hL : 0 ≤ L) (φ ψ : Cvs.WeilForm.WeilFormOnWindowL2.window L) :
    inner ℝ φ ψ = ∫ s in (0:ℝ)..L, Cvs.WeilForm.WindowRepresentative.rep φ s * Cvs.WeilForm.WindowRepresentative.rep ψ s := by
  have h : inner ℝ φ ψ = ∫ x, Cvs.WeilForm.WindowRepresentative.rep φ x * Cvs.WeilForm.WindowRepresentative.rep ψ x := by
    show inner ℝ (φ : Lp ℝ 2 (volume : Measure ℝ)) (ψ : Lp ℝ 2 (volume : Measure ℝ)) = _
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [Cvs.WeilForm.WindowRepresentative.ae_eq_rep φ, Cvs.WeilForm.WindowRepresentative.ae_eq_rep ψ]
      with x hx hy
    show (ψ : Lp ℝ 2 (volume : Measure ℝ)) x * (φ : Lp ℝ 2 (volume : Measure ℝ)) x = _
    rw [← hx, ← hy]
    unfold Cvs.WeilForm.WindowRepresentative.fn
    ring
  rw [h, Cvs.WeilForm.TruncOperatorQuadForm.integral_eq_interval hL
    (fun x hx => by rw [Cvs.WeilForm.WindowRepresentative.rep_supp φ x hx, zero_mul])]

/-! ### Regularity: an almost-everywhere eigenfunction has a continuous representative -/

/-- The convolution only sees the class on the window, at points of the window. -/
theorem convSplit_congr_ae {f g : ℝ → ℝ} (hfg : ∀ᵐ x ∂(volume.restrict (Ioc (0:ℝ) L)), f x = g x)
    (b : ℝ) {s : ℝ} (h0 : 0 ≤ s) (hs : s ≤ L) : convSplit b L f s = convSplit b L g s := by
  rw [ae_restrict_iff' measurableSet_Ioc] at hfg
  unfold convSplit leftMoment rightMoment
  congr 1
  · congr 1
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hfg] with x hx hxI
    rw [uIoc_of_le h0] at hxI
    rw [hx ⟨hxI.1, hxI.2.trans hs⟩]
  · congr 1
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hfg] with x hx hxI
    rw [uIoc_of_le hs] at hxI
    rw [hx ⟨h0.trans_lt hxI.1, hxI.2⟩]

/-- The pole operator only sees the class on the window. -/
theorem poleOp_congr_ae (hL : 0 ≤ L) {f g : ℝ → ℝ}
    (hfg : ∀ᵐ x ∂(volume.restrict (Ioc (0:ℝ) L)), f x = g x) (s : ℝ) :
    poleOp L f s = poleOp L g s := by
  rw [ae_restrict_iff' measurableSet_Ioc] at hfg
  unfold poleOp poleA poleB
  have h1 : (∫ u in (0:ℝ)..L, Real.exp (u / 2) * f u) = ∫ u in (0:ℝ)..L, Real.exp (u / 2) * g u := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hfg] with x hx hxI
    rw [uIoc_of_le hL] at hxI
    rw [hx hxI]
  have h2 : (∫ u in (0:ℝ)..L, Real.exp (-(u / 2)) * f u)
      = ∫ u in (0:ℝ)..L, Real.exp (-(u / 2)) * g u := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hfg] with x hx hxI
    rw [uIoc_of_le hL] at hxI
    rw [hx hxI]
  rw [h1, h2]

/-! ### Reflection invariance and bilinearity of the polarised form -/

/-- The representative of a sum. -/
theorem rep_add_ae (φ ψ : Cvs.WeilForm.WeilFormOnWindowL2.window L) :
    Cvs.WeilForm.WindowRepresentative.rep (φ + ψ)
      =ᵐ[volume] fun x => Cvs.WeilForm.WindowRepresentative.rep φ x + Cvs.WeilForm.WindowRepresentative.rep ψ x := by
  have h := rep_add_smul_ae φ ψ 1
  rw [one_smul] at h
  filter_upwards [h] with x hx
  rw [hx, one_mul]

/-! ### The even sector -/

/-! ### The assembly -/

/-! ### At `x = 2` the polarised prime side vanishes -/

end Cvs.WeilForm.TruncatedFormPolarised
