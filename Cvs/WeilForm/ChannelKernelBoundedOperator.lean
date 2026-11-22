import Mathlib
import Cvs.Finite.ExponentialKernelLocalises
import Cvs.WeilForm.Archimedean.OffWindowDefect
import Cvs.WeilForm.OddCapTransfer
import Cvs.WeilForm.PoleTermOperator
import Cvs.WeilForm.TruncOperatorQuadForm
import Cvs.WeilForm.TruncatedFormPolarised
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowCutBoundedBridge
import Cvs.WeilForm.WindowRepresentative

/-!
# The channel kernel as a bounded operator on the window

    Kb φ = 1_(0,L] · ∫₀ᴸ e^{−b|s−u|} φ(u) du

The window's `L²` carries the channel integral as a continuous linear map, so the truncated form
is a constant multiple of the norm less the operator's quadratic form.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open Cvs.Finite.ExponentialKernelLocalises (convSplit)
open Cvs.WeilForm.Archimedean.OffWindowDefect (bIdx)

namespace Cvs.WeilForm.ChannelKernelBoundedOperator

variable {L b : ℝ}

/-- **Window classes with almost everywhere equal representatives agree.** -/
theorem window_ext {φ ψ : Cvs.WeilForm.WeilFormOnWindowL2.window L}
    (h : Cvs.WeilForm.WindowRepresentative.rep φ =ᵐ[volume] Cvs.WeilForm.WindowRepresentative.rep ψ) : φ = ψ := by
  refine Subtype.ext (Lp.ext ?_)
  exact ((Cvs.WeilForm.WindowRepresentative.ae_eq_rep φ).trans h).trans
    (Cvs.WeilForm.WindowRepresentative.ae_eq_rep ψ).symm

/-- The channel integral of a window representative is continuous. -/
theorem continuous_conv (b : ℝ) (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) :
    Continuous (convSplit b L (Cvs.WeilForm.WindowRepresentative.rep φ)) :=
  Cvs.WeilForm.TruncatedFormPolarised.continuous_convSplit_of_integrable
    (Cvs.WeilForm.TruncatedFormPolarised.integrable_rep φ) b L

/-- The channel image of a window class, cut back to the window. -/
def chanFn (b L : ℝ) (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) : ℝ → ℝ :=
  Cvs.WeilForm.WindowCutBoundedBridge.cut L (convSplit b L (Cvs.WeilForm.WindowRepresentative.rep φ))

/-- **The cut of a continuous function is square integrable.** -/
theorem memLp_cut_of_continuous {g : ℝ → ℝ} (hg : Continuous g) (L : ℝ) :
    MemLp (Cvs.WeilForm.WindowCutBoundedBridge.cut L g) 2 (volume : Measure ℝ) := by
  obtain ⟨C, hC⟩ := Cvs.WeilForm.WindowCutBoundedBridge.bound_of_continuous hg L
  refine (memLp_indicator_iff_restrict measurableSet_Ioc.nullMeasurableSet).2 ?_
  have hfin : IsFiniteMeasure ((volume : Measure ℝ).restrict (Ioc (0:ℝ) L)) :=
    ⟨by simp⟩
  refine MemLp.of_bound hg.aestronglyMeasurable.restrict C ?_
  rw [ae_restrict_iff' measurableSet_Ioc]
  filter_upwards with x hx
  rw [Real.norm_eq_abs]
  exact hC x hx

/-- The channel image is square integrable. -/
theorem memLp_chanFn (b : ℝ) (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) :
    MemLp (chanFn b L φ) 2 (volume : Measure ℝ) :=
  memLp_cut_of_continuous (continuous_conv b φ) L

/-- The channel image of a window class, as a window class. -/
def chanMap (b L : ℝ) (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Cvs.WeilForm.WeilFormOnWindowL2.window L :=
  ⟨(memLp_chanFn b φ).toLp _, by
    filter_upwards [(memLp_chanFn b φ).coeFn_toLp] with x hx hxne
    rw [hx]
    exact Cvs.WeilForm.WindowCutBoundedBridge.cut_of_notMem hxne⟩

/-- Its representative is the cut channel integral. -/
theorem rep_chanMap (b : ℝ) (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) :
    Cvs.WeilForm.WindowRepresentative.rep (chanMap b L φ) =ᵐ[volume] chanFn b L φ :=
  (Cvs.WeilForm.WindowRepresentative.ae_eq_rep _).symm.trans (memLp_chanFn b φ).coeFn_toLp

/-- An integrable function against the left exponential is interval integrable. -/
theorem intIntegrable_expMul {f : ℝ → ℝ} (hf : Integrable f) (c : ℝ) (a d : ℝ) :
    IntervalIntegrable (fun u => Real.exp (c * u) * f u) volume a d :=
  hf.intervalIntegrable.continuousOn_mul
    (by fun_prop : Continuous fun u => Real.exp (c * u)).continuousOn

/-- **The channel integral is additive.** -/
theorem convSplit_add {f g : ℝ → ℝ} (hf : Integrable f) (hg : Integrable g) (b L s : ℝ) :
    convSplit b L (fun u => f u + g u) s = convSplit b L f s + convSplit b L g s := by
  have hl : Cvs.Finite.ExponentialKernelLocalises.leftMoment b (fun u => f u + g u) s
      = Cvs.Finite.ExponentialKernelLocalises.leftMoment b f s + Cvs.Finite.ExponentialKernelLocalises.leftMoment b g s := by
    unfold Cvs.Finite.ExponentialKernelLocalises.leftMoment
    rw [← intervalIntegral.integral_add (intIntegrable_expMul hf b 0 s)
      (intIntegrable_expMul hg b 0 s)]
    exact intervalIntegral.integral_congr fun u _ => by ring
  have hr : Cvs.Finite.ExponentialKernelLocalises.rightMoment b L (fun u => f u + g u) s
      = Cvs.Finite.ExponentialKernelLocalises.rightMoment b L f s + Cvs.Finite.ExponentialKernelLocalises.rightMoment b L g s := by
    unfold Cvs.Finite.ExponentialKernelLocalises.rightMoment
    rw [← intervalIntegral.integral_add (intIntegrable_expMul hf (-b) s L)
      (intIntegrable_expMul hg (-b) s L)]
    exact intervalIntegral.integral_congr fun u _ => by ring
  unfold convSplit
  rw [hl, hr]
  ring

/-- **The channel integral is homogeneous.** -/
theorem convSplit_smul {f : ℝ → ℝ} (t : ℝ) (b L s : ℝ) :
    convSplit b L (fun u => t * f u) s = t * convSplit b L f s := by
  have hl : Cvs.Finite.ExponentialKernelLocalises.leftMoment b (fun u => t * f u) s
      = t * Cvs.Finite.ExponentialKernelLocalises.leftMoment b f s := by
    unfold Cvs.Finite.ExponentialKernelLocalises.leftMoment
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun u _ => by ring
  have hr : Cvs.Finite.ExponentialKernelLocalises.rightMoment b L (fun u => t * f u) s
      = t * Cvs.Finite.ExponentialKernelLocalises.rightMoment b L f s := by
    unfold Cvs.Finite.ExponentialKernelLocalises.rightMoment
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun u _ => by ring
  unfold convSplit
  rw [hl, hr]
  ring

/-- Scaling a window class scales its representative. -/
theorem rep_smul_ae (t : ℝ) (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) :
    Cvs.WeilForm.WindowRepresentative.rep (t • φ) =ᵐ[volume] fun x => t * Cvs.WeilForm.WindowRepresentative.rep φ x := by
  filter_upwards [Lp.coeFn_smul t (φ : Lp ℝ 2 (volume : Measure ℝ))] with x hx
  unfold Cvs.WeilForm.WindowRepresentative.rep Cvs.WeilForm.WindowRepresentative.fn
  by_cases h : x ∈ Ioc (0:ℝ) L
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
    simpa using hx
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, mul_zero]

/-- **The channel image is additive.** -/
theorem chanFn_add (b : ℝ) (φ ψ : Cvs.WeilForm.WeilFormOnWindowL2.window L) :
    chanFn b L (φ + ψ) = fun x => chanFn b L φ x + chanFn b L ψ x := by
  have hae : ∀ᵐ x ∂((volume : Measure ℝ).restrict (Ioc (0:ℝ) L)),
      Cvs.WeilForm.WindowRepresentative.rep (φ + ψ) x
        = (fun u => Cvs.WeilForm.WindowRepresentative.rep φ u + Cvs.WeilForm.WindowRepresentative.rep ψ u) x :=
    ae_restrict_of_ae (Cvs.WeilForm.TruncatedFormPolarised.rep_add_ae φ ψ)
  funext x
  unfold chanFn Cvs.WeilForm.WindowCutBoundedBridge.cut
  by_cases hx : x ∈ Ioc (0:ℝ) L
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, Set.indicator_of_mem hx,
      Cvs.WeilForm.TruncatedFormPolarised.convSplit_congr_ae hae b hx.1.le hx.2,
      convSplit_add (Cvs.WeilForm.TruncatedFormPolarised.integrable_rep φ)
        (Cvs.WeilForm.TruncatedFormPolarised.integrable_rep ψ)]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, Set.indicator_of_notMem hx,
      add_zero]

/-- **The channel image is homogeneous.** -/
theorem chanFn_smul (b : ℝ) (t : ℝ) (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) :
    chanFn b L (t • φ) = fun x => t * chanFn b L φ x := by
  have hae : ∀ᵐ x ∂((volume : Measure ℝ).restrict (Ioc (0:ℝ) L)),
      Cvs.WeilForm.WindowRepresentative.rep (t • φ) x
        = (fun u => t * Cvs.WeilForm.WindowRepresentative.rep φ u) x :=
    ae_restrict_of_ae (rep_smul_ae t φ)
  funext x
  unfold chanFn Cvs.WeilForm.WindowCutBoundedBridge.cut
  by_cases hx : x ∈ Ioc (0:ℝ) L
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx,
      Cvs.WeilForm.TruncatedFormPolarised.convSplit_congr_ae hae b hx.1.le hx.2, convSplit_smul]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, mul_zero]

/-- The channel map is additive. -/
theorem chanMap_add (b : ℝ) (φ ψ : Cvs.WeilForm.WeilFormOnWindowL2.window L) :
    chanMap b L (φ + ψ) = chanMap b L φ + chanMap b L ψ := by
  refine window_ext ?_
  filter_upwards [rep_chanMap b (φ + ψ), Cvs.WeilForm.TruncatedFormPolarised.rep_add_ae
    (chanMap b L φ) (chanMap b L ψ), rep_chanMap b φ, rep_chanMap b ψ] with x h1 h2 h3 h4
  rw [h1, h2, h3, h4, chanFn_add]

/-- The channel map is homogeneous. -/
theorem chanMap_smul (b : ℝ) (t : ℝ) (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) :
    chanMap b L (t • φ) = t • chanMap b L φ := by
  refine window_ext ?_
  filter_upwards [rep_chanMap b (t • φ), rep_smul_ae t (chanMap b L φ), rep_chanMap b φ]
    with x h1 h2 h3
  rw [h1, h2, h3, chanFn_smul]

/-- **The window's `L¹` mass is at most `√L` times its `L²` norm**, in squared form. -/
theorem sq_integral_abs_rep_le (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) :
    (∫ x, |Cvs.WeilForm.WindowRepresentative.rep φ x|) ^ 2 ≤ L * ‖φ‖ ^ 2 := by
  rcases le_or_gt L 0 with hL | hL
  · have hzero : ∀ x, Cvs.WeilForm.WindowRepresentative.rep φ x = 0 := fun x =>
      Cvs.WeilForm.WindowRepresentative.rep_supp φ x fun hx => absurd (hx.1.trans_le hx.2) (not_lt.2 hL)
    have h1 : (∫ x, |Cvs.WeilForm.WindowRepresentative.rep φ x|) = 0 := by simp [hzero]
    have h2 : ‖φ‖ ^ 2 = 0 := by
      rw [Cvs.WeilForm.OddCapTransfer.sq_norm_eq_integral_rep]; simp [hzero]
    rw [h1, h2]; simp
  · have hvol : (volume : Measure ℝ).real (Ioc (0:ℝ) L) = L := by
      rw [measureReal_def, Real.volume_Ioc,
        ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ L - 0)]
      ring
    have hint_abs : Integrable fun x => |Cvs.WeilForm.WindowRepresentative.rep φ x| :=
      (Cvs.WeilForm.TruncatedFormPolarised.integrable_rep φ).abs
    have hint_sq : Integrable fun x => (Cvs.WeilForm.WindowRepresentative.rep φ x) ^ 2 :=
      Cvs.WeilForm.WindowRepresentative.integrable_sq_rep φ
    have hind : Integrable ((Ioc (0:ℝ) L).indicator fun _ => (1:ℝ)) :=
      (integrable_indicator_iff measurableSet_Ioc).2
        (integrableOn_const measure_Ioc_lt_top.ne)
    set A := ∫ x, |Cvs.WeilForm.WindowRepresentative.rep φ x| with hA
    set S := ∫ x, (Cvs.WeilForm.WindowRepresentative.rep φ x) ^ 2 with hS
    have hexp : ∀ x, (|Cvs.WeilForm.WindowRepresentative.rep φ x|
        - (A / L) * (Ioc (0:ℝ) L).indicator (fun _ => (1:ℝ)) x) ^ 2
        = (Cvs.WeilForm.WindowRepresentative.rep φ x) ^ 2 - 2 * (A / L) * |Cvs.WeilForm.WindowRepresentative.rep φ x|
          + (A / L) ^ 2 * (Ioc (0:ℝ) L).indicator (fun _ => (1:ℝ)) x := by
      intro x
      by_cases hx : x ∈ Ioc (0:ℝ) L
      · rw [Set.indicator_of_mem hx]
        linear_combination sq_abs (Cvs.WeilForm.WindowRepresentative.rep φ x)
      · rw [Set.indicator_of_notMem hx, Cvs.WeilForm.WindowRepresentative.rep_supp φ x hx]; simp
    have hnn : 0 ≤ ∫ x, ((Cvs.WeilForm.WindowRepresentative.rep φ x) ^ 2
        - 2 * (A / L) * |Cvs.WeilForm.WindowRepresentative.rep φ x|
          + (A / L) ^ 2 * (Ioc (0:ℝ) L).indicator (fun _ => (1:ℝ)) x) := by
      rw [← integral_congr_ae (Filter.Eventually.of_forall hexp)]
      exact integral_nonneg fun x => sq_nonneg _
    have hi1 : Integrable fun x => (Cvs.WeilForm.WindowRepresentative.rep φ x) ^ 2
        - 2 * (A / L) * |Cvs.WeilForm.WindowRepresentative.rep φ x| :=
      hint_sq.sub (hint_abs.const_mul _)
    have hi2 : Integrable fun x => (A / L) ^ 2
        * (Ioc (0:ℝ) L).indicator (fun _ => (1:ℝ)) x := hind.const_mul _
    have e1 : (∫ x, ((Cvs.WeilForm.WindowRepresentative.rep φ x) ^ 2
        - 2 * (A / L) * |Cvs.WeilForm.WindowRepresentative.rep φ x|
          + (A / L) ^ 2 * (Ioc (0:ℝ) L).indicator (fun _ => (1:ℝ)) x))
        = (∫ x, ((Cvs.WeilForm.WindowRepresentative.rep φ x) ^ 2
            - 2 * (A / L) * |Cvs.WeilForm.WindowRepresentative.rep φ x|))
          + ∫ x, (A / L) ^ 2 * (Ioc (0:ℝ) L).indicator (fun _ => (1:ℝ)) x :=
      integral_add hi1 hi2
    have e2 : (∫ x, ((Cvs.WeilForm.WindowRepresentative.rep φ x) ^ 2
        - 2 * (A / L) * |Cvs.WeilForm.WindowRepresentative.rep φ x|)) = S - 2 * (A / L) * A := by
      rw [integral_sub hint_sq (hint_abs.const_mul _), integral_const_mul]
    have e3 : (∫ x, (A / L) ^ 2 * (Ioc (0:ℝ) L).indicator (fun _ => (1:ℝ)) x)
        = (A / L) ^ 2 * L := by
      rw [integral_const_mul, integral_indicator_const (1:ℝ) measurableSet_Ioc, smul_eq_mul,
        hvol, mul_one]
    rw [e1, e2, e3] at hnn
    have heq : S - 2 * (A / L) * A + (A / L) ^ 2 * L = S - A ^ 2 / L := by
      field_simp; ring
    rw [heq] at hnn
    rw [Cvs.WeilForm.OddCapTransfer.sq_norm_eq_integral_rep, ← hS]
    have hdiv : A ^ 2 / L ≤ S := by linarith
    have := (div_le_iff₀ hL).1 hdiv
    linarith

/-- **The channel integral is bounded by the `L¹` mass.** -/
theorem abs_convSplit_le (hb : 0 ≤ b) (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) {s : ℝ}
    (hs : s ∈ Icc (0:ℝ) L) :
    |convSplit b L (Cvs.WeilForm.WindowRepresentative.rep φ) s| ≤ ∫ x, |Cvs.WeilForm.WindowRepresentative.rep φ x| := by
  have hL : (0:ℝ) ≤ L := hs.1.trans hs.2
  have hkey : ∀ u : ℝ, |Real.exp (-b * |s - u|) * Cvs.WeilForm.WindowRepresentative.rep φ u|
      ≤ |Cvs.WeilForm.WindowRepresentative.rep φ u| := by
    intro u
    rw [abs_mul, Real.abs_exp]
    refine mul_le_of_le_one_left (abs_nonneg _) ?_
    exact Real.exp_le_one_iff.2 (by nlinarith [abs_nonneg (s - u)])
  have hi1 : IntervalIntegrable (fun u => |Real.exp (-b * |s - u|)
      * Cvs.WeilForm.WindowRepresentative.rep φ u|) volume 0 L := by
    refine (IntervalIntegrable.abs ?_)
    exact (Cvs.WeilForm.TruncatedFormPolarised.integrable_rep φ).intervalIntegrable.continuousOn_mul
      (by fun_prop : Continuous fun u => Real.exp (-b * |s - u|)).continuousOn
  have hi2 : IntervalIntegrable (fun u => |Cvs.WeilForm.WindowRepresentative.rep φ u|) volume 0 L :=
    (Cvs.WeilForm.TruncatedFormPolarised.integrable_rep φ).abs.intervalIntegrable
  calc |convSplit b L (Cvs.WeilForm.WindowRepresentative.rep φ) s|
      = |∫ u in (0:ℝ)..L, Real.exp (-b * |s - u|) * Cvs.WeilForm.WindowRepresentative.rep φ u| := by
        rw [Cvs.WeilForm.TruncatedFormPolarised.convSplit_eq_of_integrable
          (Cvs.WeilForm.TruncatedFormPolarised.integrable_rep φ) hs.1 hs.2]
    _ ≤ ∫ u in (0:ℝ)..L, |Real.exp (-b * |s - u|) * Cvs.WeilForm.WindowRepresentative.rep φ u| :=
        intervalIntegral.abs_integral_le_integral_abs hL
    _ ≤ ∫ u in (0:ℝ)..L, |Cvs.WeilForm.WindowRepresentative.rep φ u| :=
        intervalIntegral.integral_mono_on hL hi1 hi2 fun u _ => hkey u
    _ = ∫ x, |Cvs.WeilForm.WindowRepresentative.rep φ x| :=
        (Cvs.WeilForm.TruncOperatorQuadForm.integral_eq_interval hL fun x hx => by
          rw [Cvs.WeilForm.WindowRepresentative.rep_supp φ x hx, abs_zero]).symm

/-- **The channel map is bounded**, with norm at most the window length. -/
theorem norm_chanMap_le (hb : 0 ≤ b) (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) :
    ‖chanMap b L φ‖ ≤ L * ‖φ‖ := by
  rcases le_or_gt L 0 with hL | hL
  · have hzero : ∀ x, Cvs.WeilForm.WindowRepresentative.rep φ x = 0 := fun x =>
      Cvs.WeilForm.WindowRepresentative.rep_supp φ x fun hx => absurd (hx.1.trans_le hx.2) (not_lt.2 hL)
    have hcf : ∀ x, chanFn b L φ x = 0 := by
      intro x
      unfold chanFn Cvs.WeilForm.WindowCutBoundedBridge.cut
      by_cases hx : x ∈ Ioc (0:ℝ) L
      · exact absurd (hx.1.trans_le hx.2) (not_lt.2 hL)
      · exact Set.indicator_of_notMem hx _
    have h1 : ‖chanMap b L φ‖ ^ 2 = 0 := by
      rw [Cvs.WeilForm.OddCapTransfer.sq_norm_eq_integral_rep,
        integral_congr_ae ((rep_chanMap b φ).mono fun x hx => by rw [hx])]
      simp [hcf]
    have h2 : ‖φ‖ ^ 2 = 0 := by
      rw [Cvs.WeilForm.OddCapTransfer.sq_norm_eq_integral_rep]; simp [hzero]
    have h3 : ‖chanMap b L φ‖ = 0 := by nlinarith [norm_nonneg (chanMap b L φ)]
    have h4 : ‖φ‖ = 0 := by nlinarith [norm_nonneg φ]
    rw [h3, h4, mul_zero]
  · have hvol : (volume : Measure ℝ).real (Ioc (0:ℝ) L) = L := by
      rw [measureReal_def, Real.volume_Ioc,
        ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ L - 0)]
      ring
    set A := ∫ x, |Cvs.WeilForm.WindowRepresentative.rep φ x| with hA
    have hA0 : 0 ≤ A := integral_nonneg fun x => abs_nonneg _
    have hpt : ∀ x, (chanFn b L φ x) ^ 2 ≤ (Ioc (0:ℝ) L).indicator (fun _ => A ^ 2) x := by
      intro x
      unfold chanFn Cvs.WeilForm.WindowCutBoundedBridge.cut
      by_cases hx : x ∈ Ioc (0:ℝ) L
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
        have := abs_convSplit_le hb φ (s := x) ⟨hx.1.le, hx.2⟩
        nlinarith [abs_nonneg (convSplit b L (Cvs.WeilForm.WindowRepresentative.rep φ) x),
          sq_abs (convSplit b L (Cvs.WeilForm.WindowRepresentative.rep φ) x)]
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]; simp
    have hintL : Integrable ((Ioc (0:ℝ) L).indicator fun _ => A ^ 2) :=
      (integrable_indicator_iff measurableSet_Ioc).2 (integrableOn_const measure_Ioc_lt_top.ne)
    have hsq : ‖chanMap b L φ‖ ^ 2 ≤ L * A ^ 2 := by
      rw [Cvs.WeilForm.OddCapTransfer.sq_norm_eq_integral_rep,
        integral_congr_ae ((rep_chanMap b φ).mono fun x hx => by rw [hx])]
      calc (∫ x, (chanFn b L φ x) ^ 2)
          ≤ ∫ x, (Ioc (0:ℝ) L).indicator (fun _ => A ^ 2) x :=
            integral_mono ((memLp_chanFn b φ).integrable_sq) hintL hpt
        _ = L * A ^ 2 := by
            rw [integral_indicator_const (A ^ 2) measurableSet_Ioc, smul_eq_mul, hvol]
    have hcs : A ^ 2 ≤ L * ‖φ‖ ^ 2 := sq_integral_abs_rep_le φ
    have hfin : ‖chanMap b L φ‖ ^ 2 ≤ (L * ‖φ‖) ^ 2 := by nlinarith [hsq, hcs, hL.le]
    nlinarith [norm_nonneg (chanMap b L φ), mul_nonneg hL.le (norm_nonneg φ), hfin]

/-- The channel map, as a linear map on the window. -/
def chanHom (b L : ℝ) : Cvs.WeilForm.WeilFormOnWindowL2.window L →ₗ[ℝ] Cvs.WeilForm.WeilFormOnWindowL2.window L where
  toFun := chanMap b L
  map_add' := chanMap_add b
  map_smul' := by intro t φ; simpa using chanMap_smul b t φ

/-- **The channel operator**, as a continuous linear map on the window. -/
def chanCLM (b L : ℝ) (hb : 0 ≤ b) :
    Cvs.WeilForm.WeilFormOnWindowL2.window L →L[ℝ] Cvs.WeilForm.WeilFormOnWindowL2.window L :=
  LinearMap.mkContinuous (chanHom b L) L (norm_chanMap_le hb)

/-- The pole image of a window class, cut to the window. -/
def poleFn (L : ℝ) (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) : ℝ → ℝ :=
  Cvs.WeilForm.WindowCutBoundedBridge.cut L (Cvs.WeilForm.PoleTermOperator.poleOp L (Cvs.WeilForm.WindowRepresentative.rep φ))

/-- The pole image is continuous before cutting. -/
theorem continuous_poleOp (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) :
    Continuous (Cvs.WeilForm.PoleTermOperator.poleOp L (Cvs.WeilForm.WindowRepresentative.rep φ)) := by
  unfold Cvs.WeilForm.PoleTermOperator.poleOp
  fun_prop

/-- The pole image is square integrable. -/
theorem memLp_poleFn (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) :
    MemLp (poleFn L φ) 2 (volume : Measure ℝ) :=
  memLp_cut_of_continuous (continuous_poleOp φ) L

/-- The pole image of a window class, as a window class. -/
def poleMap (L : ℝ) (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Cvs.WeilForm.WeilFormOnWindowL2.window L :=
  ⟨(memLp_poleFn φ).toLp _, by
    filter_upwards [(memLp_poleFn φ).coeFn_toLp] with x hx hxne
    rw [hx]
    exact Cvs.WeilForm.WindowCutBoundedBridge.cut_of_notMem hxne⟩

/-- Its representative is the cut pole image. -/
theorem rep_poleMap (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) :
    Cvs.WeilForm.WindowRepresentative.rep (poleMap L φ) =ᵐ[volume] poleFn L φ :=
  (Cvs.WeilForm.WindowRepresentative.ae_eq_rep _).symm.trans (memLp_poleFn φ).coeFn_toLp

/-- The left pole moment is additive. -/
theorem poleA_add {f g : ℝ → ℝ} (hf : Integrable f) (hg : Integrable g) (L : ℝ) :
    Cvs.WeilForm.PoleTermOperator.poleA L (fun u => f u + g u)
      = Cvs.WeilForm.PoleTermOperator.poleA L f + Cvs.WeilForm.PoleTermOperator.poleA L g := by
  unfold Cvs.WeilForm.PoleTermOperator.poleA
  rw [← intervalIntegral.integral_add
    (hf.intervalIntegrable.continuousOn_mul
      (by fun_prop : Continuous fun s => Real.exp (s / 2)).continuousOn)
    (hg.intervalIntegrable.continuousOn_mul
      (by fun_prop : Continuous fun s => Real.exp (s / 2)).continuousOn)]
  exact intervalIntegral.integral_congr fun u _ => by simp only; ring

/-- The right pole moment is additive. -/
theorem poleB_add {f g : ℝ → ℝ} (hf : Integrable f) (hg : Integrable g) (L : ℝ) :
    Cvs.WeilForm.PoleTermOperator.poleB L (fun u => f u + g u)
      = Cvs.WeilForm.PoleTermOperator.poleB L f + Cvs.WeilForm.PoleTermOperator.poleB L g := by
  unfold Cvs.WeilForm.PoleTermOperator.poleB
  rw [← intervalIntegral.integral_add
    (hf.intervalIntegrable.continuousOn_mul
      (by fun_prop : Continuous fun s => Real.exp (-(s / 2))).continuousOn)
    (hg.intervalIntegrable.continuousOn_mul
      (by fun_prop : Continuous fun s => Real.exp (-(s / 2))).continuousOn)]
  exact intervalIntegral.integral_congr fun u _ => by simp only; ring

/-- The left pole moment is homogeneous. -/
theorem poleA_smul (t : ℝ) (f : ℝ → ℝ) (L : ℝ) :
    Cvs.WeilForm.PoleTermOperator.poleA L (fun u => t * f u)
      = t * Cvs.WeilForm.PoleTermOperator.poleA L f := by
  unfold Cvs.WeilForm.PoleTermOperator.poleA
  rw [← intervalIntegral.integral_const_mul]
  exact intervalIntegral.integral_congr fun u _ => by simp only; ring

/-- The right pole moment is homogeneous. -/
theorem poleB_smul (t : ℝ) (f : ℝ → ℝ) (L : ℝ) :
    Cvs.WeilForm.PoleTermOperator.poleB L (fun u => t * f u)
      = t * Cvs.WeilForm.PoleTermOperator.poleB L f := by
  unfold Cvs.WeilForm.PoleTermOperator.poleB
  rw [← intervalIntegral.integral_const_mul]
  exact intervalIntegral.integral_congr fun u _ => by simp only; ring

/-- The pole image is additive. -/
theorem poleFn_add (φ ψ : Cvs.WeilForm.WeilFormOnWindowL2.window L) (hL : 0 ≤ L) :
    poleFn L (φ + ψ) = fun x => poleFn L φ x + poleFn L ψ x := by
  have hae : ∀ᵐ x ∂((volume : Measure ℝ).restrict (Ioc (0:ℝ) L)),
      Cvs.WeilForm.WindowRepresentative.rep (φ + ψ) x
        = (fun u => Cvs.WeilForm.WindowRepresentative.rep φ u + Cvs.WeilForm.WindowRepresentative.rep ψ u) x :=
    ae_restrict_of_ae (Cvs.WeilForm.TruncatedFormPolarised.rep_add_ae φ ψ)
  funext x
  unfold poleFn Cvs.WeilForm.WindowCutBoundedBridge.cut
  by_cases hx : x ∈ Ioc (0:ℝ) L
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, Set.indicator_of_mem hx,
      Cvs.WeilForm.TruncatedFormPolarised.poleOp_congr_ae hL hae x]
    unfold Cvs.WeilForm.PoleTermOperator.poleOp
    rw [poleA_add (Cvs.WeilForm.TruncatedFormPolarised.integrable_rep φ)
        (Cvs.WeilForm.TruncatedFormPolarised.integrable_rep ψ),
      poleB_add (Cvs.WeilForm.TruncatedFormPolarised.integrable_rep φ)
        (Cvs.WeilForm.TruncatedFormPolarised.integrable_rep ψ)]
    ring
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, Set.indicator_of_notMem hx,
      add_zero]

/-- The pole image is homogeneous. -/
theorem poleFn_smul (t : ℝ) (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) (hL : 0 ≤ L) :
    poleFn L (t • φ) = fun x => t * poleFn L φ x := by
  have hae : ∀ᵐ x ∂((volume : Measure ℝ).restrict (Ioc (0:ℝ) L)),
      Cvs.WeilForm.WindowRepresentative.rep (t • φ) x
        = (fun u => t * Cvs.WeilForm.WindowRepresentative.rep φ u) x :=
    ae_restrict_of_ae (rep_smul_ae t φ)
  funext x
  unfold poleFn Cvs.WeilForm.WindowCutBoundedBridge.cut
  by_cases hx : x ∈ Ioc (0:ℝ) L
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx,
      Cvs.WeilForm.TruncatedFormPolarised.poleOp_congr_ae hL hae x]
    unfold Cvs.WeilForm.PoleTermOperator.poleOp
    rw [poleA_smul, poleB_smul]
    ring
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, mul_zero]

/-- The pole map is additive. -/
theorem poleMap_add (hL : 0 ≤ L) (φ ψ : Cvs.WeilForm.WeilFormOnWindowL2.window L) :
    poleMap L (φ + ψ) = poleMap L φ + poleMap L ψ := by
  refine window_ext ?_
  filter_upwards [rep_poleMap (φ + ψ), Cvs.WeilForm.TruncatedFormPolarised.rep_add_ae
    (poleMap L φ) (poleMap L ψ), rep_poleMap φ, rep_poleMap ψ] with x h1 h2 h3 h4
  rw [h1, h2, h3, h4, poleFn_add φ ψ hL]

/-- The pole map is homogeneous. -/
theorem poleMap_smul (hL : 0 ≤ L) (t : ℝ) (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) :
    poleMap L (t • φ) = t • poleMap L φ := by
  refine window_ext ?_
  filter_upwards [rep_poleMap (t • φ), rep_smul_ae t (poleMap L φ), rep_poleMap φ]
    with x h1 h2 h3
  rw [h1, h2, h3, poleFn_smul t φ hL]

/-- The pole moments are bounded by the `L¹` mass, up to the window's exponential. -/
theorem abs_poleA_le (hL : 0 ≤ L) (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) :
    |Cvs.WeilForm.PoleTermOperator.poleA L (Cvs.WeilForm.WindowRepresentative.rep φ)|
      ≤ Real.exp (L / 2) * ∫ x, |Cvs.WeilForm.WindowRepresentative.rep φ x| := by
  unfold Cvs.WeilForm.PoleTermOperator.poleA
  have hi1 : IntervalIntegrable (fun s => |Real.exp (s / 2)
      * Cvs.WeilForm.WindowRepresentative.rep φ s|) volume 0 L :=
    (((Cvs.WeilForm.TruncatedFormPolarised.integrable_rep φ).intervalIntegrable.continuousOn_mul
      (by fun_prop : Continuous fun s => Real.exp (s / 2)).continuousOn)).abs
  have hi2 : IntervalIntegrable (fun s => Real.exp (L / 2)
      * |Cvs.WeilForm.WindowRepresentative.rep φ s|) volume 0 L :=
    ((Cvs.WeilForm.TruncatedFormPolarised.integrable_rep φ).abs.intervalIntegrable).const_mul _
  calc |∫ s in (0:ℝ)..L, Real.exp (s / 2) * Cvs.WeilForm.WindowRepresentative.rep φ s|
      ≤ ∫ s in (0:ℝ)..L, |Real.exp (s / 2) * Cvs.WeilForm.WindowRepresentative.rep φ s| :=
        intervalIntegral.abs_integral_le_integral_abs hL
    _ ≤ ∫ s in (0:ℝ)..L, Real.exp (L / 2) * |Cvs.WeilForm.WindowRepresentative.rep φ s| := by
        refine intervalIntegral.integral_mono_on hL hi1 hi2 fun u hu => ?_
        rw [abs_mul, Real.abs_exp]
        exact mul_le_mul_of_nonneg_right
          (Real.exp_le_exp.2 (by linarith [hu.2])) (abs_nonneg _)
    _ = Real.exp (L / 2) * ∫ x, |Cvs.WeilForm.WindowRepresentative.rep φ x| := by
        rw [intervalIntegral.integral_const_mul,
          ← Cvs.WeilForm.TruncOperatorQuadForm.integral_eq_interval hL fun x hx => by
            rw [Cvs.WeilForm.WindowRepresentative.rep_supp φ x hx, abs_zero]]

/-- The right pole moment obeys the same bound. -/
theorem abs_poleB_le (hL : 0 ≤ L) (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) :
    |Cvs.WeilForm.PoleTermOperator.poleB L (Cvs.WeilForm.WindowRepresentative.rep φ)|
      ≤ ∫ x, |Cvs.WeilForm.WindowRepresentative.rep φ x| := by
  unfold Cvs.WeilForm.PoleTermOperator.poleB
  have hi1 : IntervalIntegrable (fun s => |Real.exp (-(s / 2))
      * Cvs.WeilForm.WindowRepresentative.rep φ s|) volume 0 L :=
    (((Cvs.WeilForm.TruncatedFormPolarised.integrable_rep φ).intervalIntegrable.continuousOn_mul
      (by fun_prop : Continuous fun s => Real.exp (-(s / 2))).continuousOn)).abs
  have hi2 : IntervalIntegrable (fun s => |Cvs.WeilForm.WindowRepresentative.rep φ s|) volume 0 L :=
    (Cvs.WeilForm.TruncatedFormPolarised.integrable_rep φ).abs.intervalIntegrable
  calc |∫ s in (0:ℝ)..L, Real.exp (-(s / 2)) * Cvs.WeilForm.WindowRepresentative.rep φ s|
      ≤ ∫ s in (0:ℝ)..L, |Real.exp (-(s / 2)) * Cvs.WeilForm.WindowRepresentative.rep φ s| :=
        intervalIntegral.abs_integral_le_integral_abs hL
    _ ≤ ∫ s in (0:ℝ)..L, |Cvs.WeilForm.WindowRepresentative.rep φ s| := by
        refine intervalIntegral.integral_mono_on hL hi1 hi2 fun u hu => ?_
        rw [abs_mul, Real.abs_exp]
        refine mul_le_of_le_one_left (abs_nonneg _) ?_
        exact Real.exp_le_one_iff.2 (by linarith [hu.1])
    _ = ∫ x, |Cvs.WeilForm.WindowRepresentative.rep φ x| :=
        (Cvs.WeilForm.TruncOperatorQuadForm.integral_eq_interval hL fun x hx => by
          rw [Cvs.WeilForm.WindowRepresentative.rep_supp φ x hx, abs_zero]).symm

/-- **The pole image is bounded by the `L¹` mass.** -/
theorem abs_poleOp_le (hL : 0 ≤ L) (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) {s : ℝ}
    (hs : s ∈ Icc (0:ℝ) L) :
    |Cvs.WeilForm.PoleTermOperator.poleOp L (Cvs.WeilForm.WindowRepresentative.rep φ) s|
      ≤ 2 * Real.exp (L / 2) * ∫ x, |Cvs.WeilForm.WindowRepresentative.rep φ x| := by
  have hA0 : 0 ≤ ∫ x, |Cvs.WeilForm.WindowRepresentative.rep φ x| :=
    integral_nonneg fun x => abs_nonneg _
  have hE : (1:ℝ) ≤ Real.exp (L / 2) := Real.one_le_exp (by linarith [hs.1, hs.2])
  have h1 := abs_poleA_le hL φ
  have h2 := abs_poleB_le hL φ
  have he1 : |Real.exp (-(s / 2))| ≤ 1 := by
    rw [Real.abs_exp]
    exact Real.exp_le_one_iff.2 (by linarith [hs.1])
  have he2 : |Real.exp (s / 2)| ≤ Real.exp (L / 2) := by
    rw [Real.abs_exp]
    exact Real.exp_le_exp.2 (by linarith [hs.2])
  unfold Cvs.WeilForm.PoleTermOperator.poleOp
  calc |Cvs.WeilForm.PoleTermOperator.poleA L (Cvs.WeilForm.WindowRepresentative.rep φ) * Real.exp (-(s / 2))
        + Cvs.WeilForm.PoleTermOperator.poleB L (Cvs.WeilForm.WindowRepresentative.rep φ) * Real.exp (s / 2)|
      ≤ |Cvs.WeilForm.PoleTermOperator.poleA L (Cvs.WeilForm.WindowRepresentative.rep φ) * Real.exp (-(s / 2))|
        + |Cvs.WeilForm.PoleTermOperator.poleB L (Cvs.WeilForm.WindowRepresentative.rep φ) * Real.exp (s / 2)| :=
        abs_add_le _ _
    _ ≤ 2 * Real.exp (L / 2) * ∫ x, |Cvs.WeilForm.WindowRepresentative.rep φ x| := by
        rw [abs_mul, abs_mul]
        have p1 : |Cvs.WeilForm.PoleTermOperator.poleA L (Cvs.WeilForm.WindowRepresentative.rep φ)|
            * |Real.exp (-(s / 2))|
            ≤ (Real.exp (L / 2) * ∫ x, |Cvs.WeilForm.WindowRepresentative.rep φ x|) * 1 :=
          mul_le_mul h1 he1 (abs_nonneg _)
            (mul_nonneg (Real.exp_nonneg _) hA0)
        have p2 : |Cvs.WeilForm.PoleTermOperator.poleB L (Cvs.WeilForm.WindowRepresentative.rep φ)|
            * |Real.exp (s / 2)|
            ≤ (∫ x, |Cvs.WeilForm.WindowRepresentative.rep φ x|) * Real.exp (L / 2) :=
          mul_le_mul h2 he2 (abs_nonneg _) hA0
        nlinarith [p1, p2, hA0, Real.exp_nonneg (L / 2)]

/-- **The pole map is bounded.** -/
theorem norm_poleMap_le (hL : 0 ≤ L) (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) :
    ‖poleMap L φ‖ ≤ (2 * Real.exp (L / 2) * L) * ‖φ‖ := by
  rcases le_or_gt L 0 with hL0 | hL0
  · have hLz : L = 0 := le_antisymm hL0 hL
    have hzero : ∀ x, Cvs.WeilForm.WindowRepresentative.rep φ x = 0 := fun x =>
      Cvs.WeilForm.WindowRepresentative.rep_supp φ x fun hx => by
        rw [hLz] at hx; exact absurd (hx.1.trans_le hx.2) (lt_irrefl 0)
    have hpf : ∀ x, poleFn L φ x = 0 := by
      intro x
      unfold poleFn Cvs.WeilForm.WindowCutBoundedBridge.cut
      by_cases hx : x ∈ Ioc (0:ℝ) L
      · rw [hLz] at hx; exact absurd (hx.1.trans_le hx.2) (lt_irrefl 0)
      · exact Set.indicator_of_notMem hx _
    have h1 : ‖poleMap L φ‖ ^ 2 = 0 := by
      rw [Cvs.WeilForm.OddCapTransfer.sq_norm_eq_integral_rep,
        integral_congr_ae ((rep_poleMap φ).mono fun x hx => by rw [hx])]
      simp [hpf]
    have h3 : ‖poleMap L φ‖ = 0 := by nlinarith [norm_nonneg (poleMap L φ)]
    have h4 : (0:ℝ) ≤ (2 * Real.exp (L / 2) * L) * ‖φ‖ :=
      mul_nonneg (mul_nonneg (by positivity) hL) (norm_nonneg φ)
    rw [h3]; exact h4
  · have hvol : (volume : Measure ℝ).real (Ioc (0:ℝ) L) = L := by
      rw [measureReal_def, Real.volume_Ioc,
        ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ L - 0)]
      ring
    set A := ∫ x, |Cvs.WeilForm.WindowRepresentative.rep φ x| with hA
    have hA0 : 0 ≤ A := integral_nonneg fun x => abs_nonneg _
    set C := 2 * Real.exp (L / 2) with hC
    have hC0 : 0 ≤ C := by
      rw [hC]; positivity
    have hpt : ∀ x, (poleFn L φ x) ^ 2
        ≤ (Ioc (0:ℝ) L).indicator (fun _ => (C * A) ^ 2) x := by
      intro x
      unfold poleFn Cvs.WeilForm.WindowCutBoundedBridge.cut
      by_cases hx : x ∈ Ioc (0:ℝ) L
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
        have hb := abs_poleOp_le hL φ (s := x) ⟨hx.1.le, hx.2⟩
        have habs := sq_abs (Cvs.WeilForm.PoleTermOperator.poleOp L (Cvs.WeilForm.WindowRepresentative.rep φ) x)
        nlinarith [abs_nonneg (Cvs.WeilForm.PoleTermOperator.poleOp L
          (Cvs.WeilForm.WindowRepresentative.rep φ) x), mul_nonneg hC0 hA0]
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]; simp
    have hintL : Integrable ((Ioc (0:ℝ) L).indicator fun _ => (C * A) ^ 2) :=
      (integrable_indicator_iff measurableSet_Ioc).2 (integrableOn_const measure_Ioc_lt_top.ne)
    have hsq : ‖poleMap L φ‖ ^ 2 ≤ L * (C * A) ^ 2 := by
      rw [Cvs.WeilForm.OddCapTransfer.sq_norm_eq_integral_rep,
        integral_congr_ae ((rep_poleMap φ).mono fun x hx => by rw [hx])]
      calc (∫ x, (poleFn L φ x) ^ 2)
          ≤ ∫ x, (Ioc (0:ℝ) L).indicator (fun _ => (C * A) ^ 2) x :=
            integral_mono ((memLp_poleFn φ).integrable_sq) hintL hpt
        _ = L * (C * A) ^ 2 := by
            rw [integral_indicator_const ((C * A) ^ 2) measurableSet_Ioc, smul_eq_mul, hvol]
    have hcs : A ^ 2 ≤ L * ‖φ‖ ^ 2 := sq_integral_abs_rep_le φ
    have hfin : ‖poleMap L φ‖ ^ 2 ≤ ((C * L) * ‖φ‖) ^ 2 := by
      calc ‖poleMap L φ‖ ^ 2 ≤ L * (C * A) ^ 2 := hsq
        _ = (L * C ^ 2) * A ^ 2 := by ring
        _ ≤ (L * C ^ 2) * (L * ‖φ‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hcs (by positivity)
        _ = ((C * L) * ‖φ‖) ^ 2 := by ring
    have hCL : (0:ℝ) ≤ (C * L) * ‖φ‖ :=
      mul_nonneg (mul_nonneg hC0 hL0.le) (norm_nonneg φ)
    have hsqrt := Real.sqrt_le_sqrt hfin
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hCL] at hsqrt

/-- The pole map, as a linear map on the window. -/
def poleHom (L : ℝ) (hL : 0 ≤ L) :
    Cvs.WeilForm.WeilFormOnWindowL2.window L →ₗ[ℝ] Cvs.WeilForm.WeilFormOnWindowL2.window L where
  toFun := poleMap L
  map_add' := poleMap_add hL
  map_smul' := by intro t φ; simpa using poleMap_smul hL t φ

/-- **The pole operator**, as a continuous linear map on the window. -/
def poleCLM (L : ℝ) (hL : 0 ≤ L) :
    Cvs.WeilForm.WeilFormOnWindowL2.window L →L[ℝ] Cvs.WeilForm.WeilFormOnWindowL2.window L :=
  LinearMap.mkContinuous (poleHom L hL) (2 * Real.exp (L / 2) * L) (norm_poleMap_le hL)

/-- **The truncated kernel operator**: the channels less the pole. -/
def kernelCLM (N : ℕ) (L : ℝ) (hL : 0 ≤ L) :
    Cvs.WeilForm.WeilFormOnWindowL2.window L →L[ℝ] Cvs.WeilForm.WeilFormOnWindowL2.window L :=
  (∑ k ∈ Finset.range N, chanCLM (bIdx k) L (Cvs.WeilForm.TruncOperatorQuadForm.bIdx_pos k).le)
    - poleCLM L hL

/-- The kernel operator acts by the channel sum less the pole. -/
theorem kernelCLM_apply (N : ℕ) (hL : 0 ≤ L) (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) :
    kernelCLM N L hL φ
      = (∑ k ∈ Finset.range N, chanMap (bIdx k) L φ) - poleMap L φ := by
  unfold kernelCLM
  rw [sub_apply, sum_apply]
  rfl

end Cvs.WeilForm.ChannelKernelBoundedOperator
