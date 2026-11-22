import Mathlib
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.LevyIntegrandSpectral
import Cvs.WeilForm.Archimedean.SymbolMinimumAtOrigin
import Cvs.WeilForm.Archimedean.TruncatedLevyDensityBelow
import Cvs.WeilForm.EffectiveSymbol
import Cvs.WeilForm.EffectiveSymbolThreeFacts
import Cvs.WeilForm.RegularisedSpectralMass
import Cvs.WeilForm.SelfConvolutionClassLipschitz
import Cvs.WeilForm.SelfConvolutionContinuous
import Cvs.WeilForm.SelfConvolutionCosine
import Cvs.WeilForm.SelfConvolutionTransform
import Cvs.WeilForm.SpectralDensityIntegrable
import Cvs.WeilForm.TruncatedFormL2Below
import Cvs.Zeta.PrimePowerSideTruncated
import Cvs.Zeta.WeilPositivityStatement

/-!
# The truncated effective symbol

The half-line integral `∫_{u>0} e^{−a u} cos (c u) = a/(a²+c²)` and its `1 − cos` companion give
each Lévy channel a closed spectral weight, so the truncated archimedean symbol
`truncArchSymbol N` sits above `archSymbol 0` term by term.
-/

set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Set Real Complex Cvs.Zeta.Explicit.Weil
open scoped FourierTransform

namespace Cvs.WeilForm.TruncatedEffectiveSymbol

/-- **The cosine–exponential half-line integral.**  `∫_{u>0} e^{−a u} cos (c u) du = a/(a²+c²)`,
from the complex exponential integral by taking real parts. -/
theorem cos_exp_integral (a c : ℝ) (ha : 0 < a) :
    ∫ u in Ioi (0:ℝ), Real.exp (-(a * u)) * Real.cos (c * u) = a / (a ^ 2 + c ^ 2) := by
  set z : ℂ := (-a : ℂ) + c * Complex.I with hz
  have hzre : z.re < 0 := by rw [hz]; simp; linarith
  have hcx := integral_exp_mul_complex_Ioi (a := z) hzre 0
  rw [Complex.ofReal_zero, mul_zero, Complex.exp_zero] at hcx
  have hint : IntegrableOn (fun u : ℝ => Complex.exp (z * u)) (Ioi 0) :=
    integrableOn_exp_mul_complex_Ioi hzre 0
  have hpt : ∀ u : ℝ, (Complex.exp (z * u)).re = Real.exp (-(a * u)) * Real.cos (c * u) := by
    intro u
    rw [Complex.exp_re]
    congr 1
    · congr 1; rw [hz]; simp [Complex.mul_re]
    · rw [hz]; simp [Complex.mul_im]
  have h1 : (∫ u in Ioi (0:ℝ), Real.exp (-(a * u)) * Real.cos (c * u))
      = ∫ u in Ioi (0:ℝ), RCLike.re (Complex.exp (z * u)) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun u _ => ?_)
    rw [RCLike.re_to_complex, hpt u]
  rw [h1, integral_re hint, hcx, RCLike.re_to_complex, hz]
  simp only [Complex.div_re, Complex.normSq_apply, Complex.add_re, Complex.neg_re,
    Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im,
    Complex.add_im, Complex.neg_im, Complex.mul_im, Complex.one_re, Complex.one_im,
    mul_zero, zero_mul, sub_zero, add_zero, neg_zero, mul_one, mul_neg]
  have hden : a ^ 2 + c ^ 2 ≠ 0 := by positivity
  field_simp
  ring

/-- **The `1 − cos` companion.**  `∫_{u>0} e^{−a u} (1 − cos (c u)) du = 1/a − a/(a²+c²)`. -/
theorem one_sub_cos_exp_integral (a c : ℝ) (ha : 0 < a) :
    ∫ u in Ioi (0:ℝ), Real.exp (-(a * u)) * (1 - Real.cos (c * u))
      = 1 / a - a / (a ^ 2 + c ^ 2) := by
  have hexp_int : IntegrableOn (fun u => Real.exp (-(a * u))) (Ioi (0:ℝ)) := by
    have h : (fun u : ℝ => Real.exp (-(a * u))) = fun u => Real.exp ((-a) * u) := by
      funext u; rw [neg_mul]
    rw [h]; exact integrableOn_exp_mul_Ioi (by linarith) 0
  have hcos_int : IntegrableOn (fun u => Real.exp (-(a * u)) * Real.cos (c * u)) (Ioi (0:ℝ)) := by
    refine hexp_int.mono' (by fun_prop) (Filter.Eventually.of_forall fun u => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    have := Real.abs_cos_le_one (c * u)
    nlinarith [Real.exp_pos (-(a * u))]
  have hsplit : ∫ u in Ioi (0:ℝ), Real.exp (-(a * u)) * (1 - Real.cos (c * u))
      = (∫ u in Ioi (0:ℝ), Real.exp (-(a * u)))
        - ∫ u in Ioi (0:ℝ), Real.exp (-(a * u)) * Real.cos (c * u) := by
    rw [← integral_sub hexp_int hcos_int]
    refine setIntegral_congr_fun measurableSet_Ioi (fun u _ => ?_)
    ring
  rw [hsplit, cos_exp_integral a c ha]
  congr 1
  have h : (fun u : ℝ => Real.exp (-(a * u))) = fun u => Real.exp ((-a) * u) := by
    funext u; rw [neg_mul]
  rw [h, integral_exp_mul_Ioi (by linarith : -a < 0) 0]
  simp

/-- **`specDensity` against a cosine is integrable.** -/
theorem specDensity_cos_integrable {f : ℝ → ℝ} (hf : MemLp f 2 volume) (hfint : Integrable f)
    (v : ℝ) :
    Integrable (fun t => Cvs.WeilForm.SelfConvolutionCosine.specDensity f t * Real.cos (t * v)) volume := by
  have hsd := Cvs.WeilForm.Archimedean.LevyIntegrandSpectral.integrable_specDensity hf hfint
  refine hsd.mono' (by fun_prop) (Filter.Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Cvs.WeilForm.SelfConvolutionCosine.specDensity_nonneg f t)]
  nlinarith [Cvs.WeilForm.SelfConvolutionCosine.specDensity_nonneg f t, Real.abs_cos_le_one (t * v)]

/-- **The Lévy increment is a spectral `1 − cos` integral**, pointwise in the displacement. -/
theorem selfConv_diff_spectral {f : ℝ → ℝ} (hf : MemLp f 2 volume) (hfint : Integrable f) (u : ℝ) :
    selfConvolution f 0 - selfConvolution f (u / 2)
      = ∫ t, Cvs.WeilForm.SelfConvolutionCosine.specDensity f t * (1 - Real.cos (t * (u / 2))) := by
  have hgint := Cvs.WeilForm.RegularisedSpectralMass.integrable_selfConvolution hfint
  have hW := Cvs.WeilForm.SpectralDensityIntegrable.integrable_fourier_sq hf hfint
  have hcontc : Continuous (fun w : ℝ => ((selfConvolution f w : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (Cvs.WeilForm.SelfConvolutionContinuous.continuous_selfConvolution hf)
  rw [Cvs.WeilForm.SelfConvolutionCosine.selfConvolution_eq_cosIntegral hfint hgint hW hcontc.continuousAt (v := 0),
      Cvs.WeilForm.SelfConvolutionCosine.selfConvolution_eq_cosIntegral hfint hgint hW hcontc.continuousAt
        (v := u / 2)]
  rw [← integral_sub (by simpa using specDensity_cos_integrable hf hfint 0)
        (specDensity_cos_integrable hf hfint (u / 2))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [mul_zero, Real.cos_zero, mul_one]; ring

/-- **The per-channel spectral identity.**  A single exponential channel's Lévy integral is the
channel's closed spectral weight against the density, by Fubini and the `1 − cos` integral. -/
theorem channel_spectral (a : ℝ) (ha : 0 < a) {f : ℝ → ℝ}
    (hf : MemLp f 2 volume) (hfint : Integrable f) :
    ∫ u in Ioi (0:ℝ), Real.exp (-(a * u)) * (selfConvolution f 0 - selfConvolution f (u / 2))
      = ∫ t : ℝ, Cvs.WeilForm.SelfConvolutionCosine.specDensity f t * (1 / a - a / (a ^ 2 + (t / 2) ^ 2)) := by
  set W := Cvs.WeilForm.SelfConvolutionCosine.specDensity f with hWdef
  have hsd := Cvs.WeilForm.Archimedean.LevyIntegrandSpectral.integrable_specDensity hf hfint
  have hexp : IntegrableOn (fun u => Real.exp (-(a * u))) (Ioi (0:ℝ)) := by
    have h : (fun u : ℝ => Real.exp (-(a * u))) = fun u => Real.exp ((-a) * u) := by
      funext u; rw [neg_mul]
    rw [h]; exact integrableOn_exp_mul_Ioi (by linarith) 0
  set F : ℝ → ℝ → ℝ :=
    fun u t => Real.exp (-(a * u)) * (W t * (1 - Real.cos (t * (u / 2)))) with hF
  have hdom : Integrable (fun z : ℝ × ℝ => (2 * Real.exp (-(a * z.1))) * W z.2)
      ((volume.restrict (Ioi (0:ℝ))).prod volume) :=
    Integrable.mul_prod (by simpa using hexp.const_mul 2) hsd
  have hFint : Integrable (Function.uncurry F) ((volume.restrict (Ioi (0:ℝ))).prod volume) := by
    refine hdom.mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
    · exact (Continuous.aestronglyMeasurable (by fun_prop)).mul
        ((hsd.aestronglyMeasurable.comp_snd).mul (Continuous.aestronglyMeasurable
          (continuous_const.sub (Real.continuous_cos.comp
            (continuous_snd.mul (continuous_fst.div_const 2))))))
    · simp only [Function.uncurry, hF, hWdef]
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_mul,
        abs_of_nonneg (Cvs.WeilForm.SelfConvolutionCosine.specDensity_nonneg f z.2)]
      have hc : |1 - Real.cos (z.2 * (z.1 / 2))| ≤ 2 := by
        have := Real.neg_one_le_cos (z.2 * (z.1 / 2)); have := Real.cos_le_one (z.2 * (z.1 / 2))
        rw [abs_le]; constructor <;> linarith
      have hprod : (0:ℝ) ≤ Real.exp (-(a * z.1)) * Cvs.WeilForm.SelfConvolutionCosine.specDensity f z.2
          * (2 - |1 - Real.cos (z.2 * (z.1 / 2))|) :=
        mul_nonneg (mul_nonneg (Real.exp_pos _).le (Cvs.WeilForm.SelfConvolutionCosine.specDensity_nonneg f z.2))
          (by linarith)
      nlinarith [hprod]
  have hLHS : ∫ u in Ioi (0:ℝ),
        Real.exp (-(a * u)) * (selfConvolution f 0 - selfConvolution f (u / 2))
      = ∫ u in Ioi (0:ℝ), ∫ t, F u t := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun u _ => ?_)
    rw [selfConv_diff_spectral hf hfint u, hF, integral_const_mul]
  rw [hLHS, integral_integral_swap hFint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  show ∫ u in Ioi (0:ℝ), F u t
      = Cvs.WeilForm.SelfConvolutionCosine.specDensity f t * (1 / a - a / (a ^ 2 + (t / 2) ^ 2))
  have hpull : ∫ u in Ioi (0:ℝ), F u t
      = W t * ∫ u in Ioi (0:ℝ), Real.exp (-(a * u)) * (1 - Real.cos ((t / 2) * u)) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun u _ => ?_)
    simp only [hF]
    rw [show t * (u / 2) = (t / 2) * u by ring]; ring
  rw [hpull, one_sub_cos_exp_integral a (t / 2) ha]

/-- **The truncated archimedean symbol.**  `archSymbol 0` plus the spectral weight of the first
`N` Lévy channels. -/
def truncArchSymbol (N : ℕ) (t : ℝ) : ℝ :=
  Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0
    + ∑ k ∈ Finset.range N,
        (1 / ((k : ℝ) + 1 / 4) - ((k : ℝ) + 1 / 4) / (((k : ℝ) + 1 / 4) ^ 2 + (t / 2) ^ 2))

/-- **The truncated effective symbol.**  The truncated archimedean charge less the prime refund. -/
def truncEffSymbol (N P R : ℕ) (t : ℝ) : ℝ :=
  truncArchSymbol N t - Cvs.WeilForm.EffectiveSymbol.primeSymbol P R t

/-- **Each channel weight is nonnegative**, so the truncated symbol sits above `archSymbol 0`. -/
theorem truncArchSymbol_ge (N : ℕ) (t : ℝ) :
    Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 ≤ truncArchSymbol N t := by
  unfold truncArchSymbol
  have : (0 : ℝ) ≤ ∑ k ∈ Finset.range N,
      (1 / ((k : ℝ) + 1 / 4) - ((k : ℝ) + 1 / 4) / (((k : ℝ) + 1 / 4) ^ 2 + (t / 2) ^ 2)) := by
    refine Finset.sum_nonneg (fun k _ => ?_)
    have ha : (0 : ℝ) < (k : ℝ) + 1 / 4 := by positivity
    have hd : (0 : ℝ) < ((k : ℝ) + 1 / 4) ^ 2 + (t / 2) ^ 2 := by positivity
    have hterm : 1 / ((k : ℝ) + 1 / 4)
          - ((k : ℝ) + 1 / 4) / (((k : ℝ) + 1 / 4) ^ 2 + (t / 2) ^ 2)
        = (t / 2) ^ 2 / (((k : ℝ) + 1 / 4) * (((k : ℝ) + 1 / 4) ^ 2 + (t / 2) ^ 2)) := by
      field_simp
      ring
    rw [hterm]
    positivity
  linarith

/-- **Cauchy–Schwarz bound on the self-convolution.**  `|g ⋆ g̃ (v)| ≤ g ⋆ g̃ (0)` for any `L²`
function, since it is the inner product of the class with its translate. -/
theorem abs_selfConvolution_le {f : ℝ → ℝ} (hf : MemLp f 2 volume) (v : ℝ) :
    |selfConvolution f v| ≤ selfConvolution f 0 := by
  set g : Lp ℝ 2 volume := hf.toLp f with hgdef
  have hgae : (g : ℝ → ℝ) =ᵐ[volume] f := hf.coeFn_toLp
  have hv : ∀ w : ℝ, selfConvolution f w = inner ℝ g (Cvs.WeilForm.SelfConvolutionClassLipschitz.tr w g) := by
    intro w
    rw [L2.inner_def]; unfold selfConvolution
    refine integral_congr_ae ?_
    have h3 : (fun s => f (s + w)) =ᵐ[volume] fun s => (g : ℝ → ℝ) (s + w) :=
      (measurePreserving_add_right volume w).quasiMeasurePreserving.ae_eq_comp hgae.symm
    filter_upwards [hgae, Cvs.WeilForm.SelfConvolutionClassLipschitz.tr_ae w g, h3] with s hs1 hs2 hs3
    simp [hs1, hs2, hs3, mul_comm]
  have h0 : selfConvolution f 0 = ‖g‖ ^ 2 := by
    rw [hv 0]
    have htr0 : Cvs.WeilForm.SelfConvolutionClassLipschitz.tr 0 g = g := by
      apply Lp.ext; filter_upwards [Cvs.WeilForm.SelfConvolutionClassLipschitz.tr_ae 0 g] with s hs; rw [hs]; simp
    rw [htr0, real_inner_self_eq_norm_sq]
  rw [hv v, h0]
  calc |inner ℝ g (Cvs.WeilForm.SelfConvolutionClassLipschitz.tr v g)| ≤ ‖g‖ * ‖Cvs.WeilForm.SelfConvolutionClassLipschitz.tr v g‖ :=
        abs_real_inner_le_norm g _
    _ = ‖g‖ * ‖g‖ := by rw [Cvs.WeilForm.SelfConvolutionClassLipschitz.norm_tr]
    _ = ‖g‖ ^ 2 := by ring

/-- **The self-convolution at the origin is nonnegative.** -/
theorem selfConvolution_zero_nonneg {f : ℝ → ℝ} (hf : MemLp f 2 volume) :
    0 ≤ selfConvolution f 0 :=
  le_trans (abs_nonneg _) (abs_selfConvolution_le hf 0)

/-- **Each channel's Lévy increment is integrable** on the half-line. -/
theorem channel_term_integrable {f : ℝ → ℝ} (hf : MemLp f 2 volume) (a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun u => Real.exp (-(a * u))
        * (selfConvolution f 0 - selfConvolution f (u / 2))) (Ioi (0:ℝ)) := by
  have hcont : Continuous (fun u : ℝ => selfConvolution f (u / 2)) :=
    (Cvs.WeilForm.SelfConvolutionContinuous.continuous_selfConvolution hf).comp (continuous_id.div_const 2)
  have hdom : IntegrableOn (fun u => (2 * selfConvolution f 0) * Real.exp (-(a * u)))
      (Ioi (0:ℝ)) := by
    have h : (fun u : ℝ => Real.exp (-(a * u))) = fun u => Real.exp ((-a) * u) := by
      funext u; rw [neg_mul]
    have hb : IntegrableOn (fun u => Real.exp (-(a * u))) (Ioi (0:ℝ)) := by
      rw [h]; exact integrableOn_exp_mul_Ioi (by linarith) 0
    exact hb.const_mul _
  refine hdom.mono' ?_ (Filter.Eventually.of_forall fun u => ?_)
  · exact ((Real.continuous_exp.comp (by fun_prop)).mul
      (continuous_const.sub hcont)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    have hb := abs_selfConvolution_le hf (u / 2)
    have hn := selfConvolution_zero_nonneg hf
    have hdiff : |selfConvolution f 0 - selfConvolution f (u / 2)| ≤ 2 * selfConvolution f 0 := by
      rw [abs_le]; constructor <;> [nlinarith [abs_le.mp hb]; nlinarith [abs_le.mp hb]]
    nlinarith [Real.exp_pos (-(a * u)), hdiff]

/-- **The spectral weight against the density is integrable.** -/
theorem spectral_weight_integrable {f : ℝ → ℝ} (hf : MemLp f 2 volume) (hfint : Integrable f)
    (a : ℝ) (ha : 0 < a) :
    Integrable (fun t => Cvs.WeilForm.SelfConvolutionCosine.specDensity f t
      * (1 / a - a / (a ^ 2 + (t / 2) ^ 2))) volume := by
  have hsd := Cvs.WeilForm.Archimedean.LevyIntegrandSpectral.integrable_specDensity hf hfint
  have hcw : Continuous (fun t : ℝ => 1 / a - a / (a ^ 2 + (t / 2) ^ 2)) :=
    continuous_const.sub (continuous_const.div₀
      (continuous_const.add ((continuous_id.div_const 2).pow 2))
      (fun t => (by positivity : (0:ℝ) < a ^ 2 + (t / 2) ^ 2).ne'))
  refine (hsd.const_mul (1 / a)).mono' (hsd.aestronglyMeasurable.mul hcw.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Cvs.WeilForm.SelfConvolutionCosine.specDensity_nonneg f t)]
  have hge : (0:ℝ) ≤ a / (a ^ 2 + (t / 2) ^ 2) := by positivity
  have hclosed : 1 / a - a / (a ^ 2 + (t / 2) ^ 2)
      = (t / 2) ^ 2 / (a * (a ^ 2 + (t / 2) ^ 2)) := by
    have hd : (0:ℝ) < a ^ 2 + (t / 2) ^ 2 := by positivity
    field_simp; ring
  have hwnn : (0:ℝ) ≤ 1 / a - a / (a ^ 2 + (t / 2) ^ 2) := by rw [hclosed]; positivity
  have hw : |1 / a - a / (a ^ 2 + (t / 2) ^ 2)| ≤ 1 / a := by
    rw [abs_of_nonneg hwnn]; exact sub_le_self _ hge
  have hsn := Cvs.WeilForm.SelfConvolutionCosine.specDensity_nonneg f t
  rw [show (1 / a) * Cvs.WeilForm.SelfConvolutionCosine.specDensity f t
      = Cvs.WeilForm.SelfConvolutionCosine.specDensity f t * (1 / a) from by ring]
  exact mul_le_mul_of_nonneg_left hw hsn

/-- **The truncated archimedean symbol against the density is integrable.** -/
theorem integrable_truncArch_mul (N : ℕ) {f : ℝ → ℝ} (hf : MemLp f 2 volume)
    (hfint : Integrable f) :
    Integrable (fun t => truncArchSymbol N t * Cvs.WeilForm.SelfConvolutionCosine.specDensity f t) volume := by
  have hsd := Cvs.WeilForm.Archimedean.LevyIntegrandSpectral.integrable_specDensity hf hfint
  have h1 : Integrable (fun t => Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0
      * Cvs.WeilForm.SelfConvolutionCosine.specDensity f t) volume := hsd.const_mul _
  have h2 : Integrable (fun t => ∑ k ∈ Finset.range N,
      Cvs.WeilForm.SelfConvolutionCosine.specDensity f t
        * (1 / ((k : ℝ) + 1 / 4) - ((k : ℝ) + 1 / 4)
            / (((k : ℝ) + 1 / 4) ^ 2 + (t / 2) ^ 2))) volume :=
    integrable_finsetSum _ (fun k _ => spectral_weight_integrable hf hfint _ (by positivity))
  refine (h1.add h2).congr (Filter.Eventually.of_forall fun t => ?_)
  simp only [Pi.add_apply]
  unfold truncArchSymbol
  rw [add_mul, Finset.sum_mul]
  congr 1
  exact Finset.sum_congr rfl (fun k _ => by ring)

/-- **The truncated archimedean form, spectrally.**  Its position-space arch-plus-Lévy part is
the truncated archimedean symbol against the spectral density. -/
theorem archLevy_spectral (N : ℕ) {f : ℝ → ℝ} (hf : MemLp f 2 volume) (hfint : Integrable f) :
    Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 * selfConvolution f 0
      + ∫ u in Ioi (0:ℝ), Cvs.WeilForm.Archimedean.TruncatedLevyDensityBelow.densityTrunc N u
          * (selfConvolution f 0 - selfConvolution f (u / 2))
      = ∫ t, truncArchSymbol N t * Cvs.WeilForm.SelfConvolutionCosine.specDensity f t := by
  have hgint := Cvs.WeilForm.RegularisedSpectralMass.integrable_selfConvolution hfint
  have hFsq := Cvs.WeilForm.SpectralDensityIntegrable.integrable_fourier_sq hf hfint
  have hcontc : Continuous (fun u : ℝ => ((selfConvolution f u : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (Cvs.WeilForm.SelfConvolutionContinuous.continuous_selfConvolution hf)
  have hsd := Cvs.WeilForm.Archimedean.LevyIntegrandSpectral.integrable_specDensity hf hfint
  -- split the Lévy integral over channels
  have hsplit : (∫ u in Ioi (0:ℝ), Cvs.WeilForm.Archimedean.TruncatedLevyDensityBelow.densityTrunc N u
        * (selfConvolution f 0 - selfConvolution f (u / 2)))
      = ∑ k ∈ Finset.range N, ∫ u in Ioi (0:ℝ),
          Real.exp (-(((k : ℝ) + 1 / 4) * u)) * (selfConvolution f 0 - selfConvolution f (u / 2)) := by
    have hfun : (fun u => Cvs.WeilForm.Archimedean.TruncatedLevyDensityBelow.densityTrunc N u
          * (selfConvolution f 0 - selfConvolution f (u / 2)))
        = fun u => ∑ k ∈ Finset.range N,
            Real.exp (-(((k : ℝ) + 1 / 4) * u)) * (selfConvolution f 0 - selfConvolution f (u / 2)) := by
      funext u
      unfold Cvs.WeilForm.Archimedean.TruncatedLevyDensityBelow.densityTrunc
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun k _ => by rw [show (1 / 4 + (k : ℝ)) = (k : ℝ) + 1 / 4 by ring])
    rw [hfun, integral_finsetSum _ (fun k _ => channel_term_integrable hf _ (by positivity))]
  -- each channel is a spectral integral
  have hchan : ∀ k ∈ Finset.range N,
      (∫ u in Ioi (0:ℝ), Real.exp (-(((k : ℝ) + 1 / 4) * u))
          * (selfConvolution f 0 - selfConvolution f (u / 2)))
        = ∫ t, Cvs.WeilForm.SelfConvolutionCosine.specDensity f t
            * (1 / ((k : ℝ) + 1 / 4)
              - ((k : ℝ) + 1 / 4) / (((k : ℝ) + 1 / 4) ^ 2 + (t / 2) ^ 2)) :=
    fun k _ => channel_spectral ((k : ℝ) + 1 / 4) (by positivity) hf hfint
  rw [hsplit, Finset.sum_congr rfl hchan,
    ← integral_finsetSum _ (fun k _ => spectral_weight_integrable hf hfint _ (by positivity))]
  -- add the constant term as a mass integral
  have hmass : Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 * selfConvolution f 0
      = ∫ t, Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 * Cvs.WeilForm.SelfConvolutionCosine.specDensity f t := by
    rw [integral_const_mul, Cvs.WeilForm.Archimedean.SymbolMinimumAtOrigin.integral_specDensity hfint hgint
      hcontc.continuousAt hFsq]
  rw [hmass, ← integral_add (hsd.const_mul _)
    (integrable_finsetSum _ (fun k _ => spectral_weight_integrable hf hfint _ (by positivity)))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  dsimp only
  unfold truncArchSymbol
  rw [add_mul, Finset.sum_mul]
  congr 1
  exact Finset.sum_congr rfl (fun k _ => by ring)

/-- **The truncated Weil form, through the truncated effective symbol.** -/
theorem weilFormTrunc_effective (N P R : ℕ) {f : ℝ → ℝ} (hf : MemLp f 2 volume)
    (hfint : Integrable f) :
    Cvs.WeilForm.TruncatedFormL2Below.weilFormTrunc N P R f
      = 2 * (∫ x : ℝ, f x * Real.exp (x / 2)) * (∫ x : ℝ, f x * Real.exp (-(x / 2)))
        + ∫ t : ℝ, truncEffSymbol N P R t * Cvs.WeilForm.SelfConvolutionCosine.specDensity f t := by
  unfold Cvs.WeilForm.TruncatedFormL2Below.weilFormTrunc
  rw [archLevy_spectral N hf hfint, Cvs.WeilForm.EffectiveSymbol.prime_spectral P R hf hfint,
    add_sub_assoc, ← integral_sub (integrable_truncArch_mul N hf hfint)
    (Cvs.WeilForm.EffectiveSymbolThreeFacts.integrable_prime_mul P R hf hfint)]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  unfold truncEffSymbol
  ring

end Cvs.WeilForm.TruncatedEffectiveSymbol
