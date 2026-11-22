import Mathlib
import Cvs.Upstream.MassBoundOffSubspace
import Cvs.Upstream.PlancherelL1L2SpectralDensity
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.CappedSymbolLowers
import Cvs.WeilForm.Archimedean.LevyIntegrandSpectral
import Cvs.WeilForm.AutocorrSelfConvolution
import Cvs.WeilForm.EffectiveSymbol
import Cvs.WeilForm.EffectiveSymbolThreeFacts
import Cvs.WeilForm.LevyDomainSpectral
import Cvs.WeilForm.OddCapTransfer
import Cvs.WeilForm.PrimeSideVanishesLogTwo
import Cvs.WeilForm.SelfConvolutionCosine
import Cvs.WeilForm.SelfConvolutionTransform
import Cvs.WeilForm.SimplicityCriterionWindow
import Cvs.WeilForm.TruncatedArchCappedBudget
import Cvs.WeilForm.TruncatedEffectiveSymbol
import Cvs.WeilForm.TruncatedFormL2Below
import Cvs.WeilForm.WeilFormAeClass
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowReflectionSymmetry
import Cvs.WeilForm.WindowRepresentative
import Cvs.Zeta.PrimePowerSideTruncated
import Cvs.Zeta.WeilPositivityStatement

/-!
# The even-sector multiplier of the truncated form at `x = 2`

The capping multiplier `m`, its window functional `Msym`, and the excess `Dsym`, with the scaling
law and the level's sign, toward the even plane gap through `Cvs.WeilForm.PlaneHyperplaneTraceCap.even_plane_bound`.
-/

noncomputable section

open MeasureTheory MeasureTheory.Measure
open scoped FourierTransform

namespace Cvs.StepA.EvenMultiplierAtTwo

/-- The capping level. -/
def lamstar : ℝ := 113 / 20

theorem lamstar_pos : 0 < lamstar := by unfold lamstar; norm_num

/-- The capped-symbol multiplier at `100` channels: `m t = max 0 (1 − (truncArchSymbol−A₀)/λ*)`. -/
def mcap (t : ℝ) : ℝ :=
  max 0 (1 - (Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol 100 t - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0)
    / lamstar)

theorem mcap_nonneg (t : ℝ) : 0 ≤ mcap t := le_max_left _ _

/-- The mass functional `M v = ∫ m · specDensity (rep v)`. -/
def Msym {L : ℝ} (v : Cvs.WeilForm.WeilFormOnWindowL2.window L) : ℝ :=
  ∫ t : ℝ, mcap t * Cvs.WeilForm.SelfConvolutionCosine.specDensity (Cvs.WeilForm.WindowRepresentative.rep v) t

/-- **`M` is a quadratic form: `M (c • v) = c² · M v`.** -/
theorem Msym_smul {L : ℝ} (c : ℝ) (v : Cvs.WeilForm.WeilFormOnWindowL2.window L) :
    Msym (c • v) = c ^ 2 * Msym v := by
  unfold Msym
  rw [← integral_const_mul]
  refine integral_congr_ae ?_
  have hae := Cvs.WeilForm.LevyDomainSpectral.rep_smul_ae c v
  have h1 : Cvs.WeilForm.SelfConvolutionCosine.specDensity (Cvs.WeilForm.WindowRepresentative.rep (c • v))
      = Cvs.WeilForm.SelfConvolutionCosine.specDensity (fun x => c * Cvs.WeilForm.WindowRepresentative.rep v x) :=
    Cvs.WeilForm.LevyDomainSpectral.specDensity_congr_ae hae
  filter_upwards [] with t
  rw [h1, Cvs.WeilForm.LevyDomainSpectral.specDensity_smul c (Cvs.WeilForm.WindowRepresentative.rep v) t]
  ring

/-- **The spectral density as a cosine/sine square modulus.**  `specDensity f t` is the squared
modulus of `f`'s character pairings, `((∫ f·cos)² + (∫ f·sin)²)/(2π)`. -/
theorem specDensity_cos_sin (f : ℝ → ℝ) (t : ℝ)
    (hfcos : Integrable (fun y => f y * Real.cos (t * y)))
    (hfsin : Integrable (fun y => f y * Real.sin (t * y))) :
    Cvs.WeilForm.SelfConvolutionCosine.specDensity f t
      = ((∫ y, f y * Real.cos (t * y)) ^ 2 + (∫ y, f y * Real.sin (t * y)) ^ 2) / (2 * Real.pi) := by
  unfold Cvs.WeilForm.SelfConvolutionCosine.specDensity
  rw [Real.fourier_real_eq_integral_exp_smul]
  have hexp : ∀ y : ℝ, Complex.exp ((↑(-2 * Real.pi * y * (t / (2 * Real.pi))) : ℂ) * Complex.I)
        • Cvs.WeilForm.SelfConvolutionTransform.cf f y
      = (((f y * Real.cos (t * y) : ℝ) : ℂ)) - (((f y * Real.sin (t * y) : ℝ) : ℂ)) * Complex.I := by
    intro y
    have harg : (↑(-2 * Real.pi * y * (t / (2 * Real.pi))) : ℂ) = ((-(t * y) : ℝ) : ℂ) := by
      have hpi : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
      push_cast; field_simp
    rw [harg, Cvs.WeilForm.SelfConvolutionTransform.cf, smul_eq_mul, Complex.exp_mul_I]
    have hc : Complex.cos ((-(t * y) : ℝ) : ℂ) = ((Real.cos (t * y) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_cos]; push_cast; rw [Complex.cos_neg]
    have hs : Complex.sin ((-(t * y) : ℝ) : ℂ) = -((Real.sin (t * y) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_sin]; push_cast; rw [Complex.sin_neg]
    rw [hc, hs]; push_cast; ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hexp)]
  have hi1 : Integrable (fun y => (((f y * Real.cos (t * y) : ℝ) : ℂ))) := hfcos.ofReal
  have hi2 : Integrable (fun y => (((f y * Real.sin (t * y) : ℝ) : ℂ)) * Complex.I) :=
    (hfsin.ofReal (𝕜 := ℂ)).mul_const _
  rw [integral_sub hi1 hi2, integral_mul_const,
      integral_complex_ofReal, integral_complex_ofReal]
  set A := ∫ y, f y * Real.cos (t * y)
  set B := ∫ y, f y * Real.sin (t * y)
  have hnorm : ‖(A : ℂ) - (B : ℂ) * Complex.I‖ ^ 2 = A ^ 2 + B ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  rw [hnorm]

/-! ### Window characters and the spectral density as inner products (for the even plane gap `hpair`) -/

noncomputable def charFn (g : ℝ → ℝ) (L : ℝ) : ℝ → ℝ := (Set.Ioc 0 L).indicator g
theorem charFn_memLp {g : ℝ → ℝ} (hg : Continuous g) (hb : ∀ x, |g x| ≤ 1) (L : ℝ) :
    MemLp (charFn g L) 2 (volume : Measure ℝ) := by
  have hind : MemLp ((Set.Ioc 0 L).indicator (fun _ => (1:ℝ))) 2 (volume : Measure ℝ) :=
    memLp_indicator_const 2 measurableSet_Ioc.nullMeasurableSet 1 (Or.inr (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top))
  have hmeas : AEStronglyMeasurable (charFn g L) (volume : Measure ℝ) := by
    unfold charFn; exact (hg.aestronglyMeasurable).indicator measurableSet_Ioc
  refine hind.mono hmeas (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) x)]
  unfold charFn
  by_cases hx : x ∈ Set.Ioc 0 L
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]; exact hb x
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, abs_zero]
noncomputable def charW {g : ℝ → ℝ} (hg : Continuous g) (hb : ∀ x, |g x| ≤ 1) {L : ℝ} :
    Cvs.WeilForm.WeilFormOnWindowL2.window L :=
  ⟨(charFn_memLp hg hb L).toLp _, by
    show ∀ᵐ x ∂(volume : Measure ℝ), x ∉ Set.Ioc (0:ℝ) L → ((charFn_memLp hg hb L).toLp _ : ℝ → ℝ) x = 0
    filter_upwards [(charFn_memLp hg hb L).coeFn_toLp] with x hx hxL
    rw [hx]; unfold charFn; rw [Set.indicator_of_notMem hxL]⟩
theorem rep_charW_ae {g : ℝ → ℝ} (hg : Continuous g) (hb : ∀ x, |g x| ≤ 1) {L : ℝ} :
    Cvs.WeilForm.WindowRepresentative.rep (charW hg hb (L := L)) =ᵐ[volume] charFn g L := by
  refine (Cvs.WeilForm.WindowRepresentative.ae_eq_rep _).symm.trans ?_
  exact (charFn_memLp hg hb L).coeFn_toLp
theorem coe_charW_ae {g : ℝ → ℝ} (hg : Continuous g) (hb : ∀ x, |g x| ≤ 1) {L : ℝ} :
    ((charW hg hb (L := L) : Lp ℝ 2 (volume : Measure ℝ)) : ℝ → ℝ) =ᵐ[volume] charFn g L :=
  (charFn_memLp hg hb L).coeFn_toLp
theorem inner_charW {L : ℝ} (v : Cvs.WeilForm.WeilFormOnWindowL2.window L)
    {g : ℝ → ℝ} (hg : Continuous g) (hb : ∀ x, |g x| ≤ 1) :
    (inner ℝ (v : Lp ℝ 2 (volume : Measure ℝ))
        (charW hg hb (L := L) : Lp ℝ 2 (volume : Measure ℝ)) : ℝ)
      = ∫ x, Cvs.WeilForm.WindowRepresentative.rep v x * g x := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coe_charW_ae hg hb (L := L)] with x hxc
  have hpt : Cvs.WeilForm.WindowRepresentative.fn v x * charFn g L x = Cvs.WeilForm.WindowRepresentative.rep v x * g x := by
    unfold charFn Cvs.WeilForm.WindowRepresentative.rep
    by_cases hxA : x ∈ Set.Ioc (0:ℝ) L
    · rw [Set.indicator_of_mem hxA, Set.indicator_of_mem hxA]
    · rw [Set.indicator_of_notMem hxA, Set.indicator_of_notMem hxA, mul_zero, zero_mul]
  show inner ℝ (((v : Lp ℝ 2 (volume : Measure ℝ)) : ℝ → ℝ) x)
      (((charW hg hb (L := L) : Lp ℝ 2 (volume : Measure ℝ)) : ℝ → ℝ) x) = _
  rw [RCLike.inner_apply, starRingEnd_apply, star_trivial, hxc, mul_comm]
  exact hpt
theorem integrable_rep {L : ℝ} (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) :
    Integrable (Cvs.WeilForm.WindowRepresentative.rep φ) (volume : Measure ℝ) := by
  have h1 : MemLp ((Set.Ioc 0 L).indicator (fun _ => (1:ℝ))) 2 (volume : Measure ℝ) :=
    memLp_indicator_const 2 measurableSet_Ioc.nullMeasurableSet 1 (Or.inr (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top))
  have hmul := (Cvs.WeilForm.WindowRepresentative.memLp_rep φ).integrable_mul h1
  have heq : Cvs.WeilForm.WindowRepresentative.rep φ * (Set.Ioc 0 L).indicator (fun _ => (1:ℝ))
      = Cvs.WeilForm.WindowRepresentative.rep φ := by
    funext x; simp only [Pi.mul_apply]; unfold Cvs.WeilForm.WindowRepresentative.rep
    by_cases hx : x ∈ Set.Ioc (0:ℝ) L
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, mul_one]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, mul_zero]
  rwa [heq] at hmul
theorem integrable_rep_mul {L : ℝ} (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) {g : ℝ → ℝ}
    (hg : Continuous g) (hb : ∀ x, |g x| ≤ 1) :
    Integrable (fun x => Cvs.WeilForm.WindowRepresentative.rep φ x * g x) (volume : Measure ℝ) :=
  (integrable_rep φ).mul_bdd hg.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hb x)
noncomputable def cosW (t L : ℝ) : Cvs.WeilForm.WeilFormOnWindowL2.window L :=
  charW (g := fun s => Real.cos (t * s)) (by fun_prop) (fun x => Real.abs_cos_le_one _)
noncomputable def sinW (t L : ℝ) : Cvs.WeilForm.WeilFormOnWindowL2.window L :=
  charW (g := fun s => Real.sin (t * s)) (by fun_prop) (fun x => Real.abs_sin_le_one _)
theorem specDensity_inner {L : ℝ} (v : Cvs.WeilForm.WeilFormOnWindowL2.window L) (t : ℝ) :
    Cvs.WeilForm.SelfConvolutionCosine.specDensity (Cvs.WeilForm.WindowRepresentative.rep v) t
      = ((inner ℝ (v : Lp ℝ 2 (volume : Measure ℝ)) (cosW t L : Lp ℝ 2 (volume : Measure ℝ)) : ℝ) ^ 2
        + (inner ℝ (v : Lp ℝ 2 (volume : Measure ℝ)) (sinW t L : Lp ℝ 2 (volume : Measure ℝ)) : ℝ) ^ 2)
        / (2 * Real.pi) := by
  rw [specDensity_cos_sin (Cvs.WeilForm.WindowRepresentative.rep v) t
      (integrable_rep_mul v (by fun_prop) (fun x => Real.abs_cos_le_one _))
      (integrable_rep_mul v (by fun_prop) (fun x => Real.abs_sin_le_one _)),
    ← inner_charW v (g := fun s => Real.cos (t * s)) (by fun_prop) (fun x => Real.abs_cos_le_one _),
    ← inner_charW v (g := fun s => Real.sin (t * s)) (by fun_prop) (fun x => Real.abs_sin_le_one _)]
  rfl

/-! ### Reflection symmetry and the even density-of-states norm (for `hpair`) -/

theorem refl_integral_self (L : ℝ) {h : ℝ → ℝ} (hh : AEStronglyMeasurable h (volume : Measure ℝ)) :
    (∫ x, h (L - x)) = ∫ x, h x := by
  have hmp : MeasurePreserving (fun s => L - s) (volume : Measure ℝ) volume := measurePreserving_sub_left volume L
  have hmeas : Measurable (fun s : ℝ => L - s) := by fun_prop
  have hh' : AEStronglyMeasurable h (volume.map (fun s => L - s)) := by rw [hmp.map_eq]; exact hh
  rw [show (∫ x, h (L - x)) = ∫ y, h y ∂(volume.map (fun s => L - s)) from
    (integral_map hmeas.aemeasurable hh').symm, hmp.map_eq]
theorem even_rep {L : ℝ} {u : Cvs.WeilForm.WeilFormOnWindowL2.window L} (hu : Cvs.WeilForm.WindowReflectionSymmetry.reflW u = u) :
    Cvs.WeilForm.WindowRepresentative.rep u =ᵐ[volume] fun s => Cvs.WeilForm.WindowRepresentative.rep u (L - s) := by
  have h := Cvs.WeilForm.WindowReflectionSymmetry.rep_reflW_ae u; rw [hu] at h; exact h
theorem even_integral_refl {L : ℝ} {u : Cvs.WeilForm.WeilFormOnWindowL2.window L}
    (hu : Cvs.WeilForm.WindowReflectionSymmetry.reflW u = u) {g : ℝ → ℝ} (hg : Continuous g) :
    (∫ x, Cvs.WeilForm.WindowRepresentative.rep u x * g x) = ∫ x, Cvs.WeilForm.WindowRepresentative.rep u x * g (L - x) := by
  have hmeasu : AEStronglyMeasurable (Cvs.WeilForm.WindowRepresentative.rep u) (volume : Measure ℝ) :=
    (Cvs.WeilForm.WindowRepresentative.memLp_rep u).aestronglyMeasurable
  have hstep1 : (∫ x, Cvs.WeilForm.WindowRepresentative.rep u x * g x)
      = ∫ x, Cvs.WeilForm.WindowRepresentative.rep u (L - x) * g x := by
    refine integral_congr_ae ?_; filter_upwards [even_rep hu] with x hx; rw [hx]
  rw [hstep1]
  rw [show (∫ x, Cvs.WeilForm.WindowRepresentative.rep u (L - x) * g x)
      = ∫ x, (fun y => Cvs.WeilForm.WindowRepresentative.rep u y * g (L - y)) (L - x) from by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only; rw [show L - (L - x) = x by ring]]
  exact refl_integral_self (h := fun y => Cvs.WeilForm.WindowRepresentative.rep u y * g (L - y)) L
    (hmeasu.mul ((hg.comp (continuous_const.sub continuous_id)).aestronglyMeasurable))
theorem sym_bound (a b : ℝ) (ha : |a| ≤ 1) (hb : |b| ≤ 1) : |(a + b)/2| ≤ 1 := by
  rw [abs_le] at ha hb ⊢; constructor <;> linarith
noncomputable def ccosW (t L : ℝ) : Cvs.WeilForm.WeilFormOnWindowL2.window L :=
  charW (g := fun s => (Real.cos (t * s) + Real.cos (t * (L - s)))/2) (by fun_prop)
    (fun x => sym_bound _ _ (Real.abs_cos_le_one _) (Real.abs_cos_le_one _))
noncomputable def csinW (t L : ℝ) : Cvs.WeilForm.WeilFormOnWindowL2.window L :=
  charW (g := fun s => (Real.sin (t * s) + Real.sin (t * (L - s)))/2) (by fun_prop)
    (fun x => sym_bound _ _ (Real.abs_sin_le_one _) (Real.abs_sin_le_one _))
theorem even_inner_cosW {L : ℝ} {u : Cvs.WeilForm.WeilFormOnWindowL2.window L}
    (hu : Cvs.WeilForm.WindowReflectionSymmetry.reflW u = u) (t : ℝ) :
    (inner ℝ (u : Lp ℝ 2 (volume : Measure ℝ)) (cosW t L : Lp ℝ 2 (volume : Measure ℝ)) : ℝ)
      = inner ℝ (u : Lp ℝ 2 (volume : Measure ℝ)) (ccosW t L : Lp ℝ 2 (volume : Measure ℝ)) := by
  rw [cosW, ccosW, inner_charW u (by fun_prop) (fun x => Real.abs_cos_le_one _),
    inner_charW u (by fun_prop) (fun x => sym_bound _ _ (Real.abs_cos_le_one _) (Real.abs_cos_le_one _))]
  have hrefl := even_integral_refl hu (g := fun s => Real.cos (t * s)) (by fun_prop)
  have hsplit : (∫ x, Cvs.WeilForm.WindowRepresentative.rep u x * ((Real.cos (t * x) + Real.cos (t * (L - x)))/2))
      = ((∫ x, Cvs.WeilForm.WindowRepresentative.rep u x * Real.cos (t * x))
        + ∫ x, Cvs.WeilForm.WindowRepresentative.rep u x * Real.cos (t * (L - x)))/2 := by
    rw [← integral_add (integrable_rep_mul u (by fun_prop) (fun x => Real.abs_cos_le_one _))
      (integrable_rep_mul u (by fun_prop) (fun x => Real.abs_cos_le_one _)), ← integral_div]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_); ring
  rw [hsplit, ← hrefl]; ring
theorem even_inner_sinW {L : ℝ} {u : Cvs.WeilForm.WeilFormOnWindowL2.window L}
    (hu : Cvs.WeilForm.WindowReflectionSymmetry.reflW u = u) (t : ℝ) :
    (inner ℝ (u : Lp ℝ 2 (volume : Measure ℝ)) (sinW t L : Lp ℝ 2 (volume : Measure ℝ)) : ℝ)
      = inner ℝ (u : Lp ℝ 2 (volume : Measure ℝ)) (csinW t L : Lp ℝ 2 (volume : Measure ℝ)) := by
  rw [sinW, csinW, inner_charW u (by fun_prop) (fun x => Real.abs_sin_le_one _),
    inner_charW u (by fun_prop) (fun x => sym_bound _ _ (Real.abs_sin_le_one _) (Real.abs_sin_le_one _))]
  have hrefl := even_integral_refl hu (g := fun s => Real.sin (t * s)) (by fun_prop)
  have hsplit : (∫ x, Cvs.WeilForm.WindowRepresentative.rep u x * ((Real.sin (t * x) + Real.sin (t * (L - x)))/2))
      = ((∫ x, Cvs.WeilForm.WindowRepresentative.rep u x * Real.sin (t * x))
        + ∫ x, Cvs.WeilForm.WindowRepresentative.rep u x * Real.sin (t * (L - x)))/2 := by
    rw [← integral_add (integrable_rep_mul u (by fun_prop) (fun x => Real.abs_sin_le_one _))
      (integrable_rep_mul u (by fun_prop) (fun x => Real.abs_sin_le_one _)), ← integral_div]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_); ring
  rw [hsplit, ← hrefl]; ring
-- norm of the symmetrised character as an interval integral of its square
theorem norm_sq_charW {L : ℝ} {g : ℝ → ℝ} (hg : Continuous g) (hb : ∀ x, |g x| ≤ 1) (hL : 0 ≤ L) :
    ‖(charW hg hb (L := L) : Lp ℝ 2 (volume : Measure ℝ))‖ ^ 2 = ∫ s in (0:ℝ)..L, g s ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_charW (charW hg hb) hg hb]
  rw [show (∫ x, Cvs.WeilForm.WindowRepresentative.rep (charW hg hb (L := L)) x * g x)
      = ∫ x in Set.Ioc (0:ℝ) L, g x ^ 2 from ?_]
  · rw [← intervalIntegral.integral_of_le hL]
  · rw [← MeasureTheory.integral_indicator measurableSet_Ioc]
    refine integral_congr_ae ?_
    filter_upwards [rep_charW_ae hg hb (L := L)] with x hx
    rw [hx]; unfold charFn
    by_cases hxA : x ∈ Set.Ioc (0:ℝ) L
    · rw [Set.indicator_of_mem hxA, Set.indicator_of_mem hxA]; ring
    · rw [Set.indicator_of_notMem hxA, Set.indicator_of_notMem hxA, zero_mul]

/-! ### Elementary exponential integrals (for the constant trial's channel weights) -/

theorem u_exp_interval (c L : ℝ) (hc : 0 < c) (hL : 0 < L) :
    (∫ u in (0:ℝ)..(2*L), Real.exp (-(c*u)) * (u/2))
      = 1/(2*c^2) - Real.exp (-(2*c*L)) * (L/c + 1/(2*c^2)) := by
  have hG : ∀ u : ℝ, HasDerivAt (fun u => -Real.exp (-(c*u)) * (u/(2*c) + 1/(2*c^2)))
      (Real.exp (-(c*u)) * (u/2)) u := by
    intro u
    have hb : HasDerivAt (fun u : ℝ => -(c*u)) (-c) u := by
      simpa [neg_mul] using (hasDerivAt_id u).const_mul (-c)
    have h2 : HasDerivAt (fun u : ℝ => u/(2*c) + 1/(2*c^2)) (1/(2*c)) u :=
      ((hasDerivAt_id u).div_const (2*c)).add_const _
    have hcne : c ≠ 0 := ne_of_gt hc
    refine (((hb.exp).neg).mul h2).congr_deriv ?_
    simp only [Pi.neg_apply]
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hG u)
      (by apply Continuous.intervalIntegrable; fun_prop)]
  simp only [mul_zero, neg_zero, Real.exp_zero, zero_div, zero_add, mul_one, neg_mul]
  rw [show -(c*(2*L)) = -(2*c*L) by ring]
  ring

theorem min_exp_integral (c L : ℝ) (hc : 0 < c) (hL : 0 < L) :
    (∫ u in Set.Ioi (0:ℝ), Real.exp (-(c*u)) * min (u/2) L)
      = (1 - Real.exp (-(2*c*L))) / (2*c^2) := by
  have hcne : c ≠ 0 := ne_of_gt hc
  have hexpIoi : IntegrableOn (fun u : ℝ => Real.exp (-(c*u))) (Set.Ioi (0:ℝ)) := by
    have h : (fun u : ℝ => Real.exp (-(c*u))) = fun u => Real.exp ((-c)*u) := by funext u; rw [neg_mul]
    rw [h]; exact integrableOn_exp_mul_Ioi (a := -c) (by linarith) 0
  have hdom : IntegrableOn (fun u : ℝ => L * Real.exp (-(c*u))) (Set.Ioi (0:ℝ)) := hexpIoi.const_mul L
  have hIall : IntegrableOn (fun u => Real.exp (-(c*u)) * min (u/2) L) (Set.Ioi (0:ℝ)) := by
    refine Integrable.mono' hdom (by fun_prop)
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun u hu => ?_))
    rw [Set.mem_Ioi] at hu
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    have h0 : (0:ℝ) ≤ min (u/2) L := le_min (by linarith) hL.le
    rw [abs_of_nonneg h0, mul_comm]
    exact mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.exp_pos _).le
  have hI1 := hIall.mono_set (show Set.Ioc (0:ℝ) (2*L) ⊆ Set.Ioi 0 from fun x hx => (Set.mem_Ioc.mp hx).1)
  have hI2 := hIall.mono_set (Set.Ioi_subset_Ioi (by linarith : (0:ℝ) ≤ 2*L))
  have heq1 : (∫ u in Set.Ioc (0:ℝ) (2*L), Real.exp (-(c*u)) * min (u/2) L)
      = ∫ u in Set.Ioc (0:ℝ) (2*L), Real.exp (-(c*u)) * (u/2) := by
    refine setIntegral_congr_fun measurableSet_Ioc (fun u hu => ?_)
    rw [min_eq_left (by rw [Set.mem_Ioc] at hu; linarith [hu.2])]
  have hIoc_eq : (∫ u in Set.Ioc (0:ℝ) (2*L), Real.exp (-(c*u)) * (u/2))
      = ∫ u in (0:ℝ)..(2*L), Real.exp (-(c*u)) * (u/2) :=
    (intervalIntegral.integral_of_le (by linarith)).symm
  have heq2 : (∫ u in Set.Ioi (2*L), Real.exp (-(c*u)) * min (u/2) L)
      = L * ∫ u in Set.Ioi (2*L), Real.exp (-(c*u)) := by
    rw [← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun u hu => ?_)
    rw [Set.mem_Ioi] at hu
    rw [min_eq_right (by linarith), mul_comm]
  have hexpval : (∫ u in Set.Ioi (2*L), Real.exp (-(c*u))) = Real.exp (-(2*c*L))/c := by
    have h : (fun u : ℝ => Real.exp (-(c*u))) = fun u => Real.exp ((-c)*u) := by
      funext u; rw [neg_mul]
    rw [h, integral_exp_mul_Ioi (a := -c) (by linarith) (2*L), show (-c)*(2*L) = -(2*c*L) by ring]
    field_simp
  rw [← Set.Ioc_union_Ioi_eq_Ioi (by linarith : (0:ℝ) ≤ 2*L),
    setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hI1 hI2,
    heq1, hIoc_eq, u_exp_interval c L hc hL, heq2, hexpval]
  field_simp
  ring

/-! ### The constant even trial (for `hea`) -/

noncomputable def constW (L : ℝ) : Cvs.WeilForm.WeilFormOnWindowL2.window L :=
  charW (g := fun _ => (1:ℝ)) continuous_const (fun _ => le_of_eq abs_one)

theorem rep_constW_ae {L : ℝ} :
    Cvs.WeilForm.WindowRepresentative.rep (constW L) =ᵐ[volume] charFn (fun _ => (1:ℝ)) L :=
  rep_charW_ae continuous_const (fun _ => le_of_eq abs_one)

theorem norm_sq_constW {L : ℝ} (hL : 0 ≤ L) :
    ‖(constW L : Lp ℝ 2 (volume : Measure ℝ))‖ ^ 2 = L := by
  rw [constW, norm_sq_charW _ _ hL]; simp

theorem reflW_constW {L : ℝ} : Cvs.WeilForm.WindowReflectionSymmetry.reflW (constW L) = constW L := by
  have hae : Cvs.WeilForm.WindowRepresentative.rep (Cvs.WeilForm.WindowReflectionSymmetry.reflW (constW L))
      =ᵐ[volume] Cvs.WeilForm.WindowRepresentative.rep (constW L) := by
    have hne0 : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 0 := by rw [ae_iff]; simp
    have hneL : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ L := by rw [ae_iff]; simp
    have hcomp : (fun x => charFn (fun _ => (1:ℝ)) L (L - x))
        =ᵐ[volume] fun x => Cvs.WeilForm.WindowRepresentative.rep (constW L) (L - x) :=
      (measurePreserving_sub_left (volume : Measure ℝ) L).quasiMeasurePreserving.ae_eq_comp
        rep_constW_ae.symm
    filter_upwards [Cvs.WeilForm.WindowReflectionSymmetry.rep_reflW_ae (constW L), rep_constW_ae, hcomp, hne0, hneL]
      with x h1 h2 h3 h4 h5
    rw [h1, ← h3, h2]; unfold charFn
    by_cases hx : x ∈ Set.Ioc (0:ℝ) L
    · have hxm := Set.mem_Ioc.mp hx
      have hxlt : x < L := lt_of_le_of_ne hxm.2 h5
      have hx' : L - x ∈ Set.Ioc (0:ℝ) L :=
        Set.mem_Ioc.mpr ⟨by linarith, by linarith [hxm.1]⟩
      rw [Set.indicator_of_mem hx', Set.indicator_of_mem hx]
    · rw [Set.mem_Ioc, not_and_or, not_lt, not_le] at hx
      have hx' : L - x ∉ Set.Ioc (0:ℝ) L := by
        rw [Set.mem_Ioc, not_and_or, not_lt, not_le]
        rcases hx with h | h
        · exact Or.inr (by have : x < 0 := lt_of_le_of_ne h h4; linarith)
        · exact Or.inl (by linarith)
      rw [Set.indicator_of_notMem hx',
        Set.indicator_of_notMem (by rw [Set.mem_Ioc, not_and_or, not_lt, not_le]; exact hx)]
  apply Subtype.ext; apply Lp.ext
  filter_upwards [Cvs.WeilForm.WindowRepresentative.ae_eq_rep (Cvs.WeilForm.WindowReflectionSymmetry.reflW (constW L)),
    Cvs.WeilForm.WindowRepresentative.ae_eq_rep (constW L), hae] with x h1 h2 h3
  show Cvs.WeilForm.WindowRepresentative.fn (Cvs.WeilForm.WindowReflectionSymmetry.reflW (constW L)) x
    = Cvs.WeilForm.WindowRepresentative.fn (constW L) x
  rw [h1, h2]; exact h3

theorem int_const_cos {L : ℝ} (hL : 0 < L) (t : ℝ) (ht : t ≠ 0) :
    (∫ x, Cvs.WeilForm.WindowRepresentative.rep (constW L) x * Real.cos (t * x)) = Real.sin (t * L) / t := by
  have hrw : (∫ x, Cvs.WeilForm.WindowRepresentative.rep (constW L) x * Real.cos (t * x))
      = ∫ x in Set.Ioc (0:ℝ) L, Real.cos (t * x) := by
    rw [← MeasureTheory.integral_indicator measurableSet_Ioc]
    refine integral_congr_ae ?_
    filter_upwards [rep_constW_ae] with x hx
    rw [hx]; unfold charFn
    by_cases hxA : x ∈ Set.Ioc (0:ℝ) L
    · rw [Set.indicator_of_mem hxA, Set.indicator_of_mem hxA, one_mul]
    · rw [Set.indicator_of_notMem hxA, Set.indicator_of_notMem hxA, zero_mul]
  rw [hrw, ← intervalIntegral.integral_of_le hL.le]
  have hmc := intervalIntegral.mul_integral_comp_mul_left (f := Real.cos) (a := 0) (b := L) t
  rw [mul_zero] at hmc
  rw [show (∫ x in (0:ℝ)..L, Real.cos (t*x)) = (t * ∫ x in (0:ℝ)..L, Real.cos (t*x))/t by field_simp,
    hmc, integral_cos, Real.sin_zero, sub_zero]

theorem int_const_sin {L : ℝ} (hL : 0 < L) (t : ℝ) (ht : t ≠ 0) :
    (∫ x, Cvs.WeilForm.WindowRepresentative.rep (constW L) x * Real.sin (t * x)) = (1 - Real.cos (t * L)) / t := by
  have hrw : (∫ x, Cvs.WeilForm.WindowRepresentative.rep (constW L) x * Real.sin (t * x))
      = ∫ x in Set.Ioc (0:ℝ) L, Real.sin (t * x) := by
    rw [← MeasureTheory.integral_indicator measurableSet_Ioc]
    refine integral_congr_ae ?_
    filter_upwards [rep_constW_ae] with x hx
    rw [hx]; unfold charFn
    by_cases hxA : x ∈ Set.Ioc (0:ℝ) L
    · rw [Set.indicator_of_mem hxA, Set.indicator_of_mem hxA, one_mul]
    · rw [Set.indicator_of_notMem hxA, Set.indicator_of_notMem hxA, zero_mul]
  rw [hrw, ← intervalIntegral.integral_of_le hL.le]
  have hmc := intervalIntegral.mul_integral_comp_mul_left (f := Real.sin) (a := 0) (b := L) t
  rw [mul_zero] at hmc
  rw [show (∫ x in (0:ℝ)..L, Real.sin (t*x)) = (t * ∫ x in (0:ℝ)..L, Real.sin (t*x))/t by field_simp,
    hmc, integral_sin, Real.cos_zero]

theorem specDensity_constW {L : ℝ} (hL : 0 < L) (t : ℝ) (ht : t ≠ 0) :
    Cvs.WeilForm.SelfConvolutionCosine.specDensity (Cvs.WeilForm.WindowRepresentative.rep (constW L)) t
      = (1 - Real.cos (t * L)) / (Real.pi * t ^ 2) := by
  rw [specDensity_cos_sin (Cvs.WeilForm.WindowRepresentative.rep (constW L)) t
      (integrable_rep_mul (constW L) (by fun_prop) (fun x => Real.abs_cos_le_one _))
      (integrable_rep_mul (constW L) (by fun_prop) (fun x => Real.abs_sin_le_one _)),
    int_const_cos hL t ht, int_const_sin hL t ht]
  have hs := Real.sin_sq_add_cos_sq (t * L)
  field_simp
  nlinarith [hs, Real.sin_sq_add_cos_sq (t*L)]

theorem selfConv_constW {L : ℝ} (v : ℝ) (hv : 0 ≤ v) :
    Cvs.Zeta.Explicit.Weil.selfConvolution (Cvs.WeilForm.WindowRepresentative.rep (constW L)) v = max 0 (L - v) := by
  have hcong : Cvs.Zeta.Explicit.Weil.selfConvolution (Cvs.WeilForm.WindowRepresentative.rep (constW L)) v
      = Cvs.Zeta.Explicit.Weil.selfConvolution (Set.indicator (Set.Ioc (0:ℝ) L) (fun _ => (1:ℝ))) v :=
    Cvs.WeilForm.WeilFormAeClass.selfConvolution_congr_ae rep_constW_ae v
  rw [hcong]
  by_cases hvL : v ≤ L
  · -- integrand = indicator (Ioc 0 (L-v)) 1
    have hpt : (fun x => Set.indicator (Set.Ioc (0:ℝ) L) (fun _ => (1:ℝ)) x
          * Set.indicator (Set.Ioc (0:ℝ) L) (fun _ => (1:ℝ)) (x + v))
        = Set.indicator (Set.Ioc (0:ℝ) (L - v)) (fun _ => (1:ℝ)) := by
      funext x
      by_cases hx : x ∈ Set.Ioc (0:ℝ) (L - v)
      · have h1 := hx.1; have h2 := hx.2
        rw [Set.indicator_of_mem (show x ∈ Set.Ioc (0:ℝ) L from ⟨h1, by linarith⟩),
          Set.indicator_of_mem (show x + v ∈ Set.Ioc (0:ℝ) L from ⟨by linarith, by linarith⟩),
          Set.indicator_of_mem hx, mul_one]
      · rw [Set.indicator_of_notMem hx]
        rw [Set.mem_Ioc, not_and_or, not_lt, not_le] at hx
        rcases hx with h | h
        · exact mul_eq_zero.mpr (Or.inl (Set.indicator_of_notMem
            (by rw [Set.mem_Ioc, not_and_or, not_lt, not_le]; exact Or.inl h) _))
        · exact mul_eq_zero.mpr (Or.inr (Set.indicator_of_notMem
            (by rw [Set.mem_Ioc, not_and_or, not_lt, not_le]; exact Or.inr (by linarith)) _))
    unfold Cvs.Zeta.Explicit.Weil.selfConvolution
    rw [hpt, MeasureTheory.integral_indicator_const (1:ℝ) measurableSet_Ioc, smul_eq_mul, mul_one,
      Real.volume_real_Ioc_of_le (by linarith), sub_zero, max_eq_right (by linarith)]
  · push Not at hvL
    rw [Cvs.WeilForm.AutocorrSelfConvolution.selfConvolution_indicator_eq_zero L (fun _ => (1:ℝ))
      (by rw [abs_of_nonneg hv]; linarith), max_eq_left (by linarith)]

theorem channel_dsym {L : ℝ} (hL : 0 < L) (c : ℝ) (hc : 0 < c) :
    (∫ t, Cvs.WeilForm.SelfConvolutionCosine.specDensity (Cvs.WeilForm.WindowRepresentative.rep (constW L)) t
        * (1/c - c/(c^2 + (t/2)^2)))
      = (1 - Real.exp (-(2*c*L))) / (2*c^2) := by
  rw [← Cvs.WeilForm.TruncatedEffectiveSymbol.channel_spectral c hc
      (Cvs.WeilForm.WindowRepresentative.memLp_rep (constW L)) (integrable_rep (constW L)),
    ← min_exp_integral c L hc hL]
  refine setIntegral_congr_fun measurableSet_Ioi (fun u hu => ?_)
  rw [Set.mem_Ioi] at hu
  rw [selfConv_constW (0:ℝ) le_rfl, selfConv_constW (u/2) (by linarith)]
  congr 1
  rcases le_total (u/2) L with h | h
  · rw [max_eq_right (by linarith : (0:ℝ) ≤ L - 0), max_eq_right (by linarith : (0:ℝ) ≤ L - u/2),
      min_eq_left h]; ring
  · rw [max_eq_right (by linarith : (0:ℝ) ≤ L - 0), max_eq_left (by linarith : L - u/2 ≤ 0),
      min_eq_right h]; ring

/-- The truncated symbol excess functional `D v = ∫ (truncArchSymbol − A₀) · specDensity (rep v)`. -/
def Dsym {L : ℝ} (v : Cvs.WeilForm.WeilFormOnWindowL2.window L) : ℝ :=
  ∫ t : ℝ, (Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol 100 t - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0)
    * Cvs.WeilForm.SelfConvolutionCosine.specDensity (Cvs.WeilForm.WindowRepresentative.rep v) t

/-- The archimedean rank-one term `2·A·B`, the pole of the form. -/
def poleForm {L : ℝ} (v : Cvs.WeilForm.WeilFormOnWindowL2.window L) : ℝ :=
  2 * (∫ x : ℝ, Cvs.WeilForm.WindowRepresentative.rep v x * Real.exp (x / 2))
    * (∫ x : ℝ, Cvs.WeilForm.WindowRepresentative.rep v x * Real.exp (-(x / 2)))

/-- **The truncated form on the even window, in the `Cvs.WeilForm.PlaneHyperplaneTraceCap` shape.**  At `x = 2` the prime term
drops (its symbol pairs to `selfConv (rep v) (log 2) = 0`), leaving `A₀‖v‖² + D v + pole v`. -/
theorem weilQWTrunc_decomp (v : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) :
    Cvs.WeilForm.SimplicityCriterionWindow.weilQWTrunc 100 2 1 v
      = poleForm v + Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 * ‖v‖ ^ 2 + Dsym v := by
  have hf : MeasureTheory.MemLp (Cvs.WeilForm.WindowRepresentative.rep v) 2 volume :=
    Cvs.WeilForm.WindowRepresentative.memLp_rep v
  have hfint : Integrable (Cvs.WeilForm.WindowRepresentative.rep v) :=
    Cvs.WeilForm.LevyDomainSpectral.integrable_rep (Real.log_pos (by norm_num)).le v
  have hstep : Cvs.WeilForm.SimplicityCriterionWindow.weilQWTrunc 100 2 1 v
      = Cvs.WeilForm.TruncatedFormL2Below.weilFormTrunc 100 2 1 (Cvs.WeilForm.WindowRepresentative.rep v) :=
    Cvs.WeilForm.TruncatedFormL2Below.weilQTrunc_eq (Cvs.WeilForm.WindowRepresentative.ae_eq_rep v)
  have hprime : (∫ t : ℝ, Cvs.WeilForm.EffectiveSymbol.primeSymbol 2 1 t
      * Cvs.WeilForm.SelfConvolutionCosine.specDensity (Cvs.WeilForm.WindowRepresentative.rep v) t) = 0 := by
    rw [← Cvs.WeilForm.EffectiveSymbol.prime_spectral 2 1 hf hfint]
    exact Cvs.WeilForm.PrimeSideVanishesLogTwo.primeSide_eq_zero v
  have hmass : (∫ t : ℝ, Cvs.WeilForm.SelfConvolutionCosine.specDensity (Cvs.WeilForm.WindowRepresentative.rep v) t)
      = ‖v‖ ^ 2 := by
    rw [Cvs.Upstream.PlancherelL1L2SpectralDensity.integral_specDensity_eq_selfConvolution hfint hf,
      Cvs.WeilForm.TruncatedArchCappedBudget.selfConvolution_zero_eq, ← Cvs.WeilForm.OddCapTransfer.sq_norm_eq_integral_rep]
  have hiA := Cvs.WeilForm.TruncatedEffectiveSymbol.integrable_truncArch_mul 100 hf hfint
  have hiP := Cvs.WeilForm.EffectiveSymbolThreeFacts.integrable_prime_mul 2 1 hf hfint
  have hspec := Cvs.WeilForm.Archimedean.LevyIntegrandSpectral.integrable_specDensity hf hfint
  rw [hstep, Cvs.WeilForm.TruncatedEffectiveSymbol.weilFormTrunc_effective 100 2 1 hf hfint]
  have hsplit : (∫ t : ℝ, Cvs.WeilForm.TruncatedEffectiveSymbol.truncEffSymbol 100 2 1 t
        * Cvs.WeilForm.SelfConvolutionCosine.specDensity (Cvs.WeilForm.WindowRepresentative.rep v) t)
      = (∫ t : ℝ, Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol 100 t
          * Cvs.WeilForm.SelfConvolutionCosine.specDensity (Cvs.WeilForm.WindowRepresentative.rep v) t)
        - (∫ t : ℝ, Cvs.WeilForm.EffectiveSymbol.primeSymbol 2 1 t
          * Cvs.WeilForm.SelfConvolutionCosine.specDensity (Cvs.WeilForm.WindowRepresentative.rep v) t) := by
    rw [← integral_sub hiA hiP]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    unfold Cvs.WeilForm.TruncatedEffectiveSymbol.truncEffSymbol; ring
  have hexc : Integrable (fun t : ℝ => (Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol 100 t
      - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0)
      * Cvs.WeilForm.SelfConvolutionCosine.specDensity (Cvs.WeilForm.WindowRepresentative.rep v) t) := by
    have he : (fun t : ℝ => (Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol 100 t
        - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0) * Cvs.WeilForm.SelfConvolutionCosine.specDensity (Cvs.WeilForm.WindowRepresentative.rep v) t)
        = (fun t : ℝ => Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol 100 t
            * Cvs.WeilForm.SelfConvolutionCosine.specDensity (Cvs.WeilForm.WindowRepresentative.rep v) t
          - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0
            * Cvs.WeilForm.SelfConvolutionCosine.specDensity (Cvs.WeilForm.WindowRepresentative.rep v) t) := by
      funext t; ring
    rw [he]; exact hiA.sub (hspec.const_mul _)
  have harch : (∫ t : ℝ, Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol 100 t
        * Cvs.WeilForm.SelfConvolutionCosine.specDensity (Cvs.WeilForm.WindowRepresentative.rep v) t)
      = Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 * ‖v‖ ^ 2 + Dsym v := by
    have hc : (fun t : ℝ => Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol 100 t
          * Cvs.WeilForm.SelfConvolutionCosine.specDensity (Cvs.WeilForm.WindowRepresentative.rep v) t)
        = (fun t : ℝ => Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0
            * Cvs.WeilForm.SelfConvolutionCosine.specDensity (Cvs.WeilForm.WindowRepresentative.rep v) t
          + (Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol 100 t - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0)
            * Cvs.WeilForm.SelfConvolutionCosine.specDensity (Cvs.WeilForm.WindowRepresentative.rep v) t) := by
      funext t; ring
    rw [show (∫ t : ℝ, Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol 100 t
          * Cvs.WeilForm.SelfConvolutionCosine.specDensity (Cvs.WeilForm.WindowRepresentative.rep v) t)
        = ∫ t : ℝ, (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0
            * Cvs.WeilForm.SelfConvolutionCosine.specDensity (Cvs.WeilForm.WindowRepresentative.rep v) t
          + (Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol 100 t - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0)
            * Cvs.WeilForm.SelfConvolutionCosine.specDensity (Cvs.WeilForm.WindowRepresentative.rep v) t) from by rw [hc],
      integral_add (hspec.const_mul _) hexc, integral_const_mul, hmass]
    rfl
  rw [hsplit, hprime, sub_zero, harch]
  unfold poleForm; ring

/-- The multiplier is at most one. -/
theorem mcap_le_one (t : ℝ) : mcap t ≤ 1 := by
  unfold mcap
  refine max_le (by norm_num) ?_
  have : (0:ℝ) ≤ (Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol 100 t - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0)
      / lamstar :=
    div_nonneg (sub_nonneg.mpr (Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol_ge 100 t)) lamstar_pos.le
  linarith

/-- **The cap.**  Capping the truncated symbol at `λ*` only lowers the excess:
`λ* (‖v‖² − M v) ≤ D v`. -/
theorem cap (v : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) :
    lamstar * (‖v‖ ^ 2 - Msym v) ≤ Dsym v := by
  have hf : MeasureTheory.MemLp (Cvs.WeilForm.WindowRepresentative.rep v) 2 volume :=
    Cvs.WeilForm.WindowRepresentative.memLp_rep v
  have hfint : Integrable (Cvs.WeilForm.WindowRepresentative.rep v) :=
    Cvs.WeilForm.LevyDomainSpectral.integrable_rep (Real.log_pos (by norm_num)).le v
  have hspec := Cvs.WeilForm.Archimedean.LevyIntegrandSpectral.integrable_specDensity hf hfint
  set sp := Cvs.WeilForm.SelfConvolutionCosine.specDensity (Cvs.WeilForm.WindowRepresentative.rep v) with hsp
  have hspnn : ∀ t, 0 ≤ sp t := fun t => Cvs.WeilForm.SelfConvolutionCosine.specDensity_nonneg _ t
  have hmass : (∫ t, sp t) = ‖v‖ ^ 2 := by
    rw [hsp, Cvs.Upstream.PlancherelL1L2SpectralDensity.integral_specDensity_eq_selfConvolution hfint hf,
      Cvs.WeilForm.TruncatedArchCappedBudget.selfConvolution_zero_eq, ← Cvs.WeilForm.OddCapTransfer.sq_norm_eq_integral_rep]
  have hexcont : Continuous (fun t : ℝ =>
      Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol 100 t - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0) := by
    have hgen : ∀ N : ℕ, Continuous (fun t : ℝ => Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol N t) := by
      intro N
      simp only [Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol]
      fun_prop (disch := intro x; positivity)
    exact (hgen 100).sub continuous_const
  have hmcapcont : Continuous mcap :=
    continuous_const.max (continuous_const.sub (hexcont.div_const lamstar))
  have hexc : Integrable (fun t => (Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol 100 t
      - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0) * sp t) := by
    have he : (fun t => (Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol 100 t
        - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0) * sp t)
        = (fun t => Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol 100 t * sp t
          - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 * sp t) := by funext t; ring
    rw [he]; exact (Cvs.WeilForm.TruncatedEffectiveSymbol.integrable_truncArch_mul 100 hf hfint).sub (hspec.const_mul _)
  have hmcapsp : Integrable (fun t => mcap t * sp t) := by
    refine Integrable.mono' hspec (hmcapcont.aestronglyMeasurable.mul hspec.aestronglyMeasurable) ?_
    filter_upwards [] with t
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mcap_nonneg t) (hspnn t))]
    exact mul_le_of_le_one_left (hspnn t) (mcap_le_one t)
  have hminsp : Integrable (fun t => min (Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol 100 t
      - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0) lamstar * sp t) := by
    refine Integrable.mono' (hspec.const_mul lamstar)
      (((hexcont.min continuous_const).aestronglyMeasurable).mul hspec.aestronglyMeasurable) ?_
    filter_upwards [] with t
    have hmnn : 0 ≤ min (Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol 100 t
        - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0) lamstar :=
      le_min (sub_nonneg.mpr (Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol_ge 100 t)) lamstar_pos.le
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hmnn (hspnn t))]
    exact mul_le_mul_of_nonneg_right (min_le_right _ _) (hspnn t)
  have hlhs : lamstar * (‖v‖ ^ 2 - Msym v)
      = ∫ t, min (Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol 100 t
        - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0) lamstar * sp t := by
    have e1 : lamstar * (‖v‖ ^ 2 - Msym v)
        = (∫ t, lamstar * sp t) - (∫ t, lamstar * (mcap t * sp t)) := by
      rw [integral_const_mul, integral_const_mul, hmass]; unfold Msym; rw [← hsp]; ring
    rw [e1, ← integral_sub (hspec.const_mul _) (hmcapsp.const_mul _)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only []
    have hmin : min (Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol 100 t
        - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0) lamstar = lamstar * (1 - mcap t) := by
      rw [Cvs.WeilForm.Archimedean.CappedSymbolLowers.min_eq_lam_sub lamstar_pos]; rfl
    rw [hmin]; ring
  rw [hlhs]; unfold Dsym; rw [← hsp]
  exact integral_mono hminsp hexc
    (fun t => mul_le_mul_of_nonneg_right (min_le_left _ _) (hspnn t))

/-- **The pole is nonnegative on the even sector.**  For an even window class the two exponential
moments are proportional by `e^{L/2}`, so `poleForm v = 2 e^{L/2} (∫ rep v · e^{−s/2})² ≥ 0`. -/
theorem poleForm_nonneg {v : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)}
    (heven : Cvs.WeilForm.WindowRepresentative.rep v
      =ᵐ[volume] fun s => Cvs.WeilForm.WindowRepresentative.rep v (Real.log 2 - s)) :
    0 ≤ poleForm v := by
  have hA : (∫ s, Cvs.WeilForm.WindowRepresentative.rep v s * Real.exp (s / 2))
      = Real.exp (Real.log 2 / 2)
        * ∫ s, Cvs.WeilForm.WindowRepresentative.rep v s * Real.exp (-(s / 2)) := by
    have hrefl : (∫ x, Cvs.WeilForm.WindowRepresentative.rep v (Real.log 2 - x)
          * Real.exp ((Real.log 2 - x) / 2))
        = ∫ x, Cvs.WeilForm.WindowRepresentative.rep v x * Real.exp (x / 2) := by
      calc (∫ x, Cvs.WeilForm.WindowRepresentative.rep v (Real.log 2 - x)
              * Real.exp ((Real.log 2 - x) / 2))
          = ∫ x, Cvs.WeilForm.WindowRepresentative.rep v (-(x - Real.log 2))
              * Real.exp ((-(x - Real.log 2)) / 2) := by simp only [neg_sub]
        _ = ∫ x, Cvs.WeilForm.WindowRepresentative.rep v (-x) * Real.exp ((-x) / 2) :=
              integral_sub_right_eq_self
                (fun y => Cvs.WeilForm.WindowRepresentative.rep v (-y) * Real.exp ((-y) / 2)) (Real.log 2)
        _ = ∫ x, Cvs.WeilForm.WindowRepresentative.rep v x * Real.exp (x / 2) :=
              integral_neg_eq_self
                (fun x => Cvs.WeilForm.WindowRepresentative.rep v x * Real.exp (x / 2)) volume
    rw [← hrefl, ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [heven] with x hx
    rw [← hx, show (Real.log 2 - x) / 2 = Real.log 2 / 2 + -(x / 2) from by ring, Real.exp_add]
    ring
  rw [poleForm, hA]
  have hsq : (2 : ℝ) * (Real.exp (Real.log 2 / 2)
        * ∫ s, Cvs.WeilForm.WindowRepresentative.rep v s * Real.exp (-(s / 2)))
      * ∫ s, Cvs.WeilForm.WindowRepresentative.rep v s * Real.exp (-(s / 2))
      = 2 * Real.exp (Real.log 2 / 2)
        * (∫ s, Cvs.WeilForm.WindowRepresentative.rep v s * Real.exp (-(s / 2))) ^ 2 := by ring
  rw [hsq]; positivity

/-- **The 16-channel excess lies below the 100-channel one**: extra channels add nonneg terms. -/
theorem truncArchSymbol_le_N (t : ℝ) :
    Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol 16 t ≤ Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol 100 t := by
  unfold Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol
  have hsub : Finset.range 16 ⊆ Finset.range 100 :=
    fun x hx => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) (by norm_num))
  have hnn : ∀ k ∈ Finset.range 100, k ∉ Finset.range 16 →
      (0:ℝ) ≤ 1 / ((k : ℝ) + 1 / 4)
        - ((k : ℝ) + 1 / 4) / (((k : ℝ) + 1 / 4) ^ 2 + (t / 2) ^ 2) := by
    intro k _ _
    have hk : (0:ℝ) < (k : ℝ) + 1 / 4 := by positivity
    have hd : (0:ℝ) < ((k : ℝ) + 1 / 4) ^ 2 + (t / 2) ^ 2 := by positivity
    have heq : 1 / ((k : ℝ) + 1 / 4)
          - ((k : ℝ) + 1 / 4) / (((k : ℝ) + 1 / 4) ^ 2 + (t / 2) ^ 2)
        = (t / 2) ^ 2 / (((k : ℝ) + 1 / 4) * (((k : ℝ) + 1 / 4) ^ 2 + (t / 2) ^ 2)) := by
      field_simp; ring
    rw [heq]; positivity
  have := Finset.sum_le_sum_of_subset_of_nonneg hsub hnn
  linarith

/-- The `16`-channel capped multiplier, an upper bound on `mcap` used to cut the term count. -/
def mcap16 (t : ℝ) : ℝ :=
  max 0 (1 - (Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol 16 t - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0)
    / lamstar)

/-- **`mcap ≤ mcap16`**: the full multiplier lies below its 16-channel relaxation. -/
theorem Dsym_constW_eq {L : ℝ} (hL : 0 < L) :
    Dsym (constW L)
      = ∑ k ∈ Finset.range 100,
          (1 - Real.exp (-(2 * ((k:ℝ) + 1/4) * L))) / (2 * ((k:ℝ) + 1/4)^2) := by
  unfold Dsym
  have hf := Cvs.WeilForm.WindowRepresentative.memLp_rep (constW L)
  have hfint := integrable_rep (constW L)
  have hsum : (fun t => (Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol 100 t
        - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0)
        * Cvs.WeilForm.SelfConvolutionCosine.specDensity (Cvs.WeilForm.WindowRepresentative.rep (constW L)) t)
      = fun t => ∑ k ∈ Finset.range 100,
          Cvs.WeilForm.SelfConvolutionCosine.specDensity (Cvs.WeilForm.WindowRepresentative.rep (constW L)) t
            * (1 / ((k:ℝ)+1/4) - ((k:ℝ)+1/4) / (((k:ℝ)+1/4)^2 + (t/2)^2)) := by
    funext t
    have hE : Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol 100 t - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0
        = ∑ k ∈ Finset.range 100,
            (1/((k:ℝ)+1/4) - ((k:ℝ)+1/4)/(((k:ℝ)+1/4)^2+(t/2)^2)) := by
      unfold Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol; rw [add_sub_cancel_left]
    rw [hE, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  rw [hsum, integral_finsetSum _ (fun k _ =>
      Cvs.WeilForm.TruncatedEffectiveSymbol.spectral_weight_integrable hf hfint _ (by positivity))]
  exact Finset.sum_congr rfl (fun k _ => channel_dsym hL _ (by positivity))

theorem mcap_le_mcap16 (t : ℝ) : mcap t ≤ mcap16 t := by
  unfold mcap mcap16
  refine max_le_max le_rfl ?_
  have hl : (0:ℝ) < lamstar := lamstar_pos
  have h16 := truncArchSymbol_le_N t
  have : (Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol 16 t - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0) / lamstar
      ≤ (Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol 100 t - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0) / lamstar := by
    gcongr
  linarith

/-- The even density-of-states weight `wdos t = L/2 + sin(tL)/(2t)`, `L = log 2`. -/
noncomputable def wdos (t : ℝ) : ℝ := Real.log 2 / 2 + Real.sin (t * Real.log 2) / (2 * t)

/-- **The symmetrised character has the even density-of-states norm.**  The `L²` mass of the
even parts of `cos(t·)` and `sin(t·)` on `(0,L]` sums to `wdos t = L/2 + sin(tL)/(2t)`. -/
theorem char_sym_sq_integral (t : ℝ) (ht : t ≠ 0) :
    (∫ s in (0:ℝ)..Real.log 2,
      (((Real.cos (t * s) + Real.cos (t * (Real.log 2 - s))) / 2) ^ 2
        + ((Real.sin (t * s) + Real.sin (t * (Real.log 2 - s))) / 2) ^ 2)) = wdos t := by
  have hpt : ∀ s : ℝ,
      (((Real.cos (t * s) + Real.cos (t * (Real.log 2 - s))) / 2) ^ 2
        + ((Real.sin (t * s) + Real.sin (t * (Real.log 2 - s))) / 2) ^ 2)
        = (1 + Real.cos (t * (2 * s - Real.log 2))) / 2 := by
    intro s
    have hcos_sub : Real.cos (t * s - t * (Real.log 2 - s)) =
        Real.cos (t * s) * Real.cos (t * (Real.log 2 - s))
          + Real.sin (t * s) * Real.sin (t * (Real.log 2 - s)) := Real.cos_sub _ _
    have harg : t * s - t * (Real.log 2 - s) = t * (2 * s - Real.log 2) := by ring
    rw [harg] at hcos_sub
    nlinarith [hcos_sub, Real.cos_sq_add_sin_sq (t * s),
      Real.cos_sq_add_sin_sq (t * (Real.log 2 - s))]
  rw [intervalIntegral.integral_congr (fun s _ => hpt s)]
  have hG : ∀ s : ℝ, HasDerivAt (fun s => s / 2 + Real.sin (t * (2 * s - Real.log 2)) / (4 * t))
      ((1 + Real.cos (t * (2 * s - Real.log 2))) / 2) s := by
    intro s
    have harg : HasDerivAt (fun s : ℝ => t * (2 * s - Real.log 2)) (2 * t) s := by
      have : HasDerivAt (fun s : ℝ => 2 * s - Real.log 2) 2 s := by
        simpa using (hasDerivAt_id s).const_mul 2 |>.sub_const (Real.log 2)
      simpa [mul_comm] using this.const_mul t
    have h1 : HasDerivAt (fun s : ℝ => s / 2) (1 / 2) s := by simpa using (hasDerivAt_id s).div_const 2
    refine (h1.add (harg.sin.div_const (4 * t))).congr_deriv ?_
    field_simp; ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hG s)
    (by apply Continuous.intervalIntegrable; fun_prop)]
  have e1 : t * (2 * Real.log 2 - Real.log 2) = t * Real.log 2 := by ring
  have e2 : t * (2 * 0 - Real.log 2) = -(t * Real.log 2) := by ring
  rw [e1, e2, Real.sin_neg, wdos]; field_simp; ring

/-! ### The Bessel bound: the mass functional is capped by the even trace (for `hpair`) -/

theorem norm_ccosW_add (t : ℝ) (ht : t ≠ 0) :
    ‖(ccosW t (Real.log 2) : Lp ℝ 2 (volume : Measure ℝ))‖ ^ 2
      + ‖(csinW t (Real.log 2) : Lp ℝ 2 (volume : Measure ℝ))‖ ^ 2 = wdos t := by
  have hL : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  rw [ccosW, csinW, norm_sq_charW _ _ hL, norm_sq_charW _ _ hL,
    ← intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop)]
  exact char_sym_sq_integral t ht
-- pairwise Bessel from Cvs.Upstream.MassBoundOffSubspace
theorem bessel_pair {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {u v : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : (inner ℝ u v : ℝ) = 0) (w : E) :
    (inner ℝ w u : ℝ) ^ 2 + (inner ℝ w v : ℝ) ^ 2 ≤ ‖w‖ ^ 2 := by
  have horth : Orthonormal ℝ ![u, v] := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp_all [real_inner_self_eq_norm_sq, hu, hv, real_inner_comm u v, huv]
  have hb := Cvs.Upstream.MassBoundOffSubspace.bessel ![u, v] horth w
  simpa [Fin.sum_univ_two] using hb
theorem specDensity_sum_le {u v : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)}
    (hu : Cvs.WeilForm.WindowReflectionSymmetry.reflW u = u) (hv : Cvs.WeilForm.WindowReflectionSymmetry.reflW v = v)
    (hun : ‖(u : Lp ℝ 2 (volume : Measure ℝ))‖ = 1) (hvn : ‖(v : Lp ℝ 2 (volume : Measure ℝ))‖ = 1)
    (huv : (inner ℝ (u : Lp ℝ 2 (volume : Measure ℝ)) (v : Lp ℝ 2 (volume : Measure ℝ)) : ℝ) = 0)
    (t : ℝ) (ht : t ≠ 0) :
    Cvs.WeilForm.SelfConvolutionCosine.specDensity (Cvs.WeilForm.WindowRepresentative.rep u) t
      + Cvs.WeilForm.SelfConvolutionCosine.specDensity (Cvs.WeilForm.WindowRepresentative.rep v) t ≤ wdos t / (2 * Real.pi) := by
  have hpi : (0:ℝ) < 2 * Real.pi := by positivity
  rw [specDensity_inner u t, specDensity_inner v t,
    even_inner_cosW hu, even_inner_sinW hu, even_inner_cosW hv, even_inner_sinW hv,
    ← add_div, div_le_div_iff_of_pos_right hpi, ← norm_ccosW_add t ht]
  have hbc := bessel_pair hun hvn huv (ccosW t (Real.log 2) : Lp ℝ 2 (volume : Measure ℝ))
  have hbs := bessel_pair hun hvn huv (csinW t (Real.log 2) : Lp ℝ 2 (volume : Measure ℝ))
  have c1 : (inner ℝ (u : Lp ℝ 2 (volume : Measure ℝ)) (ccosW t (Real.log 2) : Lp ℝ 2 (volume : Measure ℝ)) : ℝ)
      = inner ℝ (ccosW t (Real.log 2) : Lp ℝ 2 (volume : Measure ℝ)) (u : Lp ℝ 2 (volume : Measure ℝ)) := real_inner_comm _ _
  have c2 : (inner ℝ (v : Lp ℝ 2 (volume : Measure ℝ)) (ccosW t (Real.log 2) : Lp ℝ 2 (volume : Measure ℝ)) : ℝ)
      = inner ℝ (ccosW t (Real.log 2) : Lp ℝ 2 (volume : Measure ℝ)) (v : Lp ℝ 2 (volume : Measure ℝ)) := real_inner_comm _ _
  have c3 : (inner ℝ (u : Lp ℝ 2 (volume : Measure ℝ)) (csinW t (Real.log 2) : Lp ℝ 2 (volume : Measure ℝ)) : ℝ)
      = inner ℝ (csinW t (Real.log 2) : Lp ℝ 2 (volume : Measure ℝ)) (u : Lp ℝ 2 (volume : Measure ℝ)) := real_inner_comm _ _
  have c4 : (inner ℝ (v : Lp ℝ 2 (volume : Measure ℝ)) (csinW t (Real.log 2) : Lp ℝ 2 (volume : Measure ℝ)) : ℝ)
      = inner ℝ (csinW t (Real.log 2) : Lp ℝ 2 (volume : Measure ℝ)) (v : Lp ℝ 2 (volume : Measure ℝ)) := real_inner_comm _ _
  rw [c1, c2, c3, c4]; nlinarith [hbc, hbs]

/-- **Region 1 bound (all `t > 0`)**: `wdos t ≤ L/2 + min(1/(2t), L/2)`, from `sin x ≤ min(x,1)`. -/
theorem wdos_le_region1 {t : ℝ} (ht : 0 < t) :
    wdos t ≤ Real.log 2 / 2 + min (1 / (2 * t)) (Real.log 2 / 2) := by
  unfold wdos
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have htL : 0 < t * Real.log 2 := mul_pos ht hL
  have h2t : 0 < 2 * t := by linarith
  have hs1 : Real.sin (t * Real.log 2) ≤ 1 := Real.sin_le_one _
  have hsx : Real.sin (t * Real.log 2) ≤ t * Real.log 2 := (Real.sin_lt htL).le
  have e1 : Real.sin (t * Real.log 2) / (2 * t) ≤ 1 / (2 * t) := by gcongr
  have e2 : Real.sin (t * Real.log 2) / (2 * t) ≤ Real.log 2 / 2 := by
    have hrw : t * Real.log 2 / (2 * t) = Real.log 2 / 2 := by field_simp
    rw [← hrw]; gcongr
  have hmin : Real.sin (t * Real.log 2) / (2 * t) ≤ min (1 / (2 * t)) (Real.log 2 / 2) :=
    le_min e1 e2
  linarith

/-- **Region 2 bound**: for `π ≤ tL ≤ 2π`, `sin(tL) ≤ 0`, so `wdos t ≤ L/2`. -/
theorem wdos_le_region2 {t : ℝ} (ht : 0 < t) (h1 : Real.pi ≤ t * Real.log 2)
    (h2 : t * Real.log 2 ≤ 2 * Real.pi) : wdos t ≤ Real.log 2 / 2 := by
  unfold wdos
  have h2t : 0 < 2 * t := by linarith
  have hshift : Real.sin (t * Real.log 2) = Real.sin (t * Real.log 2 - 2 * Real.pi) :=
    (Real.sin_sub_two_pi _).symm
  have hnp : Real.sin (t * Real.log 2 - 2 * Real.pi) ≤ 0 :=
    Real.sin_nonpos_of_nonpos_of_neg_pi_le (by linarith) (by linarith)
  have : Real.sin (t * Real.log 2) / (2 * t) ≤ 0 := by
    rw [hshift]; exact div_nonpos_of_nonpos_of_nonneg hnp (by linarith)
  linarith

/-- **The 16-channel truncated symbol is increasing in `|t|`** (each weight decreases in `t²`). -/
theorem truncArchSymbol16_mono {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol 16 s ≤ Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol 16 t := by
  unfold Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol
  have hsum : (∑ k ∈ Finset.range 16, (1 / ((k : ℝ) + 1 / 4)
        - ((k : ℝ) + 1 / 4) / (((k : ℝ) + 1 / 4) ^ 2 + (s / 2) ^ 2)))
      ≤ ∑ k ∈ Finset.range 16, (1 / ((k : ℝ) + 1 / 4)
        - ((k : ℝ) + 1 / 4) / (((k : ℝ) + 1 / 4) ^ 2 + (t / 2) ^ 2)) := by
    refine Finset.sum_le_sum fun k _ => ?_
    have hds : (0:ℝ) < ((k : ℝ) + 1 / 4) ^ 2 + (s / 2) ^ 2 := by positivity
    have hsq : (s / 2) ^ 2 ≤ (t / 2) ^ 2 := by nlinarith
    have hle : ((k : ℝ) + 1 / 4) / (((k : ℝ) + 1 / 4) ^ 2 + (t / 2) ^ 2)
        ≤ ((k : ℝ) + 1 / 4) / (((k : ℝ) + 1 / 4) ^ 2 + (s / 2) ^ 2) :=
      div_le_div_of_nonneg_left (by positivity) hds (by linarith)
    linarith
  linarith

/-- **`mcap16` is antitone on `[0,∞)`**: the excess grows, so the relaxed multiplier decreases. -/
theorem mcap16_antitone {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) : mcap16 t ≤ mcap16 s := by
  unfold mcap16
  refine max_le_max le_rfl ?_
  have h := truncArchSymbol16_mono hs hst
  have hl : (0:ℝ) < lamstar := lamstar_pos
  have : (Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol 16 s - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0) / lamstar
      ≤ (Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol 16 t - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0) / lamstar := by
    gcongr
  linarith

/-- **The region split point lies above `π`**: `4.6·log 2 ≥ π`, so `sin(tL) ≤ 0` for `t ≥ 4.6`. -/
theorem region_split_pi : Real.pi ≤ (46 / 10 : ℝ) * Real.log 2 := by
  have h1 := Real.log_two_gt_d9
  have h2 := Real.pi_lt_d6
  linarith

/-- The excess `truncArchSymbol 16 − A₀`, a rational function of `t` with the transcendental `A₀`
cancelled: `∑_{k<16} (1/(k+¼) − (k+¼)/((k+¼)²+(t/2)²))`. -/
def excess16 (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range 16, (1 / ((k : ℝ) + 1 / 4)
    - ((k : ℝ) + 1 / 4) / (((k : ℝ) + 1 / 4) ^ 2 + (t / 2) ^ 2))

/-- The excess of the 16-channel symbol over `A₀` is `excess16`. -/
theorem excess16_eq (t : ℝ) :
    Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol 16 t - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 = excess16 t := by
  unfold Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol excess16; ring

/-- `mcap16` in terms of `excess16`. -/
theorem mcap16_eq (t : ℝ) : mcap16 t = max 0 (1 - excess16 t / lamstar) := by
  unfold mcap16; rw [excess16_eq]

/-- The 16-channel multiplier is nonnegative. -/
theorem mcap16_nonneg (t : ℝ) : 0 ≤ mcap16 t := le_max_left _ _

/-- At `t = 87/10` the excess already reaches `λ*`, so the 16-channel multiplier vanishes. -/
theorem mcap16_735_zero : mcap16 (87 / 10 : ℝ) = 0 := by
  rw [mcap16_eq]
  apply max_eq_left
  unfold excess16 lamstar
  norm_num [Finset.sum_range_succ]

/-- Beyond `87/10` the 16-channel multiplier is zero (antitone from `mcap16_735_zero`). -/
theorem mcap16_eq_zero_of_ge {t : ℝ} (ht : (87 / 10 : ℝ) ≤ t) : mcap16 t = 0 :=
  le_antisymm (le_trans (mcap16_antitone (by norm_num) ht) (le_of_eq mcap16_735_zero))
    (mcap16_nonneg t)

/-- Beyond `87/10` the full multiplier is zero (it sits below `mcap16`). -/
theorem mcap_eq_zero_of_ge {t : ℝ} (ht : (87 / 10 : ℝ) ≤ t) : mcap t = 0 :=
  le_antisymm (le_trans (mcap_le_mcap16 t) (le_of_eq (mcap16_eq_zero_of_ge ht))) (mcap_nonneg t)

/-- The window majorant: region-1 shape below `46/10`, the flat `L/2` above. -/
noncomputable def wmaj (t : ℝ) : ℝ :=
  if t < 46 / 10 then Real.log 2 / 2 + min (1 / (2 * t)) (Real.log 2 / 2) else Real.log 2 / 2

/-- `wmaj` is nonnegative for `t ≥ 0`. -/
theorem wmaj_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ wmaj t := by
  have hL : (0 : ℝ) ≤ Real.log 2 / 2 := by
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2); linarith
  unfold wmaj
  split
  · have h1 : (0 : ℝ) ≤ 1 / (2 * t) := div_nonneg zero_le_one (by linarith)
    have := le_min h1 hL; linarith
  · exact hL

/-- `47/20·log 2 ≤ 2π` — the region-2 window stays within `[π, 2π]` up to `87/10`. -/
theorem xi16_log2_le_two_pi : (87 / 10 : ℝ) * Real.log 2 ≤ 2 * Real.pi := by
  have h1 : (87 / 10 : ℝ) * Real.log 2 < 87 / 10 * 0.6931471808 :=
    mul_lt_mul_of_pos_left Real.log_two_lt_d9 (by norm_num)
  have h2 := Real.pi_gt_d6
  linarith

/-- `wdos ≤ wmaj` on `(0, 87/10]`: region-1 below `46/10`, region-2 above. -/
theorem wdos_le_wmaj {t : ℝ} (ht : 0 < t) (htX : t ≤ 87 / 10) : wdos t ≤ wmaj t := by
  unfold wmaj
  split
  · exact wdos_le_region1 ht
  · rename_i hge
    push Not at hge
    have hL0 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    refine wdos_le_region2 ht ?_ ?_
    · have := region_split_pi
      have hmono : (46 / 10 : ℝ) * Real.log 2 ≤ t * Real.log 2 :=
        mul_le_mul_of_nonneg_right hge hL0
      linarith
    · have hmono : t * Real.log 2 ≤ (87 / 10 : ℝ) * Real.log 2 :=
        mul_le_mul_of_nonneg_right htX hL0
      have := xi16_log2_le_two_pi
      linarith

/-- `wmaj ≤ log 2` everywhere on `[0,∞)` (the `min` caps at `L/2`). -/
theorem wmaj_le_L {t : ℝ} : wmaj t ≤ Real.log 2 := by
  have hL0 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  unfold wmaj
  split
  · have := min_le_right (1 / (2 * t)) (Real.log 2 / 2); linarith
  · linarith

/-- `wmaj ≤ L/2 + 1/(2t)` for `t > 0` (the `min` is below its first argument). -/
theorem wmaj_le_half_add {t : ℝ} (ht : 0 < t) : wmaj t ≤ Real.log 2 / 2 + 1 / (2 * t) := by
  unfold wmaj
  split
  · have := min_le_left (1 / (2 * t)) (Real.log 2 / 2); linarith
  · have : (0 : ℝ) ≤ 1 / (2 * t) := div_nonneg zero_le_one (by linarith); linarith

/-- Above `46/10` the majorant is exactly `L/2`. -/
theorem wmaj_regionC {t : ℝ} (ht : (46 / 10 : ℝ) ≤ t) : wmaj t = Real.log 2 / 2 := by
  unfold wmaj; rw [ite_eq_right (not_lt.mpr ht)]

/-- `mcap` is continuous. -/
theorem mcap_continuous : Continuous mcap := by
  have hexcont : Continuous (fun t : ℝ =>
      Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol 100 t - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0) := by
    have hgen : ∀ N : ℕ, Continuous (fun t : ℝ => Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol N t) := by
      intro N
      simp only [Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol]
      fun_prop (disch := intro x; positivity)
    exact (hgen 100).sub continuous_const
  exact continuous_const.max (continuous_const.sub (hexcont.div_const lamstar))

/-- `wdos` is continuous on `(0,∞)`. -/
theorem wdos_continuousOn_Ioi : ContinuousOn wdos (Set.Ioi (0 : ℝ)) := by
  unfold wdos
  refine continuousOn_const.add (ContinuousOn.div ?_ ?_ ?_)
  · exact (Real.continuous_sin.comp (continuous_id.mul continuous_const)).continuousOn
  · exact (continuous_const.mul continuous_id).continuousOn
  · intro t ht; rw [Set.mem_Ioi] at ht
    have : (0 : ℝ) < 2 * t := by linarith
    exact this.ne'

/-- The trace integrand `mcap · wdos` is continuous on `(0,∞)`. -/
theorem g_continuousOn_Ioi : ContinuousOn (fun t => mcap t * wdos t) (Set.Ioi (0 : ℝ)) :=
  mcap_continuous.continuousOn.mul wdos_continuousOn_Ioi

/-- `|sin x| ≤ |x|`. -/
theorem abs_sin_le (x : ℝ) : |Real.sin x| ≤ |x| := by
  have h := Real.lipschitzWith_sin.dist_le_mul x 0
  simpa [Real.dist_eq, Real.sin_zero, NNReal.coe_one] using h

/-- `|wdos t| ≤ log 2` for `t > 0` (the `sin` cancels the `1/(2t)` near `0`). -/
theorem abs_wdos_le {t : ℝ} (ht : 0 < t) : |wdos t| ≤ Real.log 2 := by
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h2t : 0 < 2 * t := by linarith
  have hsin : |Real.sin (t * Real.log 2)| ≤ t * Real.log 2 := by
    have := abs_sin_le (t * Real.log 2)
    rwa [abs_of_nonneg (by positivity : (0:ℝ) ≤ t * Real.log 2)] at this
  have hquot : |Real.sin (t * Real.log 2) / (2 * t)| ≤ Real.log 2 / 2 := by
    rw [abs_div, abs_of_pos h2t]
    calc |Real.sin (t * Real.log 2)| / (2 * t) ≤ (t * Real.log 2) / (2 * t) := by gcongr
      _ = Real.log 2 / 2 := by field_simp
  have hb := abs_le.mp hquot
  unfold wdos
  rw [abs_le]
  exact ⟨by linarith [hb.1], by linarith [hb.2]⟩

/-- The integrand is integrable on any `Ioc a b` with `a ≥ 0`. -/
theorem g_integrableOn {a b : ℝ} (ha : 0 ≤ a) :
    IntegrableOn (fun t => mcap t * wdos t) (Set.Ioc a b) volume := by
  have hsub : Set.Ioc a b ⊆ Set.Ioi (0 : ℝ) :=
    Set.Ioc_subset_Ioi_self.trans (Set.Ioi_subset_Ioi ha)
  have hmeas : AEStronglyMeasurable (fun t => mcap t * wdos t)
      (volume.restrict (Set.Ioc a b)) :=
    (g_continuousOn_Ioi.mono hsub).aestronglyMeasurable measurableSet_Ioc
  refine Integrable.mono' (g := fun _ => Real.log 2)
    (integrableOn_const (μ := volume) (s := Set.Ioc a b) (C := Real.log 2)
      (hs := by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)) hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have ht0 : 0 < t := hsub ht
  rw [Real.norm_eq_abs, abs_mul]
  calc |mcap t| * |wdos t| ≤ 1 * Real.log 2 := by
        refine mul_le_mul ?_ (abs_wdos_le ht0) (abs_nonneg _) zero_le_one
        rw [abs_of_nonneg (mcap_nonneg t)]; exact mcap_le_one t
    _ = Real.log 2 := one_mul _

/-- Pointwise: `mcap · wdos ≤ mcap16 · wmaj` on `(0, 87/10]`. -/
theorem pointwise {t : ℝ} (ht : 0 < t) (htX : t ≤ 87 / 10) :
    mcap t * wdos t ≤ mcap16 t * wmaj t := by
  have h1 : mcap t * wdos t ≤ mcap t * wmaj t :=
    mul_le_mul_of_nonneg_left (wdos_le_wmaj ht htX) (mcap_nonneg t)
  have h2 : mcap t * wmaj t ≤ mcap16 t * wmaj t :=
    mul_le_mul_of_nonneg_right (mcap_le_mcap16 t) (wmaj_nonneg ht.le)
  linarith

/-- The general per-interval trace bound against a rational majorant `W` of `wmaj`. -/
theorem step {s s' r W : ℝ} (hs : 0 ≤ s) (hss : s ≤ s') (hs'X : s' ≤ 87 / 10)
    (hcap : mcap16 s ≤ r) (hr : 0 ≤ r) (hW : ∀ t, s < t → t < s' → wmaj t ≤ W)
    (hWnn : 0 ≤ W) :
    ∫ x in s..s', mcap x * wdos x ≤ (s' - s) * (r * W) := by
  have hII : IntervalIntegrable (fun t => mcap t * wdos t) volume s s' :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hss).mpr (g_integrableOn hs)
  have hconst : IntervalIntegrable (fun _ : ℝ => r * W) volume s s' := intervalIntegrable_const
  have hpt : ∀ x ∈ Set.Ioo s s', mcap x * wdos x ≤ r * W := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := hx
    have hx0 : 0 < x := lt_of_le_of_lt hs hx1
    have hxX : x ≤ 87 / 10 := le_trans hx2.le hs'X
    calc mcap x * wdos x ≤ mcap16 x * wmaj x := pointwise hx0 hxX
      _ ≤ r * W := by
          refine mul_le_mul (le_trans (mcap16_antitone hs hx1.le) hcap) (hW x hx1 hx2)
            (wmaj_nonneg hx0.le) hr
  have hmono := intervalIntegral.integral_mono_on_of_le_Ioo hss hII hconst hpt
  rwa [intervalIntegral.integral_const, smul_eq_mul] at hmono

noncomputable def node : ℕ → ℝ := fun i => (i : ℝ) / 40

/-- Half of `log 2` lies below `0.3465735904`. -/
theorem half_log_two_lt : Real.log 2 / 2 < 0.3465735904 := by
  have := Real.log_two_lt_d9; linarith

/-- Region-A interval bound: `wmaj ≤ log 2 ≤ 0.6931471808`. -/
theorem stepA (k : ℕ) (hk : k + 1 ≤ 348) (r : ℝ) (hcap : mcap16 (node k) ≤ r) (hr : 0 ≤ r) :
    (∫ x in node k..node (k+1), mcap x * wdos x) ≤ (1/40) * (r * 0.6931471808) := by
  have hs : (0:ℝ) ≤ node k := by unfold node; positivity
  have hkr : ((k:ℝ) + 1) ≤ 348 := by exact_mod_cast hk
  have hss : node k ≤ node (k+1) := by unfold node; push_cast; linarith
  have hs'X : node (k+1) ≤ 87/10 := by unfold node; push_cast; linarith
  have hW : ∀ t, node k < t → t < node (k+1) → wmaj t ≤ (0.6931471808 : ℝ) :=
    fun t _ _ => wmaj_le_L.trans Real.log_two_lt_d9.le
  have h := step hs hss hs'X hcap hr hW (by norm_num)
  have hd : node (k+1) - node k = 1/40 := by unfold node; push_cast; ring
  rwa [hd] at h

/-- Region-B interval bound: `wmaj ≤ L/2 + 1/(2t) ≤ 0.3465735904 + qk`. -/
theorem stepB (k : ℕ) (hk : 58 ≤ k) (hk2 : k + 1 ≤ 348) (r qk : ℝ)
    (hcap : mcap16 (node k) ≤ r) (hr : 0 ≤ r) (hqk : 0 ≤ qk)
    (hq : 1 / (2 * node k) ≤ qk) :
    (∫ x in node k..node (k+1), mcap x * wdos x) ≤ (1/40) * (r * (0.3465735904 + qk)) := by
  have hnpos : (0:ℝ) < node k := by
    have hkc : (58:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
    unfold node; linarith
  have hs : (0:ℝ) ≤ node k := hnpos.le
  have hkr : ((k:ℝ) + 1) ≤ 348 := by exact_mod_cast hk2
  have hss : node k ≤ node (k+1) := by unfold node; push_cast; linarith
  have hs'X : node (k+1) ≤ 87/10 := by unfold node; push_cast; linarith
  have hW : ∀ t, node k < t → t < node (k+1) → wmaj t ≤ (0.3465735904 : ℝ) + qk := by
    intro t ht1 _
    have ht0 : 0 < t := lt_trans hnpos ht1
    have h1 : wmaj t ≤ Real.log 2 / 2 + 1 / (2 * t) := wmaj_le_half_add ht0
    have h2 : 1 / (2 * t) ≤ 1 / (2 * node k) :=
      one_div_le_one_div_of_le (by linarith) (by linarith)
    have h3 := half_log_two_lt
    linarith
  have hWnn : (0:ℝ) ≤ 0.3465735904 + qk := by linarith
  have h := step hs hss hs'X hcap hr hW hWnn
  have hd : node (k+1) - node k = 1/40 := by unfold node; push_cast; ring
  rwa [hd] at h

/-- Region-C interval bound: above `46/10`, `wmaj = L/2 ≤ 0.3465735904`. -/
theorem stepC (k : ℕ) (hk : 184 ≤ k) (hk2 : k + 1 ≤ 348) (r : ℝ)
    (hcap : mcap16 (node k) ≤ r) (hr : 0 ≤ r) :
    (∫ x in node k..node (k+1), mcap x * wdos x) ≤ (1/40) * (r * 0.3465735904) := by
  have h46 : (46/10:ℝ) ≤ node k := by
    have hkc : (184:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
    unfold node; linarith
  have hs : (0:ℝ) ≤ node k := by unfold node; positivity
  have hkr : ((k:ℝ) + 1) ≤ 348 := by exact_mod_cast hk2
  have hss : node k ≤ node (k+1) := by unfold node; push_cast; linarith
  have hs'X : node (k+1) ≤ 87/10 := by unfold node; push_cast; linarith
  have hW : ∀ t, node k < t → t < node (k+1) → wmaj t ≤ (0.3465735904 : ℝ) := by
    intro t ht1 _
    have : (46/10:ℝ) ≤ t := le_of_lt (lt_of_le_of_lt h46 ht1)
    rw [wmaj_regionC this]; exact half_log_two_lt.le
  have h := step hs hss hs'X hcap hr hW (by norm_num)
  have hd : node (k+1) - node k = 1/40 := by unfold node; push_cast; ring
  rwa [hd] at h

set_option maxRecDepth 8000 in
/-- The flat table of per-interval trace bounds. -/
noncomputable def ccList : ℕ → ℝ := fun k =>
  ([(108304247/6250000000 : ℝ), (108111140527599/6250000000000000 : ℝ), (53768618161373/3125000000000000 : ℝ), (106599213239479/6250000000000000 : ℝ), (105323605818313/6250000000000000 : ℝ), (103744529897053/6250000000000000 : ℝ), (12737770793917/781250000000000 : ℝ), (49919918439981/3125000000000000 : ℝ), (19520432566539/1250000000000000 : ℝ), (95232682516829/6250000000000000 : ℝ), (5798284471639/390625000000000 : ℝ), (45129621595171/3125000000000000 : ℝ), (87725681940271/6250000000000000 : ℝ), (3408009740349/250000000000000 : ℝ), (82706429917303/6250000000000000 : ℝ), (8026319440923/625000000000000 : ℝ), (19471262438401/1562500000000000 : ℝ), (75583259592113/6250000000000000 : ℝ), (366826484589/31250000000000 : ℝ), (35618126015137/3125000000000000 : ℝ), (69198724231463/6250000000000000 : ℝ), (67253796563837/6250000000000000 : ℝ), (65400710897667/6250000000000000 : ℝ), (994341291707/97656250000000 : ℝ), (61962700880899/6250000000000000 : ℝ), (60372144709457/6250000000000000 : ℝ), (29431354209509/3125000000000000 : ℝ), (57430601360937/6250000000000000 : ℝ), (28035962291161/3125000000000000 : ℝ), (27391335413017/3125000000000000 : ℝ), (53558941139181/6250000000000000 : ℝ), (26198472436559/3125000000000000 : ℝ), (4007257139/488281250000 : ℝ), (50243314921523/6250000000000000 : ℝ), (1538895045623/195312500000000 : ℝ), (48293838475523/6250000000000000 : ℝ), (23693828420437/3125000000000000 : ℝ), (46523280645567/6250000000000000 : ℝ), (45698002283427/6250000000000000 : ℝ), (2245471953051/312500000000000 : ℝ), (22077495838209/3125000000000000 : ℝ), (43432494044681/6250000000000000 : ℝ), (42739996689363/6250000000000000 : ℝ), (21037775067009/3125000000000000 : ℝ), (41437313206447/6250000000000000 : ℝ), (8164732268589/1250000000000000 : ℝ), (20116539142027/3125000000000000 : ℝ), (9916011942579/1562500000000000 : ℝ), (39115270150767/6250000000000000 : ℝ), (38585662382937/6250000000000000 : ℝ), (7614763302323/1250000000000000 : ℝ), (1503154644113/250000000000000 : ℝ), (37099728114097/6250000000000000 : ℝ), (7327107222291/1250000000000000 : ℝ), (36185423660923/6250000000000000 : ℝ), (1429940973141/250000000000000 : ℝ), (8831019996133/1562500000000000 : ℝ), (34911549107709/6250000000000000 : ℝ), (34423372745037/6250000000000000 : ℝ), (33745929677199/6250000000000000 : ℝ), (16547144745799/3125000000000000 : ℝ), (129868557574329/25000000000000000 : ℝ), (127451783725393/25000000000000000 : ℝ), (62560773869679/12500000000000000 : ℝ), (15359092142781/3125000000000000 : ℝ), (60350777048353/12500000000000000 : ℝ), (29650795525939/6250000000000000 : ℝ), (58286951864583/12500000000000000 : ℝ), (3581566098397/781250000000000 : ℝ), (7044281144493/1562500000000000 : ℝ), (22173175324221/5000000000000000 : ℝ), (3408728068289/781250000000000 : ℝ), (3354560612397/781250000000000 : ℝ), (2641589267009/625000000000000 : ℝ), (26007324514871/6250000000000000 : ℝ), (51220537037791/12500000000000000 : ℝ), (6306053703151/1562500000000000 : ℝ), (99394287644129/25000000000000000 : ℝ), (4896611739417/1250000000000000 : ℝ), (96508059784073/25000000000000000 : ℝ), (47560524489911/12500000000000000 : ℝ), (2930275428273/781250000000000 : ℝ), (9245018166319/2500000000000000 : ℝ), (45582084290717/12500000000000000 : ℝ), (11238628492217/3125000000000000 : ℝ), (44341659599301/12500000000000000 : ℝ), (87486302810907/25000000000000000 : ℝ), (10789612167879/3125000000000000 : ℝ), (85173538834239/25000000000000000 : ℝ), (10506981773691/3125000000000000 : ℝ), (8296253768853/2500000000000000 : ℝ), (40946374971063/12500000000000000 : ℝ), (40422762409661/12500000000000000 : ℝ), (19955067058467/6250000000000000 : ℝ), (3940809604801/1250000000000000 : ℝ), (4864532717799/1562500000000000 : ℝ), (480428587251/156250000000000 : ℝ), (9490493508081/3125000000000000 : ℝ), (73239478959/24414062500000 : ℝ), (74088728048377/25000000000000000 : ℝ), (142963154739/48828125000000 : ℝ), (36161184588057/12500000000000000 : ℝ), (71463615419121/25000000000000000 : ℝ), (17655103508691/6250000000000000 : ℝ), (17448143894667/6250000000000000 : ℝ), (34489724572107/12500000000000000 : ℝ), (1065321911643/390625000000000 : ℝ), (33697703262119/12500000000000000 : ℝ), (4163989170717/1562500000000000 : ℝ), (2058291530097/781250000000000 : ℝ), (1017485981889/390625000000000 : ℝ), (64385542806211/25000000000000000 : ℝ), (31831864070093/12500000000000000 : ℝ), (6295385381819/2500000000000000 : ℝ), (12450979054647/5000000000000000 : ℝ), (384794849059/156250000000000 : ℝ), (15222473669109/6250000000000000 : ℝ), (60223496331467/25000000000000000 : ℝ), (744585884649/312500000000000 : ℝ), (1473000727023/625000000000000 : ℝ), (29141479947543/12500000000000000 : ℝ), (7206919384803/3125000000000000 : ℝ), (57036891330309/25000000000000000 : ℝ), (3526717212351/1562500000000000 : ℝ), (55826697684351/25000000000000000 : ℝ), (5523393482077/2500000000000000 : ℝ), (13662488678309/6250000000000000 : ℝ), (10814806271151/5000000000000000 : ℝ), (6688221564901/3125000000000000 : ℝ), (661815111459/312500000000000 : ℝ), (10478494400107/5000000000000000 : ℝ), (25923483295767/12500000000000000 : ℝ), (25654260006549/12500000000000000 : ℝ), (6347133346637/3125000000000000 : ℝ), (12563109044821/6250000000000000 : ℝ), (49734771214531/25000000000000000 : ℝ), (49223499312843/25000000000000000 : ℝ), (608984515459/312500000000000 : ℝ), (24110149734331/12500000000000000 : ℝ), (477277515783/250000000000000 : ℝ), (5905183322391/3125000000000000 : ℝ), (23380397421951/12500000000000000 : ℝ), (5785746697359/3125000000000000 : ℝ), (45816970048157/25000000000000000 : ℝ), (45353432265763/25000000000000000 : ℝ), (22447598227223/12500000000000000 : ℝ), (888844810229/500000000000000 : ℝ), (879892248873/500000000000000 : ℝ), (10887991551263/6250000000000000 : ℝ), (1724578791441/1000000000000000 : ℝ), (106704453303/62500000000000 : ℝ), (42253860948077/25000000000000000 : ℝ), (20915290840203/12500000000000000 : ℝ), (41411993298187/25000000000000000 : ℝ), (512475712549/312500000000000 : ℝ), (8117712735771/5000000000000000 : ℝ), (10045816842687/6250000000000000 : ℝ), (39782346251843/25000000000000000 : ℝ), (615399290389/390625000000000 : ℝ), (19496388143391/12500000000000000 : ℝ), (965104826103/625000000000000 : ℝ), (19109821318583/12500000000000000 : ℝ), (7567786274559/5000000000000000 : ℝ), (1170690960051/781250000000000 : ℝ), (18544389282279/12500000000000000 : ℝ), (18359746573343/12500000000000000 : ℝ), (2272097736783/1562500000000000 : ℝ), (35991412227953/25000000000000000 : ℝ), (4454107032417/3125000000000000 : ℝ), (8819341403141/6250000000000000 : ℝ), (2182856959609/1562500000000000 : ℝ), (17288499233697/12500000000000000 : ℝ), (17115891847751/12500000000000000 : ℝ), (33889680653949/25000000000000000 : ℝ), (8387775582651/6250000000000000 : ℝ), (2075956426819/1562500000000000 : ℝ), (16441310973659/12500000000000000 : ℝ), (16276483320123/12500000000000000 : ℝ), (503536198717/390625000000000 : ℝ), (996957879617/781250000000000 : ℝ), (3158173600507/2500000000000000 : ℝ), (3053095389/2441406250000 : ℝ), (30948584519489/25000000000000000 : ℝ), (3829503459761/3125000000000000 : ℝ), (5771425018383/6250000000000000 : ℝ), (2288143826369/2500000000000000 : ℝ), (5669619026203/6250000000000000 : ℝ), (2247638037991/2500000000000000 : ℝ), (5568896076493/6250000000000000 : ℝ), (2759483909313/3125000000000000 : ℝ), (10938620642753/12500000000000000 : ℝ), (10839847169489/12500000000000000 : ℝ), (10741723521707/12500000000000000 : ℝ), (10644033090913/12500000000000000 : ℝ), (5273442090677/6250000000000000 : ℝ), (1045027679303/1250000000000000 : ℝ), (5177051310847/6250000000000000 : ℝ), (4007257139/4882812500000 : ℝ), (5081743573487/6250000000000000 : ℝ), (10068937539343/12500000000000000 : ℝ), (99748211487/125000000000000 : ℝ), (2470311569823/3125000000000000 : ℝ), (9788212931119/12500000000000000 : ℝ), (4847806399967/6250000000000000 : ℝ), (300111068437/390625000000000 : ℝ), (380472819711/500000000000000 : ℝ), (1177592077631/1562500000000000 : ℝ), (4664988831031/6250000000000000 : ℝ), (9239760224311/12500000000000000 : ℝ), (2287494000887/3125000000000000 : ℝ), (453036665201/625000000000000 : ℝ), (8971815517233/12500000000000000 : ℝ), (4441665473717/6250000000000000 : ℝ), (879538789887/1250000000000000 : ℝ), (4353939033647/6250000000000000 : ℝ), (8620693148459/12500000000000000 : ℝ), (8534049750859/12500000000000000 : ℝ), (8447839570247/12500000000000000 : ℝ), (1045244287797/1562500000000000 : ℝ), (8276502251493/12500000000000000 : ℝ), (4095741708799/6250000000000000 : ℝ), (8106897800691/12500000000000000 : ℝ), (2005686350193/3125000000000000 : ℝ), (3969458956797/6250000000000000 : ℝ), (7855631947651/12500000000000000 : ℝ), (3886281295101/6250000000000000 : ℝ), (1922508688497/3125000000000000 : ℝ), (1521566366103/2500000000000000 : ℝ), (7525953819783/12500000000000000 : ℝ), (7444509026039/12500000000000000 : ℝ), (7363497449283/12500000000000000 : ℝ), (1820702696317/3125000000000000 : ℝ), (3601224516997/6250000000000000 : ℝ), (1780630124927/3125000000000000 : ℝ), (7042916878163/12500000000000000 : ℝ), (3481873236803/6250000000000000 : ℝ), (688490098179/1250000000000000 : ℝ), (1361276080543/2500000000000000 : ℝ), (1682073260157/3125000000000000 : ℝ), (3325265295641/6250000000000000 : ℝ), (6573093054677/12500000000000000 : ℝ), (6495980430813/12500000000000000 : ℝ), (641919271969/1250000000000000 : ℝ), (1268567645111/2500000000000000 : ℝ), (3133350169957/6250000000000000 : ℝ), (6190995671261/12500000000000000 : ℝ), (6115615915349/12500000000000000 : ℝ), (3020280536089/6250000000000000 : ℝ), (1491457785437/3125000000000000 : ℝ), (1472829454953/3125000000000000 : ℝ), (363577357179/781250000000000 : ℝ), (5743482522657/12500000000000000 : ℝ), (5670052243191/12500000000000000 : ℝ), (5596838572219/12500000000000000 : ℝ), (1104811623647/2500000000000000 : ℝ), (1090298854549/2500000000000000 : ℝ), (1344813834999/3125000000000000 : ℝ), (1326835329997/3125000000000000 : ℝ), (5235752212721/12500000000000000 : ℝ), (1032897603639/2500000000000000 : ℝ), (5093440432163/12500000000000000 : ℝ), (627839719859/1562500000000000 : ℝ), (2476159999161/6250000000000000 : ℝ), (2441069423133/6250000000000000 : ℝ), (4812282606951/12500000000000000 : ℝ), (4742751280377/12500000000000000 : ℝ), (292096554159/781250000000000 : ℝ), (920911012241/2500000000000000 : ℝ), (113394546609/312500000000000 : ℝ), (139604174383/390625000000000 : ℝ), (4399210208893/12500000000000000 : ℝ), (541412930753/1562500000000000 : ℝ), (532965199487/1562500000000000 : ℝ), (4196464658509/12500000000000000 : ℝ), (4129316025369/12500000000000000 : ℝ), (4062600609217/12500000000000000 : ℝ), (124874796791/390625000000000 : ℝ), (982427824537/3125000000000000 : ℝ), (154550160469/500000000000000 : ℝ), (949503333449/3125000000000000 : ℝ), (3732489264361/12500000000000000 : ℝ), (3667290107667/12500000000000000 : ℝ), (3602307559467/12500000000000000 : ℝ), (3537541619761/12500000000000000 : ℝ), (868275148199/3125000000000000 : ℝ), (136355046973/500000000000000 : ℝ), (836217091087/3125000000000000 : ℝ), (410148183389/1562500000000000 : ℝ), (321771917837/1250000000000000 : ℝ), (1577234749061/6250000000000000 : ℝ), (24151847081/97656250000000 : ℝ), (605745653471/2500000000000000 : ℝ), (2966128412589/12500000000000000 : ℝ), (725963367641/3125000000000000 : ℝ), (2841795137033/12500000000000000 : ℝ), (694988352999/3125000000000000 : ℝ), (27184365997/125000000000000 : ℝ), (2657028091651/12500000000000000 : ℝ), (2595944496343/12500000000000000 : ℝ), (1267484602641/6250000000000000 : ℝ), (1237159413481/6250000000000000 : ℝ), (150867816071/781250000000000 : ℝ), (588416973951/3125000000000000 : ℝ), (1146833671483/6250000000000000 : ℝ), (1116941699311/6250000000000000 : ℝ), (543579015693/3125000000000000 : ℝ), (264370666927/1562500000000000 : ℝ), (1027915608277/6250000000000000 : ℝ), (1996805401939/12500000000000000 : ℝ), (387620900013/2500000000000000 : ℝ), (375924041337/2500000000000000 : ℝ), (1821352521799/12500000000000000 : ℝ), (1763301445407/12500000000000000 : ℝ), (852679336631/6250000000000000 : ℝ), (823870406929/6250000000000000 : ℝ), (1590231258701/12500000000000000 : ℝ), (306609323257/2500000000000000 : ℝ), (368992569529/3125000000000000 : ℝ), (1419110548441/12500000000000000 : ℝ), (68123371363/625000000000000 : ℝ), (1306040914573/12500000000000000 : ℝ), (1249722706133/12500000000000000 : ℝ), (596864705217/6250000000000000 : ℝ), (568922209491/6250000000000000 : ℝ), (135272004503/1562500000000000 : ℝ), (25668106539/312500000000000 : ℝ), (971380791343/12500000000000000 : ℝ), (45812696481/625000000000000 : ℝ), (861343676391/12500000000000000 : ℝ), (100831253957/1562500000000000 : ℝ), (150434599083/2500000000000000 : ℝ), (697804263421/12500000000000000 : ℝ), (643652139921/12500000000000000 : ℝ), (117943324983/2500000000000000 : ℝ), (133972353539/3125000000000000 : ℝ), (482278811891/12500000000000000 : ℝ), (10722120453/312500000000000 : ℝ), (93899782149/3125000000000000 : ℝ), (161265023783/6250000000000000 : ℝ), (26967757503/1250000000000000 : ℝ), (216933406741/12500000000000000 : ℝ), (82202923473/6250000000000000 : ℝ), (22418979129/2500000000000000 : ℝ), (59892248591/12500000000000000 : ℝ), (7906210031/12500000000000000 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)]).getD k 0

set_option maxRecDepth 8000 in
theorem ibound_0 : (∫ x in node 0..node (0+1), mcap x * wdos x) ≤ ccList 0 := by
  refine le_of_le_of_eq (stepA 0 (by norm_num) (1/1) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_1 : (∫ x in node 1..node (1+1), mcap x * wdos x) ≤ ccList 1 := by
  refine le_of_le_of_eq (stepA 1 (by norm_num) (998217/1000000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_2 : (∫ x in node 2..node (2+1), mcap x * wdos x) ≤ ccList 2 := by
  refine le_of_le_of_eq (stepA 2 (by norm_num) (496459/500000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_3 : (∫ x in node 3..node (3+1), mcap x * wdos x) ≤ ccList 3 := by
  refine le_of_le_of_eq (stepA 3 (by norm_num) (984257/1000000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_4 : (∫ x in node 4..node (4+1), mcap x * wdos x) ≤ ccList 4 := by
  refine le_of_le_of_eq (stepA 4 (by norm_num) (972479/1000000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_5 : (∫ x in node 5..node (5+1), mcap x * wdos x) ≤ ccList 5 := by
  refine le_of_le_of_eq (stepA 5 (by norm_num) (957899/1000000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_6 : (∫ x in node 6..node (6+1), mcap x * wdos x) ≤ ccList 6 := by
  refine le_of_le_of_eq (stepA 6 (by norm_num) (117611/125000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_7 : (∫ x in node 7..node (7+1), mcap x * wdos x) ≤ ccList 7 := by
  refine le_of_le_of_eq (stepA 7 (by norm_num) (460923/500000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_8 : (∫ x in node 8..node (8+1), mcap x * wdos x) ≤ ccList 8 := by
  refine le_of_le_of_eq (stepA 8 (by norm_num) (180237/200000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_9 : (∫ x in node 9..node (9+1), mcap x * wdos x) ≤ ccList 9 := by
  refine le_of_le_of_eq (stepA 9 (by norm_num) (879307/1000000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_10 : (∫ x in node 10..node (10+1), mcap x * wdos x) ≤ ccList 10 := by
  refine le_of_le_of_eq (stepA 10 (by norm_num) (53537/62500) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_11 : (∫ x in node 11..node (11+1), mcap x * wdos x) ≤ ccList 11 := by
  refine le_of_le_of_eq (stepA 11 (by norm_num) (416693/500000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_12 : (∫ x in node 12..node (12+1), mcap x * wdos x) ≤ ccList 12 := by
  refine le_of_le_of_eq (stepA 12 (by norm_num) (809993/1000000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_13 : (∫ x in node 13..node (13+1), mcap x * wdos x) ≤ ccList 13 := by
  refine le_of_le_of_eq (stepA 13 (by norm_num) (31467/40000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_14 : (∫ x in node 14..node (14+1), mcap x * wdos x) ≤ ccList 14 := by
  refine le_of_le_of_eq (stepA 14 (by norm_num) (763649/1000000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_15 : (∫ x in node 15..node (15+1), mcap x * wdos x) ≤ ccList 15 := by
  refine le_of_le_of_eq (stepA 15 (by norm_num) (74109/100000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_16 : (∫ x in node 16..node (16+1), mcap x * wdos x) ≤ ccList 16 := by
  refine le_of_le_of_eq (stepA 16 (by norm_num) (179783/250000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_17 : (∫ x in node 17..node (17+1), mcap x * wdos x) ≤ ccList 17 := by
  refine le_of_le_of_eq (stepA 17 (by norm_num) (697879/1000000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_18 : (∫ x in node 18..node (18+1), mcap x * wdos x) ≤ ccList 18 := by
  refine le_of_le_of_eq (stepA 18 (by norm_num) (3387/5000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_19 : (∫ x in node 19..node (19+1), mcap x * wdos x) ≤ ccList 19 := by
  refine le_of_le_of_eq (stepA 19 (by norm_num) (328871/500000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_20 : (∫ x in node 20..node (20+1), mcap x * wdos x) ≤ ccList 20 := by
  refine le_of_le_of_eq (stepA 20 (by norm_num) (638929/1000000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_21 : (∫ x in node 21..node (21+1), mcap x * wdos x) ≤ ccList 21 := by
  refine le_of_le_of_eq (stepA 21 (by norm_num) (620971/1000000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_22 : (∫ x in node 22..node (22+1), mcap x * wdos x) ≤ ccList 22 := by
  refine le_of_le_of_eq (stepA 22 (by norm_num) (603861/1000000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_23 : (∫ x in node 23..node (23+1), mcap x * wdos x) ≤ ccList 23 := by
  refine le_of_le_of_eq (stepA 23 (by norm_num) (9181/15625) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_24 : (∫ x in node 24..node (24+1), mcap x * wdos x) ≤ ccList 24 := by
  refine le_of_le_of_eq (stepA 24 (by norm_num) (572117/1000000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_25 : (∫ x in node 25..node (25+1), mcap x * wdos x) ≤ ccList 25 := by
  refine le_of_le_of_eq (stepA 25 (by norm_num) (557431/1000000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_26 : (∫ x in node 26..node (26+1), mcap x * wdos x) ≤ ccList 26 := by
  refine le_of_le_of_eq (stepA 26 (by norm_num) (271747/500000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_27 : (∫ x in node 27..node (27+1), mcap x * wdos x) ≤ ccList 27 := by
  refine le_of_le_of_eq (stepA 27 (by norm_num) (530271/1000000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_28 : (∫ x in node 28..node (28+1), mcap x * wdos x) ≤ ccList 28 := by
  refine le_of_le_of_eq (stepA 28 (by norm_num) (258863/500000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_29 : (∫ x in node 29..node (29+1), mcap x * wdos x) ≤ ccList 29 := by
  refine le_of_le_of_eq (stepA 29 (by norm_num) (252911/500000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_30 : (∫ x in node 30..node (30+1), mcap x * wdos x) ≤ ccList 30 := by
  refine le_of_le_of_eq (stepA 30 (by norm_num) (494523/1000000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_31 : (∫ x in node 31..node (31+1), mcap x * wdos x) ≤ ccList 31 := by
  refine le_of_le_of_eq (stepA 31 (by norm_num) (241897/500000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_32 : (∫ x in node 32..node (32+1), mcap x * wdos x) ≤ ccList 32 := by
  refine le_of_le_of_eq (stepA 32 (by norm_num) (296/625) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_33 : (∫ x in node 33..node (33+1), mcap x * wdos x) ≤ ccList 33 := by
  refine le_of_le_of_eq (stepA 33 (by norm_num) (463909/1000000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_34 : (∫ x in node 34..node (34+1), mcap x * wdos x) ≤ ccList 34 := by
  refine le_of_le_of_eq (stepA 34 (by norm_num) (14209/31250) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_35 : (∫ x in node 35..node (35+1), mcap x * wdos x) ≤ ccList 35 := by
  refine le_of_le_of_eq (stepA 35 (by norm_num) (445909/1000000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_36 : (∫ x in node 36..node (36+1), mcap x * wdos x) ≤ ccList 36 := by
  refine le_of_le_of_eq (stepA 36 (by norm_num) (218771/500000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_37 : (∫ x in node 37..node (37+1), mcap x * wdos x) ≤ ccList 37 := by
  refine le_of_le_of_eq (stepA 37 (by norm_num) (429561/1000000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_38 : (∫ x in node 38..node (38+1), mcap x * wdos x) ≤ ccList 38 := by
  refine le_of_le_of_eq (stepA 38 (by norm_num) (421941/1000000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_39 : (∫ x in node 39..node (39+1), mcap x * wdos x) ≤ ccList 39 := by
  refine le_of_le_of_eq (stepA 39 (by norm_num) (20733/50000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_40 : (∫ x in node 40..node (40+1), mcap x * wdos x) ≤ ccList 40 := by
  refine le_of_le_of_eq (stepA 40 (by norm_num) (203847/500000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_41 : (∫ x in node 41..node (41+1), mcap x * wdos x) ≤ ccList 41 := by
  refine le_of_le_of_eq (stepA 41 (by norm_num) (401023/1000000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_42 : (∫ x in node 42..node (42+1), mcap x * wdos x) ≤ ccList 42 := by
  refine le_of_le_of_eq (stepA 42 (by norm_num) (394629/1000000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_43 : (∫ x in node 43..node (43+1), mcap x * wdos x) ≤ ccList 43 := by
  refine le_of_le_of_eq (stepA 43 (by norm_num) (194247/500000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_44 : (∫ x in node 44..node (44+1), mcap x * wdos x) ≤ ccList 44 := by
  refine le_of_le_of_eq (stepA 44 (by norm_num) (382601/1000000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_45 : (∫ x in node 45..node (45+1), mcap x * wdos x) ≤ ccList 45 := by
  refine le_of_le_of_eq (stepA 45 (by norm_num) (75387/200000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_46 : (∫ x in node 46..node (46+1), mcap x * wdos x) ≤ ccList 46 := by
  refine le_of_le_of_eq (stepA 46 (by norm_num) (185741/500000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_47 : (∫ x in node 47..node (47+1), mcap x * wdos x) ≤ ccList 47 := by
  refine le_of_le_of_eq (stepA 47 (by norm_num) (91557/250000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_48 : (∫ x in node 48..node (48+1), mcap x * wdos x) ≤ ccList 48 := by
  refine le_of_le_of_eq (stepA 48 (by norm_num) (361161/1000000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_49 : (∫ x in node 49..node (49+1), mcap x * wdos x) ≤ ccList 49 := by
  refine le_of_le_of_eq (stepA 49 (by norm_num) (356271/1000000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_50 : (∫ x in node 50..node (50+1), mcap x * wdos x) ≤ ccList 50 := by
  refine le_of_le_of_eq (stepA 50 (by norm_num) (70309/200000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_51 : (∫ x in node 51..node (51+1), mcap x * wdos x) ≤ ccList 51 := by
  refine le_of_le_of_eq (stepA 51 (by norm_num) (13879/40000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_52 : (∫ x in node 52..node (52+1), mcap x * wdos x) ≤ ccList 52 := by
  refine le_of_le_of_eq (stepA 52 (by norm_num) (342551/1000000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_53 : (∫ x in node 53..node (53+1), mcap x * wdos x) ≤ ccList 53 := by
  refine le_of_le_of_eq (stepA 53 (by norm_num) (67653/200000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_54 : (∫ x in node 54..node (54+1), mcap x * wdos x) ≤ ccList 54 := by
  refine le_of_le_of_eq (stepA 54 (by norm_num) (334109/1000000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_55 : (∫ x in node 55..node (55+1), mcap x * wdos x) ≤ ccList 55 := by
  refine le_of_le_of_eq (stepA 55 (by norm_num) (13203/40000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_56 : (∫ x in node 56..node (56+1), mcap x * wdos x) ≤ ccList 56 := by
  refine le_of_le_of_eq (stepA 56 (by norm_num) (81539/250000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_57 : (∫ x in node 57..node (57+1), mcap x * wdos x) ≤ ccList 57 := by
  refine le_of_le_of_eq (stepA 57 (by norm_num) (322347/1000000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_58 : (∫ x in node 58..node (58+1), mcap x * wdos x) ≤ ccList 58 := by
  refine le_of_le_of_eq (stepB 58 (by norm_num) (by norm_num) (159321/500000) (86207/250000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_59 : (∫ x in node 59..node (59+1), mcap x * wdos x) ≤ ccList 59 := by
  refine le_of_le_of_eq (stepB 59 (by norm_num) (by norm_num) (157517/500000) (42373/125000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_60 : (∫ x in node 60..node (60+1), mcap x * wdos x) ≤ ccList 60 := by
  refine le_of_le_of_eq (stepB 60 (by norm_num) (by norm_num) (155759/500000) (166667/500000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_61 : (∫ x in node 61..node (61+1), mcap x * wdos x) ≤ ccList 61 := by
  refine le_of_le_of_eq (stepB 61 (by norm_num) (by norm_num) (308091/1000000) (327869/1000000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_62 : (∫ x in node 62..node (62+1), mcap x * wdos x) ≤ ccList 62 := by
  refine le_of_le_of_eq (stepB 62 (by norm_num) (by norm_num) (304747/1000000) (322581/1000000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_63 : (∫ x in node 63..node (63+1), mcap x * wdos x) ≤ ccList 63 := by
  refine le_of_le_of_eq (stepB 63 (by norm_num) (by norm_num) (150741/500000) (317461/1000000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_64 : (∫ x in node 64..node (64+1), mcap x * wdos x) ≤ ccList 64 := by
  refine le_of_le_of_eq (stepB 64 (by norm_num) (by norm_num) (74573/250000) (5/16) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_65 : (∫ x in node 65..node (65+1), mcap x * wdos x) ≤ ccList 65 := by
  refine le_of_le_of_eq (stepB 65 (by norm_num) (by norm_num) (147587/500000) (307693/1000000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_66 : (∫ x in node 66..node (66+1), mcap x * wdos x) ≤ ccList 66 := by
  refine le_of_le_of_eq (stepB 66 (by norm_num) (by norm_num) (73031/250000) (303031/1000000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_67 : (∫ x in node 67..node (67+1), mcap x * wdos x) ≤ ccList 67 := by
  refine le_of_le_of_eq (stepB 67 (by norm_num) (by norm_num) (289139/1000000) (74627/250000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_68 : (∫ x in node 68..node (68+1), mcap x * wdos x) ≤ ccList 68 := by
  refine le_of_le_of_eq (stepB 68 (by norm_num) (by norm_num) (35777/125000) (147059/500000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_69 : (∫ x in node 69..node (69+1), mcap x * wdos x) ≤ ccList 69 := by
  refine le_of_le_of_eq (stepB 69 (by norm_num) (by norm_num) (35419/125000) (4529/15625) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_70 : (∫ x in node 70..node (70+1), mcap x * wdos x) ≤ ccList 70 := by
  refine le_of_le_of_eq (stepB 70 (by norm_num) (by norm_num) (56109/200000) (57143/200000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_71 : (∫ x in node 71..node (71+1), mcap x * wdos x) ≤ ccList 71 := by
  refine le_of_le_of_eq (stepB 71 (by norm_num) (by norm_num) (8681/31250) (281691/1000000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_72 : (∫ x in node 72..node (72+1), mcap x * wdos x) ≤ ccList 72 := by
  refine le_of_le_of_eq (stepB 72 (by norm_num) (by norm_num) (275091/1000000) (138889/500000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_73 : (∫ x in node 73..node (73+1), mcap x * wdos x) ≤ ccList 73 := by
  refine le_of_le_of_eq (stepB 73 (by norm_num) (by norm_num) (6811/25000) (273973/1000000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_74 : (∫ x in node 74..node (74+1), mcap x * wdos x) ≤ ccList 74 := by
  refine le_of_le_of_eq (stepB 74 (by norm_num) (by norm_num) (67459/250000) (270271/1000000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_75 : (∫ x in node 75..node (75+1), mcap x * wdos x) ≤ ccList 75 := by
  refine le_of_le_of_eq (stepB 75 (by norm_num) (by norm_num) (133639/500000) (266667/1000000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_76 : (∫ x in node 76..node (76+1), mcap x * wdos x) ≤ ccList 76 := by
  refine le_of_le_of_eq (stepB 76 (by norm_num) (by norm_num) (66191/250000) (131579/500000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_77 : (∫ x in node 77..node (77+1), mcap x * wdos x) ≤ ccList 77 := by
  refine le_of_le_of_eq (stepB 77 (by norm_num) (by norm_num) (262291/1000000) (259741/1000000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_78 : (∫ x in node 78..node (78+1), mcap x * wdos x) ≤ ccList 78 := by
  refine le_of_le_of_eq (stepB 78 (by norm_num) (by norm_num) (12993/50000) (256411/1000000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_79 : (∫ x in node 79..node (79+1), mcap x * wdos x) ≤ ccList 79 := by
  refine le_of_le_of_eq (stepB 79 (by norm_num) (by norm_num) (257467/1000000) (50633/200000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_80 : (∫ x in node 80..node (80+1), mcap x * wdos x) ≤ ccList 80 := by
  refine le_of_le_of_eq (stepB 80 (by norm_num) (by norm_num) (255113/1000000) (1/4) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_81 : (∫ x in node 81..node (81+1), mcap x * wdos x) ≤ ccList 81 := by
  refine le_of_le_of_eq (stepB 81 (by norm_num) (by norm_num) (126397/500000) (123457/500000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_82 : (∫ x in node 82..node (82+1), mcap x * wdos x) ≤ ccList 82 := by
  refine le_of_le_of_eq (stepB 82 (by norm_num) (by norm_num) (25051/100000) (243903/1000000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_83 : (∫ x in node 83..node (83+1), mcap x * wdos x) ≤ ccList 83 := by
  refine le_of_le_of_eq (stepB 83 (by norm_num) (by norm_num) (248261/1000000) (60241/250000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_84 : (∫ x in node 84..node (84+1), mcap x * wdos x) ≤ ccList 84 := by
  refine le_of_le_of_eq (stepB 84 (by norm_num) (by norm_num) (61511/250000) (14881/62500) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_85 : (∫ x in node 85..node (85+1), mcap x * wdos x) ≤ ccList 85 := by
  refine le_of_le_of_eq (stepB 85 (by norm_num) (by norm_num) (121929/500000) (47059/200000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_86 : (∫ x in node 86..node (86+1), mcap x * wdos x) ≤ ccList 86 := by
  refine le_of_le_of_eq (stepB 86 (by norm_num) (by norm_num) (241703/1000000) (232559/1000000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_87 : (∫ x in node 87..node (87+1), mcap x * wdos x) ≤ ccList 87 := by
  refine le_of_le_of_eq (stepB 87 (by norm_num) (by norm_num) (119789/500000) (114943/500000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_88 : (∫ x in node 88..node (88+1), mcap x * wdos x) ≤ ccList 88 := by
  refine le_of_le_of_eq (stepB 88 (by norm_num) (by norm_num) (237481/1000000) (227273/1000000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_89 : (∫ x in node 89..node (89+1), mcap x * wdos x) ≤ ccList 89 := by
  refine le_of_le_of_eq (stepB 89 (by norm_num) (by norm_num) (58853/250000) (2809/12500) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_90 : (∫ x in node 90..node (90+1), mcap x * wdos x) ≤ ccList 90 := by
  refine le_of_le_of_eq (stepB 90 (by norm_num) (by norm_num) (23337/100000) (222223/1000000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_91 : (∫ x in node 91..node (91+1), mcap x * wdos x) ≤ ccList 91 := by
  refine le_of_le_of_eq (stepB 91 (by norm_num) (by norm_num) (115677/500000) (219781/1000000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_92 : (∫ x in node 92..node (92+1), mcap x * wdos x) ≤ ccList 92 := by
  refine le_of_le_of_eq (stepB 92 (by norm_num) (by norm_num) (229363/1000000) (13587/62500) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_93 : (∫ x in node 93..node (93+1), mcap x * wdos x) ≤ ccList 93 := by
  refine le_of_le_of_eq (stepB 93 (by norm_num) (by norm_num) (227397/1000000) (107527/500000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_94 : (∫ x in node 94..node (94+1), mcap x * wdos x) ≤ ccList 94 := by
  refine le_of_le_of_eq (stepB 94 (by norm_num) (by norm_num) (45091/200000) (106383/500000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_95 : (∫ x in node 95..node (95+1), mcap x * wdos x) ≤ ccList 95 := by
  refine le_of_le_of_eq (stepB 95 (by norm_num) (by norm_num) (13971/62500) (210527/1000000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_96 : (∫ x in node 96..node (96+1), mcap x * wdos x) ≤ ccList 96 := by
  refine le_of_le_of_eq (stepB 96 (by norm_num) (by norm_num) (5541/25000) (104167/500000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_97 : (∫ x in node 97..node (97+1), mcap x * wdos x) ≤ ccList 97 := by
  refine le_of_le_of_eq (stepB 97 (by norm_num) (by norm_num) (219767/1000000) (103093/500000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_98 : (∫ x in node 98..node (98+1), mcap x * wdos x) ≤ ccList 98 := by
  refine le_of_le_of_eq (stepB 98 (by norm_num) (by norm_num) (108957/500000) (102041/500000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_99 : (∫ x in node 99..node (99+1), mcap x * wdos x) ≤ ccList 99 := by
  refine le_of_le_of_eq (stepB 99 (by norm_num) (by norm_num) (216083/1000000) (202021/1000000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_100 : (∫ x in node 100..node (100+1), mcap x * wdos x) ≤ ccList 100 := by
  refine le_of_le_of_eq (stepB 100 (by norm_num) (by norm_num) (3348/15625) (1/5) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_101 : (∫ x in node 101..node (101+1), mcap x * wdos x) ≤ ccList 101 := by
  refine le_of_le_of_eq (stepB 101 (by norm_num) (by norm_num) (212481/1000000) (9901/50000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_102 : (∫ x in node 102..node (102+1), mcap x * wdos x) ≤ ccList 102 := by
  refine le_of_le_of_eq (stepB 102 (by norm_num) (by norm_num) (210709/1000000) (196079/1000000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_103 : (∫ x in node 103..node (103+1), mcap x * wdos x) ≤ ccList 103 := by
  refine le_of_le_of_eq (stepB 103 (by norm_num) (by norm_num) (52239/250000) (7767/40000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_104 : (∫ x in node 104..node (104+1), mcap x * wdos x) ≤ ccList 104 := by
  refine le_of_le_of_eq (stepB 104 (by norm_num) (by norm_num) (103611/500000) (48077/250000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_105 : (∫ x in node 105..node (105+1), mcap x * wdos x) ≤ ccList 105 := by
  refine le_of_le_of_eq (stepB 105 (by norm_num) (by norm_num) (102753/500000) (190477/1000000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_106 : (∫ x in node 106..node (106+1), mcap x * wdos x) ≤ ccList 106 := by
  refine le_of_le_of_eq (stepB 106 (by norm_num) (by norm_num) (6369/31250) (4717/25000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_107 : (∫ x in node 107..node (107+1), mcap x * wdos x) ≤ ccList 107 := by
  refine le_of_le_of_eq (stepB 107 (by norm_num) (by norm_num) (202127/1000000) (46729/250000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_108 : (∫ x in node 108..node (108+1), mcap x * wdos x) ≤ ccList 108 := by
  refine le_of_le_of_eq (stepB 108 (by norm_num) (by norm_num) (200463/1000000) (92593/500000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_109 : (∫ x in node 109..node (109+1), mcap x * wdos x) ≤ ccList 109 := by
  refine le_of_le_of_eq (stepB 109 (by norm_num) (by norm_num) (6213/31250) (183487/1000000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_110 : (∫ x in node 110..node (110+1), mcap x * wdos x) ≤ ccList 110 := by
  refine le_of_le_of_eq (stepB 110 (by norm_num) (by norm_num) (3081/15625) (181819/1000000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_111 : (∫ x in node 111..node (111+1), mcap x * wdos x) ≤ ccList 111 := by
  refine le_of_le_of_eq (stepB 111 (by norm_num) (by norm_num) (195569/1000000) (180181/1000000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_112 : (∫ x in node 112..node (112+1), mcap x * wdos x) ≤ ccList 112 := by
  refine le_of_le_of_eq (stepB 112 (by norm_num) (by norm_num) (193969/1000000) (44643/250000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_113 : (∫ x in node 113..node (113+1), mcap x * wdos x) ≤ ccList 113 := by
  refine le_of_le_of_eq (stepB 113 (by norm_num) (by norm_num) (38477/200000) (5531/31250) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_114 : (∫ x in node 114..node (114+1), mcap x * wdos x) ≤ ccList 114 := by
  refine le_of_le_of_eq (stepB 114 (by norm_num) (by norm_num) (38163/200000) (175439/1000000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_115 : (∫ x in node 115..node (115+1), mcap x * wdos x) ≤ ccList 115 := by
  refine le_of_le_of_eq (stepB 115 (by norm_num) (by norm_num) (9463/50000) (86957/500000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_116 : (∫ x in node 116..node (116+1), mcap x * wdos x) ≤ ccList 116 := by
  refine le_of_le_of_eq (stepB 116 (by norm_num) (by norm_num) (187719/1000000) (86207/500000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_117 : (∫ x in node 117..node (117+1), mcap x * wdos x) ≤ ccList 117 := by
  refine le_of_le_of_eq (stepB 117 (by norm_num) (by norm_num) (186193/1000000) (170941/1000000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_118 : (∫ x in node 118..node (118+1), mcap x * wdos x) ≤ ccList 118 := by
  refine le_of_le_of_eq (stepB 118 (by norm_num) (by norm_num) (4617/25000) (42373/250000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_119 : (∫ x in node 119..node (119+1), mcap x * wdos x) ≤ ccList 119 := by
  refine le_of_le_of_eq (stepB 119 (by norm_num) (by norm_num) (9159/50000) (42017/250000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_120 : (∫ x in node 120..node (120+1), mcap x * wdos x) ≤ ccList 120 := by
  refine le_of_le_of_eq (stepB 120 (by norm_num) (by norm_num) (90847/500000) (166667/1000000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_121 : (∫ x in node 121..node (121+1), mcap x * wdos x) ≤ ccList 121 := by
  refine le_of_le_of_eq (stepB 121 (by norm_num) (by norm_num) (180221/1000000) (16529/100000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_122 : (∫ x in node 122..node (122+1), mcap x * wdos x) ≤ ccList 122 := by
  refine le_of_le_of_eq (stepB 122 (by norm_num) (by norm_num) (178761/1000000) (32787/200000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_123 : (∫ x in node 123..node (123+1), mcap x * wdos x) ≤ ccList 123 := by
  refine le_of_le_of_eq (stepB 123 (by norm_num) (by norm_num) (88657/500000) (81301/500000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_124 : (∫ x in node 124..node (124+1), mcap x * wdos x) ≤ ccList 124 := by
  refine le_of_le_of_eq (stepB 124 (by norm_num) (by norm_num) (175879/1000000) (161291/1000000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_125 : (∫ x in node 125..node (125+1), mcap x * wdos x) ≤ ccList 125 := by
  refine le_of_le_of_eq (stepB 125 (by norm_num) (by norm_num) (34891/200000) (4/25) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_126 : (∫ x in node 126..node (126+1), mcap x * wdos x) ≤ ccList 126 := by
  refine le_of_le_of_eq (stepB 126 (by norm_num) (by norm_num) (43261/250000) (158731/1000000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_127 : (∫ x in node 127..node (127+1), mcap x * wdos x) ≤ ccList 127 := by
  refine le_of_le_of_eq (stepB 127 (by norm_num) (by norm_num) (34329/200000) (157481/1000000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_128 : (∫ x in node 128..node (128+1), mcap x * wdos x) ≤ ccList 128 := by
  refine le_of_le_of_eq (stepB 128 (by norm_num) (by norm_num) (170257/1000000) (5/32) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_129 : (∫ x in node 129..node (129+1), mcap x * wdos x) ≤ ccList 129 := by
  refine le_of_le_of_eq (stepB 129 (by norm_num) (by norm_num) (2111/12500) (155039/1000000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_130 : (∫ x in node 130..node (130+1), mcap x * wdos x) ≤ ccList 130 := by
  refine le_of_le_of_eq (stepB 130 (by norm_num) (by norm_num) (33503/200000) (153847/1000000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_131 : (∫ x in node 131..node (131+1), mcap x * wdos x) ≤ ccList 131 := by
  refine le_of_le_of_eq (stepB 131 (by norm_num) (by norm_num) (166161/1000000) (4771/31250) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_132 : (∫ x in node 132..node (132+1), mcap x * wdos x) ≤ ccList 132 := by
  refine le_of_le_of_eq (stepB 132 (by norm_num) (by norm_num) (164817/1000000) (37879/250000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_133 : (∫ x in node 133..node (133+1), mcap x * wdos x) ≤ ccList 133 := by
  refine le_of_le_of_eq (stepB 133 (by norm_num) (by norm_num) (40871/250000) (18797/125000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_134 : (∫ x in node 134..node (134+1), mcap x * wdos x) ≤ ccList 134 := by
  refine le_of_le_of_eq (stepB 134 (by norm_num) (by norm_num) (162161/1000000) (74627/500000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_135 : (∫ x in node 135..node (135+1), mcap x * wdos x) ≤ ccList 135 := by
  refine le_of_le_of_eq (stepB 135 (by norm_num) (by norm_num) (160849/1000000) (148149/1000000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_136 : (∫ x in node 136..node (136+1), mcap x * wdos x) ≤ ccList 136 := by
  refine le_of_le_of_eq (stepB 136 (by norm_num) (by norm_num) (159547/1000000) (147059/1000000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_137 : (∫ x in node 137..node (137+1), mcap x * wdos x) ≤ ccList 137 := by
  refine le_of_le_of_eq (stepB 137 (by norm_num) (by norm_num) (31651/200000) (72993/500000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_138 : (∫ x in node 138..node (138+1), mcap x * wdos x) ≤ ccList 138 := by
  refine le_of_le_of_eq (stepB 138 (by norm_num) (by norm_num) (156973/1000000) (4529/31250) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_139 : (∫ x in node 139..node (139+1), mcap x * wdos x) ≤ ccList 139 := by
  refine le_of_le_of_eq (stepB 139 (by norm_num) (by norm_num) (1557/10000) (28777/200000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_140 : (∫ x in node 140..node (140+1), mcap x * wdos x) ≤ ccList 140 := by
  refine le_of_le_of_eq (stepB 140 (by norm_num) (by norm_num) (154437/1000000) (71429/500000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_141 : (∫ x in node 141..node (141+1), mcap x * wdos x) ≤ ccList 141 := by
  refine le_of_le_of_eq (stepB 141 (by norm_num) (by norm_num) (153183/1000000) (35461/250000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_142 : (∫ x in node 142..node (142+1), mcap x * wdos x) ≤ ccList 142 := by
  refine le_of_le_of_eq (stepB 142 (by norm_num) (by norm_num) (75969/500000) (70423/500000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_143 : (∫ x in node 143..node (143+1), mcap x * wdos x) ≤ ccList 143 := by
  refine le_of_le_of_eq (stepB 143 (by norm_num) (by norm_num) (150703/1000000) (139861/1000000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_144 : (∫ x in node 144..node (144+1), mcap x * wdos x) ≤ ccList 144 := by
  refine le_of_le_of_eq (stepB 144 (by norm_num) (by norm_num) (149477/1000000) (138889/1000000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_145 : (∫ x in node 145..node (145+1), mcap x * wdos x) ≤ ccList 145 := by
  refine le_of_le_of_eq (stepB 145 (by norm_num) (by norm_num) (148259/1000000) (34483/250000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_146 : (∫ x in node 146..node (146+1), mcap x * wdos x) ≤ ccList 146 := by
  refine le_of_le_of_eq (stepB 146 (by norm_num) (by norm_num) (2941/20000) (136987/1000000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_147 : (∫ x in node 147..node (147+1), mcap x * wdos x) ≤ ccList 147 := by
  refine le_of_le_of_eq (stepB 147 (by norm_num) (by norm_num) (2917/20000) (27211/200000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_148 : (∫ x in node 148..node (148+1), mcap x * wdos x) ≤ ccList 148 := by
  refine le_of_le_of_eq (stepB 148 (by norm_num) (by norm_num) (72329/500000) (4223/31250) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_149 : (∫ x in node 149..node (149+1), mcap x * wdos x) ≤ ccList 149 := by
  refine le_of_le_of_eq (stepB 149 (by norm_num) (by norm_num) (5739/40000) (134229/1000000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_150 : (∫ x in node 150..node (150+1), mcap x * wdos x) ≤ ccList 150 := by
  refine le_of_le_of_eq (stepB 150 (by norm_num) (by norm_num) (1423/10000) (66667/500000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_151 : (∫ x in node 151..node (151+1), mcap x * wdos x) ≤ ccList 151 := by
  refine le_of_le_of_eq (stepB 151 (by norm_num) (by norm_num) (141133/1000000) (132451/1000000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_152 : (∫ x in node 152..node (152+1), mcap x * wdos x) ≤ ccList 152 := by
  refine le_of_le_of_eq (stepB 152 (by norm_num) (by norm_num) (69987/500000) (131579/1000000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_153 : (∫ x in node 153..node (153+1), mcap x * wdos x) ≤ ccList 153 := by
  refine le_of_le_of_eq (stepB 153 (by norm_num) (by norm_num) (138823/1000000) (130719/1000000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_154 : (∫ x in node 154..node (154+1), mcap x * wdos x) ≤ ccList 154 := by
  refine le_of_le_of_eq (stepB 154 (by norm_num) (by norm_num) (1721/12500) (129871/1000000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_155 : (∫ x in node 155..node (155+1), mcap x * wdos x) ≤ ccList 155 := by
  refine le_of_le_of_eq (stepB 155 (by norm_num) (by norm_num) (27309/200000) (129033/1000000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_156 : (∫ x in node 156..node (156+1), mcap x * wdos x) ≤ ccList 156 := by
  refine le_of_le_of_eq (stepB 156 (by norm_num) (by norm_num) (135417/1000000) (64103/500000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_157 : (∫ x in node 157..node (157+1), mcap x * wdos x) ≤ ccList 157 := by
  refine le_of_le_of_eq (stepB 157 (by norm_num) (by norm_num) (134297/1000000) (127389/1000000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_158 : (∫ x in node 158..node (158+1), mcap x * wdos x) ≤ ccList 158 := by
  refine le_of_le_of_eq (stepB 158 (by norm_num) (by norm_num) (2081/15625) (126583/1000000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_159 : (∫ x in node 159..node (159+1), mcap x * wdos x) ≤ ccList 159 := by
  refine le_of_le_of_eq (stepB 159 (by norm_num) (by norm_num) (66039/500000) (125787/1000000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_160 : (∫ x in node 160..node (160+1), mcap x * wdos x) ≤ ccList 160 := by
  refine le_of_le_of_eq (stepB 160 (by norm_num) (by norm_num) (6549/50000) (1/8) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_161 : (∫ x in node 161..node (161+1), mcap x * wdos x) ≤ ccList 161 := by
  refine le_of_le_of_eq (stepB 161 (by norm_num) (by norm_num) (129889/1000000) (1941/15625) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_162 : (∫ x in node 162..node (162+1), mcap x * wdos x) ≤ ccList 162 := by
  refine le_of_le_of_eq (stepB 162 (by norm_num) (by norm_num) (25761/200000) (123457/1000000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_163 : (∫ x in node 163..node (163+1), mcap x * wdos x) ≤ ccList 163 := by
  refine le_of_le_of_eq (stepB 163 (by norm_num) (by norm_num) (7983/62500) (1227/10000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_164 : (∫ x in node 164..node (164+1), mcap x * wdos x) ≤ ccList 164 := by
  refine le_of_le_of_eq (stepB 164 (by norm_num) (by norm_num) (126657/1000000) (3811/31250) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_165 : (∫ x in node 165..node (165+1), mcap x * wdos x) ≤ ccList 165 := by
  refine le_of_le_of_eq (stepB 165 (by norm_num) (by norm_num) (62797/500000) (121213/1000000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_166 : (∫ x in node 166..node (166+1), mcap x * wdos x) ≤ ccList 166 := by
  refine le_of_le_of_eq (stepB 166 (by norm_num) (by norm_num) (124537/1000000) (60241/500000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_167 : (∫ x in node 167..node (167+1), mcap x * wdos x) ≤ ccList 167 := by
  refine le_of_le_of_eq (stepB 167 (by norm_num) (by norm_num) (123487/1000000) (119761/1000000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_168 : (∫ x in node 168..node (168+1), mcap x * wdos x) ≤ ccList 168 := by
  refine le_of_le_of_eq (stepB 168 (by norm_num) (by norm_num) (30611/250000) (14881/125000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_169 : (∫ x in node 169..node (169+1), mcap x * wdos x) ≤ ccList 169 := by
  refine le_of_le_of_eq (stepB 169 (by norm_num) (by norm_num) (60703/500000) (14793/125000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_170 : (∫ x in node 170..node (170+1), mcap x * wdos x) ≤ ccList 170 := by
  refine le_of_le_of_eq (stepB 170 (by norm_num) (by norm_num) (15047/125000) (7353/62500) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_171 : (∫ x in node 171..node (171+1), mcap x * wdos x) ≤ ccList 171 := by
  refine le_of_le_of_eq (stepB 171 (by norm_num) (by norm_num) (119351/1000000) (731/6250) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_172 : (∫ x in node 172..node (172+1), mcap x * wdos x) ≤ ccList 172 := by
  refine le_of_le_of_eq (stepB 172 (by norm_num) (by norm_num) (118333/1000000) (2907/25000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_173 : (∫ x in node 173..node (173+1), mcap x * wdos x) ≤ ccList 173 := by
  refine le_of_le_of_eq (stepB 173 (by norm_num) (by norm_num) (117321/1000000) (115607/1000000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_174 : (∫ x in node 174..node (174+1), mcap x * wdos x) ≤ ccList 174 := by
  refine le_of_le_of_eq (stepB 174 (by norm_num) (by norm_num) (29079/250000) (114943/1000000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_175 : (∫ x in node 175..node (175+1), mcap x * wdos x) ≤ ccList 175 := by
  refine le_of_le_of_eq (stepB 175 (by norm_num) (by norm_num) (28829/250000) (57143/500000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_176 : (∫ x in node 176..node (176+1), mcap x * wdos x) ≤ ccList 176 := by
  refine le_of_le_of_eq (stepB 176 (by norm_num) (by norm_num) (57161/500000) (113637/1000000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_177 : (∫ x in node 177..node (177+1), mcap x * wdos x) ≤ ccList 177 := by
  refine le_of_le_of_eq (stepB 177 (by norm_num) (by norm_num) (56667/500000) (22599/200000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_178 : (∫ x in node 178..node (178+1), mcap x * wdos x) ≤ ccList 178 := by
  refine le_of_le_of_eq (stepB 178 (by norm_num) (by norm_num) (3511/31250) (2809/25000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_179 : (∫ x in node 179..node (179+1), mcap x * wdos x) ≤ ccList 179 := by
  refine le_of_le_of_eq (stepB 179 (by norm_num) (by norm_num) (6961/62500) (27933/250000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_180 : (∫ x in node 180..node (180+1), mcap x * wdos x) ≤ ccList 180 := by
  refine le_of_le_of_eq (stepB 180 (by norm_num) (by norm_num) (22081/200000) (13889/125000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_181 : (∫ x in node 181..node (181+1), mcap x * wdos x) ≤ ccList 181 := by
  refine le_of_le_of_eq (stepB 181 (by norm_num) (by norm_num) (342/3125) (55249/500000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_182 : (∫ x in node 182..node (182+1), mcap x * wdos x) ≤ ccList 182 := by
  refine le_of_le_of_eq (stepB 182 (by norm_num) (by norm_num) (108481/1000000) (109891/1000000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_183 : (∫ x in node 183..node (183+1), mcap x * wdos x) ≤ ccList 183 := by
  refine le_of_le_of_eq (stepB 183 (by norm_num) (by norm_num) (107527/1000000) (10929/100000) ?_ (by norm_num) (by norm_num) (by unfold node; norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_184 : (∫ x in node 184..node (184+1), mcap x * wdos x) ≤ ccList 184 := by
  refine le_of_le_of_eq (stepC 184 (by norm_num) (by norm_num) (53289/500000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_185 : (∫ x in node 185..node (185+1), mcap x * wdos x) ≤ ccList 185 := by
  refine le_of_le_of_eq (stepC 185 (by norm_num) (by norm_num) (21127/200000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_186 : (∫ x in node 186..node (186+1), mcap x * wdos x) ≤ ccList 186 := by
  refine le_of_le_of_eq (stepC 186 (by norm_num) (by norm_num) (52349/500000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_187 : (∫ x in node 187..node (187+1), mcap x * wdos x) ≤ ccList 187 := by
  refine le_of_le_of_eq (stepC 187 (by norm_num) (by norm_num) (20753/200000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_188 : (∫ x in node 188..node (188+1), mcap x * wdos x) ≤ ccList 188 := by
  refine le_of_le_of_eq (stepC 188 (by norm_num) (by norm_num) (51419/500000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_189 : (∫ x in node 189..node (189+1), mcap x * wdos x) ≤ ccList 189 := by
  refine le_of_le_of_eq (stepC 189 (by norm_num) (by norm_num) (25479/250000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_190 : (∫ x in node 190..node (190+1), mcap x * wdos x) ≤ ccList 190 := by
  refine le_of_le_of_eq (stepC 190 (by norm_num) (by norm_num) (100999/1000000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_191 : (∫ x in node 191..node (191+1), mcap x * wdos x) ≤ ccList 191 := by
  refine le_of_le_of_eq (stepC 191 (by norm_num) (by norm_num) (100087/1000000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_192 : (∫ x in node 192..node (192+1), mcap x * wdos x) ≤ ccList 192 := by
  refine le_of_le_of_eq (stepC 192 (by norm_num) (by norm_num) (99181/1000000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_193 : (∫ x in node 193..node (193+1), mcap x * wdos x) ≤ ccList 193 := by
  refine le_of_le_of_eq (stepC 193 (by norm_num) (by norm_num) (98279/1000000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_194 : (∫ x in node 194..node (194+1), mcap x * wdos x) ≤ ccList 194 := by
  refine le_of_le_of_eq (stepC 194 (by norm_num) (by norm_num) (48691/500000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_195 : (∫ x in node 195..node (195+1), mcap x * wdos x) ≤ ccList 195 := by
  refine le_of_le_of_eq (stepC 195 (by norm_num) (by norm_num) (9649/100000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_196 : (∫ x in node 196..node (196+1), mcap x * wdos x) ≤ ccList 196 := by
  refine le_of_le_of_eq (stepC 196 (by norm_num) (by norm_num) (47801/500000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_197 : (∫ x in node 197..node (197+1), mcap x * wdos x) ≤ ccList 197 := by
  refine le_of_le_of_eq (stepC 197 (by norm_num) (by norm_num) (296/3125) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_198 : (∫ x in node 198..node (198+1), mcap x * wdos x) ≤ ccList 198 := by
  refine le_of_le_of_eq (stepC 198 (by norm_num) (by norm_num) (46921/500000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_199 : (∫ x in node 199..node (199+1), mcap x * wdos x) ≤ ccList 199 := by
  refine le_of_le_of_eq (stepC 199 (by norm_num) (by norm_num) (92969/1000000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_200 : (∫ x in node 200..node (200+1), mcap x * wdos x) ≤ ccList 200 := by
  refine le_of_le_of_eq (stepC 200 (by norm_num) (by norm_num) (921/10000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_201 : (∫ x in node 201..node (201+1), mcap x * wdos x) ≤ ccList 201 := by
  refine le_of_le_of_eq (stepC 201 (by norm_num) (by norm_num) (22809/250000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_202 : (∫ x in node 202..node (202+1), mcap x * wdos x) ≤ ccList 202 := by
  refine le_of_le_of_eq (stepC 202 (by norm_num) (by norm_num) (90377/1000000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_203 : (∫ x in node 203..node (203+1), mcap x * wdos x) ≤ ccList 203 := by
  refine le_of_le_of_eq (stepC 203 (by norm_num) (by norm_num) (44761/500000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_204 : (∫ x in node 204..node (204+1), mcap x * wdos x) ≤ ccList 204 := by
  refine le_of_le_of_eq (stepC 204 (by norm_num) (by norm_num) (2771/31250) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_205 : (∫ x in node 205..node (205+1), mcap x * wdos x) ≤ ccList 205 := by
  refine le_of_le_of_eq (stepC 205 (by norm_num) (by norm_num) (3513/40000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_206 : (∫ x in node 206..node (206+1), mcap x * wdos x) ≤ ccList 206 := by
  refine le_of_le_of_eq (stepC 206 (by norm_num) (by norm_num) (10873/125000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_207 : (∫ x in node 207..node (207+1), mcap x * wdos x) ≤ ccList 207 := by
  refine le_of_le_of_eq (stepC 207 (by norm_num) (by norm_num) (43073/500000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_208 : (∫ x in node 208..node (208+1), mcap x * wdos x) ≤ ccList 208 := by
  refine le_of_le_of_eq (stepC 208 (by norm_num) (by norm_num) (85313/1000000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_209 : (∫ x in node 209..node (209+1), mcap x * wdos x) ≤ ccList 209 := by
  refine le_of_le_of_eq (stepC 209 (by norm_num) (by norm_num) (21121/250000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_210 : (∫ x in node 210..node (210+1), mcap x * wdos x) ≤ ccList 210 := by
  refine le_of_le_of_eq (stepC 210 (by norm_num) (by norm_num) (4183/50000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_211 : (∫ x in node 211..node (211+1), mcap x * wdos x) ≤ ccList 211 := by
  refine le_of_le_of_eq (stepC 211 (by norm_num) (by norm_num) (82839/1000000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_212 : (∫ x in node 212..node (212+1), mcap x * wdos x) ≤ ccList 212 := by
  refine le_of_le_of_eq (stepC 212 (by norm_num) (by norm_num) (41011/500000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_213 : (∫ x in node 213..node (213+1), mcap x * wdos x) ≤ ccList 213 := by
  refine le_of_le_of_eq (stepC 213 (by norm_num) (by norm_num) (8121/100000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_214 : (∫ x in node 214..node (214+1), mcap x * wdos x) ≤ ccList 214 := by
  refine le_of_le_of_eq (stepC 214 (by norm_num) (by norm_num) (40201/500000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_215 : (∫ x in node 215..node (215+1), mcap x * wdos x) ≤ ccList 215 := by
  refine le_of_le_of_eq (stepC 215 (by norm_num) (by norm_num) (79597/1000000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_216 : (∫ x in node 216..node (216+1), mcap x * wdos x) ≤ ccList 216 := by
  refine le_of_le_of_eq (stepC 216 (by norm_num) (by norm_num) (78797/1000000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_217 : (∫ x in node 217..node (217+1), mcap x * wdos x) ≤ ccList 217 := by
  refine le_of_le_of_eq (stepC 217 (by norm_num) (by norm_num) (78001/1000000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_218 : (∫ x in node 218..node (218+1), mcap x * wdos x) ≤ ccList 218 := by
  refine le_of_le_of_eq (stepC 218 (by norm_num) (by norm_num) (9651/125000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_219 : (∫ x in node 219..node (219+1), mcap x * wdos x) ≤ ccList 219 := by
  refine le_of_le_of_eq (stepC 219 (by norm_num) (by norm_num) (76419/1000000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_220 : (∫ x in node 220..node (220+1), mcap x * wdos x) ≤ ccList 220 := by
  refine le_of_le_of_eq (stepC 220 (by norm_num) (by norm_num) (37817/500000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_221 : (∫ x in node 221..node (221+1), mcap x * wdos x) ≤ ccList 221 := by
  refine le_of_le_of_eq (stepC 221 (by norm_num) (by norm_num) (74853/1000000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_222 : (∫ x in node 222..node (222+1), mcap x * wdos x) ≤ ccList 222 := by
  refine le_of_le_of_eq (stepC 222 (by norm_num) (by norm_num) (18519/250000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_223 : (∫ x in node 223..node (223+1), mcap x * wdos x) ≤ ccList 223 := by
  refine le_of_le_of_eq (stepC 223 (by norm_num) (by norm_num) (36651/500000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_224 : (∫ x in node 224..node (224+1), mcap x * wdos x) ≤ ccList 224 := by
  refine le_of_le_of_eq (stepC 224 (by norm_num) (by norm_num) (72533/1000000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_225 : (∫ x in node 225..node (225+1), mcap x * wdos x) ≤ ccList 225 := by
  refine le_of_le_of_eq (stepC 225 (by norm_num) (by norm_num) (35883/500000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_226 : (∫ x in node 226..node (226+1), mcap x * wdos x) ≤ ccList 226 := by
  refine le_of_le_of_eq (stepC 226 (by norm_num) (by norm_num) (17751/250000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_227 : (∫ x in node 227..node (227+1), mcap x * wdos x) ≤ ccList 227 := by
  refine le_of_le_of_eq (stepC 227 (by norm_num) (by norm_num) (14049/200000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_228 : (∫ x in node 228..node (228+1), mcap x * wdos x) ≤ ccList 228 := by
  refine le_of_le_of_eq (stepC 228 (by norm_num) (by norm_num) (69489/1000000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_229 : (∫ x in node 229..node (229+1), mcap x * wdos x) ≤ ccList 229 := by
  refine le_of_le_of_eq (stepC 229 (by norm_num) (by norm_num) (68737/1000000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_230 : (∫ x in node 230..node (230+1), mcap x * wdos x) ≤ ccList 230 := by
  refine le_of_le_of_eq (stepC 230 (by norm_num) (by norm_num) (67989/1000000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_231 : (∫ x in node 231..node (231+1), mcap x * wdos x) ≤ ccList 231 := by
  refine le_of_le_of_eq (stepC 231 (by norm_num) (by norm_num) (16811/250000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_232 : (∫ x in node 232..node (232+1), mcap x * wdos x) ≤ ccList 232 := by
  refine le_of_le_of_eq (stepC 232 (by norm_num) (by norm_num) (33251/500000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_233 : (∫ x in node 233..node (233+1), mcap x * wdos x) ≤ ccList 233 := by
  refine le_of_le_of_eq (stepC 233 (by norm_num) (by norm_num) (16441/250000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_234 : (∫ x in node 234..node (234+1), mcap x * wdos x) ≤ ccList 234 := by
  refine le_of_le_of_eq (stepC 234 (by norm_num) (by norm_num) (65029/1000000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_235 : (∫ x in node 235..node (235+1), mcap x * wdos x) ≤ ccList 235 := by
  refine le_of_le_of_eq (stepC 235 (by norm_num) (by norm_num) (32149/500000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_236 : (∫ x in node 236..node (236+1), mcap x * wdos x) ≤ ccList 236 := by
  refine le_of_le_of_eq (stepC 236 (by norm_num) (by norm_num) (6357/100000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_237 : (∫ x in node 237..node (237+1), mcap x * wdos x) ≤ ccList 237 := by
  refine le_of_le_of_eq (stepC 237 (by norm_num) (by norm_num) (12569/200000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_238 : (∫ x in node 238..node (238+1), mcap x * wdos x) ≤ ccList 238 := by
  refine le_of_le_of_eq (stepC 238 (by norm_num) (by norm_num) (15531/250000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_239 : (∫ x in node 239..node (239+1), mcap x * wdos x) ≤ ccList 239 := by
  refine le_of_le_of_eq (stepC 239 (by norm_num) (by norm_num) (30703/500000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_240 : (∫ x in node 240..node (240+1), mcap x * wdos x) ≤ ccList 240 := by
  refine le_of_le_of_eq (stepC 240 (by norm_num) (by norm_num) (60691/1000000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_241 : (∫ x in node 241..node (241+1), mcap x * wdos x) ≤ ccList 241 := by
  refine le_of_le_of_eq (stepC 241 (by norm_num) (by norm_num) (59979/1000000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_242 : (∫ x in node 242..node (242+1), mcap x * wdos x) ≤ ccList 242 := by
  refine le_of_le_of_eq (stepC 242 (by norm_num) (by norm_num) (5927/100000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_243 : (∫ x in node 243..node (243+1), mcap x * wdos x) ≤ ccList 243 := by
  refine le_of_le_of_eq (stepC 243 (by norm_num) (by norm_num) (11713/200000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_244 : (∫ x in node 244..node (244+1), mcap x * wdos x) ≤ ccList 244 := by
  refine le_of_le_of_eq (stepC 244 (by norm_num) (by norm_num) (28931/500000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_245 : (∫ x in node 245..node (245+1), mcap x * wdos x) ≤ ccList 245 := by
  refine le_of_le_of_eq (stepC 245 (by norm_num) (by norm_num) (57163/1000000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_246 : (∫ x in node 246..node (246+1), mcap x * wdos x) ≤ ccList 246 := by
  refine le_of_le_of_eq (stepC 246 (by norm_num) (by norm_num) (56467/1000000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_247 : (∫ x in node 247..node (247+1), mcap x * wdos x) ≤ ccList 247 := by
  refine le_of_le_of_eq (stepC 247 (by norm_num) (by norm_num) (27887/500000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_248 : (∫ x in node 248..node (248+1), mcap x * wdos x) ≤ ccList 248 := by
  refine le_of_le_of_eq (stepC 248 (by norm_num) (by norm_num) (13771/250000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_249 : (∫ x in node 249..node (249+1), mcap x * wdos x) ≤ ccList 249 := by
  refine le_of_le_of_eq (stepC 249 (by norm_num) (by norm_num) (13599/250000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_250 : (∫ x in node 250..node (250+1), mcap x * wdos x) ≤ ccList 250 := by
  refine le_of_le_of_eq (stepC 250 (by norm_num) (by norm_num) (3357/62500) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_251 : (∫ x in node 251..node (251+1), mcap x * wdos x) ≤ ccList 251 := by
  refine le_of_le_of_eq (stepC 251 (by norm_num) (by norm_num) (53031/1000000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_252 : (∫ x in node 252..node (252+1), mcap x * wdos x) ≤ ccList 252 := by
  refine le_of_le_of_eq (stepC 252 (by norm_num) (by norm_num) (52353/1000000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_253 : (∫ x in node 253..node (253+1), mcap x * wdos x) ≤ ccList 253 := by
  refine le_of_le_of_eq (stepC 253 (by norm_num) (by norm_num) (51677/1000000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_254 : (∫ x in node 254..node (254+1), mcap x * wdos x) ≤ ccList 254 := by
  refine le_of_le_of_eq (stepC 254 (by norm_num) (by norm_num) (10201/200000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_255 : (∫ x in node 255..node (255+1), mcap x * wdos x) ≤ ccList 255 := by
  refine le_of_le_of_eq (stepC 255 (by norm_num) (by norm_num) (10067/200000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_256 : (∫ x in node 256..node (256+1), mcap x * wdos x) ≤ ccList 256 := by
  refine le_of_le_of_eq (stepC 256 (by norm_num) (by norm_num) (12417/250000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_257 : (∫ x in node 257..node (257+1), mcap x * wdos x) ≤ ccList 257 := by
  refine le_of_le_of_eq (stepC 257 (by norm_num) (by norm_num) (12251/250000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_258 : (∫ x in node 258..node (258+1), mcap x * wdos x) ≤ ccList 258 := by
  refine le_of_le_of_eq (stepC 258 (by norm_num) (by norm_num) (48343/1000000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_259 : (∫ x in node 259..node (259+1), mcap x * wdos x) ≤ ccList 259 := by
  refine le_of_le_of_eq (stepC 259 (by norm_num) (by norm_num) (9537/200000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_260 : (∫ x in node 260..node (260+1), mcap x * wdos x) ≤ ccList 260 := by
  refine le_of_le_of_eq (stepC 260 (by norm_num) (by norm_num) (47029/1000000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_261 : (∫ x in node 261..node (261+1), mcap x * wdos x) ≤ ccList 261 := by
  refine le_of_le_of_eq (stepC 261 (by norm_num) (by norm_num) (5797/125000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_262 : (∫ x in node 262..node (262+1), mcap x * wdos x) ≤ ccList 262 := by
  refine le_of_le_of_eq (stepC 262 (by norm_num) (by norm_num) (22863/500000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_263 : (∫ x in node 263..node (263+1), mcap x * wdos x) ≤ ccList 263 := by
  refine le_of_le_of_eq (stepC 263 (by norm_num) (by norm_num) (22539/500000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_264 : (∫ x in node 264..node (264+1), mcap x * wdos x) ≤ ccList 264 := by
  refine le_of_le_of_eq (stepC 264 (by norm_num) (by norm_num) (44433/1000000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_265 : (∫ x in node 265..node (265+1), mcap x * wdos x) ≤ ccList 265 := by
  refine le_of_le_of_eq (stepC 265 (by norm_num) (by norm_num) (43791/1000000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_266 : (∫ x in node 266..node (266+1), mcap x * wdos x) ≤ ccList 266 := by
  refine le_of_le_of_eq (stepC 266 (by norm_num) (by norm_num) (2697/62500) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_267 : (∫ x in node 267..node (267+1), mcap x * wdos x) ≤ ccList 267 := by
  refine le_of_le_of_eq (stepC 267 (by norm_num) (by norm_num) (8503/200000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_268 : (∫ x in node 268..node (268+1), mcap x * wdos x) ≤ ccList 268 := by
  refine le_of_le_of_eq (stepC 268 (by norm_num) (by norm_num) (1047/25000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_269 : (∫ x in node 269..node (269+1), mcap x * wdos x) ≤ ccList 269 := by
  refine le_of_le_of_eq (stepC 269 (by norm_num) (by norm_num) (1289/31250) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_270 : (∫ x in node 270..node (270+1), mcap x * wdos x) ≤ ccList 270 := by
  refine le_of_le_of_eq (stepC 270 (by norm_num) (by norm_num) (40619/1000000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_271 : (∫ x in node 271..node (271+1), mcap x * wdos x) ≤ ccList 271 := by
  refine le_of_le_of_eq (stepC 271 (by norm_num) (by norm_num) (4999/125000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_272 : (∫ x in node 272..node (272+1), mcap x * wdos x) ≤ ccList 272 := by
  refine le_of_le_of_eq (stepC 272 (by norm_num) (by norm_num) (4921/125000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_273 : (∫ x in node 273..node (273+1), mcap x * wdos x) ≤ ccList 273 := by
  refine le_of_le_of_eq (stepC 273 (by norm_num) (by norm_num) (38747/1000000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_274 : (∫ x in node 274..node (274+1), mcap x * wdos x) ≤ ccList 274 := by
  refine le_of_le_of_eq (stepC 274 (by norm_num) (by norm_num) (38127/1000000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_275 : (∫ x in node 275..node (275+1), mcap x * wdos x) ≤ ccList 275 := by
  refine le_of_le_of_eq (stepC 275 (by norm_num) (by norm_num) (37511/1000000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_276 : (∫ x in node 276..node (276+1), mcap x * wdos x) ≤ ccList 276 := by
  refine le_of_le_of_eq (stepC 276 (by norm_num) (by norm_num) (1153/31250) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_277 : (∫ x in node 277..node (277+1), mcap x * wdos x) ≤ ccList 277 := by
  refine le_of_le_of_eq (stepC 277 (by norm_num) (by norm_num) (9071/250000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_278 : (∫ x in node 278..node (278+1), mcap x * wdos x) ≤ ccList 278 := by
  refine le_of_le_of_eq (stepC 278 (by norm_num) (by norm_num) (1427/40000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_279 : (∫ x in node 279..node (279+1), mcap x * wdos x) ≤ ccList 279 := by
  refine le_of_le_of_eq (stepC 279 (by norm_num) (by norm_num) (8767/250000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_280 : (∫ x in node 280..node (280+1), mcap x * wdos x) ≤ ccList 280 := by
  refine le_of_le_of_eq (stepC 280 (by norm_num) (by norm_num) (34463/1000000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_281 : (∫ x in node 281..node (281+1), mcap x * wdos x) ≤ ccList 281 := by
  refine le_of_le_of_eq (stepC 281 (by norm_num) (by norm_num) (33861/1000000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_282 : (∫ x in node 282..node (282+1), mcap x * wdos x) ≤ ccList 282 := by
  refine le_of_le_of_eq (stepC 282 (by norm_num) (by norm_num) (33261/1000000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_283 : (∫ x in node 283..node (283+1), mcap x * wdos x) ≤ ccList 283 := by
  refine le_of_le_of_eq (stepC 283 (by norm_num) (by norm_num) (32663/1000000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_284 : (∫ x in node 284..node (284+1), mcap x * wdos x) ≤ ccList 284 := by
  refine le_of_le_of_eq (stepC 284 (by norm_num) (by norm_num) (8017/250000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_285 : (∫ x in node 285..node (285+1), mcap x * wdos x) ≤ ccList 285 := by
  refine le_of_le_of_eq (stepC 285 (by norm_num) (by norm_num) (1259/40000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_286 : (∫ x in node 286..node (286+1), mcap x * wdos x) ≤ ccList 286 := by
  refine le_of_le_of_eq (stepC 286 (by norm_num) (by norm_num) (7721/250000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_287 : (∫ x in node 287..node (287+1), mcap x * wdos x) ≤ ccList 287 := by
  refine le_of_le_of_eq (stepC 287 (by norm_num) (by norm_num) (3787/125000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_288 : (∫ x in node 288..node (288+1), mcap x * wdos x) ≤ ccList 288 := by
  refine le_of_le_of_eq (stepC 288 (by norm_num) (by norm_num) (2971/100000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_289 : (∫ x in node 289..node (289+1), mcap x * wdos x) ≤ ccList 289 := by
  refine le_of_le_of_eq (stepC 289 (by norm_num) (by norm_num) (14563/500000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_290 : (∫ x in node 290..node (290+1), mcap x * wdos x) ≤ ccList 290 := by
  refine le_of_le_of_eq (stepC 290 (by norm_num) (by norm_num) (446/15625) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_291 : (∫ x in node 291..node (291+1), mcap x * wdos x) ≤ ccList 291 := by
  refine le_of_le_of_eq (stepC 291 (by norm_num) (by norm_num) (5593/200000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_292 : (∫ x in node 292..node (292+1), mcap x * wdos x) ≤ ccList 292 := by
  refine le_of_le_of_eq (stepC 292 (by norm_num) (by norm_num) (27387/1000000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_293 : (∫ x in node 293..node (293+1), mcap x * wdos x) ≤ ccList 293 := by
  refine le_of_le_of_eq (stepC 293 (by norm_num) (by norm_num) (6703/250000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_294 : (∫ x in node 294..node (294+1), mcap x * wdos x) ≤ ccList 294 := by
  refine le_of_le_of_eq (stepC 294 (by norm_num) (by norm_num) (26239/1000000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_295 : (∫ x in node 295..node (295+1), mcap x * wdos x) ≤ ccList 295 := by
  refine le_of_le_of_eq (stepC 295 (by norm_num) (by norm_num) (6417/250000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_296 : (∫ x in node 296..node (296+1), mcap x * wdos x) ≤ ccList 296 := by
  refine le_of_le_of_eq (stepC 296 (by norm_num) (by norm_num) (251/10000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_297 : (∫ x in node 297..node (297+1), mcap x * wdos x) ≤ ccList 297 := by
  refine le_of_le_of_eq (stepC 297 (by norm_num) (by norm_num) (24533/1000000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_298 : (∫ x in node 298..node (298+1), mcap x * wdos x) ≤ ccList 298 := by
  refine le_of_le_of_eq (stepC 298 (by norm_num) (by norm_num) (23969/1000000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_299 : (∫ x in node 299..node (299+1), mcap x * wdos x) ≤ ccList 299 := by
  refine le_of_le_of_eq (stepC 299 (by norm_num) (by norm_num) (11703/500000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_300 : (∫ x in node 300..node (300+1), mcap x * wdos x) ≤ ccList 300 := by
  refine le_of_le_of_eq (stepC 300 (by norm_num) (by norm_num) (11423/500000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_301 : (∫ x in node 301..node (301+1), mcap x * wdos x) ≤ ccList 301 := by
  refine le_of_le_of_eq (stepC 301 (by norm_num) (by norm_num) (1393/62500) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_302 : (∫ x in node 302..node (302+1), mcap x * wdos x) ≤ ccList 302 := by
  refine le_of_le_of_eq (stepC 302 (by norm_num) (by norm_num) (5433/250000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_303 : (∫ x in node 303..node (303+1), mcap x * wdos x) ≤ ccList 303 := by
  refine le_of_le_of_eq (stepC 303 (by norm_num) (by norm_num) (10589/500000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_304 : (∫ x in node 304..node (304+1), mcap x * wdos x) ≤ ccList 304 := by
  refine le_of_le_of_eq (stepC 304 (by norm_num) (by norm_num) (10313/500000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_305 : (∫ x in node 305..node (305+1), mcap x * wdos x) ≤ ccList 305 := by
  refine le_of_le_of_eq (stepC 305 (by norm_num) (by norm_num) (5019/250000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_306 : (∫ x in node 306..node (306+1), mcap x * wdos x) ≤ ccList 306 := by
  refine le_of_le_of_eq (stepC 306 (by norm_num) (by norm_num) (2441/125000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_307 : (∫ x in node 307..node (307+1), mcap x * wdos x) ≤ ccList 307 := by
  refine le_of_le_of_eq (stepC 307 (by norm_num) (by norm_num) (9491/500000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_308 : (∫ x in node 308..node (308+1), mcap x * wdos x) ≤ ccList 308 := by
  refine le_of_le_of_eq (stepC 308 (by norm_num) (by norm_num) (18437/1000000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_309 : (∫ x in node 309..node (309+1), mcap x * wdos x) ≤ ccList 309 := by
  refine le_of_le_of_eq (stepC 309 (by norm_num) (by norm_num) (3579/200000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_310 : (∫ x in node 310..node (310+1), mcap x * wdos x) ≤ ccList 310 := by
  refine le_of_le_of_eq (stepC 310 (by norm_num) (by norm_num) (3471/200000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_311 : (∫ x in node 311..node (311+1), mcap x * wdos x) ≤ ccList 311 := by
  refine le_of_le_of_eq (stepC 311 (by norm_num) (by norm_num) (16817/1000000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_312 : (∫ x in node 312..node (312+1), mcap x * wdos x) ≤ ccList 312 := by
  refine le_of_le_of_eq (stepC 312 (by norm_num) (by norm_num) (16281/1000000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_313 : (∫ x in node 313..node (313+1), mcap x * wdos x) ≤ ccList 313 := by
  refine le_of_le_of_eq (stepC 313 (by norm_num) (by norm_num) (7873/500000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_314 : (∫ x in node 314..node (314+1), mcap x * wdos x) ≤ ccList 314 := by
  refine le_of_le_of_eq (stepC 314 (by norm_num) (by norm_num) (7607/500000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_315 : (∫ x in node 315..node (315+1), mcap x * wdos x) ≤ ccList 315 := by
  refine le_of_le_of_eq (stepC 315 (by norm_num) (by norm_num) (14683/1000000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_316 : (∫ x in node 316..node (316+1), mcap x * wdos x) ≤ ccList 316 := by
  refine le_of_le_of_eq (stepC 316 (by norm_num) (by norm_num) (2831/200000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_317 : (∫ x in node 317..node (317+1), mcap x * wdos x) ≤ ccList 317 := by
  refine le_of_le_of_eq (stepC 317 (by norm_num) (by norm_num) (3407/250000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_318 : (∫ x in node 318..node (318+1), mcap x * wdos x) ≤ ccList 318 := by
  refine le_of_le_of_eq (stepC 318 (by norm_num) (by norm_num) (13103/1000000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_319 : (∫ x in node 319..node (319+1), mcap x * wdos x) ≤ ccList 319 := by
  refine le_of_le_of_eq (stepC 319 (by norm_num) (by norm_num) (629/50000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_320 : (∫ x in node 320..node (320+1), mcap x * wdos x) ≤ ccList 320 := by
  refine le_of_le_of_eq (stepC 320 (by norm_num) (by norm_num) (12059/1000000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_321 : (∫ x in node 321..node (321+1), mcap x * wdos x) ≤ ccList 321 := by
  refine le_of_le_of_eq (stepC 321 (by norm_num) (by norm_num) (11539/1000000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_322 : (∫ x in node 322..node (322+1), mcap x * wdos x) ≤ ccList 322 := by
  refine le_of_le_of_eq (stepC 322 (by norm_num) (by norm_num) (5511/500000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_323 : (∫ x in node 323..node (323+1), mcap x * wdos x) ≤ ccList 323 := by
  refine le_of_le_of_eq (stepC 323 (by norm_num) (by norm_num) (5253/500000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_324 : (∫ x in node 324..node (324+1), mcap x * wdos x) ≤ ccList 324 := by
  refine le_of_le_of_eq (stepC 324 (by norm_num) (by norm_num) (1249/125000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_325 : (∫ x in node 325..node (325+1), mcap x * wdos x) ≤ ccList 325 := by
  refine le_of_le_of_eq (stepC 325 (by norm_num) (by norm_num) (237/25000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_326 : (∫ x in node 326..node (326+1), mcap x * wdos x) ≤ ccList 326 := by
  refine le_of_le_of_eq (stepC 326 (by norm_num) (by norm_num) (8969/1000000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_327 : (∫ x in node 327..node (327+1), mcap x * wdos x) ≤ ccList 327 := by
  refine le_of_le_of_eq (stepC 327 (by norm_num) (by norm_num) (423/50000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_328 : (∫ x in node 328..node (328+1), mcap x * wdos x) ≤ ccList 328 := by
  refine le_of_le_of_eq (stepC 328 (by norm_num) (by norm_num) (7953/1000000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_329 : (∫ x in node 329..node (329+1), mcap x * wdos x) ≤ ccList 329 := by
  refine le_of_le_of_eq (stepC 329 (by norm_num) (by norm_num) (931/125000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_330 : (∫ x in node 330..node (330+1), mcap x * wdos x) ≤ ccList 330 := by
  refine le_of_le_of_eq (stepC 330 (by norm_num) (by norm_num) (1389/200000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_331 : (∫ x in node 331..node (331+1), mcap x * wdos x) ≤ ccList 331 := by
  refine le_of_le_of_eq (stepC 331 (by norm_num) (by norm_num) (6443/1000000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_332 : (∫ x in node 332..node (332+1), mcap x * wdos x) ≤ ccList 332 := by
  refine le_of_le_of_eq (stepC 332 (by norm_num) (by norm_num) (5943/1000000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_333 : (∫ x in node 333..node (333+1), mcap x * wdos x) ≤ ccList 333 := by
  refine le_of_le_of_eq (stepC 333 (by norm_num) (by norm_num) (1089/200000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_334 : (∫ x in node 334..node (334+1), mcap x * wdos x) ≤ ccList 334 := by
  refine le_of_le_of_eq (stepC 334 (by norm_num) (by norm_num) (1237/250000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_335 : (∫ x in node 335..node (335+1), mcap x * wdos x) ≤ ccList 335 := by
  refine le_of_le_of_eq (stepC 335 (by norm_num) (by norm_num) (4453/1000000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_336 : (∫ x in node 336..node (336+1), mcap x * wdos x) ≤ ccList 336 := by
  refine le_of_le_of_eq (stepC 336 (by norm_num) (by norm_num) (99/25000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_337 : (∫ x in node 337..node (337+1), mcap x * wdos x) ≤ ccList 337 := by
  refine le_of_le_of_eq (stepC 337 (by norm_num) (by norm_num) (867/250000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_338 : (∫ x in node 338..node (338+1), mcap x * wdos x) ≤ ccList 338 := by
  refine le_of_le_of_eq (stepC 338 (by norm_num) (by norm_num) (1489/500000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_339 : (∫ x in node 339..node (339+1), mcap x * wdos x) ≤ ccList 339 := by
  refine le_of_le_of_eq (stepC 339 (by norm_num) (by norm_num) (249/100000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_340 : (∫ x in node 340..node (340+1), mcap x * wdos x) ≤ ccList 340 := by
  refine le_of_le_of_eq (stepC 340 (by norm_num) (by norm_num) (2003/1000000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_341 : (∫ x in node 341..node (341+1), mcap x * wdos x) ≤ ccList 341 := by
  refine le_of_le_of_eq (stepC 341 (by norm_num) (by norm_num) (759/500000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_342 : (∫ x in node 342..node (342+1), mcap x * wdos x) ≤ ccList 342 := by
  refine le_of_le_of_eq (stepC 342 (by norm_num) (by norm_num) (207/200000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_343 : (∫ x in node 343..node (343+1), mcap x * wdos x) ≤ ccList 343 := by
  refine le_of_le_of_eq (stepC 343 (by norm_num) (by norm_num) (553/1000000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_344 : (∫ x in node 344..node (344+1), mcap x * wdos x) ≤ ccList 344 := by
  refine le_of_le_of_eq (stepC 344 (by norm_num) (by norm_num) (73/1000000) ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_345 : (∫ x in node 345..node (345+1), mcap x * wdos x) ≤ ccList 345 := by
  refine le_of_le_of_eq (stepC 345 (by norm_num) (by norm_num) 0 ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_346 : (∫ x in node 346..node (346+1), mcap x * wdos x) ≤ ccList 346 := by
  refine le_of_le_of_eq (stepC 346 (by norm_num) (by norm_num) 0 ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
theorem ibound_347 : (∫ x in node 347..node (347+1), mcap x * wdos x) ≤ ccList 347 := by
  refine le_of_le_of_eq (stepC 347 (by norm_num) (by norm_num) 0 ?_ (by norm_num)) ?_
  · rw [mcap16_eq]; refine max_le (by norm_num) ?_
    unfold excess16 node lamstar; norm_num [Finset.sum_range_succ]
  · simp only [ccList, List.getD_cons_zero, List.getD_cons_succ]; norm_num

set_option maxRecDepth 8000 in
/-- Each interval integral is under its tabulated bound. -/
theorem trace_sum_le : ∀ k ∈ Finset.range 348,
    (∫ x in node k..node (k+1), mcap x * wdos x) ≤ ccList k := by
  intro k hk
  have hk348 := Finset.mem_range.mp hk
  interval_cases k
  · exact ibound_0
  · exact ibound_1
  · exact ibound_2
  · exact ibound_3
  · exact ibound_4
  · exact ibound_5
  · exact ibound_6
  · exact ibound_7
  · exact ibound_8
  · exact ibound_9
  · exact ibound_10
  · exact ibound_11
  · exact ibound_12
  · exact ibound_13
  · exact ibound_14
  · exact ibound_15
  · exact ibound_16
  · exact ibound_17
  · exact ibound_18
  · exact ibound_19
  · exact ibound_20
  · exact ibound_21
  · exact ibound_22
  · exact ibound_23
  · exact ibound_24
  · exact ibound_25
  · exact ibound_26
  · exact ibound_27
  · exact ibound_28
  · exact ibound_29
  · exact ibound_30
  · exact ibound_31
  · exact ibound_32
  · exact ibound_33
  · exact ibound_34
  · exact ibound_35
  · exact ibound_36
  · exact ibound_37
  · exact ibound_38
  · exact ibound_39
  · exact ibound_40
  · exact ibound_41
  · exact ibound_42
  · exact ibound_43
  · exact ibound_44
  · exact ibound_45
  · exact ibound_46
  · exact ibound_47
  · exact ibound_48
  · exact ibound_49
  · exact ibound_50
  · exact ibound_51
  · exact ibound_52
  · exact ibound_53
  · exact ibound_54
  · exact ibound_55
  · exact ibound_56
  · exact ibound_57
  · exact ibound_58
  · exact ibound_59
  · exact ibound_60
  · exact ibound_61
  · exact ibound_62
  · exact ibound_63
  · exact ibound_64
  · exact ibound_65
  · exact ibound_66
  · exact ibound_67
  · exact ibound_68
  · exact ibound_69
  · exact ibound_70
  · exact ibound_71
  · exact ibound_72
  · exact ibound_73
  · exact ibound_74
  · exact ibound_75
  · exact ibound_76
  · exact ibound_77
  · exact ibound_78
  · exact ibound_79
  · exact ibound_80
  · exact ibound_81
  · exact ibound_82
  · exact ibound_83
  · exact ibound_84
  · exact ibound_85
  · exact ibound_86
  · exact ibound_87
  · exact ibound_88
  · exact ibound_89
  · exact ibound_90
  · exact ibound_91
  · exact ibound_92
  · exact ibound_93
  · exact ibound_94
  · exact ibound_95
  · exact ibound_96
  · exact ibound_97
  · exact ibound_98
  · exact ibound_99
  · exact ibound_100
  · exact ibound_101
  · exact ibound_102
  · exact ibound_103
  · exact ibound_104
  · exact ibound_105
  · exact ibound_106
  · exact ibound_107
  · exact ibound_108
  · exact ibound_109
  · exact ibound_110
  · exact ibound_111
  · exact ibound_112
  · exact ibound_113
  · exact ibound_114
  · exact ibound_115
  · exact ibound_116
  · exact ibound_117
  · exact ibound_118
  · exact ibound_119
  · exact ibound_120
  · exact ibound_121
  · exact ibound_122
  · exact ibound_123
  · exact ibound_124
  · exact ibound_125
  · exact ibound_126
  · exact ibound_127
  · exact ibound_128
  · exact ibound_129
  · exact ibound_130
  · exact ibound_131
  · exact ibound_132
  · exact ibound_133
  · exact ibound_134
  · exact ibound_135
  · exact ibound_136
  · exact ibound_137
  · exact ibound_138
  · exact ibound_139
  · exact ibound_140
  · exact ibound_141
  · exact ibound_142
  · exact ibound_143
  · exact ibound_144
  · exact ibound_145
  · exact ibound_146
  · exact ibound_147
  · exact ibound_148
  · exact ibound_149
  · exact ibound_150
  · exact ibound_151
  · exact ibound_152
  · exact ibound_153
  · exact ibound_154
  · exact ibound_155
  · exact ibound_156
  · exact ibound_157
  · exact ibound_158
  · exact ibound_159
  · exact ibound_160
  · exact ibound_161
  · exact ibound_162
  · exact ibound_163
  · exact ibound_164
  · exact ibound_165
  · exact ibound_166
  · exact ibound_167
  · exact ibound_168
  · exact ibound_169
  · exact ibound_170
  · exact ibound_171
  · exact ibound_172
  · exact ibound_173
  · exact ibound_174
  · exact ibound_175
  · exact ibound_176
  · exact ibound_177
  · exact ibound_178
  · exact ibound_179
  · exact ibound_180
  · exact ibound_181
  · exact ibound_182
  · exact ibound_183
  · exact ibound_184
  · exact ibound_185
  · exact ibound_186
  · exact ibound_187
  · exact ibound_188
  · exact ibound_189
  · exact ibound_190
  · exact ibound_191
  · exact ibound_192
  · exact ibound_193
  · exact ibound_194
  · exact ibound_195
  · exact ibound_196
  · exact ibound_197
  · exact ibound_198
  · exact ibound_199
  · exact ibound_200
  · exact ibound_201
  · exact ibound_202
  · exact ibound_203
  · exact ibound_204
  · exact ibound_205
  · exact ibound_206
  · exact ibound_207
  · exact ibound_208
  · exact ibound_209
  · exact ibound_210
  · exact ibound_211
  · exact ibound_212
  · exact ibound_213
  · exact ibound_214
  · exact ibound_215
  · exact ibound_216
  · exact ibound_217
  · exact ibound_218
  · exact ibound_219
  · exact ibound_220
  · exact ibound_221
  · exact ibound_222
  · exact ibound_223
  · exact ibound_224
  · exact ibound_225
  · exact ibound_226
  · exact ibound_227
  · exact ibound_228
  · exact ibound_229
  · exact ibound_230
  · exact ibound_231
  · exact ibound_232
  · exact ibound_233
  · exact ibound_234
  · exact ibound_235
  · exact ibound_236
  · exact ibound_237
  · exact ibound_238
  · exact ibound_239
  · exact ibound_240
  · exact ibound_241
  · exact ibound_242
  · exact ibound_243
  · exact ibound_244
  · exact ibound_245
  · exact ibound_246
  · exact ibound_247
  · exact ibound_248
  · exact ibound_249
  · exact ibound_250
  · exact ibound_251
  · exact ibound_252
  · exact ibound_253
  · exact ibound_254
  · exact ibound_255
  · exact ibound_256
  · exact ibound_257
  · exact ibound_258
  · exact ibound_259
  · exact ibound_260
  · exact ibound_261
  · exact ibound_262
  · exact ibound_263
  · exact ibound_264
  · exact ibound_265
  · exact ibound_266
  · exact ibound_267
  · exact ibound_268
  · exact ibound_269
  · exact ibound_270
  · exact ibound_271
  · exact ibound_272
  · exact ibound_273
  · exact ibound_274
  · exact ibound_275
  · exact ibound_276
  · exact ibound_277
  · exact ibound_278
  · exact ibound_279
  · exact ibound_280
  · exact ibound_281
  · exact ibound_282
  · exact ibound_283
  · exact ibound_284
  · exact ibound_285
  · exact ibound_286
  · exact ibound_287
  · exact ibound_288
  · exact ibound_289
  · exact ibound_290
  · exact ibound_291
  · exact ibound_292
  · exact ibound_293
  · exact ibound_294
  · exact ibound_295
  · exact ibound_296
  · exact ibound_297
  · exact ibound_298
  · exact ibound_299
  · exact ibound_300
  · exact ibound_301
  · exact ibound_302
  · exact ibound_303
  · exact ibound_304
  · exact ibound_305
  · exact ibound_306
  · exact ibound_307
  · exact ibound_308
  · exact ibound_309
  · exact ibound_310
  · exact ibound_311
  · exact ibound_312
  · exact ibound_313
  · exact ibound_314
  · exact ibound_315
  · exact ibound_316
  · exact ibound_317
  · exact ibound_318
  · exact ibound_319
  · exact ibound_320
  · exact ibound_321
  · exact ibound_322
  · exact ibound_323
  · exact ibound_324
  · exact ibound_325
  · exact ibound_326
  · exact ibound_327
  · exact ibound_328
  · exact ibound_329
  · exact ibound_330
  · exact ibound_331
  · exact ibound_332
  · exact ibound_333
  · exact ibound_334
  · exact ibound_335
  · exact ibound_336
  · exact ibound_337
  · exact ibound_338
  · exact ibound_339
  · exact ibound_340
  · exact ibound_341
  · exact ibound_342
  · exact ibound_343
  · exact ibound_344
  · exact ibound_345
  · exact ibound_346
  · exact ibound_347

set_option maxRecDepth 8000 in
/-- The tabulated bounds sum to the certificate value. -/
theorem ccList_sum : ∑ k ∈ Finset.range 348, ccList k = 4910662215588023/5000000000000000 := by
  simp only [ccList, List.getD_cons_zero, List.getD_cons_succ, Finset.sum_range_succ,
    Finset.sum_range_zero]
  norm_num
/-- **The trace quadrature bound.**  `(1/π) ∫₀^∞ mcap · wdos ≤ 0.315`, the trace input for the
even-plane pairing budget (item 15). -/
theorem trace_le :
    (1 / Real.pi) * ∫ t in Set.Ioi (0:ℝ), mcap t * wdos t ≤ (315/1000 : ℝ) := by
  have hIoi : (∫ t in Set.Ioi (0:ℝ), mcap t * wdos t)
      = ∫ t in (0:ℝ)..(87/10), mcap t * wdos t := by
    have hbeyond : ∀ t ∈ Set.Ioi (87/10:ℝ), mcap t * wdos t = 0 := by
      intro t ht; rw [Set.mem_Ioi] at ht; rw [mcap_eq_zero_of_ge ht.le, zero_mul]
    rw [← Set.Ioc_union_Ioi_eq_Ioi (by norm_num : (0:ℝ) ≤ 87/10),
      setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
        (g_integrableOn le_rfl)
        (integrableOn_zero.congr_fun (fun t ht => (hbeyond t ht).symm) measurableSet_Ioi),
      setIntegral_eq_zero_of_forall_eq_zero hbeyond, add_zero,
      intervalIntegral.integral_of_le (by norm_num)]
  have hpart : (∫ t in (0:ℝ)..(87/10), mcap t * wdos t)
      = ∑ k ∈ Finset.range 348, ∫ x in node k..node (k+1), mcap x * wdos x := by
    have hint : ∀ k < 348, IntervalIntegrable (fun t => mcap t * wdos t) volume
        (node k) (node (k+1)) := by
      intro k _
      refine (intervalIntegrable_iff_integrableOn_Ioc_of_le ?_).mpr
        (g_integrableOn (by unfold node; positivity))
      unfold node; push_cast; linarith
    have h := (intervalIntegral.sum_integral_adjacent_intervals hint).symm
    have e0 : node 0 = 0 := by unfold node; norm_num
    have e348 : node 348 = 87/10 := by unfold node; norm_num
    rw [e0, e348] at h; exact h
  rw [hIoi, hpart]
  have hsumle : (∑ k ∈ Finset.range 348, ∫ x in node k..node (k+1), mcap x * wdos x)
      ≤ ∑ k ∈ Finset.range 348, ccList k := Finset.sum_le_sum trace_sum_le
  rw [ccList_sum] at hsumle
  have hfin : (1 / Real.pi) * (4910662215588023/5000000000000000 : ℝ) ≤ 315/1000 := by
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ Real.pi_pos]
    nlinarith [Real.pi_gt_d6]
  calc (1 / Real.pi) * (∑ k ∈ Finset.range 348, ∫ x in node k..node (k+1), mcap x * wdos x)
      ≤ (1 / Real.pi) * (4910662215588023/5000000000000000 : ℝ) := by
        apply mul_le_mul_of_nonneg_left hsumle (one_div_nonneg.mpr Real.pi_pos.le)
    _ ≤ 315/1000 := hfin

/-! ### The even plane gap `hpair`: the mass functional obeys the trace bound -/

theorem truncArchSymbol_even (N : ℕ) (t : ℝ) :
    Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol N (-t) = Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol N t := by
  unfold Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol
  refine congrArg _ (Finset.sum_congr rfl (fun k _ => ?_)); rw [show (-t/2)^2 = (t/2)^2 by ring]
theorem mcap_even (t : ℝ) : mcap (-t) = mcap t := by unfold mcap; rw [truncArchSymbol_even]
theorem wdos_even (t : ℝ) : wdos (-t) = wdos t := by
  unfold wdos; rw [show (-t)*Real.log 2 = -(t*Real.log 2) by ring, Real.sin_neg]; ring
theorem mcap_zero_of_le_neg {t : ℝ} (ht : t ≤ -(87/10 : ℝ)) : mcap t = 0 := by
  rw [← mcap_even, ← neg_neg t]; exact mcap_eq_zero_of_ge (by rw [neg_neg]; linarith)
theorem abs_wdos_le_all (t : ℝ) : |wdos t| ≤ Real.log 2 := by
  rcases lt_trichotomy t 0 with h | h | h
  · rw [← wdos_even]; exact abs_wdos_le (by linarith)
  · subst h; unfold wdos
    rw [show Real.sin ((0:ℝ) * Real.log 2) / (2 * 0) = 0 by simp, add_zero,
      abs_of_nonneg (by positivity)]
    linarith [Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)]
  · exact abs_wdos_le h
theorem integrable_mcap_wdos : Integrable (fun t => mcap t * wdos t) (volume : Measure ℝ) := by
  have hsupp : (fun t => mcap t * wdos t)
      = (Set.Icc (-(87/10):ℝ) (87/10)).indicator (fun t => mcap t * wdos t) := by
    funext t; by_cases ht : t ∈ Set.Icc (-(87/10):ℝ) (87/10)
    · rw [Set.indicator_of_mem ht]
    · rw [Set.indicator_of_notMem ht, Set.mem_Icc, not_and_or, not_le, not_le] at *
      rcases ht with h | h
      · rw [mcap_zero_of_le_neg (by linarith), zero_mul]
      · rw [mcap_eq_zero_of_ge (by linarith), zero_mul]
  rw [hsupp, integrable_indicator_iff measurableSet_Icc]
  refine Integrable.mono' (g := fun _ => Real.log 2)
    (integrableOn_const (C := Real.log 2) (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
    (by
      have hw : Measurable wdos := by unfold wdos; fun_prop
      exact (mcap_continuous.measurable.mul hw).aestronglyMeasurable.restrict) ?_
  filter_upwards [] with t
  rw [Real.norm_eq_abs, abs_mul]
  calc |mcap t| * |wdos t| ≤ 1 * Real.log 2 :=
        mul_le_mul (by rw [abs_of_nonneg (mcap_nonneg t)]; exact mcap_le_one t) (abs_wdos_le_all t) (abs_nonneg _) zero_le_one
    _ = Real.log 2 := one_mul _
theorem even_integral_two_Ioi {f : ℝ → ℝ} (hf : Integrable f (volume : Measure ℝ))
    (he : ∀ x, f (-x) = f x) : (∫ x, f x) = 2 * ∫ x in Set.Ioi (0:ℝ), f x := by
  have hIic : (∫ x in Set.Iic (0:ℝ), f x) = ∫ x in Set.Ioi (0:ℝ), f x := by
    have h := integral_comp_neg_Ioi (0:ℝ) f
    rw [neg_zero] at h
    rw [← h]; exact setIntegral_congr_fun measurableSet_Ioi (fun x _ => he x)
  rw [← intervalIntegral.integral_Iic_add_Ioi hf.integrableOn hf.integrableOn, hIic]; ring
theorem mcap_wdos_even (t : ℝ) : mcap (-t) * wdos (-t) = mcap t * wdos t := by
  rw [mcap_even, wdos_even]
theorem integrable_mcap_specDensity {L : ℝ} (u : Cvs.WeilForm.WeilFormOnWindowL2.window L) :
    Integrable (fun t => mcap t * Cvs.WeilForm.SelfConvolutionCosine.specDensity (Cvs.WeilForm.WindowRepresentative.rep u) t)
      (volume : Measure ℝ) := by
  have hspu := Cvs.WeilForm.Archimedean.LevyIntegrandSpectral.integrable_specDensity (Cvs.WeilForm.WindowRepresentative.memLp_rep u) (integrable_rep u)
  refine Integrable.mono' hspu (mcap_continuous.measurable.aestronglyMeasurable.mul hspu.aestronglyMeasurable) ?_
  filter_upwards [] with t
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mcap_nonneg t) (Cvs.WeilForm.SelfConvolutionCosine.specDensity_nonneg _ t))]
  exact mul_le_of_le_one_left (Cvs.WeilForm.SelfConvolutionCosine.specDensity_nonneg _ t) (mcap_le_one t)
theorem hpair {u v : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)}
    (hu : Cvs.WeilForm.WindowReflectionSymmetry.reflW u = u) (hv : Cvs.WeilForm.WindowReflectionSymmetry.reflW v = v)
    (hun : ‖(u : Lp ℝ 2 (volume : Measure ℝ))‖ = 1) (hvn : ‖(v : Lp ℝ 2 (volume : Measure ℝ))‖ = 1)
    (huv : (inner ℝ (u : Lp ℝ 2 (volume : Measure ℝ)) (v : Lp ℝ 2 (volume : Measure ℝ)) : ℝ) = 0) :
    Msym u + Msym v ≤ (315/1000 : ℝ) := by
  have hmu := integrable_mcap_specDensity u
  have hmv := integrable_mcap_specDensity v
  have hae0 : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ 0 := by
    rw [ae_iff]; simp only [not_ne_iff]; rw [show {t : ℝ | t = 0} = {(0:ℝ)} by ext; simp]; exact measure_singleton 0
  unfold Msym
  rw [← integral_add hmu hmv]
  have hmono : (∫ t, mcap t * Cvs.WeilForm.SelfConvolutionCosine.specDensity (Cvs.WeilForm.WindowRepresentative.rep u) t
      + mcap t * Cvs.WeilForm.SelfConvolutionCosine.specDensity (Cvs.WeilForm.WindowRepresentative.rep v) t)
      ≤ ∫ t, mcap t * wdos t / (2 * Real.pi) := by
    refine integral_mono_ae (hmu.add hmv) (integrable_mcap_wdos.div_const _) ?_
    filter_upwards [hae0] with t ht
    have hsum := specDensity_sum_le hu hv hun hvn huv t ht
    have := mul_le_mul_of_nonneg_left hsum (mcap_nonneg t)
    calc mcap t * Cvs.WeilForm.SelfConvolutionCosine.specDensity (Cvs.WeilForm.WindowRepresentative.rep u) t
        + mcap t * Cvs.WeilForm.SelfConvolutionCosine.specDensity (Cvs.WeilForm.WindowRepresentative.rep v) t
        = mcap t * (Cvs.WeilForm.SelfConvolutionCosine.specDensity (Cvs.WeilForm.WindowRepresentative.rep u) t
          + Cvs.WeilForm.SelfConvolutionCosine.specDensity (Cvs.WeilForm.WindowRepresentative.rep v) t) := by ring
      _ ≤ mcap t * (wdos t / (2 * Real.pi)) := this
      _ = mcap t * wdos t / (2 * Real.pi) := by ring
  refine le_trans hmono ?_
  rw [integral_div, even_integral_two_Ioi integrable_mcap_wdos (fun x => mcap_wdos_even x)]
  have htrace := trace_le
  rw [show (2 * ∫ x in Set.Ioi (0:ℝ), mcap x * wdos x) / (2 * Real.pi)
      = (1 / Real.pi) * ∫ x in Set.Ioi (0:ℝ), mcap x * wdos x by
        rw [mul_comm 2 Real.pi]; field_simp]
  exact htrace
