import Mathlib
import Cvs.Upstream.L2FourierIntegralL1L2
import Cvs.Upstream.PlancherelL1L2SpectralDensity

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The cosine transform on `L²(0, ∞)`

    `calK c h y = √(2c/π) ∫₀^∞ h x cos (c x y) dx`,   `‖calK c h‖₂ = ‖h‖₂`,   `calK c ∘ calK c = id`

for `c > 0`, defined on `L²(0, ∞)` through the even extension and the `L²` Fourier transform, and
equal to the integral on `L¹ ∩ L²` by `Cvs.Upstream.L2FourierIntegralL1L2`; its compression to `(t, ∞)` is a contraction.
-/

noncomputable section

open MeasureTheory FourierTransform SchwartzMap Set Real
open scoped ContDiff

namespace Cvs.Upstream.CosineTransformHalfLine

/-- **Pairing with the `L²` transform.**  Against a Schwartz function, `∫ G • 𝓕 u = ∫ 𝓕 G • u`. -/
theorem integral_smul_fourier (u : Lp ℂ 2 (volume : Measure ℝ)) (G : 𝓢(ℝ, ℂ)) :
    ∫ x, G x • (𝓕 u : Lp ℂ 2 (volume : Measure ℝ)) x = ∫ x, (𝓕 G) x • (u : ℝ → ℂ) x := by
  have key := congrArg (fun T : TemperedDistribution ℝ ℂ => T G)
    (Lp.fourier_toTemperedDistribution_eq u)
  simp only [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply] at key
  exact key.symm

/-- **Pairing with the inverse `L²` transform.**  Against a Schwartz function,
`∫ G • 𝓕⁻ u = ∫ 𝓕⁻ G • u`. -/
theorem integral_smul_fourierInv (u : Lp ℂ 2 (volume : Measure ℝ)) (G : 𝓢(ℝ, ℂ)) :
    ∫ x, G x • (𝓕⁻ u : Lp ℂ 2 (volume : Measure ℝ)) x = ∫ x, (𝓕⁻ G) x • (u : ℝ → ℂ) x := by
  have key := congrArg (fun T : TemperedDistribution ℝ ℂ => T G)
    (Lp.fourierInv_toTemperedDistribution_eq u)
  simp only [TemperedDistribution.fourierInv_apply, Lp.toTemperedDistribution_apply] at key
  exact key.symm

/-- **Schwartz pairings determine a function.**  Locally integrable functions with the same pairing
against every Schwartz function agree almost everywhere. -/
theorem ae_eq_of_pairing {u v : ℝ → ℂ} (hu : LocallyIntegrable u volume)
    (hv : LocallyIntegrable v volume)
    (h : ∀ G : 𝓢(ℝ, ℂ), ∫ x, G x • u x = ∫ x, G x • v x) : u =ᵐ[volume] v := by
  refine ae_eq_of_integral_contDiff_smul_eq hu hv fun g hg hgc => ?_
  have hgc' : HasCompactSupport (fun x => (g x : ℂ)) := hgc.comp_left Complex.ofReal_zero
  have hgs : ContDiff ℝ ∞ (fun x => (g x : ℂ)) := Complex.ofRealCLM.contDiff.comp hg
  set G : 𝓢(ℝ, ℂ) := hgc'.toSchwartzMap hgs with hG
  have hGx : ∀ x, G x = (g x : ℂ) := fun x => rfl
  have hsmul : ∀ (x : ℝ) (z : ℂ), g x • z = G x • z := fun x z => by
    rw [hGx, Complex.real_smul, smul_eq_mul]
  simp only [hsmul]
  exact h G

/-- Multiplication by a nonzero real is quasi-measure-preserving. -/
theorem qmp_mul {a : ℝ} (ha : a ≠ 0) :
    QuasiMeasurePreserving (fun x : ℝ => a * x) volume volume := by
  simpa [smul_eq_mul] using Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ)) ha

/-- A dilate of a square-integrable function is square-integrable. -/
theorem memLp_comp_mul {f : ℝ → ℂ} (hf : MemLp f 2 (volume : Measure ℝ)) {a : ℝ} (ha : a ≠ 0) :
    MemLp (fun x => f (a * x)) 2 (volume : Measure ℝ) := by
  have hm : AEStronglyMeasurable (fun x => f (a * x)) volume :=
    hf.aestronglyMeasurable.comp_quasiMeasurePreserving (qmp_mul ha)
  rw [memLp_two_iff_integrable_sq_norm hm]
  have := ((memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).1 hf).comp_mul_left' ha
  simpa using this

/-- Multiplication by a nonzero real, as a continuous linear equivalence of `ℝ`. -/
def dil {a : ℝ} (ha : a ≠ 0) : ℝ ≃L[ℝ] ℝ :=
  (LinearEquiv.smulOfNeZero ℝ ℝ a ha).toContinuousLinearEquiv

/-- **Fourier integral of a dilate.**  `𝓕 (G (a ·)) ξ = |a|⁻¹ 𝓕 G (ξ / a)`. -/
theorem fourier_comp_mul (G : ℝ → ℂ) {a : ℝ} (ha : a ≠ 0) (ξ : ℝ) :
    𝓕 (fun x => G (a * x)) ξ = ((|a|⁻¹ : ℝ) : ℂ) * 𝓕 G (a⁻¹ * ξ) := by
  rw [Real.fourier_real_eq, Real.fourier_real_eq]
  have h := Measure.integral_comp_mul_left
    (fun w : ℝ => 𝐞 (-(w * (a⁻¹ * ξ))) • G w) a
  have h2 : ∀ v : ℝ, 𝐞 (-(a * v * (a⁻¹ * ξ))) • G (a * v) = 𝐞 (-(v * ξ)) • G (a * v) := by
    intro v; congr 3; field_simp
  simp only [h2] at h
  rw [h, abs_inv, Complex.real_smul]

/-- **Change of variables `x ↦ a x`** on the whole line, solved for the original integral. -/
theorem integral_eq_abs_mul_comp (g : ℝ → ℂ) {a : ℝ} (ha : a ≠ 0) :
    ∫ x, g x = ((|a| : ℝ) : ℂ) * ∫ x, g (a * x) := by
  rw [Measure.integral_comp_mul_left, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul,
    abs_inv, mul_inv_cancel₀ (abs_ne_zero.2 ha), Complex.ofReal_one, one_mul]

/-- **The `L²` transform of a dilate.**  For `u ∈ L²(ℝ)` and `a ≠ 0`,
`𝓕 (u (a ·)) = |a|⁻¹ (𝓕 u)(· / a)` almost everywhere. -/
theorem fourier_toLp_comp_mul (u : Lp ℂ 2 (volume : Measure ℝ)) {a : ℝ} (ha : a ≠ 0)
    (hm : MemLp (fun x => (u : ℝ → ℂ) (a * x)) 2 (volume : Measure ℝ)) :
    ((𝓕 (hm.toLp _) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume]
      fun ξ => ((|a|⁻¹ : ℝ) : ℂ) * (𝓕 u : Lp ℂ 2 (volume : Measure ℝ)) (a⁻¹ * ξ) := by
  set c : ℂ := ((|a|⁻¹ : ℝ) : ℂ) with hc
  have hc0 : (|a|⁻¹ : ℝ) ≠ 0 := by positivity
  refine ae_eq_of_pairing ((Lp.memLp _).locallyIntegrable one_le_two)
    (((memLp_comp_mul (Lp.memLp (𝓕 u : Lp ℂ 2 (volume : Measure ℝ))) (inv_ne_zero ha)).const_mul
      c).locallyIntegrable one_le_two) fun G => ?_
  set Ga : 𝓢(ℝ, ℂ) := compCLMOfContinuousLinearEquiv ℂ (dil ha) G with hGa
  have hGa' : ∀ x, Ga x = G (a * x) := fun x => rfl
  have hFGa : ∀ x, (𝓕 Ga) x = c * (𝓕 G) (a⁻¹ * x) := by
    intro x
    rw [fourier_coe, fourier_coe]
    have : (Ga : ℝ → ℂ) = fun y => G (a * y) := funext hGa'
    rw [this, fourier_comp_mul _ ha]
  rw [integral_smul_fourier]
  -- left side: the dilated function
  have hL : ∫ x, (𝓕 G) x • (hm.toLp _ : Lp ℂ 2 (volume : Measure ℝ)) x
      = ∫ x, (𝓕 G) x * (u : ℝ → ℂ) (a * x) := by
    refine integral_congr_ae ?_
    filter_upwards [hm.coeFn_toLp] with x hx
    rw [hx, smul_eq_mul]
  rw [hL]
  -- right side: substitute `ξ = a x`
  have hca : ((|a| : ℝ) : ℂ) * c = 1 := by
    rw [hc, ← Complex.ofReal_mul, mul_inv_cancel₀ (abs_ne_zero.2 ha), Complex.ofReal_one]
  have hR1' : ∫ x, G x • (c * (𝓕 u : Lp ℂ 2 (volume : Measure ℝ)) (a⁻¹ * x))
      = ∫ x, Ga x • (𝓕 u : Lp ℂ 2 (volume : Measure ℝ)) x := by
    rw [integral_eq_abs_mul_comp _ ha]
    have e : ∀ x : ℝ, G (a * x) • (c * (𝓕 u : Lp ℂ 2 (volume : Measure ℝ)) (a⁻¹ * (a * x)))
        = c * (Ga x • (𝓕 u : Lp ℂ 2 (volume : Measure ℝ)) x) := by
      intro x
      rw [hGa', inv_mul_cancel_left₀ ha, smul_eq_mul, smul_eq_mul]; ring
    simp only [e]
    rw [integral_const_mul, ← mul_assoc, hca, one_mul]
  rw [hR1', integral_smul_fourier]
  have e1 : ∀ x : ℝ, (𝓕 Ga) x • (u : ℝ → ℂ) x = c * (𝓕 G) (a⁻¹ * x) * (u : ℝ → ℂ) x := by
    intro x; rw [hFGa, smul_eq_mul]
  simp only [e1]
  -- substitute `x = a y`
  conv_rhs => rw [integral_eq_abs_mul_comp _ ha]
  have e2 : ∀ y : ℝ, c * (𝓕 G) (a⁻¹ * (a * y)) * (u : ℝ → ℂ) (a * y)
      = c * ((𝓕 G) y * (u : ℝ → ℂ) (a * y)) := by
    intro y; rw [inv_mul_cancel_left₀ ha]; ring
  simp only [e2]
  rw [integral_const_mul, ← mul_assoc, hca, one_mul]

/-- **The inverse `L²` transform is the reflected transform**: `𝓕⁻ V (ξ) = 𝓕 V (-ξ)` almost
everywhere. -/
theorem fourierInv_ae_eq (V : Lp ℂ 2 (volume : Measure ℝ)) :
    ((𝓕⁻ V : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume]
      fun ξ => (𝓕 V : Lp ℂ 2 (volume : Measure ℝ)) (-ξ) := by
  have hneg : MemLp (fun ξ => (𝓕 V : Lp ℂ 2 (volume : Measure ℝ)) (-ξ)) 2 volume := by
    simpa using memLp_comp_mul (Lp.memLp (𝓕 V : Lp ℂ 2 (volume : Measure ℝ)))
      (a := -1) (by norm_num)
  refine ae_eq_of_pairing ((Lp.memLp _).locallyIntegrable one_le_two)
    (hneg.locallyIntegrable one_le_two) fun G => ?_
  set Gn : 𝓢(ℝ, ℂ) := compCLMOfContinuousLinearEquiv ℂ (ContinuousLinearEquiv.neg ℝ) G
  have hGn : ∀ x, Gn x = G (-x) := fun x => rfl
  have hFGn : ∀ x, (𝓕 Gn) x = (𝓕⁻ G) x := by
    intro x
    rw [fourier_coe, fourierInv_coe, Real.fourierInv_eq_fourier_comp_neg]
    rfl
  rw [integral_smul_fourierInv]
  conv_rhs => rw [← integral_neg_eq_self]
  simp only [neg_neg]
  have e : ∀ x : ℝ, G (-x) • (𝓕 V : Lp ℂ 2 (volume : Measure ℝ)) x
      = Gn x • (𝓕 V : Lp ℂ 2 (volume : Measure ℝ)) x := fun x => by rw [hGn]
  simp only [e]
  rw [integral_smul_fourier]
  simp only [hFGn]

/-- **The `L²` transform of an even function is even.** -/
theorem fourier_even {V : Lp ℂ 2 (volume : Measure ℝ)}
    (hV : ∀ᵐ x ∂volume, (V : ℝ → ℂ) (-x) = V x) :
    ∀ᵐ ξ ∂volume, (𝓕 V : Lp ℂ 2 (volume : Measure ℝ)) (-ξ)
      = (𝓕 V : Lp ℂ 2 (volume : Measure ℝ)) ξ := by
  have hm := memLp_comp_mul (Lp.memLp V) (a := -1) (by norm_num)
  have hW : hm.toLp _ = V := by
    refine Lp.ext ?_
    filter_upwards [hm.coeFn_toLp, hV] with x hx hVx
    rw [hx]; simpa using hVx
  have h := fourier_toLp_comp_mul V (a := -1) (by norm_num) hm
  rw [hW] at h
  filter_upwards [h] with ξ hξ
  rw [hξ]; simp

/-- **Inversion on even functions.**  For even `V ∈ L²(ℝ)`, `𝓕 (𝓕 V) = V` almost everywhere. -/
theorem fourier_fourier_even {V : Lp ℂ 2 (volume : Measure ℝ)}
    (hV : ∀ᵐ x ∂volume, (V : ℝ → ℂ) (-x) = V x) :
    ((𝓕 (𝓕 V) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume] V := by
  have h := fourierInv_ae_eq (𝓕 V : Lp ℂ 2 (volume : Measure ℝ))
  rw [fourierInv_fourier_eq] at h
  have hq := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving
  have h2 := hq.ae_eq_comp h
  filter_upwards [h2, hV] with x hx hVx
  simp only [Function.comp_apply, neg_neg] at hx
  rw [← hx, hVx]

/-- **The even extension** `x ↦ h |x|` of a function on `(0, ∞)`. -/
def ev {E : Type*} (h : ℝ → E) : ℝ → E := fun x => h |x|

/-- The even extension agrees with the function on `(0, ∞)`. -/
theorem ev_of_pos {E : Type*} (h : ℝ → E) {x : ℝ} (hx : 0 < x) : ev h x = h x := by
  simp [ev, abs_of_pos hx]

/-- The even extension is even. -/
theorem ev_neg {E : Type*} (h : ℝ → E) (x : ℝ) : ev h (-x) = ev h x := by
  simp [ev]

/-- `x ↦ |x|` is quasi-measure-preserving from Lebesgue measure to Lebesgue measure on `(0, ∞)`. -/
theorem qmp_abs : QuasiMeasurePreserving (fun x : ℝ => |x|) volume
    (volume.restrict (Ioi 0)) := by
  refine ⟨continuous_abs.measurable.aemeasurable, Measure.AbsolutelyContinuous.mk fun s hs h0 => ?_⟩
  rw [Measure.restrict_apply hs] at h0
  rw [Measure.map_apply continuous_abs.measurable hs]
  have hsub : (fun x : ℝ => |x|) ⁻¹' s ⊆ (s ∩ Ioi 0) ∪ (Neg.neg ⁻¹' (s ∩ Ioi 0)) ∪ {0} := by
    intro x hx
    simp only [mem_preimage] at hx
    rcases lt_trichotomy x 0 with h | h | h
    · left; right
      simp only [mem_preimage, mem_inter_iff, mem_Ioi]
      exact ⟨by rwa [abs_of_neg h] at hx, by linarith⟩
    · right; exact h
    · left; left
      exact ⟨by rwa [abs_of_pos h] at hx, h⟩
  refine measure_mono_null hsub (measure_union_null (measure_union_null h0 ?_) ?_)
  · rw [Measure.measure_preimage_neg]; exact h0
  · exact measure_singleton 0

/-- The even extension of a function integrable on `(0, ∞)` is integrable. -/
theorem integrable_ev {E : Type*} [NormedAddCommGroup E] {h : ℝ → E}
    (hh : IntegrableOn h (Ioi 0)) : Integrable (ev h) := by
  have hIoi : IntegrableOn (ev h) (Ioi 0) :=
    hh.congr_fun (fun x hx => (ev_of_pos h hx).symm) measurableSet_Ioi
  have hIic : IntegrableOn (ev h) (Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let m : MeasurableEmbedding fun x : ℝ => -x := (Homeomorph.neg ℝ).measurableEmbedding
    rw [m.integrableOn_map_iff]
    simp_rw [Function.comp_def, ev_neg, neg_preimage, neg_Iic, neg_zero]
    exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hIoi
  have := hIic.union hIoi
  rwa [Iic_union_Ioi, integrableOn_univ] at this

/-- The even extension of a function in `L²(0, ∞)` is in `L²(ℝ)`. -/
theorem memLp_ev {h : ℝ → ℂ} (hh : MemLp h 2 (volume.restrict (Ioi 0))) :
    MemLp (ev h) 2 (volume : Measure ℝ) := by
  have hm : AEStronglyMeasurable (ev h) volume :=
    hh.aestronglyMeasurable.comp_quasiMeasurePreserving qmp_abs
  rw [memLp_two_iff_integrable_sq_norm hm]
  exact integrable_ev (h := fun x => ‖h x‖ ^ 2)
    ((memLp_two_iff_integrable_sq_norm hh.aestronglyMeasurable).1 hh)

/-- The squared `L²(ℝ)` norm of the even extension is twice the squared norm on `(0, ∞)`. -/
theorem integral_norm_sq_ev (h : ℝ → ℂ) :
    ∫ x, ‖ev h x‖ ^ 2 = 2 * ∫ x in Ioi 0, ‖h x‖ ^ 2 :=
  integral_comp_abs (f := fun x => ‖h x‖ ^ 2)

/-- The `L²` class of an even extension is even almost everywhere. -/
theorem toLp_ev_even {h : ℝ → ℂ} (hm : MemLp (ev h) 2 (volume : Measure ℝ)) :
    ∀ᵐ x ∂volume, ((hm.toLp (ev h) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) (-x)
      = (hm.toLp (ev h) : Lp ℂ 2 (volume : Measure ℝ)) x := by
  have hq := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving
  filter_upwards [hq.ae_eq_comp hm.coeFn_toLp, hm.coeFn_toLp] with x hx hx'
  simp only [Function.comp_apply] at hx
  rw [hx, hx', ev_neg]

open scoped Classical in
/-- **The cosine transform** `calK c h y = √(c/2π) · 𝓕 (h |·|) (c y / 2π)`, through the `L²`
transform of the even extension (`0` when that extension is not in `L²`). -/
def calK (c : ℝ) (h : ℝ → ℂ) : ℝ → ℂ :=
  if hm : MemLp (ev h) 2 (volume : Measure ℝ) then
    fun y => ((√(c / (2 * π)) : ℝ) : ℂ) *
      (𝓕 (hm.toLp (ev h)) : Lp ℂ 2 (volume : Measure ℝ)) (c / (2 * π) * y)
  else 0

/-- The cosine transform of a function whose even extension is in `L²`. -/
theorem calK_eq {c : ℝ} {h : ℝ → ℂ} (hm : MemLp (ev h) 2 (volume : Measure ℝ)) :
    calK c h = fun y => ((√(c / (2 * π)) : ℝ) : ℂ) *
      (𝓕 (hm.toLp (ev h)) : Lp ℂ 2 (volume : Measure ℝ)) (c / (2 * π) * y) := by
  rw [calK, dite_eq_left hm]

/-- **The even extension of `calK c h`** is the dilated transform on the whole line, by evenness of
the transform. -/
theorem ev_calK_ae_eq {c : ℝ} (hc : 0 < c) {h : ℝ → ℂ}
    (hm : MemLp (ev h) 2 (volume : Measure ℝ)) :
    ev (calK c h) =ᵐ[volume] fun y => ((√(c / (2 * π)) : ℝ) : ℂ) *
      (𝓕 (hm.toLp (ev h)) : Lp ℂ 2 (volume : Measure ℝ)) (c / (2 * π) * y) := by
  have ha : c / (2 * π) ≠ 0 := by positivity
  have hF := fourier_even (toLp_ev_even hm)
  filter_upwards [(qmp_mul ha).ae hF] with y hy
  simp only [ev, calK_eq hm]
  rcases le_or_gt 0 y with h0 | h0
  · rw [abs_of_nonneg h0]
  · rw [abs_of_neg h0, mul_neg, hy]

/-- The even extension of the cosine transform is in `L²(ℝ)`. -/
theorem memLp_ev_calK {c : ℝ} (hc : 0 < c) {h : ℝ → ℂ}
    (hm : MemLp (ev h) 2 (volume : Measure ℝ)) :
    MemLp (ev (calK c h)) 2 (volume : Measure ℝ) := by
  have ha : c / (2 * π) ≠ 0 := by positivity
  exact ((memLp_comp_mul (Lp.memLp _) ha).const_mul _).ae_eq (ev_calK_ae_eq hc hm).symm

/-- **Plancherel for the cosine transform**, for `h` with even extension in `L²(ℝ)`. -/
theorem integral_norm_sq_calK {c : ℝ} (hc : 0 < c) {h : ℝ → ℂ}
    (hm : MemLp (ev h) 2 (volume : Measure ℝ)) :
    ∫ y in Ioi 0, ‖calK c h y‖ ^ 2 = ∫ y in Ioi 0, ‖h y‖ ^ 2 := by
  set a : ℝ := c / (2 * π) with ha_def
  have ha : 0 < a := by positivity
  set V : Lp ℂ 2 (volume : Measure ℝ) := hm.toLp (ev h)
  set F : Lp ℂ 2 (volume : Measure ℝ) := 𝓕 V
  have e1 := integral_norm_sq_ev (calK c h)
  have e2 := integral_norm_sq_ev h
  have key : ∫ x, ‖ev (calK c h) x‖ ^ 2 = ∫ x, ‖ev h x‖ ^ 2 := by
    calc ∫ x, ‖ev (calK c h) x‖ ^ 2
        = ∫ x, a * ‖(F : ℝ → ℂ) (a * x)‖ ^ 2 := by
          refine integral_congr_ae ?_
          filter_upwards [ev_calK_ae_eq hc hm] with x hx
          rw [hx, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs,
            Real.sq_sqrt ha.le]
      _ = a * (|a⁻¹| * ∫ x, ‖(F : ℝ → ℂ) x‖ ^ 2) := by
          rw [integral_const_mul, Measure.integral_comp_mul_left
            (fun x => ‖(F : ℝ → ℂ) x‖ ^ 2) a, smul_eq_mul]
      _ = ∫ x, ‖(F : ℝ → ℂ) x‖ ^ 2 := by
          rw [abs_of_pos (inv_pos.2 ha), ← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul]
      _ = ‖F‖ ^ 2 := (Cvs.Upstream.PlancherelL1L2SpectralDensity.norm_sq_eq_integral F).symm
      _ = ‖V‖ ^ 2 := by rw [Lp.norm_fourier_eq]
      _ = ∫ x, ‖(V : ℝ → ℂ) x‖ ^ 2 := Cvs.Upstream.PlancherelL1L2SpectralDensity.norm_sq_eq_integral V
      _ = ∫ x, ‖ev h x‖ ^ 2 := by
          refine integral_congr_ae ?_
          filter_upwards [hm.coeFn_toLp] with x hx
          rw [hx]
  linarith

/-- **The cosine transform is an involution**: `calK c (calK c h)` is the even extension of `h`
almost everywhere. -/
theorem calK_calK_ae_eq {c : ℝ} (hc : 0 < c) {h : ℝ → ℂ}
    (hm : MemLp (ev h) 2 (volume : Measure ℝ)) :
    calK c (calK c h) =ᵐ[volume] ev h := by
  set a : ℝ := c / (2 * π) with ha_def
  have ha : 0 < a := by positivity
  set V : Lp ℂ 2 (volume : Measure ℝ) := hm.toLp (ev h)
  set F : Lp ℂ 2 (volume : Measure ℝ) := 𝓕 V
  have hk := memLp_ev_calK hc hm
  have hW := memLp_comp_mul (Lp.memLp F) ha.ne'
  set W : Lp ℂ 2 (volume : Measure ℝ) := hW.toLp _
  have hKW : hk.toLp (ev (calK c h)) = ((√a : ℝ) : ℂ) • W := by
    refine Lp.ext ?_
    filter_upwards [hk.coeFn_toLp, Lp.coeFn_smul ((√a : ℝ) : ℂ) W, hW.coeFn_toLp,
      ev_calK_ae_eq hc hm] with x h1 h2 h3 h4
    rw [h1, h2, Pi.smul_apply, h3, h4, smul_eq_mul]
  have hFW := fourier_toLp_comp_mul F ha.ne' hW
  have hsm := Lp.coeFn_smul ((√a : ℝ) : ℂ) (𝓕 W : Lp ℂ 2 (volume : Measure ℝ))
  have hFF := fourier_fourier_even (toLp_ev_even hm)
  rw [calK_eq hk, hKW, fourier_smul]
  filter_upwards [(qmp_mul ha.ne').ae hsm, (qmp_mul ha.ne').ae hFW, hFF, hm.coeFn_toLp]
    with y h1 h2 h3 h4
  rw [h1, Pi.smul_apply, smul_eq_mul, h2, inv_mul_cancel_left₀ ha.ne', h3, h4,
    abs_of_pos ha, ← mul_assoc, ← Complex.ofReal_mul, Real.mul_self_sqrt ha.le, ← mul_assoc,
    ← Complex.ofReal_mul, mul_inv_cancel₀ ha.ne', Complex.ofReal_one, one_mul]

/-- The cosine transform depends only on the class of `h` on `(0, ∞)`. -/
theorem calK_congr {c : ℝ} {h₁ h₂ : ℝ → ℂ} (h : h₁ =ᵐ[volume.restrict (Ioi 0)] h₂) :
    calK c h₁ = calK c h₂ := by
  have he : ev h₁ =ᵐ[volume] ev h₂ := qmp_abs.ae_eq_comp h
  by_cases hm : MemLp (ev h₁) 2 (volume : Measure ℝ)
  · have hm2 : MemLp (ev h₂) 2 (volume : Measure ℝ) := hm.ae_eq he
    rw [calK_eq hm, calK_eq hm2, MemLp.toLp_congr hm hm2 he]
  · have hm2 : ¬ MemLp (ev h₂) 2 (volume : Measure ℝ) := fun h2 => hm (h2.ae_eq he.symm)
    rw [calK, dite_eq_right hm, calK, dite_eq_right hm2]

/-- **Additivity** of the cosine transform, almost everywhere. -/
theorem calK_add {c : ℝ} (hc : 0 < c) {h₁ h₂ : ℝ → ℂ}
    (hm₁ : MemLp (ev h₁) 2 (volume : Measure ℝ)) (hm₂ : MemLp (ev h₂) 2 (volume : Measure ℝ)) :
    calK c (h₁ + h₂) =ᵐ[volume] calK c h₁ + calK c h₂ := by
  have ha : c / (2 * π) ≠ 0 := by positivity
  have hm : MemLp (ev (h₁ + h₂)) 2 (volume : Measure ℝ) := hm₁.add hm₂
  have hL : hm.toLp (ev (h₁ + h₂)) = hm₁.toLp (ev h₁) + hm₂.toLp (ev h₂) :=
    (MemLp.toLp_congr hm (hm₁.add hm₂) (ae_of_all _ fun _ => rfl)).trans
      (MemLp.toLp_add hm₁ hm₂)
  rw [calK_eq hm, calK_eq hm₁, calK_eq hm₂, hL, FourierTransform.fourier_add]
  filter_upwards [(qmp_mul ha).ae (Lp.coeFn_add (𝓕 (hm₁.toLp (ev h₁)) :
    Lp ℂ 2 (volume : Measure ℝ)) (𝓕 (hm₂.toLp (ev h₂))))] with y hy
  rw [hy, Pi.add_apply, Pi.add_apply, mul_add]

/-- **Homogeneity** of the cosine transform, almost everywhere. -/
theorem calK_smul {c : ℝ} (hc : 0 < c) (r : ℂ) {h : ℝ → ℂ}
    (hm : MemLp (ev h) 2 (volume : Measure ℝ)) :
    calK c (r • h) =ᵐ[volume] r • calK c h := by
  have ha : c / (2 * π) ≠ 0 := by positivity
  have hm' : MemLp (ev (r • h)) 2 (volume : Measure ℝ) := hm.const_smul r
  have hL : hm'.toLp (ev (r • h)) = r • hm.toLp (ev h) :=
    (MemLp.toLp_congr hm' (hm.const_smul r) (ae_of_all _ fun _ => rfl)).trans
      (MemLp.toLp_const_smul r hm)
  rw [calK_eq hm', calK_eq hm, hL, fourier_smul]
  filter_upwards [(qmp_mul ha).ae (Lp.coeFn_smul r (𝓕 (hm.toLp (ev h)) :
    Lp ℂ 2 (volume : Measure ℝ)))] with y hy
  rw [hy]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- **The Fourier integral of an integrable even extension** is twice the cosine integral over
`(0, ∞)`. -/
theorem fourier_ev {h : ℝ → ℂ} (hi : Integrable (ev h)) (ξ : ℝ) :
    𝓕 (ev h) ξ = 2 * ∫ x in Ioi 0, h x * (Real.cos (2 * π * x * ξ) : ℂ) := by
  rw [Real.fourier_real_eq]
  set g : ℝ → ℂ := fun v => 𝐞 (-(v * ξ)) • ev h v with hg_def
  have hg : Integrable g := by
    have := (Real.fourierIntegral_convergent_iff (μ := volume) (f := ev h) ξ).2 hi
    convert this using 3 with v
    simp [mul_comm]
  have hgn : Integrable (fun v => g (-v)) := hg.comp_neg
  rw [← intervalIntegral.integral_Iic_add_Ioi (b := 0) hg.integrableOn hg.integrableOn]
  rw [← neg_zero, ← integral_comp_neg_Ioi, neg_zero]
  rw [← integral_add hgn.integrableOn hg.integrableOn, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  simp only [hg_def, ev_neg, ev_of_pos h hx, Circle.smul_def, Real.fourierChar_apply,
    smul_eq_mul]
  have h2 := Complex.two_cos (((2 * π * x * ξ : ℝ)) : ℂ)
  rw [← Complex.ofReal_cos] at h2
  rw [← add_mul, mul_comm (h x), ← mul_assoc, h2]
  congr 2
  · congr 1; push_cast; ring
  · congr 1; push_cast; ring

/-- **The cosine transform is the cosine integral** `√(2c/π) ∫₀^∞ h x cos (c x y) dx` when the even
extension is in `L¹ ∩ L²`. -/
theorem calK_ae_eq_integral {c : ℝ} (hc : 0 < c) {h : ℝ → ℂ}
    (hm : MemLp (ev h) 2 (volume : Measure ℝ)) (hi : Integrable (ev h)) :
    calK c h =ᵐ[volume] fun y => ((√(2 * c / π) : ℝ) : ℂ) *
      ∫ x in Ioi 0, h x * (Real.cos (c * x * y) : ℂ) := by
  have ha : c / (2 * π) ≠ 0 := by positivity
  rw [calK_eq hm]
  filter_upwards [(qmp_mul ha).ae (Cvs.Upstream.L2FourierIntegralL1L2.fourier_toLp_ae_eq hi hm)] with y hy
  rw [hy, fourier_ev hi]
  have hcos : ∀ x : ℝ, 2 * π * x * (c / (2 * π) * y) = c * x * y := by
    intro x; field_simp
  simp only [hcos]
  have hs : √(2 * c / π) = √(c / (2 * π)) * 2 := by
    rw [show 2 * c / π = 2 ^ 2 * (c / (2 * π)) by field_simp,
      Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num), mul_comm]
  rw [hs, Complex.ofReal_mul, mul_assoc]
  norm_num

/-- **The cosine transform maps `L²(0, ∞)` to itself.** -/
theorem memLp_calK {c : ℝ} (hc : 0 < c) {h : ℝ → ℂ}
    (hh : MemLp h 2 (volume.restrict (Ioi 0))) :
    MemLp (calK c h) 2 (volume.restrict (Ioi 0)) :=
  ((memLp_ev_calK hc (memLp_ev hh)).restrict (Ioi 0)).ae_eq
    ((ae_restrict_mem measurableSet_Ioi).mono fun _ hx => ev_of_pos _ hx)

/-- **Unitarity on `L²(0, ∞)`**: `∫₀^∞ ‖calK c h‖² = ∫₀^∞ ‖h‖²`. -/
theorem norm_calK {c : ℝ} (hc : 0 < c) {h : ℝ → ℂ}
    (hh : MemLp h 2 (volume.restrict (Ioi 0))) :
    ∫ y in Ioi 0, ‖calK c h y‖ ^ 2 = ∫ y in Ioi 0, ‖h y‖ ^ 2 :=
  integral_norm_sq_calK hc (memLp_ev hh)

/-- **Involution on `L²(0, ∞)`**: `calK c (calK c h) = h` almost everywhere on `(0, ∞)`. -/
theorem calK_calK {c : ℝ} (hc : 0 < c) {h : ℝ → ℂ}
    (hh : MemLp h 2 (volume.restrict (Ioi 0))) :
    calK c (calK c h) =ᵐ[volume.restrict (Ioi 0)] h := by
  filter_upwards [ae_restrict_of_ae (calK_calK_ae_eq hc (memLp_ev hh)),
    ae_restrict_mem measurableSet_Ioi] with y hy hy0
  rw [hy, ev_of_pos h hy0]

/-- **Integral form on `L¹ ∩ L²(0, ∞)`**: `calK c h y = √(2c/π) ∫₀^∞ h x cos (c x y) dx` almost
everywhere. -/
theorem calK_eq_integral {c : ℝ} (hc : 0 < c) {h : ℝ → ℂ}
    (hh : MemLp h 2 (volume.restrict (Ioi 0))) (hi : IntegrableOn h (Ioi 0)) :
    calK c h =ᵐ[volume] fun y => ((√(2 * c / π) : ℝ) : ℂ) *
      ∫ x in Ioi 0, h x * (Real.cos (c * x * y) : ℂ) :=
  calK_ae_eq_integral hc (memLp_ev hh) (integrable_ev hi)

/-- **Integral form for a real function** on `L¹ ∩ L²(0, ∞)`, as a real cosine integral. -/
theorem calK_ofReal_eq_integral {c : ℝ} (hc : 0 < c) {h : ℝ → ℝ}
    (hh : MemLp h 2 (volume.restrict (Ioi 0))) (hi : IntegrableOn h (Ioi 0)) :
    calK c (fun x => (h x : ℂ)) =ᵐ[volume] fun y =>
      ((√(2 * c / π) * ∫ x in Ioi 0, h x * Real.cos (c * x * y) : ℝ) : ℂ) := by
  have hh' : MemLp (fun x => (h x : ℂ)) 2 (volume.restrict (Ioi 0)) := hh.ofReal
  have hi' : IntegrableOn (fun x => (h x : ℂ)) (Ioi 0) := hi.ofReal
  filter_upwards [calK_eq_integral hc hh' hi'] with y hy
  rw [hy, Complex.ofReal_mul, ← integral_complex_ofReal]
  push_cast
  rfl

/-- **The compression to `(t, ∞)` is a contraction**, for `t ≥ 0`:
`∫_t^∞ ‖calK c (1_(t,∞) h)‖² ≤ ∫_t^∞ ‖h‖²`. -/
theorem norm_calK_indicator_le {c t : ℝ} (hc : 0 < c) (ht : 0 ≤ t) {h : ℝ → ℂ}
    (hh : MemLp h 2 (volume.restrict (Ioi t))) :
    ∫ y in Ioi t, ‖calK c ((Ioi t).indicator h) y‖ ^ 2 ≤ ∫ y in Ioi t, ‖h y‖ ^ 2 := by
  have hI : MemLp ((Ioi t).indicator h) 2 (volume : Measure ℝ) :=
    (memLp_indicator_iff_restrict measurableSet_Ioi.nullMeasurableSet).2 hh
  have hI0 := hI.restrict (Ioi 0)
  have hK := memLp_calK hc hI0
  have hInt := (memLp_two_iff_integrable_sq_norm hK.aestronglyMeasurable).1 hK
  calc ∫ y in Ioi t, ‖calK c ((Ioi t).indicator h) y‖ ^ 2
      ≤ ∫ y in Ioi 0, ‖calK c ((Ioi t).indicator h) y‖ ^ 2 :=
        setIntegral_mono_set hInt (ae_of_all _ fun _ => by positivity)
          (Ioi_subset_Ioi ht).eventuallySubset
    _ = ∫ y in Ioi 0, ‖(Ioi t).indicator h y‖ ^ 2 := norm_calK hc hI0
    _ = ∫ y in Ioi 0, (Ioi t).indicator (fun x => ‖h x‖ ^ 2) y := by
        congr 1; ext y
        by_cases hy : y ∈ Ioi t <;> simp [hy]
    _ = ∫ y in Ioi t, ‖h y‖ ^ 2 := by
        rw [setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi, max_eq_right ht]

end Cvs.Upstream.CosineTransformHalfLine
