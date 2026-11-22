/-
The Single-Atom Path Law — the complexification bridge.

The paper's DTFT is genuinely complex (`𝓕v(φ) = Σ vₙ e^{inφ}`), while the
circle-side development of this repository is real. The two are related by
complexification: the masked rotation `W` has real coefficients, so it
preserves real-valued functions, and `pathLawW` is exactly its restriction.

This file supplies the bridge in the form that makes the norms match: an
`L²` function splits into real and imaginary parts, orthogonally, so an
operator acting the same way on both parts has the same norm on the complex
space as on the real one.

Proved here (no `sorry`):
* `reLp`, `imLp` — the real and imaginary parts of a complex `L²` function;
* `norm_sq_eq_re_add_im` — `‖f‖² = ‖Re f‖² + ‖Im f‖²`.
-/
import Cvs.PathLaw.Fourier

open MeasureTheory Real

namespace Cvs.PathLaw

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- The real part of a complex `L²` function. -/
noncomputable def reLp (f : Lp ℂ 2 μ) : Lp ℝ 2 μ := Complex.reCLM.compLp f

/-- The imaginary part of a complex `L²` function. -/
noncomputable def imLp (f : Lp ℂ 2 μ) : Lp ℝ 2 μ := Complex.imCLM.compLp f

theorem coeFn_reLp (f : Lp ℂ 2 μ) :
    (reLp f : α → ℝ) =ᵐ[μ] fun x => ((f : α → ℂ) x).re := by
  filter_upwards [ContinuousLinearMap.coeFn_compLp' Complex.reCLM f] with x hx
  show (Complex.reCLM.compLp f : α → ℝ) x = _
  rw [hx]
  rfl

theorem coeFn_imLp (f : Lp ℂ 2 μ) :
    (imLp f : α → ℝ) =ᵐ[μ] fun x => ((f : α → ℂ) x).im := by
  filter_upwards [ContinuousLinearMap.coeFn_compLp' Complex.imCLM f] with x hx
  show (Complex.imCLM.compLp f : α → ℝ) x = _
  rw [hx]
  rfl

/-! ### The norm splits -/

/-- For a real `L²` function, `‖f‖² = ∫ f²`. -/
theorem norm_sq_eq_integral_real (f : Lp ℝ 2 μ) :
    ‖f‖ ^ 2 = ∫ x, (f : α → ℝ) x ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [sq]

/-- For a complex `L²` function, `‖f‖² = ∫ ‖f‖²`. -/
theorem norm_sq_eq_integral_complex (f : Lp ℂ 2 μ) :
    ‖f‖ ^ 2 = ∫ x, ‖(f : α → ℂ) x‖ ^ 2 ∂μ := by
  have h1 : (inner ℂ f f : ℂ) = ((‖f‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  have h2 : (inner ℂ f f : ℂ) = ((∫ x, ‖(f : α → ℂ) x‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    rw [L2.inner_def, ← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show (inner ℂ ((f : α → ℂ) x) ((f : α → ℂ) x) : ℂ) = _
    rw [inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  rw [h1] at h2
  exact_mod_cast h2

/-- **The norm splits into real and imaginary parts.** -/
theorem norm_sq_eq_re_add_im (f : Lp ℂ 2 μ) :
    ‖f‖ ^ 2 = ‖reLp f‖ ^ 2 + ‖imLp f‖ ^ 2 := by
  rw [norm_sq_eq_integral_complex, norm_sq_eq_integral_real, norm_sq_eq_integral_real]
  have hre : ∫ x, (reLp f : α → ℝ) x ^ 2 ∂μ
      = ∫ x, ((f : α → ℂ) x).re ^ 2 ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [coeFn_reLp f] with x hx
    rw [hx]
  have him : ∫ x, (imLp f : α → ℝ) x ^ 2 ∂μ
      = ∫ x, ((f : α → ℂ) x).im ^ 2 ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [coeFn_imLp f] with x hx
    rw [hx]
  rw [hre, him, ← integral_add]
  · refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show ‖(f : α → ℂ) x‖ ^ 2 = ((f : α → ℂ) x).re ^ 2 + ((f : α → ℂ) x).im ^ 2
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  · exact ((Lp.memLp (reLp f)).ae_eq (coeFn_reLp f)).integrable_sq
  · exact ((Lp.memLp (imLp f)).ae_eq (coeFn_imLp f)).integrable_sq

/-! ### The masked rotation over `ℂ`

The same formula as `pathLawW`, but acting on complex-valued functions. This
is the operator the paper's DTFT actually produces. -/

section CircleC

variable {P : ℝ} [Fact (0 < P)]

local notation "L2C" => Lp ℂ 2 (volume : Measure (AddCircle P))

/-- Indicator multiplication on complex `L²`. -/
noncomputable def maskFunC (s : Set (AddCircle P)) (hs : MeasurableSet s)
    (f : L2C) : L2C :=
  MemLp.toLp (s.indicator (f : AddCircle P → ℂ)) ((Lp.memLp f).indicator hs.nullMeasurableSet)

lemma coeFn_maskFunC (s : Set (AddCircle P)) (hs : MeasurableSet s) (f : L2C) :
    (maskFunC s hs f : AddCircle P → ℂ)
      =ᵐ[volume] s.indicator (f : AddCircle P → ℂ) :=
  MemLp.coeFn_toLp _

set_option maxHeartbeats 800000 in
/-- Indicator multiplication as a linear map on complex `L²`. -/
noncomputable def maskCₗ (s : Set (AddCircle P)) (hs : MeasurableSet s) :
    L2C →ₗ[ℂ] L2C where
  toFun := maskFunC s hs
  map_add' f g := by
    apply Lp.ext
    filter_upwards [coeFn_maskFunC s hs (f + g),
      Lp.coeFn_add (maskFunC s hs f) (maskFunC s hs g),
      coeFn_maskFunC s hs f, coeFn_maskFunC s hs g,
      Lp.coeFn_add f g] with x h1 h2 h3 h4 h5
    rw [h1, h2, Pi.add_apply, h3, h4]
    by_cases hx : x ∈ s
    · simp only [Set.indicator_of_mem hx]
      rw [h5, Pi.add_apply]
    · simp only [Set.indicator_of_notMem hx, add_zero]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [coeFn_maskFunC s hs (c • f),
      Lp.coeFn_smul c (maskFunC s hs f),
      coeFn_maskFunC s hs f, Lp.coeFn_smul c f] with x h1 h2 h3 h4
    rw [RingHom.id_apply, h1, h2, Pi.smul_apply, h3]
    by_cases hx : x ∈ s
    · simp only [Set.indicator_of_mem hx]
      rw [h4, Pi.smul_apply]
    · simp only [Set.indicator_of_notMem hx, smul_zero]

theorem norm_maskCₗ_le (s : Set (AddCircle P)) (hs : MeasurableSet s) (f : L2C) :
    ‖maskCₗ s hs f‖ ≤ ‖f‖ := by
  have h1 : ‖maskFunC s hs f‖
      = (eLpNorm (s.indicator (f : AddCircle P → ℂ)) 2 volume).toReal :=
    Lp.norm_toLp _ _
  show ‖maskFunC s hs f‖ ≤ ‖f‖
  rw [h1, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f) (eLpNorm_indicator_le _ hs.nullMeasurableSet)

/-- Indicator multiplication as a bounded operator on complex `L²`. -/
noncomputable def maskCLMC (s : Set (AddCircle P)) (hs : MeasurableSet s) :
    L2C →L[ℂ] L2C :=
  LinearMap.mkContinuous (maskCₗ s hs) 1 fun f => by
    rw [one_mul]; exact norm_maskCₗ_le s hs f

lemma coeFn_maskCLMC (s : Set (AddCircle P)) (hs : MeasurableSet s) (f : L2C) :
    (maskCLMC s hs f : AddCircle P → ℂ)
      =ᵐ[volume] s.indicator (f : AddCircle P → ℂ) :=
  coeFn_maskFunC s hs f

/-- The Koopman rotation on complex `L²`. -/
noncomputable def koopmanC (a : AddCircle P) : L2C →ₗᵢ[ℂ] L2C :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun x => x + a) (measurePreserving_add_right volume a)

lemma koopmanC_ae (a : AddCircle P) (f : L2C) :
    ∀ᵐ x ∂(volume : Measure (AddCircle P)),
      (koopmanC a f : AddCircle P → ℂ) x = (f : AddCircle P → ℂ) (x + a) := by
  filter_upwards [Lp.coeFn_compMeasurePreserving f (measurePreserving_add_right volume a)]
    with x hx using hx

/-- The masked rotation on complex `L²`. -/
noncomputable def maskedRotationC (a : AddCircle P) (s₁ s₂ : Set (AddCircle P))
    (h₁ : MeasurableSet s₁) (h₂ : MeasurableSet s₂) : L2C →L[ℂ] L2C :=
  (maskCLMC s₁ h₁).comp (koopmanC a).toContinuousLinearMap
    + (maskCLMC s₂ h₂).comp (koopmanC (-a)).toContinuousLinearMap

end CircleC

/-! ### The two norms agree -/

section NormEq

variable {P : ℝ} [Fact (0 < P)]

/-- `reLp` is additive. -/
theorem reLp_add {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (u v : Lp ℂ 2 μ) : reLp (u + v) = reLp u + reLp v := by
  apply Lp.ext
  filter_upwards [coeFn_reLp (u + v), Lp.coeFn_add (reLp u) (reLp v),
    coeFn_reLp u, coeFn_reLp v, Lp.coeFn_add u v] with x h1 h2 h3 h4 h5
  rw [h1, h2, Pi.add_apply, h3, h4, h5, Pi.add_apply, Complex.add_re]

/-- Taking real parts commutes with the mask. -/
theorem reLp_maskCLMC (s : Set (AddCircle P)) (hs : MeasurableSet s)
    (g : Lp ℂ 2 (volume : Measure (AddCircle P))) :
    reLp (maskCLMC s hs g) = maskCLM volume s hs (reLp g) := by
  apply Lp.ext
  filter_upwards [coeFn_reLp (maskCLMC s hs g), coeFn_maskCLMC s hs g,
    coeFn_maskCLM volume s hs (reLp g), coeFn_reLp g] with x h1 h2 h3 h4
  rw [h1, h2, h3]
  by_cases hx : x ∈ s
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, h4]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, Complex.zero_re]

/-- Taking real parts commutes with the rotation. -/
theorem reLp_koopmanC (a : AddCircle P)
    (g : Lp ℂ 2 (volume : Measure (AddCircle P))) :
    reLp (koopmanC a g) = koopman a (reLp g) := by
  apply Lp.ext
  filter_upwards [coeFn_reLp (koopmanC a g), koopmanC_ae a g,
    koopman_ae a (reLp g), ae_translate a (coeFn_reLp g)] with x h1 h2 h3 h4
  rw [h1, h2, h3, h4]

/-- **Taking real parts commutes with the masked rotation.** -/
theorem reLp_maskedRotationC (a : AddCircle P) (s₁ s₂ : Set (AddCircle P))
    (h₁ : MeasurableSet s₁) (h₂ : MeasurableSet s₂)
    (f : Lp ℂ 2 (volume : Measure (AddCircle P))) :
    reLp (maskedRotationC a s₁ s₂ h₁ h₂ f)
      = maskedRotation a s₁ s₂ h₁ h₂ (reLp f) := by
  show reLp ((maskCLMC s₁ h₁) (koopmanC a f) + (maskCLMC s₂ h₂) (koopmanC (-a) f))
      = (maskCLM volume s₁ h₁) (koopman a (reLp f))
        + (maskCLM volume s₂ h₂) (koopman (-a) (reLp f))
  rw [reLp_add, reLp_maskCLMC, reLp_maskCLMC, reLp_koopmanC, reLp_koopmanC]

/-- `imLp` is additive. -/
theorem imLp_add {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (u v : Lp ℂ 2 μ) : imLp (u + v) = imLp u + imLp v := by
  apply Lp.ext
  filter_upwards [coeFn_imLp (u + v), Lp.coeFn_add (imLp u) (imLp v),
    coeFn_imLp u, coeFn_imLp v, Lp.coeFn_add u v] with x h1 h2 h3 h4 h5
  rw [h1, h2, Pi.add_apply, h3, h4, h5, Pi.add_apply, Complex.add_im]

theorem imLp_maskCLMC (s : Set (AddCircle P)) (hs : MeasurableSet s)
    (g : Lp ℂ 2 (volume : Measure (AddCircle P))) :
    imLp (maskCLMC s hs g) = maskCLM volume s hs (imLp g) := by
  apply Lp.ext
  filter_upwards [coeFn_imLp (maskCLMC s hs g), coeFn_maskCLMC s hs g,
    coeFn_maskCLM volume s hs (imLp g), coeFn_imLp g] with x h1 h2 h3 h4
  rw [h1, h2, h3]
  by_cases hx : x ∈ s
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, h4]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, Complex.zero_im]

theorem imLp_koopmanC (a : AddCircle P)
    (g : Lp ℂ 2 (volume : Measure (AddCircle P))) :
    imLp (koopmanC a g) = koopman a (imLp g) := by
  apply Lp.ext
  filter_upwards [coeFn_imLp (koopmanC a g), koopmanC_ae a g,
    koopman_ae a (imLp g), ae_translate a (coeFn_imLp g)] with x h1 h2 h3 h4
  rw [h1, h2, h3, h4]

theorem imLp_maskedRotationC (a : AddCircle P) (s₁ s₂ : Set (AddCircle P))
    (h₁ : MeasurableSet s₁) (h₂ : MeasurableSet s₂)
    (f : Lp ℂ 2 (volume : Measure (AddCircle P))) :
    imLp (maskedRotationC a s₁ s₂ h₁ h₂ f)
      = maskedRotation a s₁ s₂ h₁ h₂ (imLp f) := by
  show imLp ((maskCLMC s₁ h₁) (koopmanC a f) + (maskCLMC s₂ h₂) (koopmanC (-a) f))
      = (maskCLM volume s₁ h₁) (koopman a (imLp f))
        + (maskCLM volume s₂ h₂) (koopman (-a) (imLp f))
  rw [imLp_add, imLp_maskCLMC, imLp_maskCLMC, imLp_koopmanC, imLp_koopmanC]

/-- **The complex masked rotation is no larger than the real one.** -/
theorem norm_maskedRotationC_le (a : AddCircle P) (s₁ s₂ : Set (AddCircle P))
    (h₁ : MeasurableSet s₁) (h₂ : MeasurableSet s₂) :
    ‖maskedRotationC a s₁ s₂ h₁ h₂‖ ≤ ‖maskedRotation a s₁ s₂ h₁ h₂‖ := by
  set W := maskedRotation a s₁ s₂ h₁ h₂ with hW
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg W) fun f => ?_
  have hsq : ‖maskedRotationC a s₁ s₂ h₁ h₂ f‖ ^ 2
      = ‖W (reLp f)‖ ^ 2 + ‖W (imLp f)‖ ^ 2 := by
    rw [norm_sq_eq_re_add_im, reLp_maskedRotationC, imLp_maskedRotationC]
  have hb1 : ‖W (reLp f)‖ ≤ ‖W‖ * ‖reLp f‖ := W.le_opNorm _
  have hb2 : ‖W (imLp f)‖ ≤ ‖W‖ * ‖imLp f‖ := W.le_opNorm _
  have hfsq : ‖f‖ ^ 2 = ‖reLp f‖ ^ 2 + ‖imLp f‖ ^ 2 := norm_sq_eq_re_add_im f
  have hfinal : ‖maskedRotationC a s₁ s₂ h₁ h₂ f‖ ^ 2 ≤ (‖W‖ * ‖f‖) ^ 2 := by
    rw [hsq, mul_pow, hfsq]
    nlinarith [norm_nonneg (W (reLp f)), norm_nonneg (W (imLp f)),
      norm_nonneg (reLp f), norm_nonneg (imLp f), norm_nonneg W]
  have hnn : 0 ≤ ‖W‖ * ‖f‖ := by positivity
  nlinarith [norm_nonneg (maskedRotationC a s₁ s₂ h₁ h₂ f), hfinal, hnn]

end NormEq

/-! ### Embedding the real space, and the reverse inequality -/

/-- A real `L²` function viewed as a complex one. -/
noncomputable def ofRealLp {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (g : Lp ℝ 2 μ) : Lp ℂ 2 μ := Complex.ofRealCLM.compLp g

theorem coeFn_ofRealLp {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (g : Lp ℝ 2 μ) :
    (ofRealLp g : α → ℂ) =ᵐ[μ] fun x => ((g : α → ℝ) x : ℂ) := by
  filter_upwards [ContinuousLinearMap.coeFn_compLp' Complex.ofRealCLM g] with x hx
  show (Complex.ofRealCLM.compLp g : α → ℂ) x = _
  rw [hx]
  rfl

theorem reLp_ofRealLp {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (g : Lp ℝ 2 μ) : reLp (ofRealLp g) = g := by
  apply Lp.ext
  filter_upwards [coeFn_reLp (ofRealLp g), coeFn_ofRealLp g] with x h1 h2
  rw [h1, h2, Complex.ofReal_re]

theorem imLp_ofRealLp {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (g : Lp ℝ 2 μ) : imLp (ofRealLp g) = 0 := by
  apply Lp.ext
  filter_upwards [coeFn_imLp (ofRealLp g), coeFn_ofRealLp g,
    Lp.coeFn_zero ℝ 2 μ] with x h1 h2 h3
  rw [h1, h2, Complex.ofReal_im, h3]
  rfl

theorem norm_ofRealLp {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (g : Lp ℝ 2 μ) : ‖ofRealLp g‖ = ‖g‖ := by
  have hsq : ‖ofRealLp g‖ ^ 2 = ‖g‖ ^ 2 := by
    rw [norm_sq_eq_re_add_im, reLp_ofRealLp, imLp_ofRealLp, norm_zero]
    ring
  have h1 : (0 : ℝ) ≤ ‖ofRealLp g‖ := norm_nonneg _
  have h2 : (0 : ℝ) ≤ ‖g‖ := norm_nonneg _
  nlinarith [hsq, h1, h2]

section OfRealCommute

variable {P : ℝ} [Fact (0 < P)]

theorem ofRealLp_add (u v : Lp ℝ 2 (volume : Measure (AddCircle P))) :
    ofRealLp (u + v) = ofRealLp u + ofRealLp v := by
  apply Lp.ext
  filter_upwards [coeFn_ofRealLp (u + v), Lp.coeFn_add (ofRealLp u) (ofRealLp v),
    coeFn_ofRealLp u, coeFn_ofRealLp v, Lp.coeFn_add u v] with x h1 h2 h3 h4 h5
  rw [h1, h2, Pi.add_apply, h3, h4, h5, Pi.add_apply, Complex.ofReal_add]

theorem ofRealLp_maskCLM (s : Set (AddCircle P)) (hs : MeasurableSet s)
    (g : Lp ℝ 2 (volume : Measure (AddCircle P))) :
    ofRealLp (maskCLM volume s hs g) = maskCLMC s hs (ofRealLp g) := by
  apply Lp.ext
  filter_upwards [coeFn_ofRealLp (maskCLM volume s hs g),
    coeFn_maskCLM volume s hs g, coeFn_maskCLMC s hs (ofRealLp g),
    coeFn_ofRealLp g] with x h1 h2 h3 h4
  rw [h1, h2, h3]
  by_cases hx : x ∈ s
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, h4]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, Complex.ofReal_zero]

theorem ofRealLp_koopman (a : AddCircle P)
    (g : Lp ℝ 2 (volume : Measure (AddCircle P))) :
    ofRealLp (koopman a g) = koopmanC a (ofRealLp g) := by
  apply Lp.ext
  filter_upwards [coeFn_ofRealLp (koopman a g), koopman_ae a g,
    koopmanC_ae a (ofRealLp g), ae_translate a (coeFn_ofRealLp g)]
    with x h1 h2 h3 h4
  rw [h1, h2, h3, h4]

theorem ofRealLp_maskedRotation (a : AddCircle P) (s₁ s₂ : Set (AddCircle P))
    (h₁ : MeasurableSet s₁) (h₂ : MeasurableSet s₂)
    (g : Lp ℝ 2 (volume : Measure (AddCircle P))) :
    ofRealLp (maskedRotation a s₁ s₂ h₁ h₂ g)
      = maskedRotationC a s₁ s₂ h₁ h₂ (ofRealLp g) := by
  show ofRealLp ((maskCLM volume s₁ h₁) (koopman a g)
      + (maskCLM volume s₂ h₂) (koopman (-a) g))
    = (maskCLMC s₁ h₁) (koopmanC a (ofRealLp g))
      + (maskCLMC s₂ h₂) (koopmanC (-a) (ofRealLp g))
  rw [ofRealLp_add, ofRealLp_maskCLM, ofRealLp_maskCLM, ofRealLp_koopman,
    ofRealLp_koopman]

/-- **The two masked rotations have the same norm.** -/
theorem norm_maskedRotationC (a : AddCircle P) (s₁ s₂ : Set (AddCircle P))
    (h₁ : MeasurableSet s₁) (h₂ : MeasurableSet s₂) :
    ‖maskedRotationC a s₁ s₂ h₁ h₂‖ = ‖maskedRotation a s₁ s₂ h₁ h₂‖ := by
  refine le_antisymm (norm_maskedRotationC_le a s₁ s₂ h₁ h₂) ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun g => ?_
  have hstep : ‖maskedRotation a s₁ s₂ h₁ h₂ g‖
      = ‖maskedRotationC a s₁ s₂ h₁ h₂ (ofRealLp g)‖ := by
    rw [← ofRealLp_maskedRotation, norm_ofRealLp]
  rw [hstep, ← norm_ofRealLp g]
  exact (maskedRotationC a s₁ s₂ h₁ h₂).le_opNorm _

end OfRealCommute

/-! ### The Path Law norm identity, over `ℂ` -/

/-- The paper's masked rotation, on complex `L²`. -/
noncomputable def pathLawWC (β : ℝ) :
    Lp ℂ 2 (volume : Measure (AddCircle (1 : ℝ)))
      →L[ℂ] Lp ℂ 2 (volume : Measure (AddCircle (1 : ℝ))) :=
  maskedRotationC ((β : ℝ) : AddCircle (1 : ℝ)) (maskFwd β) (maskBwd β)
    (measurableSet_maskFwd β) (measurableSet_maskBwd β)

/-- **The Path Law norm identity for the complex masked rotation.**
`‖W‖ = 2cos(π/(m+1))` with `m = ⌈1/β⌉`, now on the space the paper's DTFT
actually lands in. -/
theorem norm_pathLawWC (β : ℝ) (hβ : 0 < β) (hβ1 : β ≤ 1) :
    ‖pathLawWC β‖ = chebFactor (capacity 1 β) := by
  rw [pathLawWC, norm_maskedRotationC]
  exact norm_pathLawW β hβ hβ1

end Cvs.PathLaw
