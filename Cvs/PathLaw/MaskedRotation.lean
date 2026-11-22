/-
The Single-Atom Path Law — the masked rotation on `L²(𝕋)`, as a genuine
bounded operator.

This is the analytic side of the Path Law's architecture: the DTFT carries
the Loewner atom to the masked circle rotation
`W f(φ) = 1_{s₁}(φ) f(φ+α) + 1_{s₂}(φ) f(φ−α)`.
Here we construct `W` on `Lp ℝ 2 (volume : Measure (AddCircle T))` from
Mathlib blocks and prove the operator-norm cap `‖W‖ ≤ 2` — the `L²` avatar
of the universal stability bound `‖ΔO_q‖ ≤ 2Λ(q)/√q`.

Blocks leaned on:
* `MeasureTheory.Lp.compMeasurePreservingₗᵢ` — the Koopman operator of a
  measure-preserving map, bundled as a linear isometry;
* `measurePreserving_add_right` + the Haar `MeasureSpace (AddCircle T)`
  instance — rotations preserve the circle's measure;
* `MeasureTheory.MemLp.indicator`, `eLpNorm_indicator_le` — masking does
  not increase the `L²` norm;
* `LinearMap.mkContinuous`, `LinearIsometry.norm_toContinuousLinearMap_le`,
  `ContinuousLinearMap.opNorm_comp_le` — assembling the norm cap.

Proved here (no `sorry`):
* `norm_maskCLM_le`      — `‖M_s‖ ≤ 1` for the mask (indicator) operator;
* `norm_koopman_apply`   — the rotation operator is an isometry;
* `norm_maskedRotation_le` — `‖W‖ ≤ 2`;
* `norm_smul_maskedRotation_le` — `‖(Λ(q)/√q) • W‖ ≤ 2 Λ(q)/√q`.

The exact norm `‖W‖ = chebFactor m` for the paper's masks and angle is proved
in `Cvs.PathLaw.Weight` (`norm_pathLawW`), and the DTFT transfer from `ℓ²(ℤ)`
in `Cvs.PathLaw.Model`.
-/
import Cvs.PathLaw.OpNorm

open MeasureTheory Real

namespace Cvs.PathLaw

/-! ### The mask (indicator multiplication) operator on `L²` -/

variable {X : Type*} [MeasurableSpace X]

/-- The masked function underlying the indicator-multiplication operator. -/
noncomputable def maskFun (μ : Measure X) (s : Set X) (hs : MeasurableSet s)
    (f : Lp ℝ 2 μ) : Lp ℝ 2 μ :=
  MemLp.toLp (s.indicator f) ((Lp.memLp f).indicator hs.nullMeasurableSet)

lemma coeFn_maskFun (μ : Measure X) (s : Set X) (hs : MeasurableSet s)
    (f : Lp ℝ 2 μ) : maskFun μ s hs f =ᵐ[μ] s.indicator f :=
  MemLp.coeFn_toLp _

set_option maxHeartbeats 800000 in
/-- Multiplication by the indicator of a measurable set, as a linear map on
`L²(μ)`. -/
noncomputable def maskₗ (μ : Measure X) (s : Set X) (hs : MeasurableSet s) :
    Lp ℝ 2 μ →ₗ[ℝ] Lp ℝ 2 μ where
  toFun := maskFun μ s hs
  map_add' f g := by
    apply Lp.ext
    filter_upwards [coeFn_maskFun μ s hs (f + g),
      Lp.coeFn_add (maskFun μ s hs f) (maskFun μ s hs g),
      coeFn_maskFun μ s hs f, coeFn_maskFun μ s hs g,
      Lp.coeFn_add f g] with x h1 h2 h3 h4 h5
    rw [h1, h2, Pi.add_apply, h3, h4]
    by_cases hx : x ∈ s
    · simp only [Set.indicator_of_mem hx]
      rw [h5, Pi.add_apply]
    · simp only [Set.indicator_of_notMem hx, add_zero]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [coeFn_maskFun μ s hs (c • f),
      Lp.coeFn_smul c (maskFun μ s hs f),
      coeFn_maskFun μ s hs f, Lp.coeFn_smul c f] with x h1 h2 h3 h4
    rw [RingHom.id_apply, h1, h2, Pi.smul_apply, h3]
    by_cases hx : x ∈ s
    · simp only [Set.indicator_of_mem hx]
      rw [h4, Pi.smul_apply]
    · simp only [Set.indicator_of_notMem hx, smul_zero]

lemma norm_maskₗ_le (μ : Measure X) (s : Set X) (hs : MeasurableSet s)
    (f : Lp ℝ 2 μ) : ‖maskₗ μ s hs f‖ ≤ ‖f‖ := by
  have h1 : ‖maskFun μ s hs f‖ = (eLpNorm (s.indicator f) 2 μ).toReal :=
    Lp.norm_toLp _ _
  show ‖maskFun μ s hs f‖ ≤ ‖f‖
  rw [h1, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f) (eLpNorm_indicator_le _ hs.nullMeasurableSet)

/-- Multiplication by the indicator of a measurable set, as a bounded
operator on `L²(μ)`. -/
noncomputable def maskCLM (μ : Measure X) (s : Set X) (hs : MeasurableSet s) :
    Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  LinearMap.mkContinuous (maskₗ μ s hs) 1 fun f => by
    rw [one_mul]
    exact norm_maskₗ_le μ s hs f

/-- The a.e. description of the mask operator. -/
lemma coeFn_maskCLM (μ : Measure X) (s : Set X) (hs : MeasurableSet s)
    (f : Lp ℝ 2 μ) : (maskCLM μ s hs f : X → ℝ) =ᵐ[μ] s.indicator (f : X → ℝ) :=
  coeFn_maskFun μ s hs f

lemma norm_maskCLM_le (μ : Measure X) (s : Set X) (hs : MeasurableSet s) :
    ‖maskCLM μ s hs‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-! ### The Koopman rotation operator on the circle -/

variable {T : ℝ} [hT : Fact (0 < T)]

/-- The Koopman operator `f ↦ f(· + a)` of the rotation by `a` on
`L²(AddCircle T)`, a linear isometry (rotations preserve Haar measure). -/
noncomputable def koopman (a : AddCircle T) :
    Lp ℝ 2 (volume : Measure (AddCircle T)) →ₗᵢ[ℝ]
      Lp ℝ 2 (volume : Measure (AddCircle T)) :=
  Lp.compMeasurePreservingₗᵢ ℝ (fun x => x + a)
    (measurePreserving_add_right volume a)

theorem norm_koopman_apply (a : AddCircle T)
    (f : Lp ℝ 2 (volume : Measure (AddCircle T))) : ‖koopman a f‖ = ‖f‖ :=
  (koopman a).norm_map f

/-! ### The masked rotation -/

/-- The masked rotation
`W f = 1_{s₁} · f(· + a) + 1_{s₂} · f(· − a)` on `L²(AddCircle T)`. -/
noncomputable def maskedRotation (a : AddCircle T) (s₁ s₂ : Set (AddCircle T))
    (h₁ : MeasurableSet s₁) (h₂ : MeasurableSet s₂) :
    Lp ℝ 2 (volume : Measure (AddCircle T)) →L[ℝ]
      Lp ℝ 2 (volume : Measure (AddCircle T)) :=
  (maskCLM volume s₁ h₁).comp (koopman a).toContinuousLinearMap
    + (maskCLM volume s₂ h₂).comp (koopman (-a)).toContinuousLinearMap

private lemma norm_mask_comp_koopman_le (a : AddCircle T) (s : Set (AddCircle T))
    (hs : MeasurableSet s) :
    ‖(maskCLM volume s hs).comp (koopman a).toContinuousLinearMap‖ ≤ 1 := by
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  calc ‖maskCLM volume s hs‖ * ‖(koopman a).toContinuousLinearMap‖
      ≤ 1 * 1 :=
        mul_le_mul (norm_maskCLM_le volume s hs)
          (koopman a).norm_toContinuousLinearMap_le (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-- **The `L²` stability cap.** The masked rotation has operator norm at
most `2`, whatever the masks and the angle. -/
theorem norm_maskedRotation_le (a : AddCircle T) (s₁ s₂ : Set (AddCircle T))
    (h₁ : MeasurableSet s₁) (h₂ : MeasurableSet s₂) :
    ‖maskedRotation a s₁ s₂ h₁ h₂‖ ≤ 2 := by
  refine (norm_add_le _ _).trans ?_
  have b₁ := norm_mask_comp_koopman_le a s₁ h₁
  have b₂ := norm_mask_comp_koopman_le (-a) s₂ h₂
  linarith

/-- **The Weyl budget on the circle.** The arithmetically weighted masked
rotation obeys the universal cap `2Λ(q)/√q` — the `L²(𝕋)` avatar of
`pathLawNorm_le_cap`. -/
theorem norm_smul_maskedRotation_le (q : ℕ) (a : AddCircle T)
    (s₁ s₂ : Set (AddCircle T)) (h₁ : MeasurableSet s₁) (h₂ : MeasurableSet s₂) :
    ‖weight q • maskedRotation a s₁ s₂ h₁ h₂‖ ≤ 2 * weight q := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (weight_nonneg q)]
  calc weight q * ‖maskedRotation a s₁ s₂ h₁ h₂‖
      ≤ weight q * 2 :=
        mul_le_mul_of_nonneg_left (norm_maskedRotation_le a s₁ s₂ h₁ h₂)
          (weight_nonneg q)
    _ = 2 * weight q := mul_comm _ _

end Cvs.PathLaw
