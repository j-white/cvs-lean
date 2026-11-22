import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Basic.NNReal.Defs
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Topology.Instances.AddCircle.Defs
import Cvs.WeilForm.MaskedShift.CoherentFamilyDefs
import Cvs.WeilForm.MaskedShift.MasksCompose

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

open MeasureTheory
open scoped NNReal

namespace Cvs.Operator

open Cvs.Operator

/-! # B20: the masked shift, and its composition law

B19's mask identity, lifted to operators on `L²(𝕋)`.  `S_comp` is the
composition law `S a ∘ S b = S (a + b)` — the property `Cvs.Operator.IsCoherent` asks
for, and which `Cvs.Operator.isCoherent_zero` shows is not automatic.
-/

variable {X : Type*} [MeasurableSpace X]

/-- The masked function underlying indicator multiplication. -/
noncomputable def maskFun (μ : Measure X) (s : Set X) (hs : MeasurableSet s)
    (f : Lp ℝ 2 μ) : Lp ℝ 2 μ :=
  MemLp.toLp (s.indicator f) ((Lp.memLp f).indicator hs.nullMeasurableSet)

lemma coeFn_maskFun (μ : Measure X) (s : Set X) (hs : MeasurableSet s)
    (f : Lp ℝ 2 μ) : maskFun μ s hs f =ᵐ[μ] s.indicator f :=
  MemLp.coeFn_toLp _

set_option maxHeartbeats 800000 in
/-- Indicator multiplication as a linear map on `L²(μ)`. -/
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
    · simp [Set.indicator_of_notMem hx]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [coeFn_maskFun μ s hs (c • f),
      Lp.coeFn_smul c (maskFun μ s hs f),
      coeFn_maskFun μ s hs f, Lp.coeFn_smul c f] with x h1 h2 h3 h4
    rw [RingHom.id_apply, h1, h2, Pi.smul_apply, h3]
    by_cases hx : x ∈ s
    · simp only [Set.indicator_of_mem hx]
      rw [h4, Pi.smul_apply]
    · simp [Set.indicator_of_notMem hx]

lemma norm_maskₗ_le (μ : Measure X) (s : Set X) (hs : MeasurableSet s)
    (f : Lp ℝ 2 μ) : ‖maskₗ μ s hs f‖ ≤ ‖f‖ := by
  have h1 : ‖maskFun μ s hs f‖ = (eLpNorm (s.indicator f) 2 μ).toReal :=
    Lp.norm_toLp _ _
  show ‖maskFun μ s hs f‖ ≤ ‖f‖
  rw [h1, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f) (eLpNorm_indicator_le _ (s := s) hs.nullMeasurableSet)

/-- Indicator multiplication as a bounded operator on `L²(μ)`. -/
noncomputable def maskCLM (μ : Measure X) (s : Set X) (hs : MeasurableSet s) :
    Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  LinearMap.mkContinuous (maskₗ μ s hs) 1 fun f => by
    rw [one_mul]; exact norm_maskₗ_le μ s hs f

lemma coeFn_maskCLM (μ : Measure X) (s : Set X) (hs : MeasurableSet s)
    (f : Lp ℝ 2 μ) : (maskCLM μ s hs f : X → ℝ) =ᵐ[μ] s.indicator (f : X → ℝ) :=
  coeFn_maskFun μ s hs f

/-! ## The masked shift on `L²(𝕋)` -/

abbrev T1 := AddCircle (1 : ℝ)
noncomputable abbrev L2 := Lp ℝ 2 (volume : Measure T1)

/-- Translation by `a`, as a bounded operator. -/
noncomputable def shift (a : ℝ) : L2 →L[ℝ] L2 :=
  (Lp.compMeasurePreservingₗᵢ ℝ (fun x : T1 => x + (a : T1))
    (measurePreserving_add_right volume ((a : ℝ) : T1))).toContinuousLinearMap

lemma coeFn_shift (a : ℝ) (f : L2) :
    (shift a f : T1 → ℝ) =ᵐ[volume] (f : T1 → ℝ) ∘ (fun x => x + (a : T1)) :=
  Lp.coeFn_compMeasurePreserving _ _

lemma measurableSet_maskFwd (β : ℝ) : MeasurableSet (maskFwd β) := by
  have h : maskFwd β = rep ⁻¹' (Set.Iio (1 - β)) := by
    ext z; simp only [maskFwd, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Iio]
    constructor <;> intro h <;> linarith
  rw [h]
  exact (measurable_subtype_coe.comp
    (AddCircle.measurableEquivIco (T := (1:ℝ)) 0).measurable) measurableSet_Iio

/-- **The masked shift** `S β f = 1_{maskFwd β} · f(· + β)`. -/
noncomputable def S (β : ℝ) : L2 →L[ℝ] L2 :=
  (maskCLM volume (maskFwd β) (measurableSet_maskFwd β)).comp (shift β)

lemma coeFn_S (β : ℝ) (f : L2) :
    (S β f : T1 → ℝ)
      =ᵐ[volume] (maskFwd β).indicator ((f : T1 → ℝ) ∘ (fun x => x + (β : T1))) := by
  have h1 := coeFn_maskCLM volume (maskFwd β) (measurableSet_maskFwd β) (shift β f)
  have h2 := coeFn_shift β f
  filter_upwards [h1, h2] with x hx1 hx2
  rw [show (S β f : T1 → ℝ) x = (maskCLM volume (maskFwd β)
    (measurableSet_maskFwd β) (shift β f) : T1 → ℝ) x from rfl, hx1]
  by_cases hmem : x ∈ maskFwd β
  · simp only [Set.indicator_of_mem hmem, hx2]
  · simp only [Set.indicator_of_notMem hmem]

/-! ## The composition law -/

lemma quasi_shift (a : ℝ) :
    QuasiMeasurePreserving (fun x : T1 => x + (a : T1)) volume volume :=
  (measurePreserving_add_right volume ((a : ℝ) : T1)).quasiMeasurePreserving

lemma add_shift (a b : ℝ) (x : T1) :
    x + (a : T1) + (b : T1) = x + ((a + b : ℝ) : T1) := by
  rw [AddCircle.coe_add, add_assoc]

/-- **The masked shifts compose.** `S a ∘ S b = S (a + b)` for `0 ≤ a, 0 ≤ b`. -/
theorem S_comp {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (S a).comp (S b) = S (a + b) := by
  refine ContinuousLinearMap.ext fun f => ?_
  refine Lp.ext ?_
  have h1 := coeFn_S a (S b f)
  have h2 : ((S b f : T1 → ℝ) ∘ (fun x : T1 => x + (a : T1)))
      =ᵐ[volume]
      ((maskFwd b).indicator ((f : T1 → ℝ) ∘ (fun x : T1 => x + (b : T1))))
        ∘ (fun x : T1 => x + (a : T1)) :=
    (quasi_shift a).ae_eq_comp (coeFn_S b f)
  have h3 := coeFn_S (a + b) f
  filter_upwards [h1, h2, h3] with x hx1 hx2 hx3
  rw [show ((S a).comp (S b) f : T1 → ℝ) x = (S a (S b f) : T1 → ℝ) x from rfl,
    hx1, hx3]
  simp only [Function.comp_apply] at hx2
  by_cases hmem : x ∈ maskFwd (a + b)
  · obtain ⟨hxa, hxb⟩ := (Cvs.Operator.maskFwd_comp ha hb x).mpr hmem
    rw [Set.indicator_of_mem hxa, Set.indicator_of_mem hmem]
    simp only [Function.comp_apply]
    rw [hx2, Set.indicator_of_mem hxb]
    simp only [Function.comp_apply, add_shift]
  · rw [Set.indicator_of_notMem hmem]
    by_cases hxa : x ∈ maskFwd a
    · have hxb : x + (a : T1) ∉ maskFwd b := fun hc =>
        hmem ((Cvs.Operator.maskFwd_comp ha hb x).mp ⟨hxa, hc⟩)
      rw [Set.indicator_of_mem hxa]
      simp only [Function.comp_apply]
      rw [hx2, Set.indicator_of_notMem hxb]
    · rw [Set.indicator_of_notMem hxa]

/-- **The mask operator is self-adjoint.**  Both sides of the pairing are the
integral of `f · g` over `s`. -/
theorem isSelfAdjoint_maskCLM (μ : Measure X) (s : Set X) (hs : MeasurableSet s) :
    ∀ f g : Lp ℝ 2 μ,
      inner ℝ (maskCLM μ s hs f) g = inner ℝ f (maskCLM μ s hs g) := by
  intro f g
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_maskCLM μ s hs f, coeFn_maskCLM μ s hs g] with x hf hg
  rw [hf, hg]
  by_cases hx : x ∈ s
  · simp [Set.indicator_of_mem hx]
  · simp [Set.indicator_of_notMem hx]

/-- **The shift's adjoint is the opposite shift.**  Change of variables under a
measure-preserving translation. -/
theorem adjoint_shift (a : ℝ) :
    ContinuousLinearMap.adjoint (shift a) = shift (-a) := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro f g
  rw [L2.inner_def, L2.inner_def]
  have hmp : MeasurePreserving (fun x : T1 => x + (a : T1))
      (volume : Measure T1) volume := measurePreserving_add_right volume ((a : ℝ) : T1)
  have h1 : ∫ x : T1, inner ℝ ((shift (-a) f : T1 → ℝ) x) ((g : T1 → ℝ) x)
      = ∫ x : T1, inner ℝ ((f : T1 → ℝ) (x + ((-a : ℝ) : T1))) ((g : T1 → ℝ) x) := by
    refine integral_congr_ae ?_
    filter_upwards [coeFn_shift (-a) f] with x hx
    rw [hx]; rfl
  have h2 : ∫ x : T1, inner ℝ ((f : T1 → ℝ) x) ((shift a g : T1 → ℝ) x)
      = ∫ x : T1, inner ℝ ((f : T1 → ℝ) x) ((g : T1 → ℝ) (x + (a : T1))) := by
    refine integral_congr_ae ?_
    filter_upwards [coeFn_shift a g] with x hx
    rw [hx]; rfl
  rw [h1, h2]
  rw [← hmp.integral_comp (MeasurableEquiv.addRight ((a : ℝ) : T1)).measurableEmbedding]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  norm_num [← AddCircle.coe_add]

/-- The mask operator equals its own adjoint. -/
theorem adjoint_maskCLM (μ : Measure X) (s : Set X) (hs : MeasurableSet s) :
    ContinuousLinearMap.adjoint (maskCLM μ s hs) = maskCLM μ s hs := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro f g
  exact isSelfAdjoint_maskCLM μ s hs f g

/-- **The adjoint of the masked shift**: mask first, then shift back. -/
theorem adjoint_S (β : ℝ) :
    ContinuousLinearMap.adjoint (S β)
      = (shift (-β)).comp (maskCLM volume (maskFwd β) (measurableSet_maskFwd β)) := by
  unfold S
  rw [ContinuousLinearMap.adjoint_comp, adjoint_shift, adjoint_maskCLM]

/-- Its pointwise form: `S* f (x) = 1_{maskFwd β}(x - β) · f (x - β)`. -/
theorem coeFn_adjoint_S (β : ℝ) (f : L2) :
    (ContinuousLinearMap.adjoint (S β) f : T1 → ℝ)
      =ᵐ[volume] fun x => (maskFwd β).indicator (fun y => (f : T1 → ℝ) y)
          (x + ((-β : ℝ) : T1)) := by
  rw [adjoint_S]
  have h1 := coeFn_shift (-β)
    (maskCLM volume (maskFwd β) (measurableSet_maskFwd β) f)
  have h2 := (quasi_shift (-β)).ae_eq_comp
    (coeFn_maskCLM volume (maskFwd β) (measurableSet_maskFwd β) f)
  filter_upwards [h1, h2] with x hx1 hx2
  rw [show (((shift (-β)).comp (maskCLM volume (maskFwd β)
      (measurableSet_maskFwd β))) f : T1 → ℝ) x
      = (shift (-β) (maskCLM volume (maskFwd β) (measurableSet_maskFwd β) f) : T1 → ℝ) x
      from rfl, hx1]
  simpa using hx2

/-!
## Coherence

`S_comp` needs `0 ≤ a, 0 ≤ b`, and that is not an artefact of the proof.
-/

/-- The masked shift, indexed by `ℝ≥0`. -/
noncomputable def Snn (β : ℝ≥0) : L2 →L[ℝ] L2 := S (β : ℝ)

/-- **The masked shift is a coherent family.** This defeats the vacuity of `Cvs.Operator.isCoherent_zero`:
every `Snn β` with `0 < β < 1` is a non-zero masked shift, and the family satisfies the
composition law with no side conditions. -/
theorem isCoherent_S : Cvs.Operator.IsCoherent Snn :=
  ⟨fun a b => by
    have h := S_comp a.coe_nonneg b.coe_nonneg
    simpa [Snn, NNReal.coe_add] using h⟩

end Cvs.Operator
