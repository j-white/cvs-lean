import Mathlib
import Cvs.Prolate.Gram.EquilibriumPotential
import Cvs.Prolate.Gram.WeylCountsDiscretePotential
import Cvs.Upstream.DiscreteContinuousLogPotential
import Cvs.Upstream.SliceMeasurePushforward

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The selection target `ν′ = z + μ_a^{(U)}`: a measure below the Dirichlet density (deepcell §6)

With `φ = 1/(2π√(1 − t²))`, `z` slices `φ` over `u ≤ √(1 − t²)` and `μ_a^{(U)}` slices `sgn(t − a)φ` over `u ≤ U`,
`t ≤ t_e`; their distribution function `F` is nondecreasing (Chebyshev, using `∫_0^a φ = ∫_a^{t_e} φ`) with increments
at most those of `Λ_a`, so `ν′ + μ⁻ = z + μ⁺` for a finite measure `ν′` with `ν′(−∞, y] = F(y)`.
-/

noncomputable section

open Real Set Filter Topology MeasureTheory
open Cvs.Upstream.SliceMeasurePushforward (sliceMeas)
open Cvs.Prolate.Gram.EquilibriumPotential (tE)

namespace Cvs.Prolate.Gram.SelectionTargetMeasure
open Cvs.ZeroCounting

/-! ### A measure from a nondecreasing difference of distribution functions -/

/-- **The difference measure**: if `F = μ₊(−∞, y] − μ₋(−∞, y]` is nondecreasing, continuous and `→ 0` at `−∞`, there is
a finite `ρ` with `ρ + μ₋ = μ₊` and `ρ(−∞, y] = F(y)`. -/
theorem exists_add_eq {μp μm : Measure ℝ} [IsFiniteMeasure μp] [IsFiniteMeasure μm]
    (hmono : Monotone fun y => μp.real (Iic y) - μm.real (Iic y))
    (hcont : Continuous fun y => μp.real (Iic y) - μm.real (Iic y))
    (hbot : Tendsto (fun y => μp.real (Iic y) - μm.real (Iic y)) atBot (𝓝 0)) :
    ∃ ρ : Measure ℝ, IsFiniteMeasure ρ ∧ ρ + μm = μp ∧ ∀ y, ρ.real (Iic y) = μp.real (Iic y) - μm.real (Iic y) := by
  set F := fun y => μp.real (Iic y) - μm.real (Iic y) with hF
  let f : StieltjesFunction ℝ := ⟨F, hmono, fun x => hcont.continuousWithinAt⟩
  have hf : ∀ y, f.measure (Iic y) = ENNReal.ofReal (F y) := fun y => by
    rw [f.measure_Iic hbot y, sub_zero]
  have hF0 : ∀ y, 0 ≤ F y := fun y =>
    le_of_tendsto hbot (Filter.eventually_atBot.2 ⟨y, fun z hz => hmono hz⟩)
  have heq : μp = f.measure + μm := by
    refine Measure.ext_of_Iic μp _ fun y => ?_
    rw [add_apply, hf, ← ofReal_measureReal (measure_ne_top μm _), ← ofReal_measureReal
      (measure_ne_top μp _), ← ENNReal.ofReal_add (hF0 y) measureReal_nonneg]
    congr 1; simp only [hF]; ring
  have hfin : IsFiniteMeasure f.measure := ⟨by
    calc f.measure univ ≤ (f.measure + μm) univ := by rw [add_apply]; exact le_self_add
      _ = μp univ := by rw [← heq]
      _ < ⊤ := measure_lt_top μp univ⟩
  refine ⟨f.measure, hfin, heq.symm, fun y => ?_⟩
  rw [measureReal_def, hf, ENNReal.toReal_ofReal (hF0 y)]

/-! ### Continuity of slice distribution functions -/

section Slice

variable {φ L : ℝ → ℝ} {α β : ℝ}

/-- **Hölder continuity**: `|ν(−∞, y′] − ν(−∞, y]| ≤ (√2∫φ)√|y′ − y|` for a finite slice measure. -/
theorem abs_sliceMeas_real_Iic_sub_le (hφ : Measurable φ) (hL : Measurable L) (hφ0 : ∀ t ∈ Icc α β, 0 ≤ φ t)
    (hφi : IntegrableOn φ (Icc α β)) (hαβ : α ≤ β) [IsFiniteMeasure (sliceMeas φ L α β)] (y y' : ℝ) :
    |(sliceMeas φ L α β).real (Iic y') - (sliceMeas φ L α β).real (Iic y)| ≤
      (√2 * ∫ t in α..β, φ t) * √|y' - y| := by
  set ν := sliceMeas φ L α β
  have key : ∀ y y' : ℝ, y ≤ y' → ν.real (Iic y') - ν.real (Iic y) ≤ (√2 * ∫ t in α..β, φ t) * √(y' - y) := by
    intro y y' h
    have hd : ν.real (Iic y') - ν.real (Iic y) = ν.real (Ioc y y') := by
      have e : Ioc y y' = Iic y' \ Iic y := by ext v; simp [and_comm]
      rw [e, measureReal_sdiff (Iic_subset_Iic.mpr h) measurableSet_Iic]
    rw [hd]
    have hsub : Ioc y y' ⊆ Ioo (y' - (y' - y)) (y' + (y' - y)) ∪ {y'} := by
      intro v hv
      rcases eq_or_lt_of_le hv.2 with h' | h'
      · exact Or.inr h'
      · exact Or.inl ⟨by linarith [hv.1], by linarith [hv.1]⟩
    calc ν.real (Ioc y y') ≤ ν.real (Ioo (y' - (y' - y)) (y' + (y' - y)) ∪ {y'}) := measureReal_mono hsub
      _ ≤ ν.real (Ioo (y' - (y' - y)) (y' + (y' - y))) + ν.real {y'} := measureReal_union_le _ _
      _ = ν.real (Ioo (y' - (y' - y)) (y' + (y' - y))) := by
          have h0 : ν {y'} = 0 := Cvs.Upstream.SliceMeasurePushforward.sliceMeas_singleton hφ hL y'
          simp [measureReal_def, h0]
      _ ≤ _ := Cvs.Upstream.SliceMeasurePushforward.sliceMeas_real_Ioo_le hφ hL hφ0 hφi hαβ (by linarith) y'
  rcases le_total y y' with h | h
  · have h1 := key y y' h
    have h0 : ν.real (Iic y) ≤ ν.real (Iic y') := measureReal_mono (Iic_subset_Iic.mpr h)
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; exact h1
  · have h1 := key y' y h
    have h0 : ν.real (Iic y') ≤ ν.real (Iic y) := measureReal_mono (Iic_subset_Iic.mpr h)
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), neg_sub, neg_sub]; exact h1

/-- A finite slice measure has a continuous distribution function. -/
theorem continuous_sliceMeas_real_Iic (hφ : Measurable φ) (hL : Measurable L) (hφ0 : ∀ t ∈ Icc α β, 0 ≤ φ t)
    (hφi : IntegrableOn φ (Icc α β)) (hαβ : α ≤ β) [IsFiniteMeasure (sliceMeas φ L α β)] :
    Continuous fun y => (sliceMeas φ L α β).real (Iic y) := by
  set K := √2 * ∫ t in α..β, φ t
  refine continuous_iff_continuousAt.mpr fun y => ?_
  have hlim : Tendsto (fun y' : ℝ => K * √|y' - y|) (𝓝 y) (𝓝 0) := by
    have : Tendsto (fun y' : ℝ => K * √|y' - y|) (𝓝 y) (𝓝 (K * √|y - y|)) := by
      exact (continuous_const.mul (Real.continuous_sqrt.comp (continuous_id.sub continuous_const).abs)).tendsto y
    simpa using this
  refine tendsto_iff_norm_sub_tendsto_zero.mpr (squeeze_zero (fun _ => norm_nonneg _) (fun y' => ?_) hlim)
  rw [Real.norm_eq_abs]
  exact abs_sliceMeas_real_Iic_sub_le hφ hL hφ0 hφi hαβ y y'

end Slice

/-! ### The three slice measures -/

/-- The weight `φ(t) = 1/(2π√(1 − t²))`. -/
def phiZ (t : ℝ) : ℝ := 1 / (2 * π) * (1 / √(1 - t ^ 2))

/-- The rung measure `z`: `φ` sliced over `0 ≤ u ≤ √(1 − t²)`, `t ∈ [0, 1]`. -/
def zMeas : Measure ℝ := sliceMeas phiZ (fun t => √(1 - t ^ 2)) 0 1

/-- The positive part `μ⁺` of `μ_a^{(U)}`: `φ` sliced over `0 ≤ u ≤ U`, `t ∈ [a, t_e]`. -/
def muP (a U : ℝ) : Measure ℝ := sliceMeas phiZ (fun _ => U) a (tE a)

/-- The negative part `μ⁻` of `μ_a^{(U)}`: `φ` sliced over `0 ≤ u ≤ U`, `t ∈ [0, a]`. -/
def muM (a U : ℝ) : Measure ℝ := sliceMeas phiZ (fun _ => U) 0 a

theorem measurable_phiZ : Measurable phiZ := by unfold phiZ; fun_prop

theorem phiZ_nonneg (t : ℝ) : 0 ≤ phiZ t := by unfold phiZ; positivity

/-- `φ√(1 − t²) ≤ 1/(2π)`. -/
theorem phiZ_mul_sqrt_le (t : ℝ) : phiZ t * √(1 - t ^ 2) ≤ 1 / (2 * π) := by
  unfold phiZ
  rcases eq_or_ne (√(1 - t ^ 2)) 0 with h | h
  · rw [h]; simp; positivity
  · rw [mul_assoc, one_div_mul_cancel h, mul_one]

/-- `φ ≤ 1/(2π√(1 − b²))` on `[0, b]`, `b < 1`. -/
theorem phiZ_le {b t : ℝ} (hb : b < 1) (ht : t ∈ Icc 0 b) : phiZ t ≤ 1 / (2 * π) * (1 / √(1 - b ^ 2)) := by
  unfold phiZ
  have h1 : 0 < 1 - b ^ 2 := by nlinarith [ht.1, ht.2]
  refine mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le (Real.sqrt_pos.mpr h1) ?_) (by positivity)
  exact Real.sqrt_le_sqrt (by nlinarith [ht.1, ht.2])

/-- `1/√(1 − t²)` is integrable on `[0, 1]`. -/
theorem integrableOn_inv_sqrt : IntegrableOn (fun t : ℝ => 1 / √(1 - t ^ 2)) (Icc 0 1) := by
  have h := intervalIntegral.integrableOn_deriv_of_nonneg (g := arcsin) (g' := fun t => 1 / √(1 - t ^ 2))
    (a := 0) (b := 1) Real.continuous_arcsin.continuousOn
    (fun t ht => Cvs.Prolate.Gram.EquilibriumPotential.hasDerivAt_arcsin' (by nlinarith [ht.1, ht.2])) (fun t _ => by positivity)
  exact h.congr_set_ae Ioc_ae_eq_Icc.symm

theorem integrableOn_phiZ : IntegrableOn phiZ (Icc 0 1) := integrableOn_inv_sqrt.const_mul _

theorem integrableOn_phiZ_of_subset {α β : ℝ} (h0 : 0 ≤ α) (h1 : β ≤ 1) : IntegrableOn phiZ (Icc α β) :=
  integrableOn_phiZ.mono_set (Icc_subset_Icc h0 h1)

instance : IsFiniteMeasure zMeas :=
  Cvs.Upstream.SliceMeasurePushforward.isFiniteMeasure_sliceMeas measurable_phiZ (by fun_prop) (fun t _ => phiZ_nonneg t)
    (fun t _ => phiZ_mul_sqrt_le t)

theorem isFiniteMeasure_box {α β U : ℝ} (hβ : β < 1) (hα : 0 ≤ α) :
    IsFiniteMeasure (sliceMeas phiZ (fun _ => U) α β) :=
  Cvs.Upstream.SliceMeasurePushforward.isFiniteMeasure_sliceMeas measurable_phiZ measurable_const (fun t _ => phiZ_nonneg t)
    (M := 1 / (2 * π) * (1 / √(1 - β ^ 2)) * |U|) fun t ht =>
    (mul_le_mul_of_nonneg_left (le_abs_self U) (phiZ_nonneg t)).trans
      (mul_le_mul_of_nonneg_right (phiZ_le hβ ⟨hα.trans ht.1, ht.2⟩) (abs_nonneg U))

/-- The parameter window `a ∈ [½, 3/5]` has `0 ≤ a ≤ t_e < 1`. -/
theorem tE_facts {a : ℝ} (ha : a ∈ Icc (1 / 2 : ℝ) (3 / 5)) : 0 ≤ a ∧ a ≤ tE a ∧ tE a < 1 ∧ 2 * a ^ 2 < 1 := by
  have h0 : 0 ≤ a := by linarith [ha.1]
  have h2 : 2 * a ^ 2 < 1 := by nlinarith [ha.1, ha.2]
  exact ⟨h0, Cvs.Prolate.Gram.EquilibriumPotential.le_tE h0 (by nlinarith [ha.1, ha.2]), Cvs.Prolate.Gram.EquilibriumPotential.tE_lt_one h2, h2⟩

instance isFiniteMeasure_muP {a U : ℝ} [Fact (a ∈ Icc (1 / 2 : ℝ) (3 / 5))] : IsFiniteMeasure (muP a U) :=
  isFiniteMeasure_box (tE_facts (Fact.out)).2.2.1 (tE_facts (Fact.out)).1

instance isFiniteMeasure_muM {a U : ℝ} [Fact (a ∈ Icc (1 / 2 : ℝ) (3 / 5))] : IsFiniteMeasure (muM a U) :=
  isFiniteMeasure_box ((tE_facts (Fact.out)).2.1.trans_lt (tE_facts (Fact.out)).2.2.1) le_rfl

/-! ### The distribution functions -/

/-- The distribution function of `z`. -/
def zcdf (y : ℝ) : ℝ := ∫ t in (0 : ℝ)..1, phiZ t * min √(1 - t ^ 2) √(y - t ^ 2)

/-- The distribution function of a box slice `φ` over `[α, β] × [0, U]`. -/
def boxcdf (α β U y : ℝ) : ℝ := ∫ t in α..β, phiZ t * min U √(y - t ^ 2)

/-- The distribution function `F` of `ν′ = z + μ⁺ − μ⁻`. -/
def Fcdf (a U y : ℝ) : ℝ := zcdf y + boxcdf a (tE a) U y - boxcdf 0 a U y

theorem intervalIntegrable_phiZ {α β : ℝ} (h0 : 0 ≤ α) (hαβ : α ≤ β) (h1 : β ≤ 1) :
    IntervalIntegrable phiZ volume α β :=
  (intervalIntegrable_iff_integrableOn_Icc_of_le hαβ).mpr (integrableOn_phiZ_of_subset h0 h1)

theorem intervalIntegrable_phiZ_mul {α β : ℝ} (h0 : 0 ≤ α) (hαβ : α ≤ β) (h1 : β ≤ 1) {g : ℝ → ℝ}
    (hg : Continuous g) : IntervalIntegrable (fun t => phiZ t * g t) volume α β :=
  (intervalIntegrable_phiZ h0 hαβ h1).mul_continuousOn hg.continuousOn

theorem zMeas_real_Iic (y : ℝ) : zMeas.real (Iic y) = zcdf y :=
  Cvs.Upstream.SliceMeasurePushforward.sliceMeas_real_Iic measurable_phiZ (by fun_prop) (fun t _ => phiZ_nonneg t)
    (fun _ _ => Real.sqrt_nonneg _) (fun t _ => phiZ_mul_sqrt_le t) zero_le_one y

theorem box_real_Iic {α β U : ℝ} (hβ : β < 1) (hα : 0 ≤ α) (hαβ : α ≤ β) (hU : 0 ≤ U) (y : ℝ) :
    (sliceMeas phiZ (fun _ => U) α β).real (Iic y) = boxcdf α β U y :=
  Cvs.Upstream.SliceMeasurePushforward.sliceMeas_real_Iic measurable_phiZ measurable_const (fun t _ => phiZ_nonneg t) (fun _ _ => hU)
    (M := 1 / (2 * π) * (1 / √(1 - β ^ 2)) * U)
    (fun _ ht => mul_le_mul_of_nonneg_right (phiZ_le hβ ⟨hα.trans ht.1, ht.2⟩) hU) hαβ y

/-! ### Capped increments -/

/-- Capped increments are nonnegative. -/
theorem capInc_nonneg {C x₁ x₂ : ℝ} (h : x₁ ≤ x₂) : 0 ≤ min C x₂ - min C x₁ := by
  have := min_le_min_left C h; linarith

/-- Capped increments are at most the increment. -/
theorem capInc_le {C x₁ x₂ : ℝ} (h : x₁ ≤ x₂) : min C x₂ - min C x₁ ≤ x₂ - x₁ := by
  rcases le_total C x₁ with h1 | h1
  · rw [min_eq_left h1, min_eq_left (h1.trans h)]; linarith
  · rw [min_eq_right h1]; linarith [min_le_right C x₂]

/-- Capped increments grow with the cap. -/
theorem capInc_mono {C C' x₁ x₂ : ℝ} (hC : C ≤ C') (h : x₁ ≤ x₂) :
    min C x₂ - min C x₁ ≤ min C' x₂ - min C' x₁ := by
  rcases le_total x₂ C with h2 | h2
  · rw [min_eq_right h2, min_eq_right (h.trans h2), min_eq_right (h2.trans hC), min_eq_right ((h.trans h2).trans hC)]
  · rw [min_eq_left h2]
    rcases le_total x₁ C with h1 | h1
    · rw [min_eq_right h1, min_eq_right (h1.trans hC)]
      have := le_min hC h2; linarith
    · rw [min_eq_left h1]
      have := capInc_nonneg (C := C') h; linarith

/-- Square-root increments shrink: `√(x + d) − √x ≤ √(x′ + d) − √x′` for `0 ≤ x′ ≤ x`, `0 ≤ d`. -/
theorem sqrt_inc_anti {x x' d : ℝ} (hx' : 0 ≤ x') (hxx : x' ≤ x) (hd : 0 ≤ d) :
    √(x + d) - √x ≤ √(x' + d) - √x' := by
  have hx : 0 ≤ x := hx'.trans hxx
  set A := √(x + d); set B := √x; set A' := √(x' + d); set B' := √x'
  have hA : A ^ 2 = x + d := Real.sq_sqrt (by linarith)
  have hB : B ^ 2 = x := Real.sq_sqrt hx
  have hA' : A' ^ 2 = x' + d := Real.sq_sqrt (by linarith)
  have hB' : B' ^ 2 = x' := Real.sq_sqrt hx'
  have hAA : A' ≤ A := Real.sqrt_le_sqrt (by linarith)
  have hBB : B' ≤ B := Real.sqrt_le_sqrt hxx
  have hBA : B ≤ A := Real.sqrt_le_sqrt (by linarith)
  have h0 : 0 ≤ B' := Real.sqrt_nonneg _
  have hBA' : B' ≤ A' := Real.sqrt_le_sqrt (by linarith)
  have key : (A - B) * (A + B) = (A' - B') * (A' + B') := by nlinarith
  rcases eq_or_lt_of_le (add_nonneg (h0.trans hBA') h0 : 0 ≤ A' + B') with h | h
  · have hA'0 : A' = 0 := by linarith [h0.trans hBA']
    have hd0 : d = 0 := by nlinarith
    have : A = B := by simp only [A, B, hd0, add_zero]
    linarith
  · nlinarith

/-- **Capped square-root increments shrink**: `h(x + d) − h(x) ≤ h(x′ + d) − h(x′)` for `h = min(U, √·)`. -/
theorem capSqrt_inc_anti {U x x' d : ℝ} (hx' : 0 ≤ x') (hxx : x' ≤ x) (hd : 0 ≤ d) :
    min U √(x + d) - min U √x ≤ min U √(x' + d) - min U √x' := by
  have hs := sqrt_inc_anti hx' hxx hd
  have h1 : √x' ≤ √x := Real.sqrt_le_sqrt hxx
  have h2 : √x ≤ √(x + d) := Real.sqrt_le_sqrt (by linarith)
  have h3 : √x' ≤ √(x' + d) := Real.sqrt_le_sqrt (by linarith)
  have h4 : √(x' + d) ≤ √(x + d) := Real.sqrt_le_sqrt (by linarith)
  rcases le_total U √x with hU | hU
  · rw [min_eq_left hU, min_eq_left (hU.trans h2), sub_self]
    exact capInc_nonneg h3
  · rw [min_eq_right hU]
    rcases le_total √(x + d) U with hU' | hU'
    · rw [min_eq_right hU', min_eq_right (h4.trans hU'), min_eq_right (h1.trans hU)]; exact hs
    · rw [min_eq_left hU', min_eq_right (h1.trans hU)]
      rcases le_total U √(x' + d) with hV | hV
      · rw [min_eq_left hV]; linarith
      · rw [min_eq_right hV]; linarith

/-! ### The Chebyshev comparison -/

section Cheb

variable {a U : ℝ}

theorem intervalIntegral_sub_mul {α β : ℝ} (h0 : 0 ≤ α) (hαβ : α ≤ β) (h1 : β ≤ 1) {g₁ g₂ : ℝ → ℝ}
    (hg₁ : Continuous g₁) (hg₂ : Continuous g₂) :
    (∫ t in α..β, phiZ t * g₂ t) - ∫ t in α..β, phiZ t * g₁ t = ∫ t in α..β, phiZ t * (g₂ t - g₁ t) := by
  rw [← intervalIntegral.integral_sub (intervalIntegrable_phiZ_mul h0 hαβ h1 hg₂)
    (intervalIntegrable_phiZ_mul h0 hαβ h1 hg₁)]
  congr 1; ext t; ring

/-- `Λ_a(v) = ∫_a^1 2φ(t)√(v − t²) dt`. -/
theorem dirWeyl_eq (a v : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    Cvs.Prolate.Gram.WeylCountsDiscretePotential.dirWeyl a v = ∫ t in a..1, 2 * (phiZ t * √(v - t ^ 2)) := by
  unfold Cvs.Prolate.Gram.WeylCountsDiscretePotential.dirWeyl
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [uIcc_of_le ha1] at ht
  rw [Real.sqrt_div' _ (by nlinarith [ht.1, ht.2] : (0 : ℝ) ≤ 1 - t ^ 2), phiZ]
  field_simp

/-- **Zero mass**: `∫_0^a φ = ∫_a^{t_e} φ`. -/
theorem integral_phiZ_eq (ha : a ∈ Icc (1 / 2 : ℝ) (3 / 5)) :
    ∫ t in (0 : ℝ)..a, phiZ t = ∫ t in a..tE a, phiZ t := by
  obtain ⟨h0, hat, hte, h2⟩ := tE_facts ha
  unfold phiZ
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    Cvs.Prolate.Gram.EquilibriumPotential.integral_inv_sqrt le_rfl h0 (hat.trans_lt hte), Cvs.Prolate.Gram.EquilibriumPotential.integral_inv_sqrt h0 hat hte,
    Cvs.Prolate.Gram.EquilibriumPotential.arcsin_tE h0 h2.le, Real.arcsin_zero]
  ring

theorem cont_capSqrt (C y : ℝ) : Continuous fun t : ℝ => min C √(y - t ^ 2) := by fun_prop

theorem cont_capSqrt' (y : ℝ) : Continuous fun t : ℝ => min √(1 - t ^ 2) √(y - t ^ 2) := by fun_prop

/-- **Increments below `Λ_a`**: `F(y₂) − F(y₁) ≤ Λ_a(y₂) − Λ_a(y₁)` for `y₁ ≤ y₂`, `U ≥ 1`. -/
theorem Fcdf_sub_le (ha : a ∈ Icc (1 / 2 : ℝ) (3 / 5)) (hU : 1 ≤ U) {y₁ y₂ : ℝ} (h : y₁ ≤ y₂) :
    Fcdf a U y₂ - Fcdf a U y₁ ≤ Cvs.Prolate.Gram.WeylCountsDiscretePotential.dirWeyl a y₂ - Cvs.Prolate.Gram.WeylCountsDiscretePotential.dirWeyl a y₁ := by
  obtain ⟨h0, hat, hte, -⟩ := tE_facts ha
  have ha1 : a ≤ 1 := hat.trans hte.le
  set ΔD : ℝ → ℝ := fun t => min √(1 - t ^ 2) √(y₂ - t ^ 2) - min √(1 - t ^ 2) √(y₁ - t ^ 2)
  set ΔU : ℝ → ℝ := fun t => min U √(y₂ - t ^ 2) - min U √(y₁ - t ^ 2)
  set Δ : ℝ → ℝ := fun t => √(y₂ - t ^ 2) - √(y₁ - t ^ 2)
  have cD : Continuous ΔD := (cont_capSqrt' y₂).sub (cont_capSqrt' y₁)
  have cU : Continuous ΔU := (cont_capSqrt U y₂).sub (cont_capSqrt U y₁)
  have cΔ : Continuous Δ := by fun_prop
  have hs : ∀ t, √(y₁ - t ^ 2) ≤ √(y₂ - t ^ 2) := fun t => Real.sqrt_le_sqrt (by linarith)
  have ez : zcdf y₂ - zcdf y₁ = (∫ t in (0 : ℝ)..a, phiZ t * ΔD t) + ∫ t in a..1, phiZ t * ΔD t := by
    unfold zcdf
    rw [intervalIntegral_sub_mul le_rfl zero_le_one le_rfl (cont_capSqrt' y₁) (cont_capSqrt' y₂),
      intervalIntegral.integral_add_adjacent_intervals (intervalIntegrable_phiZ_mul le_rfl h0 ha1 cD)
        (intervalIntegrable_phiZ_mul h0 ha1 le_rfl cD)]
  have ep : boxcdf a (tE a) U y₂ - boxcdf a (tE a) U y₁ = ∫ t in a..tE a, phiZ t * ΔU t :=
    intervalIntegral_sub_mul h0 hat hte.le (cont_capSqrt U y₁) (cont_capSqrt U y₂)
  have em : boxcdf 0 a U y₂ - boxcdf 0 a U y₁ = ∫ t in (0 : ℝ)..a, phiZ t * ΔU t :=
    intervalIntegral_sub_mul le_rfl h0 ha1 (cont_capSqrt U y₁) (cont_capSqrt U y₂)
  have ew : Cvs.Prolate.Gram.WeylCountsDiscretePotential.dirWeyl a y₂ - Cvs.Prolate.Gram.WeylCountsDiscretePotential.dirWeyl a y₁ = 2 * ∫ t in a..1, phiZ t * Δ t := by
    rw [dirWeyl_eq a y₂ h0 ha1, dirWeyl_eq a y₁ h0 ha1, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, ← mul_sub,
      intervalIntegral_sub_mul h0 ha1 le_rfl (by fun_prop) (by fun_prop)]
  have i1 : ∫ t in (0 : ℝ)..a, phiZ t * ΔD t ≤ ∫ t in (0 : ℝ)..a, phiZ t * ΔU t := by
    refine intervalIntegral.integral_mono_on h0 (intervalIntegrable_phiZ_mul le_rfl h0 ha1 cD)
      (intervalIntegrable_phiZ_mul le_rfl h0 ha1 cU) fun t ht => mul_le_mul_of_nonneg_left ?_ (phiZ_nonneg t)
    refine capInc_mono ((Real.sqrt_le_sqrt (by nlinarith : 1 - t ^ 2 ≤ 1)).trans (by simpa using hU)) (hs t)
  have i2 : ∫ t in a..1, phiZ t * ΔD t ≤ ∫ t in a..1, phiZ t * Δ t :=
    intervalIntegral.integral_mono_on ha1 (intervalIntegrable_phiZ_mul h0 ha1 le_rfl cD)
      (intervalIntegrable_phiZ_mul h0 ha1 le_rfl cΔ) fun t _ =>
      mul_le_mul_of_nonneg_left (capInc_le (hs t)) (phiZ_nonneg t)
  have i3 : ∫ t in a..tE a, phiZ t * ΔU t ≤ ∫ t in a..tE a, phiZ t * Δ t :=
    intervalIntegral.integral_mono_on hat (intervalIntegrable_phiZ_mul h0 hat hte.le cU)
      (intervalIntegrable_phiZ_mul h0 hat hte.le cΔ) fun t _ =>
      mul_le_mul_of_nonneg_left (capInc_le (hs t)) (phiZ_nonneg t)
  have i4 : ∫ t in a..tE a, phiZ t * Δ t ≤ ∫ t in a..1, phiZ t * Δ t :=
    intervalIntegral.integral_mono_interval le_rfl hat hte.le
      (Eventually.of_forall fun t => mul_nonneg (phiZ_nonneg t) (sub_nonneg.mpr (hs t)))
      (intervalIntegrable_phiZ_mul h0 ha1 le_rfl cΔ)
  have eF : Fcdf a U y₂ - Fcdf a U y₁ = (zcdf y₂ - zcdf y₁) + (boxcdf a (tE a) U y₂ - boxcdf a (tE a) U y₁) -
      (boxcdf 0 a U y₂ - boxcdf 0 a U y₁) := by unfold Fcdf; ring
  rw [eF, ez, ep, em, ew]
  linarith

/-- `F = 0` on `(−∞, 0]`. -/
theorem Fcdf_of_nonpos (hU : 0 ≤ U) {y : ℝ} (hy : y ≤ 0) : Fcdf a U y = 0 := by
  have h : ∀ t : ℝ, √(y - t ^ 2) = 0 := fun t => Real.sqrt_eq_zero_of_nonpos (by nlinarith [sq_nonneg t])
  unfold Fcdf zcdf boxcdf
  simp only [h, min_eq_right hU, min_eq_right (Real.sqrt_nonneg _), mul_zero, intervalIntegral.integral_zero]
  ring

/-- `F = 1/(2π)` on `[1 + U², ∞)`. -/
theorem Fcdf_of_ge (ha : a ∈ Icc (1 / 2 : ℝ) (3 / 5)) (hU : 0 ≤ U) {y : ℝ} (hy : 1 + U ^ 2 ≤ y) :
    Fcdf a U y = 1 / (2 * π) := by
  obtain ⟨h0, hat, hte, -⟩ := tE_facts ha
  have hz : zcdf y = 1 / (2 * π) := by
    unfold zcdf
    rw [intervalIntegral.integral_congr_ae (g := fun _ => 1 / (2 * π)) ?_]
    · simp
    · have hne : ∀ᵐ t ∂volume, t ≠ (1 : ℝ) := by rw [ae_iff]; simp
      filter_upwards [hne] with t h1 ht
      rw [uIoc_of_le zero_le_one] at ht
      have hm : min √(1 - t ^ 2) √(y - t ^ 2) = √(1 - t ^ 2) :=
        min_eq_left (Real.sqrt_le_sqrt (by nlinarith [sq_nonneg U]))
      have ht1 : t < 1 := lt_of_le_of_ne ht.2 h1
      rw [hm, phiZ, mul_assoc, one_div_mul_cancel (Real.sqrt_pos.mpr (by nlinarith [ht.1])).ne', mul_one]
  have hb : ∀ α β : ℝ, 0 ≤ α → α ≤ β → β ≤ 1 → boxcdf α β U y = U * ∫ t in α..β, phiZ t := by
    intro α β hα hαβ hβ
    unfold boxcdf
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le hαβ] at ht
    have : U ≤ √(y - t ^ 2) := by
      rw [← Real.sqrt_sq hU]; exact Real.sqrt_le_sqrt (by nlinarith [ht.1, ht.2])
    rw [min_eq_left this, mul_comm]
  unfold Fcdf
  rw [hz, hb a (tE a) h0 hat hte.le, hb 0 a le_rfl h0 (hat.trans hte.le), ← integral_phiZ_eq ha]
  ring

/-- `F` is nondecreasing below `1`. -/
theorem Fcdf_le_of_le_one (ha : a ∈ Icc (1 / 2 : ℝ) (3 / 5)) (hU : 1 ≤ U) {y₁ y₂ : ℝ} (h : y₁ ≤ y₂)
    (h2 : y₂ ≤ 1) : Fcdf a U y₁ ≤ Fcdf a U y₂ := by
  obtain ⟨h0, hat, hte, -⟩ := tE_facts ha
  have ha1 : a ≤ 1 := hat.trans hte.le
  set Δ : ℝ → ℝ := fun t => √(y₂ - t ^ 2) - √(y₁ - t ^ 2)
  have cΔ : Continuous Δ := by fun_prop
  have hs : ∀ t, √(y₁ - t ^ 2) ≤ √(y₂ - t ^ 2) := fun t => Real.sqrt_le_sqrt (by linarith)
  have hcap : ∀ C : ℝ, ∀ t, √(1 - t ^ 2) ≤ C → ∀ y ≤ y₂, min C √(y - t ^ 2) = √(y - t ^ 2) := fun C t hC y hy =>
    min_eq_right ((Real.sqrt_le_sqrt (by linarith)).trans hC)
  have hU1 : ∀ t, √(1 - t ^ 2) ≤ U := fun t =>
    (Real.sqrt_le_sqrt (by nlinarith [sq_nonneg t] : 1 - t ^ 2 ≤ 1)).trans (by simpa using hU)
  have ez : zcdf y₂ - zcdf y₁ = (∫ t in (0 : ℝ)..a, phiZ t * Δ t) + ∫ t in a..1, phiZ t * Δ t := by
    unfold zcdf
    rw [intervalIntegral_sub_mul le_rfl zero_le_one le_rfl (cont_capSqrt' y₁) (cont_capSqrt' y₂),
      intervalIntegral.integral_congr (g := fun t => phiZ t * Δ t) fun t _ => by
        simp only; rw [hcap _ t le_rfl y₂ le_rfl, hcap _ t le_rfl y₁ h],
      intervalIntegral.integral_add_adjacent_intervals (intervalIntegrable_phiZ_mul le_rfl h0 ha1 cΔ)
        (intervalIntegrable_phiZ_mul h0 ha1 le_rfl cΔ)]
  have ebox : ∀ α β : ℝ, 0 ≤ α → α ≤ β → β ≤ 1 →
      boxcdf α β U y₂ - boxcdf α β U y₁ = ∫ t in α..β, phiZ t * Δ t := fun α β hα hαβ hβ => by
    unfold boxcdf
    rw [intervalIntegral_sub_mul hα hαβ hβ (cont_capSqrt U y₁) (cont_capSqrt U y₂)]
    exact intervalIntegral.integral_congr fun t _ => by
      rw [hcap _ t (hU1 t) y₂ le_rfl, hcap _ t (hU1 t) y₁ h]
  have hp : 0 ≤ ∫ t in a..tE a, phiZ t * Δ t :=
    intervalIntegral.integral_nonneg hat fun t _ => mul_nonneg (phiZ_nonneg t) (sub_nonneg.mpr (hs t))
  have hq : 0 ≤ ∫ t in a..1, phiZ t * Δ t :=
    intervalIntegral.integral_nonneg ha1 fun t _ => mul_nonneg (phiZ_nonneg t) (sub_nonneg.mpr (hs t))
  have eF : Fcdf a U y₂ - Fcdf a U y₁ = (zcdf y₂ - zcdf y₁) + (boxcdf a (tE a) U y₂ - boxcdf a (tE a) U y₁) -
      (boxcdf 0 a U y₂ - boxcdf 0 a U y₁) := by unfold Fcdf; ring
  rw [ebox a (tE a) h0 hat hte.le, ebox 0 a le_rfl h0 ha1, ez] at eF
  linarith

/-- `F` is nondecreasing above `1` (Chebyshev with `∫_0^a φ = ∫_a^{t_e} φ`). -/
theorem Fcdf_le_of_one_le (ha : a ∈ Icc (1 / 2 : ℝ) (3 / 5)) {y₁ y₂ : ℝ} (h : y₁ ≤ y₂)
    (h1 : 1 ≤ y₁) : Fcdf a U y₁ ≤ Fcdf a U y₂ := by
  obtain ⟨h0, hat, hte, -⟩ := tE_facts ha
  have ha1 : a ≤ 1 := hat.trans hte.le
  set ΔU : ℝ → ℝ := fun t => min U √(y₂ - t ^ 2) - min U √(y₁ - t ^ 2)
  have cU : Continuous ΔU := (cont_capSqrt U y₂).sub (cont_capSqrt U y₁)
  have hz : zcdf y₂ = zcdf y₁ := by
    unfold zcdf
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le zero_le_one] at ht
    have hm : ∀ y, 1 ≤ y → min √(1 - t ^ 2) √(y - t ^ 2) = √(1 - t ^ 2) := fun y hy =>
      min_eq_left (Real.sqrt_le_sqrt (by linarith))
    rw [hm y₂ (h1.trans h), hm y₁ h1]
  -- the monotone increment
  have hmono : ∀ t t', 0 ≤ t → t ≤ t' → t' ≤ tE a → ΔU t ≤ ΔU t' := fun t t' ht htt ht' => by
    have hx' : 0 ≤ y₁ - t' ^ 2 := by nlinarith
    have := capSqrt_inc_anti (U := U) hx' (by nlinarith : y₁ - t' ^ 2 ≤ y₁ - t ^ 2) (by linarith : 0 ≤ y₂ - y₁)
    simp only [ΔU]
    have e1 : y₁ - t ^ 2 + (y₂ - y₁) = y₂ - t ^ 2 := by ring
    have e2 : y₁ - t' ^ 2 + (y₂ - y₁) = y₂ - t' ^ 2 := by ring
    rwa [e1, e2] at this
  have i1 : ∫ t in (0 : ℝ)..a, phiZ t * ΔU t ≤ ∫ t in (0 : ℝ)..a, phiZ t * ΔU a :=
    intervalIntegral.integral_mono_on h0 (intervalIntegrable_phiZ_mul le_rfl h0 ha1 cU)
      (intervalIntegrable_phiZ_mul le_rfl h0 ha1 continuous_const) fun t ht =>
      mul_le_mul_of_nonneg_left (hmono t a ht.1 ht.2 hat) (phiZ_nonneg t)
  have i2 : ∫ t in a..tE a, phiZ t * ΔU a ≤ ∫ t in a..tE a, phiZ t * ΔU t :=
    intervalIntegral.integral_mono_on hat (intervalIntegrable_phiZ_mul h0 hat hte.le continuous_const)
      (intervalIntegrable_phiZ_mul h0 hat hte.le cU) fun t ht =>
      mul_le_mul_of_nonneg_left (hmono a t h0 ht.1 ht.2) (phiZ_nonneg t)
  have i3 : ∫ t in (0 : ℝ)..a, phiZ t * ΔU a = ∫ t in a..tE a, phiZ t * ΔU a := by
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const, integral_phiZ_eq ha]
  have ep : boxcdf a (tE a) U y₂ - boxcdf a (tE a) U y₁ = ∫ t in a..tE a, phiZ t * ΔU t :=
    intervalIntegral_sub_mul h0 hat hte.le (cont_capSqrt U y₁) (cont_capSqrt U y₂)
  have em : boxcdf 0 a U y₂ - boxcdf 0 a U y₁ = ∫ t in (0 : ℝ)..a, phiZ t * ΔU t :=
    intervalIntegral_sub_mul le_rfl h0 ha1 (cont_capSqrt U y₁) (cont_capSqrt U y₂)
  have eF : Fcdf a U y₂ - Fcdf a U y₁ = (zcdf y₂ - zcdf y₁) + (boxcdf a (tE a) U y₂ - boxcdf a (tE a) U y₁) -
      (boxcdf 0 a U y₂ - boxcdf 0 a U y₁) := by unfold Fcdf; ring
  rw [ep, em, hz, sub_self, zero_add] at eF
  linarith

/-- **`F` is nondecreasing** for `U ≥ 1`. -/
theorem Fcdf_mono (ha : a ∈ Icc (1 / 2 : ℝ) (3 / 5)) (hU : 1 ≤ U) : Monotone (Fcdf a U) := by
  intro y₁ y₂ h
  rcases le_total y₂ 1 with h2 | h2
  · exact Fcdf_le_of_le_one ha hU h h2
  rcases le_total 1 y₁ with h1 | h1
  · exact Fcdf_le_of_one_le ha h h1
  · exact (Fcdf_le_of_le_one ha hU h1 le_rfl).trans (Fcdf_le_of_one_le ha h2 le_rfl)

/-! ### The target measure `ν′` -/

/-- `∫_0^1 φ = 1/4`. -/
theorem integral_phiZ_zero_one : ∫ t in (0 : ℝ)..1, phiZ t = 1 / 4 := by
  unfold phiZ
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one
    Real.continuous_arcsin.continuousOn (fun t ht => Cvs.Prolate.Gram.EquilibriumPotential.hasDerivAt_arcsin' (by nlinarith [ht.1, ht.2]))
    ((intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mpr integrableOn_inv_sqrt),
    Real.arcsin_one, Real.arcsin_zero]
  field_simp; ring

/-- `∫_a^{t_e} φ ≤ 1/4`. -/
theorem integral_phiZ_le (ha : a ∈ Icc (1 / 2 : ℝ) (3 / 5)) : ∫ t in a..tE a, phiZ t ≤ 1 / 4 := by
  obtain ⟨h0, hat, hte, -⟩ := tE_facts ha
  rw [← integral_phiZ_zero_one]
  exact intervalIntegral.integral_mono_interval h0 hat hte.le (Eventually.of_forall phiZ_nonneg)
    (intervalIntegrable_phiZ le_rfl zero_le_one le_rfl)

/-- **The target measure**: for `a ∈ [½, 3/5]`, `U ≥ 1` there is a finite `ν′` with `ν′ + μ⁻ = z + μ⁺` and
`ν′(−∞, y] = F(y)`. -/
theorem exists_nu (ha : a ∈ Icc (1 / 2 : ℝ) (3 / 5)) (hU : 1 ≤ U) :
    ∃ ν : Measure ℝ, IsFiniteMeasure ν ∧ ν + muM a U = zMeas + muP a U ∧ (∀ y, ν.real (Iic y) = Fcdf a U y) ∧
      ν ≤ zMeas + muP a U := by
  have : Fact (a ∈ Icc (1 / 2 : ℝ) (3 / 5)) := ⟨ha⟩
  obtain ⟨h0, hat, hte, -⟩ := tE_facts ha
  have hU0 : (0 : ℝ) ≤ U := by linarith
  have : IsFiniteMeasure (sliceMeas phiZ (fun t => √(1 - t ^ 2)) 0 1) := (inferInstance : IsFiniteMeasure zMeas)
  have : IsFiniteMeasure (sliceMeas phiZ (fun _ => U) a (tE a)) := (inferInstance : IsFiniteMeasure (muP a U))
  have : IsFiniteMeasure (sliceMeas phiZ (fun _ => U) 0 a) := (inferInstance : IsFiniteMeasure (muM a U))
  have hF : (fun y => (zMeas + muP a U).real (Iic y) - (muM a U).real (Iic y)) = Fcdf a U := by
    ext y
    rw [measureReal_add_apply, zMeas_real_Iic, muP, muM, box_real_Iic hte h0 hat hU0,
      box_real_Iic (hat.trans_lt hte) le_rfl h0 hU0]
    rfl
  have hcz := continuous_sliceMeas_real_Iic (φ := phiZ) (L := fun t => √(1 - t ^ 2)) (α := 0) (β := 1)
    measurable_phiZ (by fun_prop) (fun t _ => phiZ_nonneg t) integrableOn_phiZ zero_le_one
  have hcp := continuous_sliceMeas_real_Iic (φ := phiZ) (L := fun _ => U) (α := a) (β := tE a)
    measurable_phiZ measurable_const (fun t _ => phiZ_nonneg t) (integrableOn_phiZ_of_subset h0 hte.le) hat
  have hcm := continuous_sliceMeas_real_Iic (φ := phiZ) (L := fun _ => U) (α := 0) (β := a)
    measurable_phiZ measurable_const (fun t _ => phiZ_nonneg t) (integrableOn_phiZ_of_subset le_rfl
    (hat.trans hte.le)) h0
  have hcont : Continuous fun y => (zMeas + muP a U).real (Iic y) - (muM a U).real (Iic y) := by
    have e : (fun y => (zMeas + muP a U).real (Iic y) - (muM a U).real (Iic y)) =
        fun y => zMeas.real (Iic y) + (muP a U).real (Iic y) - (muM a U).real (Iic y) := by
      ext y; rw [measureReal_add_apply]
    rw [e]; exact (hcz.add hcp).sub hcm
  have hbot : Tendsto (fun y => (zMeas + muP a U).real (Iic y) - (muM a U).real (Iic y)) atBot (𝓝 0) := by
    rw [hF]
    exact tendsto_const_nhds.congr' (Filter.eventually_atBot.2 ⟨0, fun y hy => (Fcdf_of_nonpos hU0 hy).symm⟩)
  obtain ⟨ν, hfin, hadd, hIic⟩ := exists_add_eq (by rw [hF]; exact Fcdf_mono ha hU) hcont hbot
  refine ⟨ν, hfin, hadd, fun y => by rw [hIic y]; exact congrFun hF y, ?_⟩
  rw [← hadd]; exact Measure.le_add_right le_rfl

end Cheb
/-! ### The local inputs of Cvs.Upstream.DiscreteContinuousLogPotential for `z + μ⁺` and every measure below it -/

/-- The local inputs of Cvs.Upstream.DiscreteContinuousLogPotential on a measure: support in `[0, B]`, no atoms, `ν(y − r, y + r) ≤ 2√r`, integrable log
potentials and `∫(log max(|y − v|, r) − log|y − v|) dν ≤ 2√r`. -/
structure LocalInputs (ν : Measure ℝ) (B : ℝ) : Prop where
  supp : ν (Icc 0 B)ᶜ = 0
  atom : ∀ y, ν {y} = 0
  ball : ∀ y r, 0 ≤ r → ν.real (Ioo (y - r) (y + r)) ≤ 2 * √r
  intLog : ∀ y, Integrable (fun v => log |y - v|) ν
  loc : ∀ y r, 0 < r → r ≤ 1 → ∫ v, (Cvs.Upstream.DiscreteContinuousLogPotential.logTr y r v - log |y - v|) ∂ν ≤ 2 * √r

theorem integrable_logTr_sub {ν : Measure ℝ} [IsFiniteMeasure ν] {B : ℝ} (hB : 1 ≤ B) (hsupp : ν (Icc 0 B)ᶜ = 0)
    (y : ℝ) (hint : Integrable (fun v => log |y - v|) ν) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    Integrable (fun v => Cvs.Upstream.DiscreteContinuousLogPotential.logTr y r v - log |y - v|) ν := by
  refine Integrable.sub ?_ hint
  have hνae : ∀ᵐ v ∂ν, v ∈ Icc 0 B := by rw [ae_iff]; simpa [compl_def] using hsupp
  refine Integrable.of_bound (Cvs.Upstream.DiscreteContinuousLogPotential.measurable_logTr y r).aestronglyMeasurable (|log r| + log (|y| + B))
    (hνae.mono fun v hv => ?_)
  have h1 := Cvs.Upstream.DiscreteContinuousLogPotential.log_le_logTr (y := y) (v := v) hr
  have hm : max |y - v| r ≤ |y| + B := max_le (by
    rw [abs_le]; constructor <;> linarith [abs_nonneg y, le_abs_self y, neg_abs_le y, hv.1, hv.2]) (by
    linarith [abs_nonneg y])
  have h2 := Real.log_le_log (lt_max_of_lt_right hr) hm
  have h3 : 0 ≤ log (|y| + B) := Real.log_nonneg (by linarith [abs_nonneg y])
  rw [Real.norm_eq_abs, abs_le]
  change log r ≤ log (max |y - v| r) at h1
  change -(|log r| + log (|y| + B)) ≤ log (max |y - v| r) ∧ log (max |y - v| r) ≤ |log r| + log (|y| + B)
  constructor <;> linarith [neg_abs_le (log r), le_abs_self (log r)]

/-- **Local inputs pass to smaller measures.** -/
theorem LocalInputs.mono {ν ζ : Measure ℝ} [IsFiniteMeasure ζ] {B : ℝ} (hB : 1 ≤ B) (h : LocalInputs ζ B)
    (hνζ : ν ≤ ζ) : LocalInputs ν B := by
  have : IsFiniteMeasure ν := isFiniteMeasure_of_le ζ hνζ
  refine ⟨nonpos_iff_eq_zero.mp ((hνζ _).trans_eq h.supp), fun y => nonpos_iff_eq_zero.mp
    ((hνζ _).trans_eq (h.atom y)), fun y r hr => ?_, fun y => (h.intLog y).mono_measure hνζ, fun y r hr hr1 => ?_⟩
  · exact (ENNReal.toReal_mono (measure_ne_top ζ _) (hνζ _)).trans (h.ball y r hr)
  · refine (integral_mono_measure hνζ ?_ (integrable_logTr_sub hB h.supp y (h.intLog y) hr hr1)).trans
      (h.loc y r hr hr1)
    have hne : ∀ᵐ v ∂ζ, v ≠ y := by rw [ae_iff]; simpa using h.atom y
    exact hne.mono fun v hv => Cvs.Upstream.SliceMeasurePushforward.kap_nonneg (sub_ne_zero.mpr hv.symm)

/-- **The local inputs for `z + μ⁺`** on `[0, 1 + U²]`. -/
theorem localInputs_zeta {a : ℝ} (ha : a ∈ Icc (1 / 2 : ℝ) (3 / 5)) (U : ℝ) :
    LocalInputs (zMeas + muP a U) (1 + U ^ 2) := by
  have : Fact (a ∈ Icc (1 / 2 : ℝ) (3 / 5)) := ⟨ha⟩
  obtain ⟨h0, hat, hte, -⟩ := tE_facts ha
  have : IsFiniteMeasure (sliceMeas phiZ (fun t => √(1 - t ^ 2)) 0 1) := (inferInstance : IsFiniteMeasure zMeas)
  have : IsFiniteMeasure (sliceMeas phiZ (fun _ => U) a (tE a)) := (inferInstance : IsFiniteMeasure (muP a U))
  have hz1 : IntegrableOn phiZ (Icc 0 1) := integrableOn_phiZ
  have hp1 : IntegrableOn phiZ (Icc a (tE a)) := integrableOn_phiZ_of_subset h0 hte.le
  have Iz := integral_phiZ_zero_one
  have Ip := integral_phiZ_le ha
  have Ip0 : 0 ≤ ∫ t in a..tE a, phiZ t := intervalIntegral.integral_nonneg hat fun t _ => phiZ_nonneg t
  have hsz : zMeas (Icc 0 (1 + U ^ 2))ᶜ = 0 := Cvs.Upstream.SliceMeasurePushforward.sliceMeas_compl measurable_phiZ (by fun_prop) fun t ht => by
    rw [Real.sq_sqrt (by nlinarith [ht.1, ht.2])]; nlinarith [sq_nonneg U]
  have hsp : muP a U (Icc 0 (1 + U ^ 2))ᶜ = 0 := Cvs.Upstream.SliceMeasurePushforward.sliceMeas_compl measurable_phiZ measurable_const
    fun t ht => by nlinarith [ht.1, ht.2]
  refine ⟨by rw [add_apply, hsz, hsp, add_zero], fun y => ?_, fun y r hr => ?_, fun y => ?_,
    fun y r hr hr1 => ?_⟩
  · rw [add_apply, zMeas, muP, Cvs.Upstream.SliceMeasurePushforward.sliceMeas_singleton measurable_phiZ (by fun_prop),
      Cvs.Upstream.SliceMeasurePushforward.sliceMeas_singleton measurable_phiZ measurable_const, add_zero]
  · rw [measureReal_add_apply]
    have h1 := Cvs.Upstream.SliceMeasurePushforward.sliceMeas_real_Ioo_le (L := fun t => √(1 - t ^ 2)) measurable_phiZ (by fun_prop)
      (fun t _ => phiZ_nonneg t) hz1 zero_le_one hr y
    have h2 := Cvs.Upstream.SliceMeasurePushforward.sliceMeas_real_Ioo_le (L := fun _ => U) measurable_phiZ measurable_const
      (fun t _ => phiZ_nonneg t) hp1 hat hr y
    rw [Iz] at h1
    have hs2 : √2 ≤ 2 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
    have hr0 := Real.sqrt_nonneg r
    simp only [zMeas, muP] at h1 h2 ⊢
    nlinarith [mul_le_mul_of_nonneg_left Ip (Real.sqrt_nonneg 2), mul_nonneg (Real.sqrt_nonneg 2) Ip0]
  · exact (Cvs.Upstream.SliceMeasurePushforward.integrable_log_sliceMeas measurable_phiZ (by fun_prop) (fun t _ => phiZ_nonneg t) hz1 hsz
      y).add_measure
      (Cvs.Upstream.SliceMeasurePushforward.integrable_log_sliceMeas measurable_phiZ measurable_const (fun t _ => phiZ_nonneg t) hp1 hsp y)
  · have hB : (1 : ℝ) ≤ 1 + U ^ 2 := by nlinarith [sq_nonneg U]
    have hiz := Cvs.Upstream.SliceMeasurePushforward.integrable_log_sliceMeas measurable_phiZ (by fun_prop) (fun t _ => phiZ_nonneg t) hz1 hsz y
    have hip := Cvs.Upstream.SliceMeasurePushforward.integrable_log_sliceMeas measurable_phiZ measurable_const (fun t _ => phiZ_nonneg t) hp1 hsp y
    rw [integral_add_measure (integrable_logTr_sub hB hsz y hiz hr hr1) (integrable_logTr_sub hB hsp y hip hr hr1)]
    have h1 := Cvs.Upstream.SliceMeasurePushforward.integral_logTr_sub_le (L := fun t => √(1 - t ^ 2)) measurable_phiZ (by fun_prop)
      (fun t _ => phiZ_nonneg t) hz1 zero_le_one hr y
    have h2 := Cvs.Upstream.SliceMeasurePushforward.integral_logTr_sub_le (L := fun _ => U) measurable_phiZ measurable_const
      (fun t _ => phiZ_nonneg t) hp1 hat hr y
    rw [Iz] at h1
    simp only [zMeas, muP] at h1 h2 ⊢
    nlinarith [mul_le_mul_of_nonneg_right Ip (Real.sqrt_nonneg r), mul_nonneg Ip0 (Real.sqrt_nonneg r)]

/-- Local inputs persist on a larger support interval. -/
theorem LocalInputs.mono_right {ν : Measure ℝ} {B B' : ℝ} (h : LocalInputs ν B) (hBB : B ≤ B') : LocalInputs ν B' :=
  ⟨measure_mono_null (compl_subset_compl.mpr (Icc_subset_Icc le_rfl hBB)) h.supp, h.atom, h.ball, h.intLog, h.loc⟩

end Cvs.Prolate.Gram.SelectionTargetMeasure

end
