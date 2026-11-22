import Mathlib
import Cvs.Finite.CoshMomentRecentred
import Cvs.L2a.FullTailPolarisation
import Cvs.WeilForm.BandFreedomCosine
import Cvs.WeilForm.EffectiveSymbol
import Cvs.WeilForm.SeparatedArchDilationPairing
import Cvs.WeilForm.TruncatedFormPolarised
import Cvs.Zeta.PrimePowerSideTruncated

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The pole and prime channels of the window form as cosine multipliers

The pole kernel `2cosh(v/2) dv` on `(−L, L]` and the prime atoms `w(p,r)(δ_{r log p} + δ_{−r log p})` are finite
measures with cosine transforms `poleSymbol L t = (8 sinh(L/2) cos(Lt) + 16t cosh(L/2) sin(Lt))/(1 + 4t²)` and
`primeSymbol P R`; against `ρ_{f,g}` they give `poleF f poleG g + poleF g poleG f` (for `f, g` vanishing off
`[a, b]`, `b − a ≤ L`) and `½ PPS(polar f g)`. `poleSymbol L' − poleSymbol L` is band-free at `L ≤ L'`.
-/

noncomputable section

open Real Set Filter MeasureTheory Cvs.Zeta.Explicit.Weil
open scoped NNReal ENNReal
open Cvs.L2a.FullTailPolarisation (crossSpec)
open Cvs.WeilForm.TruncatedFormPolarised (polar crossConv poleF poleG)

namespace Cvs.WeilForm.PolePrimeCosineMultipliers
open Cvs.ZeroCounting

variable {f g : ℝ → ℝ}

/-! ### The pole products as a kernel against the cross-convolution -/

/-- `f e^{c·}` is integrable for integrable `f` vanishing off `[a, b]`. -/
theorem integrable_mul_exp {a b : ℝ} (hf : Integrable f) (hfs : ∀ x ∉ Icc a b, f x = 0) (c : ℝ) :
    Integrable fun x => f x * Real.exp (c * x) := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
    (by fun_prop : Continuous fun x : ℝ => Real.exp (c * x)).continuousOn
  have h := hf.bdd_mul (c := max M 0)
    ((by fun_prop : Continuous fun x : ℝ => Real.exp (c * x)).aestronglyMeasurable.indicator
      (measurableSet_Icc (a := a) (b := b)))
    (Eventually.of_forall fun x => by
      by_cases hx : x ∈ Icc a b
      · rw [indicator_of_mem hx]; exact (hM x hx).trans (le_max_left _ _)
      · rw [indicator_of_notMem hx, norm_zero]; exact le_max_right _ _)
  refine h.congr (Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ Icc a b
  · simp only [indicator_of_mem hx]; ring
  · simp only [indicator_of_notMem hx, hfs x hx]; ring

/-- **The pole products as a kernel**: `(∫ f e^{c·})(∫ g e^{−c·}) = ∫ e^{−cv} (f ⋆ g̃)(v) dv` when both weighted
functions are integrable. -/
theorem integral_mul_exp_mul_integral (c : ℝ) (hF : Integrable fun x => f x * Real.exp (c * x))
    (hG : Integrable fun x => g x * Real.exp (-(c * x))) :
    (∫ x, f x * Real.exp (c * x)) * (∫ x, g x * Real.exp (-(c * x)))
      = ∫ v, Real.exp (-(c * v)) * crossConv f g v := by
  set F : ℝ → ℝ := fun x => f x * Real.exp (c * x) with hFdef
  set G : ℝ → ℝ := fun x => g x * Real.exp (-(c * x)) with hGdef
  have hj : Integrable (fun p : ℝ × ℝ => F p.1 * G (p.1 + p.2)) ((volume : Measure ℝ).prod volume) :=
    (measurePreserving_prod_add volume volume).integrable_comp_of_integrable (hF.mul_prod hG)
  calc (∫ x, F x) * (∫ x, G x) = ∫ x, ∫ v, F x * G (x + v) := by
        rw [← integral_mul_const]
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        dsimp only
        rw [← integral_const_mul]
        exact (integral_add_left_eq_self (fun y => F x * G y) x).symm
    _ = ∫ v, ∫ x, F x * G (x + v) := integral_integral_swap (f := fun x v => F x * G (x + v)) hj
    _ = ∫ v, Real.exp (-(c * v)) * crossConv f g v := by
        refine integral_congr_ae (Eventually.of_forall fun v => ?_)
        dsimp only
        rw [crossConv, ← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        simp only [hFdef, hGdef]
        rw [show -(c * (x + v)) = -(c * v) - c * x by ring, Real.exp_sub]
        field_simp

/-- `v ↦ e^{−cv} (f ⋆ g̃)(v)` is integrable when both weighted functions are. -/
theorem integrable_exp_mul_crossConv (c : ℝ) (hF : Integrable fun x => f x * Real.exp (c * x))
    (hG : Integrable fun x => g x * Real.exp (-(c * x))) :
    Integrable fun v => Real.exp (-(c * v)) * crossConv f g v := by
  have hj : Integrable (fun p : ℝ × ℝ => (fun x => f x * Real.exp (c * x)) p.1
      * (fun x => g x * Real.exp (-(c * x))) (p.1 + p.2)) ((volume : Measure ℝ).prod volume) :=
    (measurePreserving_prod_add volume volume).integrable_comp_of_integrable (hF.mul_prod hG)
  refine hj.integral_prod_right.congr (Eventually.of_forall fun v => ?_)
  dsimp only
  rw [crossConv, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  dsimp only
  rw [show -(c * (x + v)) = -(c * v) - c * x by ring, Real.exp_sub]
  field_simp

/-- `poleF f poleG g + poleF g poleG f = ∫ 2cosh(v/2) (f ⋆ g̃)(v) dv` for integrable `f, g` vanishing off
`[a, b]`. -/
theorem pole_eq_integral_cosh_mul_crossConv {a b : ℝ} (hf : Integrable f) (hg : Integrable g)
    (hfs : ∀ x ∉ Icc a b, f x = 0) (hgs : ∀ x ∉ Icc a b, g x = 0) :
    poleF f * poleG g + poleF g * poleG f = ∫ v, 2 * Real.cosh (v / 2) * crossConv f g v := by
  have e1 : ∀ x : ℝ, x / 2 = 1 / 2 * x := fun x => by ring
  have e2 : ∀ x : ℝ, -(x / 2) = -(1 / 2) * x := fun x => by ring
  have e3 : ∀ x : ℝ, x / 2 = -(-(1 / 2) * x) := fun x => by ring
  have hFp : poleF f = ∫ x, f x * Real.exp (1 / 2 * x) :=
    integral_congr_ae (Eventually.of_forall fun x => by simp only; rw [e1])
  have hGp : poleG g = ∫ x, g x * Real.exp (-(1 / 2 * x)) :=
    integral_congr_ae (Eventually.of_forall fun x => by simp only; rw [e1])
  have hFm : poleG f = ∫ x, f x * Real.exp (-(1 / 2) * x) :=
    integral_congr_ae (Eventually.of_forall fun x => by simp only; rw [e2])
  have hGm : poleF g = ∫ x, g x * Real.exp (-(-(1 / 2) * x)) :=
    integral_congr_ae (Eventually.of_forall fun x => by simp only; rw [e3])
  have i1 := integrable_mul_exp hf hfs (1 / 2)
  have i2 : Integrable fun x => g x * Real.exp (-(1 / 2 * x)) :=
    (integrable_mul_exp hg hgs (-(1 / 2))).congr (Eventually.of_forall fun x => by simp only; ring_nf)
  have i3 := integrable_mul_exp hf hfs (-(1 / 2))
  have i4 : Integrable fun x => g x * Real.exp (-(-(1 / 2) * x)) :=
    (integrable_mul_exp hg hgs (1 / 2)).congr (Eventually.of_forall fun x => by simp only; ring_nf)
  rw [mul_comm (poleF g), hFp, hGp, hFm, hGm, integral_mul_exp_mul_integral _ i1 i2,
    integral_mul_exp_mul_integral _ i3 i4,
    ← integral_add (integrable_exp_mul_crossConv _ i1 i2) (integrable_exp_mul_crossConv _ i3 i4)]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  dsimp only
  rw [Real.cosh_eq, show -(-(1 / 2) * v) = v / 2 by ring, show -(1 / 2 * v) = -(v / 2) by ring]
  ring

/-- `v ↦ cosh(v/2) (f ⋆ g̃)(v)` is integrable for integrable `f, g` vanishing off `[a, b]`. -/
theorem integrable_cosh_mul_crossConv {a b : ℝ} (hf : Integrable f) (hg : Integrable g)
    (hfs : ∀ x ∉ Icc a b, f x = 0) (hgs : ∀ x ∉ Icc a b, g x = 0) :
    Integrable fun v => Real.cosh (v / 2) * crossConv f g v := by
  have i1 := integrable_exp_mul_crossConv (1 / 2) (integrable_mul_exp hf hfs (1 / 2))
    ((integrable_mul_exp hg hgs (-(1 / 2))).congr (Eventually.of_forall fun x => by simp only; ring_nf))
  have i2 := integrable_exp_mul_crossConv (-(1 / 2)) (integrable_mul_exp hf hfs (-(1 / 2)))
    ((integrable_mul_exp hg hgs (1 / 2)).congr (Eventually.of_forall fun x => by simp only; ring_nf))
  refine ((i1.add i2).div_const 2).congr (Eventually.of_forall fun v => ?_)
  simp only [Pi.add_apply]
  rw [Real.cosh_eq, show -(-(1 / 2) * v) = v / 2 by ring, show -(1 / 2 * v) = -(v / 2) by ring]
  ring

/-- **The pole channel on the cross-convolution**: `poleF f poleG g + poleF g poleG f = ∫ cosh(v/2) polar f g v`
for integrable `f, g` vanishing off `[a, b]`. -/
theorem pole_eq_integral_cosh_mul_polar {a b : ℝ} (hf : Integrable f) (hg : Integrable g)
    (hfs : ∀ x ∉ Icc a b, f x = 0) (hgs : ∀ x ∉ Icc a b, g x = 0) :
    poleF f * poleG g + poleF g * poleG f = ∫ v, Real.cosh (v / 2) * polar f g v := by
  have h1 := pole_eq_integral_cosh_mul_crossConv hf hg hfs hgs
  have h2 := pole_eq_integral_cosh_mul_crossConv hg hf hgs hfs
  simp only [mul_assoc, integral_const_mul] at h1 h2
  rw [show (fun v => Real.cosh (v / 2) * polar f g v)
      = fun v => Real.cosh (v / 2) * crossConv f g v + Real.cosh (v / 2) * crossConv g f v from
      funext fun v => by simp only [polar]; ring,
    integral_add (integrable_cosh_mul_crossConv hf hg hfs hgs) (integrable_cosh_mul_crossConv hg hf hgs hfs)]
  linarith

/-! ### The pole measure and its cosine transform -/

/-- **The pole measure** `2cosh(v/2) dv` on `(a, b]`. -/
def poleMeasure (a b : ℝ) : Measure ℝ :=
  (volume.restrict (Ioc a b)).withDensity fun v => ENNReal.ofReal (2 * Real.cosh (v / 2))

instance (a b : ℝ) : IsFiniteMeasure (poleMeasure a b) :=
  isFiniteMeasure_withDensity_ofReal
    (((by fun_prop : Continuous fun v : ℝ => 2 * Real.cosh (v / 2)).integrableOn_Icc
      (a := a) (b := b)).mono_set Ioc_subset_Icc_self).2

/-- `∫ h d(poleMeasure a b) = ∫_{(a, b]} 2cosh(v/2) h(v) dv`. -/
theorem integral_poleMeasure (a b : ℝ) (h : ℝ → ℝ) :
    ∫ v, h v ∂poleMeasure a b = ∫ v in Ioc a b, 2 * Real.cosh (v / 2) * h v := by
  have hm : Measurable fun v : ℝ => (2 * Real.cosh (v / 2)).toNNReal :=
    (by fun_prop : Continuous fun v : ℝ => 2 * Real.cosh (v / 2)).measurable.real_toNNReal
  rw [poleMeasure, show (fun v : ℝ => ENNReal.ofReal (2 * Real.cosh (v / 2)))
      = fun v => (((2 * Real.cosh (v / 2)).toNNReal : ℝ≥0) : ℝ≥0∞) from rfl,
    integral_withDensity_eq_integral_smul hm]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (by positivity : (0 : ℝ) ≤ 2 * Real.cosh (v / 2))]

/-- The cosine transform of `poleMeasure a b` is `∫_a^b 2cosh(v/2) cos(tv) dv` for `a ≤ b`. -/
theorem integral_cos_poleMeasure {a b : ℝ} (hab : a ≤ b) (t : ℝ) :
    ∫ v, Real.cos (t * v) ∂poleMeasure a b = ∫ v in a..b, 2 * Real.cosh (v / 2) * Real.cos (t * v) := by
  rw [integral_poleMeasure, intervalIntegral.integral_of_le hab]

/-- **The pole symbol** `(8 sinh(L/2) cos(Lt) + 16t cosh(L/2) sin(Lt))/(1 + 4t²)`. -/
def poleSymbol (L t : ℝ) : ℝ :=
  (8 * Real.sinh (L / 2) * Real.cos (L * t) + 16 * t * Real.cosh (L / 2) * Real.sin (L * t)) / (1 + 4 * t ^ 2)

/-- **The pole symbol is the cosine transform of the pole kernel**:
`poleSymbol L t = ∫_{−L}^{L} 2cosh(v/2) cos(tv) dv`. -/
theorem poleSymbol_eq_intervalIntegral (L t : ℝ) :
    poleSymbol L t = ∫ v in (-L)..L, 2 * Real.cosh (v / 2) * Real.cos (t * v) := by
  have e : (∫ v in (-L)..L, 2 * Real.cosh (v / 2) * Real.cos (t * v))
      = 2 * ∫ v in (-L)..L, Real.cosh (1 / 2 * v) * Real.cos (t * v) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun v _ => ?_
    rw [show v / 2 = 1 / 2 * v by ring]; ring
  rw [e, Cvs.Finite.CoshMomentRecentred.integral_cosh_mul_cos (by positivity)]
  unfold poleSymbol
  rw [show 1 / 2 * L = L / 2 by ring, mul_comm t L]
  field_simp
  ring

/-- `poleSymbol L` is the cosine transform of `poleMeasure (−L) L` for `0 ≤ L`. -/
theorem poleSymbol_eq_integral {L : ℝ} (hL : 0 ≤ L) (t : ℝ) :
    poleSymbol L t = ∫ v, Real.cos (t * v) ∂poleMeasure (-L) L := by
  rw [poleSymbol_eq_intervalIntegral, integral_cos_poleMeasure (by linarith)]

/-- `poleSymbol 0 = 0`. -/
theorem poleSymbol_zero_left (t : ℝ) : poleSymbol 0 t = 0 := by
  simp [poleSymbol]

/-- `poleMeasure a b` is null on `(−L, L)` when `(a, b]` misses it. -/
theorem poleMeasure_Ioo {a b L : ℝ} (h : Disjoint (Ioc a b) (Ioo (-L) L)) :
    poleMeasure a b (Ioo (-L) L) = 0 :=
  withDensity_absolutelyContinuous _ _ (by
    rw [Measure.restrict_apply measurableSet_Ioo, Set.inter_comm, h.inter_eq, measure_empty])

/-- **The pole symbol is band-free in its length**: `poleSymbol L' − poleSymbol L ∈ bandFree L` for
`L ≤ L'`, the cosine transform of `2cosh(v/2) dv` on `(−L', −L] ∪ (L, L']`. -/
theorem poleSymbol_sub_mem_bandFree {L L' : ℝ} (h : L ≤ L') :
    (fun t => poleSymbol L' t - poleSymbol L t) ∈ Cvs.WeilForm.BandFreedomCosine.bandFree L := by
  refine ⟨poleMeasure (-L') (-L) + poleMeasure L L', 0, inferInstance, inferInstance, ?_, by simp,
    fun t => ?_⟩
  · rw [Measure.add_apply,
      poleMeasure_Ioo (Set.disjoint_left.2 fun x hx hy => absurd hy.1 (not_lt.2 hx.2)),
      poleMeasure_Ioo (Set.disjoint_left.2 fun x hx hy => absurd hy.2 (not_lt.2 hx.1.le)), add_zero]
  · have hc : ∀ a b : ℝ, IntervalIntegrable (fun v => 2 * Real.cosh (v / 2) * Real.cos (t * v)) volume a b :=
      fun a b => (by fun_prop : Continuous fun v : ℝ => 2 * Real.cosh (v / 2) * Real.cos (t * v)).intervalIntegrable a b
    dsimp only
    rw [integral_add_measure (Cvs.WeilForm.BandFreedomCosine.integrable_cos_mul _ t) (Cvs.WeilForm.BandFreedomCosine.integrable_cos_mul _ t),
      integral_cos_poleMeasure (by linarith) t, integral_cos_poleMeasure h t, integral_zero_measure,
      poleSymbol_eq_intervalIntegral, poleSymbol_eq_intervalIntegral,
      ← intervalIntegral.integral_add_adjacent_intervals (hc (-L') (-L)) (hc (-L) L'),
      ← intervalIntegral.integral_add_adjacent_intervals (hc (-L) L) (hc L L')]
    ring

/-- **The pole symbol is the cosine transform of a finite signed measure**: `poleSymbol L ∈ bandFree 0`. -/
theorem poleSymbol_mem_bandFree (L : ℝ) : poleSymbol L ∈ Cvs.WeilForm.BandFreedomCosine.bandFree 0 := by
  rcases le_total 0 L with hL | hL
  · convert poleSymbol_sub_mem_bandFree hL using 1
    funext t; rw [poleSymbol_zero_left, sub_zero]
  · obtain ⟨μ, ν, hμ, hν, -, -, e⟩ := poleSymbol_sub_mem_bandFree hL
    refine ⟨ν, μ, hν, hμ, by simp, by simp, fun t => ?_⟩
    have := e t
    dsimp only at this
    rw [poleSymbol_zero_left] at this
    linarith

/-- `poleSymbol L ρ_{f,g}` is integrable for `f, g ∈ L¹ ∩ L²`. -/
theorem integrable_poleSymbol_mul_crossSpec (L : ℝ) (hf1 : Integrable f) (hf2 : MemLp f 2 volume)
    (hg1 : Integrable g) (hg2 : MemLp g 2 volume) :
    Integrable fun t => poleSymbol L t * crossSpec f g t :=
  Cvs.WeilForm.BandFreedomCosine.integrable_mul_crossSpec (poleSymbol_mem_bandFree L) hf1 hf2 hg1 hg2

/-- **The pole channel as a multiplier**: `poleF f poleG g + poleF g poleG f = ∫ poleSymbol L ρ_{f,g}` for
`f, g ∈ L¹ ∩ L²` vanishing off `[a, b]` with `b − a ≤ L`. -/
theorem pole_eq_integral_crossSpec {L a b : ℝ} (hf1 : Integrable f) (hf2 : MemLp f 2 volume)
    (hg1 : Integrable g) (hg2 : MemLp g 2 volume) (hfs : ∀ x ∉ Icc a b, f x = 0)
    (hgs : ∀ x ∉ Icc a b, g x = 0) (hab : b - a ≤ L) :
    poleF f * poleG g + poleF g * poleG f = ∫ t, poleSymbol L t * crossSpec f g t := by
  rw [pole_eq_integral_cosh_mul_polar hf1 hg1 hfs hgs]
  rcases le_or_gt 0 L with hL | hL
  · have hz : ∀ v ∉ Ioc (-L) L, 2 * Real.cosh (v / 2) * polar f g v = 0 := fun v hv => by
      refine mul_eq_zero_of_right _ (Cvs.WeilForm.BandFreedomCosine.polar_eq_zero_of_support hfs hgs (hab.trans ?_))
      simp only [mem_Ioc, not_and_or, not_lt, not_le] at hv
      rcases hv with h | h
      · exact (by linarith : L ≤ -v).trans (neg_le_abs v)
      · exact h.le.trans (le_abs_self v)
    calc ∫ v, Real.cosh (v / 2) * polar f g v = (∫ v, polar f g v ∂poleMeasure (-L) L) / 2 := by
          rw [integral_poleMeasure, setIntegral_eq_integral_of_forall_compl_eq_zero hz, ← integral_div]
          exact integral_congr_ae (Eventually.of_forall fun v => by ring)
      _ = ∫ t, (∫ v, Real.cos (t * v) ∂poleMeasure (-L) L) * crossSpec f g t :=
          (Cvs.WeilForm.BandFreedomCosine.integral_cosTransform_mul_crossSpec hf1 hf2 hg1 hg2 _).symm
      _ = ∫ t, poleSymbol L t * crossSpec f g t :=
          integral_congr_ae (Eventually.of_forall fun t => by dsimp only; rw [poleSymbol_eq_integral hL])
  · have h0 : ∀ v, polar f g v = 0 := fun v =>
      Cvs.WeilForm.BandFreedomCosine.polar_eq_zero_of_support hfs hgs (hab.trans (hL.le.trans (abs_nonneg v)))
    simp only [h0, mul_zero, integral_zero]
    have hm := Cvs.WeilForm.BandFreedomCosine.bandFree_anti hL.le (poleSymbol_mem_bandFree L)
    exact (Cvs.WeilForm.BandFreedomCosine.integral_mul_crossSpec_eq_zero hm hf1 hf2 hg1 hg2 hfs hgs hab).symm

/-! ### The prime measure and its cosine transform -/

/-- **The prime measure** `Σ_{p ≤ P, r ≤ R} w(p,r)(δ_{r log p} + δ_{−r log p})`, `w(p,r) = log p · p^{−r/2}`. -/
def primeMeasure (P R : ℕ) : Measure ℝ :=
  ∑ p ∈ (Finset.range (P + 1)).filter Nat.Prime, ∑ r ∈ Finset.Icc 1 R,
    (primePowerWeight p r).toNNReal •
      (Measure.dirac ((r : ℝ) * Real.log p) + Measure.dirac (-((r : ℝ) * Real.log p)))

instance (P R : ℕ) : IsFiniteMeasure (primeMeasure P R) := by
  unfold primeMeasure; infer_instance

/-- **The prime side is integration against the prime measure**: `∫ h d(primeMeasure P R) = PPS P R h`. -/
theorem integral_primeMeasure (P R : ℕ) (h : ℝ → ℝ) :
    ∫ v, h v ∂primeMeasure P R = primePowerSideTruncated P R h := by
  have hi : ∀ x : ℝ, Integrable h (Measure.dirac x) := fun x => integrable_dirac enorm_lt_top
  have hpr : ∀ p r : ℕ, Integrable h ((primePowerWeight p r).toNNReal •
      (Measure.dirac ((r : ℝ) * Real.log p) + Measure.dirac (-((r : ℝ) * Real.log p)))) :=
    fun p r => ((hi _).add_measure (hi _)).smul_measure_nnreal
  unfold primeMeasure primePowerSideTruncated
  rw [integral_finsetSum_measure fun p _ => integrable_finsetSum_measure.2 fun r _ => hpr p r]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [integral_finsetSum_measure fun r _ => hpr p r]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [integral_smul_nnreal_measure, integral_add_measure (hi _) (hi _), integral_dirac, integral_dirac,
    NNReal.smul_def, Real.coe_toNNReal _
      (primePowerWeight_nonneg (Nat.Prime.one_lt (Finset.mem_filter.1 hp).2).le r), smul_eq_mul]

/-- **The prime symbol is the cosine transform of the prime measure.** -/
theorem primeSymbol_eq_integral (P R : ℕ) (t : ℝ) :
    Cvs.WeilForm.EffectiveSymbol.primeSymbol P R t = ∫ v, Real.cos (t * v) ∂primeMeasure P R := by
  rw [integral_primeMeasure]
  unfold Cvs.WeilForm.EffectiveSymbol.primeSymbol primePowerSideTruncated
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun r _ => ?_
  dsimp only
  rw [show t * -((r : ℝ) * Real.log p) = -(t * ((r : ℝ) * Real.log p)) by ring, Real.cos_neg]
  ring

/-- `primeSymbol P R ρ_{f,g}` is integrable for `f, g ∈ L¹ ∩ L²`. -/
theorem integrable_primeSymbol_mul_crossSpec (P R : ℕ) (hf1 : Integrable f) (hf2 : MemLp f 2 volume)
    (hg1 : Integrable g) (hg2 : MemLp g 2 volume) :
    Integrable fun t => Cvs.WeilForm.EffectiveSymbol.primeSymbol P R t * crossSpec f g t :=
  (Cvs.WeilForm.BandFreedomCosine.integrable_cosTransform_mul_crossSpec hf1 hf2 hg1 hg2 (primeMeasure P R)).congr
    (Eventually.of_forall fun t => by simp only [primeSymbol_eq_integral])

/-- **The prime channel as a multiplier**: `½ PPS P R (polar f g) = ∫ primeSymbol P R ρ_{f,g}` for
`f, g ∈ L¹ ∩ L²`. -/
theorem primeSide_polar_eq_integral (P R : ℕ) (hf1 : Integrable f) (hf2 : MemLp f 2 volume)
    (hg1 : Integrable g) (hg2 : MemLp g 2 volume) :
    primePowerSideTruncated P R (polar f g) / 2 = ∫ t, Cvs.WeilForm.EffectiveSymbol.primeSymbol P R t * crossSpec f g t := by
  rw [← integral_primeMeasure, ← Cvs.WeilForm.BandFreedomCosine.integral_cosTransform_mul_crossSpec hf1 hf2 hg1 hg2]
  exact integral_congr_ae (Eventually.of_forall fun t => by simp only [primeSymbol_eq_integral])

end Cvs.WeilForm.PolePrimeCosineMultipliers
