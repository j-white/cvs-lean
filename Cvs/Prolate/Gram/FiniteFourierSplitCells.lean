import Mathlib
import Cvs.Prolate.Gram.EvenFirstCellEnergyGram
import Cvs.Prolate.Gram.WindowFloorExtension
import Cvs.Prolate.Gram.WindowFloorTransferSolutions
import Cvs.Upstream.CosineKernelContraction

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The finite Fourier transform on `L²(0, 1/2] ⊕ L²(1/2, 1]`

An element `z = (z₁, z₂)` of `E2` is the function `zf z = 1_{(0,1/2]} z₁ + 1_{(1/2,1]} z₂` on `ℝ`, and
`⟨z, w⟩ = ∫ zf z · zf w`. The even finite Fourier transform in these coordinates is
`(𝓕z)(s) = √(2c/π) ∫ cos(csu) zf z(u) du` on `(0, 1]`; it is a symmetric contraction of `E2` (Plancherel, Cvs.Upstream.CosineKernelContraction).
-/

noncomputable section

open Real MeasureTheory Set Filter

namespace Cvs.Prolate.Gram.FiniteFourierSplitCells
open Cvs.ZeroCounting

open Cvs.Prolate.Gram.EvenFirstCellEnergyGram (L2c)
open Cvs.Prolate.Gram.WindowFloorExtension (L2i)
open Cvs.Prolate.Gram.WindowFloorTransferSolutions (E2)

/-- The function on `ℝ` of `z ∈ E2`: `z₁` on `(0, 1/2]`, `z₂` on `(1/2, 1]`, `0` elsewhere. -/
def zf (z : E2) : ℝ → ℝ := fun u =>
  (Ioc (0 : ℝ) (1 / 2)).indicator ((WithLp.ofLp z).1 : ℝ → ℝ) u +
    (Ioc (1 / 2 : ℝ) 1).indicator ((WithLp.ofLp z).2 : ℝ → ℝ) u

/-- `z₁` is integrable on `(0, 1/2]`. -/
theorem integrable_fst (z : E2) : IntegrableOn ((WithLp.ofLp z).1 : ℝ → ℝ) (Ioc (0 : ℝ) (1 / 2)) :=
  (Lp.memLp (WithLp.ofLp z).1).integrable one_le_two

/-- `z₂` is integrable on `(1/2, 1]`. -/
theorem integrable_snd (z : E2) : IntegrableOn ((WithLp.ofLp z).2 : ℝ → ℝ) (Ioc (1 / 2 : ℝ) 1) :=
  (Lp.memLp (WithLp.ofLp z).2).integrable one_le_two

/-- `zf z` is integrable. -/
theorem integrable_zf (z : E2) : Integrable (zf z) :=
  ((integrable_indicator_iff measurableSet_Ioc).2 (integrable_fst z)).add
    ((integrable_indicator_iff measurableSet_Ioc).2 (integrable_snd z))

/-- `zf z` vanishes off `(0, 1]`. -/
theorem zf_eq_zero {z : E2} {u : ℝ} (hu : u ∉ Ioc (0 : ℝ) 1) : zf z u = 0 := by
  have h1 : u ∉ Ioc (0 : ℝ) (1 / 2) := fun h => hu ⟨h.1, by linarith [h.2]⟩
  have h2 : u ∉ Ioc (1 / 2 : ℝ) 1 := fun h => hu ⟨by linarith [h.1], h.2⟩
  rw [zf, Set.indicator_of_notMem h1, Set.indicator_of_notMem h2, add_zero]

/-- The product of two `zf` splits on the two halves. -/
theorem zf_mul (z w : E2) (u : ℝ) :
    zf z u * zf w u = (Ioc (0 : ℝ) (1 / 2)).indicator
        (fun u => ((WithLp.ofLp z).1 : ℝ → ℝ) u * ((WithLp.ofLp w).1 : ℝ → ℝ) u) u
      + (Ioc (1 / 2 : ℝ) 1).indicator
        (fun u => ((WithLp.ofLp z).2 : ℝ → ℝ) u * ((WithLp.ofLp w).2 : ℝ → ℝ) u) u := by
  by_cases h1 : u ∈ Ioc (0 : ℝ) (1 / 2)
  · have h2 : u ∉ Ioc (1 / 2 : ℝ) 1 := fun h => by linarith [h.1, h1.2]
    simp only [zf, Set.indicator_of_mem h1, Set.indicator_of_notMem h2, add_zero]
  · by_cases h2 : u ∈ Ioc (1 / 2 : ℝ) 1
    · simp only [zf, Set.indicator_of_mem h2, Set.indicator_of_notMem h1, zero_add]
    · simp only [zf, Set.indicator_of_notMem h1, Set.indicator_of_notMem h2, add_zero, mul_zero]

/-- **The inner product of `E2` is the integral of the product**: `⟨z, w⟩ = ∫ zf z · zf w`. -/
theorem inner_eq_integral (z w : E2) : inner ℝ z w = ∫ u, zf z u * zf w u := by
  have hi1 : IntegrableOn (fun u => ((WithLp.ofLp z).1 : ℝ → ℝ) u * ((WithLp.ofLp w).1 : ℝ → ℝ) u)
      (Ioc (0 : ℝ) (1 / 2)) := (Lp.memLp (WithLp.ofLp z).1).integrable_mul (Lp.memLp (WithLp.ofLp w).1)
  have hi2 : IntegrableOn (fun u => ((WithLp.ofLp z).2 : ℝ → ℝ) u * ((WithLp.ofLp w).2 : ℝ → ℝ) u)
      (Ioc (1 / 2 : ℝ) 1) := (Lp.memLp (WithLp.ofLp z).2).integrable_mul (Lp.memLp (WithLp.ofLp w).2)
  simp_rw [zf_mul]
  rw [integral_add ((integrable_indicator_iff measurableSet_Ioc).2 hi1)
      ((integrable_indicator_iff measurableSet_Ioc).2 hi2),
    integral_indicator measurableSet_Ioc, integral_indicator measurableSet_Ioc, WithLp.prod_inner_apply,
    L2.inner_def, L2.inner_def]
  simp only [RCLike.inner_apply, conj_trivial]
  congr 1 <;> exact integral_congr_ae (ae_of_all _ fun _ => mul_comm _ _)

/-- `zf` is additive almost everywhere. -/
theorem zf_add (z w : E2) : zf (z + w) =ᵐ[volume] zf z + zf w := by
  have h1 := (ae_eq_restrict_iff_indicator_ae_eq (μ := volume) measurableSet_Ioc).1
    (Lp.coeFn_add (WithLp.ofLp z).1 (WithLp.ofLp w).1)
  have h2 := (ae_eq_restrict_iff_indicator_ae_eq (μ := volume) measurableSet_Ioc).1
    (Lp.coeFn_add (WithLp.ofLp z).2 (WithLp.ofLp w).2)
  filter_upwards [h1, h2] with u hu1 hu2
  simp only [zf, WithLp.ofLp_add, Prod.fst_add, Prod.snd_add, Pi.add_apply] at hu1 hu2 ⊢
  rw [hu1, hu2, Set.indicator_add', Set.indicator_add', Pi.add_apply, Pi.add_apply]
  ring

/-- `zf` is homogeneous almost everywhere. -/
theorem zf_smul (r : ℝ) (z : E2) : zf (r • z) =ᵐ[volume] r • zf z := by
  have h1 := (ae_eq_restrict_iff_indicator_ae_eq (μ := volume) measurableSet_Ioc).1
    (Lp.coeFn_smul r (WithLp.ofLp z).1)
  have h2 := (ae_eq_restrict_iff_indicator_ae_eq (μ := volume) measurableSet_Ioc).1
    (Lp.coeFn_smul r (WithLp.ofLp z).2)
  filter_upwards [h1, h2] with u hu1 hu2
  simp only [zf, WithLp.ofLp_smul, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul] at hu1 hu2 ⊢
  rw [hu1, hu2]
  simp only [Set.indicator_apply, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> ring

/-- `cos(csu) · zf z(u)` is integrable in `u`. -/
theorem integrable_cos_mul (c s : ℝ) (z : E2) : Integrable fun u => Real.cos (c * s * u) * zf z u :=
  (integrable_zf z).bdd_mul (by fun_prop : Continuous fun u => Real.cos (c * s * u)).aestronglyMeasurable
    (ae_of_all _ fun u => by rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)

/-- The cosine integral `J z s = ∫ cos(csu) zf z(u) du`. -/
def cosInt (c : ℝ) (z : E2) (s : ℝ) : ℝ := ∫ u, Real.cos (c * s * u) * zf z u

/-- `J` is additive in `z`. -/
theorem cosInt_add (c : ℝ) (z w : E2) (s : ℝ) : cosInt c (z + w) s = cosInt c z s + cosInt c w s := by
  rw [cosInt, cosInt, cosInt, ← integral_add (integrable_cos_mul c s z) (integrable_cos_mul c s w)]
  refine integral_congr_ae ?_
  filter_upwards [zf_add z w] with u hu
  rw [hu, Pi.add_apply]; ring

/-- `J` is homogeneous in `z`. -/
theorem cosInt_smul (c r : ℝ) (z : E2) (s : ℝ) : cosInt c (r • z) s = r * cosInt c z s := by
  rw [cosInt, cosInt, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [zf_smul r z] with u hu
  rw [hu, Pi.smul_apply, smul_eq_mul]; ring

/-- `J z` is continuous. -/
theorem continuous_cosInt (c : ℝ) (z : E2) : Continuous (cosInt c z) := by
  refine continuous_of_dominated (bound := fun u => |zf z u|) (fun s => (integrable_cos_mul c s z).1)
    (fun s => ae_of_all _ fun u => ?_) (integrable_zf z).abs (ae_of_all _ fun u => by fun_prop)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_of_le_one_left (abs_nonneg _) (Real.abs_cos_le_one _)

/-- `|J z s| ≤ ∫ |zf z|`. -/
theorem abs_cosInt_le (c : ℝ) (z : E2) (s : ℝ) : |cosInt c z s| ≤ ∫ u, |zf z u| := by
  refine (abs_integral_le_integral_abs).trans (integral_mono (integrable_cos_mul c s z).abs (integrable_zf z).abs
    fun u => ?_)
  rw [abs_mul]
  exact mul_le_of_le_one_left (abs_nonneg _) (Real.abs_cos_le_one _)

/-- `J z` is even. -/
theorem cosInt_neg (c : ℝ) (z : E2) (s : ℝ) : cosInt c z (-s) = cosInt c z s := by
  simp only [cosInt, neg_mul, mul_neg, Real.cos_neg]

/-- The Fourier image `s ↦ √(2c/π) J z s`. -/
def fimg (c : ℝ) (z : E2) (s : ℝ) : ℝ := √(2 * c / π) * cosInt c z s

/-- The Fourier image is continuous. -/
theorem continuous_fimg (c : ℝ) (z : E2) : Continuous (fimg c z) :=
  continuous_const.mul (continuous_cosInt c z)

/-- The Fourier image is square integrable on every `(a, b]`. -/
theorem memLp_fimg_of {a b : ℝ} (c : ℝ) (z : E2) : MemLp (fimg c z) 2 (volume.restrict (Ioc a b)) := by
  refine MemLp.of_bound (continuous_fimg c z).aestronglyMeasurable (√(2 * c / π) * ∫ u, |zf z u|)
    (ae_of_all _ fun s => ?_)
  rw [Real.norm_eq_abs, fimg, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_mul_of_nonneg_left (abs_cosInt_le c z s) (Real.sqrt_nonneg _)

/-- The Fourier image is additive. -/
theorem fimg_add (c : ℝ) (z w : E2) : fimg c (z + w) = fimg c z + fimg c w := by
  funext s; simp only [fimg, cosInt_add, Pi.add_apply]; ring

/-- The Fourier image is homogeneous. -/
theorem fimg_smul (c r : ℝ) (z : E2) : fimg c (r • z) = r • fimg c z := by
  funext s; simp only [fimg, cosInt_smul, Pi.smul_apply, smul_eq_mul]; ring

/-- **The finite Fourier transform on `E2`**: `z ↦ (√(2c/π) J z|_{(0,1/2]}, √(2c/π) J z|_{(1/2,1]})`. -/
def fourierE2 (c : ℝ) : E2 →ₗ[ℝ] E2 where
  toFun z := WithLp.toLp 2 ((memLp_fimg_of c z).toLp (fimg c z), (memLp_fimg_of c z).toLp (fimg c z))
  map_add' z w := by
    rw [← WithLp.toLp_add]
    congr 1
    ext1
    · exact (MemLp.toLp_congr (memLp_fimg_of c (z + w)) ((memLp_fimg_of c z).add (memLp_fimg_of c w))
        (Filter.Eventually.of_forall fun s => congrFun (fimg_add c z w) s)).trans
        (MemLp.toLp_add (memLp_fimg_of c z) (memLp_fimg_of c w))
    · exact (MemLp.toLp_congr (memLp_fimg_of c (z + w)) ((memLp_fimg_of c z).add (memLp_fimg_of c w))
        (Filter.Eventually.of_forall fun s => congrFun (fimg_add c z w) s)).trans
        (MemLp.toLp_add (memLp_fimg_of c z) (memLp_fimg_of c w))
  map_smul' r z := by
    rw [RingHom.id_apply, ← WithLp.toLp_smul]
    congr 1
    ext1
    · exact (MemLp.toLp_congr (memLp_fimg_of c (r • z)) ((memLp_fimg_of c z).const_smul r)
        (Filter.Eventually.of_forall fun s => congrFun (fimg_smul c r z) s)).trans
        (MemLp.toLp_const_smul r (memLp_fimg_of c z))
    · exact (MemLp.toLp_congr (memLp_fimg_of c (r • z)) ((memLp_fimg_of c z).const_smul r)
        (Filter.Eventually.of_forall fun s => congrFun (fimg_smul c r z) s)).trans
        (MemLp.toLp_const_smul r (memLp_fimg_of c z))

/-- `zf (𝓕z) = 1_{(0,1]} · √(2c/π) J z` almost everywhere. -/
theorem zf_fourierE2 (c : ℝ) (z : E2) : zf (fourierE2 c z) =ᵐ[volume] (Ioc (0 : ℝ) 1).indicator (fimg c z) := by
  have h1 := (ae_eq_restrict_iff_indicator_ae_eq (μ := volume) (s := Ioc (0 : ℝ) (1 / 2)) measurableSet_Ioc).1
    (MemLp.coeFn_toLp (memLp_fimg_of c z))
  have h2 := (ae_eq_restrict_iff_indicator_ae_eq (μ := volume) (s := Ioc (1 / 2 : ℝ) 1) measurableSet_Ioc).1
    (MemLp.coeFn_toLp (memLp_fimg_of c z))
  filter_upwards [h1, h2] with u hu1 hu2
  simp only [zf, fourierE2, LinearMap.coe_mk, AddHom.coe_mk] at hu1 hu2 ⊢
  rw [hu1, hu2]
  by_cases ha : u ∈ Ioc (0 : ℝ) (1 / 2)
  · have hb : u ∉ Ioc (1 / 2 : ℝ) 1 := fun h => by linarith [h.1, ha.2]
    have hc : u ∈ Ioc (0 : ℝ) 1 := ⟨ha.1, by linarith [ha.2]⟩
    rw [Set.indicator_of_mem ha, Set.indicator_of_notMem hb, Set.indicator_of_mem hc, add_zero]
  · by_cases hb : u ∈ Ioc (1 / 2 : ℝ) 1
    · have hc : u ∈ Ioc (0 : ℝ) 1 := ⟨by linarith [hb.1], hb.2⟩
      rw [Set.indicator_of_notMem ha, Set.indicator_of_mem hb, Set.indicator_of_mem hc, zero_add]
    · have hc : u ∉ Ioc (0 : ℝ) 1 := fun h => by
        by_cases h' : u ≤ 1 / 2
        · exact ha ⟨h.1, h'⟩
        · exact hb ⟨lt_of_not_ge h', h.2⟩
      rw [Set.indicator_of_notMem ha, Set.indicator_of_notMem hb, Set.indicator_of_notMem hc, add_zero]

/-- `⟨𝓕z, w⟩ = √(2c/π) ∫_s ∫_u cos(csu) zf z(u) zf w(s)`. -/
theorem inner_fourierE2 (c : ℝ) (z w : E2) :
    inner ℝ (fourierE2 c z) w = √(2 * c / π) * ∫ s, ∫ u, Real.cos (c * s * u) * zf z u * zf w s := by
  rw [inner_eq_integral]
  have e1 : (fun s => zf (fourierE2 c z) s * zf w s) =ᵐ[volume] fun s => fimg c z s * zf w s := by
    filter_upwards [zf_fourierE2 c z] with s hs
    rw [hs]
    by_cases h : s ∈ Ioc (0 : ℝ) 1
    · rw [Set.indicator_of_mem h]
    · rw [Set.indicator_of_notMem h, zf_eq_zero h, mul_zero, mul_zero]
  rw [integral_congr_ae e1, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun s => ?_)
  simp only [fimg, cosInt]
  rw [mul_assoc, ← integral_mul_const, ← integral_const_mul]

/-- The kernel `cos(csu) zf z(u) zf w(s)` is integrable on `ℝ²`. -/
theorem integrable_kernel (c : ℝ) (z w : E2) :
    Integrable (Function.uncurry fun s u => Real.cos (c * s * u) * zf z u * zf w s) (volume.prod volume) := by
  have h := ((integrable_zf w).mul_prod (integrable_zf z)).bdd_mul (c := 1)
    (by fun_prop : Continuous fun p : ℝ × ℝ => Real.cos (c * p.1 * p.2)).aestronglyMeasurable
    (ae_of_all _ fun p => by rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
  refine h.congr (ae_of_all _ fun p => ?_)
  simp only [Function.uncurry]
  ring

/-- **`𝓕` is symmetric on `E2`** (Fubini). -/
theorem fourierE2_symm (c : ℝ) (z w : E2) : inner ℝ (fourierE2 c z) w = inner ℝ z (fourierE2 c w) := by
  rw [real_inner_comm (fourierE2 c w) z, inner_fourierE2, inner_fourierE2,
    integral_integral_swap (integrable_kernel c z w)]
  refine congrArg (√(2 * c / π) * ·) ?_
  refine integral_congr_ae (ae_of_all _ fun u => integral_congr_ae (ae_of_all _ fun s => ?_))
  simp only
  rw [show c * u * s = c * s * u by ring]
  ring

/-- `zf z` is square integrable on `ℝ`. -/
theorem memLp_zf (z : E2) : MemLp (zf z) 2 volume :=
  ((memLp_indicator_iff_restrict measurableSet_Ioc.nullMeasurableSet).2 (Lp.memLp (WithLp.ofLp z).1)).add
    ((memLp_indicator_iff_restrict measurableSet_Ioc.nullMeasurableSet).2 (Lp.memLp (WithLp.ofLp z).2))

/-- `‖z‖² = ∫ (zf z)²`. -/
theorem norm_sq_eq_integral (z : E2) : ‖z‖ ^ 2 = ∫ u, zf z u ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_eq_integral]
  exact integral_congr_ae (ae_of_all _ fun u => (sq _).symm)

/-- `zf z(t) · zf z(−t) = 0`: the supports `(0, 1]` and `[−1, 0)` are disjoint. -/
theorem zf_mul_zf_neg (z : E2) (t : ℝ) : zf z t * zf z (-t) = 0 := by
  by_cases h : t ∈ Ioc (0 : ℝ) 1
  · have h' : -t ∉ Ioc (0 : ℝ) 1 := fun h' => by linarith [h.1, h'.1]
    rw [zf_eq_zero h', mul_zero]
  · rw [zf_eq_zero h, zero_mul]

/-- The even extension `φ(t) = (zf z(t) + zf z(−t))/√2`. -/
def evenExt (z : E2) (t : ℝ) : ℝ := (zf z t + zf z (-t)) / √2

/-- `φ` is square integrable. -/
theorem memLp_evenExt (z : E2) : MemLp (evenExt z) 2 volume := by
  have h := (memLp_zf z).add ((memLp_zf z).comp_measurePreserving (Measure.measurePreserving_neg volume))
  refine (h.const_smul (√2)⁻¹).ae_eq (ae_of_all _ fun t => ?_)
  simp only [evenExt, Pi.smul_apply, Pi.add_apply, Function.comp_apply, smul_eq_mul]
  ring

/-- `φ` is integrable. -/
theorem integrable_evenExt (z : E2) : Integrable (evenExt z) :=
  ((integrable_zf z).add (integrable_zf z).comp_neg).div_const _

/-- `∫ φ² = ‖z‖²`. -/
theorem integral_evenExt_sq (z : E2) : ∫ t, evenExt z t ^ 2 = ‖z‖ ^ 2 := by
  have h2 : (√2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have e : ∀ t, evenExt z t ^ 2 = (zf z t ^ 2 + zf z (-t) ^ 2) / 2 := fun t => by
    rw [evenExt, div_pow, h2, add_sq, mul_assoc 2, zf_mul_zf_neg]; ring
  have hi : Integrable fun t => zf z t ^ 2 := (memLp_zf z).integrable_sq
  simp_rw [e]
  rw [integral_div, integral_add hi (hi.comp_neg (f := fun t => zf z t ^ 2)),
    integral_neg_eq_self (fun t => zf z t ^ 2), norm_sq_eq_integral]
  ring

/-- `∫ cos(cst) φ(t) dt = √2 J z s`. -/
theorem integral_cos_evenExt (c : ℝ) (z : E2) (s : ℝ) :
    ∫ t, Real.cos (c * s * t) * evenExt z t = √2 * cosInt c z s := by
  have hs2 : √2 ≠ 0 := by positivity
  have e : ∀ t, Real.cos (c * s * t) * evenExt z t =
      (Real.cos (c * s * t) * zf z t + Real.cos (c * s * -t) * zf z (-t)) / √2 := fun t => by
    rw [evenExt, mul_neg, Real.cos_neg]; ring
  simp_rw [e]
  rw [integral_div, integral_add (integrable_cos_mul c s z)
      ((integrable_cos_mul c s z).comp_neg (f := fun t => Real.cos (c * s * t) * zf z t)),
    integral_neg_eq_self (fun t => Real.cos (c * s * t) * zf z t)]
  rw [cosInt]
  field_simp
  rw [Real.sq_sqrt (by norm_num)]
  ring

/-- For `g` continuous and even, `∫_{(−1,1]} g = 2∫_{(0,1]} g`. -/
theorem setIntegral_Ioc_neg_one_one {g : ℝ → ℝ} (hg : Continuous g) (hev : ∀ s, g (-s) = g s) :
    ∫ s in Ioc (-1 : ℝ) 1, g s = 2 * ∫ s in Ioc (0 : ℝ) 1, g s := by
  rw [← intervalIntegral.integral_of_le (by norm_num), ← intervalIntegral.integral_of_le (by norm_num),
    ← intervalIntegral.integral_add_adjacent_intervals (b := 0) (hg.intervalIntegrable _ _)
      (hg.intervalIntegrable _ _)]
  have h : ∫ s in (-1 : ℝ)..0, g s = ∫ s in (0 : ℝ)..1, g s := by
    have := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := 1) g
    rw [neg_zero] at this
    rw [← this]
    exact intervalIntegral.integral_congr fun s _ => hev s
  rw [h]; ring

/-- **`𝓕` is a contraction on `E2`** (Plancherel, Cvs.Upstream.CosineKernelContraction): `‖𝓕z‖ ≤ ‖z‖` for `c > 0`. -/
theorem norm_fourierE2_le {c : ℝ} (hc : 0 < c) (z : E2) : ‖fourierE2 c z‖ ≤ ‖z‖ := by
  have hP := Cvs.Upstream.CosineKernelContraction.setIntegral_sq_cosIntegral_le hc (memLp_evenExt z) (integrable_evenExt z)
    (Ioc (-1 : ℝ) 1)
  simp_rw [integral_cos_evenExt] at hP
  rw [integral_evenExt_sq] at hP
  have hJc : Continuous fun s => cosInt c z s ^ 2 := (continuous_cosInt c z).pow 2
  have hev : ∀ s, cosInt c z (-s) ^ 2 = cosInt c z s ^ 2 := fun s => by rw [cosInt_neg]
  have hpi : 0 < π := Real.pi_pos
  have hk1 : (√(c / (2 * π))) ^ 2 = c / (2 * π) := Real.sq_sqrt (by positivity)
  have hk2 : (√(2 * c / π)) ^ 2 = 2 * c / π := Real.sq_sqrt (by positivity)
  have h22 : (√2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have e1 : ∫ s in Ioc (-1 : ℝ) 1, (√(c / (2 * π)) * (√2 * cosInt c z s)) ^ 2
      = (c / π) * ∫ s in Ioc (-1 : ℝ) 1, cosInt c z s ^ 2 := by
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun s => ?_)
    simp only [mul_pow, hk1, h22]; field_simp
  rw [e1, setIntegral_Ioc_neg_one_one hJc hev] at hP
  have hT : ‖fourierE2 c z‖ ^ 2 = (2 * c / π) * ∫ s in Ioc (0 : ℝ) 1, cosInt c z s ^ 2 := by
    rw [norm_sq_eq_integral, ← integral_const_mul, ← integral_indicator measurableSet_Ioc]
    refine integral_congr_ae ?_
    filter_upwards [zf_fourierE2 c z] with s hs
    rw [hs]
    by_cases h : s ∈ Ioc (0 : ℝ) 1
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, fimg, mul_pow, hk2]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]; ring
  have h3 : ‖fourierE2 c z‖ ^ 2 ≤ ‖z‖ ^ 2 := by
    rw [hT]
    have e2 : 2 * c / π * ∫ s in Ioc (0 : ℝ) 1, cosInt c z s ^ 2
        = c / π * (2 * ∫ s in Ioc (0 : ℝ) 1, cosInt c z s ^ 2) := by ring
    linarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) (by norm_num)).1 h3

end Cvs.Prolate.Gram.FiniteFourierSplitCells

end
