import Mathlib
import Cvs.StepA.Edge.EdgeDiscriminant
import Cvs.StepA.Edge.OneOrdinateDiscriminant
import Cvs.StepA.Edge.TwoEdgeSplit

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Merged ordinates and the Gram matrix of the damped edge functions

The edge form of a finite family depends on `|γᵢ|` only, and for distinct positive ordinates `g`
the edge functions `e^{−δu}cos gᵢu`, `e^{−δu}sin gᵢu` have a positive definite Gram matrix on
`[0, ∞)`, `½ Re(cₑc_f/(2δ + i(gᵢ + gⱼ)) + cₑc̄_f/(2δ + i(gᵢ − gⱼ)))`, the limit of their Gram
matrices on `[0, b]`.
-/

noncomputable section

open Real MeasureTheory Filter Topology Matrix

namespace Cvs.StepA.Edge.DampedEdgeGram
open Cvs.ZeroCounting

open Cvs.StepA.Edge.TwoEdgeSplit (edgePair edgeForm)
open Cvs.StepA.Edge.EdgeDiscriminant (edgeRay edgeDisc)

/-! ### Merging to distinct positive ordinates -/

/-- One term of the edge form depends on the ordinate through `|γ|`. -/
theorem edgeTerm_abs (δ γ L : ℝ) (F : ℝ → ℝ) (a : ℝ) :
    (Complex.exp ((|γ| : ℝ) * L * Complex.I) * edgePair δ |γ| F a ^ 2).re
      = (Complex.exp (γ * L * Complex.I) * edgePair δ γ F a ^ 2).re := by
  rcases abs_choice γ with h | h
  · rw [h]
  · rw [h, Cvs.StepA.Edge.OneOrdinateDiscriminant.edgeTerm_neg]

/-- The merged ordinates `{|γᵢ| : i ∈ s}`. -/
def mergeOrd {α : Type*} (s : Finset α) (γ : α → ℝ) : Finset ℝ :=
  s.image fun i => |γ i|

/-- The merged weight `∑_{i ∈ s, |γᵢ| = r} mᵢ` of an ordinate `r`. -/
def mergeW {α : Type*} (s : Finset α) (m γ : α → ℝ) (r : ℝ) : ℝ :=
  ∑ i ∈ s with |γ i| = r, m i

/-- **Merging**: the edge form of `s` is that of the merged ordinates with the merged weights. -/
theorem edgeForm_merge {α : Type*} (s : Finset α) (m γ : α → ℝ) (δ L : ℝ) (F : ℝ → ℝ) (a : ℝ) :
    edgeForm (Finset.univ : Finset (mergeOrd s γ)) (fun r => mergeW s m γ r) (fun r => (r : ℝ))
      δ L F a = edgeForm s m γ δ L F a := by
  unfold edgeForm mergeW
  rw [Finset.sum_coe_sort (mergeOrd s γ) (fun r => (∑ i ∈ s with |γ i| = r, m i) *
    (Complex.exp (r * L * Complex.I) * edgePair δ r F a ^ 2).re)]
  rw [← Finset.sum_fiberwise_of_maps_to (s := s) (t := mergeOrd s γ) (g := fun i => |γ i|)
    (fun i hi => Finset.mem_image_of_mem _ hi)]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [← (Finset.mem_filter.mp hi).2, edgeTerm_abs]

/-- **Merging the edge discriminant**: `edgeDisc` of `s` is that of the merged family. -/
theorem edgeDisc_merge {α : Type*} (s : Finset α) (m γ : α → ℝ) (δ L : ℝ) :
    edgeDisc (Finset.univ : Finset (mergeOrd s γ)) (fun r => mergeW s m γ r) (fun r => (r : ℝ))
      δ L = edgeDisc s m γ δ L := by
  unfold edgeDisc edgeRay
  simp only [edgeForm_merge]

/-- Merged ordinates of nonzero ordinates are positive. -/
theorem pos_of_mem_mergeOrd {α : Type*} {s : Finset α} {γ : α → ℝ} (hγ : ∀ i ∈ s, γ i ≠ 0)
    (r : mergeOrd s γ) : 0 < (r : ℝ) := by
  obtain ⟨i, hi, hr⟩ := Finset.mem_image.mp r.2
  rw [← hr]
  exact abs_pos.mpr (hγ i hi)

/-- Merged weights of positive weights are positive. -/
theorem mergeW_pos {α : Type*} {s : Finset α} {m γ : α → ℝ} (hm : ∀ i ∈ s, 0 < m i)
    (r : mergeOrd s γ) : 0 < mergeW s m γ r := by
  obtain ⟨i, hi, hr⟩ := Finset.mem_image.mp r.2
  refine Finset.sum_pos (fun j hj => hm j (Finset.mem_filter.mp hj).1) ⟨i, ?_⟩
  exact Finset.mem_filter.mpr ⟨hi, hr⟩

/-- The merged ordinates of a nonempty family are nonempty. -/
theorem nonempty_mergeOrd {α : Type*} {s : Finset α} (hs : s.Nonempty) (γ : α → ℝ) :
    Nonempty (mergeOrd s γ) :=
  (hs.image _).coe_sort

/-! ### The damped edge functions -/

/-- The unit `cₑ`: `c₀ = 1` selects the cosine edge function and `c₁ = i` the sine one. -/
def edgeUnit (e : Fin 2) : ℂ := ![1, Complex.I] e

/-- The damped edge function `Re(cₑ e^{−(δ + ig)u})`. -/
def edgeFn (δ g : ℝ) (e : Fin 2) (u : ℝ) : ℝ :=
  (edgeUnit e * Complex.exp (-((δ : ℂ) + g * Complex.I) * u)).re

/-- The edge functions are continuous. -/
@[fun_prop] theorem continuous_edgeFn (δ g : ℝ) (e : Fin 2) : Continuous (edgeFn δ g e) := by
  unfold edgeFn; fun_prop

/-- The cosine edge function: `edgeFn δ g 0 u = e^{−δu} cos gu`. -/
theorem edgeFn_zero (δ g u : ℝ) : edgeFn δ g 0 u = Real.exp (-(δ * u)) * Real.cos (g * u) := by
  simp [edgeFn, edgeUnit, Complex.exp_re, Complex.mul_re, Complex.mul_im, Real.cos_neg]

/-- The sine edge function: `edgeFn δ g 1 u = e^{−δu} sin gu`. -/
theorem edgeFn_one (δ g u : ℝ) : edgeFn δ g 1 u = Real.exp (-(δ * u)) * Real.sin (g * u) := by
  simp [edgeFn, edgeUnit, Complex.exp_im, Complex.mul_re, Complex.mul_im, Real.sin_neg]

/-- The pairing vector `p_{(e,i)} = ∫₀^a F · edgeFn(δ, gᵢ, e)` of a profile on `[0, a]`. -/
def pairVec {ι : Type*} (δ : ℝ) (g : ι → ℝ) (F : ℝ → ℝ) (a : ℝ) (k : Fin 2 × ι) : ℝ :=
  ∫ u in (0 : ℝ)..a, F u * edgeFn δ (g k.2) k.1 u

/-- For continuous `F`, the pairing is `p_{(e,i)} = Re(cₑ · edgePair(δ, gᵢ, F, a))`. -/
theorem pairVec_eq {ι : Type*} (δ : ℝ) (g : ι → ℝ) {F : ℝ → ℝ} (hF : Continuous F) (a : ℝ)
    (k : Fin 2 × ι) : pairVec δ g F a k = (edgeUnit k.1 * edgePair δ (g k.2) F a).re := by
  unfold pairVec edgePair
  rw [← intervalIntegral.integral_const_mul]
  have hc : Continuous fun u : ℝ => edgeUnit k.1 * (((F u : ℝ) : ℂ)
      * Complex.exp (-((δ : ℂ) + (g k.2 : ℂ) * Complex.I) * u)) := by fun_prop
  have h := intervalIntegral.intervalIntegral_re (μ := volume) (hc.intervalIntegrable 0 a)
  simp only [RCLike.re_to_complex] at h
  rw [← h]
  refine intervalIntegral.integral_congr fun u _ => ?_
  simp only [edgeFn]
  rw [mul_left_comm, Complex.re_ofReal_mul]

/-! ### Integrals of damped exponentials -/

/-- `∫₀^b e^{−(c + iω)u} du = (1 − e^{−(c + iω)b})/(c + iω)` for `c ≠ 0`. -/
theorem integral_exp_rate {c : ℝ} (hc : c ≠ 0) (ω b : ℝ) :
    ∫ u in (0 : ℝ)..b, Complex.exp (-((c : ℂ) + ω * Complex.I) * u)
      = (1 - Complex.exp (-((c : ℂ) + ω * Complex.I) * b)) / ((c : ℂ) + ω * Complex.I) := by
  have hz : (c : ℂ) + ω * Complex.I ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    exact hc this
  rw [integral_exp_mul_complex (neg_ne_zero.mpr hz)]
  push_cast
  rw [mul_zero, Complex.exp_zero]
  field_simp
  ring

/-- `e^{−(c + iω)b} → 0` as `b → ∞`, for `c > 0`. -/
theorem tendsto_exp_rate {c : ℝ} (hc : 0 < c) (ω : ℝ) :
    Tendsto (fun b : ℝ => Complex.exp (-((c : ℂ) + ω * Complex.I) * b)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h := Cvs.StepA.Edge.OneOrdinateDiscriminant.tendsto_exp_neg_two_mul (δ := c / 2) (by positivity)
  refine h.congr fun b => ?_
  rw [Complex.norm_exp]
  congr 1
  simp only [neg_mul, Complex.neg_re, Complex.mul_re, Complex.add_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.add_im, Complex.I_re, Complex.I_im, Complex.mul_im]
  ring

/-! ### The Gram matrices -/

/-- `Re z · Re w = Re(zw + z w̄)/2`. -/
theorem re_mul_re (z w : ℂ) : z.re * w.re = (z * w + z * starRingEnd ℂ w).re / 2 := by
  simp only [Complex.add_re, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- The product of two edge functions as a sum of two damped exponentials. -/
theorem edgeFn_mul_edgeFn (δ g g' : ℝ) (e f : Fin 2) (u : ℝ) :
    edgeFn δ g e u * edgeFn δ g' f u
      = (edgeUnit e * edgeUnit f * Complex.exp (-(((2 * δ : ℝ) : ℂ) + (g + g' : ℝ) * Complex.I) * u)
        + edgeUnit e * starRingEnd ℂ (edgeUnit f)
          * Complex.exp (-(((2 * δ : ℝ) : ℂ) + (g - g' : ℝ) * Complex.I) * u)).re / 2 := by
  unfold edgeFn
  rw [re_mul_re]
  congr 2
  rw [map_mul, ← Complex.exp_conj]
  have h1 : Complex.exp (-((δ : ℂ) + g * Complex.I) * u)
        * Complex.exp (-((δ : ℂ) + g' * Complex.I) * u)
      = Complex.exp (-(((2 * δ : ℝ) : ℂ) + (g + g' : ℝ) * Complex.I) * u) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  have h2 : Complex.exp (-((δ : ℂ) + g * Complex.I) * u)
        * Complex.exp (starRingEnd ℂ (-((δ : ℂ) + g' * Complex.I) * u))
      = Complex.exp (-(((2 * δ : ℝ) : ℂ) + (g - g' : ℝ) * Complex.I) * u) := by
    rw [← Complex.exp_add]
    congr 1
    simp only [map_mul, map_neg, map_add, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  rw [← h1, ← h2]
  ring

/-- The Gram matrix of the edge functions on `[0, b]`. -/
def gramOn {ι : Type*} (δ : ℝ) (g : ι → ℝ) (b : ℝ) : Matrix (Fin 2 × ι) (Fin 2 × ι) ℝ :=
  Matrix.of fun k l => ∫ u in (0 : ℝ)..b, edgeFn δ (g k.2) k.1 u * edgeFn δ (g l.2) l.1 u

/-- The closed form of the Gram matrix of the edge functions on `[0, ∞)`, which it is for
`δ > 0`: `½ Re(cₑc_f/(2δ + i(gᵢ + gⱼ)) + cₑc̄_f/(2δ + i(gᵢ − gⱼ)))`. -/
def gram {ι : Type*} (δ : ℝ) (g : ι → ℝ) : Matrix (Fin 2 × ι) (Fin 2 × ι) ℝ :=
  Matrix.of fun k l =>
    (edgeUnit k.1 * edgeUnit l.1 / (((2 * δ : ℝ) : ℂ) + (g k.2 + g l.2 : ℝ) * Complex.I)
      + edgeUnit k.1 * starRingEnd ℂ (edgeUnit l.1)
        / (((2 * δ : ℝ) : ℂ) + (g k.2 - g l.2 : ℝ) * Complex.I)).re / 2

/-- **The finite Gram matrix in closed form**: for `δ ≠ 0`, its entries are those of `gram` with
`1/ζ` replaced by `(1 − e^{−ζb})/ζ`. -/
theorem gramOn_eq {ι : Type*} {δ : ℝ} (hδ : δ ≠ 0) (g : ι → ℝ) (b : ℝ) (k l : Fin 2 × ι) :
    gramOn δ g b k l
      = (edgeUnit k.1 * edgeUnit l.1
          * ((1 - Complex.exp (-(((2 * δ : ℝ) : ℂ) + (g k.2 + g l.2 : ℝ) * Complex.I) * b))
            / (((2 * δ : ℝ) : ℂ) + (g k.2 + g l.2 : ℝ) * Complex.I))
        + edgeUnit k.1 * starRingEnd ℂ (edgeUnit l.1)
          * ((1 - Complex.exp (-(((2 * δ : ℝ) : ℂ) + (g k.2 - g l.2 : ℝ) * Complex.I) * b))
            / (((2 * δ : ℝ) : ℂ) + (g k.2 - g l.2 : ℝ) * Complex.I))).re / 2 := by
  have h2δ : 2 * δ ≠ 0 := mul_ne_zero two_ne_zero hδ
  simp only [gramOn, Matrix.of_apply, edgeFn_mul_edgeFn]
  rw [intervalIntegral.integral_div]
  congr 1
  have hc : Continuous fun u : ℝ =>
      edgeUnit k.1 * edgeUnit l.1
          * Complex.exp (-(((2 * δ : ℝ) : ℂ) + (g k.2 + g l.2 : ℝ) * Complex.I) * u)
        + edgeUnit k.1 * starRingEnd ℂ (edgeUnit l.1)
          * Complex.exp (-(((2 * δ : ℝ) : ℂ) + (g k.2 - g l.2 : ℝ) * Complex.I) * u) := by
    fun_prop
  have h := intervalIntegral.intervalIntegral_re (μ := volume) (hc.intervalIntegrable 0 b)
  simp only [RCLike.re_to_complex] at h
  rw [h]
  congr 1
  rw [intervalIntegral.integral_add ((by fun_prop : Continuous fun u : ℝ => edgeUnit k.1
      * edgeUnit l.1 * Complex.exp (-(((2 * δ : ℝ) : ℂ) + (g k.2 + g l.2 : ℝ) * Complex.I)
        * u)).intervalIntegrable 0 b)
    ((by fun_prop : Continuous fun u : ℝ => edgeUnit k.1 * starRingEnd ℂ (edgeUnit l.1)
      * Complex.exp (-(((2 * δ : ℝ) : ℂ) + (g k.2 - g l.2 : ℝ) * Complex.I) * u)).intervalIntegrable
        0 b),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_exp_rate h2δ, integral_exp_rate h2δ]

/-- **The finite Gram matrices converge to `gram`** as `b → ∞`, for `δ > 0`. -/
theorem tendsto_gramOn {ι : Type*} {δ : ℝ} (hδ : 0 < δ) (g : ι → ℝ) :
    Tendsto (fun b => gramOn δ g b) atTop (𝓝 (gram δ g)) := by
  refine tendsto_pi_nhds.mpr fun k => tendsto_pi_nhds.mpr fun l => ?_
  simp only [gramOn_eq hδ.ne']
  have h2δ : (0 : ℝ) < 2 * δ := by positivity
  set ζ₁ : ℂ := ((2 * δ : ℝ) : ℂ) + (g k.2 + g l.2 : ℝ) * Complex.I
  set ζ₂ : ℂ := ((2 * δ : ℝ) : ℂ) + (g k.2 - g l.2 : ℝ) * Complex.I
  have t1 := tendsto_exp_rate h2δ (g k.2 + g l.2)
  have t2 := tendsto_exp_rate h2δ (g k.2 - g l.2)
  have h1 := ((tendsto_const_nhds (x := (1 : ℂ))).sub t1).div_const ζ₁ |>.const_mul
    (edgeUnit k.1 * edgeUnit l.1)
  have h2 := ((tendsto_const_nhds (x := (1 : ℂ))).sub t2).div_const ζ₂ |>.const_mul
    (edgeUnit k.1 * starRingEnd ℂ (edgeUnit l.1))
  have h' := ((Complex.continuous_re.tendsto _).comp (h1.add h2)).div_const 2
  simp only [sub_zero, mul_one_div] at h'
  exact h'

/-- The Gram matrix `gram` is symmetric. -/
theorem gram_comm {ι : Type*} (δ : ℝ) (g : ι → ℝ) (k l : Fin 2 × ι) :
    gram δ g k l = gram δ g l k := by
  simp only [gram, Matrix.of_apply]
  congr 1
  have h1 : edgeUnit k.1 * edgeUnit l.1 / (((2 * δ : ℝ) : ℂ) + (g k.2 + g l.2 : ℝ) * Complex.I)
      = edgeUnit l.1 * edgeUnit k.1 / (((2 * δ : ℝ) : ℂ) + (g l.2 + g k.2 : ℝ) * Complex.I) := by
    rw [mul_comm, add_comm (g k.2)]
  have h2 : edgeUnit l.1 * starRingEnd ℂ (edgeUnit k.1)
        / (((2 * δ : ℝ) : ℂ) + (g l.2 - g k.2 : ℝ) * Complex.I)
      = starRingEnd ℂ (edgeUnit k.1 * starRingEnd ℂ (edgeUnit l.1)
        / (((2 * δ : ℝ) : ℂ) + (g k.2 - g l.2 : ℝ) * Complex.I)) := by
    simp only [map_div₀, map_mul, Complex.conj_conj, map_add, Complex.conj_ofReal, Complex.conj_I]
    congr 1
    · ring
    · push_cast; ring
  rw [Complex.add_re, Complex.add_re, h1, h2, Complex.conj_re]

/-- `1/(c + iω) = (c − iω)/(c² + ω²)`, in real and imaginary parts. -/
theorem inv_rate (c ω : ℝ) :
    (((c : ℂ) + ω * Complex.I)⁻¹).re = c / (c ^ 2 + ω ^ 2) ∧
      (((c : ℂ) + ω * Complex.I)⁻¹).im = -ω / (c ^ 2 + ω ^ 2) := by
  simp [Complex.inv_re, Complex.inv_im, Complex.normSq_apply, sq, neg_div]

/-- **The Gram matrix in real form**, cosine–cosine:
`G_{(0,i),(0,j)} = δ/(4δ² + (gᵢ + gⱼ)²) + δ/(4δ² + (gᵢ − gⱼ)²)`. -/
theorem gram_cos_cos {ι : Type*} (δ : ℝ) (g : ι → ℝ) (i j : ι) :
    gram δ g (0, i) (0, j)
      = δ / (4 * δ ^ 2 + (g i + g j) ^ 2) + δ / (4 * δ ^ 2 + (g i - g j) ^ 2) := by
  simp only [gram, Matrix.of_apply, edgeUnit, Matrix.cons_val_zero, mul_one, map_one,
    div_eq_mul_inv, one_mul, Complex.add_re, (inv_rate _ _).1]
  ring

/-- **The Gram matrix in real form**, sine–sine:
`G_{(1,i),(1,j)} = δ/(4δ² + (gᵢ − gⱼ)²) − δ/(4δ² + (gᵢ + gⱼ)²)`. -/
theorem gram_sin_sin {ι : Type*} (δ : ℝ) (g : ι → ℝ) (i j : ι) :
    gram δ g (1, i) (1, j)
      = δ / (4 * δ ^ 2 + (g i - g j) ^ 2) - δ / (4 * δ ^ 2 + (g i + g j) ^ 2) := by
  simp only [gram, Matrix.of_apply, edgeUnit, Matrix.cons_val_one, Matrix.cons_val_zero,
    Complex.I_mul_I, Complex.conj_I, mul_neg, Complex.I_mul_I, neg_neg, div_eq_mul_inv,
    neg_one_mul, one_mul, Complex.add_re, Complex.neg_re, (inv_rate _ _).1]
  ring

/-- **The Gram matrix in real form**, cosine–sine: `G_{(0,i),(1,j)}` is
`((gᵢ + gⱼ)/(4δ² + (gᵢ + gⱼ)²) − (gᵢ − gⱼ)/(4δ² + (gᵢ − gⱼ)²))/2`. -/
theorem gram_cos_sin {ι : Type*} (δ : ℝ) (g : ι → ℝ) (i j : ι) :
    gram δ g (0, i) (1, j)
      = ((g i + g j) / (4 * δ ^ 2 + (g i + g j) ^ 2)
        - (g i - g j) / (4 * δ ^ 2 + (g i - g j) ^ 2)) / 2 := by
  simp only [gram, Matrix.of_apply, edgeUnit, Matrix.cons_val_one, Matrix.cons_val_zero,
    Complex.conj_I, one_mul, div_eq_mul_inv, Complex.add_re, neg_mul, Complex.neg_re,
    Complex.I_mul_re, (inv_rate _ _).2]
  ring

/-- **The Gram matrix in real form**, sine–cosine: `G_{(1,i),(0,j)}` is
`((gᵢ + gⱼ)/(4δ² + (gᵢ + gⱼ)²) + (gᵢ − gⱼ)/(4δ² + (gᵢ − gⱼ)²))/2`. -/
theorem gram_sin_cos {ι : Type*} (δ : ℝ) (g : ι → ℝ) (i j : ι) :
    gram δ g (1, i) (0, j)
      = ((g i + g j) / (4 * δ ^ 2 + (g i + g j) ^ 2)
        + (g i - g j) / (4 * δ ^ 2 + (g i - g j) ^ 2)) / 2 := by
  simp only [gram, Matrix.of_apply, edgeUnit, Matrix.cons_val_one, Matrix.cons_val_zero,
    map_one, mul_one, div_eq_mul_inv, Complex.add_re, Complex.I_mul_re, (inv_rate _ _).2]
  ring

/-! ### Combinations of edge functions -/

/-- The edge combination `∑ₖ xₖ edgeFnₖ`. -/
def comb {ι : Type*} [Fintype ι] (δ : ℝ) (g : ι → ℝ) (x : Fin 2 × ι → ℝ) (u : ℝ) : ℝ :=
  ∑ k, x k * edgeFn δ (g k.2) k.1 u

variable {ι : Type*} [Fintype ι]

/-- Edge combinations are continuous. -/
@[fun_prop] theorem continuous_comb (δ : ℝ) (g : ι → ℝ) (x : Fin 2 × ι → ℝ) :
    Continuous (comb δ g x) := by
  unfold comb; fun_prop

/-- `x · p(F, a) = ∫₀^a F · comb x`, for continuous `F`. -/
theorem dotProduct_pairVec (δ : ℝ) (g : ι → ℝ) {F : ℝ → ℝ} (hF : Continuous F)
    (x : Fin 2 × ι → ℝ) (a : ℝ) :
    x ⬝ᵥ pairVec δ g F a = ∫ u in (0 : ℝ)..a, F u * comb δ g x u := by
  unfold comb pairVec dotProduct
  simp_rw [Finset.mul_sum]
  rw [intervalIntegral.integral_finsetSum fun k _ =>
    (by fun_prop : Continuous fun u => F u * (x k * edgeFn δ (g k.2) k.1 u)).intervalIntegrable _ _]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun u _ => ?_
  ring

/-- **The pairing of an edge combination**: `p(comb x, b) = G_b x`. -/
theorem pairVec_comb (δ : ℝ) (g : ι → ℝ) (x : Fin 2 × ι → ℝ) (b : ℝ) :
    pairVec δ g (comb δ g x) b = gramOn δ g b *ᵥ x := by
  funext k
  unfold pairVec comb
  simp only [mulVec, dotProduct, gramOn, Matrix.of_apply, Finset.sum_mul]
  rw [intervalIntegral.integral_finsetSum fun l _ =>
    (by fun_prop : Continuous fun u => x l * edgeFn δ (g l.2) l.1 u
      * edgeFn δ (g k.2) k.1 u).intervalIntegrable _ _]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← intervalIntegral.integral_mul_const]
  refine intervalIntegral.integral_congr fun u _ => ?_
  ring

/-- **The quadratic form of a finite Gram matrix**: `xᵀ G_b x = ∫₀^b (comb x)²`. -/
theorem quad_gramOn (δ : ℝ) (g : ι → ℝ) (x : Fin 2 × ι → ℝ) (b : ℝ) :
    x ⬝ᵥ (gramOn δ g b *ᵥ x) = ∫ u in (0 : ℝ)..b, comb δ g x u ^ 2 := by
  rw [← pairVec_comb, dotProduct_pairVec δ g (continuous_comb δ g x)]
  simp only [sq]

/-- **Bessel's inequality on `[0, a]`**: for continuous `F` and `a ≥ 0`,
`2 x·p(F, a) − xᵀ G_a x ≤ ∫₀^a F²`. -/
theorem bessel (δ : ℝ) (g : ι → ℝ) {F : ℝ → ℝ} (hF : Continuous F) (x : Fin 2 × ι → ℝ) {a : ℝ}
    (ha : 0 ≤ a) :
    2 * (x ⬝ᵥ pairVec δ g F a) - x ⬝ᵥ (gramOn δ g a *ᵥ x) ≤ ∫ u in (0 : ℝ)..a, F u ^ 2 := by
  rw [dotProduct_pairVec δ g hF, quad_gramOn]
  have h0 : 0 ≤ ∫ u in (0 : ℝ)..a, (F u - comb δ g x u) ^ 2 :=
    intervalIntegral.integral_nonneg ha fun u _ => sq_nonneg _
  have hc := continuous_comb δ g x
  have e : ∫ u in (0 : ℝ)..a, (F u - comb δ g x u) ^ 2
      = (∫ u in (0 : ℝ)..a, F u ^ 2) - 2 * (∫ u in (0 : ℝ)..a, F u * comb δ g x u)
        + ∫ u in (0 : ℝ)..a, comb δ g x u ^ 2 := by
    have e1 : ∀ u, (F u - comb δ g x u) ^ 2
        = (F u ^ 2 - 2 * (F u * comb δ g x u)) + comb δ g x u ^ 2 := fun u => by ring
    simp_rw [e1]
    rw [intervalIntegral.integral_add ((by fun_prop : Continuous fun u =>
        F u ^ 2 - 2 * (F u * comb δ g x u)).intervalIntegrable _ _)
        ((by fun_prop : Continuous fun u => comb δ g x u ^ 2).intervalIntegrable _ _),
      intervalIntegral.integral_sub ((by fun_prop : Continuous fun u => F u ^ 2).intervalIntegrable
        _ _) ((by fun_prop : Continuous fun u => 2 * (F u * comb δ g x u)).intervalIntegrable _ _),
      intervalIntegral.integral_const_mul]
  linarith

/-- The quadratic forms of the finite Gram matrices converge to that of `gram`, for `δ > 0`. -/
theorem tendsto_quad_gramOn {δ : ℝ} (hδ : 0 < δ) (g : ι → ℝ) (x : Fin 2 × ι → ℝ) :
    Tendsto (fun b => x ⬝ᵥ (gramOn δ g b *ᵥ x)) atTop (𝓝 (x ⬝ᵥ (gram δ g *ᵥ x))) := by
  have hc : Continuous fun M : Matrix (Fin 2 × ι) (Fin 2 × ι) ℝ => x ⬝ᵥ (M *ᵥ x) :=
    continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const)
  exact (hc.tendsto _).comp (tendsto_gramOn hδ g)

/-- **The finite Gram matrices lie below `gram`**: `xᵀ G_a x ≤ xᵀ G x` for `a ≥ 0`, `δ > 0`. -/
theorem quad_gramOn_le {δ : ℝ} (hδ : 0 < δ) (g : ι → ℝ) (x : Fin 2 × ι → ℝ) {a : ℝ}
    (ha : 0 ≤ a) : x ⬝ᵥ (gramOn δ g a *ᵥ x) ≤ x ⬝ᵥ (gram δ g *ᵥ x) := by
  refine ge_of_tendsto (tendsto_quad_gramOn hδ g x) ?_
  filter_upwards [eventually_ge_atTop a] with b hb
  rw [quad_gramOn, quad_gramOn]
  exact intervalIntegral.integral_mono_interval le_rfl ha hb
    (Eventually.of_forall fun u => sq_nonneg _)
    ((by fun_prop : Continuous fun u => comb δ g x u ^ 2).intervalIntegrable _ _)

/-! ### Independence of the edge functions -/

/-- The character `u ↦ e^{iωu}` of the additive monoid `[0, ∞)`. -/
def chr (ω : ℝ) : Multiplicative NNReal →* ℂ where
  toFun x := Complex.exp (ω * ((Multiplicative.toAdd x : NNReal) : ℝ) * Complex.I)
  map_one' := by simp
  map_mul' x y := by
    rw [toAdd_mul, NNReal.coe_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring

/-- Distinct frequencies give distinct characters. -/
theorem chr_injective : Function.Injective chr := by
  intro ω ω' h
  by_contra hne
  have hd : 0 < |ω - ω'| := abs_pos.mpr (sub_ne_zero.mpr hne)
  obtain ⟨u, hu⟩ : ∃ u : NNReal, (u : ℝ) = π / |ω - ω'| := ⟨⟨π / |ω - ω'|, by positivity⟩, rfl⟩
  have h1 := congrArg (fun F => F (Multiplicative.ofAdd u)) h
  simp only [chr, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd, hu] at h1
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h1
  have hre : (ω - ω') * (π / |ω - ω'|) = 2 * π * n := by
    have := congrArg Complex.im hn
    simp [Complex.mul_im, Complex.mul_re] at this
    linear_combination this
  have habs : |(ω - ω') * (π / |ω - ω'|)| = π := by
    rw [abs_mul, abs_div, abs_abs, abs_of_pos Real.pi_pos]
    field_simp
  rw [hre, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)] at habs
  have h2 : (2 * |(n : ℤ)| : ℤ) = 1 := by
    have : (2 : ℝ) * |(n : ℝ)| = 1 := by
      have hπ := Real.pi_pos
      field_simp at habs
      nlinarith
    exact_mod_cast this
  omega

/-- **Distinct frequencies are independent on `[0, ∞)`**: if `∑ₖ dₖ e^{iωₖu} = 0` for every `u ≥ 0`
and `ω` is injective, then `d = 0`. -/
theorem eq_zero_of_sum_exp {K : Type*} [Fintype K] {ω : K → ℝ} (hω : Function.Injective ω)
    (d : K → ℂ) (h : ∀ u : ℝ, 0 ≤ u → ∑ k, d k * Complex.exp (ω k * u * Complex.I) = 0) :
    d = 0 := by
  have hli := (linearIndependent_monoidHom (Multiplicative NNReal) ℂ).comp
    (fun k => chr (ω k)) (chr_injective.comp hω)
  have hz := Fintype.linearIndependent_iff.mp hli d ?_
  · funext k; exact hz k
  · funext x
    simp only [Function.comp_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    exact h _ (NNReal.coe_nonneg _)

/-- The frequencies `±gᵢ` of the edge functions: `+gᵢ` for `e = 0`, `−gᵢ` for `e = 1`. -/
def freq (g : ι → ℝ) (k : Fin 2 × ι) : ℝ := ![g k.2, -g k.2] k.1

omit [Fintype ι] in
/-- For distinct positive ordinates the frequencies `±gᵢ` are distinct. -/
theorem freq_injective {g : ι → ℝ} (hg0 : ∀ i, 0 < g i) (hg : Function.Injective g) :
    Function.Injective (freq g) := by
  rintro ⟨e, i⟩ ⟨f, j⟩ h
  fin_cases e <;> fin_cases f <;> simp [freq] at h
  · rw [hg h]
  · linarith [hg0 i, hg0 j]
  · linarith [hg0 i, hg0 j]
  · rw [hg h]

/-- The exponential coefficients `(x₀ − ix₁)/2`, `(x₀ + ix₁)/2` of `x₀ cos + x₁ sin`. -/
def expCoef (x : Fin 2 × ι → ℝ) (k : Fin 2 × ι) : ℂ :=
  ![((x (0, k.2) : ℂ) - x (1, k.2) * Complex.I) / 2,
    ((x (0, k.2) : ℂ) + x (1, k.2) * Complex.I) / 2] k.1

/-- An edge combination is `e^{−δu}` times an exponential sum with frequencies `±gᵢ`. -/
theorem comb_eq (δ : ℝ) (g : ι → ℝ) (x : Fin 2 × ι → ℝ) (u : ℝ) :
    ((comb δ g x u : ℝ) : ℂ)
      = Real.exp (-(δ * u)) * ∑ k, expCoef x k * Complex.exp (freq g k * u * Complex.I) := by
  unfold comb
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, edgeFn_zero, edgeFn_one, expCoef, freq,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  push_cast
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e1 : Complex.exp ((g i : ℂ) * u * Complex.I)
      = Complex.cos ((g i : ℂ) * u) + Complex.sin ((g i : ℂ) * u) * Complex.I :=
    Complex.exp_mul_I _
  have e2 : Complex.exp (-(g i : ℂ) * u * Complex.I)
      = Complex.cos ((g i : ℂ) * u) - Complex.sin ((g i : ℂ) * u) * Complex.I := by
    rw [show -(g i : ℂ) * u * Complex.I = (-((g i : ℂ) * u)) * Complex.I by ring,
      Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
    ring
  rw [e1, e2]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- **The edge functions are independent on `[0, ∞)`**: for distinct positive ordinates, an edge
combination vanishing on `[0, ∞)` has zero coefficients. -/
theorem eq_zero_of_comb {δ : ℝ} {g : ι → ℝ} (hg0 : ∀ i, 0 < g i) (hg : Function.Injective g)
    {x : Fin 2 × ι → ℝ} (h : ∀ u, 0 ≤ u → comb δ g x u = 0) : x = 0 := by
  have hd := eq_zero_of_sum_exp (freq_injective hg0 hg) (expCoef x) fun u hu => by
    have h1 := comb_eq δ g x u
    rw [h u hu, Complex.ofReal_zero] at h1
    have h2 : (Real.exp (-(δ * u)) : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos _).ne'
    exact (mul_eq_zero.mp h1.symm).resolve_left h2
  have h0 : ∀ i, x (0, i) = 0 ∧ x (1, i) = 0 := by
    intro i
    have a0 := congr_fun hd (0, i)
    have a1 := congr_fun hd (1, i)
    simp only [expCoef, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply] at a0 a1
    have s := congrArg Complex.re (show ((x (0, i) : ℂ) - x (1, i) * Complex.I) / 2
      + ((x (0, i) : ℂ) + x (1, i) * Complex.I) / 2 = 0 by rw [a0, a1, add_zero])
    have t := congrArg Complex.im (show ((x (0, i) : ℂ) + x (1, i) * Complex.I) / 2
      - ((x (0, i) : ℂ) - x (1, i) * Complex.I) / 2 = 0 by rw [a0, a1, sub_zero])
    simp at s t
    exact ⟨by linarith, by linarith⟩
  funext ⟨e, i⟩
  fin_cases e
  · exact (h0 i).1
  · exact (h0 i).2

/-- **The Gram matrix of distinct positive ordinates is positive definite**, for `δ > 0`. -/
theorem gram_posDef {δ : ℝ} (hδ : 0 < δ) {g : ι → ℝ} (hg0 : ∀ i, 0 < g i)
    (hg : Function.Injective g) : (gram δ g).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_
  · ext k l
    simp only [conjTranspose_apply, star_trivial]
    exact gram_comm δ g l k
  · simp only [star_trivial]
    obtain ⟨u₀, hu₀, hne⟩ : ∃ u₀, 0 ≤ u₀ ∧ comb δ g x u₀ ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hx (eq_zero_of_comb hg0 hg hc)
    have h1 : 0 < ∫ u in (0 : ℝ)..u₀ + 1, comb δ g x u ^ 2 :=
      intervalIntegral.integral_pos (by linarith)
        (by fun_prop : Continuous fun u => comb δ g x u ^ 2).continuousOn
        (fun u _ => sq_nonneg _)
        ⟨u₀, ⟨hu₀, by linarith⟩, lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hne))⟩
    rw [← quad_gramOn] at h1
    exact h1.trans_le (quad_gramOn_le hδ g x (by linarith))

end Cvs.StepA.Edge.DampedEdgeGram
