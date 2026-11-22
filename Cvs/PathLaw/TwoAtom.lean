/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/
import Cvs.PathLaw.Schur
import Cvs.Zeta.WeilPositivityStatement

/-!
# Two atoms on a window: the weighted Schur bound and the two-atom path law

**Weighted Schur bound.** For shifts `ℓᵢ` with weights `wᵢ ≥ 0`, take a weight `v` on a window `W`,
bounded between `m > 0` and `M`. Suppose it satisfies `∑ᵢ wᵢ (v(s + ℓᵢ) + v(s − ℓᵢ)) ≤ μ v(s)` on `W`,
with terms whose point leaves `W` dropped. Then it bounds the joint shift form:
`|∑ᵢ 2wᵢ (f ⋆ f)(ℓᵢ)| ≤ μ ∫ f²` for every `L²` function `f` vanishing off `W`. Each pair is split by
weighted AM-GM with the ratio of the weights at its two ends, and the second halves are moved back by
translation.

**Two-atom path law.** For shifts `a < b < L ≤ 2a` with `L ≤ 2b − a`, the cut has a four-piece class,
the path `(a, L+a−b] — (0, L−b] — (b, L] — (b−a, L−a]` with links `wa, wb, wa`. Its Perron vector
`(wa, μ, μ, wa)`, with `μ = (wb + √(wb² + 4wa²))/2`, is a weight for the Schur bound. So the two
shifts move `∫ f²` by at most `μ`: more than either alone, less than their sum, and
`two_shift_attained` shows that `μ` is attained.

`selfConvolution` is the one used to build the prime side of the windowed Weil form
(`Cvs.Zeta.Explicit.Weil.selfConvolution`).
-/

noncomputable section

open MeasureTheory Cvs.Zeta.Explicit.Weil

namespace Cvs.PathLaw.TwoAtom

/-- The forward coefficient of shift `ℓ`: `v(s + ℓ)/v(s)` on `W`, with the term dropped when `s + ℓ` leaves `W`. -/
def fwd (W : Set ℝ) (v : ℝ → ℝ) (ℓ : ℝ) : ℝ → ℝ :=
  W.indicator fun s => W.indicator v (s + ℓ) / v s

/-- The backward coefficient of shift `ℓ`: `v(s − ℓ)/v(s)` on `W`, with the term dropped when `s − ℓ` leaves `W`. -/
def bwd (W : Set ℝ) (v : ℝ → ℝ) (ℓ : ℝ) : ℝ → ℝ :=
  W.indicator fun s => W.indicator v (s - ℓ) / v s

section Coeff

variable {W : Set ℝ} {v : ℝ → ℝ} {m M : ℝ}

theorem indicator_nonneg (hm : 0 < m) (hvlo : ∀ x ∈ W, m ≤ v x) (y : ℝ) : 0 ≤ W.indicator v y := by
  by_cases hy : y ∈ W
  · rw [Set.indicator_of_mem hy]; linarith [hvlo y hy]
  · rw [Set.indicator_of_notMem hy]

theorem indicator_le_abs (hvhi : ∀ x ∈ W, v x ≤ M) (y : ℝ) : W.indicator v y ≤ |M| := by
  by_cases hy : y ∈ W
  · rw [Set.indicator_of_mem hy]; exact (hvhi y hy).trans (le_abs_self M)
  · rw [Set.indicator_of_notMem hy]; exact abs_nonneg M

/-- A dropped-or-kept ratio `1_W(s)·v(y)1_W(y)/v(s)` lies in `[0, |M|/m]`. -/
theorem ratio_mem (hm : 0 < m) (hvlo : ∀ x ∈ W, m ≤ v x) (hvhi : ∀ x ∈ W, v x ≤ M) (y s : ℝ) :
    0 ≤ (W.indicator fun s => W.indicator v y / v s) s ∧
      (W.indicator fun s => W.indicator v y / v s) s ≤ |M| / m := by
  by_cases hs : s ∈ W
  · rw [Set.indicator_of_mem hs]
    have hvs : m ≤ v s := hvlo s hs
    have hpos : 0 < v s := by linarith
    have h0 := indicator_nonneg hm hvlo y
    have h1 := indicator_le_abs hvhi y
    refine ⟨div_nonneg h0 hpos.le, ?_⟩
    calc W.indicator v y / v s ≤ |M| / v s := div_le_div_of_nonneg_right h1 hpos.le
      _ ≤ |M| / m := div_le_div_of_nonneg_left (abs_nonneg M) hm hvs
  · rw [Set.indicator_of_notMem hs]
    exact ⟨le_rfl, div_nonneg (abs_nonneg M) hm.le⟩

theorem fwd_mem (hm : 0 < m) (hvlo : ∀ x ∈ W, m ≤ v x) (hvhi : ∀ x ∈ W, v x ≤ M) (ℓ x : ℝ) :
    0 ≤ fwd W v ℓ x ∧ fwd W v ℓ x ≤ |M| / m := by
  have e : fwd W v ℓ x = (W.indicator fun s => W.indicator v (x + ℓ) / v s) x := by
    by_cases hx : x ∈ W
    · rw [fwd, Set.indicator_of_mem hx, Set.indicator_of_mem hx]
    · rw [fwd, Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
  rw [e]; exact ratio_mem hm hvlo hvhi (x + ℓ) x

theorem bwd_mem (hm : 0 < m) (hvlo : ∀ x ∈ W, m ≤ v x) (hvhi : ∀ x ∈ W, v x ≤ M) (ℓ x : ℝ) :
    0 ≤ bwd W v ℓ x ∧ bwd W v ℓ x ≤ |M| / m := by
  have e : bwd W v ℓ x = (W.indicator fun s => W.indicator v (x - ℓ) / v s) x := by
    by_cases hx : x ∈ W
    · rw [bwd, Set.indicator_of_mem hx, Set.indicator_of_mem hx]
    · rw [bwd, Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
  rw [e]; exact ratio_mem hm hvlo hvhi (x - ℓ) x

theorem measurable_fwd (hW : MeasurableSet W) (hv : Measurable v) (ℓ : ℝ) : Measurable (fwd W v ℓ) :=
  (((hv.indicator hW).comp (measurable_add_const ℓ)).div hv).indicator hW

theorem measurable_bwd (hW : MeasurableSet W) (hv : Measurable v) (ℓ : ℝ) : Measurable (bwd W v ℓ) :=
  (((hv.indicator hW).comp (measurable_sub_const ℓ)).div hv).indicator hW

end Coeff

variable {ι : Type*}

/-- **The weighted Schur bound for several shifts on a window.** If `v` on `W` lies between `m > 0` and `M` and
`∑ᵢ wᵢ (1_W v(s + ℓᵢ) + 1_W v(s − ℓᵢ)) ≤ μ v(s)` at every `s ∈ W`, then `|∑ᵢ 2wᵢ (f ⋆ f)(ℓᵢ)| ≤ μ ∫ f²` for every
`f ∈ L²` vanishing off `W`. -/
theorem abs_sum_selfConvolution_le (s : Finset ι) (ℓ w : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    {W : Set ℝ} (hW : MeasurableSet W) {v : ℝ → ℝ} (hv : Measurable v) {m M : ℝ} (hm : 0 < m)
    (hvlo : ∀ x ∈ W, m ≤ v x) (hvhi : ∀ x ∈ W, v x ≤ M) {μ : ℝ}
    (hμ : ∀ x ∈ W, ∑ i ∈ s, w i * (W.indicator v (x + ℓ i) + W.indicator v (x - ℓ i)) ≤ μ * v x)
    {f : ℝ → ℝ} (hfW : ∀ x ∉ W, f x = 0) (hf : MemLp f 2) :
    |∑ i ∈ s, 2 * w i * selfConvolution f (ℓ i)| ≤ μ * ∫ x, f x ^ 2 := by
  have hf2 : Integrable (fun x => f x ^ 2) := hf.integrable_sq
  have hbf : ∀ ℓ x, |fwd W v ℓ x| ≤ |M| / m := fun ℓ x => by
    rw [abs_of_nonneg (fwd_mem hm hvlo hvhi ℓ x).1]; exact (fwd_mem hm hvlo hvhi ℓ x).2
  have hbb : ∀ ℓ x, |bwd W v ℓ x| ≤ |M| / m := fun ℓ x => by
    rw [abs_of_nonneg (bwd_mem hm hvlo hvhi ℓ x).1]; exact (bwd_mem hm hvlo hvhi ℓ x).2
  have hfwd0 : ∀ ℓ x, 0 ≤ fwd W v ℓ x := fun ℓ x => (fwd_mem hm hvlo hvhi ℓ x).1
  have hbwd0 : ∀ ℓ x, 0 ≤ bwd W v ℓ x := fun ℓ x => (bwd_mem hm hvlo hvhi ℓ x).1
  have hig : ∀ ℓ, Integrable (fun x => fwd W v ℓ x * f x ^ 2) := fun ℓ =>
    hf2.bdd_mul (measurable_fwd hW hv ℓ).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hbf ℓ x)
  have hih : ∀ ℓ, Integrable (fun x => bwd W v ℓ x * f x ^ 2) := fun ℓ =>
    hf2.bdd_mul (measurable_bwd hW hv ℓ).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hbb ℓ x)
  -- each pair, split by weighted AM-GM with the ratio of the weights at its ends
  have hpt : ∀ ℓ x, 2 * |f x * f (x + ℓ)|
      ≤ fwd W v ℓ x * f x ^ 2 + bwd W v ℓ (x + ℓ) * f (x + ℓ) ^ 2 := by
    intro ℓ x
    have hrhs : 0 ≤ fwd W v ℓ x * f x ^ 2 + bwd W v ℓ (x + ℓ) * f (x + ℓ) ^ 2 :=
      add_nonneg (mul_nonneg (hfwd0 ℓ x) (sq_nonneg _)) (mul_nonneg (hbwd0 ℓ _) (sq_nonneg _))
    by_cases hx : x ∈ W
    · by_cases hxl : x + ℓ ∈ W
      · have hv1 : 0 < v x := lt_of_lt_of_le hm (hvlo x hx)
        have hv2 : 0 < v (x + ℓ) := lt_of_lt_of_le hm (hvlo _ hxl)
        have hf1 : fwd W v ℓ x = v (x + ℓ) / v x := by
          rw [fwd, Set.indicator_of_mem hx, Set.indicator_of_mem hxl]
        have hb1 : bwd W v ℓ (x + ℓ) = v x / v (x + ℓ) := by
          rw [bwd, Set.indicator_of_mem hxl, add_sub_cancel_right, Set.indicator_of_mem hx]
        rw [hf1, hb1]
        have h := Cvs.PathLaw.two_abs_mul_le (div_pos hv2 hv1) (f x) (f (x + ℓ))
        have he : f (x + ℓ) ^ 2 / (v (x + ℓ) / v x) = v x / v (x + ℓ) * f (x + ℓ) ^ 2 := by
          field_simp
        linarith [he ▸ h]
      · rw [show f x * f (x + ℓ) = 0 by rw [hfW _ hxl, mul_zero], abs_zero, mul_zero]; exact hrhs
    · rw [show f x * f (x + ℓ) = 0 by rw [hfW _ hx, zero_mul], abs_zero, mul_zero]; exact hrhs
  have hpair : ∀ ℓ, |2 * selfConvolution f ℓ| ≤ ∫ x, (fwd W v ℓ x + bwd W v ℓ x) * f x ^ 2 := by
    intro ℓ
    have hup : Integrable (fun x => fwd W v ℓ x * f x ^ 2 + bwd W v ℓ (x + ℓ) * f (x + ℓ) ^ 2) :=
      (hig ℓ).add ((hih ℓ).comp_add_right ℓ)
    calc |2 * selfConvolution f ℓ| = |∫ x, 2 * (f x * f (x + ℓ))| := by
          rw [selfConvolution, integral_const_mul]
      _ ≤ ∫ x, |2 * (f x * f (x + ℓ))| := abs_integral_le_integral_abs
      _ ≤ ∫ x, (fwd W v ℓ x * f x ^ 2 + bwd W v ℓ (x + ℓ) * f (x + ℓ) ^ 2) := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => abs_nonneg _) hup
            (Filter.Eventually.of_forall fun x => ?_)
          show |2 * (f x * f (x + ℓ))| ≤ fwd W v ℓ x * f x ^ 2 + bwd W v ℓ (x + ℓ) * f (x + ℓ) ^ 2
          rw [abs_mul, abs_two]
          exact hpt ℓ x
      _ = (∫ x, fwd W v ℓ x * f x ^ 2) + ∫ x, bwd W v ℓ x * f x ^ 2 := by
          rw [integral_add (hig ℓ) ((hih ℓ).comp_add_right ℓ),
            integral_add_right_eq_self (fun x => bwd W v ℓ x * f x ^ 2) ℓ]
      _ = ∫ x, (fwd W v ℓ x + bwd W v ℓ x) * f x ^ 2 := by
          rw [← integral_add (hig ℓ) (hih ℓ)]
          exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp only; ring)
  -- the coefficients sum to at most `μ` on `W`, and `f` vanishes off it
  have hcoef : ∀ x, (∑ i ∈ s, w i * (fwd W v (ℓ i) x + bwd W v (ℓ i) x)) * f x ^ 2 ≤ μ * f x ^ 2 := by
    intro x
    by_cases hx : x ∈ W
    · have hv1 : 0 < v x := lt_of_lt_of_le hm (hvlo x hx)
      have hsum : ∑ i ∈ s, w i * (fwd W v (ℓ i) x + bwd W v (ℓ i) x)
          = (∑ i ∈ s, w i * (W.indicator v (x + ℓ i) + W.indicator v (x - ℓ i))) / v x := by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [fwd, bwd, Set.indicator_of_mem hx, Set.indicator_of_mem hx]
        field_simp
      rw [hsum]
      have hle : (∑ i ∈ s, w i * (W.indicator v (x + ℓ i) + W.indicator v (x - ℓ i))) / v x ≤ μ := by
        rw [div_le_iff₀ hv1]; exact hμ x hx
      exact mul_le_mul_of_nonneg_right hle (sq_nonneg _)
    · rw [hfW x hx]; simp
  have hF : ∀ i ∈ s, Integrable (fun x => w i * ((fwd W v (ℓ i) x + bwd W v (ℓ i) x) * f x ^ 2)) :=
    fun i _ => (((hig (ℓ i)).add (hih (ℓ i))).congr
      (Filter.Eventually.of_forall fun x => by simp only [Pi.add_apply]; ring)).const_mul (w i)
  have hsumF : (fun x => (∑ i ∈ s, w i * (fwd W v (ℓ i) x + bwd W v (ℓ i) x)) * f x ^ 2)
      = fun x => ∑ i ∈ s, w i * ((fwd W v (ℓ i) x + bwd W v (ℓ i) x) * f x ^ 2) := by
    funext x
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  calc |∑ i ∈ s, 2 * w i * selfConvolution f (ℓ i)|
      ≤ ∑ i ∈ s, |2 * w i * selfConvolution f (ℓ i)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ s, w i * |2 * selfConvolution f (ℓ i)| := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [show 2 * w i * selfConvolution f (ℓ i) = w i * (2 * selfConvolution f (ℓ i)) by ring, abs_mul,
          abs_of_nonneg (hw i hi)]
    _ ≤ ∑ i ∈ s, w i * ∫ x, (fwd W v (ℓ i) x + bwd W v (ℓ i) x) * f x ^ 2 :=
        Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hpair (ℓ i)) (hw i hi)
    _ = ∫ x, (∑ i ∈ s, w i * (fwd W v (ℓ i) x + bwd W v (ℓ i) x)) * f x ^ 2 := by
        rw [hsumF, integral_finsetSum s hF]
        exact Finset.sum_congr rfl fun i _ => (integral_const_mul (w i) _).symm
    _ ≤ ∫ x, μ * f x ^ 2 := by
        refine integral_mono ?_ (hf2.const_mul μ) hcoef
        rw [hsumF]
        exact integrable_finsetSum s hF
    _ = μ * ∫ x, f x ^ 2 := integral_const_mul μ _


/-! ### The joint constant of a path with links `a, b, a` -/

/-- The top eigenvalue of the path with links `a, b, a`: `(b + √(b² + 4a²))/2`. -/
def jointNorm (a b : ℝ) : ℝ := (b + Real.sqrt (b ^ 2 + 4 * a ^ 2)) / 2

theorem sqrt_sq_eq (a b : ℝ) : Real.sqrt (b ^ 2 + 4 * a ^ 2) ^ 2 = b ^ 2 + 4 * a ^ 2 :=
  Real.sq_sqrt (by positivity)

/-- `μ² = bμ + a²`: the Perron relation of the path. -/
theorem jointNorm_sq (a b : ℝ) : jointNorm a b * jointNorm a b = b * jointNorm a b + a * a := by
  have h := sqrt_sq_eq a b
  unfold jointNorm
  nlinarith [h]

theorem lt_jointNorm_left {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : a < jointNorm a b := by
  have h := sqrt_sq_eq a b
  have hr : 0 ≤ Real.sqrt (b ^ 2 + 4 * a ^ 2) := Real.sqrt_nonneg _
  have h2a : 2 * a ≤ Real.sqrt (b ^ 2 + 4 * a ^ 2) := by nlinarith [sq_nonneg b]
  unfold jointNorm
  linarith

theorem lt_jointNorm_right {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : b < jointNorm a b := by
  have h := sqrt_sq_eq a b
  have hr : 0 ≤ Real.sqrt (b ^ 2 + 4 * a ^ 2) := Real.sqrt_nonneg _
  have hbr : b < Real.sqrt (b ^ 2 + 4 * a ^ 2) := by nlinarith [sq_nonneg a, mul_pos ha ha]
  unfold jointNorm
  linarith

/-- **The primes interfere**: the path's top eigenvalue is below the sum of its two links, `μ < a + b`. -/
theorem jointNorm_lt_add {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : jointNorm a b < a + b := by
  have h := sqrt_sq_eq a b
  have hr : 0 ≤ Real.sqrt (b ^ 2 + 4 * a ^ 2) := Real.sqrt_nonneg _
  have hlt : Real.sqrt (b ^ 2 + 4 * a ^ 2) < b + 2 * a := by nlinarith [mul_pos ha hb]
  unfold jointNorm
  linarith

/-! ### Two shifts on a window: the path's Perron vector as the weight -/

section Weight

variable (a b L wa wb : ℝ)

/-- The weight on `(0, L]` for shifts `a < b`: `wa` on the path's end pieces `(b − a, L − a]` and `(a, L + a − b]`,
and `μ = jointNorm wa wb` elsewhere. -/
def weight2 : ℝ → ℝ := fun s =>
  if s ∈ Set.Ioc (b - a) (L - a) ∨ s ∈ Set.Ioc a (L + a - b) then wa else jointNorm wa wb

theorem measurable_weight2 : Measurable (weight2 a b L wa wb) :=
  Measurable.ite (measurableSet_Ioc.union measurableSet_Ioc) measurable_const measurable_const

end Weight

/-- **The weight is sub-eigen on the window.** For `a < b < L ≤ 2a`, `L ≤ 2b − a`, links `wa, wb > 0`, `W = (0, L]`
and `μ = jointNorm wa wb`: `wa (v(s + a) + v(s − a)) + wb (v(s + b) + v(s − b)) ≤ μ v(s)` at every `s ∈ W`, terms
leaving `W` dropped; checked on the seven cut pieces between `0, L−b, b−a, L−a, a, L+a−b, b, L`. -/
theorem weight2_cond {a b L wa wb : ℝ} (hab : a < b) (hbL : b < L) (hL2a : L ≤ 2 * a)
    (hL2b : L ≤ 2 * b - a) (hwa : 0 < wa) (hwb : 0 < wb) {s : ℝ} (hs : s ∈ Set.Ioc (0 : ℝ) L) :
    wa * ((Set.Ioc (0 : ℝ) L).indicator (weight2 a b L wa wb) (s + a)
        + (Set.Ioc (0 : ℝ) L).indicator (weight2 a b L wa wb) (s - a))
      + wb * ((Set.Ioc (0 : ℝ) L).indicator (weight2 a b L wa wb) (s + b)
        + (Set.Ioc (0 : ℝ) L).indicator (weight2 a b L wa wb) (s - b))
      ≤ jointNorm wa wb * weight2 a b L wa wb s := by
  have hsq := jointNorm_sq wa wb
  have haμ := lt_jointNorm_left hwa hwb
  set μ := jointNorm wa wb with hμ
  have hμpos : 0 < μ := lt_trans hwa haμ
  have hamu : wa * μ ≤ μ * μ := mul_le_mul_of_nonneg_right haμ.le hμpos.le
  obtain ⟨hs0, hsL⟩ := hs
  have inW : ∀ y, 0 < y → y ≤ L → (Set.Ioc (0 : ℝ) L).indicator (weight2 a b L wa wb) y = weight2 a b L wa wb y :=
    fun y h1 h2 => Set.indicator_of_mem (show y ∈ Set.Ioc (0 : ℝ) L from ⟨h1, h2⟩) _
  have loW : ∀ y, y ≤ 0 → (Set.Ioc (0 : ℝ) L).indicator (weight2 a b L wa wb) y = 0 := fun y h =>
    Set.indicator_of_notMem (fun hm : y ∈ Set.Ioc (0 : ℝ) L => by linarith [hm.1]) _
  have hiW : ∀ y, L < y → (Set.Ioc (0 : ℝ) L).indicator (weight2 a b L wa wb) y = 0 := fun y h =>
    Set.indicator_of_notMem (fun hm : y ∈ Set.Ioc (0 : ℝ) L => by linarith [hm.2]) _
  have vEnd1 : ∀ y, b - a < y → y ≤ L - a → weight2 a b L wa wb y = wa := fun y h1 h2 =>
    ite_eq_left (Or.inl ⟨h1, h2⟩)
  have vEnd2 : ∀ y, a < y → y ≤ L + a - b → weight2 a b L wa wb y = wa := fun y h1 h2 =>
    ite_eq_left (Or.inr ⟨h1, h2⟩)
  have vMid : ∀ y, (y ≤ b - a ∨ L - a < y) → (y ≤ a ∨ L + a - b < y) → weight2 a b L wa wb y = μ :=
    fun y h1 h2 => ite_eq_right fun hm => by
      rcases hm with hm | hm
      · rcases h1 with h1 | h1 <;> linarith [hm.1, hm.2]
      · rcases h2 with h2 | h2 <;> linarith [hm.1, hm.2]
  rcases le_or_gt s (L - b) with h0 | h0
  · -- (0, L − b]: neighbours (a, L + a − b] at `wa` and (b, L] at `μ`
    rw [inW (s + a) (by linarith) (by linarith), vEnd2 (s + a) (by linarith) (by linarith),
      loW (s - a) (by linarith), inW (s + b) (by linarith) (by linarith),
      vMid (s + b) (Or.inr (by linarith)) (Or.inr (by linarith)), loW (s - b) (by linarith),
      vMid s (Or.inl (by linarith)) (Or.inl (by linarith))]
    nlinarith [hsq]
  rcases le_or_gt s (b - a) with h1 | h1
  · -- (L − b, b − a]: one neighbour (L + a − b, b] at `μ`
    rw [inW (s + a) (by linarith) (by linarith), vMid (s + a) (Or.inr (by linarith)) (Or.inr (by linarith)),
      loW (s - a) (by linarith), hiW (s + b) (by linarith), loW (s - b) (by linarith),
      vMid s (Or.inl h1) (Or.inl (by linarith))]
    nlinarith [hamu]
  rcases le_or_gt s (L - a) with h2 | h2
  · -- (b − a, L − a]: one neighbour (b, L] at `μ`; the weight is `wa`
    rw [inW (s + a) (by linarith) (by linarith), vMid (s + a) (Or.inr (by linarith)) (Or.inr (by linarith)),
      loW (s - a) (by linarith), hiW (s + b) (by linarith), loW (s - b) (by linarith), vEnd1 s h1 h2]
    nlinarith
  rcases le_or_gt s a with h3 | h3
  · -- (L − a, a]: isolated
    rw [hiW (s + a) (by linarith), loW (s - a) (by linarith), hiW (s + b) (by linarith),
      loW (s - b) (by linarith), vMid s (Or.inr h2) (Or.inl h3)]
    nlinarith
  rcases le_or_gt s (L + a - b) with h4 | h4
  · -- (a, L + a − b]: one neighbour (0, L − b] at `μ`; the weight is `wa`
    rw [hiW (s + a) (by linarith), inW (s - a) (by linarith) (by linarith),
      vMid (s - a) (Or.inl (by linarith)) (Or.inl (by linarith)), hiW (s + b) (by linarith),
      loW (s - b) (by linarith), vEnd2 s h3 h4]
    nlinarith
  rcases le_or_gt s b with h5 | h5
  · -- (L + a − b, b]: one neighbour (L − b, b − a] at `μ`
    rw [hiW (s + a) (by linarith), inW (s - a) (by linarith) (by linarith),
      vMid (s - a) (Or.inl (by linarith)) (Or.inl (by linarith)), hiW (s + b) (by linarith),
      loW (s - b) (by linarith), vMid s (Or.inr (by linarith)) (Or.inr h4)]
    nlinarith [hamu]
  · -- (b, L]: neighbours (b − a, L − a] at `wa` and (0, L − b] at `μ`
    rw [hiW (s + a) (by linarith), inW (s - a) (by linarith) (by linarith), vEnd1 (s - a) (by linarith)
      (by linarith), hiW (s + b) (by linarith), inW (s - b) (by linarith) (by linarith),
      vMid (s - b) (Or.inl (by linarith)) (Or.inl (by linarith)), vMid s (Or.inr (by linarith)) (Or.inr (by linarith))]
    nlinarith [hsq]

/-- **The two-shift path law.** For shifts `a < b < L ≤ 2a` with `L ≤ 2b − a`, links `wa, wb > 0` and `f ∈ L²`
vanishing off `(0, L]`: `|2wa (f ⋆ f)(a) + 2wb (f ⋆ f)(b)| ≤ μ ∫ f²`, `μ = (wb + √(wb² + 4wa²))/2`. -/
theorem abs_two_shift_le {a b L wa wb : ℝ} (hab : a < b) (hbL : b < L) (hL2a : L ≤ 2 * a)
    (hL2b : L ≤ 2 * b - a) (hwa : 0 < wa) (hwb : 0 < wb) {f : ℝ → ℝ}
    (hfW : ∀ x ∉ Set.Ioc (0 : ℝ) L, f x = 0) (hf : MemLp f 2) :
    |2 * wa * selfConvolution f a + 2 * wb * selfConvolution f b| ≤ jointNorm wa wb * ∫ x, f x ^ 2 := by
  have haμ := lt_jointNorm_left hwa hwb
  have h := abs_sum_selfConvolution_le (Finset.univ : Finset (Fin 2))
    ![a, b] ![wa, wb] (fun i _ => by fin_cases i <;> simp [hwa.le, hwb.le])
    measurableSet_Ioc (measurable_weight2 a b L wa wb) (m := wa) (M := jointNorm wa wb) hwa
    (fun x _ => by
      unfold weight2; split_ifs
      · exact le_rfl
      · exact haμ.le)
    (fun x _ => by
      unfold weight2; split_ifs
      · exact haμ.le
      · exact le_rfl)
    (fun x hx => by
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      exact weight2_cond hab hbL hL2a hL2b hwa hwb hx)
    hfW hf
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  exact h


/-! ### Attainment: the Perron test function on the four-piece path -/

section Attain

/-- The indicator of the box `(t, t + δ]`. -/
def box (δ t : ℝ) : ℝ → ℝ := (Set.Ioc t (t + δ)).indicator fun _ => (1 : ℝ)

theorem box_apply (δ t x : ℝ) : box δ t x = if t < x ∧ x ≤ t + δ then 1 else 0 := by
  simp [box, Set.indicator_apply, Set.mem_Ioc]

/-- A box and the box exactly `ℓ` later: the product is the first box. -/
theorem box_mul_box_link {δ s ℓ : ℝ} (x : ℝ) : box δ s x * box δ (s + ℓ) (x + ℓ) = box δ s x := by
  rw [box_apply, box_apply]
  by_cases hx : s < x ∧ x ≤ s + δ
  · rw [ite_eq_left hx, ite_eq_left ⟨by linarith [hx.1], by linarith [hx.2]⟩, mul_one]
  · rw [ite_eq_right hx, zero_mul]

/-- Boxes whose offset differs from `ℓ` by at least the width do not meet. -/
theorem box_mul_box_gap {δ s t ℓ : ℝ} (h : δ ≤ |t - s - ℓ|) (x : ℝ) : box δ s x * box δ t (x + ℓ) = 0 := by
  rw [box_apply, box_apply]
  by_cases h1 : s < x ∧ x ≤ s + δ
  · by_cases h2 : t < x + ℓ ∧ x + ℓ ≤ t + δ
    · exfalso
      rcases le_abs.mp h with h3 | h3 <;> linarith [h1.1, h1.2, h2.1, h2.2]
    · rw [ite_eq_left h1, ite_eq_right h2, mul_zero]
  · rw [ite_eq_right h1, zero_mul]

theorem integrable_box (δ t : ℝ) : Integrable (box δ t) :=
  memLp_one_iff_integrable.1
    (memLp_indicator_const 1 measurableSet_Ioc.nullMeasurableSet (1 : ℝ) (Or.inr (by simp [Real.volume_Ioc])))

theorem memLp_box (δ t : ℝ) : MemLp (box δ t) 2 :=
  memLp_indicator_const 2 measurableSet_Ioc.nullMeasurableSet (1 : ℝ) (Or.inr (by simp [Real.volume_Ioc]))

theorem integral_box {δ : ℝ} (hδ : 0 ≤ δ) (t : ℝ) : ∫ x, box δ t x = δ := by
  rw [box, integral_indicator_const _ measurableSet_Ioc, Real.volume_real_Ioc_of_le (by linarith),
    smul_eq_mul, mul_one]
  ring

/-- A finite combination of boxes of common width `δ`, at offsets `t i` with coefficients `c i`. -/
def boxSum {n : ℕ} (δ : ℝ) (t c : Fin n → ℝ) : ℝ → ℝ := fun x => ∑ i, c i * box δ (t i) x

/-- **The shifted pairing of a box combination.** Let `lk i j` record whether box `j` sits exactly `ℓ` after box
`i` (`lk i j = δ`) or is at least `δ` away from that position (`lk i j = 0`). Then
`∫ f(x) f(x + ℓ) = ∑ᵢⱼ cᵢ cⱼ lkᵢⱼ`. -/
theorem integral_boxSum_shift {n : ℕ} {δ ℓ : ℝ} (hδ : 0 < δ) (t c : Fin n → ℝ) (lk : Fin n → Fin n → ℝ)
    (hlk : ∀ i j, (t j = t i + ℓ ∧ lk i j = δ) ∨ (δ ≤ |t j - t i - ℓ| ∧ lk i j = 0)) :
    ∫ x, boxSum δ t c x * boxSum δ t c (x + ℓ) = ∑ i, ∑ j, c i * c j * lk i j := by
  have hpt : ∀ x, boxSum δ t c x * boxSum δ t c (x + ℓ)
      = ∑ i, ∑ j, (c i * c j * (lk i j / δ)) * box δ (t i) x := by
    intro x
    simp only [boxSum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rcases hlk i j with ⟨ht, hl⟩ | ⟨hg, hl⟩
    · have h := box_mul_box_link (δ := δ) (s := t i) (ℓ := ℓ) x
      rw [← ht] at h
      rw [hl, div_self hδ.ne']
      calc c i * box δ (t i) x * (c j * box δ (t j) (x + ℓ))
          = c i * c j * (box δ (t i) x * box δ (t j) (x + ℓ)) := by ring
        _ = _ := by rw [h]; ring
    · have h := box_mul_box_gap (x := x) hg
      rw [hl, zero_div]
      calc c i * box δ (t i) x * (c j * box δ (t j) (x + ℓ))
          = c i * c j * (box δ (t i) x * box δ (t j) (x + ℓ)) := by ring
        _ = _ := by rw [h]; ring
  have hint : ∀ i j, Integrable fun x => (c i * c j * (lk i j / δ)) * box δ (t i) x :=
    fun i j => (integrable_box δ (t i)).const_mul _
  simp_rw [hpt]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => hint i j]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, integral_box hδ.le]
  field_simp

/-- **The two-atom law is attained.** Under the hypotheses of `abs_two_shift_le`, the Perron test function
`wa 1_{J+a} + μ 1_J + μ 1_{J+b} + wa 1_{J+b−a}` on a short box `J ⊂ (0, L − b]` gives equality:
`2wa (f ⋆ f)(a) + 2wb (f ⋆ f)(b) = μ ∫ f²`, with `μ = jointNorm wa wb` and `∫ f² > 0`. So `μ` is the norm of
the two-shift form, not only a bound on it. -/
theorem two_shift_attained {a b L wa wb : ℝ} (hab : a < b) (hbL : b < L) (hL2a : L ≤ 2 * a)
    (hL2b : L ≤ 2 * b - a) (hwa : 0 < wa) (hwb : 0 < wb) :
    ∃ f : ℝ → ℝ, (∀ x ∉ Set.Ioc (0 : ℝ) L, f x = 0) ∧ MemLp f 2 ∧ 0 < ∫ x, f x ^ 2 ∧
      2 * wa * selfConvolution f a + 2 * wb * selfConvolution f b = jointNorm wa wb * ∫ x, f x ^ 2 := by
  have hμpos : 0 < jointNorm wa wb := lt_trans hwb (lt_jointNorm_right hwa hwb)
  have hsq := jointNorm_sq wa wb
  set μ := jointNorm wa wb
  set δ := min (L - b) (min (b - a) (2 * a - b)) with hδdef
  have hδ : 0 < δ := lt_min (by linarith) (lt_min (by linarith) (by linarith))
  have hδ1 : δ ≤ L - b := min_le_left _ _
  have hδ2 : δ ≤ b - a := (min_le_right _ _).trans (min_le_left _ _)
  have hδ3 : δ ≤ 2 * a - b := (min_le_right _ _).trans (min_le_right _ _)
  let t : Fin 4 → ℝ := ![a, 0, b, b - a]
  let c : Fin 4 → ℝ := ![wa, μ, μ, wa]
  -- the link tables for the shifts `0`, `a`, `b`
  let l0 : Fin 4 → Fin 4 → ℝ := ![![δ, 0, 0, 0], ![0, δ, 0, 0], ![0, 0, δ, 0], ![0, 0, 0, δ]]
  let la : Fin 4 → Fin 4 → ℝ := ![![0, 0, 0, 0], ![δ, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, δ, 0]]
  let lb : Fin 4 → Fin 4 → ℝ := ![![0, 0, 0, 0], ![0, 0, δ, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]
  have key : ∀ (ℓ : ℝ) (lk : Fin 4 → Fin 4 → ℝ),
      (∀ i j, (t j = t i + ℓ ∧ lk i j = δ) ∨ (δ ≤ |t j - t i - ℓ| ∧ lk i j = 0)) →
      ∫ x, boxSum δ t c x * boxSum δ t c (x + ℓ) = ∑ i, ∑ j, c i * c j * lk i j :=
    fun ℓ lk h => integral_boxSum_shift hδ t c lk h
  have h0 := key 0 l0 (by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp only [t, l0, Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
        Matrix.tail_cons] <;>
      first
        | exact Or.inl ⟨by ring, by first | rfl | trivial⟩
        | exact Or.inr ⟨by rw [le_abs]; first | (left; linarith) | (right; linarith), by first | rfl | trivial⟩)
  have ha := key a la (by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp only [t, la, Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
        Matrix.tail_cons] <;>
      first
        | exact Or.inl ⟨by ring, by first | rfl | trivial⟩
        | exact Or.inr ⟨by rw [le_abs]; first | (left; linarith) | (right; linarith), by first | rfl | trivial⟩)
  have hb := key b lb (by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp only [t, lb, Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
        Matrix.tail_cons] <;>
      first
        | exact Or.inl ⟨by ring, by first | rfl | trivial⟩
        | exact Or.inr ⟨by rw [le_abs]; first | (left; linarith) | (right; linarith), by first | rfl | trivial⟩)
  have v0 : ∑ i, ∑ j, c i * c j * l0 i j = (2 * wa * wa + 2 * μ * μ) * δ := by
    simp only [Fin.sum_univ_four, c, l0, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    ring
  have va : ∑ i, ∑ j, c i * c j * la i j = 2 * wa * μ * δ := by
    simp only [Fin.sum_univ_four, c, la, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    ring
  have vb : ∑ i, ∑ j, c i * c j * lb i j = μ * μ * δ := by
    simp only [Fin.sum_univ_four, c, lb, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    ring
  rw [v0] at h0
  rw [va] at ha
  rw [vb] at hb
  have hsq0 : ∫ x, boxSum δ t c x ^ 2 = ∫ x, boxSum δ t c x * boxSum δ t c (x + 0) := by
    simp only [add_zero, sq]
  refine ⟨boxSum δ t c, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have hz : ∀ s, Set.Ioc s (s + δ) ⊆ Set.Ioc (0 : ℝ) L → box δ s x = 0 :=
      fun s hs => Set.indicator_of_notMem (fun h => hx (hs h)) _
    simp only [boxSum, Fin.sum_univ_four, t, c, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    rw [hz a (Set.Ioc_subset_Ioc (by linarith) (by linarith)),
      hz 0 (Set.Ioc_subset_Ioc le_rfl (by linarith)),
      hz b (Set.Ioc_subset_Ioc (by linarith) (by linarith)),
      hz (b - a) (Set.Ioc_subset_Ioc (by linarith) (by linarith))]
    ring
  · have e : boxSum δ t c
        = fun x => wa * box δ a x + μ * box δ 0 x + μ * box δ b x + wa * box δ (b - a) x := by
      funext x
      simp only [boxSum, Fin.sum_univ_four, t, c, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    rw [e]
    exact ((((memLp_box δ a).const_mul wa).add ((memLp_box δ 0).const_mul μ)).add
      ((memLp_box δ b).const_mul μ)).add ((memLp_box δ (b - a)).const_mul wa)
  · rw [hsq0, h0]; positivity
  · rw [hsq0, h0]
    show 2 * wa * (∫ x, boxSum δ t c x * boxSum δ t c (x + a))
        + 2 * wb * (∫ x, boxSum δ t c x * boxSum δ t c (x + b)) = μ * _
    rw [ha, hb]
    linear_combination (-2 * μ * δ) * hsq

end Attain

end Cvs.PathLaw.TwoAtom
