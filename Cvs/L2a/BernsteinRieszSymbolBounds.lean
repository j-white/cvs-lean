import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.Prolate.SlepianCommutingRelation

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Bernstein–Riesz symbol bounds

If `|∫_{−1}^{1} g(s)e^{icts} ds| ≤ F` for every real `t`, then multiplying `g` by `s^l`, by an absolutely
summable power series, by a Stieltjes symbol `1/(ζ + s)` with `|ζ| > 1`, or by a function holomorphic on a disc
of radius `R > 1` costs at most the symbol's coefficient mass: the triangle wave `s = Σ β_k sin(ω_k s)` with
`Σ|β_k| = 1` turns each multiplication by `s` into an average of frequency shifts.
-/

namespace Cvs.L2a.BernsteinRieszSymbolBounds

open Real Set

/-- `Σ_n cos(2πnx)/n² = π²(x² − x + 1/6)` on `[0, 1]`. -/
theorem hasSum_cos_div_sq {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    HasSum (fun n : ℕ => 1 / (n : ℝ) ^ 2 * cos (2 * π * n * x)) (π ^ 2 * (x ^ 2 - x + 1 / 6)) := by
  have h := hasSum_one_div_nat_pow_mul_cos (k := 1) one_ne_zero hx
  convert h using 1
  simp [Polynomial.bernoulli, Finset.sum_range_succ, bernoulli, Polynomial.eval_monomial]
  ring

/-- **The odd cosine sum**: `Σ_k cos((2k+1)πv)/(2k+1)² = (π²/8)(1 − 2v)` on `[0, 1]`. -/
theorem hasSum_odd_cos {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) :
    HasSum (fun k : ℕ => cos ((2 * k + 1) * π * v) / (2 * k + 1) ^ 2) (π ^ 2 / 8 * (1 - 2 * v)) := by
  set f : ℕ → ℝ := fun n => 1 / (n : ℝ) ^ 2 * cos (2 * π * n * (v / 2)) with hf
  have hall : HasSum f (π ^ 2 * ((v / 2) ^ 2 - v / 2 + 1 / 6)) :=
    hasSum_cos_div_sq ⟨by linarith [hv.1], by linarith [hv.2]⟩
  have heven : HasSum (fun k : ℕ => f (2 * k)) (π ^ 2 * (v ^ 2 - v + 1 / 6) / 4) := by
    have h := (hasSum_cos_div_sq hv).div_const 4
    refine h.congr_fun fun k => ?_
    simp only [hf]; push_cast
    rcases eq_or_ne (k : ℝ) 0 with hk | hk
    · simp [hk]
    · field_simp; ring_nf
  have hodd_s : Summable (fun k : ℕ => f (2 * k + 1)) :=
    hall.summable.comp_injective (fun a b h => by simpa using h)
  have hsum := heven.even_add_odd hodd_s.hasSum
  have huniq := hall.unique hsum
  have hodd : HasSum (fun k : ℕ => f (2 * k + 1))
      (π ^ 2 * ((v / 2) ^ 2 - v / 2 + 1 / 6) - π ^ 2 * (v ^ 2 - v + 1 / 6) / 4) := by
    rw [huniq]; simpa using hodd_s.hasSum
  convert hodd using 1
  · funext k; simp only [hf]; push_cast
    have : (2 * π * (2 * (k : ℝ) + 1) * (v / 2)) = (2 * k + 1) * π * v := by ring
    rw [this]; field_simp
  · ring

/-- `cos((2k+1)π(1 − s)/2) = (−1)^k sin((2k+1)πs/2)`. -/
theorem cos_odd_reflect (k : ℕ) (s : ℝ) :
    cos ((2 * k + 1) * π * ((1 - s) / 2)) = (-1) ^ k * sin ((2 * k + 1) * π / 2 * s) := by
  have e : (2 * (k : ℝ) + 1) * π * ((1 - s) / 2) = (k * π + π / 2) - (2 * k + 1) * π / 2 * s := by ring
  rw [e, cos_sub, cos_add_pi_div_two, sin_add_pi_div_two, sin_nat_mul_pi, cos_nat_mul_pi]
  ring

/-- The triangle-wave coefficient `β_k = 8(−1)^k/(π²(2k+1)²)`. -/
noncomputable def betaT (k : ℕ) : ℝ := 8 * (-1) ^ k / (π ^ 2 * (2 * k + 1) ^ 2)

/-- The triangle-wave frequency `ω_k = (2k+1)π/2`. -/
noncomputable def omegaT (k : ℕ) : ℝ := (2 * k + 1) * π / 2

/-- **The triangle wave**: `s = Σ_k β_k sin(ω_k s)` on `[−1, 1]`. -/
theorem hasSum_triangle {s : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1) :
    HasSum (fun k : ℕ => betaT k * sin (omegaT k * s)) s := by
  have h := (hasSum_odd_cos (v := (1 - s) / 2) ⟨by linarith [hs.2], by linarith [hs.1]⟩).mul_left (8 / π ^ 2)
  have hpi : π ^ 2 ≠ 0 := by positivity
  have e1 : 8 / π ^ 2 * (π ^ 2 / 8 * (1 - 2 * ((1 - s) / 2))) = s := by field_simp; ring
  rw [e1] at h
  refine h.congr_fun fun k => ?_
  rw [cos_odd_reflect]
  unfold betaT omegaT
  field_simp

/-- `Σ |β_k| = 1`. -/
theorem hasSum_abs_betaT : HasSum (fun k : ℕ => |betaT k|) 1 := by
  have h := (hasSum_odd_cos (v := 0) ⟨le_rfl, zero_le_one⟩).mul_left (8 / π ^ 2)
  have hpi : π ^ 2 ≠ 0 := by positivity
  have e1 : 8 / π ^ 2 * (π ^ 2 / 8 * (1 - 2 * 0)) = (1 : ℝ) := by field_simp; ring
  rw [e1] at h
  refine h.congr_fun fun k => ?_
  unfold betaT
  have hp : 0 < π ^ 2 * (2 * (k : ℝ) + 1) ^ 2 := by positivity
  rw [abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, mul_one, abs_of_pos hp, abs_of_pos (by norm_num : (0:ℝ) < 8)]
  simp only [mul_zero, cos_zero]
  field_simp

open MeasureTheory intervalIntegral

/-- The kernel `e^{icts}`. -/
noncomputable def ek (c t s : ℝ) : ℂ := Complex.exp (((c * t * s : ℝ) : ℂ) * Complex.I)

theorem norm_ek (c t s : ℝ) : ‖ek c t s‖ = 1 := by
  unfold ek; exact Complex.norm_exp_ofReal_mul_I _

theorem continuous_ek (c t : ℝ) : Continuous (ek c t) := by
  unfold ek; fun_prop

/-- `sin(ωs)e^{icxs} = (i/2)(e^{ic(x − ω/c)s} − e^{ic(x + ω/c)s})`. -/
theorem sin_mul_ek {c : ℝ} (hc : c ≠ 0) (ω x s : ℝ) :
    ((sin (ω * s) : ℝ) : ℂ) * ek c x s = Complex.I / 2 * (ek c (x - ω / c) s - ek c (x + ω / c) s) := by
  unfold ek
  rw [Complex.ofReal_sin, Complex.sin]
  have r1 : c * (x - ω / c) * s = -(ω * s) + c * x * s := by field_simp; ring
  have r2 : c * (x + ω / c) * s = ω * s + c * x * s := by field_simp; ring
  have e1 : ((c * (x - ω / c) * s : ℝ) : ℂ) * Complex.I = -(((ω * s : ℝ) : ℂ)) * Complex.I + ((c * x * s : ℝ) : ℂ) * Complex.I := by
    rw [r1]; push_cast; ring
  have e2 : ((c * (x + ω / c) * s : ℝ) : ℂ) * Complex.I = ((ω * s : ℝ) : ℂ) * Complex.I + ((c * x * s : ℝ) : ℂ) * Complex.I := by
    rw [r2]; push_cast; ring
  rw [e1, e2, Complex.exp_add, Complex.exp_add]
  push_cast
  ring

/-- **Bernstein–Riesz, one step**: if `|∫ g e^{icts}| ≤ F` for every real `t`, then `|∫ g(s)·s·e^{icxs}| ≤ F`. -/
theorem norm_integral_mul_id_le {g : ℝ → ℂ} (hg : ContinuousOn g (Icc (-1) 1)) {c F : ℝ} (hc : c ≠ 0)
    (hF : ∀ t : ℝ, ‖∫ s in (-1 : ℝ)..1, g s * ek c t s‖ ≤ F) (x : ℝ) :
    ‖∫ s in (-1 : ℝ)..1, g s * (s : ℂ) * ek c x s‖ ≤ F := by
  have hu : uIoc (-1 : ℝ) 1 ⊆ Icc (-1) 1 := fun t ht => by
    rw [uIoc_of_le (by norm_num)] at ht; exact ⟨ht.1.le, ht.2⟩
  set Fk : ℕ → ℝ → ℂ := fun k s => g s * ((betaT k * sin (omegaT k * s) : ℝ) : ℂ) * ek c x s with hFk
  have hcont : ∀ k, ContinuousOn (Fk k) (Icc (-1) 1) := fun k =>
    (hg.mul (Complex.continuous_ofReal.comp (by fun_prop : Continuous fun s => betaT k * sin (omegaT k * s))).continuousOn).mul
      (continuous_ek c x).continuousOn
  have hsum := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume) (a := -1) (b := 1)
    (F := Fk) (f := fun s => g s * (s : ℂ) * ek c x s) (fun k s => ‖g s‖ * |betaT k|)
    (fun k => ((hcont k).mono hu).aestronglyMeasurable measurableSet_uIoc)
    (fun k => ae_of_all _ fun s _ => by
      simp only [hFk, norm_mul, norm_ek, mul_one, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (abs_nonneg _) (abs_sin_le_one _)) (norm_nonneg _))
    (ae_of_all _ fun s _ => (hasSum_abs_betaT.mul_left ‖g s‖).summable)
    (by
      have : (fun s => ∑' k, ‖g s‖ * |betaT k|) = fun s => ‖g s‖ := funext fun s => by
        rw [(hasSum_abs_betaT.mul_left ‖g s‖).tsum_eq, mul_one]
      rw [this]
      exact (hg.norm.intervalIntegrable_of_Icc (by norm_num)))
    (ae_of_all _ fun s hs => by
      have h := hasSum_triangle (hu hs)
      have h2 := ((Complex.hasSum_ofReal.mpr h).mul_left (g s)).mul_right (ek c x s)
      simpa [hFk] using h2)
  -- each term
  have hterm : ∀ k, ‖∫ s in (-1 : ℝ)..1, Fk k s‖ ≤ |betaT k| * F := by
    intro k
    have e : (fun s => Fk k s) = fun s => ((betaT k : ℝ) : ℂ) * (Complex.I / 2) *
        (g s * ek c (x - omegaT k / c) s - g s * ek c (x + omegaT k / c) s) := by
      funext s
      simp only [hFk]
      rw [Complex.ofReal_mul, mul_assoc (g s), mul_assoc, sin_mul_ek hc]
      ring
    have i1 : IntervalIntegrable (fun s => g s * ek c (x - omegaT k / c) s) volume (-1) 1 :=
      (hg.mul (continuous_ek c _).continuousOn).intervalIntegrable_of_Icc (by norm_num)
    have i2 : IntervalIntegrable (fun s => g s * ek c (x + omegaT k / c) s) volume (-1) 1 :=
      (hg.mul (continuous_ek c _).continuousOn).intervalIntegrable_of_Icc (by norm_num)
    rw [e, intervalIntegral.integral_const_mul, intervalIntegral.integral_sub i1 i2, norm_mul, norm_mul,
      Complex.norm_real, Real.norm_eq_abs]
    have hI : ‖Complex.I / 2‖ = 1 / 2 := by simp
    rw [hI]
    have hs := norm_sub_le (∫ s in (-1 : ℝ)..1, g s * ek c (x - omegaT k / c) s)
      (∫ s in (-1 : ℝ)..1, g s * ek c (x + omegaT k / c) s)
    have := hF (x - omegaT k / c)
    have := hF (x + omegaT k / c)
    have hb := abs_nonneg (betaT k)
    nlinarith
  rw [← hsum.tsum_eq]
  exact tsum_of_norm_bounded (hasSum_abs_betaT.mul_right F) hterm |>.trans (by simp)

/-- **Bernstein–Riesz, all powers**: `|∫ g(s) s^l e^{icxs}| ≤ F` for every `l` and real `x`. -/
theorem norm_integral_pow_mul_le {g : ℝ → ℂ} (hg : ContinuousOn g (Icc (-1) 1)) {c F : ℝ} (hc : c ≠ 0)
    (hF : ∀ t : ℝ, ‖∫ s in (-1 : ℝ)..1, g s * ek c t s‖ ≤ F) (l : ℕ) (x : ℝ) :
    ‖∫ s in (-1 : ℝ)..1, g s * (s : ℂ) ^ l * ek c x s‖ ≤ F := by
  induction l generalizing x with
  | zero => simpa using hF x
  | succ l ih =>
    have hgl : ContinuousOn (fun s => g s * (s : ℂ) ^ l) (Icc (-1) 1) :=
      hg.mul (Continuous.continuousOn (by fun_prop))
    have h := norm_integral_mul_id_le hgl hc ih x
    have e : (fun s : ℝ => g s * (s : ℂ) ^ (l + 1) * ek c x s) = fun s => g s * (s : ℂ) ^ l * (s : ℂ) * ek c x s := by
      funext s; ring
    rw [e]; exact h

/-- **The symbol bound**: for `h(s) = Σ hₗ sˡ` with `Σ |hₗ| < ∞`, `|∫ g h e^{icxs}| ≤ (Σ |hₗ|)·F`. -/
theorem norm_integral_series_le {g : ℝ → ℂ} (hg : ContinuousOn g (Icc (-1) 1)) {c F : ℝ} (hc : c ≠ 0)
    (hF : ∀ t : ℝ, ‖∫ s in (-1 : ℝ)..1, g s * ek c t s‖ ≤ F) {h : ℕ → ℂ} (hs : Summable fun l => ‖h l‖)
    (x : ℝ) :
    ‖∫ s in (-1 : ℝ)..1, g s * (∑' l, h l * (s : ℂ) ^ l) * ek c x s‖ ≤ (∑' l, ‖h l‖) * F := by
  have hu : uIoc (-1 : ℝ) 1 ⊆ Icc (-1) 1 := fun t ht => by
    rw [uIoc_of_le (by norm_num)] at ht; exact ⟨ht.1.le, ht.2⟩
  have hF0 : 0 ≤ F := (norm_nonneg _).trans (hF 0)
  have hsum := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume) (a := -1) (b := 1)
    (F := fun l s => g s * (h l * (s : ℂ) ^ l) * ek c x s) (f := fun s => g s * (∑' l, h l * (s : ℂ) ^ l) * ek c x s)
    (fun l s => ‖g s‖ * ‖h l‖)
    (fun l => (((hg.mul (Continuous.continuousOn (by fun_prop))).mul (continuous_ek c x).continuousOn).mono hu).aestronglyMeasurable
      measurableSet_uIoc)
    (fun l => ae_of_all _ fun s hs => by
      have hs1 : |s| ≤ 1 := abs_le.2 ⟨(hu hs).1, (hu hs).2⟩
      rw [norm_mul, norm_mul, norm_mul, norm_ek, mul_one, norm_pow, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (abs_nonneg _) hs1))
        (norm_nonneg _))
    (ae_of_all _ fun s _ => hs.mul_left ‖g s‖)
    (by
      have : (fun s => ∑' l, ‖g s‖ * ‖h l‖) = fun s => ‖g s‖ * ∑' l, ‖h l‖ := funext fun s => tsum_mul_left
      rw [this]
      exact (hg.norm.mul continuousOn_const).intervalIntegrable_of_Icc (by norm_num))
    (ae_of_all _ fun s hsI => by
      have hs1 : ‖(s : ℂ)‖ ≤ 1 := by rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_le.2 ⟨(hu hsI).1, (hu hsI).2⟩
      have hsum' : Summable fun l => h l * (s : ℂ) ^ l :=
        Summable.of_norm_bounded hs fun l => by
          rw [norm_mul, norm_pow]; exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hs1)
      exact ((hsum'.hasSum.mul_left (g s)).mul_right (ek c x s)))
  rw [← hsum.tsum_eq]
  refine tsum_of_norm_bounded (hs.hasSum.mul_right F) fun l => ?_
  have e : (fun s : ℝ => g s * (h l * (s : ℂ) ^ l) * ek c x s) = fun s => h l * (g s * (s : ℂ) ^ l * ek c x s) := by
    funext s; ring
  rw [e, intervalIntegral.integral_const_mul, norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_integral_pow_mul_le hg hc hF l x) (norm_nonneg _)

/-- **The complex Stieltjes symbol**: for `|ζ| > 1`, `|∫ g(s) e^{icxs}/(ζ + s) ds| ≤ F/(|ζ| − 1)`. -/
theorem norm_integral_stieltjesC_le {g : ℝ → ℂ} (hg : ContinuousOn g (Icc (-1) 1)) {c F : ℝ} (hc : c ≠ 0)
    (hF : ∀ t : ℝ, ‖∫ s in (-1 : ℝ)..1, g s * ek c t s‖ ≤ F) {ζ : ℂ} (hζ : 1 < ‖ζ‖) (x : ℝ) :
    ‖∫ s in (-1 : ℝ)..1, g s / (ζ + s) * ek c x s‖ ≤ F / (‖ζ‖ - 1) := by
  have hζ0 : 0 < ‖ζ‖ := by linarith
  have hζne : ζ ≠ 0 := norm_pos_iff.1 hζ0
  set h : ℕ → ℂ := fun n => ζ⁻¹ * (-ζ⁻¹) ^ n with hh
  have hr0 : 0 ≤ ‖ζ‖⁻¹ := inv_nonneg.2 hζ0.le
  have hr1 : ‖ζ‖⁻¹ < 1 := inv_lt_one_of_one_lt₀ hζ
  have habs : HasSum (fun n => ‖h n‖) (1 / (‖ζ‖ - 1)) := by
    have hm := (hasSum_geometric_of_lt_one hr0 hr1).mul_left ‖ζ‖⁻¹
    have hval : ‖ζ‖⁻¹ * (1 - ‖ζ‖⁻¹)⁻¹ = 1 / (‖ζ‖ - 1) := by
      have : ‖ζ‖ - 1 ≠ 0 := by linarith
      field_simp
    rw [hval] at hm
    refine hm.congr_fun fun n => ?_
    simp [hh, norm_pow, norm_neg, norm_inv]
  have hser : ∀ s ∈ Icc (-1 : ℝ) 1, (∑' n, h n * (s : ℂ) ^ n) = 1 / (ζ + s) := by
    intro s hs
    have hs1 : ‖(s : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_le.2 ⟨hs.1, hs.2⟩
    have hq : ‖-ζ⁻¹ * (s : ℂ)‖ < 1 := by
      rw [norm_mul, norm_neg, norm_inv]
      calc ‖ζ‖⁻¹ * ‖(s : ℂ)‖ ≤ ‖ζ‖⁻¹ * 1 := mul_le_mul_of_nonneg_left hs1 hr0
        _ < 1 := by rw [mul_one]; exact hr1
    have hgeo := (hasSum_geometric_of_norm_lt_one hq).mul_left ζ⁻¹
    have hzs : ζ + s ≠ 0 := by
      intro h0
      have : ‖ζ‖ = ‖(s : ℂ)‖ := by rw [eq_neg_of_add_eq_zero_left h0, norm_neg]
      linarith
    have hval : ζ⁻¹ * (1 - -ζ⁻¹ * (s : ℂ))⁻¹ = 1 / (ζ + s) := by
      rw [show (1 : ℂ) - -ζ⁻¹ * s = (ζ + s) / ζ by field_simp; ring, inv_div]
      field_simp
    rw [hval] at hgeo
    rw [← hgeo.tsum_eq]
    congr 1; funext n; simp only [hh]; rw [mul_pow]; ring
  have heq : ∫ s in (-1 : ℝ)..1, g s / (ζ + s) * ek c x s
      = ∫ s in (-1 : ℝ)..1, g s * (∑' n, h n * (s : ℂ) ^ n) * ek c x s := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le (by norm_num)] at hs
    simp only [hser s hs, div_eq_mul_one_div (g s)]
  rw [heq]
  refine (norm_integral_series_le hg hc hF habs.summable x).trans ?_
  rw [habs.tsum_eq]; field_simp; rfl

/-- **The holomorphic symbol**: if `h` is holomorphic on the closed disc of radius `R > 1` and `|h| ≤ B` on its
boundary, then `|∫ g(s)h(s)e^{icxs} ds| ≤ BR/(R − 1)·F`. -/
theorem norm_integral_holo_le {g : ℝ → ℂ} (hg : ContinuousOn g (Icc (-1) 1)) {c F : ℝ} (hc : c ≠ 0)
    (hF : ∀ t : ℝ, ‖∫ s in (-1 : ℝ)..1, g s * ek c t s‖ ≤ F) {h : ℂ → ℂ} {R B : ℝ} (hR : 1 < R)
    (hd : DifferentiableOn ℂ h (Metric.closedBall 0 R)) (hB : ∀ z ∈ Metric.sphere (0 : ℂ) R, ‖h z‖ ≤ B)
    (x : ℝ) :
    ‖∫ s in (-1 : ℝ)..1, g s * h s * ek c x s‖ ≤ B * R / (R - 1) * F := by
  have hR0 : 0 < R := by linarith
  have hF0 : 0 ≤ F := (norm_nonneg _).trans (hF 0)
  set R' : NNReal := R.toNNReal with hR'
  have hR'c : (R' : ℝ) = R := Real.coe_toNNReal _ hR0.le
  have hR'0 : 0 < R' := Real.toNNReal_pos.2 hR0
  have hd' : DifferentiableOn ℂ h (Metric.closedBall 0 (R' : ℝ)) := by rwa [hR'c]
  have hps := hd'.hasFPowerSeriesOnBall hR'0
  set p := cauchyPowerSeries h 0 R' with hp
  set hl : ℕ → ℂ := fun n => p.coeff n with hhl
  have hint : ∫ θ in (0 : ℝ)..2 * π, ‖h (circleMap 0 R θ)‖ ≤ 2 * π * B := by
    have hn := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 2 * π) (C := B)
      (f := fun θ => ‖h (circleMap 0 R θ)‖)
      (fun θ _ => by rw [norm_norm]; exact hB _ (circleMap_mem_sphere 0 hR0.le θ))
    rw [sub_zero, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)] at hn
    rw [mul_comm (2 * π)]
    exact (le_abs_self _).trans (by rw [← Real.norm_eq_abs]; exact hn)
  have hcoef : ∀ n, ‖hl n‖ ≤ B * R⁻¹ ^ n := by
    intro n
    simp only [hhl]
    rw [← p.norm_apply_eq_norm_coef]
    refine (norm_cauchyPowerSeries_le h 0 R' n).trans ?_
    rw [hR'c, abs_of_pos hR0]
    refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (inv_nonneg.2 hR0.le) n)
    calc (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, ‖h (circleMap 0 R θ)‖ ≤ (2 * π)⁻¹ * (2 * π * B) :=
          mul_le_mul_of_nonneg_left hint (by positivity)
      _ = B := by field_simp
  have hRi0 : 0 ≤ R⁻¹ := inv_nonneg.2 hR0.le
  have hRi1 : R⁻¹ < 1 := inv_lt_one_of_one_lt₀ hR
  have hgeo := (hasSum_geometric_of_lt_one hRi0 hRi1).mul_left B
  have hsum : Summable fun n => ‖hl n‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hcoef hgeo.summable
  have htsum : ∑' n, ‖hl n‖ ≤ B * R / (R - 1) := by
    refine (hsum.tsum_le_tsum hcoef hgeo.summable).trans_eq ?_
    rw [hgeo.tsum_eq]
    have : R - 1 ≠ 0 := by linarith
    field_simp
  have hser : ∀ s ∈ Icc (-1 : ℝ) 1, (∑' n, hl n * (s : ℂ) ^ n) = h s := by
    intro s hs
    have hs1 : ‖(s : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_le.2 ⟨hs.1, hs.2⟩
    have hy : (s : ℂ) ∈ Metric.eball (0 : ℂ) R' := by
      rw [Metric.mem_eball, edist_dist, dist_zero_right]
      show ENNReal.ofReal ‖(s : ℂ)‖ < ENNReal.ofReal R
      exact (ENNReal.ofReal_lt_ofReal_iff hR0).2 (by linarith)
    have hS := hps.hasSum hy
    simp only [zero_add, p.apply_eq_pow_smul_coeff, smul_eq_mul] at hS
    rw [← hS.tsum_eq]
    congr 1; funext n; simp only [hhl]; ring
  have heq : ∫ s in (-1 : ℝ)..1, g s * h s * ek c x s
      = ∫ s in (-1 : ℝ)..1, g s * (∑' n, hl n * (s : ℂ) ^ n) * ek c x s := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le (by norm_num)] at hs
    simp only [hser s hs]
  rw [heq]
  exact (norm_integral_series_le hg hc hF hsum x).trans (mul_le_mul_of_nonneg_right htsum hF0)

/-- For real even `g`, `∫ g(s)e^{icts} ds` is the cosine transform `ψ(t)`. -/
theorem ek_integral_even {g : ℝ → ℝ} (hg : ContinuousOn g (Icc (-1) 1))
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) (c t : ℝ) :
    ∫ s in (-1 : ℝ)..1, (g s : ℂ) * ek c t s = (Cvs.L2a.AngularProlateTailPositive.psi c g t : ℂ) := by
  have hsin : ∫ s in (-1 : ℝ)..1, g s * sin (c * t * s) = 0 := by
    have h := intervalIntegral.integral_comp_neg (a := (-1 : ℝ)) (b := 1) (fun s => g s * sin (c * t * s))
    simp only [neg_neg] at h
    have h2 : ∫ x in (-1 : ℝ)..1, g (-x) * sin (c * t * -x) = -∫ x in (-1 : ℝ)..1, g x * sin (c * t * x) := by
      rw [← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr fun x hx => ?_
      rw [uIcc_of_le (by norm_num)] at hx
      simp only [heven x hx, mul_neg, sin_neg]
    rw [h2] at h
    linarith
  have i1 : IntervalIntegrable (fun s => ((g s * cos (c * t * s) : ℝ) : ℂ)) MeasureTheory.volume (-1) 1 :=
    (Complex.continuous_ofReal.comp_continuousOn (hg.mul (by fun_prop : Continuous fun s => cos (c * t * s)).continuousOn)).intervalIntegrable_of_Icc (by norm_num)
  have i2 : IntervalIntegrable (fun s => ((g s * sin (c * t * s) : ℝ) : ℂ) * Complex.I) MeasureTheory.volume (-1) 1 :=
    ((Complex.continuous_ofReal.comp_continuousOn (hg.mul (by fun_prop : Continuous fun s => sin (c * t * s)).continuousOn)).mul continuousOn_const).intervalIntegrable_of_Icc (by norm_num)
  have e : (fun s => (g s : ℂ) * ek c t s)
      = fun s => ((g s * cos (c * t * s) : ℝ) : ℂ) + ((g s * sin (c * t * s) : ℝ) : ℂ) * Complex.I := by
    funext s
    unfold ek
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    push_cast; ring
  rw [e, intervalIntegral.integral_add i1 i2, intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal,
    intervalIntegral.integral_ofReal, hsin]
  unfold Cvs.L2a.AngularProlateTailPositive.psi Cvs.Prolate.SlepianCommutingRelation.kint
  simp

/-- **The hypothesis from the cosine transform**: for real even `g`, `|ψ| ≤ F` gives the Bernstein–Riesz input. -/
theorem hF_of_psi {g : ℝ → ℝ} (hg : ContinuousOn g (Icc (-1) 1))
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) {c F : ℝ}
    (hpsi : ∀ t : ℝ, |Cvs.L2a.AngularProlateTailPositive.psi c g t| ≤ F) (t : ℝ) :
    ‖∫ s in (-1 : ℝ)..1, (g s : ℂ) * ek c t s‖ ≤ F := by
  rw [ek_integral_even hg heven, Complex.norm_real, Real.norm_eq_abs]; exact hpsi t

end Cvs.L2a.BernsteinRieszSymbolBounds
