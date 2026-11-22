import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.Prolate.AngularBesselInequality
import Cvs.Prolate.CosineChristoffelDarboux
import Cvs.Prolate.PlungeMassTrace
import Cvs.Prolate.RungMirrorIdentity

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Landau's half on the cosine span: `⟨Kf, f⟩ ≥ ½‖f‖²` on `span{cos(πkt) : k < n}` at `c = πn`

Beyond `c` the transform of `f = Σ a_k cos(πkt)` is `sin η · Σ_k (−1)^k a_k (1/(η − πk) + 1/(η + πk))`; `sin²` averages
to `½` against the convex `Γ²`, and the Chebyshev pair `(c² − p²)^{−1/2}`, `(η² − c²)^{−1/2}` is a Schur pair with
constant `π` because the cells `[πk, π(k + 1)]` tile `[0, c]`. So `∫_c^∞ C² ≤ (π/2)Σa_k²`, and Plancherel concludes.
-/

noncomputable section

open Real Set MeasureTheory intervalIntegral Filter Topology
open scoped Interval

namespace Cvs.Prolate.LandauHalfCosineSpan

/-! ### Averaging `sin²` against a convex weight -/

/-- **`sin²` averages to `½` against a convex weight**: if `sin a = sin b = 0`, `a ≤ b` and `H'' ≥ 0` on `[a, b]`,
then `∫_a^b sin²·H ≤ ½∫_a^b H` (the deficit is `¼∫_a^b sin²·H''`). -/
theorem integral_sin_sq_mul_le {H H₁ H₂ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (ha : sin a = 0) (hb : sin b = 0)
    (hH : ∀ x ∈ uIcc a b, HasDerivAt H (H₁ x) x) (hH₁ : ∀ x ∈ uIcc a b, HasDerivAt H₁ (H₂ x) x)
    (hH₂c : ContinuousOn H₂ (uIcc a b)) (hH₂ : ∀ x ∈ uIcc a b, 0 ≤ H₂ x) :
    ∫ x in a..b, sin x ^ 2 * H x ≤ 1 / 2 * ∫ x in a..b, H x := by
  have hHc : ContinuousOn H (uIcc a b) := fun x hx => (hH x hx).continuousAt.continuousWithinAt
  have hΦd : ∀ x ∈ uIcc a b, HasDerivAt (fun x => sin (2 * x) / 2 * H x - sin x ^ 2 / 2 * H₁ x)
      (cos (2 * x) * H x - sin x ^ 2 / 2 * H₂ x) x := by
    intro x hx
    have h1 : HasDerivAt (fun x => sin (2 * x) / 2) (cos (2 * x)) x := by
      have h := (((hasDerivAt_id x).const_mul (2 : ℝ)).sin).div_const 2
      exact h.congr_deriv (by simp only [id, mul_one]; ring)
    have h2 : HasDerivAt (fun x => sin x ^ 2 / 2) (sin (2 * x) / 2) x := by
      have h := ((hasDerivAt_pow 2 (sin x)).comp x (hasDerivAt_sin x)).div_const 2
      exact h.congr_deriv (by rw [sin_two_mul]; norm_num)
    have h3 := (h1.mul (hH x hx)).sub (h2.mul (hH₁ x hx))
    exact h3.congr_deriv (by ring)
  have hint : IntervalIntegrable (fun x => cos (2 * x) * H x - sin x ^ 2 / 2 * H₂ x) volume a b := by
    apply ContinuousOn.intervalIntegrable
    exact ((continuous_cos.comp (continuous_const.mul continuous_id)).continuousOn.mul hHc).sub
      (((continuous_sin.pow 2).div_const 2).continuousOn.mul hH₂c)
  have hFTC := integral_eq_sub_of_hasDerivAt hΦd hint
  simp only [sin_two_mul, ha, hb, mul_zero, zero_mul, zero_div, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, sub_self] at hFTC
  have e : ∀ x, sin x ^ 2 * H x
      = H x / 2 - (cos (2 * x) * H x - sin x ^ 2 / 2 * H₂ x) / 2 - sin x ^ 2 * H₂ x / 4 := by
    intro x
    linear_combination (H x / 2) * cos_two_mul x + (H x) * sin_sq_add_cos_sq x
  have hI1 : IntervalIntegrable H volume a b := hHc.intervalIntegrable
  have hI3 : IntervalIntegrable (fun x => sin x ^ 2 * H₂ x) volume a b :=
    ((continuous_sin.pow 2).continuousOn.mul hH₂c).intervalIntegrable
  have hpos : 0 ≤ ∫ x in a..b, sin x ^ 2 * H₂ x :=
    intervalIntegral.integral_nonneg hab fun x hx => mul_nonneg (sq_nonneg _)
      (hH₂ x (by rw [uIcc_of_le hab]; exact hx))
  have hsplit : ∫ x in a..b, sin x ^ 2 * H x
      = (∫ x in a..b, H x) / 2 - (∫ x in a..b, (cos (2 * x) * H x - sin x ^ 2 / 2 * H₂ x)) / 2
        - (∫ x in a..b, sin x ^ 2 * H₂ x) / 4 := by
    simp_rw [e]
    rw [intervalIntegral.integral_sub, intervalIntegral.integral_sub, intervalIntegral.integral_div,
      intervalIntegral.integral_div, intervalIntegral.integral_div]
    · exact hI1.div_const 2
    · exact hint.div_const 2
    · exact (hI1.div_const 2).sub (hint.div_const 2)
    · exact hI3.div_const 4
  rw [hsplit, hFTC]
  linarith

/-! ### The Chebyshev pair `w(p) = (c² − p²)^{−1/2}`, `v(η) = (η² − c²)^{−1/2}` -/

/-- The Chebyshev integrand in `η`: `v(η) · 2η/(η² − p²)`. -/
def chebEta (c p η : ℝ) : ℝ := 2 * η / ((η ^ 2 - p ^ 2) * √(η ^ 2 - c ^ 2))

/-- Its antiderivative `(2/√(c² − p²)) arctan(√(η² − c²)/√(c² − p²))`. -/
def chebEtaPrim (c p η : ℝ) : ℝ := 2 / √(c ^ 2 - p ^ 2) * arctan (√(η ^ 2 - c ^ 2) / √(c ^ 2 - p ^ 2))

theorem hasDerivAt_chebEtaPrim {c p η : ℝ} (hp0 : 0 ≤ p) (hpc : p < c) (hη : c < η) :
    HasDerivAt (chebEtaPrim c p) (chebEta c p η) η := by
  have hc : 0 < c := lt_of_le_of_lt hp0 hpc
  have hd2 : 0 < c ^ 2 - p ^ 2 := by nlinarith
  have hs2 : 0 < η ^ 2 - c ^ 2 := by nlinarith
  set d := √(c ^ 2 - p ^ 2) with hd
  set s := √(η ^ 2 - c ^ 2) with hs
  have hd0 : 0 < d := Real.sqrt_pos.2 hd2
  have hs0 : 0 < s := Real.sqrt_pos.2 hs2
  have hdd : d ^ 2 = c ^ 2 - p ^ 2 := Real.sq_sqrt hd2.le
  have hss : s ^ 2 = η ^ 2 - c ^ 2 := Real.sq_sqrt hs2.le
  have hsq : HasDerivAt (fun η => √(η ^ 2 - c ^ 2)) (2 * η / (2 * s)) η := by
    have h := ((hasDerivAt_pow 2 η).sub_const (c ^ 2)).sqrt hs2.ne'
    exact h.congr_deriv (by rw [← hs]; push_cast; ring)
  have h := ((hsq.div_const d).arctan).const_mul (2 / d)
  unfold chebEtaPrim
  refine h.congr_deriv ?_
  unfold chebEta
  rw [← hs]
  have hden : η ^ 2 - p ^ 2 = d ^ 2 + s ^ 2 := by rw [hdd, hss]; ring
  rw [hden]
  field_simp

theorem continuous_chebEtaPrim (c p : ℝ) : Continuous (chebEtaPrim c p) := by
  unfold chebEtaPrim; fun_prop

theorem chebEta_nonneg {c p η : ℝ} (hp0 : 0 ≤ p) (hpc : p < c) (hη : c ≤ η) : 0 ≤ chebEta c p η := by
  have hc : 0 < c := lt_of_le_of_lt hp0 hpc
  unfold chebEta
  apply div_nonneg (by linarith)
  apply mul_nonneg _ (Real.sqrt_nonneg _)
  nlinarith

/-- **The Chebyshev integral in `η`**: `∫_c^R v(η)·2η/(η² − p²) dη ≤ π/√(c² − p²)` for `0 ≤ p < c ≤ R`, and the
integrand is integrable despite the `(η − c)^{−1/2}` edge. -/
theorem chebEta_integral {c p R : ℝ} (hp0 : 0 ≤ p) (hpc : p < c) (hR : c ≤ R) :
    IntervalIntegrable (chebEta c p) volume c R ∧ ∫ η in c..R, chebEta c p η ≤ π / √(c ^ 2 - p ^ 2) := by
  have hc : 0 < c := lt_of_le_of_lt hp0 hpc
  have hd2 : 0 < c ^ 2 - p ^ 2 := by nlinarith
  have hd0 : 0 < √(c ^ 2 - p ^ 2) := Real.sqrt_pos.2 hd2
  have hderiv : ∀ η ∈ Ioo (min c R) (max c R), HasDerivAt (chebEtaPrim c p) (chebEta c p η) η := by
    intro η hη
    rw [min_eq_left hR, max_eq_right hR] at hη
    exact hasDerivAt_chebEtaPrim hp0 hpc hη.1
  have hint : IntervalIntegrable (chebEta c p) volume c R :=
    intervalIntegral.intervalIntegrable_deriv_of_nonneg (continuous_chebEtaPrim c p).continuousOn hderiv
      (fun η hη => by
        rw [min_eq_left hR, max_eq_right hR] at hη
        exact chebEta_nonneg hp0 hpc hη.1.le)
  refine ⟨hint, ?_⟩
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hR (continuous_chebEtaPrim c p).continuousOn
    (fun η hη => hasDerivAt_chebEtaPrim hp0 hpc hη.1) hint]
  have h0 : chebEtaPrim c p c = 0 := by simp [chebEtaPrim]
  rw [h0, sub_zero]
  unfold chebEtaPrim
  have := arctan_lt_pi_div_two (√(R ^ 2 - c ^ 2) / √(c ^ 2 - p ^ 2))
  have h2 : 0 < 2 / √(c ^ 2 - p ^ 2) := by positivity
  calc 2 / √(c ^ 2 - p ^ 2) * arctan (√(R ^ 2 - c ^ 2) / √(c ^ 2 - p ^ 2))
      ≤ 2 / √(c ^ 2 - p ^ 2) * (π / 2) := mul_le_mul_of_nonneg_left this.le h2.le
    _ = π / √(c ^ 2 - p ^ 2) := by field_simp

/-! ### The Chebyshev sum in `p` -/

/-- The Chebyshev integrand in `p`: `w(p) · 2η/(η² − p²)`. -/
def chebP (c η p : ℝ) : ℝ := 2 * η / ((η ^ 2 - p ^ 2) * √(c ^ 2 - p ^ 2))

/-- Its antiderivative `(2/√(η² − c²)) arcsin(p√(η² − c²)/(c√(η² − p²)))`, continuous up to `p = c`. -/
def chebPPrim (c η p : ℝ) : ℝ := 2 / √(η ^ 2 - c ^ 2) * arcsin (p * √(η ^ 2 - c ^ 2) / (c * √(η ^ 2 - p ^ 2)))

theorem hasDerivAt_chebPPrim {c η p : ℝ} (hp0 : 0 ≤ p) (hpc : p < c) (hη : c < η) :
    HasDerivAt (chebPPrim c η) (chebP c η p) p := by
  have hc : 0 < c := lt_of_le_of_lt hp0 hpc
  have hb2 : 0 < η ^ 2 - c ^ 2 := by nlinarith
  have hq2 : 0 < η ^ 2 - p ^ 2 := by nlinarith
  have hr2 : 0 < c ^ 2 - p ^ 2 := by nlinarith
  set b := √(η ^ 2 - c ^ 2) with hb
  set q := √(η ^ 2 - p ^ 2) with hq
  set r := √(c ^ 2 - p ^ 2) with hr
  have hb0 : 0 < b := Real.sqrt_pos.2 hb2
  have hq0 : 0 < q := Real.sqrt_pos.2 hq2
  have hr0 : 0 < r := Real.sqrt_pos.2 hr2
  have hbb : b ^ 2 = η ^ 2 - c ^ 2 := Real.sq_sqrt hb2.le
  have hqq : q ^ 2 = η ^ 2 - p ^ 2 := Real.sq_sqrt hq2.le
  have hrr : r ^ 2 = c ^ 2 - p ^ 2 := Real.sq_sqrt hr2.le
  have hη0 : 0 < η := by linarith
  -- the argument `u(p) = p b/(c q(p))`
  have hqd : HasDerivAt (fun p => √(η ^ 2 - p ^ 2)) (-(2 * p) / (2 * q)) p := by
    have h := ((hasDerivAt_pow 2 p).const_sub (η ^ 2)).sqrt hq2.ne'
    exact h.congr_deriv (by rw [← hq]; push_cast; ring)
  have hud : HasDerivAt (fun p => p * b / (c * √(η ^ 2 - p ^ 2)))
      ((1 * b * (c * q) - p * b * (c * (-(2 * p) / (2 * q)))) / (c * q) ^ 2) p := by
    have h := ((hasDerivAt_id p).mul_const b).div (hqd.const_mul c) (by rw [← hq]; positivity)
    exact h
  -- `1 − u² = η² r²/(c² q²)`, so `√(1 − u²) = η r/(c q)`
  have hu1 : 1 - (p * b / (c * q)) ^ 2 = (η * r / (c * q)) ^ 2 := by
    field_simp
    rw [hbb, hqq, hrr]
    ring
  have hsq1 : √(1 - (p * b / (c * q)) ^ 2) = η * r / (c * q) := by
    rw [hu1, Real.sqrt_sq (by positivity)]
  have hu_lt : p * b / (c * q) < 1 := by
    rw [div_lt_one (by positivity)]
    have h1 : (p * b) ^ 2 < (c * q) ^ 2 := by
      rw [mul_pow, mul_pow, hbb, hqq]; nlinarith
    nlinarith [sq_nonneg (p * b), sq_nonneg (c * q), mul_pos hc hq0, mul_nonneg hp0 hb0.le]
  have hu_gt : -1 < p * b / (c * q) := by
    have : 0 ≤ p * b / (c * q) := by positivity
    linarith
  have ha := (Real.hasDerivAt_arcsin hu_gt.ne' hu_lt.ne).comp p hud
  have h := ha.const_mul (2 / b)
  unfold chebPPrim
  refine h.congr_deriv ?_
  rw [hsq1]
  unfold chebP
  rw [← hr]
  have hqq' : η ^ 2 - p ^ 2 = q ^ 2 := hqq.symm
  rw [hqq']
  field_simp
  linear_combination hqq

theorem continuousOn_chebPPrim {c η : ℝ} (hc : 0 < c) (hη : c < η) :
    ContinuousOn (chebPPrim c η) (Icc 0 c) := by
  have hcont : ContinuousOn (fun p => p * √(η ^ 2 - c ^ 2) / (c * √(η ^ 2 - p ^ 2))) (Icc 0 c) := by
    have hn : ContinuousOn (fun p : ℝ => p * √(η ^ 2 - c ^ 2)) (Icc 0 c) := by fun_prop
    have hd : ContinuousOn (fun p : ℝ => c * √(η ^ 2 - p ^ 2)) (Icc 0 c) := by fun_prop
    refine ContinuousOn.div₀ (f := fun p : ℝ => p * √(η ^ 2 - c ^ 2))
      (g := fun p : ℝ => c * √(η ^ 2 - p ^ 2)) hn hd ?_
    intro p hp
    have : 0 < η ^ 2 - p ^ 2 := by nlinarith [hp.1, hp.2]
    positivity
  unfold chebPPrim
  exact continuousOn_const.mul (continuous_arcsin.comp_continuousOn hcont)

theorem chebPPrim_zero (c η : ℝ) : chebPPrim c η 0 = 0 := by simp [chebPPrim]

theorem chebPPrim_c {c η : ℝ} (hc : 0 < c) (hη : c < η) : chebPPrim c η c = π / √(η ^ 2 - c ^ 2) := by
  have hb2 : 0 < η ^ 2 - c ^ 2 := by nlinarith
  have hb0 : 0 < √(η ^ 2 - c ^ 2) := Real.sqrt_pos.2 hb2
  unfold chebPPrim
  rw [show c * √(η ^ 2 - c ^ 2) / (c * √(η ^ 2 - c ^ 2)) = 1 by field_simp, arcsin_one]
  field_simp

/-- `chebP` increases on `[0, c)`. -/
theorem chebP_mono {c η p p' : ℝ} (hp : 0 ≤ p) (hpp' : p ≤ p') (hp' : p' < c) (hη : c < η) :
    chebP c η p ≤ chebP c η p' := by
  have hc : 0 < c := by linarith
  have h1 : 0 < η ^ 2 - p' ^ 2 := by nlinarith
  have h2 : 0 < c ^ 2 - p' ^ 2 := by nlinarith
  have h3 : η ^ 2 - p' ^ 2 ≤ η ^ 2 - p ^ 2 := by nlinarith
  have h4 : √(c ^ 2 - p' ^ 2) ≤ √(c ^ 2 - p ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
  unfold chebP
  apply div_le_div_of_nonneg_left (by linarith) (by positivity)
  exact mul_le_mul h3 h4 (Real.sqrt_nonneg _) (by nlinarith)

/-- **The Chebyshev sum**: at `c = πn` and `η > c`, `Σ_{k<n} w(πk)·2η/(η² − π²k²) ≤ v(η) = (η² − c²)^{−1/2}`.
Each cell `[πk, π(k+1)]` lies in `[0, c]`, `w·2η/(η² − ·²)` increases there, and the cells telescope the
antiderivative from `0` to `c`. -/
theorem sum_chebP_le {n : ℕ} {η : ℝ} (hn : 1 ≤ n) (hη : π * n < η) :
    ∑ k ∈ Finset.range n, chebP (π * n) η (π * k) ≤ 1 / √(η ^ 2 - (π * n) ^ 2) := by
  set c := π * (n : ℝ) with hcdef
  have hc : 0 < c := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    positivity
  have hcell : ∀ k ∈ Finset.range n, π * chebP c η (π * k) ≤ chebPPrim c η (π * (k + 1)) - chebPPrim c η (π * k) := by
    intro k hk
    have hk' : (k : ℝ) + 1 ≤ n := by
      have := Finset.mem_range.mp hk
      exact_mod_cast this
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hsub : Icc (π * k) (π * (k + 1)) ⊆ Icc 0 c := by
      intro p hp
      refine ⟨le_trans (by positivity) hp.1, le_trans hp.2 ?_⟩
      rw [hcdef]; exact mul_le_mul_of_nonneg_left hk' pi_pos.le
    have hconv : Convex ℝ (Icc (π * k) (π * (k + 1))) := convex_Icc _ _
    have hcont := (continuousOn_chebPPrim hc hη).mono hsub
    have hint : interior (Icc (π * (k : ℝ)) (π * (k + 1))) = Ioo (π * k) (π * (k + 1)) := interior_Icc
    have hlt : ∀ p ∈ Ioo (π * (k : ℝ)) (π * (k + 1)), 0 ≤ p ∧ p < c := by
      intro p hp
      refine ⟨le_trans (by positivity) hp.1.le, lt_of_lt_of_le hp.2 ?_⟩
      rw [hcdef]; exact mul_le_mul_of_nonneg_left hk' pi_pos.le
    have hdiff : DifferentiableOn ℝ (chebPPrim c η) (interior (Icc (π * k) (π * (k + 1)))) := by
      rw [hint]
      intro p hp
      exact (hasDerivAt_chebPPrim (hlt p hp).1 (hlt p hp).2 hη).differentiableAt.differentiableWithinAt
    have hge : ∀ p ∈ interior (Icc (π * (k : ℝ)) (π * (k + 1))), chebP c η (π * k) ≤ deriv (chebPPrim c η) p := by
      rw [hint]
      intro p hp
      rw [(hasDerivAt_chebPPrim (hlt p hp).1 (hlt p hp).2 hη).deriv]
      exact chebP_mono (by positivity) hp.1.le (hlt p hp).2 hη
    have := hconv.mul_sub_le_image_sub_of_le_deriv hcont hdiff hge (π * k) (left_mem_Icc.2 (by nlinarith [pi_pos]))
      (π * (k + 1)) (right_mem_Icc.2 (by nlinarith [pi_pos])) (by nlinarith [pi_pos])
    calc π * chebP c η (π * k) = chebP c η (π * k) * (π * (k + 1) - π * k) := by ring
      _ ≤ _ := this
  have htel : ∑ k ∈ Finset.range n, (chebPPrim c η (π * ((k : ℕ) + 1 : ℕ)) - chebPPrim c η (π * k))
      = chebPPrim c η (π * n) - chebPPrim c η (π * (0 : ℕ)) :=
    Finset.sum_range_sub (fun k : ℕ => chebPPrim c η (π * k)) n
  have hsum : π * ∑ k ∈ Finset.range n, chebP c η (π * k) ≤ π / √(η ^ 2 - c ^ 2) := by
    rw [Finset.mul_sum]
    calc ∑ k ∈ Finset.range n, π * chebP c η (π * k)
        ≤ ∑ k ∈ Finset.range n, (chebPPrim c η (π * ((k : ℕ) + 1 : ℕ)) - chebPPrim c η (π * k)) := by
          apply Finset.sum_le_sum
          intro k hk
          have := hcell k hk
          push_cast
          exact this
      _ = chebPPrim c η (π * n) - chebPPrim c η (π * (0 : ℕ)) := htel
      _ = π / √(η ^ 2 - c ^ 2) := by
          rw [← hcdef]
          simp only [Nat.cast_zero, mul_zero, chebPPrim_zero, sub_zero]
          exact chebPPrim_c hc hη
  have := pi_pos
  rw [show π / √(η ^ 2 - c ^ 2) = π * (1 / √(η ^ 2 - c ^ 2)) by ring] at hsum
  exact le_of_mul_le_mul_left hsum pi_pos

/-! ### The cosine span and its transform -/

/-- The cosine polynomial `f_a(t) = Σ_{k<n} a_k cos(πkt)`. -/
def cosPoly {n : ℕ} (a : Fin n → ℝ) (t : ℝ) : ℝ := ∑ k : Fin n, a k * cos (π * (k : ℕ) * t)

theorem continuous_cosPoly {n : ℕ} (a : Fin n → ℝ) : Continuous (cosPoly a) := by
  unfold cosPoly; fun_prop

theorem cosPoly_neg {n : ℕ} (a : Fin n → ℝ) (t : ℝ) : cosPoly a (-t) = cosPoly a t := by
  unfold cosPoly
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_neg, cos_neg]

/-- Its transform `C(η) = Σ_k a_k (sinc(η − πk) + sinc(η + πk))`. -/
def cosHat {n : ℕ} (a : Fin n → ℝ) (η : ℝ) : ℝ :=
  ∑ k : Fin n, a k * (sinc (η - π * (k : ℕ)) + sinc (η + π * (k : ℕ)))

theorem continuous_cosHat {n : ℕ} (a : Fin n → ℝ) : Continuous (cosHat a) := by
  unfold cosHat
  refine continuous_finsetSum _ fun k _ => ?_
  exact continuous_const.mul ((continuous_sinc.comp (continuous_id.sub continuous_const)).add
    (continuous_sinc.comp (continuous_id.add continuous_const)))

/-- `∫_{−1}^{1} f_a(s) cos(ηs) ds = C(η)`. -/
theorem integral_cosPoly_mul_cos {n : ℕ} (a : Fin n → ℝ) (η : ℝ) :
    ∫ s in (-1 : ℝ)..1, cosPoly a s * cos (η * s) = cosHat a η := by
  unfold cosPoly cosHat
  simp_rw [Finset.sum_mul]
  rw [intervalIntegral.integral_finsetSum (fun k _ => by apply Continuous.intervalIntegrable; fun_prop)]
  refine Finset.sum_congr rfl fun k _ => ?_
  have e : ∀ s, a k * cos (π * ((k : ℕ) : ℝ) * s) * cos (η * s)
      = a k * (cos ((π * ((k : ℕ) : ℝ)) * s) * cos (η * s)) := fun s => by ring
  simp_rw [e]
  rw [intervalIntegral.integral_const_mul, Cvs.Prolate.PlungeMassTrace.integral_cos_mul_cos,
    show π * ((k : ℕ) : ℝ) - η = -(η - π * (k : ℕ)) by ring, sinc_neg, add_comm (π * ((k : ℕ) : ℝ)) η]

/-- `ψ = psi c f_a` is `C` at `cξ`. -/
theorem psi_cosPoly {n : ℕ} (a : Fin n → ℝ) (c ξ : ℝ) :
    Cvs.L2a.AngularProlateTailPositive.psi c (cosPoly a) ξ = cosHat a (c * ξ) := by
  rw [← integral_cosPoly_mul_cos]
  rfl

/-- Beyond the pole: `sinc(η − πk) + sinc(η + πk) = (−1)^k sin η (1/(η − πk) + 1/(η + πk))` for `πk < η`. -/
theorem sinc_pair {η : ℝ} {k : ℕ} (hk : π * k < η) :
    sinc (η - π * k) + sinc (η + π * k) = (-1) ^ k * sin η * ((η - π * k)⁻¹ + (η + π * k)⁻¹) := by
  have h0 : 0 ≤ π * (k : ℝ) := by positivity
  have h1 : η - π * k ≠ 0 := by linarith
  have h2 : η + π * k ≠ 0 := by linarith
  have hs1 : sin (η - π * k) = (-1) ^ k * sin η := by
    rw [show η - π * k = η - k * π by ring]; exact sin_sub_nat_mul_pi η k
  have hs2 : sin (η + π * k) = (-1) ^ k * sin η := by
    rw [show η + π * k = η + k * π by ring]; exact sin_add_nat_mul_pi η k
  rw [sinc_of_ne_zero h1, sinc_of_ne_zero h2, hs1, hs2]
  ring

/-! ### The majorant `Γ` and its derivatives -/

/-- The majorant `Γ(η) = Σ_k |a_k| ((η − πk)⁻¹ + (η + πk)⁻¹)`. -/
def gam {n : ℕ} (a : Fin n → ℝ) (η : ℝ) : ℝ := ∑ k : Fin n, |a k| * ((η - π * (k : ℕ))⁻¹ + (η + π * (k : ℕ))⁻¹)

/-- `Γ'`. -/
def gam1 {n : ℕ} (a : Fin n → ℝ) (η : ℝ) : ℝ :=
  ∑ k : Fin n, |a k| * (-((η - π * (k : ℕ)) ^ 2)⁻¹ - ((η + π * (k : ℕ)) ^ 2)⁻¹)

/-- `Γ''`. -/
def gam2 {n : ℕ} (a : Fin n → ℝ) (η : ℝ) : ℝ :=
  ∑ k : Fin n, |a k| * (2 * ((η - π * (k : ℕ)) ^ 3)⁻¹ + 2 * ((η + π * (k : ℕ)) ^ 3)⁻¹)

theorem hasDerivAt_inv_sub {p η : ℝ} (h : η ≠ p) :
    HasDerivAt (fun η => (η - p)⁻¹) (-((η - p) ^ 2)⁻¹) η := by
  have := ((hasDerivAt_id' η).sub_const p).fun_inv (sub_ne_zero.2 h)
  exact this.congr_deriv (by ring)

theorem hasDerivAt_inv_add {p η : ℝ} (h : η + p ≠ 0) :
    HasDerivAt (fun η => (η + p)⁻¹) (-((η + p) ^ 2)⁻¹) η := by
  have := ((hasDerivAt_id' η).add_const p).fun_inv h
  exact this.congr_deriv (by ring)

theorem hasDerivAt_neg_inv_sq_sub {p η : ℝ} (h : η ≠ p) :
    HasDerivAt (fun η => -((η - p) ^ 2)⁻¹) (2 * ((η - p) ^ 3)⁻¹) η := by
  have hp : η - p ≠ 0 := sub_ne_zero.2 h
  have := ((((hasDerivAt_id' η).sub_const p).fun_pow 2).fun_inv (pow_ne_zero 2 hp)).neg
  refine this.congr_deriv ?_
  field_simp
  ring

theorem hasDerivAt_neg_inv_sq_add {p η : ℝ} (h : η + p ≠ 0) :
    HasDerivAt (fun η => -((η + p) ^ 2)⁻¹) (2 * ((η + p) ^ 3)⁻¹) η := by
  have := ((((hasDerivAt_id' η).add_const p).fun_pow 2).fun_inv (pow_ne_zero 2 h)).neg
  refine this.congr_deriv ?_
  field_simp
  ring

/-- All poles lie below `η`: `πk < η` for `k < n` once `πn ≤ η`. -/
theorem pole_lt {n : ℕ} {η : ℝ} (hη : π * n ≤ η) (k : Fin n) : π * (k : ℕ) < η := by
  have hk : ((k : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast k.isLt
  nlinarith [pi_pos]

theorem pole_lt' {n : ℕ} {η : ℝ} (hη : π * n ≤ η) (k : Fin n) : 0 < η + π * (k : ℕ) := by
  have := pole_lt hη k
  have : 0 ≤ π * ((k : ℕ) : ℝ) := by positivity
  linarith

theorem hasDerivAt_gam {n : ℕ} (a : Fin n → ℝ) {η : ℝ} (hη : π * n ≤ η) :
    HasDerivAt (gam a) (gam1 a η) η := by
  unfold gam gam1
  refine HasDerivAt.fun_sum fun k _ => ?_
  have h1 := hasDerivAt_inv_sub (ne_of_gt (pole_lt hη k))
  have h2 := hasDerivAt_inv_add (p := π * (k : ℕ)) (η := η) (pole_lt' hη k).ne'
  exact ((h1.fun_add h2).const_mul |a k|).congr_deriv (by ring)

theorem hasDerivAt_gam1 {n : ℕ} (a : Fin n → ℝ) {η : ℝ} (hη : π * n ≤ η) :
    HasDerivAt (gam1 a) (gam2 a η) η := by
  unfold gam1 gam2
  refine HasDerivAt.fun_sum fun k _ => ?_
  have h1 := hasDerivAt_neg_inv_sq_sub (ne_of_gt (pole_lt hη k))
  have h2 := hasDerivAt_neg_inv_sq_add (p := π * (k : ℕ)) (η := η) (pole_lt' hη k).ne'
  have := (h1.fun_add h2).const_mul |a k|
  exact (this.congr_deriv (by ring)).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun y => by simp only; ring)

theorem gam_nonneg {n : ℕ} (a : Fin n → ℝ) {η : ℝ} (hη : π * n ≤ η) : 0 ≤ gam a η := by
  unfold gam
  refine Finset.sum_nonneg fun k _ => mul_nonneg (abs_nonneg _) ?_
  have h1 := pole_lt hη k
  have h2 := pole_lt' hη k
  have : 0 < η - π * (k : ℕ) := by linarith
  positivity

theorem gam2_nonneg {n : ℕ} (a : Fin n → ℝ) {η : ℝ} (hη : π * n ≤ η) : 0 ≤ gam2 a η := by
  unfold gam2
  refine Finset.sum_nonneg fun k _ => mul_nonneg (abs_nonneg _) ?_
  have h1 := pole_lt hη k
  have h2 := pole_lt' hη k
  have : 0 < η - π * (k : ℕ) := by linarith
  positivity

/-- `|C(η)| ≤ |sin η| Γ(η)` beyond `πn`. -/
theorem cosHat_sq_le {n : ℕ} (a : Fin n → ℝ) {η : ℝ} (hη : π * n ≤ η) :
    cosHat a η ^ 2 ≤ sin η ^ 2 * gam a η ^ 2 := by
  have hc : cosHat a η = sin η * ∑ k : Fin n, (-1) ^ (k : ℕ) * a k * ((η - π * (k : ℕ))⁻¹ + (η + π * (k : ℕ))⁻¹) := by
    unfold cosHat
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [sinc_pair (pole_lt hη k)]
    ring
  have hb : |∑ k : Fin n, (-1) ^ (k : ℕ) * a k * ((η - π * (k : ℕ))⁻¹ + (η + π * (k : ℕ))⁻¹)| ≤ gam a η := by
    unfold gam
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    have h1 := pole_lt hη k
    have h2 := pole_lt' hη k
    have hpos : 0 ≤ (η - π * (k : ℕ))⁻¹ + (η + π * (k : ℕ))⁻¹ := by
      have : 0 < η - π * (k : ℕ) := by linarith
      positivity
    rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_nonneg hpos]
  rw [hc, mul_pow]
  have := sq_le_sq' (neg_le_of_abs_le hb) (le_of_abs_le hb)
  exact mul_le_mul_of_nonneg_left this (sq_nonneg _)

/-! ### The Schur test with the Chebyshev pair -/

theorem pole_lt_c {n : ℕ} (k : Fin n) : π * (k : ℕ) < π * n := by
  have hk : ((k : ℕ) : ℝ) < n := by exact_mod_cast k.isLt
  exact mul_lt_mul_of_pos_left hk pi_pos

/-- **Cauchy–Schwarz against the Chebyshev weights**: for `η > c = πn`,
`Γ(η)² ≤ Σ_k a_k² √(c² − π²k²) · v(η) 2η/(η² − π²k²)`. -/
theorem gam_sq_le {n : ℕ} (hn : 1 ≤ n) (a : Fin n → ℝ) {η : ℝ} (hη : π * n < η) :
    gam a η ^ 2 ≤ ∑ k : Fin n, a k ^ 2 * √((π * n) ^ 2 - (π * (k : ℕ)) ^ 2) * chebEta (π * n) (π * (k : ℕ)) η := by
  set c := π * (n : ℝ) with hc
  have hc0 : 0 < c := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    positivity
  have hb2 : 0 < η ^ 2 - c ^ 2 := by nlinarith
  -- `φ_k = 2η/(η² − π²k²)`, `g_k = w_k φ_k = chebP c η (πk)`
  have hφ : ∀ k : Fin n, (η - π * (k : ℕ))⁻¹ + (η + π * (k : ℕ))⁻¹ = 2 * η / (η ^ 2 - (π * (k : ℕ)) ^ 2) := by
    intro k
    have h1 := pole_lt hη.le k
    have h2 := pole_lt' hη.le k
    have h3 : η - π * (k : ℕ) ≠ 0 := by linarith
    have h4 : η + π * (k : ℕ) ≠ 0 := h2.ne'
    rw [show η ^ 2 - (π * (k : ℕ)) ^ 2 = (η - π * (k : ℕ)) * (η + π * (k : ℕ)) by ring]
    field_simp
    ring
  have hr : ∀ k : Fin n, 0 < c ^ 2 - (π * (k : ℕ)) ^ 2 := by
    intro k
    have h1 := pole_lt_c k
    have : 0 ≤ π * ((k : ℕ) : ℝ) := by positivity
    rw [hc]; nlinarith
  have hq : ∀ k : Fin n, 0 < η ^ 2 - (π * (k : ℕ)) ^ 2 := by
    intro k
    have h1 := pole_lt hη.le k
    have : 0 ≤ π * ((k : ℕ) : ℝ) := by positivity
    nlinarith
  set f : Fin n → ℝ := fun k => |a k| * (2 * η / (η ^ 2 - (π * (k : ℕ)) ^ 2)) with hf
  set g : Fin n → ℝ := fun k => chebP c η (π * (k : ℕ)) with hg
  have hgpos : ∀ k ∈ Finset.univ, 0 < g k := by
    intro k _
    simp only [hg, chebP]
    have := hr k; have := hq k
    have : 0 < η := by linarith
    positivity
  have hgam : gam a η = ∑ k, f k := by
    unfold gam; refine Finset.sum_congr rfl fun k _ => ?_; rw [hφ k]
  have hT := Finset.sq_sum_div_le_sum_sq_div Finset.univ f hgpos
  have hgsum : ∑ k, g k ≤ 1 / √(η ^ 2 - c ^ 2) := by
    have h := sum_chebP_le hn hη
    rw [← hc] at h
    calc ∑ k, g k = ∑ k ∈ Finset.range n, chebP c η (π * k) :=
          Fin.sum_univ_eq_sum_range (fun k : ℕ => chebP c η (π * k)) n
      _ ≤ _ := h
  have hgsum_pos : 0 < ∑ k, g k := by
    have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
    exact Finset.sum_pos hgpos hne
  have hfg : ∀ k, f k ^ 2 / g k
      = a k ^ 2 * √(c ^ 2 - (π * (k : ℕ)) ^ 2) * (2 * η / (η ^ 2 - (π * (k : ℕ)) ^ 2)) := by
    intro k
    simp only [hf, hg, chebP]
    have h1 := hr k; have h2 := hq k
    have h3 : 0 < √(c ^ 2 - (π * (k : ℕ)) ^ 2) := Real.sqrt_pos.2 h1
    have h4 : 0 < η := by linarith
    rw [mul_pow, sq_abs]
    field_simp
  have hS : 0 ≤ ∑ k, f k ^ 2 / g k := Finset.sum_nonneg fun k _ => div_nonneg (sq_nonneg _) (hgpos k (Finset.mem_univ _)).le
  have h1 : (∑ k, f k) ^ 2 ≤ (∑ k, g k) * ∑ k, f k ^ 2 / g k := by
    rw [div_le_iff₀ hgsum_pos] at hT; linarith
  have h2 : (∑ k, g k) * ∑ k, f k ^ 2 / g k ≤ 1 / √(η ^ 2 - c ^ 2) * ∑ k, f k ^ 2 / g k :=
    mul_le_mul_of_nonneg_right hgsum hS
  rw [hgam]
  refine h1.trans (h2.trans (le_of_eq ?_))
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hfg k]
  unfold chebEta
  have h3 : 0 < √(η ^ 2 - c ^ 2) := Real.sqrt_pos.2 hb2
  have h4 := hq k
  field_simp

/-- **The Schur bound**: `∫_c^R Γ² ≤ π Σ_k a_k²` at `c = πn ≤ R`. -/
theorem integral_gam_sq_le {n : ℕ} (hn : 1 ≤ n) (a : Fin n → ℝ) {R : ℝ} (hR : π * n ≤ R) :
    ∫ η in (π * n)..R, gam a η ^ 2 ≤ π * ∑ k : Fin n, a k ^ 2 := by
  set c := π * (n : ℝ) with hc
  have hcont : ContinuousOn (fun η => gam a η ^ 2) (Icc c R) := fun η hη =>
    ((hasDerivAt_gam a hη.1).continuousAt.pow 2).continuousWithinAt
  have hint_k : ∀ k : Fin n, IntervalIntegrable (chebEta c (π * (k : ℕ))) volume c R := fun k =>
    (chebEta_integral (by positivity) (pole_lt_c k) hR).1
  have hRHS : IntervalIntegrable (fun η => ∑ k : Fin n, a k ^ 2 * √(c ^ 2 - (π * (k : ℕ)) ^ 2)
      * chebEta c (π * (k : ℕ)) η) volume c R := by
    have := IntervalIntegrable.sum (s := Finset.univ) (fun k _ => (hint_k k).const_mul
      (a k ^ 2 * √(c ^ 2 - (π * (k : ℕ)) ^ 2)))
    exact this.congr (fun η _ => by simp only [Finset.sum_apply])
  have hle : ∫ η in c..R, gam a η ^ 2 ≤ ∫ η in c..R, ∑ k : Fin n, a k ^ 2 * √(c ^ 2 - (π * (k : ℕ)) ^ 2)
      * chebEta c (π * (k : ℕ)) η := by
    rw [intervalIntegral.integral_of_le hR, intervalIntegral.integral_of_le hR]
    refine setIntegral_mono_on ?_ hRHS.1 measurableSet_Ioc fun η hη => gam_sq_le hn a hη.1
    exact (hcont.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  refine hle.trans ?_
  rw [intervalIntegral.integral_finsetSum (fun k _ => (hint_k k).const_mul _)]
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [intervalIntegral.integral_const_mul]
  have hb := (chebEta_integral (by positivity) (pole_lt_c k) hR).2
  have hr : 0 < c ^ 2 - (π * (k : ℕ)) ^ 2 := by
    have h1 := pole_lt_c k
    have : 0 ≤ π * ((k : ℕ) : ℝ) := by positivity
    rw [hc]; nlinarith
  have hs : 0 < √(c ^ 2 - (π * (k : ℕ)) ^ 2) := Real.sqrt_pos.2 hr
  calc a k ^ 2 * √(c ^ 2 - (π * (k : ℕ)) ^ 2) * ∫ η in c..R, chebEta c (π * (k : ℕ)) η
      ≤ a k ^ 2 * √(c ^ 2 - (π * (k : ℕ)) ^ 2) * (π / √(c ^ 2 - (π * (k : ℕ)) ^ 2)) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = π * a k ^ 2 * (√(c ^ 2 - (π * (k : ℕ)) ^ 2) / √(c ^ 2 - (π * (k : ℕ)) ^ 2)) := by ring
    _ = π * a k ^ 2 := by rw [div_self hs.ne', mul_one]

/-! ### The tail of the transform -/

theorem continuousOn_gam2 {n : ℕ} (a : Fin n → ℝ) {c R : ℝ} (hc : π * n ≤ c) :
    ContinuousOn (gam2 a) (Icc c R) := by
  have hk : ∀ k : Fin n, ContinuousOn (fun η : ℝ => |a k| * (2 * ((η - π * (k : ℕ)) ^ 3)⁻¹
      + 2 * ((η + π * (k : ℕ)) ^ 3)⁻¹)) (Icc c R) := by
    intro k
    have h1 : ContinuousOn (fun η : ℝ => ((η - π * (k : ℕ)) ^ 3)⁻¹) (Icc c R) := by
      have hf : ContinuousOn (fun η : ℝ => (η - π * (k : ℕ)) ^ 3) (Icc c R) :=
        (continuousOn_id.sub continuousOn_const).pow 3
      have h0 : ∀ η ∈ Icc c R, (η - π * (k : ℕ)) ^ 3 ≠ 0 := fun η hη => by
        have := pole_lt (hc.trans hη.1) k
        have : 0 < η - π * (k : ℕ) := by linarith
        exact pow_ne_zero _ this.ne'
      exact ContinuousOn.inv₀ hf h0
    have h2 : ContinuousOn (fun η : ℝ => ((η + π * (k : ℕ)) ^ 3)⁻¹) (Icc c R) := by
      have hf : ContinuousOn (fun η : ℝ => (η + π * (k : ℕ)) ^ 3) (Icc c R) :=
        (continuousOn_id.add continuousOn_const).pow 3
      have h0 : ∀ η ∈ Icc c R, (η + π * (k : ℕ)) ^ 3 ≠ 0 := fun η hη => by
        have := pole_lt' (hc.trans hη.1) k
        positivity
      exact ContinuousOn.inv₀ hf h0
    exact continuousOn_const.mul ((continuousOn_const.mul h1).add (continuousOn_const.mul h2))
  have h := continuousOn_finsetSum (Finset.univ : Finset (Fin n)) fun k _ => hk k
  unfold gam2
  exact h.congr fun η _ => by simp only

/-- **The tail on `[c, R]`**: `∫_c^R C² ≤ (π/2) Σ_k a_k²` at `c = πn`, `sin R = 0`. -/
theorem integral_cosHat_sq_le {n : ℕ} (hn : 1 ≤ n) (a : Fin n → ℝ) {R : ℝ} (hR : π * n ≤ R) (hRs : sin R = 0) :
    ∫ η in (π * n)..R, cosHat a η ^ 2 ≤ π / 2 * ∑ k : Fin n, a k ^ 2 := by
  set c := π * (n : ℝ) with hc
  have hcs : sin c = 0 := by rw [hc, mul_comm]; exact sin_nat_mul_pi n
  have hu : uIcc c R = Icc c R := uIcc_of_le hR
  have hH : ∀ η ∈ uIcc c R, HasDerivAt (fun η => gam a η ^ 2) (2 * gam a η * gam1 a η) η := by
    intro η hη
    rw [hu] at hη
    have h := (hasDerivAt_gam a hη.1).fun_pow 2
    exact h.congr_deriv (by norm_num)
  have hH₁ : ∀ η ∈ uIcc c R, HasDerivAt (fun η => 2 * gam a η * gam1 a η)
      (2 * (gam1 a η * gam1 a η + gam a η * gam2 a η)) η := by
    intro η hη
    rw [hu] at hη
    have h := ((hasDerivAt_gam a hη.1).const_mul 2).mul (hasDerivAt_gam1 a hη.1)
    exact h.congr_deriv (by ring)
  have hH₂c : ContinuousOn (fun η => 2 * (gam1 a η * gam1 a η + gam a η * gam2 a η)) (uIcc c R) := by
    rw [hu]
    have h1 : ContinuousOn (gam a) (Icc c R) := fun η hη =>
      (hasDerivAt_gam a hη.1).continuousAt.continuousWithinAt
    have h2 : ContinuousOn (gam1 a) (Icc c R) := fun η hη =>
      (hasDerivAt_gam1 a hη.1).continuousAt.continuousWithinAt
    exact continuousOn_const.mul ((h2.mul h2).add (h1.mul (continuousOn_gam2 a le_rfl)))
  have hH₂ : ∀ η ∈ uIcc c R, 0 ≤ 2 * (gam1 a η * gam1 a η + gam a η * gam2 a η) := by
    intro η hη
    rw [hu] at hη
    have := gam_nonneg a hη.1
    have := gam2_nonneg a hη.1
    have := mul_self_nonneg (gam1 a η)
    positivity
  have hsin := integral_sin_sq_mul_le hR hcs hRs hH hH₁ hH₂c hH₂
  have hgam := integral_gam_sq_le hn a hR
  have hmono : ∫ η in c..R, cosHat a η ^ 2 ≤ ∫ η in c..R, sin η ^ 2 * gam a η ^ 2 := by
    refine intervalIntegral.integral_mono_on hR ?_ ?_ fun η hη => cosHat_sq_le a hη.1
    · exact ((continuous_cosHat a).pow 2).intervalIntegrable _ _
    · refine ContinuousOn.intervalIntegrable ?_
      rw [hu]
      exact (continuous_sin.pow 2).continuousOn.mul (fun η hη =>
        ((hasDerivAt_gam a hη.1).continuousAt.pow 2).continuousWithinAt)
  calc ∫ η in c..R, cosHat a η ^ 2 ≤ ∫ η in c..R, sin η ^ 2 * gam a η ^ 2 := hmono
    _ ≤ 1 / 2 * ∫ η in c..R, gam a η ^ 2 := hsin
    _ ≤ 1 / 2 * (π * ∑ k : Fin n, a k ^ 2) := mul_le_mul_of_nonneg_left hgam (by norm_num)
    _ = π / 2 * ∑ k : Fin n, a k ^ 2 := by ring

/-- `C` is square integrable on `(0, ∞)`: it is `psi 1 f_a`. -/
theorem integrableOn_cosHat_sq {n : ℕ} (a : Fin n → ℝ) :
    IntegrableOn (fun η => cosHat a η ^ 2) (Ioi 0) := by
  have hgc : ContinuousOn (cosPoly a) (Icc (-1 : ℝ) 1) := (continuous_cosPoly a).continuousOn
  have heven : ∀ s ∈ Icc (-1 : ℝ) 1, cosPoly a (-s) = cosPoly a s := fun s _ => cosPoly_neg a s
  have hm := Cvs.Prolate.RungMirrorIdentity.memLp_psi (c := 1) one_pos hgc heven
  have := (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).1 hm
  refine this.congr (ae_of_all _ fun η => ?_)
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs, psi_cosPoly, one_mul]

/-- **The tail of the transform**: `∫_c^∞ C² ≤ (π/2) Σ_k a_k²` at `c = πn`. -/
theorem integral_Ioi_cosHat_sq_le {n : ℕ} (hn : 1 ≤ n) (a : Fin n → ℝ) :
    ∫ η in Ioi (π * n), cosHat a η ^ 2 ≤ π / 2 * ∑ k : Fin n, a k ^ 2 := by
  have hint : IntegrableOn (fun η => cosHat a η ^ 2) (Ioi (π * n)) :=
    (integrableOn_cosHat_sq a).mono_set (Ioi_subset_Ioi (by positivity))
  have hb : Tendsto (fun m : ℕ => π * ((n + m : ℕ) : ℝ)) atTop atTop := by
    refine Tendsto.const_mul_atTop pi_pos ?_
    exact tendsto_natCast_atTop_atTop.comp (tendsto_atTop_atTop.2 fun b => ⟨b, fun m hm => by omega⟩)
  have hT := intervalIntegral_tendsto_integral_Ioi (π * n) hint hb
  refine le_of_tendsto hT (Filter.Eventually.of_forall fun m => ?_)
  have hR : π * (n : ℝ) ≤ π * ((n + m : ℕ) : ℝ) := by
    apply mul_le_mul_of_nonneg_left _ pi_pos.le
    exact_mod_cast Nat.le_add_right n m
  have hRs : sin (π * ((n + m : ℕ) : ℝ)) = 0 := by rw [mul_comm]; exact sin_nat_mul_pi _
  exact integral_cosHat_sq_le hn a hR hRs

/-- **The tail of `ψ`**: `∫_1^∞ (psi c f_a)² ≤ (π/2c) Σ_k a_k²` at `c = πn`. -/
theorem integral_Ioi_psi_sq_le {n : ℕ} (hn : 1 ≤ n) (a : Fin n → ℝ) :
    ∫ ξ in Ioi 1, Cvs.L2a.AngularProlateTailPositive.psi (π * n) (cosPoly a) ξ ^ 2
      ≤ π / (2 * (π * n)) * ∑ k : Fin n, a k ^ 2 := by
  have hc : 0 < π * (n : ℝ) := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    positivity
  simp_rw [psi_cosPoly]
  rw [integral_comp_mul_left_Ioi (fun η => cosHat a η ^ 2) 1 hc, mul_one, smul_eq_mul]
  have := integral_Ioi_cosHat_sq_le hn a
  calc (π * n)⁻¹ * ∫ η in Ioi (π * n), cosHat a η ^ 2 ≤ (π * n)⁻¹ * (π / 2 * ∑ k : Fin n, a k ^ 2) :=
        mul_le_mul_of_nonneg_left this (inv_nonneg.2 hc.le)
    _ = π / (2 * (π * n)) * ∑ k : Fin n, a k ^ 2 := by field_simp

/-! ### The norm on the cosine span -/

/-- `∫_{−1}^{1} cos(πks) cos(πls) ds = [k = l] + [k = 0][l = 0]`. -/
theorem integral_cos_pi_mul_cos_pi (k l : ℕ) :
    ∫ s in (-1 : ℝ)..1, cos (π * k * s) * cos (π * l * s)
      = (if k = l then 1 else 0) + (if k = 0 then 1 else 0) * (if l = 0 then 1 else 0) := by
  rw [Cvs.Prolate.PlungeMassTrace.integral_cos_mul_cos]
  have hsub : sinc (π * k - π * l) = if k = l then 1 else 0 := by
    split_ifs with h
    · subst h; simp
    · have hne : ((k : ℤ) - l : ℤ) ≠ 0 := sub_ne_zero.2 (by exact_mod_cast h)
      have hx : π * k - π * l = (((k : ℤ) - l : ℤ) : ℝ) * π := by push_cast; ring
      rw [hx, sinc_of_ne_zero (mul_ne_zero (by exact_mod_cast hne) pi_ne_zero), sin_int_mul_pi, zero_div]
  have hadd : sinc (π * k + π * l) = (if k = 0 then 1 else 0) * (if l = 0 then 1 else 0) := by
    by_cases h : k = 0 ∧ l = 0
    · obtain ⟨rfl, rfl⟩ := h; simp
    · have hkl : (k + l : ℕ) ≠ 0 := by omega
      have hx : π * k + π * l = ((k + l : ℕ) : ℝ) * π := by push_cast; ring
      rw [hx, sinc_of_ne_zero (mul_ne_zero (by exact_mod_cast hkl) pi_ne_zero), sin_nat_mul_pi, zero_div]
      rcases not_and_or.1 h with h | h <;> simp [h]
  rw [hsub, hadd]

/-- `∫_{−1}^{1} f_a² = Σ_k a_k² + a_0² ≥ Σ_k a_k²`. -/
theorem sum_sq_le_integral_cosPoly_sq {n : ℕ} (a : Fin n → ℝ) :
    ∑ k : Fin n, a k ^ 2 ≤ ∫ s in (-1 : ℝ)..1, cosPoly a s ^ 2 := by
  have e : ∀ s, cosPoly a s ^ 2 = ∑ k : Fin n, ∑ l : Fin n, a k * a l * (cos (π * (k : ℕ) * s) * cos (π * (l : ℕ) * s)) := by
    intro s
    unfold cosPoly
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  simp_rw [e]
  have hI : ∀ k l : Fin n, IntervalIntegrable (fun s => a k * a l * (cos (π * (k : ℕ) * s) * cos (π * (l : ℕ) * s)))
      volume (-1) 1 := fun k l => by apply Continuous.intervalIntegrable; fun_prop
  have hI' : ∀ k ∈ (Finset.univ : Finset (Fin n)), IntervalIntegrable
      (fun s => ∑ l : Fin n, a k * a l * (cos (π * (k : ℕ) * s) * cos (π * (l : ℕ) * s))) volume (-1) 1 :=
    fun k _ => by apply Continuous.intervalIntegrable; fun_prop
  rw [intervalIntegral.integral_finsetSum hI']
  simp_rw [intervalIntegral.integral_finsetSum (fun l _ => hI _ l), intervalIntegral.integral_const_mul,
    integral_cos_pi_mul_cos_pi]
  have h2 : ∀ k : Fin n, ∑ l : Fin n, a k * a l * ((if (k : ℕ) = l then 1 else 0)
      + (if (k : ℕ) = 0 then 1 else 0) * (if (l : ℕ) = 0 then 1 else 0))
      = a k ^ 2 + (a k * (if (k : ℕ) = 0 then 1 else 0)) * ∑ l : Fin n, a l * (if (l : ℕ) = 0 then 1 else 0) := by
    intro k
    have hδ : ∑ l : Fin n, a k * a l * (if (k : ℕ) = l then (1 : ℝ) else 0) = a k ^ 2 := by
      rw [Finset.sum_eq_single k]
      · simp [sq]
      · intro l _ hlk
        have : (k : ℕ) ≠ l := fun h => hlk (Fin.ext h).symm
        simp [this]
      · simp
    have hsplit : ∑ l : Fin n, a k * a l * ((if (k : ℕ) = l then 1 else 0)
        + (if (k : ℕ) = 0 then 1 else 0) * (if (l : ℕ) = 0 then 1 else 0))
        = ∑ l : Fin n, a k * a l * (if (k : ℕ) = l then (1 : ℝ) else 0)
          + ∑ l : Fin n, (a k * (if (k : ℕ) = 0 then 1 else 0)) * (a l * (if (l : ℕ) = 0 then 1 else 0)) := by
      rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun l _ => by ring
    rw [hsplit, hδ, Finset.mul_sum]
  simp_rw [h2]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul]
  have : 0 ≤ (∑ k : Fin n, a k * (if (k : ℕ) = 0 then 1 else 0)) * ∑ l : Fin n, a l * (if (l : ℕ) = 0 then 1 else 0) :=
    mul_self_nonneg _
  linarith

/-! ### The sinc form through the cosine transform -/

/-- For `f` even: `∫_{−1}^{1} kS(s − t) f(t) dt = (c/2π) ∫_{−1}^{1} cos(csx) ψ(x) dx`, `ψ = psi c f`. -/
theorem integral_kS_mul {c : ℝ} (hc : 0 < c) {f : ℝ → ℝ} (hf : Continuous f) (heven : ∀ s, f (-s) = f s) (s : ℝ) :
    ∫ t in (-1 : ℝ)..1, Cvs.Prolate.PlungeMassTrace.kS c (s - t) * f t
      = c / (2 * π) * ∫ x in (-1 : ℝ)..1, cos (c * s * x) * Cvs.L2a.AngularProlateTailPositive.psi c f x := by
  have hK := Cvs.Prolate.PlungeMassTrace.continuous_kS c
  -- `∫ kS(s + t) f(t) dt = ∫ kS(s − t) f(t) dt`
  have hrefl : ∫ t in (-1 : ℝ)..1, Cvs.Prolate.PlungeMassTrace.kS c (s + t) * f t
      = ∫ t in (-1 : ℝ)..1, Cvs.Prolate.PlungeMassTrace.kS c (s - t) * f t := by
    have h := intervalIntegral.integral_comp_neg (a := (-1 : ℝ)) (b := 1)
      (fun t => Cvs.Prolate.PlungeMassTrace.kS c (s - t) * f t)
    simp only [sub_neg_eq_add, heven, neg_neg] at h
    exact h
  have hkE : ∫ t in (-1 : ℝ)..1, Cvs.Prolate.PlungeMassTrace.kS c (s - t) * f t
      = ∫ t in (-1 : ℝ)..1, Cvs.Prolate.PlungeMassTrace.kE c s t * f t := by
    unfold Cvs.Prolate.PlungeMassTrace.kE
    have e : ∀ t, (Cvs.Prolate.PlungeMassTrace.kS c (s - t) + Cvs.Prolate.PlungeMassTrace.kS c (s + t)) / 2 * f t
        = (Cvs.Prolate.PlungeMassTrace.kS c (s - t) * f t + Cvs.Prolate.PlungeMassTrace.kS c (s + t) * f t) / 2 := by
      intro t; ring
    simp_rw [e]
    rw [intervalIntegral.integral_div, intervalIntegral.integral_add, hrefl]
    · ring
    · apply Continuous.intervalIntegrable; fun_prop
    · apply Continuous.intervalIntegrable; fun_prop
  rw [hkE]
  have hrep : ∀ t, Cvs.Prolate.PlungeMassTrace.kE c s t * f t
      = c / (2 * π) * (f t * ∫ x in (-1 : ℝ)..1, cos (c * s * x) * cos (c * t * x)) := by
    intro t
    rw [Cvs.Prolate.PlungeMassTrace.integral_cos_cos_eq_kE hc.ne']
    field_simp
  simp_rw [hrep]
  rw [intervalIntegral.integral_const_mul]
  congr 1
  have hsw := Cvs.Prolate.CosineChristoffelDarboux.swap_cos c (u := f) (v := fun x => cos (c * s * x)) hf.continuousOn
    (by fun_prop)
  rw [hsw]
  rfl

/-- **The sinc form is the low mass of `ψ`**: for `f` even continuous,
`∫∫_{[−1,1]²} f(s) kS(s − t) f(t) = (c/π) ∫_0^1 ψ²`. -/
theorem sincForm_eq {c : ℝ} (hc : 0 < c) {f : ℝ → ℝ} (hf : Continuous f) (heven : ∀ s, f (-s) = f s) :
    ∫ s in (-1 : ℝ)..1, ∫ t in (-1 : ℝ)..1, f s * Cvs.Prolate.PlungeMassTrace.kS c (s - t) * f t
      = c / π * ∫ ξ in (0 : ℝ)..1, Cvs.L2a.AngularProlateTailPositive.psi c f ξ ^ 2 := by
  have hψc : Continuous (Cvs.L2a.AngularProlateTailPositive.psi c f) :=
    Cvs.Prolate.PlungeMassTrace.continuous_psi hf.continuousOn
  have hinner : ∀ s, ∫ t in (-1 : ℝ)..1, f s * Cvs.Prolate.PlungeMassTrace.kS c (s - t) * f t
      = c / (2 * π) * (f s * ∫ x in (-1 : ℝ)..1, Cvs.L2a.AngularProlateTailPositive.psi c f x * cos (c * s * x)) := by
    intro s
    have e : ∀ t, f s * Cvs.Prolate.PlungeMassTrace.kS c (s - t) * f t
        = f s * (Cvs.Prolate.PlungeMassTrace.kS c (s - t) * f t) := fun t => by ring
    simp_rw [e]
    rw [intervalIntegral.integral_const_mul, integral_kS_mul hc hf heven s]
    have e2 : ∀ x, cos (c * s * x) * Cvs.L2a.AngularProlateTailPositive.psi c f x
        = Cvs.L2a.AngularProlateTailPositive.psi c f x * cos (c * s * x) := fun x => by ring
    simp_rw [e2]
    ring
  simp_rw [hinner]
  rw [intervalIntegral.integral_const_mul]
  have hsw := Cvs.Prolate.CosineChristoffelDarboux.swap_cos c (u := f) (v := Cvs.L2a.AngularProlateTailPositive.psi c f) hf.continuousOn
    hψc.continuousOn
  rw [hsw]
  have hsq : ∫ x in (-1 : ℝ)..1, Cvs.L2a.AngularProlateTailPositive.psi c f x * (∫ s in (-1 : ℝ)..1, f s * cos (c * x * s))
      = ∫ x in (-1 : ℝ)..1, Cvs.L2a.AngularProlateTailPositive.psi c f x ^ 2 := by
    refine intervalIntegral.integral_congr fun x _ => ?_
    show Cvs.L2a.AngularProlateTailPositive.psi c f x * Cvs.L2a.AngularProlateTailPositive.psi c f x = _
    ring
  rw [hsq]
  have hψeven : ∀ x ∈ Icc (-1 : ℝ) 1, Cvs.L2a.AngularProlateTailPositive.psi c f (-x) = Cvs.L2a.AngularProlateTailPositive.psi c f x := by
    intro x _
    show ∫ s in (-1 : ℝ)..1, f s * cos (c * -x * s) = ∫ s in (-1 : ℝ)..1, f s * cos (c * x * s)
    refine intervalIntegral.integral_congr fun s _ => ?_
    rw [show c * -x * s = -(c * x * s) by ring, cos_neg]
  rw [Cvs.Prolate.AngularBesselInequality.integral_sq_even hψc.continuousOn hψeven]
  field_simp

/-! ### Landau's half on the cosine span -/

/-- **Landau's half on the cosine span**: at `c = πn`, every `f = Σ_{k<n} a_k cos(πkt)` has
`∫∫_{[−1,1]²} f(s) kS(s − t) f(t) ds dt ≥ ½ ∫_{−1}^{1} f²`. -/
theorem sincForm_ge_half {n : ℕ} (hn : 1 ≤ n) (a : Fin n → ℝ) :
    1 / 2 * ∫ s in (-1 : ℝ)..1, cosPoly a s ^ 2
      ≤ ∫ s in (-1 : ℝ)..1, ∫ t in (-1 : ℝ)..1,
          cosPoly a s * Cvs.Prolate.PlungeMassTrace.kS (π * n) (s - t) * cosPoly a t := by
  set c := π * (n : ℝ) with hcdef
  have hc : 0 < c := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    positivity
  have hf : Continuous (cosPoly a) := continuous_cosPoly a
  have heven : ∀ s, cosPoly a (-s) = cosPoly a s := cosPoly_neg a
  rw [sincForm_eq hc hf heven]
  have hN := Cvs.Prolate.RungMirrorIdentity.norm_psi_sq hc hf.continuousOn (fun s _ => heven s)
  have hm := Cvs.Prolate.RungMirrorIdentity.memLp_psi hc hf.continuousOn (fun s _ => heven s)
  have hInt : IntegrableOn (fun ξ => Cvs.L2a.AngularProlateTailPositive.psi c (cosPoly a) ξ ^ 2) (Ioi 0) := by
    have := (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).1 hm
    refine this.congr (ae_of_all _ fun ξ => ?_)
    simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hsplit : ∫ ξ in Ioi 0, Cvs.L2a.AngularProlateTailPositive.psi c (cosPoly a) ξ ^ 2
      = (∫ ξ in (0 : ℝ)..1, Cvs.L2a.AngularProlateTailPositive.psi c (cosPoly a) ξ ^ 2)
        + ∫ ξ in Ioi 1, Cvs.L2a.AngularProlateTailPositive.psi c (cosPoly a) ξ ^ 2 := by
    rw [intervalIntegral.integral_of_le zero_le_one, ← setIntegral_union (Ioc_disjoint_Ioi le_rfl)
      measurableSet_Ioi (hInt.mono_set Ioc_subset_Ioi_self) (hInt.mono_set (Ioi_subset_Ioi zero_le_one)),
      Ioc_union_Ioi_eq_Ioi zero_le_one]
  have htail := integral_Ioi_psi_sq_le hn a
  rw [← hcdef] at htail
  have hnorm := sum_sq_le_integral_cosPoly_sq a
  have hfe := Cvs.Prolate.AngularBesselInequality.integral_sq_even hf.continuousOn (fun s _ => heven s)
  set A := ∫ ξ in (0 : ℝ)..1, Cvs.L2a.AngularProlateTailPositive.psi c (cosPoly a) ξ ^ 2
  set T := ∫ ξ in Ioi 1, Cvs.L2a.AngularProlateTailPositive.psi c (cosPoly a) ξ ^ 2
  set P := ∫ ξ in Ioi 0, Cvs.L2a.AngularProlateTailPositive.psi c (cosPoly a) ξ ^ 2
  set S := ∑ k : Fin n, a k ^ 2
  set F0 := ∫ s in (0 : ℝ)..1, cosPoly a s ^ 2
  have hπ : 0 < π := pi_pos
  have h1 : c / π * P = 2 * F0 := by
    have : c / π * P = 2 * (c / (2 * π) * P) := by field_simp
    rw [this, hN]
  have h2 : c / π * T ≤ S / 2 := by
    calc c / π * T ≤ c / π * (π / (2 * c) * S) := mul_le_mul_of_nonneg_left htail (by positivity)
      _ = S / 2 := by field_simp
  have h3 : c / π * A = c / π * P - c / π * T := by rw [hsplit]; ring
  rw [h3]
  linarith

end Cvs.Prolate.LandauHalfCosineSpan
