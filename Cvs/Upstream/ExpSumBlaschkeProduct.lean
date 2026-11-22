import Mathlib
import Cvs.Upstream.RightHalfPlaneCauchyHardy

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Finite exponential sums on the half-line and their Blaschke products

For `p_i` in `Re > 0`, `h_a(u) = Σ a_i e^{−p̄_i u}` has Laplace transform `L_a(w) = Σ a_i/(w + p̄_i)` and Gram
value `G(a) = Σ_k ā_k L_a(p_k)`. Cvs.Upstream.RightHalfPlaneCauchyHardy gives `∫ |L_a(iy)|² dy = 2π Re G(a)` and `|L_a(w)|² ≤ Re G(a)/(2 Re w)`.
With `B = Π (w − p_i)/(w + p̄_i)` and `R_a = Σ ā_i/(z − p_i)`, `B R_a` has `L_a`'s boundary modulus, so
`|R_a(z)|²|B(z)|² ≤ Re G(a)/(2 Re z)`, and for distinct points `Re G(a) = 0` forces `a = 0`.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology Finset
open scoped Interval ComplexConjugate

namespace Cvs.Upstream.ExpSumBlaschkeProduct

set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The objects -/

/-- The Laplace transform `L_a(w) = Σ a_i/(w + p̄_i)` of `h_a`. -/
def lap (p a : ι → ℂ) (w : ℂ) : ℂ := ∑ i, a i / (w + conj (p i))

/-- The Gram value `G(a) = Σ_k ā_k L_a(p_k)`. -/
def gram (p a : ι → ℂ) : ℂ := ∑ k, conj (a k) * lap p a (p k)

/-- The Blaschke factor `(w − q)/(w + q̄)`. -/
def bfac (q w : ℂ) : ℂ := (w - q) / (w + conj q)

/-- The finite Blaschke product `B(w) = Π_i (w − p_i)/(w + p̄_i)`. -/
def blaschke (p : ι → ℂ) (w : ℂ) : ℂ := ∏ i, bfac (p i) w

/-- The Cauchy sum `R_a(z) = Σ ā_i/(z − p_i)`. -/
def res (p a : ι → ℂ) (z : ℂ) : ℂ := ∑ i, conj (a i) / (z - p i)

/-- The product `B R_a`, written without the removable poles: `Σ_i ā_i Π_{j ≠ i} b_j(z)/(z + p̄_i)`. -/
def qfun (p a : ι → ℂ) (z : ℂ) : ℂ :=
  ∑ i, conj (a i) * (∏ j ∈ univ.erase i, bfac (p j) z) / (z + conj (p i))

/-! ### Elementary facts on `Re w ≥ 0` -/

/-- `|w + q̄|² − |w − q|² = 4 Re w Re q`. -/
theorem normSq_add_conj_sub (q w : ℂ) :
    ‖w + conj q‖ ^ 2 - ‖w - q‖ ^ 2 = 4 * w.re * q.re := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
    Complex.normSq_apply]
  simp; ring

/-- `w + q̄ ≠ 0` for `Re w ≥ 0`, `Re q > 0`. -/
theorem add_conj_ne_zero {q w : ℂ} (hq : 0 < q.re) (hw : 0 ≤ w.re) : w + conj q ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this; linarith

/-- `w + q̄ ≠ 0` whenever `Re w > −Re q`. -/
theorem add_conj_ne_zero' {q w : ℂ} (hw : -q.re < w.re) : w + conj q ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this; linarith

/-- `|b_q(w)| ≤ 1` on `Re w ≥ 0`. -/
theorem norm_bfac_le_one {q w : ℂ} (hq : 0 < q.re) (hw : 0 ≤ w.re) : ‖bfac q w‖ ≤ 1 := by
  have h0 := add_conj_ne_zero hq hw
  have hpos : 0 < ‖w + conj q‖ := norm_pos_iff.2 h0
  rw [bfac, norm_div, div_le_one hpos]
  have h := normSq_add_conj_sub q w
  have : ‖w - q‖ ^ 2 ≤ ‖w + conj q‖ ^ 2 := by nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hpos.le two_ne_zero).1 this

/-- `|b_q(iy)| = 1`. -/
theorem norm_bfac_I (q : ℂ) (hq : 0 < q.re) (y : ℝ) : ‖bfac q (y * I)‖ = 1 := by
  have hre : ((y : ℂ) * I).re = 0 := by simp
  have h0 := add_conj_ne_zero hq hre.ge
  rw [bfac, norm_div, div_eq_one_iff_eq (norm_ne_zero_iff.2 h0)]
  have h := normSq_add_conj_sub q (y * I)
  rw [hre] at h
  have : ‖(y : ℂ) * I - q‖ ^ 2 = ‖(y : ℂ) * I + conj q‖ ^ 2 := by linarith
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this

/-- `|B(w)| ≤ 1` on `Re w ≥ 0`. -/
theorem norm_prod_bfac_le_one {p : ι → ℂ} (hp : ∀ i, 0 < (p i).re) (s : Finset ι) {w : ℂ}
    (hw : 0 ≤ w.re) : ‖∏ j ∈ s, bfac (p j) w‖ ≤ 1 := by
  rw [norm_prod]
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun j _ => norm_bfac_le_one (hp j) hw

/-- `|B(iy)| = 1`. -/
theorem norm_prod_bfac_I {p : ι → ℂ} (hp : ∀ i, 0 < (p i).re) (s : Finset ι) (y : ℝ) :
    ‖∏ j ∈ s, bfac (p j) (y * I)‖ = 1 := by
  rw [norm_prod]
  exact Finset.prod_eq_one fun j _ => norm_bfac_I (p j) (hp j) y

/-- `|w + q̄| ≥ |w|/2` once `|w| ≥ 2|q|`. -/
theorem half_norm_le_norm_add_conj {q w : ℂ} (h : 2 * ‖q‖ ≤ ‖w‖) : ‖w‖ / 2 ≤ ‖w + conj q‖ := by
  have := norm_sub_norm_le w (-conj q)
  rw [sub_neg_eq_add, norm_neg, Complex.norm_conj] at this
  linarith

/-! ### Holomorphy and decay -/

/-- A radius beyond which every `|w + p̄_i| ≥ |w|/2`. -/
def rad (p : ι → ℂ) : ℝ := 2 * ∑ i, ‖p i‖

theorem two_norm_le_rad (p : ι → ℂ) (i : ι) : 2 * ‖p i‖ ≤ rad p := by
  unfold rad
  have := Finset.single_le_sum (f := fun i => ‖p i‖) (fun i _ => norm_nonneg _) (Finset.mem_univ i)
  linarith

/-- `L_a` is holomorphic on `Re w > −ε` when every `Re p_i ≥ ε`. -/
theorem differentiableOn_lap {p : ι → ℂ} {ε : ℝ} (hε : ∀ i, ε ≤ (p i).re) (a : ι → ℂ) :
    DifferentiableOn ℂ (lap p a) {s | -ε < s.re} := by
  intro w hw
  refine DifferentiableAt.differentiableWithinAt ?_
  unfold lap
  refine DifferentiableAt.fun_sum fun i _ => ?_
  refine (differentiableAt_const _).fun_div (by fun_prop) (add_conj_ne_zero' ?_)
  have := hε i; simp only [mem_ofPred_eq] at hw; linarith

/-- `|L_a(w)| ≤ 2Σ|a_i|/|w|` on `Re w ≥ 0`, `|w| ≥ rad p`. -/
theorem norm_lap_le {p : ι → ℂ} (hp : ∀ i, 0 < (p i).re) (a : ι → ℂ) {w : ℂ} (hR : rad p ≤ ‖w‖) :
    ‖lap p a w‖ ≤ (2 * ∑ i, ‖a i‖) / ‖w‖ := by
  unfold lap
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_le_sum fun i _ => ?_
  have hpi : 0 < ‖p i‖ := norm_pos_iff.2 fun h => by have := hp i; rw [h] at this; simp at this
  have h2 := (two_norm_le_rad p i).trans hR
  have hw0 : 0 < ‖w‖ := by linarith
  have hd := half_norm_le_norm_add_conj h2
  rw [norm_div]
  calc ‖a i‖ / ‖w + conj (p i)‖ ≤ ‖a i‖ / (‖w‖ / 2) :=
        div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) hd
    _ = 2 * ‖a i‖ / ‖w‖ := by field_simp

/-- The decay hypothesis of Cvs.Upstream.RightHalfPlaneCauchyHardy for `L_a`. -/
theorem lap_dec {p : ι → ℂ} (hp : ∀ i, 0 < (p i).re) (a : ι → ℂ) :
    ∀ s : ℂ, 0 ≤ s.re → rad p ≤ ‖s‖ → ‖lap p a s‖ ≤ (2 * ∑ i, ‖a i‖) / ‖s‖ :=
  fun _ _ h => norm_lap_le hp a h

/-! ### Plancherel and the pointwise bound for `L_a` -/

/-- `conj L_a(iy) = Σ ā_i/(p_i − iy)`. -/
theorem conj_lap_I (p a : ι → ℂ) (y : ℝ) :
    conj (lap p a (y * I)) = ∑ i, conj (a i) / (p i - y * I) := by
  unfold lap
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_div₀, map_add, Complex.conj_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  congr 1; ring

/-- **Plancherel for exponential sums**: `∫ |L_a(iy)|² dy = 2π Re G(a)`. -/
theorem integral_norm_sq_lap {p : ι → ℂ} {ε : ℝ} (hε0 : 0 < ε) (hε : ∀ i, ε ≤ (p i).re) (a : ι → ℂ) :
    ∫ y : ℝ, ‖lap p a (y * I)‖ ^ 2 = 2 * Real.pi * (gram p a).re := by
  have hp : ∀ i, 0 < (p i).re := fun i => hε0.trans_le (hε i)
  have hd := differentiableOn_lap hε a
  have hdec := lap_dec hp a
  have hint : ∀ i, Integrable fun y : ℝ => lap p a (y * I) / (p i - y * I) := fun i =>
    Cvs.Upstream.RightHalfPlaneCauchyHardy.integrable_div_sub_line hε0 hd hdec (hp i)
  have hpt : ∀ y : ℝ, (((‖lap p a (y * I)‖ ^ 2 : ℝ)) : ℂ)
      = ∑ i, conj (a i) * (lap p a (y * I) / (p i - y * I)) := by
    intro y
    rw [Complex.ofReal_pow, ← Complex.mul_conj', conj_lap_I, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hc : (((∫ y : ℝ, ‖lap p a (y * I)‖ ^ 2 : ℝ)) : ℂ) = 2 * Real.pi * gram p a := by
    rw [← integral_complex_ofReal, funext hpt, integral_finsetSum _ fun i _ => (hint i).const_mul _]
    simp_rw [integral_const_mul]
    rw [gram, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Cvs.Upstream.RightHalfPlaneCauchyHardy.integral_div_sub_eq hε0 hd hdec (hp i)]
    ring
  have := congrArg Complex.re hc
  rw [Complex.ofReal_re] at this
  rw [this]
  simp

/-- `Re G(a) ≥ 0`. -/
theorem gram_re_nonneg {p : ι → ℂ} {ε : ℝ} (hε0 : 0 < ε) (hε : ∀ i, ε ≤ (p i).re) (a : ι → ℂ) :
    0 ≤ (gram p a).re := by
  have h := integral_norm_sq_lap hε0 hε a
  have h0 := integral_nonneg (μ := (volume : Measure ℝ)) (f := fun y : ℝ => ‖lap p a (y * I)‖ ^ 2)
    fun y => sq_nonneg _
  rw [h] at h0
  have := Real.pi_pos
  exact nonneg_of_mul_nonneg_right (a := 2 * Real.pi) (by linarith) (by positivity)

/-- **The pointwise bound**: `|L_a(w)|² ≤ Re G(a)/(2 Re w)` for `Re w > 0`. -/
theorem norm_sq_lap_le {p : ι → ℂ} {ε : ℝ} (hε0 : 0 < ε) (hε : ∀ i, ε ≤ (p i).re) (a : ι → ℂ)
    {w : ℂ} (hw : 0 < w.re) : ‖lap p a w‖ ^ 2 ≤ (gram p a).re / (2 * w.re) := by
  have hp : ∀ i, 0 < (p i).re := fun i => hε0.trans_le (hε i)
  have hd := differentiableOn_lap hε a
  have h := Cvs.Upstream.RightHalfPlaneCauchyHardy.norm_sq_le hε0 hd (lap_dec hp a) (Cvs.Upstream.RightHalfPlaneCauchyHardy.integrable_norm_sq_line hε0 hd (lap_dec hp a)) hw
  rw [integral_norm_sq_lap hε0 hε a] at h
  refine h.trans_eq ?_
  have := Real.pi_pos
  field_simp
  ring

/-! ### The Blaschke product times the Cauchy sum -/

/-- `B R_a` is holomorphic on `Re z > −ε`. -/
theorem differentiableOn_qfun {p : ι → ℂ} {ε : ℝ} (hε : ∀ i, ε ≤ (p i).re) (a : ι → ℂ) :
    DifferentiableOn ℂ (qfun p a) {s | -ε < s.re} := by
  intro w hw
  simp only [mem_ofPred_eq] at hw
  refine DifferentiableAt.differentiableWithinAt ?_
  unfold qfun bfac
  refine DifferentiableAt.fun_sum fun i _ => ?_
  refine DifferentiableAt.fun_div ?_ (by fun_prop) (add_conj_ne_zero' (by linarith [hε i]))
  refine (differentiableAt_const _).mul ?_
  refine DifferentiableAt.fun_finsetProd fun j _ => ?_
  exact (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => z - p j) w).div (by fun_prop)
    (add_conj_ne_zero' (by linarith [hε j]))

/-- `|B R_a(z)| ≤ 2Σ|a_i|/|z|` on `Re z ≥ 0`, `|z| ≥ rad p`. -/
theorem qfun_dec {p : ι → ℂ} (hp : ∀ i, 0 < (p i).re) (a : ι → ℂ) :
    ∀ s : ℂ, 0 ≤ s.re → rad p ≤ ‖s‖ → ‖qfun p a s‖ ≤ (2 * ∑ i, ‖a i‖) / ‖s‖ := by
  intro w hw hR
  unfold qfun
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_le_sum fun i _ => ?_
  have hpi : 0 < ‖p i‖ := norm_pos_iff.2 fun h => by have := hp i; rw [h] at this; simp at this
  have h2 := (two_norm_le_rad p i).trans hR
  have hw0 : 0 < ‖w‖ := by linarith
  have hd := half_norm_le_norm_add_conj h2
  have hb := norm_prod_bfac_le_one hp (univ.erase i) hw
  rw [norm_div, norm_mul, Complex.norm_conj]
  calc ‖a i‖ * ‖∏ j ∈ univ.erase i, bfac (p j) w‖ / ‖w + conj (p i)‖ ≤ ‖a i‖ * 1 / (‖w‖ / 2) :=
        div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hb (norm_nonneg _)) (by positivity) hd
    _ = 2 * ‖a i‖ / ‖w‖ := by field_simp

/-- Off the points, `B R_a = B · R_a`. -/
theorem qfun_eq {p : ι → ℂ} (hp : ∀ i, 0 < (p i).re) (a : ι → ℂ) {z : ℂ} (hz : 0 ≤ z.re)
    (hzp : ∀ i, z ≠ p i) : qfun p a z = blaschke p z * res p a z := by
  unfold qfun blaschke res
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.mul_prod_erase univ (fun j => bfac (p j) z) (Finset.mem_univ i), bfac]
  have h1 : z - p i ≠ 0 := sub_ne_zero.2 (hzp i)
  have h2 := add_conj_ne_zero (hp i) hz
  field_simp

/-- On the imaginary axis `|B R_a(iy)| = |L_a(iy)|`. -/
theorem norm_qfun_I {p : ι → ℂ} (hp : ∀ i, 0 < (p i).re) (a : ι → ℂ) (y : ℝ) :
    ‖qfun p a (y * I)‖ = ‖lap p a (y * I)‖ := by
  have hre : ((y : ℂ) * I).re = 0 := by simp
  have hzp : ∀ i, (y : ℂ) * I ≠ p i := fun i h => by
    have := congrArg Complex.re h; rw [hre] at this; linarith [hp i]
  rw [qfun_eq hp a hre.ge hzp, norm_mul, blaschke, norm_prod_bfac_I hp univ y, one_mul,
    ← Complex.norm_conj (lap p a _), conj_lap_I, res]
  rw [← norm_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← div_neg, neg_sub]

/-- **The Cauchy sum against the Blaschke product**: `|B(z)R_a(z)|² ≤ Re G(a)/(2 Re z)` for `Re z > 0`. -/
theorem norm_sq_qfun_le {p : ι → ℂ} {ε : ℝ} (hε0 : 0 < ε) (hε : ∀ i, ε ≤ (p i).re) (a : ι → ℂ)
    {z : ℂ} (hz : 0 < z.re) : ‖qfun p a z‖ ^ 2 ≤ (gram p a).re / (2 * z.re) := by
  have hp : ∀ i, 0 < (p i).re := fun i => hε0.trans_le (hε i)
  have hd := differentiableOn_qfun hε a
  have h := Cvs.Upstream.RightHalfPlaneCauchyHardy.norm_sq_le hε0 hd (qfun_dec hp a) (Cvs.Upstream.RightHalfPlaneCauchyHardy.integrable_norm_sq_line hε0 hd (qfun_dec hp a)) hz
  have he : (fun y : ℝ => ‖qfun p a (y * I)‖ ^ 2) = fun y : ℝ => ‖lap p a (y * I)‖ ^ 2 := by
    funext y; rw [norm_qfun_I hp a y]
  rw [he, integral_norm_sq_lap hε0 hε a] at h
  refine h.trans_eq ?_
  have := Real.pi_pos
  field_simp
  ring

/-- `B` does not vanish off the points on `Re z ≥ 0`. -/
theorem blaschke_ne_zero {p : ι → ℂ} (hp : ∀ i, 0 < (p i).re) {z : ℂ} (hz : 0 ≤ z.re)
    (hzp : ∀ i, z ≠ p i) : blaschke p z ≠ 0 := by
  unfold blaschke
  rw [Finset.prod_ne_zero_iff]
  intro i _
  exact div_ne_zero (sub_ne_zero.2 (hzp i)) (add_conj_ne_zero (hp i) hz)

/-- **Definiteness**: for distinct points, `Re G(a) = 0` forces `a = 0`. -/
theorem eq_zero_of_gram_re_eq_zero {p : ι → ℂ} (hpi : Function.Injective p) {ε : ℝ} (hε0 : 0 < ε)
    (hε : ∀ i, ε ≤ (p i).re) {a : ι → ℂ} (h : (gram p a).re = 0) : a = 0 := by
  have hp : ∀ i, 0 < (p i).re := fun i => hε0.trans_le (hε i)
  have hres : ∀ z : ℂ, 0 < z.re → (∀ i, z ≠ p i) → res p a z = 0 := by
    intro z hz hzp
    have h1 := norm_sq_qfun_le hε0 hε a hz
    rw [h, zero_div] at h1
    have h2 : qfun p a z = 0 := by
      have := sq_nonneg ‖qfun p a z‖
      exact norm_eq_zero.1 (by nlinarith [norm_nonneg (qfun p a z)])
    rw [qfun_eq hp a hz.le hzp] at h2
    exact (mul_eq_zero.1 h2).resolve_left (blaschke_ne_zero hp hz.le hzp)
  funext k
  set g : ℂ → ℂ := fun z => conj (a k) + ∑ j ∈ univ.erase k, conj (a j) * (z - p k) / (z - p j) with hg
  have hgc : ContinuousAt g (p k) := by
    refine continuousAt_const.add ?_
    refine tendsto_finsetSum _ fun j hj => ?_
    have hne : p k - p j ≠ 0 := sub_ne_zero.2 fun h => (Finset.ne_of_mem_erase hj) (hpi h).symm
    exact (continuousAt_const.mul (continuousAt_id.sub continuousAt_const)).div₀
      (continuousAt_id.sub continuousAt_const) hne
  have hgk : g (p k) = conj (a k) := by
    simp [hg]
  have hev : ∀ᶠ z in 𝓝[≠] (p k), g z = 0 := by
    have h1 : ∀ᶠ z in 𝓝[≠] (p k), 0 < z.re :=
      mem_nhdsWithin_of_mem_nhds ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds (hp k))
    have h2 : ∀ᶠ z in 𝓝[≠] (p k), ∀ j, j ≠ k → z ≠ p j := by
      refine mem_nhdsWithin_of_mem_nhds (Filter.eventually_all.2 fun j => ?_)
      by_cases hj : j = k
      · exact Eventually.of_forall fun _ h => absurd hj h
      · exact (eventually_ne_nhds fun h => hj (hpi h).symm).mono fun _ hz _ => hz
    have h3 : ∀ᶠ z in 𝓝[≠] (p k), z ≠ p k := self_mem_nhdsWithin
    filter_upwards [h1, h2, h3] with z hz1 hz2 hz3
    have hzp : ∀ i, z ≠ p i := fun i => by
      by_cases hi : i = k
      · rw [hi]; exact hz3
      · exact hz2 i hi
    have hr := hres z hz1 hzp
    have hzk : z - p k ≠ 0 := sub_ne_zero.2 hz3
    have : g z = (z - p k) * res p a z := by
      simp only [hg, res]
      rw [← Finset.add_sum_erase univ _ (Finset.mem_univ k), mul_add, Finset.mul_sum]
      congr 1
      · field_simp
      · refine Finset.sum_congr rfl fun j hj => ?_
        ring
    rw [this, hr, mul_zero]
  have hlim : Tendsto g (𝓝[≠] (p k)) (𝓝 (g (p k))) := hgc.tendsto.mono_left nhdsWithin_le_nhds
  have hlim0 : Tendsto g (𝓝[≠] (p k)) (𝓝 0) := tendsto_const_nhds.congr' (hev.mono fun z h => h.symm)
  have := tendsto_nhds_unique hlim hlim0
  rw [hgk] at this
  simpa using this

end Cvs.Upstream.ExpSumBlaschkeProduct

end
