import Mathlib
import Cvs.StepA.OneZeroParitySectors
import Cvs.WeilForm.OddPoleTermBound

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The averaged-window frame bound for exponentials at complex points

For points `z_j ∈ ℂ` and weights `m_j ≥ 0`, the centred transforms of a real continuous `g` satisfy
`Σ m_j ‖ctr L g z_j‖² ≤ Λ ∫_{−L/2}^{L/2} g²` whenever every row sum `Σ_k m_k ‖K_L(z_j − z̄_k)‖` is at most `Λ`,
where `K_L(w) = ctr 1 1 w · ctr (L + 1) 1 w` is the transform of the trapezoid
`1_{[−(L+1)/2, (L+1)/2]} ∗ 1_{[−1/2, 1/2]}` and `‖K_L(w)‖ ≤ 4(L + 2) e^{|Im w|(L + 2)/2}/(1 + (Re w)²)`.
-/

noncomputable section

open Real MeasureTheory
open scoped ComplexConjugate

namespace Cvs.Zeta.ExplicitFormula.AveragedWindowFrameBound
open Cvs.ZeroCounting

open Cvs.StepA.OneZeroParitySectors (ctr)

/-! ### The trapezoid kernel -/

/-- The transform of the trapezoid `1_{[−(L+1)/2, (L+1)/2]} ∗ 1_{[−1/2, 1/2]}` at `w`. -/
def frameKernel (L : ℝ) (w : ℂ) : ℂ := ctr 1 (fun _ => 1) w * ctr (L + 1) (fun _ => 1) w

/-- `‖e^{−itw}‖ = e^{t Im w}`. -/
theorem norm_exp_neg_mul_I (t : ℝ) (w : ℂ) :
    ‖Complex.exp (-((t : ℂ) * w) * Complex.I)‖ = Real.exp (t * w.im) := by
  rw [Complex.norm_exp]
  congr 1
  simp

/-- `‖ctr c 1 w‖ ≤ c e^{|Im w| c/2}` for `c ≥ 0`. -/
theorem norm_ctr_one_le {c : ℝ} (hc : 0 ≤ c) (w : ℂ) :
    ‖ctr c (fun _ => 1) w‖ ≤ c * Real.exp (|w.im| * (c / 2)) := by
  unfold ctr
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -(c / 2)) (b := c / 2) (C := Real.exp (|w.im| * (c / 2)))
    (f := fun t : ℝ => Complex.exp (-((t : ℂ) * w) * Complex.I) * (((fun _ => (1 : ℝ)) t : ℝ) : ℂ))
    (fun t ht => by
      rw [Set.uIoc_of_le (by linarith)] at ht
      simp only [Complex.ofReal_one, mul_one]
      rw [norm_exp_neg_mul_I]
      refine Real.exp_le_exp.2 ?_
      have : |t| ≤ c / 2 := abs_le.2 ⟨ht.1.le, ht.2⟩
      calc t * w.im ≤ |t * w.im| := le_abs_self _
        _ = |t| * |w.im| := abs_mul _ _
        _ ≤ (c / 2) * |w.im| := mul_le_mul_of_nonneg_right this (abs_nonneg _)
        _ = |w.im| * (c / 2) := by ring)
  refine h.trans (le_of_eq ?_)
  rw [show c / 2 - -(c / 2) = c by ring, abs_of_nonneg hc]; ring

/-- `‖w‖ ‖ctr c 1 w‖ ≤ 2 e^{|Im w| c/2}` for `c ≥ 0` and `w ≠ 0`. -/
theorem norm_mul_norm_ctr_one_le {c : ℝ} (hc : 0 ≤ c) {w : ℂ} (hw : w ≠ 0) :
    ‖w‖ * ‖ctr c (fun _ => 1) w‖ ≤ 2 * Real.exp (|w.im| * (c / 2)) := by
  have hw' : -w * Complex.I ≠ 0 := mul_ne_zero (neg_ne_zero.2 hw) Complex.I_ne_zero
  have hform : ctr c (fun _ => 1) w
      = (Complex.exp ((-w * Complex.I) * ((c / 2 : ℝ) : ℂ))
          - Complex.exp ((-w * Complex.I) * ((-(c / 2) : ℝ) : ℂ))) / (-w * Complex.I) := by
    rw [← integral_exp_mul_complex hw']
    unfold ctr
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [Complex.ofReal_one, mul_one]
    congr 1; ring
  have hn : ‖-w * Complex.I‖ = ‖w‖ := by simp
  have hb : ∀ t : ℝ, |t| ≤ c / 2 →
      ‖Complex.exp ((-w * Complex.I) * (t : ℂ))‖ ≤ Real.exp (|w.im| * (c / 2)) := by
    intro t ht
    rw [show (-w * Complex.I) * (t : ℂ) = -((t : ℂ) * w) * Complex.I by ring, norm_exp_neg_mul_I]
    refine Real.exp_le_exp.2 ?_
    calc t * w.im ≤ |t * w.im| := le_abs_self _
      _ = |t| * |w.im| := abs_mul _ _
      _ ≤ (c / 2) * |w.im| := mul_le_mul_of_nonneg_right ht (abs_nonneg _)
      _ = |w.im| * (c / 2) := by ring
  have h1 := hb (c / 2) (by rw [abs_of_nonneg (by linarith)])
  have h2 := hb (-(c / 2)) (by rw [abs_neg, abs_of_nonneg (by linarith)])
  have hwpos : 0 < ‖w‖ := norm_pos_iff.2 hw
  rw [hform, norm_div, hn, mul_div_cancel₀ _ hwpos.ne']
  calc _ ≤ _ := norm_sub_le _ _
    _ ≤ _ := add_le_add h1 h2
    _ = _ := by ring

/-- **The trapezoid kernel bound**: for `L ≥ 0`, `‖K_L(w)‖ ≤ 4(L + 2) e^{|Im w|(L + 2)/2}/(1 + (Re w)²)`. -/
theorem norm_frameKernel_le {L : ℝ} (hL : 0 ≤ L) (w : ℂ) :
    ‖frameKernel L w‖ ≤ 4 * (L + 2) * Real.exp (|w.im| * ((L + 2) / 2)) / (1 + w.re ^ 2) := by
  set E := Real.exp (|w.im| * ((L + 2) / 2)) with hE
  have hEpos : 0 < E := Real.exp_pos _
  have hsplit : Real.exp (|w.im| * (1 / 2)) * Real.exp (|w.im| * ((L + 1) / 2)) = E := by
    rw [← Real.exp_add]; congr 1; ring
  have h1 := norm_ctr_one_le zero_le_one w
  have h2 := norm_ctr_one_le (by linarith : (0 : ℝ) ≤ L + 1) w
  have htriv : ‖frameKernel L w‖ ≤ (L + 1) * E := by
    unfold frameKernel
    rw [norm_mul, ← hsplit]
    calc _ ≤ (1 * Real.exp (|w.im| * (1 / 2))) * ((L + 1) * Real.exp (|w.im| * ((L + 1) / 2))) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hpos : 0 < 1 + w.re ^ 2 := by positivity
  rw [le_div_iff₀ hpos]
  rcases le_or_gt (w.re ^ 2) 1 with hr | hr
  · have hK0 := norm_nonneg (frameKernel L w)
    nlinarith
  · have hw : w ≠ 0 := by
      intro h0; rw [h0, Complex.zero_re] at hr; norm_num at hr
    have hdec : ‖w‖ ^ 2 * ‖frameKernel L w‖ ≤ 4 * E := by
      unfold frameKernel
      rw [norm_mul, ← hsplit]
      have a1 := norm_mul_norm_ctr_one_le zero_le_one hw
      have a2 := norm_mul_norm_ctr_one_le (by linarith : (0 : ℝ) ≤ L + 1) hw
      calc ‖w‖ ^ 2 * (‖ctr 1 (fun _ => 1) w‖ * ‖ctr (L + 1) (fun _ => 1) w‖)
          = (‖w‖ * ‖ctr 1 (fun _ => 1) w‖) * (‖w‖ * ‖ctr (L + 1) (fun _ => 1) w‖) := by ring
        _ ≤ (2 * Real.exp (|w.im| * (1 / 2))) * (2 * Real.exp (|w.im| * ((L + 1) / 2))) :=
          mul_le_mul a1 a2 (by positivity) (by positivity)
        _ = _ := by ring
    have hre : w.re ^ 2 ≤ ‖w‖ ^ 2 := by
      have := Complex.abs_re_le_norm w
      nlinarith [abs_nonneg w.re, sq_abs w.re]
    have hK0 := norm_nonneg (frameKernel L w)
    have : w.re ^ 2 * ‖frameKernel L w‖ ≤ 4 * E :=
      (mul_le_mul_of_nonneg_right hre hK0).trans hdec
    nlinarith

/-- `K_L(−w̄) = conj K_L(w)` factorwise: `ctr c 1 (−w̄) = conj (ctr c 1 w)` for `c ≥ 0`. -/
theorem ctr_one_neg_conj {c : ℝ} (hc : 0 ≤ c) (w : ℂ) :
    ctr c (fun _ => 1) (-conj w) = conj (ctr c (fun _ => 1) w) := by
  unfold ctr
  rw [intervalIntegral.integral_of_le (by linarith), intervalIntegral.integral_of_le (by linarith),
    ← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [Complex.ofReal_one, mul_one, map_mul, ← Complex.exp_conj, map_neg, Complex.conj_ofReal,
    Complex.conj_I]
  congr 1; ring

/-- **The kernel is symmetric in norm**: `‖K_L(−w̄)‖ = ‖K_L(w)‖` for `L ≥ 0`. -/
theorem norm_frameKernel_neg_conj {L : ℝ} (hL : 0 ≤ L) (w : ℂ) :
    ‖frameKernel L (-conj w)‖ = ‖frameKernel L w‖ := by
  unfold frameKernel
  rw [ctr_one_neg_conj zero_le_one, ctr_one_neg_conj (by linarith), ← map_mul, Complex.norm_conj]

/-! ### The averaged window -/

/-- **The averaged window dominates the window**: for `L ≥ 0` and `φ ≥ 0` continuous,
`∫_{−L/2}^{L/2} φ ≤ ∫_{−1/2}^{1/2} ∫_{−(L+1)/2}^{(L+1)/2} φ(t + u) dt du`. -/
theorem integral_le_avg {L : ℝ} (hL : 0 ≤ L) {φ : ℝ → ℝ} (hφ : Continuous φ) (h0 : ∀ t, 0 ≤ φ t) :
    ∫ t in -(L / 2)..L / 2, φ t
      ≤ ∫ u in -(1 / 2 : ℝ)..1 / 2, ∫ t in -((L + 1) / 2)..(L + 1) / 2, φ (t + u) := by
  have hcont : Continuous fun u => ∫ t in -((L + 1) / 2)..(L + 1) / 2, φ (t + u) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun u t => φ (t + u)) (hφ.comp (continuous_snd.add continuous_fst)) _ _
  calc ∫ t in -(L / 2)..L / 2, φ t
      = ∫ _ in -(1 / 2 : ℝ)..1 / 2, ∫ t in -(L / 2)..L / 2, φ t := by
        rw [intervalIntegral.integral_const]; norm_num
    _ ≤ _ := by
        refine intervalIntegral.integral_mono_on (by norm_num) (continuous_const.intervalIntegrable _ _)
          (hcont.intervalIntegrable _ _) fun u hu => ?_
        rw [intervalIntegral.integral_comp_add_right (fun t => φ t) u]
        exact intervalIntegral.integral_mono_interval (by linarith [hu.2]) (by linarith)
          (by linarith [hu.1]) (Filter.Eventually.of_forall fun t => h0 t) (hφ.intervalIntegrable _ _)

/-- A double finite sum of continuous functions integrates termwise. -/
theorem integral_sum_sum {ι : Type*} (s : Finset ι) {f : ι → ι → ℝ → ℂ} (hf : ∀ j k, Continuous (f j k))
    (a b : ℝ) :
    ∫ t in a..b, ∑ j ∈ s, ∑ k ∈ s, f j k t = ∑ j ∈ s, ∑ k ∈ s, ∫ t in a..b, f j k t := by
  rw [intervalIntegral.integral_finsetSum fun j _ =>
    (continuous_finsetSum _ fun k _ => hf j k).intervalIntegrable _ _]
  exact Finset.sum_congr rfl fun j _ =>
    intervalIntegral.integral_finsetSum fun k _ => (hf j k).intervalIntegrable _ _

/-- One product of exponentials: `e^{−iτz_j} conj(e^{−iτz_k}) = e^{−itw} e^{−iuw}` at `τ = t + u`,
`w = z_j − z̄_k`. -/
theorem exp_mul_conj_exp (t u : ℝ) (zj zk : ℂ) :
    Complex.exp (-(((t + u : ℝ) : ℂ) * zj) * Complex.I)
        * conj (Complex.exp (-(((t + u : ℝ) : ℂ) * zk) * Complex.I))
      = Complex.exp (-((t : ℂ) * (zj - conj zk)) * Complex.I)
        * Complex.exp (-((u : ℂ) * (zj - conj zk)) * Complex.I) := by
  rw [← Complex.exp_conj, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  simp only [map_mul, map_neg, map_add, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_add]
  ring

/-- **The averaged energy of an exponential sum**:
`∫_{−1/2}^{1/2} ∫_{−(L+1)/2}^{(L+1)/2} ‖Σ_j c_j e^{−i(t+u)z_j}‖² = Σ_{j,k} c_j c̄_k K_L(z_j − z̄_k)`. -/
theorem avg_norm_sq_sum_eq {ι : Type*} (s : Finset ι) (c z : ι → ℂ) (L : ℝ) :
    ((∫ u in -(1 / 2 : ℝ)..1 / 2, ∫ t in -((L + 1) / 2)..(L + 1) / 2,
        ‖∑ j ∈ s, c j * Complex.exp (-(((t + u : ℝ) : ℂ) * z j) * Complex.I)‖ ^ 2 : ℝ) : ℂ)
      = ∑ j ∈ s, ∑ k ∈ s, c j * conj (c k) * frameKernel L (z j - conj (z k)) := by
  have hpt : ∀ t u : ℝ,
      (((‖∑ j ∈ s, c j * Complex.exp (-(((t + u : ℝ) : ℂ) * z j) * Complex.I)‖ ^ 2 : ℝ)) : ℂ)
        = ∑ j ∈ s, ∑ k ∈ s, (c j * conj (c k)
            * Complex.exp (-((u : ℂ) * (z j - conj (z k))) * Complex.I))
            * Complex.exp (-((t : ℂ) * (z j - conj (z k))) * Complex.I) := by
    intro t u
    rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul]
    linear_combination (c j * conj (c k)) * exp_mul_conj_exp t u (z j) (z k)
  rw [← intervalIntegral.integral_ofReal]
  simp_rw [← intervalIntegral.integral_ofReal, hpt]
  have hin : ∀ u : ℝ, ∫ t in -((L + 1) / 2)..(L + 1) / 2, ∑ j ∈ s, ∑ k ∈ s, (c j * conj (c k)
            * Complex.exp (-((u : ℂ) * (z j - conj (z k))) * Complex.I))
            * Complex.exp (-((t : ℂ) * (z j - conj (z k))) * Complex.I)
        = ∑ j ∈ s, ∑ k ∈ s, (c j * conj (c k)
            * ctr (L + 1) (fun _ => 1) (z j - conj (z k)))
            * Complex.exp (-((u : ℂ) * (z j - conj (z k))) * Complex.I) := by
    intro u
    rw [integral_sum_sum s (fun j k => by fun_prop)]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    rw [intervalIntegral.integral_const_mul]
    unfold ctr
    simp only [Complex.ofReal_one, mul_one]
    ring
  simp_rw [hin]
  rw [integral_sum_sum s (fun j k => by fun_prop)]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [intervalIntegral.integral_const_mul]
  unfold frameKernel ctr
  simp only [Complex.ofReal_one, mul_one]
  norm_num
  ring

/-! ### The frame bound -/

/-- **The weighted Schur test**: for `m ≥ 0` and a nonnegative symmetric `κ` whose weighted row sums
`Σ_k m_k κ_jk` are at most `Λ`, `Σ_{j,k} (m_j β_j)(m_k β_k) κ_jk ≤ Λ Σ_j m_j β_j²`. -/
theorem sum_sum_mul_le_schur {ι : Type*} (s : Finset ι) {m : ι → ℝ} (hm : ∀ j ∈ s, 0 ≤ m j) (β : ι → ℝ)
    {κ : ι → ι → ℝ} (hκ0 : ∀ j ∈ s, ∀ k ∈ s, 0 ≤ κ j k) (hsym : ∀ j ∈ s, ∀ k ∈ s, κ j k = κ k j)
    {Λ : ℝ} (hΛ : ∀ j ∈ s, ∑ k ∈ s, m k * κ j k ≤ Λ) :
    ∑ j ∈ s, ∑ k ∈ s, (m j * β j) * (m k * β k) * κ j k ≤ Λ * ∑ j ∈ s, m j * β j ^ 2 := by
  calc ∑ j ∈ s, ∑ k ∈ s, (m j * β j) * (m k * β k) * κ j k
      ≤ ∑ j ∈ s, ∑ k ∈ s, (m j * β j ^ 2 * (m k * κ j k) / 2 + m k * β k ^ 2 * (m j * κ k j) / 2) := by
        refine Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun k hk => ?_
        rw [← hsym j hj k hk]
        have h0 := mul_nonneg (mul_nonneg (mul_nonneg (hm j hj) (hm k hk)) (hκ0 j hj k hk))
          (sq_nonneg (β j - β k))
        nlinarith
    _ = ∑ j ∈ s, m j * β j ^ 2 / 2 * ∑ k ∈ s, m k * κ j k
          + ∑ k ∈ s, m k * β k ^ 2 / 2 * ∑ j ∈ s, m j * κ k j := by
        simp_rw [Finset.sum_add_distrib]
        congr 1
        · refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring
        · rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
    _ ≤ ∑ j ∈ s, m j * β j ^ 2 / 2 * Λ + ∑ k ∈ s, m k * β k ^ 2 / 2 * Λ := by
        gcongr with j hj k hk
        · exact div_nonneg (mul_nonneg (hm j hj) (sq_nonneg _)) zero_le_two
        · exact hΛ j hj
        · exact div_nonneg (mul_nonneg (hm k hk) (sq_nonneg _)) zero_le_two
        · exact hΛ k hk
    _ = Λ * ∑ j ∈ s, m j * β j ^ 2 := by
        rw [← Finset.sum_mul, ← Finset.sum_div]
        ring

/-- **The averaged-window frame bound**: for `L ≥ 0`, `g` real continuous, weights `m ≥ 0` and points `z_j`, if
every weighted row sum `Σ_k m_k ‖K_L(z_j − z̄_k)‖` is at most `Λ ≥ 0`, then
`Σ_j m_j ‖ctr L g z_j‖² ≤ Λ ∫_{−L/2}^{L/2} g²`. -/
theorem sum_mul_norm_ctr_sq_le {ι : Type*} (s : Finset ι) {m : ι → ℝ} (hm : ∀ j ∈ s, 0 ≤ m j) (z : ι → ℂ)
    {L : ℝ} (hL : 0 ≤ L) {g : ℝ → ℝ} (hg : Continuous g) {Λ : ℝ} (hΛ0 : 0 ≤ Λ)
    (hΛ : ∀ j ∈ s, ∑ k ∈ s, m k * ‖frameKernel L (z j - conj (z k))‖ ≤ Λ) :
    ∑ j ∈ s, m j * ‖ctr L g (z j)‖ ^ 2 ≤ Λ * ∫ t in -(L / 2)..L / 2, g t ^ 2 := by
  set S := ∑ j ∈ s, m j * ‖ctr L g (z j)‖ ^ 2 with hSdef
  set c : ι → ℂ := fun j => (m j : ℂ) * conj (ctr L g (z j)) with hc
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun j hj => mul_nonneg (hm j hj) (sq_nonneg _)
  have hhc : Continuous fun τ : ℝ => ∑ j ∈ s, c j * Complex.exp (-((τ : ℂ) * z j) * Complex.I) := by
    fun_prop
  have hab : -(L / 2) ≤ L / 2 := by linarith
  -- `S` is the pairing of `g` with `h = Σ c_j e_j`
  have hSint : (S : ℂ) = ∫ t in -(L / 2)..L / 2,
      (∑ j ∈ s, c j * Complex.exp (-((t : ℂ) * z j) * Complex.I)) * ((g t : ℝ) : ℂ) := by
    simp_rw [Finset.sum_mul]
    rw [intervalIntegral.integral_finsetSum fun j _ => by
      exact (Continuous.intervalIntegrable (by fun_prop) _ _)]
    rw [hSdef]; push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    simp_rw [mul_assoc]
    rw [intervalIntegral.integral_const_mul, hc]
    show _ = (m j : ℂ) * conj (ctr L g (z j)) * ctr L g (z j)
    rw [mul_assoc, Complex.conj_mul']
  have hSle : S ≤ ∫ t in -(L / 2)..L / 2,
      ‖∑ j ∈ s, c j * Complex.exp (-((t : ℂ) * z j) * Complex.I)‖ * |g t| := by
    have h1 : S = ‖(S : ℂ)‖ := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hS0]
    rw [h1, hSint]
    refine (intervalIntegral.norm_integral_le_integral_norm hab).trans_eq ?_
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  -- Cauchy–Schwarz on the window
  set Ih := ∫ t in -(L / 2)..L / 2,
    ‖∑ j ∈ s, c j * Complex.exp (-((t : ℂ) * z j) * Complex.I)‖ ^ 2 with hIh
  set Ig := ∫ t in -(L / 2)..L / 2, g t ^ 2 with hIg
  have hIg0 : 0 ≤ Ig := intervalIntegral.integral_nonneg hab fun t _ => sq_nonneg _
  have hCS : (∫ t in -(L / 2)..L / 2,
      ‖∑ j ∈ s, c j * Complex.exp (-((t : ℂ) * z j) * Complex.I)‖ * |g t|) ^ 2 ≤ Ih * Ig := by
    have h := Cvs.WeilForm.OddPoleTermBound.sq_integral_mul_le hab
      (f := fun t => ‖∑ j ∈ s, c j * Complex.exp (-((t : ℂ) * z j) * Complex.I)‖)
      (w := fun t => |g t|) ((hhc.norm.pow 2).intervalIntegrable _ _)
      ((hg.abs.pow 2).intervalIntegrable _ _) ((hhc.norm.mul hg.abs).intervalIntegrable _ _)
    simp only [sq_abs] at h
    exact h
  -- the window energy against the averaged one, and its expansion
  have havg := integral_le_avg hL (φ := fun t =>
      ‖∑ j ∈ s, c j * Complex.exp (-((t : ℂ) * z j) * Complex.I)‖ ^ 2) (hhc.norm.pow 2)
    (fun t => sq_nonneg _)
  set R := ∫ u in -(1 / 2 : ℝ)..1 / 2, ∫ t in -((L + 1) / 2)..(L + 1) / 2,
    ‖∑ j ∈ s, c j * Complex.exp (-(((t + u : ℝ) : ℂ) * z j) * Complex.I)‖ ^ 2 with hR
  have hIhR : Ih ≤ R := havg
  have hRQ : R ≤ ∑ j ∈ s, ∑ k ∈ s, (m j * ‖ctr L g (z j)‖) * (m k * ‖ctr L g (z k)‖)
      * ‖frameKernel L (z j - conj (z k))‖ := by
    have hexp := avg_norm_sq_sum_eq s c z L
    rw [← hR] at hexp
    calc R ≤ |R| := le_abs_self R
      _ = ‖(R : ℂ)‖ := by rw [Complex.norm_real, Real.norm_eq_abs]
      _ = _ := by rw [hexp]
      _ ≤ ∑ j ∈ s, ‖∑ k ∈ s, c j * conj (c k) * frameKernel L (z j - conj (z k))‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ s, ∑ k ∈ s, ‖c j * conj (c k) * frameKernel L (z j - conj (z k))‖ :=
          Finset.sum_le_sum fun j _ => norm_sum_le _ _
      _ = _ := by
          refine Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun k hk => ?_
          rw [norm_mul, norm_mul, Complex.norm_conj, hc]
          simp only [norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (hm j hj), abs_of_nonneg (hm k hk)]
  have hQ : ∑ j ∈ s, ∑ k ∈ s, (m j * ‖ctr L g (z j)‖) * (m k * ‖ctr L g (z k)‖)
      * ‖frameKernel L (z j - conj (z k))‖ ≤ Λ * S :=
    sum_sum_mul_le_schur s hm (fun j => ‖ctr L g (z j)‖) (fun _ _ _ _ => norm_nonneg _)
      (fun j _ k _ => by
        rw [show z k - conj (z j) = -conj (z j - conj (z k)) by simp,
          norm_frameKernel_neg_conj hL]) hΛ
  have hS2 : S ^ 2 ≤ (Λ * Ig) * S := by
    calc S ^ 2 ≤ (∫ t in -(L / 2)..L / 2,
          ‖∑ j ∈ s, c j * Complex.exp (-((t : ℂ) * z j) * Complex.I)‖ * |g t|) ^ 2 :=
          pow_le_pow_left₀ hS0 hSle 2
      _ ≤ Ih * Ig := hCS
      _ ≤ (Λ * S) * Ig := mul_le_mul_of_nonneg_right ((hIhR.trans hRQ).trans hQ) hIg0
      _ = (Λ * Ig) * S := by ring
  rcases eq_or_lt_of_le hS0 with h0 | hpos
  · rw [← h0]; exact mul_nonneg hΛ0 hIg0
  · nlinarith

end Cvs.Zeta.ExplicitFormula.AveragedWindowFrameBound
