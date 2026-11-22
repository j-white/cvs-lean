import Mathlib
import Cvs.Upstream.ExpSumBlaschkeProduct
import Cvs.Upstream.ExpSumTwoEndedError
import Cvs.Zeta.RectArgument
import Cvs.Zeta.RectCauchy
import Cvs.Zeta.RectWinding

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Contour interpolation by exponential sums, with the two-ended correction

For points strictly inside the rectangle `[s₁, s₂] × [−Y, Y]`, `0 < s₁`, with `|B| ≥ m` on its boundary,
the rectangle Cauchy formula and Cvs.Upstream.ExpSumBlaschkeProduct give `|Σ_k ā_k g(p_k)| ≤ K_c M_g (Re G(a))^{1/2}` for `g` holomorphic
near the rectangle with `|g| ≤ M_g` on the boundary, `K_c = (2(s₂ − s₁) + 4Y)/(2πm(2s₁)^{1/2})`. When
`q = 2K_c e^{−s₁T}/(2s₁)^{1/2} < 1`, the system `L_a + err = f + c/(· − c₀)` on the points has a solution.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology Finset
open scoped Interval ComplexConjugate
open Cvs.Upstream.ExpSumBlaschkeProduct (lap gram blaschke res qfun)
open Cvs.Upstream.ExpSumTwoEndedError (err shift)
open Cvs.Zeta (rectBoundaryIntegral closedRect)

namespace Cvs.Upstream.ExpSumContourInterpolation

set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The rectangle -/

/-- A boundary point of the closed rectangle with corners `z`, `w`. -/
def OnBd (z w u : ℂ) : Prop :=
  u ∈ closedRect z w ∧ (u.re = z.re ∨ u.re = w.re ∨ u.im = z.im ∨ u.im = w.im)

/-- The boundary integral of a finite sum is the sum of the boundary integrals. -/
theorem rectBoundaryIntegral_sum {κ : Type*} (s : Finset κ) (g : κ → ℂ → ℂ) (z w : ℂ)
    (hg : ∀ k ∈ s, Cvs.Zeta.SidesIntegrable (g k) z w) :
    rectBoundaryIntegral (fun u => ∑ k ∈ s, g k u) z w = ∑ k ∈ s, rectBoundaryIntegral (g k) z w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [rectBoundaryIntegral]
  | insert k s hk ih =>
    have hs : ∀ k ∈ s, Cvs.Zeta.SidesIntegrable (g k) z w := fun j hj => hg j (Finset.mem_insert_of_mem hj)
    have hS : Cvs.Zeta.SidesIntegrable (fun u => ∑ j ∈ s, g j u) z w := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · have := IntervalIntegrable.sum s fun j hj => (hs j hj).1
        rwa [Finset.sum_fn] at this
      · have := IntervalIntegrable.sum s fun j hj => (hs j hj).2.1
        rwa [Finset.sum_fn] at this
      · have := IntervalIntegrable.sum s fun j hj => (hs j hj).2.2.1
        rwa [Finset.sum_fn] at this
      · have := IntervalIntegrable.sum s fun j hj => (hs j hj).2.2.2
        rwa [Finset.sum_fn] at this
    simp only [Finset.sum_insert hk]
    rw [Cvs.Zeta.rectBoundaryIntegral_add (hg k (Finset.mem_insert_self k s)) hS, ih hs]

/-- **The boundary integral bound**: `|∮ g| ≤ (2(Re w − Re z) + 2(Im w − Im z))·M` when `|g| ≤ M` on the boundary. -/
theorem norm_rectBoundaryIntegral_le {g : ℂ → ℂ} {z w : ℂ} (hre : z.re ≤ w.re) (him : z.im ≤ w.im) {M : ℝ}
    (hM : ∀ u, OnBd z w u → ‖g u‖ ≤ M) :
    ‖rectBoundaryIntegral g z w‖ ≤ (2 * (w.re - z.re) + 2 * (w.im - z.im)) * M := by
  have hb : ∀ x ∈ Ι z.re w.re, ‖g ((x : ℂ) + z.im * I)‖ ≤ M := fun x hx => hM _ ⟨Cvs.Zeta.bottom_mem
    (Set.uIoc_subset_uIcc hx), Or.inr (Or.inr (Or.inl (by simp)))⟩
  have ht : ∀ x ∈ Ι z.re w.re, ‖g ((x : ℂ) + w.im * I)‖ ≤ M := fun x hx => hM _ ⟨Cvs.Zeta.top_mem
    (Set.uIoc_subset_uIcc hx), Or.inr (Or.inr (Or.inr (by simp)))⟩
  have hr : ∀ y ∈ Ι z.im w.im, ‖g ((w.re : ℂ) + y * I)‖ ≤ M := fun y hy => hM _ ⟨Cvs.Zeta.right_mem
    (Set.uIoc_subset_uIcc hy), Or.inr (Or.inl (by simp))⟩
  have hl : ∀ y ∈ Ι z.im w.im, ‖g ((z.re : ℂ) + y * I)‖ ≤ M := fun y hy => hM _ ⟨Cvs.Zeta.left_mem
    (Set.uIoc_subset_uIcc hy), Or.inl (by simp)⟩
  have e1 := intervalIntegral.norm_integral_le_of_norm_le_const hb
  have e2 := intervalIntegral.norm_integral_le_of_norm_le_const ht
  have e3 := intervalIntegral.norm_integral_le_of_norm_le_const hr
  have e4 := intervalIntegral.norm_integral_le_of_norm_le_const hl
  rw [abs_of_nonneg (sub_nonneg.2 hre)] at e1 e2
  rw [abs_of_nonneg (sub_nonneg.2 him)] at e3 e4
  unfold rectBoundaryIntegral
  set A := ∫ x : ℝ in z.re..w.re, g ((x : ℂ) + z.im * I)
  set B := ∫ x : ℝ in z.re..w.re, g ((x : ℂ) + w.im * I)
  set C := ∫ y : ℝ in z.im..w.im, g ((w.re : ℂ) + y * I)
  set D := ∫ y : ℝ in z.im..w.im, g ((z.re : ℂ) + y * I)
  have h1 := norm_sub_le (A - B + I * C) (I * D)
  have h2 := norm_add_le (A - B) (I * C)
  have h3 := norm_sub_le A B
  have hC : ‖I * C‖ = ‖C‖ := by rw [norm_mul, Complex.norm_I, one_mul]
  have hD : ‖I * D‖ = ‖D‖ := by rw [norm_mul, Complex.norm_I, one_mul]
  calc ‖A - B + I * C - I * D‖
        ≤ M * (w.re - z.re) + M * (w.re - z.re) + M * (w.im - z.im) + M * (w.im - z.im) := by
          linarith
    _ = (2 * (w.re - z.re) + 2 * (w.im - z.im)) * M := by ring

/-- Points strictly inside the rectangle with corners `z`, `w`. -/
def Inside (z w ρ : ℂ) : Prop := z.re < ρ.re ∧ ρ.re < w.re ∧ z.im < ρ.im ∧ ρ.im < w.im

/-- A boundary point is not strictly inside. -/
theorem ne_of_onBd {z w u ρ : ℂ} (hu : OnBd z w u) (hρ : Inside z w ρ) : u ≠ ρ := by
  rintro rfl
  obtain ⟨-, h | h | h | h⟩ := hu <;> obtain ⟨h1, h2, h3, h4⟩ := hρ <;> linarith

/-- The four sides of the rectangle lie on its boundary. -/
theorem onBd_bottom {z w : ℂ} {x : ℝ} (hx : x ∈ uIcc z.re w.re) : OnBd z w ((x : ℂ) + z.im * I) :=
  ⟨Cvs.Zeta.bottom_mem hx, Or.inr (Or.inr (Or.inl (by simp)))⟩

theorem onBd_top {z w : ℂ} {x : ℝ} (hx : x ∈ uIcc z.re w.re) : OnBd z w ((x : ℂ) + w.im * I) :=
  ⟨Cvs.Zeta.top_mem hx, Or.inr (Or.inr (Or.inr (by simp)))⟩

theorem onBd_right {z w : ℂ} {y : ℝ} (hy : y ∈ uIcc z.im w.im) : OnBd z w ((w.re : ℂ) + y * I) :=
  ⟨Cvs.Zeta.right_mem hy, Or.inr (Or.inl (by simp))⟩

theorem onBd_left {z w : ℂ} {y : ℝ} (hy : y ∈ uIcc z.im w.im) : OnBd z w ((z.re : ℂ) + y * I) :=
  ⟨Cvs.Zeta.left_mem hy, Or.inl (by simp)⟩

/-- A function continuous on the boundary is integrable along the four sides. -/
theorem sidesIntegrable_of_continuousOn {f : ℂ → ℂ} {z w : ℂ} (hf : ContinuousOn f {u | OnBd z w u}) :
    Cvs.Zeta.SidesIntegrable f z w := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> refine ContinuousOn.intervalIntegrable ?_
  · exact hf.comp (by fun_prop) fun x hx => onBd_bottom hx
  · exact hf.comp (by fun_prop) fun x hx => onBd_top hx
  · exact hf.comp (by fun_prop) fun y hy => onBd_right hy
  · exact hf.comp (by fun_prop) fun y hy => onBd_left hy

/-- **The Cauchy sum on the rectangle**: `∮ g R_a = 2πi Σ_k ā_k g(p_k)` for `g` holomorphic near the rectangle. -/
theorem rectBoundaryIntegral_mul_res {p a : ι → ℂ} {z w : ℂ} (hpin : ∀ k, Inside z w (p k)) {U : Set ℂ}
    (hUo : IsOpen U) (hU : closedRect z w ⊆ U) {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g U) :
    rectBoundaryIntegral (fun u => g u * res p a u) z w = 2 * Real.pi * I * ∑ k, conj (a k) * g (p k) := by
  have e : (fun u => g u * res p a u) = fun u => ∑ k, conj (a k) * (g u / (u - p k)) := by
    funext u
    unfold res
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hgc : ContinuousOn g (closedRect z w) := hg.continuousOn.mono hU
  have hsi : ∀ k ∈ (univ : Finset ι), Cvs.Zeta.SidesIntegrable (fun u => conj (a k) * (g u / (u - p k))) z w := by
    intro k _
    refine sidesIntegrable_of_continuousOn ?_
    have hmono : {u | OnBd z w u} ⊆ closedRect z w := fun u (hu : OnBd z w u) => hu.1
    have hsub : ContinuousOn (fun u : ℂ => u - p k) {u | OnBd z w u} := by fun_prop
    refine continuousOn_const.mul ((hgc.mono hmono).div₀ hsub fun u (hu : OnBd z w u) => ?_)
    exact sub_ne_zero.2 (ne_of_onBd hu (hpin k))
  rw [e, rectBoundaryIntegral_sum _ _ z w hsi, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  obtain ⟨h1, h2, h3, h4⟩ := hpin k
  rw [Cvs.Zeta.rectBoundaryIntegral_const_mul, Cvs.Zeta.rectBoundaryIntegral_div_sub_eq h1 h2 h3 h4 hUo hU hg]
  ring

/-- `|R_a(u)| ≤ (Re G(a)/(2 Re u))^{1/2}/|B(u)|` off the points, `Re u > 0`. -/
theorem norm_res_le {p : ι → ℂ} {ε : ℝ} (hε0 : 0 < ε) (hε : ∀ i, ε ≤ (p i).re) (a : ι → ℂ) {u : ℂ}
    (hu : 0 < u.re) (hup : ∀ i, u ≠ p i) :
    ‖res p a u‖ ≤ √((gram p a).re / (2 * u.re)) / ‖blaschke p u‖ := by
  have hp : ∀ i, 0 < (p i).re := fun i => hε0.trans_le (hε i)
  have hB : 0 < ‖blaschke p u‖ := norm_pos_iff.2 (Cvs.Upstream.ExpSumBlaschkeProduct.blaschke_ne_zero hp hu.le hup)
  have hq := Cvs.Upstream.ExpSumBlaschkeProduct.norm_sq_qfun_le hε0 hε a hu
  rw [Cvs.Upstream.ExpSumBlaschkeProduct.qfun_eq hp a hu.le hup, norm_mul] at hq
  rw [le_div_iff₀ hB, mul_comm]
  exact Real.le_sqrt_of_sq_le hq

/-- **The contour interpolation bound**: `|Σ_k ā_k g(p_k)| ≤ K_c M (Re G(a))^{1/2}` with
`K_c = (2(Re w − Re z) + 2(Im w − Im z))/(2πm(2 Re z)^{1/2})`. -/
theorem norm_sum_conj_mul_le {p a : ι → ℂ} {z w : ℂ} (hz : 0 < z.re) (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (hpin : ∀ k, Inside z w (p k)) {m : ℝ} (hm0 : 0 < m) (hm : ∀ u, OnBd z w u → m ≤ ‖blaschke p u‖)
    {U : Set ℂ} (hUo : IsOpen U) (hU : closedRect z w ⊆ U) {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g U)
    {M : ℝ} (hgM : ∀ u, OnBd z w u → ‖g u‖ ≤ M) :
    ‖∑ k, conj (a k) * g (p k)‖
      ≤ (2 * (w.re - z.re) + 2 * (w.im - z.im)) / (2 * Real.pi * m * √(2 * z.re)) * M
        * √((gram p a).re) := by
  have hε : ∀ i, z.re ≤ (p i).re := fun i => (hpin i).1.le
  have hG := Cvs.Upstream.ExpSumBlaschkeProduct.gram_re_nonneg hz hε a
  have hpt : ∀ u, OnBd z w u → ‖g u * res p a u‖ ≤ M * (√((gram p a).re) / √(2 * z.re) / m) := by
    intro u hu
    have hure : z.re ≤ u.re := by
      have := hu.1.1
      rw [Set.mem_preimage, Set.uIcc_of_le hre] at this
      exact this.1
    have hu0 : 0 < u.re := hz.trans_le hure
    have hup : ∀ i, u ≠ p i := fun i => ne_of_onBd hu (hpin i)
    have hr := norm_res_le hz hε a hu0 hup
    have hBm := hm u hu
    have hgu := hgM u hu
    have hM0 : 0 ≤ M := (norm_nonneg _).trans hgu
    rw [norm_mul]
    refine mul_le_mul hgu ?_ (norm_nonneg _) hM0
    refine hr.trans ?_
    rw [Real.sqrt_div' _ (by positivity : (0 : ℝ) ≤ 2 * u.re)]
    have h1 : √(2 * z.re) ≤ √(2 * u.re) := Real.sqrt_le_sqrt (by linarith)
    have h2 : 0 < √(2 * z.re) := Real.sqrt_pos.2 (by linarith)
    calc √((gram p a).re) / √(2 * u.re) / ‖blaschke p u‖ ≤ √((gram p a).re) / √(2 * z.re) / ‖blaschke p u‖ :=
          div_le_div_of_nonneg_right (div_le_div_of_nonneg_left (Real.sqrt_nonneg _) h2 h1) (norm_nonneg _)
      _ ≤ √((gram p a).re) / √(2 * z.re) / m :=
          div_le_div_of_nonneg_left (by positivity) hm0 hBm
  have hb := norm_rectBoundaryIntegral_le hre him hpt
  rw [rectBoundaryIntegral_mul_res hpin hUo hU hg, norm_mul] at hb
  have h2pi : ‖2 * (Real.pi : ℂ) * I‖ = 2 * Real.pi := by
    rw [norm_mul, Complex.norm_I, mul_one, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]; norm_num
  rw [h2pi] at hb
  have hpi := Real.pi_pos
  have hs : 0 < √(2 * z.re) := Real.sqrt_pos.2 (by linarith)
  rw [← le_div_iff₀' (by positivity)] at hb
  refine hb.trans_eq ?_
  field_simp

/-! ### Solving the corrected system -/

theorem lap_add (p a b : ι → ℂ) (w : ℂ) : lap p (a + b) w = lap p a w + lap p b w := by
  simp only [lap, Pi.add_apply, add_div, Finset.sum_add_distrib]

theorem lap_smul (p a : ι → ℂ) (c w : ℂ) : lap p (c • a) w = c * lap p a w := by
  simp only [lap, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_div_assoc]

theorem shift_add (p : ι → ℂ) (T : ℝ) (a b : ι → ℂ) : shift p T (a + b) = shift p T a + shift p T b := by
  funext i; simp only [shift, Pi.add_apply]; ring

theorem shift_smul (p : ι → ℂ) (T : ℝ) (a : ι → ℂ) (c : ℂ) : shift p T (c • a) = c • shift p T a := by
  funext i; simp only [shift, Pi.smul_apply, smul_eq_mul]; ring

theorem err_add (p : ι → ℂ) (T : ℝ) (a b : ι → ℂ) (w : ℂ) : err p T (a + b) w = err p T a w + err p T b w := by
  simp only [err, shift_add, lap_add, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  ring

theorem err_smul (p : ι → ℂ) (T : ℝ) (a : ι → ℂ) (c w : ℂ) : err p T (c • a) w = c * err p T a w := by
  simp only [err, shift_smul, lap_smul, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
  ring

/-- The corrected evaluation map `a ↦ (L_a(p_k) + err(p_k))_k`. -/
def evalMap (p : ι → ℂ) (T : ℝ) : (ι → ℂ) →ₗ[ℂ] (ι → ℂ) where
  toFun a k := lap p a (p k) + err p T a (p k)
  map_add' a b := by funext k; simp only [Pi.add_apply, lap_add, err_add]; ring
  map_smul' c a := by funext k; simp only [Pi.smul_apply, smul_eq_mul, lap_smul, err_smul, RingHom.id_apply]; ring

/-- The error on the boundary: `|err(u)| ≤ 2e^{−T Re z}(Re G(a))^{1/2}/(2 Re z)^{1/2}`. -/
theorem norm_err_le_onBd {p a : ι → ℂ} {z w : ℂ} (hz : 0 < z.re) (hre : z.re ≤ w.re)
    (hε : ∀ i, z.re ≤ (p i).re) {T : ℝ} (hT : 0 ≤ T) {u : ℂ} (hu : OnBd z w u) :
    ‖err p T a u‖ ≤ 2 * Real.exp (-(z.re * T)) * √((gram p a).re) / √(2 * z.re) := by
  have hure : z.re ≤ u.re := by
    have := hu.1.1
    rw [Set.mem_preimage, Set.uIcc_of_le hre] at this
    exact this.1
  have hu0 : 0 < u.re := hz.trans_le hure
  have hG := Cvs.Upstream.ExpSumBlaschkeProduct.gram_re_nonneg hz hε a
  refine (Cvs.Upstream.ExpSumTwoEndedError.norm_err_le hz hε a hT hu0).trans ?_
  rw [Real.sqrt_div' _ (by positivity : (0 : ℝ) ≤ 2 * u.re)]
  have h1 : √(2 * z.re) ≤ √(2 * u.re) := Real.sqrt_le_sqrt (by linarith)
  have h2 : 0 < √(2 * z.re) := Real.sqrt_pos.2 (by linarith)
  have he : Real.exp (-(u.re * T)) ≤ Real.exp (-(z.re * T)) :=
    Real.exp_le_exp.2 (by nlinarith)
  calc 2 * Real.exp (-(u.re * T)) * (√((gram p a).re) / √(2 * u.re))
      ≤ 2 * Real.exp (-(z.re * T)) * (√((gram p a).re) / √(2 * z.re)) := by
        refine mul_le_mul (by linarith) (div_le_div_of_nonneg_left (Real.sqrt_nonneg _) h2 h1)
          (by positivity) (by positivity)
    _ = _ := by ring

/-- **The corrected interpolation** (caseinf-attack Theorem 4 (a)–(d), by contour): with
`q = K_c·2e^{−T Re z}/(2 Re z)^{1/2} < 1`, there are coefficients with `L_a + err = f + c/(· − c₀)` at every point
and `(1 − q)(Re G(a))^{1/2} ≤ K_c M + |c|/(β(2 Re c₀)^{1/2})`, `β ≤ |B(c₀)|`. -/
theorem exists_solution {p : ι → ℂ} (hpi : Function.Injective p) {z w : ℂ} (hz : 0 < z.re)
    (hre : z.re ≤ w.re) (him : z.im ≤ w.im) (hpin : ∀ k, Inside z w (p k)) {m : ℝ} (hm0 : 0 < m)
    (hm : ∀ u, OnBd z w u → m ≤ ‖blaschke p u‖) {U : Set ℂ} (hUo : IsOpen U) (hU : closedRect z w ⊆ U)
    {T : ℝ} (hT : 0 ≤ T)
    (hq : (2 * (w.re - z.re) + 2 * (w.im - z.im)) / (2 * Real.pi * m * √(2 * z.re))
      * (2 * Real.exp (-(z.re * T)) / √(2 * z.re)) < 1)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) {M : ℝ} (hfM : ∀ u, OnBd z w u → ‖f u‖ ≤ M)
    (c : ℂ) {c₀ : ℂ} (hc₀ : 0 < c₀.re) (hc₀p : ∀ i, c₀ ≠ p i) {β : ℝ} (hβ0 : 0 < β)
    (hβ : β ≤ ‖blaschke p c₀‖) :
    ∃ a : ι → ℂ, (∀ k, lap p a (p k) + err p T a (p k) = f (p k) + c / (p k - c₀))
      ∧ (1 - (2 * (w.re - z.re) + 2 * (w.im - z.im)) / (2 * Real.pi * m * √(2 * z.re))
          * (2 * Real.exp (-(z.re * T)) / √(2 * z.re))) * √((gram p a).re)
        ≤ (2 * (w.re - z.re) + 2 * (w.im - z.im)) / (2 * Real.pi * m * √(2 * z.re)) * M
          + ‖c‖ / (β * √(2 * c₀.re)) := by
  set Kc := (2 * (w.re - z.re) + 2 * (w.im - z.im)) / (2 * Real.pi * m * √(2 * z.re)) with hKc
  set q := Kc * (2 * Real.exp (-(z.re * T)) / √(2 * z.re)) with hqdef
  have hε : ∀ i, z.re ≤ (p i).re := fun i => (hpin i).1.le
  have hp : ∀ i, 0 < (p i).re := fun i => hz.trans_le (hε i)
  have hs0 : 0 < √(2 * z.re) := Real.sqrt_pos.2 (by linarith)
  have hKc0 : 0 ≤ Kc := by
    rw [hKc]; refine div_nonneg (by nlinarith) (by positivity)
  -- the error part
  set U' := U ∩ {s : ℂ | -z.re < s.re} with hU'
  have hU'o : IsOpen U' := hUo.inter (isOpen_lt continuous_const Complex.continuous_re)
  have hU'r : closedRect z w ⊆ U' := by
    intro u hu
    refine ⟨hU hu, ?_⟩
    have := hu.1
    rw [Set.mem_preimage, Set.uIcc_of_le hre] at this
    show -z.re < u.re
    linarith [this.1]
  have herr : ∀ a : ι → ℂ, ‖∑ k, conj (a k) * err p T a (p k)‖ ≤ q * (gram p a).re := by
    intro a
    have hG := Cvs.Upstream.ExpSumBlaschkeProduct.gram_re_nonneg hz hε a
    have h := norm_sum_conj_mul_le (a := a) hz hre him hpin hm0 hm hU'o hU'r
      ((Cvs.Upstream.ExpSumTwoEndedError.differentiableOn_err hε T a).mono Set.inter_subset_right)
      (fun u hu => norm_err_le_onBd (a := a) hz hre hε hT hu)
    refine h.trans_eq ?_
    rw [hqdef]
    have : √((gram p a).re) * √((gram p a).re) = (gram p a).re := Real.mul_self_sqrt hG
    calc Kc * (2 * Real.exp (-(z.re * T)) * √((gram p a).re) / √(2 * z.re)) * √((gram p a).re)
        = Kc * (2 * Real.exp (-(z.re * T)) / √(2 * z.re)) * (√((gram p a).re) * √((gram p a).re)) := by ring
      _ = _ := by rw [this]
  -- injectivity
  have hinj : Function.Injective (evalMap p T) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    have hk : ∀ k, lap p a (p k) = -err p T a (p k) := fun k => by
      have := congrFun ha k
      simp only [evalMap, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at this
      linear_combination this
    have hgram : gram p a = -∑ k, conj (a k) * err p T a (p k) := by
      rw [Cvs.Upstream.ExpSumBlaschkeProduct.gram, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hk k]; ring
    have hG := Cvs.Upstream.ExpSumBlaschkeProduct.gram_re_nonneg hz hε a
    have h1 : (gram p a).re ≤ q * (gram p a).re := by
      have := herr a
      rw [← norm_neg, ← hgram] at this
      exact (Complex.re_le_norm _).trans this
    have h0 : (gram p a).re = 0 := by nlinarith
    exact Cvs.Upstream.ExpSumBlaschkeProduct.eq_zero_of_gram_re_eq_zero hpi hz hε h0
  have hsurj : Function.Surjective (evalMap p T) := LinearMap.injective_iff_surjective.1 hinj
  obtain ⟨a, ha⟩ := hsurj fun k => f (p k) + c / (p k - c₀)
  refine ⟨a, fun k => congrFun ha k, ?_⟩
  have hk : ∀ k, lap p a (p k) = f (p k) - err p T a (p k) + c * (1 / (p k - c₀)) := fun k => by
    have := congrFun ha k
    simp only [evalMap, LinearMap.coe_mk, AddHom.coe_mk] at this
    linear_combination this
  have hG := Cvs.Upstream.ExpSumBlaschkeProduct.gram_re_nonneg hz hε a
  set S := √((gram p a).re) with hS
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hSS : S * S = (gram p a).re := Real.mul_self_sqrt hG
  have hgram : gram p a = (∑ k, conj (a k) * f (p k)) - (∑ k, conj (a k) * err p T a (p k))
      - c * res p a c₀ := by
    rw [Cvs.Upstream.ExpSumBlaschkeProduct.gram, Cvs.Upstream.ExpSumBlaschkeProduct.res, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hk k]
    have : c₀ - p k ≠ 0 := sub_ne_zero.2 (hc₀p k)
    have : p k - c₀ ≠ 0 := sub_ne_zero.2 (hc₀p k).symm
    field_simp
    ring
  have hf1 := norm_sum_conj_mul_le (a := a) hz hre him hpin hm0 hm hUo hU hf hfM
  have hres : ‖res p a c₀‖ ≤ S / √(2 * c₀.re) / β := by
    refine (norm_res_le hz hε a hc₀ hc₀p).trans ?_
    rw [Real.sqrt_div' _ (by positivity : (0 : ℝ) ≤ 2 * c₀.re)]
    exact div_le_div_of_nonneg_left (by positivity) hβ0 hβ
  have hnorm : ‖gram p a‖ ≤ Kc * M * S + q * (gram p a).re + ‖c‖ * (S / √(2 * c₀.re) / β) := by
    have e := hgram
    have h3 : ‖c * res p a c₀‖ ≤ ‖c‖ * (S / √(2 * c₀.re) / β) := by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_left hres (norm_nonneg _)
    have h2 := herr a
    calc ‖gram p a‖ = ‖(∑ k, conj (a k) * f (p k)) - (∑ k, conj (a k) * err p T a (p k))
          - c * res p a c₀‖ := by rw [e]
      _ ≤ _ := (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add hf1 h2)) h3)
  have hbound : S * S ≤ Kc * M * S + q * (S * S) + ‖c‖ * (S / √(2 * c₀.re) / β) := by
    rw [hSS]
    exact (Complex.re_le_norm _).trans hnorm
  have hM0 : 0 ≤ M := by
    have hb : OnBd z w z := ⟨⟨by simp, by simp⟩, Or.inl rfl⟩
    exact (norm_nonneg _).trans (hfM z hb)
  have hc0s : 0 < √(2 * c₀.re) := Real.sqrt_pos.2 (by linarith)
  rcases hS0.lt_or_eq with hSp | hSz
  · have : S * (1 - q) ≤ Kc * M + ‖c‖ / (β * √(2 * c₀.re)) := by
      have e : ‖c‖ * (S / √(2 * c₀.re) / β) = S * (‖c‖ / (β * √(2 * c₀.re))) := by
        field_simp
      rw [e] at hbound
      have : S * (S * (1 - q)) ≤ S * (Kc * M + ‖c‖ / (β * √(2 * c₀.re))) := by nlinarith
      exact le_of_mul_le_mul_left this hSp
    linarith
  · rw [← hSz, mul_zero]
    positivity

end Cvs.Upstream.ExpSumContourInterpolation

end
