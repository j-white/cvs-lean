import Mathlib
import Cvs.StepA.ModePolynomialFarEnvelope
import Cvs.StepA.OddTrialErrorBudget
import Cvs.StepA.OneZeroParitySectors
import Cvs.StepA.OneZeroSectorBottoms
import Cvs.StepA.TopQuadruple
import Cvs.Zeta.GaussKernel.DivisorWeightCoordinates
import Cvs.Zeta.GaussKernel.ZeroChain
import Cvs.Zeta.GaussKernel.ZetaZeroStatement
import Cvs.Zeta.QuadraticWeightSummable
import Cvs.Zeta.ZeroSideMoments
import Cvs.Zeta.ZeroSideMomentsConverge

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The rest envelope is small against the top exponential
For zeros with `|del ρ| < δ` and `N(L) = O(L)` modes, `∑ m_ρ envE(L, N(L), z_ρ)` and
`∑ m_ρ envO(L, N(L), z_ρ)` are `o(e^{δL})`: dominated convergence against
`m_ρ(16C/γ_ρ² + [|γ_ρ| < 2πC]/(δ − |del ρ|))` for `(2N+1)/L ≤ C`, summable as `∑ m_ρ/γ_ρ² < ∞`.
At `N = ⌈ΩL/2π⌉₊` this covers the zeros off the line outside a finite set past which `|del| < δ`.
-/

noncomputable section

open Real Filter Topology Asymptotics

namespace Cvs.StepA.RestEnvelopeSmall
open Cvs.ZeroCounting

open Cvs.Zeta.GaussKernel.AdmissibleKernel (nonTrivialZeroSet)
open Cvs.StepA.OneZeroParitySectors (ue ve uo vo)
open Cvs.StepA.TopQuadruple (offLine integral_sq_nonneg)
open Cvs.StepA.ModePolynomialFarEnvelope (envE envO)

/-! ### One zero's envelope against `cosh(Im z · L)` -/

/-- `cosh(x/2)² ≤ cosh x`. -/
theorem cosh_half_sq_le (x : ℝ) : cosh (x / 2) ^ 2 ≤ cosh x := by
  have h := Real.cosh_two_mul (x / 2)
  rw [show 2 * (x / 2) = x by ring] at h
  nlinarith [sq_nonneg (sinh (x / 2))]

/-- For `L ≥ 0`, `∫_{−L/2}^{L/2} ve_z² ≤ L cosh(Im z · L)`. -/
theorem integral_ve_sq_le {L : ℝ} (hL : 0 ≤ L) (z : ℂ) :
    ∫ t in -(L / 2)..L / 2, ve z t ^ 2 ≤ L * cosh (z.im * L) := by
  have h := Cvs.StepA.OddTrialErrorBudget.sigE_add_sigO_le hL z
  have h1 := integral_sq_nonneg hL (ue z)
  have h2 := integral_sq_nonneg hL (uo z)
  have h3 := integral_sq_nonneg hL (vo z)
  unfold Cvs.StepA.OneZeroSectorBottoms.sigE Cvs.StepA.OneZeroSectorBottoms.sigO at h
  linarith

/-- For `L ≥ 0`, `∫_{−L/2}^{L/2} uo_z² ≤ L cosh(Im z · L)`. -/
theorem integral_uo_sq_le {L : ℝ} (hL : 0 ≤ L) (z : ℂ) :
    ∫ t in -(L / 2)..L / 2, uo z t ^ 2 ≤ L * cosh (z.im * L) := by
  have h := Cvs.StepA.OddTrialErrorBudget.sigE_add_sigO_le hL z
  have h1 := integral_sq_nonneg hL (ue z)
  have h2 := integral_sq_nonneg hL (ve z)
  have h3 := integral_sq_nonneg hL (vo z)
  unfold Cvs.StepA.OneZeroSectorBottoms.sigE Cvs.StepA.OneZeroSectorBottoms.sigO at h
  linarith

/-- For `L ≥ 0`, `16(2N+1)cosh²(Im z·L/2)/(L(Re z)²) ≤ 16(2N+1)/(L(Re z)²) · cosh(Im z · L)`. -/
theorem far_le_mul_cosh {L : ℝ} (hL : 0 ≤ L) (N : ℕ) (z : ℂ) :
    16 * (2 * N + 1) * cosh (z.im * L / 2) ^ 2 / (L * z.re ^ 2)
      ≤ 16 * (2 * N + 1) / (L * z.re ^ 2) * cosh (z.im * L) := by
  rw [mul_div_right_comm]
  exact mul_le_mul_of_nonneg_left (cosh_half_sq_le _) (by positivity)

/-- For `L ≥ 0` and `2·(2πN/L) ≤ |Re z|`, `envE L N z ≤ 16(2N+1)/(L(Re z)²) · cosh(Im z · L)`. -/
theorem envE_le_of_far {L : ℝ} (hL : 0 ≤ L) {N : ℕ} {z : ℂ} (h : 2 * (2 * π * N / L) ≤ |z.re|) :
    envE L N z ≤ 16 * (2 * N + 1) / (L * z.re ^ 2) * cosh (z.im * L) := by
  rw [envE, if_pos h]
  exact far_le_mul_cosh hL N z

/-- For `L ≥ 0` and `|Re z| < 2·(2πN/L)`, `envE L N z ≤ L cosh(Im z · L)`. -/
theorem envE_le_of_near {L : ℝ} (hL : 0 ≤ L) {N : ℕ} {z : ℂ}
    (h : ¬ 2 * (2 * π * N / L) ≤ |z.re|) : envE L N z ≤ L * cosh (z.im * L) := by
  rw [envE, if_neg h]
  exact integral_ve_sq_le hL z

/-- For `L ≥ 0` and `2·(2πN/L) ≤ |Re z|`, `envO L N z ≤ 16(2N+1)/(L(Re z)²) · cosh(Im z · L)`. -/
theorem envO_le_of_far {L : ℝ} (hL : 0 ≤ L) {N : ℕ} {z : ℂ} (h : 2 * (2 * π * N / L) ≤ |z.re|) :
    envO L N z ≤ 16 * (2 * N + 1) / (L * z.re ^ 2) * cosh (z.im * L) := by
  rw [envO, if_pos h]
  exact far_le_mul_cosh hL N z

/-- For `L ≥ 0` and `|Re z| < 2·(2πN/L)`, `envO L N z ≤ L cosh(Im z · L)`. -/
theorem envO_le_of_near {L : ℝ} (hL : 0 ≤ L) {N : ℕ} {z : ℂ}
    (h : ¬ 2 * (2 * π * N / L) ≤ |z.re|) : envO L N z ≤ L * cosh (z.im * L) := by
  rw [envO, if_neg h]
  exact integral_uo_sq_le hL z

/-! ### The zeros against `1/γ²` -/

/-- `ρ ↦ m_ρ/γ_ρ²` is summable over the nontrivial zeros. -/
theorem summable_divisorWeight_div_sq :
    Summable fun ρ : nonTrivialZeroSet =>
      (Cvs.Criterion.divisorWeight ρ : ℝ) * (1 / ((ρ : ℂ).im) ^ 2) := by
  refine Summable.of_norm_bounded_eventually
    (Cvs.Zeta.QuadraticWeightSummable.summable_divisorWeight_sq.mul_left 2) ?_
  rw [Filter.eventually_cofinite]
  refine (Cvs.GaussKernel.finite_window 1).subset fun ρ hρ => ?_
  simp only [Set.mem_ofPred_eq] at hρ ⊢
  by_contra h
  apply hρ
  have hg : Cvs.GaussKernel.gam ρ = (ρ : ℂ).im := rfl
  rw [hg, not_le] at h
  set x := (ρ : ℂ).im with hx
  have hx2 : 1 ≤ x ^ 2 := by
    have := pow_le_pow_left₀ zero_le_one h.le 2
    rwa [one_pow, sq_abs] at this
  have hm : (0 : ℝ) ≤ Cvs.Criterion.divisorWeight ρ := Nat.cast_nonneg _
  have hinv : 1 / x ^ 2 ≤ 2 * (1 / (1 + x ^ 2)) := by
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hm (by positivity))]
  calc (Cvs.Criterion.divisorWeight ρ : ℝ) * (1 / x ^ 2)
      ≤ (Cvs.Criterion.divisorWeight ρ : ℝ) * (2 * (1 / (1 + x ^ 2))) :=
        mul_le_mul_of_nonneg_left hinv hm
    _ = 2 * ((Cvs.Criterion.divisorWeight ρ : ℝ) * (1 / (1 + x ^ 2))) := by ring

/-! ### One zero against `e^{δL}` -/

/-- For every `L` and `|y| < δ`, `L e^{|y|L}/e^{δL} ≤ 1/(δ − |y|)`. -/
theorem mul_exp_div_exp_le {L y δ : ℝ} (hy : |y| < δ) :
    L * exp (|y| * L) / exp (δ * L) ≤ 1 / (δ - |y|) := by
  have ha : 0 < δ - |y| := sub_pos.mpr hy
  rw [div_le_div_iff₀ (exp_pos _) ha, one_mul]
  have h1 := mul_le_mul_of_nonneg_right (Real.add_one_le_exp ((δ - |y|) * L))
    (exp_pos (|y| * L)).le
  have h2 : exp ((δ - |y|) * L) * exp (|y| * L) = exp (δ * L) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h3 := exp_pos (|y| * L)
  nlinarith

/-- With `(2N+1)/L ≤ C`, `16(2N+1)/(L x²) ≤ 16C/x²`. -/
theorem far_coef_le {L C : ℝ} {N : ℕ} (hC : (2 * N + 1) / L ≤ C) (x : ℝ) :
    16 * (2 * N + 1) / (L * x ^ 2) ≤ 16 * C / x ^ 2 := by
  have e : 16 * (2 * (N : ℝ) + 1) / (L * x ^ 2) = 16 * ((2 * N + 1) / L) / x ^ 2 := by ring
  rw [e]
  exact div_le_div_of_nonneg_right (by linarith) (sq_nonneg _)

/-- For `L ≥ 0` and `(2N+1)/L ≤ C`, a point with `|x| < 2·(2πN/L)` has `|x| < 2πC`. -/
theorem abs_lt_of_near {L C : ℝ} (hL : 0 ≤ L) {N : ℕ} (hC : (2 * N + 1) / L ≤ C) {x : ℝ}
    (h : ¬ 2 * (2 * π * N / L) ≤ |x|) : |x| < 2 * π * C := by
  have h1 : 2 * (2 * π * N / L) ≤ 2 * π * ((2 * N + 1) / L) := by
    rw [show 2 * (2 * π * (N : ℝ) / L) = 2 * π * (2 * N / L) by ring]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (by linarith) hL)
      (by positivity)
  have h2 : 2 * π * ((2 * N + 1) / L) ≤ 2 * π * C := mul_le_mul_of_nonneg_left hC (by positivity)
  linarith [not_le.mp h]

section Envelope

variable {env : ℝ → ℕ → ℂ → ℝ}

/-- **One point against `e^{δL}`**: an envelope below the far and near bounds has, for `L > 0`,
`(2N+1)/L ≤ C` and `|Im z| < δ`,
`env L N z / e^{δL} ≤ 16C/(Re z)² + [|Re z| < 2πC]/(δ − |Im z|)`. -/
theorem env_div_exp_le
    (hfar : ∀ L : ℝ, 0 < L → ∀ (N : ℕ) (z : ℂ), 2 * (2 * π * N / L) ≤ |z.re| →
      env L N z ≤ 16 * (2 * N + 1) / (L * z.re ^ 2) * cosh (z.im * L))
    (hnear : ∀ L : ℝ, 0 < L → ∀ (N : ℕ) (z : ℂ), ¬ 2 * (2 * π * N / L) ≤ |z.re| →
      env L N z ≤ L * cosh (z.im * L))
    {L C δ : ℝ} (hL : 0 < L) {N : ℕ} (hC : (2 * N + 1) / L ≤ C) {z : ℂ} (hz : |z.im| < δ) :
    env L N z / exp (δ * L)
      ≤ 16 * C / z.re ^ 2 + if |z.re| < 2 * π * C then 1 / (δ - |z.im|) else 0 := by
  have hE : 0 < exp (δ * L) := exp_pos _
  have hcosh : cosh (z.im * L) ≤ exp (|z.im| * L) := by
    refine (Cvs.StepA.OddTrialErrorBudget.cosh_le_exp_abs _).trans_eq ?_
    rw [abs_mul, abs_of_pos hL]
  have hC0 : 0 < C := lt_of_lt_of_le (by positivity) hC
  have ha : 0 < δ - |z.im| := sub_pos.mpr hz
  have h16 : 0 ≤ 16 * C / z.re ^ 2 := by positivity
  by_cases hf : 2 * (2 * π * N / L) ≤ |z.re|
  · have hite : 0 ≤ if |z.re| < 2 * π * C then 1 / (δ - |z.im|) else 0 := by
      split_ifs
      · positivity
      · exact le_refl 0
    have hexp : exp (|z.im| * L) ≤ exp (δ * L) :=
      exp_le_exp.mpr (mul_le_mul_of_nonneg_right hz.le hL.le)
    have hK : 0 ≤ 16 * (2 * N + 1) / (L * z.re ^ 2) := by positivity
    calc env L N z / exp (δ * L)
        ≤ 16 * (2 * N + 1) / (L * z.re ^ 2) * cosh (z.im * L) / exp (δ * L) :=
          div_le_div_of_nonneg_right (hfar L hL N z hf) hE.le
      _ ≤ 16 * (2 * N + 1) / (L * z.re ^ 2) * exp (δ * L) / exp (δ * L) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hcosh.trans hexp) hK) hE.le
      _ = 16 * (2 * N + 1) / (L * z.re ^ 2) := mul_div_cancel_right₀ _ hE.ne'
      _ ≤ 16 * C / z.re ^ 2 := far_coef_le hC _
      _ ≤ _ := le_add_of_nonneg_right hite
  · rw [if_pos (abs_lt_of_near hL.le hC hf)]
    calc env L N z / exp (δ * L) ≤ L * cosh (z.im * L) / exp (δ * L) :=
          div_le_div_of_nonneg_right (hnear L hL N z hf) hE.le
      _ ≤ L * exp (|z.im| * L) / exp (δ * L) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hcosh hL.le) hE.le
      _ ≤ 1 / (δ - |z.im|) := mul_exp_div_exp_le hz
      _ ≤ 16 * C / z.re ^ 2 + 1 / (δ - |z.im|) := le_add_of_nonneg_left h16

/-- `N(L) = O(L)` gives a `C` with `1 ≤ L` and `(2N(L)+1)/L ≤ C` eventually. -/
theorem exists_eventually_div_le {N : ℝ → ℕ} (hN : (fun L => (N L : ℝ)) =O[atTop] fun L => L) :
    ∃ C : ℝ, ∀ᶠ L in atTop, 1 ≤ L ∧ (2 * N L + 1) / L ≤ C := by
  obtain ⟨c, -, h⟩ := hN.exists_pos
  refine ⟨2 * c + 1, ?_⟩
  filter_upwards [h.bound, eventually_ge_atTop 1] with L hb hL1
  refine ⟨hL1, ?_⟩
  have hL : 0 < L := by linarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _), abs_of_pos hL] at hb
  rw [div_le_iff₀ hL]
  nlinarith

/-- **One point is `o(e^{δL})`**: an envelope between `0` and the far and near bounds has
`env L (N L) z = o(e^{δL})` when `|Im z| < δ` and `N(L) = O(L)`. -/
theorem isLittleO_env
    (h0 : ∀ L : ℝ, 0 < L → ∀ (N : ℕ) (z : ℂ), 0 ≤ env L N z)
    (hfar : ∀ L : ℝ, 0 < L → ∀ (N : ℕ) (z : ℂ), 2 * (2 * π * N / L) ≤ |z.re| →
      env L N z ≤ 16 * (2 * N + 1) / (L * z.re ^ 2) * cosh (z.im * L))
    (hnear : ∀ L : ℝ, 0 < L → ∀ (N : ℕ) (z : ℂ), ¬ 2 * (2 * π * N / L) ≤ |z.re| →
      env L N z ≤ L * cosh (z.im * L))
    {z : ℂ} {δ : ℝ} (hz : |z.im| < δ) {N : ℝ → ℕ}
    (hN : (fun L => (N L : ℝ)) =O[atTop] fun L => L) :
    (fun L => env L (N L) z) =o[atTop] fun L => exp (δ * L) := by
  obtain ⟨C, hC⟩ := exists_eventually_div_le hN
  refine IsBigO.trans_isLittleO (IsBigO.of_bound (1 + 16 * C / z.re ^ 2) ?_)
    (Cvs.StepA.OddTrialErrorBudget.isLittleO_mul_cosh hz)
  filter_upwards [hC] with L ⟨hL1, hCL⟩
  have hL : 0 < L := by linarith
  have hC0 : 0 < C := lt_of_lt_of_le (by positivity) hCL
  have hc : 0 < cosh (z.im * L) := Real.cosh_pos _
  have h16 : 0 ≤ 16 * C / z.re ^ 2 := by positivity
  have hLc : 0 ≤ L * cosh (z.im * L) := mul_nonneg hL.le hc.le
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (h0 L hL (N L) z), abs_of_nonneg hLc]
  by_cases hf : 2 * (2 * π * (N L) / L) ≤ |z.re|
  · have h1 := hfar L hL (N L) z hf
    have h2 := far_coef_le hCL z.re
    have h3 : cosh (z.im * L) ≤ L * cosh (z.im * L) := le_mul_of_one_le_left hc.le hL1
    calc env L (N L) z ≤ 16 * (2 * (N L) + 1) / (L * z.re ^ 2) * cosh (z.im * L) := h1
      _ ≤ 16 * C / z.re ^ 2 * (L * cosh (z.im * L)) := mul_le_mul h2 h3 hc.le h16
      _ ≤ (1 + 16 * C / z.re ^ 2) * (L * cosh (z.im * L)) := by nlinarith
  · have h1 := hnear L hL (N L) z hf
    nlinarith [mul_nonneg h16 hLc]

/-- **The dominated sum**: an envelope between `0` and the far and near bounds has
`(∑_{ρ ∈ T} m_ρ env(L, N(L), z_ρ))/e^{δL} → 0` when every `ρ ∈ T` has `|del ρ| < δ` and
`N(L) = O(L)`. -/
theorem tendsto_tsum_div_exp
    (h0 : ∀ L : ℝ, 0 < L → ∀ (N : ℕ) (z : ℂ), 0 ≤ env L N z)
    (hfar : ∀ L : ℝ, 0 < L → ∀ (N : ℕ) (z : ℂ), 2 * (2 * π * N / L) ≤ |z.re| →
      env L N z ≤ 16 * (2 * N + 1) / (L * z.re ^ 2) * cosh (z.im * L))
    (hnear : ∀ L : ℝ, 0 < L → ∀ (N : ℕ) (z : ℂ), ¬ 2 * (2 * π * N / L) ≤ |z.re| →
      env L N z ≤ L * cosh (z.im * L))
    {T : Set nonTrivialZeroSet} {δ : ℝ} (hT : ∀ ρ ∈ T, |Cvs.GaussKernel.del ρ| < δ)
    {N : ℝ → ℕ} (hN : (fun L => (N L : ℝ)) =O[atTop] fun L => L) :
    Tendsto (fun L => (∑' ρ : ↥T,
        (Cvs.Criterion.divisorWeight ρ : ℝ) * env L (N L) (Cvs.ZeroCounting.zPoint ρ)) / exp (δ * L))
      atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := exists_eventually_div_le hN
  have hz : ∀ ρ ∈ T, |(Cvs.ZeroCounting.zPoint ρ).im| < δ := fun ρ hρ => by
    rw [Cvs.StepA.TopQuadruple.im_zPoint_eq_neg_del, abs_neg]
    exact hT ρ hρ
  set b : nonTrivialZeroSet → ℝ := fun ρ => (Cvs.Criterion.divisorWeight ρ : ℝ)
    * (16 * C / (Cvs.ZeroCounting.zPoint ρ).re ^ 2
      + if |(Cvs.ZeroCounting.zPoint ρ).re| < 2 * π * C
        then 1 / (δ - |(Cvs.ZeroCounting.zPoint ρ).im|) else 0) with hb
  have hbs : Summable b := by
    have h1 := summable_divisorWeight_div_sq.mul_left (16 * C)
    have h2 : Summable fun ρ : nonTrivialZeroSet => (Cvs.Criterion.divisorWeight ρ : ℝ)
        * (if |(Cvs.ZeroCounting.zPoint ρ).re| < 2 * π * C
          then 1 / (δ - |(Cvs.ZeroCounting.zPoint ρ).im|) else 0) := by
      refine summable_of_hasFiniteSupport
        ((Cvs.GaussKernel.finite_window (2 * π * C)).subset fun ρ hρ => ?_)
      rw [Function.mem_support] at hρ
      simp only [Set.mem_ofPred_eq]
      by_contra h
      apply hρ
      have hg : Cvs.GaussKernel.gam ρ = (Cvs.ZeroCounting.zPoint ρ).re :=
        (Cvs.ZeroCounting.zPoint_re ρ).symm
      rw [hg] at h
      rw [if_neg fun h' => h h'.le, mul_zero]
    refine (h1.add h2).congr fun ρ => ?_
    simp only [hb, Cvs.ZeroCounting.zPoint_re]
    ring
  have hpt : ∀ ρ : ↥T, Tendsto (fun L => (Cvs.Criterion.divisorWeight ρ : ℝ)
      * env L (N L) (Cvs.ZeroCounting.zPoint ρ) / exp (δ * L)) atTop (𝓝 0) := fun ρ =>
    ((isLittleO_env h0 hfar hnear (hz ρ ρ.2) hN).const_mul_left _).tendsto_div_nhds_zero
  have hdom : ∀ᶠ L in atTop, ∀ ρ : ↥T, ‖(Cvs.Criterion.divisorWeight ρ : ℝ)
      * env L (N L) (Cvs.ZeroCounting.zPoint ρ) / exp (δ * L)‖ ≤ b ρ := by
    filter_upwards [hC] with L ⟨hL1, hCL⟩ ρ
    have hL : 0 < L := by linarith
    have hm : (0 : ℝ) ≤ Cvs.Criterion.divisorWeight ρ := Nat.cast_nonneg _
    have he := h0 L hL (N L) (Cvs.ZeroCounting.zPoint ρ)
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (mul_nonneg hm he) (exp_pos _).le),
      mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (env_div_exp_le hfar hnear hL hCL (hz ρ ρ.2)) hm
  have h := tendsto_tsum_of_dominated_convergence (hbs.subtype (· ∈ T)) hpt hdom
  rw [tsum_zero] at h
  exact h.congr fun L => tsum_div_const

end Envelope

/-! ### The even and odd envelopes -/

/-- **The even envelope sum is `o(e^{δL})`**: for zeros `ρ ∈ T` with `|del ρ| < δ` and
`N(L) = O(L)`, `(∑_{ρ ∈ T} m_ρ envE(L, N(L), z_ρ))/e^{δL} → 0`. -/
theorem tendsto_tsum_envE_div_exp {T : Set nonTrivialZeroSet} {δ : ℝ}
    (hT : ∀ ρ ∈ T, |Cvs.GaussKernel.del ρ| < δ) {N : ℝ → ℕ}
    (hN : (fun L => (N L : ℝ)) =O[atTop] fun L => L) :
    Tendsto (fun L => (∑' ρ : ↥T,
        (Cvs.Criterion.divisorWeight ρ : ℝ) * envE L (N L) (Cvs.ZeroCounting.zPoint ρ)) / exp (δ * L))
      atTop (𝓝 0) :=
  tendsto_tsum_div_exp (fun _ hL N z => Cvs.StepA.ModePolynomialFarEnvelope.envE_nonneg hL.le N z)
    (fun _ hL _ _ h => envE_le_of_far hL.le h) (fun _ hL _ _ h => envE_le_of_near hL.le h) hT hN

/-- **The odd envelope sum is `o(e^{δL})`**: for zeros `ρ ∈ T` with `|del ρ| < δ` and
`N(L) = O(L)`, `(∑_{ρ ∈ T} m_ρ envO(L, N(L), z_ρ))/e^{δL} → 0`. -/
theorem tendsto_tsum_envO_div_exp {T : Set nonTrivialZeroSet} {δ : ℝ}
    (hT : ∀ ρ ∈ T, |Cvs.GaussKernel.del ρ| < δ) {N : ℝ → ℕ}
    (hN : (fun L => (N L : ℝ)) =O[atTop] fun L => L) :
    Tendsto (fun L => (∑' ρ : ↥T,
        (Cvs.Criterion.divisorWeight ρ : ℝ) * envO L (N L) (Cvs.ZeroCounting.zPoint ρ)) / exp (δ * L))
      atTop (𝓝 0) :=
  tendsto_tsum_div_exp (fun _ hL N z => Cvs.StepA.ModePolynomialFarEnvelope.envO_nonneg hL.le N z)
    (fun _ hL _ _ h => envO_le_of_far hL.le h) (fun _ hL _ _ h => envO_le_of_near hL.le h) hT hN

/-! ### Bandwidth `Ω`: the zeros off the line outside a finite set -/

/-- `⌈ΩL/2π⌉₊ = O(L)` as `L → ∞`, for every real `Ω`. -/
theorem natCeil_isBigO (Ω : ℝ) :
    (fun L : ℝ => ((⌈Ω * L / (2 * π)⌉₊ : ℕ) : ℝ)) =O[atTop] fun L => L := by
  refine IsBigO.of_bound (|Ω| / (2 * π) + 1) ?_
  filter_upwards [eventually_ge_atTop 1] with L hL
  have hL0 : 0 ≤ L := by linarith
  set A := |Ω| / (2 * π) with hA
  have h1 : (⌈Ω * L / (2 * π)⌉₊ : ℝ) ≤ ⌈|Ω * L / (2 * π)|⌉₊ := by
    exact_mod_cast Nat.ceil_mono (le_abs_self _)
  have h2 : (⌈|Ω * L / (2 * π)|⌉₊ : ℝ) < |Ω * L / (2 * π)| + 1 :=
    Nat.ceil_lt_add_one (abs_nonneg _)
  have h3 : |Ω * L / (2 * π)| = A * L := by
    rw [abs_div, abs_mul, abs_of_nonneg hL0, abs_of_pos (by positivity : (0 : ℝ) < 2 * π), hA]
    ring
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg hL0]
  nlinarith

end Cvs.StepA.RestEnvelopeSmall
