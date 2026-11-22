import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.BandECouplingCollar
import Cvs.L2a.BandRungOutgoingWave
import Cvs.L2a.BandTransferBandForm
import Cvs.L2a.BernsteinRieszSymbolBounds
import Cvs.L2a.CutKernelSimplified
import Cvs.L2a.CutSymbolWavenumber
import Cvs.L2a.FarIntegrationByParts
import Cvs.L2a.OrbitGapIntegerM
import Cvs.L2a.QIdentityCutPoint
import Cvs.Prolate.BandMassLaw
import Cvs.Prolate.CosineChristoffelDarboux
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The cut multiplier of a band rung is a band multiplier
`ν(ζ) = (1/m)∫ g(s)e^{ics}μ̃(s/m, ζ) ds` is holomorphic on `Ω` and splits as `ν = ν_si + ν_co`. At real
`|η| ≥ 1 − δ`, `|ν| ≤ (K₀^si + 23‖g‖₁/c²)/m`; on the strip, `|ν| ≤ (8F/c + 130‖g‖₁/c²)/m` with `F = sup|ψ|`, so
Cauchy at radius `1/8` gives `|ν^{(k)}| ≤ (K_b/m)k!4^k` for `k ≤ 3`, `K_b = 64F/c + 1040‖g‖₁/c²`.
-/

noncomputable section

namespace Cvs.L2a.CutMultiplierBand

open Real Set Complex Metric MeasureTheory
open Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.FarIntegrationByParts Cvs.L2a.CutSymbolWavenumber
open Cvs.L2a.BandRungOutgoingWave (nuCut nuSi gL1)
open scoped Interval

/-! ### Definitions -/

/-- The cut multiplier at complex `ζ = ξ/c`: `(1/m)∫ g(s)e^{icx₀s/m}μ̃(s/m, x₀, ζ) ds`. -/
def nuCutC (c : ℝ) (g : ℝ → ℝ) (m x₀ : ℝ) (ζ : ℂ) : ℂ :=
  ((1 / m : ℝ) : ℂ) * ∫ s in (-1 : ℝ)..1, (g s : ℂ) * eF c (s / m) x₀ * muQξC c (s / m) x₀ ζ

/-- The `si` part at complex `ζ`: `(1/m)∫ g(s)e^{icx₀s/m}(−i/(c(s/m + ζ))) ds`. -/
def nuSiC (c : ℝ) (g : ℝ → ℝ) (m x₀ : ℝ) (ζ : ℂ) : ℂ :=
  ((1 / m : ℝ) : ℂ) * ∫ s in (-1 : ℝ)..1,
    (g s : ℂ) * eF c (s / m) x₀ * (-I / ((c : ℂ) * (((s / m : ℝ) : ℂ) + ζ)))

/-- The `co` part at complex `ζ`: `(1/m)∫ g(s)e^{icx₀s/m}h(s/m, x₀, ζ) ds`. -/
def nuCoC (c : ℝ) (g : ℝ → ℝ) (m x₀ : ℝ) (ζ : ℂ) : ℂ :=
  ((1 / m : ℝ) : ℂ) * ∫ s in (-1 : ℝ)..1, (g s : ℂ) * eF c (s / m) x₀ * hcoC c (s / m) x₀ ζ

/-- The `co` constant of `N_{m,0}`: `K₀^c = 23‖g‖₁/c²`. -/
def K0c (c : ℝ) (g : ℝ → ℝ) : ℝ := 23 * gL1 g / c ^ 2

/-- The derivative constant `K_b = 64F/c + 1040‖g‖₁/c²`. -/
def KbCut (c : ℝ) (g : ℝ → ℝ) (F : ℝ) : ℝ := 64 * F / c + 1040 * gL1 g / c ^ 2

/-- The norms `N_{m,0} = (K₀^si + K₀^c)/m` and `N_{m,k} = (K_b/m)k!4^k`. -/
def Ncut (c : ℝ) (g : ℝ → ℝ) (F m : ℝ) (k : ℕ) : ℝ :=
  if k = 0 then (Cvs.L2a.BandECouplingCollar.K0si c g + K0c c g) / m else KbCut c g F / m * ((k.factorial : ℝ) * 4 ^ k)

/-- The `ζ`-derivative of `μ̃`: `p[ic/Q + 2pc²ζ·i(cζ − cy)/Q² + 4pc²ζQ′/Q³]`. -/
def dmuQξC (c y x : ℝ) (ζ : ℂ) : ℂ :=
  ((pP x : ℝ) : ℂ) * (I * (c : ℂ) / qQξC c y x ζ
    + 2 * ((pP x : ℝ) : ℂ) * (c : ℂ) ^ 2 * ζ * (I * ((c : ℂ) * ζ - (c : ℂ) * (y : ℂ))) / qQξC c y x ζ ^ 2
    + 4 * ((pP x : ℝ) : ℂ) * (c : ℂ) ^ 2 * ζ * qQ₁ c y x / qQξC c y x ζ ^ 3)

/-! ### Elementary facts -/

theorem div_mem_half {m s : ℝ} (hm : 2 ≤ m) (hs : s ∈ Icc (-1 : ℝ) 1) : s / m ∈ Icc (-1 / 2 : ℝ) (1 / 2) := by
  have hm0 : 0 < m := by linarith
  constructor
  · rw [le_div_iff₀ hm0]; nlinarith [hs.1]
  · rw [div_le_iff₀ hm0]; nlinarith [hs.2]

theorem abs_le_half_of_mem {y : ℝ} (hy : y ∈ Icc (-1 / 2 : ℝ) (1 / 2)) : |y| ≤ 1 / 2 :=
  abs_le.2 ⟨by linarith [hy.1], hy.2⟩

theorem ofReal_mem_omegaC {η : ℝ} (hη : 3 / 4 ≤ |η|) : (η : ℂ) ∈ omegaC :=
  stripC_subset_omegaC (closedBall_subset_stripC hη (mem_closedBall_self (by norm_num)))

theorem gL1_nonneg (g : ℝ → ℝ) : 0 ≤ gL1 g :=
  intervalIntegral.integral_nonneg (by norm_num) fun _ _ => abs_nonneg _

theorem norm_eF (c y x : ℝ) : ‖eF c y x‖ = 1 := by
  unfold eF; exact Complex.norm_exp_ofReal_mul_I _

theorem continuous_eF_div (c m x : ℝ) : Continuous fun s : ℝ => eF c (s / m) x := by
  unfold eF; fun_prop

/-! ### `μ̃` and its derivative, jointly continuous -/

theorem continuous_qQξC_pair (c x : ℝ) : Continuous fun p : ℝ × ℂ => qQξC c p.1 x p.2 := by
  unfold qQξC; fun_prop

theorem continuous_qQ₁_pair (c x : ℝ) : Continuous fun p : ℝ × ℂ => qQ₁ c p.1 x := by
  unfold qQ₁; fun_prop

theorem qQξC_ne_zero_pair {c x : ℝ} (hc : 0 < c) (hx : 1 < x) {p : ℝ × ℂ}
    (hp : p ∈ Icc (-1 / 2 : ℝ) (1 / 2) ×ˢ omegaC) : qQξC c p.1 x p.2 ≠ 0 :=
  qQξC_ne_zero hc hx (abs_le_half_of_mem hp.1) hp.2

/-- `μ̃(y, ζ)` is jointly continuous on `[−½, ½] × Ω`. -/
theorem continuousOn_muQξC_pair {c x : ℝ} (hc : 0 < c) (hx : 1 < x) :
    ContinuousOn (fun p : ℝ × ℂ => muQξC c p.1 x p.2) (Icc (-1 / 2 : ℝ) (1 / 2) ×ˢ omegaC) := by
  intro p hp
  have hQ := qQξC_ne_zero_pair hc hx hp
  have hQc := (continuous_qQξC_pair c x).continuousAt (x := p)
  have h1c := (continuous_qQ₁_pair c x).continuousAt (x := p)
  have hn : Continuous fun p : ℝ × ℂ => I * ((c : ℂ) * p.2 - (c : ℂ) * (p.1 : ℂ)) := by fun_prop
  refine ContinuousAt.continuousWithinAt ?_
  have hQ2 : qQξC c p.1 x p.2 ^ 2 ≠ 0 := pow_ne_zero 2 hQ
  have hnc := hn.continuousAt (x := p)
  unfold muQξC
  fun_prop (disch := assumption)

/-- `∂_ζμ̃(y, ζ)` is jointly continuous on `[−½, ½] × Ω`. -/
theorem continuousOn_dmuQξC_pair {c x : ℝ} (hc : 0 < c) (hx : 1 < x) :
    ContinuousOn (fun p : ℝ × ℂ => dmuQξC c p.1 x p.2) (Icc (-1 / 2 : ℝ) (1 / 2) ×ˢ omegaC) := by
  intro p hp
  have hQ := qQξC_ne_zero_pair hc hx hp
  have hQc := (continuous_qQξC_pair c x).continuousAt (x := p)
  have h1c := (continuous_qQ₁_pair c x).continuousAt (x := p)
  have hn1 : Continuous fun p : ℝ × ℂ => I * (c : ℂ) := by fun_prop
  have hn2 : Continuous fun p : ℝ × ℂ =>
      2 * ((pP x : ℝ) : ℂ) * (c : ℂ) ^ 2 * p.2 * (I * ((c : ℂ) * p.2 - (c : ℂ) * (p.1 : ℂ))) := by fun_prop
  have hn3 : Continuous fun p : ℝ × ℂ => 4 * ((pP x : ℝ) : ℂ) * (c : ℂ) ^ 2 * p.2 := by fun_prop
  refine ContinuousAt.continuousWithinAt ?_
  have hQ2 : qQξC c p.1 x p.2 ^ 2 ≠ 0 := pow_ne_zero 2 hQ
  have hQ3 : qQξC c p.1 x p.2 ^ 3 ≠ 0 := pow_ne_zero 3 hQ
  have hn1c := hn1.continuousAt (x := p)
  have hn2c := hn2.continuousAt (x := p)
  have hn3c := hn3.continuousAt (x := p)
  unfold dmuQξC
  fun_prop (disch := assumption)

/-- `∂_ζQ = −2pc²ζ`. -/
theorem hasDerivAt_qQξC (c y x : ℝ) (ζ : ℂ) :
    HasDerivAt (qQξC c y x) (-(2 * ((pP x : ℝ) : ℂ) * (c : ℂ) ^ 2 * ζ)) ζ := by
  have h := ((((hasDerivAt_pow 2 ζ).const_mul ((c : ℂ) ^ 2)).const_sub ((c : ℂ) ^ 2 * (y : ℂ) ^ 2)).const_mul
    ((pP x : ℝ) : ℂ)).sub_const (2 * I * (c : ℂ) * (x : ℂ) * (y : ℂ))
  refine h.congr_deriv ?_
  push_cast
  ring

/-- **`∂_ζμ̃ = dmuQξC`** wherever `Q ≠ 0`. -/
theorem hasDerivAt_muQξC {c y x : ℝ} {ζ : ℂ} (hQ : qQξC c y x ζ ≠ 0) :
    HasDerivAt (muQξC c y x) (dmuQξC c y x ζ) ζ := by
  have hQd := hasDerivAt_qQξC c y x ζ
  have hn : HasDerivAt (fun ζ : ℂ => I * ((c : ℂ) * ζ - (c : ℂ) * (y : ℂ))) (I * (c : ℂ)) ζ := by
    have := (((hasDerivAt_id ζ).const_mul (c : ℂ)).sub_const ((c : ℂ) * (y : ℂ))).const_mul I
    simpa using this
  have h1 := hn.div hQd hQ
  have h2 := (hasDerivAt_const ζ (qQ₁ c y x)).div (hQd.pow 2) (pow_ne_zero 2 hQ)
  refine ((h1.add h2).const_mul ((pP x : ℝ) : ℂ)).congr_deriv ?_
  simp only [Pi.pow_apply]
  unfold dmuQξC
  field_simp
  ring

/-- A jointly continuous kernel on `[−½, ½] × Ω`, sampled along `y = s/m`, is continuous in `s`. -/
theorem continuousOn_comp_div {φ : ℝ → ℂ → ℂ}
    (hφ : ContinuousOn (fun p : ℝ × ℂ => φ p.1 p.2) (Icc (-1 / 2 : ℝ) (1 / 2) ×ˢ omegaC)) {m : ℝ}
    (hm : 2 ≤ m) {ζ : ℂ} (hζ : ζ ∈ omegaC) : ContinuousOn (fun s : ℝ => φ (s / m) ζ) (Icc (-1) 1) :=
  hφ.comp (f := fun s : ℝ => (s / m, ζ)) (by fun_prop : Continuous fun s : ℝ => (s / m, ζ)).continuousOn
    fun _ hs => ⟨div_mem_half hm hs, hζ⟩

theorem continuousOn_pole_s {c m : ℝ} (hc : 0 < c) (hm : 2 ≤ m) {ζ : ℂ} (hζ : ζ ∈ omegaC) :
    ContinuousOn (fun s : ℝ => -I / ((c : ℂ) * (((s / m : ℝ) : ℂ) + ζ))) (Icc (-1) 1) :=
  continuousOn_const.div₀ (by fun_prop : Continuous fun s : ℝ => (c : ℂ) * (((s / m : ℝ) : ℂ) + ζ)).continuousOn
    fun _ hs => mul_ne_zero (Complex.ofReal_ne_zero.2 hc.ne')
      (add_ne_zero_of_mem_omegaC (abs_le_half_of_mem (div_mem_half hm hs)) hζ)

/-! ### Differentiation under the integral in `ζ` -/

/-- **Differentiation under the integral** in a complex parameter, with the derivative bounded on a ball. -/
theorem hasDerivAt_cint_near {G : ℝ → ℂ} {k k' : ℂ → ℝ → ℂ} {ζ₀ : ℂ} {r C : ℝ} (hr : 0 < r)
    (hG : ContinuousOn G (Icc (-1) 1)) (hkc : ∀ ζ ∈ ball ζ₀ r, ContinuousOn (k ζ) (Icc (-1) 1))
    (hk'c : ContinuousOn (k' ζ₀) (Icc (-1) 1))
    (hd : ∀ ζ ∈ ball ζ₀ r, ∀ s ∈ Icc (-1 : ℝ) 1, HasDerivAt (fun ζ => k ζ s) (k' ζ s) ζ)
    (hb : ∀ ζ ∈ ball ζ₀ r, ∀ s ∈ Icc (-1 : ℝ) 1, ‖k' ζ s‖ ≤ C) :
    HasDerivAt (fun ζ => ∫ s in (-1 : ℝ)..1, G s * k ζ s) (∫ s in (-1 : ℝ)..1, G s * k' ζ₀ s) ζ₀ := by
  have hu : uIcc (-1 : ℝ) 1 = Icc (-1) 1 := uIcc_of_le (by norm_num)
  have hI : ∀ s ∈ Ι (-1 : ℝ) 1, s ∈ Icc (-1 : ℝ) 1 := by
    intro s hs
    rw [uIoc_of_le (by norm_num)] at hs
    exact ⟨hs.1.le, hs.2⟩
  have hint : ∀ f : ℝ → ℂ, ContinuousOn f (Icc (-1) 1) →
      IntervalIntegrable (fun s => G s * f s) volume (-1) 1 := fun f hf => by
    apply ContinuousOn.intervalIntegrable
    rw [hu]; exact hG.mul hf
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (a := -1) (b := 1) (F := fun ζ s => G s * k ζ s) (F' := fun ζ s => G s * k' ζ s) (x₀ := ζ₀)
    (bound := fun s => ‖G s‖ * C) (s := ball ζ₀ r) (ball_mem_nhds ζ₀ hr)
    (Filter.eventually_of_mem (ball_mem_nhds ζ₀ hr) fun ζ hζ =>
      ((hint _ (hkc ζ hζ)).def').aestronglyMeasurable)
    (hint _ (hkc ζ₀ (mem_ball_self hr)))
    ((hint _ hk'c).def').aestronglyMeasurable
    (Filter.Eventually.of_forall fun s hs ζ hζ => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hb ζ hζ s (hI s hs)) (norm_nonneg _))
    (by
      apply ContinuousOn.intervalIntegrable
      rw [hu]; exact hG.norm.mul continuousOn_const)
    (Filter.Eventually.of_forall fun s hs ζ hζ => (hd ζ hζ s (hI s hs)).const_mul (G s))
  exact key.2

/-! ### Holomorphy of the cut multiplier on `Ω` -/

/-- **The cut multiplier is holomorphic on `Ω`** for `m ≥ 2`, `x₀ > 1`. -/
theorem differentiableOn_nuCutC {c m x₀ : ℝ} {g : ℝ → ℝ} (hc : 0 < c) (hm : 2 ≤ m) (hx : 1 < x₀)
    (hg : ContinuousOn g (Icc (-1) 1)) : DifferentiableOn ℂ (nuCutC c g m x₀) omegaC := by
  intro ζ₀ hζ₀
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_omegaC ζ₀ hζ₀
  set r := ε / 2 with hr
  have hr0 : 0 < r := by positivity
  have hcl : closedBall ζ₀ r ⊆ omegaC := (closedBall_subset_ball (by linarith)).trans hball
  have hbl : ball ζ₀ r ⊆ omegaC := ball_subset_closedBall.trans hcl
  have hK : IsCompact (Icc (-1 / 2 : ℝ) (1 / 2) ×ˢ closedBall ζ₀ r) := isCompact_Icc.prod (isCompact_closedBall _ _)
  have hKsub : Icc (-1 / 2 : ℝ) (1 / 2) ×ˢ closedBall ζ₀ r ⊆ Icc (-1 / 2 : ℝ) (1 / 2) ×ˢ omegaC :=
    prod_mono subset_rfl hcl
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn ((continuousOn_dmuQξC_pair hc hx).mono hKsub)
  have hGc : ContinuousOn (fun s : ℝ => (g s : ℂ) * eF c (s / m) x₀) (Icc (-1) 1) :=
    (Complex.continuous_ofReal.comp_continuousOn hg).mul (continuous_eF_div c m x₀).continuousOn
  have hD := hasDerivAt_cint_near (G := fun s => (g s : ℂ) * eF c (s / m) x₀)
    (k := fun ζ s => muQξC c (s / m) x₀ ζ) (k' := fun ζ s => dmuQξC c (s / m) x₀ ζ) (C := C) hr0 hGc
    (fun ζ hζ => continuousOn_comp_div (φ := fun y ζ => muQξC c y x₀ ζ) (continuousOn_muQξC_pair hc hx) hm
      (hbl hζ))
    (continuousOn_comp_div (φ := fun y ζ => dmuQξC c y x₀ ζ) (continuousOn_dmuQξC_pair hc hx) hm hζ₀)
    (fun ζ hζ s hs => hasDerivAt_muQξC (qQξC_ne_zero hc hx (abs_le_half_of_mem (div_mem_half hm hs)) (hbl hζ)))
    (fun ζ hζ s hs => hC (s / m, ζ) ⟨div_mem_half hm hs, ball_subset_closedBall hζ⟩)
  exact (hD.const_mul ((1 / m : ℝ) : ℂ)).differentiableAt.differentiableWithinAt

/-- Every iterated derivative of a function holomorphic on an open set is holomorphic there. -/
theorem differentiableOn_iteratedDeriv {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (k : ℕ) : DifferentiableOn ℂ (iteratedDeriv k f) U := by
  induction k with
  | zero => simpa using hf
  | succ k ih => rw [iteratedDeriv_succ]; exact ih.deriv hU

/-- The real trace of the `k`-th derivative has derivative the `(k + 1)`-th. -/
theorem hasDerivAt_iteratedDeriv_ofReal {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (k : ℕ) {η : ℝ} (hη : (η : ℂ) ∈ U) :
    HasDerivAt (fun t : ℝ => iteratedDeriv k f (t : ℂ)) (iteratedDeriv (k + 1) f (η : ℂ)) η := by
  rw [iteratedDeriv_succ]
  exact (((differentiableOn_iteratedDeriv hU hf k).differentiableAt (hU.mem_nhds hη)).hasDerivAt).comp_ofReal

/-! ### The real trace and the split -/

/-- **The real trace**: `ν_C(η) = ν(cη)`. -/
theorem nuCutC_ofReal (c : ℝ) (g : ℝ → ℝ) (m x₀ η : ℝ) : nuCutC c g m x₀ (η : ℂ) = nuCut c g m x₀ (c * η) := by
  unfold nuCutC nuCut
  refine congrArg (_ * ·) ?_
  refine intervalIntegral.integral_congr fun s _ => ?_
  simp only [Cvs.L2a.QIdentityCutPoint.muCut, muQξC_ofReal]
  ring

theorem nuSiC_ofReal (c : ℝ) (g : ℝ → ℝ) (m η : ℝ) :
    nuSiC c g m m (η : ℂ) = nuSi c g m (c * η) := by
  unfold nuSiC nuSi
  refine congrArg (_ * ·) ?_
  refine intervalIntegral.integral_congr fun s _ => ?_
  simp only [Cvs.L2a.CutKernelSimplified.muSi]
  have e : ((c * (s / m) + c * η : ℝ) : ℂ) = (c : ℂ) * (((s / m : ℝ) : ℂ) + (η : ℂ)) := by push_cast; ring
  rw [e]
  ring

/-- **`ν_C = ν_si + ν_co` on `Ω`**. -/
theorem nuCutC_eq_add {c m x₀ : ℝ} {g : ℝ → ℝ} (hc : 0 < c) (hm : 2 ≤ m) (hx : 1 < x₀)
    (hg : ContinuousOn g (Icc (-1) 1)) {ζ : ℂ} (hζ : ζ ∈ omegaC) :
    nuCutC c g m x₀ ζ = nuSiC c g m x₀ ζ + nuCoC c g m x₀ ζ := by
  have hu : uIcc (-1 : ℝ) 1 = Icc (-1) 1 := uIcc_of_le (by norm_num)
  have hGc : ContinuousOn (fun s : ℝ => (g s : ℂ) * eF c (s / m) x₀) (Icc (-1) 1) :=
    (Complex.continuous_ofReal.comp_continuousOn hg).mul (continuous_eF_div c m x₀).continuousOn
  have hpc := continuousOn_pole_s hc hm hζ
  have hmc := continuousOn_comp_div (φ := fun y ζ => muQξC c y x₀ ζ) (continuousOn_muQξC_pair hc hx) hm hζ
  have hhc : ContinuousOn (fun s : ℝ => hcoC c (s / m) x₀ ζ) (Icc (-1) 1) := by
    unfold hcoC; exact hmc.sub hpc
  have iA : IntervalIntegrable (fun s : ℝ => (g s : ℂ) * eF c (s / m) x₀
      * (-I / ((c : ℂ) * (((s / m : ℝ) : ℂ) + ζ)))) volume (-1) 1 := by
    apply ContinuousOn.intervalIntegrable; rw [hu]; exact hGc.mul hpc
  have iB : IntervalIntegrable (fun s : ℝ => (g s : ℂ) * eF c (s / m) x₀ * hcoC c (s / m) x₀ ζ)
      volume (-1) 1 := by
    apply ContinuousOn.intervalIntegrable; rw [hu]; exact hGc.mul hhc
  unfold nuCutC nuSiC nuCoC
  rw [← mul_add, ← intervalIntegral.integral_add iA iB]
  refine congrArg (_ * ·) ?_
  refine intervalIntegral.integral_congr fun s _ => ?_
  simp only [hcoC]
  ring

/-! ### The two bounds -/

/-- **The `co` part**: `|ν_co(ζ)| ≤ ‖g‖₁H/m` when `|h(s/m, ζ)| ≤ H` on `[−1, 1]`. -/
theorem norm_nuCoC_le {c m x₀ H : ℝ} {g : ℝ → ℝ} (hg : ContinuousOn g (Icc (-1) 1)) (hm : 0 < m) {ζ : ℂ}
    (hH : ∀ s ∈ Icc (-1 : ℝ) 1, ‖hcoC c (s / m) x₀ ζ‖ ≤ H) : ‖nuCoC c g m x₀ ζ‖ ≤ gL1 g * H / m := by
  have hu : uIcc (-1 : ℝ) 1 = Icc (-1) 1 := uIcc_of_le (by norm_num)
  have hb : ‖∫ s in (-1 : ℝ)..1, (g s : ℂ) * eF c (s / m) x₀ * hcoC c (s / m) x₀ ζ‖
      ≤ ∫ s in (-1 : ℝ)..1, |g s| * H := by
    refine intervalIntegral.norm_integral_le_of_norm_le (by norm_num) ?_
      (by apply ContinuousOn.intervalIntegrable; rw [hu]; exact hg.abs.mul continuousOn_const)
    refine Filter.Eventually.of_forall fun s hs => ?_
    rw [norm_mul, norm_mul, norm_eF, mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hH s ⟨hs.1.le, hs.2⟩) (abs_nonneg _)
  unfold nuCoC
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity), intervalIntegral.integral_mul_const]
    at *
  unfold gL1
  calc 1 / m * ‖∫ s in (-1 : ℝ)..1, (g s : ℂ) * eF c (s / m) x₀ * hcoC c (s / m) x₀ ζ‖
      ≤ 1 / m * ((∫ s in (-1 : ℝ)..1, |g s|) * H) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = (∫ s in (-1 : ℝ)..1, |g s|) * H / m := by ring

/-- **The `si` part is a Stieltjes transform**: `|ν_si(ζ)| ≤ F/(c(|mζ| − 1))` for `|mζ| > 1`, `|ψ| ≤ F`. -/
theorem norm_nuSiC_le {c m F : ℝ} {g : ℝ → ℝ} (hg : ContinuousOn g (Icc (-1) 1))
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) (hpsi : ∀ t : ℝ, |Cvs.L2a.AngularProlateTailPositive.psi c g t| ≤ F)
    (hc : 0 < c) (hm : 0 < m) {ζ : ℂ} (hζ : 1 < ‖(m : ℂ) * ζ‖) :
    ‖nuSiC c g m m ζ‖ ≤ F / (c * (‖(m : ℂ) * ζ‖ - 1)) := by
  have hmC : (m : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hm.ne'
  have hcC : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc.ne'
  have hS := Cvs.L2a.BernsteinRieszSymbolBounds.norm_integral_stieltjesC_le (g := fun s => (g s : ℂ))
    (Complex.continuous_ofReal.comp_continuousOn hg) hc.ne' (Cvs.L2a.BernsteinRieszSymbolBounds.hF_of_psi hg heven hpsi)
    hζ 1
  have e : nuSiC c g m m ζ = -I / (c : ℂ) * ∫ s in (-1 : ℝ)..1,
      (g s : ℂ) / ((m : ℂ) * ζ + s) * Cvs.L2a.BernsteinRieszSymbolBounds.ek c 1 s := by
    unfold nuSiC
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s _ => ?_
    have he : eF c (s / m) m = Cvs.L2a.BernsteinRieszSymbolBounds.ek c 1 s := by
      unfold eF Cvs.L2a.BernsteinRieszSymbolBounds.ek
      congr 3
      field_simp
    have hd : (c : ℂ) * (((s / m : ℝ) : ℂ) + ζ) = (c / m : ℂ) * ((m : ℂ) * ζ + s) := by
      push_cast; field_simp; ring
    have hX : (m : ℂ) * ζ + s ≠ 0 := by
      intro h0
      have h1 : (m : ℂ) * ζ = -(s : ℂ) := by linear_combination h0
      rw [h1, norm_neg, Complex.norm_real, Real.norm_eq_abs] at hζ
      rw [uIcc_of_le (by norm_num)] at *
      have := abs_le.2 ⟨‹s ∈ Icc (-1 : ℝ) 1›.1, ‹s ∈ Icc (-1 : ℝ) 1›.2⟩
      linarith
    rw [he, hd]
    push_cast
    field_simp
  rw [e, norm_mul, norm_div, norm_neg, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
  have h0 : 0 < ‖(m : ℂ) * ζ‖ - 1 := by linarith
  calc 1 / c * ‖∫ s in (-1 : ℝ)..1, (g s : ℂ) / ((m : ℂ) * ζ + s) * Cvs.L2a.BernsteinRieszSymbolBounds.ek c 1 s‖
      ≤ 1 / c * (F / (‖(m : ℂ) * ζ‖ - 1)) := mul_le_mul_of_nonneg_left hS (by positivity)
    _ = F / (c * (‖(m : ℂ) * ζ‖ - 1)) := by field_simp

/-- **The cut multiplier on the strip**: `|ν_C(ζ)| ≤ (8F/c + 130‖g‖₁/c²)/m` for `c ≥ 11`, `m ≥ 2`. -/
theorem norm_nuCutC_le_strip {c m F : ℝ} {g : ℝ → ℝ} (hg : ContinuousOn g (Icc (-1) 1))
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) (hpsi : ∀ t : ℝ, |Cvs.L2a.AngularProlateTailPositive.psi c g t| ≤ F)
    (hc : 11 ≤ c) (hm : 2 ≤ m) {ζ : ℂ} (hζ : ζ ∈ stripC) :
    ‖nuCutC c g m m ζ‖ ≤ (8 * F / c + 130 * gL1 g / c ^ 2) / m := by
  have hc0 : 0 < c := by linarith
  have hm0 : 0 < m := by linarith
  have hF0 : 0 ≤ F := (abs_nonneg _).trans (hpsi 0)
  have hmz : 5 * m / 8 ≤ ‖(m : ℂ) * ζ‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm0]
    have := Complex.abs_re_le_norm ζ
    nlinarith [hζ.1]
  have hsi := norm_nuSiC_le hg heven hpsi hc0 hm0 (by linarith : 1 < ‖(m : ℂ) * ζ‖)
  have hsi' : F / (c * (‖(m : ℂ) * ζ‖ - 1)) ≤ 8 * F / c / m := by
    rw [div_div, div_le_div_iff₀ (by nlinarith) (by positivity)]
    have : m ≤ 8 * (‖(m : ℂ) * ζ‖ - 1) := by linarith
    nlinarith [mul_le_mul_of_nonneg_left this (mul_nonneg hF0 hc0.le)]
  have hco := norm_nuCoC_le (x₀ := m) (H := 130 / c ^ 2) hg hm0 (ζ := ζ) fun s hs =>
    norm_hcoC_le_strip_130 hc hm (abs_le_half_of_mem (div_mem_half hm hs)) hζ
  rw [nuCutC_eq_add hc0 hm (by linarith) hg (stripC_subset_omegaC hζ)]
  refine (norm_add_le _ _).trans ?_
  have e : (8 * F / c + 130 * gL1 g / c ^ 2) / m = 8 * F / c / m + gL1 g * (130 / c ^ 2) / m := by ring
  rw [e]
  exact add_le_add (hsi.trans hsi') hco

/-! ### The norms -/

/-- **`N_{m,0}` on the collar**: for `m ≥ 2`, `δ ≤ 1/4`, `|η| ≥ 1 − δ`, `c ≥ 80`, an even angular rung has
`|ν(cη)| ≤ (K₀^si + K₀^c)/m`. -/
theorem norm_nuCut_le_collar {g g₁ g₂ : ℝ → ℝ} {c χ : ℝ} (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) (hc : 80 ≤ c) (hχ : 0 ≤ χ) (hχc : χ < c ^ 2)
    {m δ η : ℝ} (hm : 2 ≤ m) (hδ4 : δ ≤ 1 / 4) (hη : 1 - δ ≤ |η|) :
    ‖nuCut c g m m (c * η)‖ ≤ (Cvs.L2a.BandECouplingCollar.K0si c g + K0c c g) / m := by
  have hc0 : 0 < c := by linarith
  have hm0 : 0 < m := by linarith
  have hgc := Cvs.Prolate.CosineChristoffelDarboux.continuousOn_of_hasDerivAt hg
  have hη34 : 3 / 4 ≤ |η| := by linarith
  have hsi := Cvs.L2a.BandRungOutgoingWave.norm_nuSi_le_collar hg hg₁ hg₂c hang heven hc hχ hχc hm hδ4 hη
  have hco := norm_nuCoC_le (c := c) (x₀ := m) (H := 23 / c ^ 2) hgc hm0 (ζ := (η : ℂ)) fun s hs =>
    norm_hcoC_le_real_23 (by linarith) hm (abs_le_half_of_mem (div_mem_half hm hs)) hη34
  rw [← nuCutC_ofReal, nuCutC_eq_add hc0 hm (by linarith) hgc (ofReal_mem_omegaC hη34),
    nuSiC_ofReal c g m η]
  refine (norm_add_le _ _).trans ?_
  have e : (Cvs.L2a.BandECouplingCollar.K0si c g + K0c c g) / m = Cvs.L2a.BandECouplingCollar.K0si c g / m + gL1 g * (23 / c ^ 2) / m := by
    unfold K0c; ring
  rw [e]
  exact add_le_add hsi hco

/-- **Cauchy at radius `1/8`**: `|ν_C^{(k)}(η)| ≤ (K_b/m)k!4^k` at real `|η| ≥ 3/4` for `k ≤ 3`. -/
theorem norm_iteratedDeriv_nuCutC_le {c m F : ℝ} {g : ℝ → ℝ} (hg : ContinuousOn g (Icc (-1) 1))
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) (hpsi : ∀ t : ℝ, |Cvs.L2a.AngularProlateTailPositive.psi c g t| ≤ F)
    (hc : 11 ≤ c) (hm : 2 ≤ m) {k : ℕ} (hk : k ≤ 3) {η : ℝ} (hη : 3 / 4 ≤ |η|) :
    ‖iteratedDeriv k (nuCutC c g m m) (η : ℂ)‖ ≤ KbCut c g F / m * ((k.factorial : ℝ) * 4 ^ k) := by
  have hc0 : 0 < c := by linarith
  have hm0 : 0 < m := by linarith
  have hF0 : 0 ≤ F := (abs_nonneg _).trans (hpsi 0)
  have hball := closedBall_subset_stripC hη
  have hd := (differentiableOn_nuCutC (x₀ := m) hc0 hm (by linarith) hg).diffContOnCl_ball
    (hball.trans stripC_subset_omegaC)
  set Cs := (8 * F / c + 130 * gL1 g / c ^ 2) / m with hCs
  have hC : ∀ z ∈ sphere (η : ℂ) (1 / 8), ‖nuCutC c g m m z‖ ≤ Cs := fun z hz =>
    norm_nuCutC_le_strip hg heven hpsi hc hm (hball (sphere_subset_closedBall hz))
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k (by norm_num) hd hC
  refine h.trans ?_
  have hCs0 : 0 ≤ Cs := by have := gL1_nonneg g; positivity
  have h8 : (1 : ℝ) ≤ 8 * 4 ^ k * (1 / 8) ^ k := by interval_cases k <;> norm_num
  have hKb : KbCut c g F / m = 8 * Cs := by rw [hCs]; unfold KbCut; ring
  rw [hKb, div_le_iff₀ (by positivity)]
  have hf0 : (0 : ℝ) ≤ k.factorial := Nat.cast_nonneg _
  calc (k.factorial : ℝ) * Cs = k.factorial * Cs * 1 := by ring
    _ ≤ k.factorial * Cs * (8 * 4 ^ k * (1 / 8) ^ k) := mul_le_mul_of_nonneg_left h8 (by positivity)
    _ = 8 * Cs * (k.factorial * 4 ^ k) * (1 / 8) ^ k := by ring

/-- `K₀^si ≤ 4F/c ≤ 64F/c` for `c ≥ 12`, from `Λ̂(12/(5c)) ≤ 2`. -/
theorem K0si_le {c F : ℝ} {g : ℝ → ℝ} (hc : 12 ≤ c) (hF : |Cvs.L2a.AngularProlateTailPositive.psi c g 1| ≤ F) :
    Cvs.L2a.BandECouplingCollar.K0si c g ≤ 64 * F / c := by
  have hc0 : 0 < c := by linarith
  have hF0 : 0 ≤ F := (abs_nonneg _).trans hF
  have hw : Cvs.Prolate.BandMassLaw.wUp c (3 / 2) ≤ 1 / 5 := by
    rw [Cvs.L2a.BandECouplingCollar.wUp_three_halves_eq, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hw0 : 0 ≤ Cvs.Prolate.BandMassLaw.wUp c (3 / 2) := by rw [Cvs.L2a.BandECouplingCollar.wUp_three_halves_eq]; positivity
  have hL := Cvs.L2a.BandECouplingCollar.lamHat_le_two hw0 hw
  have hsL : √(Cvs.L2a.BandRungOutgoingWave.lamHat (Cvs.Prolate.BandMassLaw.wUp c (3 / 2))) ≤ √5 := Real.sqrt_le_sqrt (by linarith)
  have h5 : 0 < √5 := by positivity
  have h1 : |Cvs.L2a.AngularProlateTailPositive.psi c g 1| * √(Cvs.L2a.BandRungOutgoingWave.lamHat (Cvs.Prolate.BandMassLaw.wUp c (3 / 2)))
      ≤ F * √5 := mul_le_mul hF hsL (Real.sqrt_nonneg _) hF0
  unfold Cvs.L2a.BandECouplingCollar.K0si
  rw [div_le_div_iff₀ (by positivity) hc0]
  nlinarith [mul_le_mul_of_nonneg_right h1 hc0.le, mul_nonneg (mul_nonneg hF0 h5.le) hc0.le]

theorem Ncut_zero_le {c m F : ℝ} {g : ℝ → ℝ} (hc : 12 ≤ c) (hm : 0 < m)
    (hF : |Cvs.L2a.AngularProlateTailPositive.psi c g 1| ≤ F) : Ncut c g F m 0 ≤ KbCut c g F / m := by
  have hc0 : 0 < c := by linarith
  have h1 := K0si_le hc hF
  have h2 : K0c c g ≤ 1040 * gL1 g / c ^ 2 := by
    unfold K0c; have := gL1_nonneg g; gcongr; norm_num
  simp only [Ncut]
  unfold KbCut
  exact div_le_div_of_nonneg_right (add_le_add h1 h2) hm.le

/-- **The norms in the form of THEOREM E**: `N_{m,i} ≤ (K_b/m)·i!/(1/4)^i` for `i ≤ 3`. -/
theorem Ncut_le_band {c m F : ℝ} {g : ℝ → ℝ} (hc : 12 ≤ c) (hm : 0 < m)
    (hF : |Cvs.L2a.AngularProlateTailPositive.psi c g 1| ≤ F) (i : ℕ) :
    Ncut c g F m i ≤ KbCut c g F / m * ((i.factorial : ℝ) / (1 / 4) ^ i) := by
  have e : (i.factorial : ℝ) / (1 / 4) ^ i = i.factorial * 4 ^ i := by
    rw [one_div, inv_pow, div_inv_eq_mul]
  rw [e]
  rcases Nat.eq_zero_or_pos i with h | h
  · subst h; simpa using Ncut_zero_le hc hm hF
  · simp only [Ncut, ite_eq_right h.ne']; exact le_rfl

/-! ### The cut multiplier is a band multiplier -/

/-- **The cut multiplier is a band multiplier**: for `c ≥ 80`, `m ≥ 2`, `δ ≤ 1/4` and an even angular rung with
`|ψ| ≤ F`, `η ↦ ν_m(cη)` is `C³` on the band region with derivatives the real traces of `ν_C^{(k)}` and norms
`Ncut`. -/
theorem cut_isBandMult {g g₁ g₂ : ℝ → ℝ} {c χ F δ : ℝ} (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) (hc : 80 ≤ c) (hχ : 0 ≤ χ) (hχc : χ < c ^ 2)
    (hpsi : ∀ t : ℝ, |Cvs.L2a.AngularProlateTailPositive.psi c g t| ≤ F) {m : ℕ} (hm : 2 ≤ m) (hδ : δ ≤ 1 / 4) :
    Cvs.L2a.BandTransferBandForm.IsBandMult (fun η => nuCut c g m m (c * η))
      (fun η => iteratedDeriv 1 (nuCutC c g m m) (η : ℂ)) (fun η => iteratedDeriv 2 (nuCutC c g m m) (η : ℂ))
      (fun η => iteratedDeriv 3 (nuCutC c g m m) (η : ℂ)) δ (Cvs.L2a.OrbitGapIntegerM.Ymax m) (Ncut c g F m) := by
  have hc0 : 0 < c := by linarith
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hgc := Cvs.Prolate.CosineChristoffelDarboux.continuousOn_of_hasDerivAt hg
  have hD := differentiableOn_nuCutC (x₀ := m) hc0 hmR (by linarith) hgc
  have hmem : ∀ η ∈ Cvs.L2a.BandTransferBandForm.bandRg δ (Cvs.L2a.OrbitGapIntegerM.Ymax m), 1 - δ ≤ |η| :=
    fun η hη => hη.1
  have hΩ : ∀ η ∈ Cvs.L2a.BandTransferBandForm.bandRg δ (Cvs.L2a.OrbitGapIntegerM.Ymax m), (η : ℂ) ∈ omegaC :=
    fun η hη => ofReal_mem_omegaC (by linarith [hmem η hη])
  have hfun : (fun η : ℝ => nuCut c g m m (c * η)) = fun t : ℝ => iteratedDeriv 0 (nuCutC c g m m) (t : ℂ) := by
    funext t; rw [iteratedDeriv_zero, nuCutC_ofReal]
  have hdk := fun k η hη => hasDerivAt_iteratedDeriv_ofReal isOpen_omegaC hD k (hΩ η hη)
  refine ⟨fun η hη => ?_, fun η hη => hdk 1 η hη, fun η hη => hdk 2 η hη,
    fun η hη => (hdk 3 η hη).continuousAt.continuousWithinAt, fun η hη => ?_⟩
  · rw [hfun]; exact hdk 0 η hη
  have hη34 : 3 / 4 ≤ |η| := by linarith [hmem η hη]
  have hk : ∀ k, 1 ≤ k → k ≤ 3 → ‖iteratedDeriv k (nuCutC c g m m) (η : ℂ)‖ ≤ Ncut c g F m k := by
    intro k hk1 hk3
    simp only [Ncut, ite_eq_right (by omega : k ≠ 0)]
    exact norm_iteratedDeriv_nuCutC_le hgc heven hpsi (by linarith) hmR hk3 hη34
  refine ⟨?_, hk 1 le_rfl (by norm_num), hk 2 (by norm_num) (by norm_num), hk 3 (by norm_num) le_rfl⟩
  simp only [Ncut]
  exact norm_nuCut_le_collar hg hg₁ hg₂c hang heven hc hχ hχc hmR hδ (hmem η hη)

end Cvs.L2a.CutMultiplierBand
