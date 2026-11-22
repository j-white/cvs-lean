import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Cvs.Zeta.ExplicitFormula.HannWindowShifts

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# `d/du` and `1/4 − d²/du²` on the window's test functions, diagonalised by `f̂(s)`
On `𝓓((0, L), ℝ)`, `f̂(s) = ∫₀ᴸ f(u) e^{(s − 1/2)u} du` turns `D = d/du` into multiplication by `1/2 − s` and
`T = 1/4 − D²` into multiplication by `s(1 − s)`. Every `f ↦ f̂(s)` is a nonzero eigenfunctional of `T`, so
every `μ ∈ ℂ` is the eigenvalue of one, while `T` has no eigenvector in `𝓓`. `f̂(1/2 − ξi)` is the window
transform at `ξ`, and `f̂(s̄) = conj f̂(s)`.
-/

noncomputable section

open scoped Distributions
open Set TopologicalSpace MeasureTheory Complex

namespace Cvs.WeilForm.WindowTestOperators

/-! ### The window, its test functions, `D` and `T` -/

/-- The open window `(0, L)`. -/
def win (L : ℝ) : Opens ℝ := ⟨Ioo 0 L, isOpen_Ioo⟩

/-- `D = d/du` on the window's test functions. -/
def opD (L : ℝ) : 𝓓(win L, ℝ) →L[ℝ] 𝓓(win L, ℝ) := LineDeriv.lineDerivOpCLM ℝ 𝓓(win L, ℝ) (1 : ℝ)

/-- `T = 1/4 − d²/du²` on the window's test functions. -/
def opT (L : ℝ) : 𝓓(win L, ℝ) →L[ℝ] 𝓓(win L, ℝ) :=
  (1 / 4 : ℝ) • ContinuousLinearMap.id ℝ _ - (opD L).comp (opD L)

variable {L : ℝ}

theorem differentiable (f : 𝓓(win L, ℝ)) : Differentiable ℝ f :=
  f.contDiff.differentiable (by simp)

theorem continuous_deriv (f : 𝓓(win L, ℝ)) : Continuous (deriv f) :=
  f.contDiff.continuous_deriv (by simp)

theorem opD_apply (f : 𝓓(win L, ℝ)) (u : ℝ) : opD L f u = deriv f u := by
  show (TestFunction.lineDerivCLM ℝ (1 : ℝ) f : 𝓓(win L, ℝ)) u = _
  rw [TestFunction.lineDerivCLM_apply_of_le (by simp), (differentiable f u).lineDeriv_eq_fderiv]
  rfl

theorem coe_opT (f : 𝓓(win L, ℝ)) : ⇑(opT L f) = (1 / 4 : ℝ) • ⇑f - ⇑(opD L (opD L f)) := by
  funext u
  simp [opT]

theorem opT_apply (f : 𝓓(win L, ℝ)) (u : ℝ) : opT L f u = f u / 4 - deriv (deriv f) u := by
  rw [coe_opT, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, opD_apply, show ⇑(opD L f) = deriv f from
    funext (opD_apply f)]
  ring

/-- A test function on the window vanishes at `0`. -/
theorem apply_zero (f : 𝓓(win L, ℝ)) : f 0 = 0 :=
  image_eq_zero_of_notMem_tsupport fun h => by simpa [win] using f.tsupport_subset h

/-- A test function on the window vanishes at `L`. -/
theorem apply_L (f : 𝓓(win L, ℝ)) : f L = 0 :=
  image_eq_zero_of_notMem_tsupport fun h => by simpa [win] using f.tsupport_subset h

/-! ### The transform -/

/-- The transform `f̂(s) = ∫₀ᴸ f(u) e^{(s − 1/2)u} du`. -/
def hat (L : ℝ) (f : ℝ → ℝ) (s : ℂ) : ℂ := ∫ u in (0 : ℝ)..L, (f u : ℂ) * cexp ((s - 1 / 2) * u)

theorem hasDerivAt_cexp_mul (c : ℂ) (u : ℝ) :
    HasDerivAt (fun t : ℝ => cexp (c * t)) (c * cexp (c * u)) u := by
  have h := (((hasDerivAt_id' (u : ℂ)).const_mul c).cexp).comp_ofReal
  convert h using 1
  ring

theorem intervalIntegrable_mul_cexp {f : ℝ → ℝ} (hf : Continuous f) (c : ℂ) (a b : ℝ) :
    IntervalIntegrable (fun u : ℝ => (f u : ℂ) * cexp (c * u)) volume a b := by
  apply Continuous.intervalIntegrable
  fun_prop

theorem hat_add {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) (s : ℂ) :
    hat L (f + g) s = hat L f s + hat L g s := by
  unfold hat
  rw [← intervalIntegral.integral_add (intervalIntegrable_mul_cexp hf _ _ _)
    (intervalIntegrable_mul_cexp hg _ _ _)]
  refine intervalIntegral.integral_congr fun u _ => ?_
  simp only [Pi.add_apply]
  push_cast
  ring

theorem hat_sub {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) (s : ℂ) :
    hat L (f - g) s = hat L f s - hat L g s := by
  unfold hat
  rw [← intervalIntegral.integral_sub (intervalIntegrable_mul_cexp hf _ _ _)
    (intervalIntegrable_mul_cexp hg _ _ _)]
  refine intervalIntegral.integral_congr fun u _ => ?_
  simp only [Pi.sub_apply]
  push_cast
  ring

theorem hat_smul (a : ℝ) (f : ℝ → ℝ) (s : ℂ) : hat L (a • f) s = a * hat L f s := by
  unfold hat
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun u _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

/-- **`D` acts on `f̂` as multiplication by `1/2 − s`.** -/
theorem hat_opD (f : 𝓓(win L, ℝ)) (s : ℂ) : hat L (opD L f) s = (1 / 2 - s) * hat L f s := by
  set c : ℂ := s - 1 / 2 with hc
  have hu : ∀ x ∈ uIcc 0 L, HasDerivAt (fun t : ℝ => (f t : ℂ)) ((deriv f x : ℝ) : ℂ) x :=
    fun x _ => ((differentiable f x).hasDerivAt).ofReal_comp
  have hv : ∀ x ∈ uIcc 0 L, HasDerivAt (fun t : ℝ => cexp (c * t)) (c * cexp (c * x)) x :=
    fun x _ => hasDerivAt_cexp_mul c x
  have hu' : IntervalIntegrable (fun x : ℝ => ((deriv f x : ℝ) : ℂ)) volume 0 L :=
    (continuous_ofReal.comp (continuous_deriv f)).intervalIntegrable _ _
  have hv' : IntervalIntegrable (fun x : ℝ => c * cexp (c * x)) volume 0 L := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
  rw [apply_zero, apply_L] at hibp
  simp only [ofReal_zero, zero_mul, sub_zero, zero_sub] at hibp
  have hmul : (∫ x in (0 : ℝ)..L, (f x : ℂ) * (c * cexp (c * x)))
      = c * ∫ x in (0 : ℝ)..L, (f x : ℂ) * cexp (c * x) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun u _ => ?_
    ring
  have hD : hat L (opD L f) s = ∫ x in (0 : ℝ)..L, ((deriv f x : ℝ) : ℂ) * cexp (c * x) := by
    unfold hat
    refine intervalIntegral.integral_congr fun u _ => ?_
    simp only [opD_apply, hc]
  have h0 : hat L f s = ∫ x in (0 : ℝ)..L, (f x : ℂ) * cexp (c * x) := rfl
  rw [hD, h0]
  rw [hmul, hc] at hibp
  linear_combination hibp

/-- **`T = 1/4 − D²` acts on `f̂` as multiplication by `s(1 − s)`.** -/
theorem hat_opT (f : 𝓓(win L, ℝ)) (s : ℂ) : hat L (opT L f) s = s * (1 - s) * hat L f s := by
  rw [coe_opT, hat_sub (f.continuous.const_smul _) (opD L (opD L f)).continuous, hat_smul, hat_opD,
    hat_opD]
  push_cast
  ring

/-! ### The evaluations as eigenfunctionals -/

/-- The evaluation `f ↦ f̂(s)` on the window's test functions. -/
def ev (L : ℝ) (s : ℂ) : 𝓓(win L, ℝ) →ₗ[ℝ] ℂ where
  toFun f := hat L f s
  map_add' f g := hat_add f.continuous g.continuous s
  map_smul' a f := by
    show hat L (a • ⇑f) s = _
    rw [hat_smul]
    rfl

theorem ev_apply (s : ℂ) (f : 𝓓(win L, ℝ)) : ev L s f = hat L f s := rfl

/-- **Every evaluation is an eigenfunctional of `D`**: `f̂ ∘ D = (1/2 − s) f̂`. -/
theorem ev_comp_opD (s : ℂ) : (ev L s).comp (opD L).toLinearMap = (1 / 2 - s) • ev L s :=
  LinearMap.ext fun f => by
    rw [LinearMap.comp_apply, LinearMap.smul_apply, ContinuousLinearMap.coe_coe, ev_apply, ev_apply,
      hat_opD, smul_eq_mul]

/-- **Every evaluation is an eigenfunctional of `T`, with eigenvalue `s(1 − s)`.** -/
theorem ev_comp_opT (s : ℂ) : (ev L s).comp (opT L).toLinearMap = (s * (1 - s)) • ev L s :=
  LinearMap.ext fun f => by
    rw [LinearMap.comp_apply, LinearMap.smul_apply, ContinuousLinearMap.coe_coe, ev_apply, ev_apply,
      hat_opT, smul_eq_mul]

/-! ### The window transform and conjugation -/

/-- `f̂(1/2 − ξi)` is the window transform of `f` at `ξ`. -/
theorem windowTransform_eq_hat (f : ℝ → ℝ) (ξ : ℂ) :
    Cvs.Detection.windowTransform L (fun u => (f u : ℂ)) ξ = hat L f (1 / 2 - ξ * I) := by
  unfold Cvs.Detection.windowTransform hat
  refine intervalIntegral.integral_congr fun u _ => ?_
  simp only
  rw [mul_comm]
  congr 2
  ring

/-- `f̂(s̄) = conj f̂(s)` for a real `f`. -/
theorem hat_conj (f : ℝ → ℝ) (s : ℂ) : hat L f ((starRingEnd ℂ) s) = (starRingEnd ℂ) (hat L f s) := by
  unfold hat
  have hc : ∀ g : ℝ → ℂ, (starRingEnd ℂ) (∫ u in (0 : ℝ)..L, g u) = ∫ u in (0 : ℝ)..L, (starRingEnd ℂ) (g u) := by
    intro g
    rw [intervalIntegral, intervalIntegral, map_sub, ← integral_conj, ← integral_conj]
  rw [hc]
  refine intervalIntegral.integral_congr fun u _ => ?_
  simp only [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_sub, map_div₀, map_one, map_ofNat]

/-! ### Every complex number is an eigenvalue of a nonzero eigenfunctional -/

/-- **Every evaluation is nonzero**: for `0 < L` and every `s ∈ ℂ` some test function has `f̂(s) ≠ 0`. -/
theorem ev_ne_zero (hL : 0 < L) (s : ℂ) : ev L s ≠ 0 := by
  set c : ℂ := s - 1 / 2 with hc
  set r : ℝ := min (L / 4) (1 / (4 * (‖c‖ + 1))) with hr
  have hr0 : 0 < r := lt_min (by linarith) (by positivity)
  have hrL : r ≤ L / 4 := min_le_left _ _
  have hrc : ‖c‖ * r ≤ 1 / 4 := by
    have h1 : r * (4 * (‖c‖ + 1)) ≤ 1 := by
      have h2 : r ≤ 1 / (4 * (‖c‖ + 1)) := min_le_right _ _
      calc r * (4 * (‖c‖ + 1)) ≤ 1 / (4 * (‖c‖ + 1)) * (4 * (‖c‖ + 1)) := by gcongr
        _ = 1 := by field_simp
    nlinarith [norm_nonneg c]
  let φ : ContDiffBump (L / 2 : ℝ) := ⟨r / 2, r, by positivity, by linarith⟩
  have hball : ∀ u, φ u ≠ 0 → |u - L / 2| < r := fun u hu => by
    have h := φ.support_eq ▸ (Function.mem_support.2 hu)
    rwa [Metric.mem_ball, Real.dist_eq] at h
  have hts : tsupport φ ⊆ Ioo 0 L := by
    rw [φ.tsupport_eq]
    intro u hu
    rw [Metric.mem_closedBall, Real.dist_eq, abs_le] at hu
    exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
  let f : 𝓓(win L, ℝ) := ⟨φ, φ.contDiff, φ.hasCompactSupport, hts⟩
  intro h0
  have hf : hat L f s = 0 := by
    have := LinearMap.congr_fun h0 f
    rwa [ev_apply, LinearMap.zero_apply] at this
  set e : ℝ → ℂ := fun u => cexp (c * ((u : ℂ) - L / 2)) with he
  have hsplit : hat L f s = cexp (c * (L / 2)) * ∫ u in (0 : ℝ)..L, (φ u : ℂ) * e u := by
    unfold hat
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun u _ => ?_
    simp only [he]
    rw [show (s - 1 / 2) * (u : ℂ) = c * (L / 2) + c * ((u : ℂ) - L / 2) by rw [hc]; ring,
      Complex.exp_add]
    show (φ u : ℂ) * _ = _
    ring
  have hI : (∫ u in (0 : ℝ)..L, (φ u : ℂ) * e u) = 0 := by
    rw [hsplit] at hf
    exact (mul_eq_zero.1 hf).resolve_left (Complex.exp_ne_zero _)
  have hφ0 : ∀ u, 0 ≤ φ u := fun u => φ.nonneg' u
  have hφc : Continuous φ := φ.continuous
  have hec : Continuous e := by simp only [he]; fun_prop
  set A : ℝ := ∫ u in (0 : ℝ)..L, φ u with hA
  have hApos : 0 < A := by
    rw [hA, intervalIntegral.integral_of_le hL.le, setIntegral_eq_integral_of_forall_compl_eq_zero]
    · exact φ.integral_pos
    · intro u hu
      by_contra hne
      have := abs_lt.1 (hball u hne)
      exact hu ⟨by linarith [this.1], by linarith [this.2]⟩
  have hpt : ∀ u ∈ Icc 0 L, ‖(φ u : ℂ) * (1 - e u)‖ ≤ φ u * (1 / 2) := by
    intro u _
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hφ0 u)]
    by_cases hu : φ u = 0
    · rw [hu]; simp
    · refine mul_le_mul_of_nonneg_left ?_ (hφ0 u)
      have hw : ‖c * ((u : ℂ) - L / 2)‖ ≤ 1 / 4 := by
        rw [norm_mul, show ((u : ℂ) - L / 2) = ((u - L / 2 : ℝ) : ℂ) by push_cast; ring,
          Complex.norm_real, Real.norm_eq_abs]
        calc ‖c‖ * |u - L / 2| ≤ ‖c‖ * r := mul_le_mul_of_nonneg_left (hball u hu).le (norm_nonneg c)
          _ ≤ 1 / 4 := hrc
      rw [norm_sub_rev]
      calc ‖e u - 1‖ ≤ 2 * ‖c * ((u : ℂ) - L / 2)‖ := Complex.norm_exp_sub_one_le (by linarith)
        _ ≤ 1 / 2 := by linarith
  have hbound : ‖(A : ℂ) - ∫ u in (0 : ℝ)..L, (φ u : ℂ) * e u‖ ≤ A / 2 := by
    have h1 : (A : ℂ) - ∫ u in (0 : ℝ)..L, (φ u : ℂ) * e u
        = ∫ u in (0 : ℝ)..L, (φ u : ℂ) * (1 - e u) := by
      rw [hA, ← intervalIntegral.integral_ofReal, ← intervalIntegral.integral_sub]
      · refine intervalIntegral.integral_congr fun u _ => ?_
        ring
      · exact (continuous_ofReal.comp hφc).intervalIntegrable _ _
      · exact ((continuous_ofReal.comp hφc).mul hec).intervalIntegrable _ _
    rw [h1]
    refine (intervalIntegral.norm_integral_le_integral_norm hL.le).trans ?_
    calc (∫ u in (0 : ℝ)..L, ‖(φ u : ℂ) * (1 - e u)‖) ≤ ∫ u in (0 : ℝ)..L, φ u * (1 / 2) := by
          refine intervalIntegral.integral_mono_on hL.le ?_ ?_ hpt
          · exact (((continuous_ofReal.comp hφc).mul (continuous_const.sub hec)).norm).intervalIntegrable _ _
          · exact (hφc.mul continuous_const).intervalIntegrable _ _
      _ = A / 2 := by rw [intervalIntegral.integral_mul_const, hA]; ring
  rw [hI, sub_zero, Complex.norm_real, Real.norm_of_nonneg hApos.le] at hbound
  linarith

/-- **Every `μ ∈ ℂ` is the eigenvalue of a nonzero eigenfunctional of `T`**: `μ = s(1 − s)` for some `s ∈ ℂ`,
and `f ↦ f̂(s)` is nonzero with `f̂ ∘ T = μ f̂`. -/
theorem exists_eigenfunctional (hL : 0 < L) (μ : ℂ) :
    ∃ ℓ : 𝓓(win L, ℝ) →ₗ[ℝ] ℂ, ℓ ≠ 0 ∧ ℓ.comp (opT L).toLinearMap = μ • ℓ := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_eq_mul_self (1 - 4 * μ)
  refine ⟨ev L ((1 + z) / 2), ev_ne_zero hL _, ?_⟩
  rw [ev_comp_opT]
  congr 1
  linear_combination (1 / 4 : ℂ) * hz

/-! ### `T` has no eigenvector among the test functions -/

theorem deriv_apply_zero (f : 𝓓(win L, ℝ)) : deriv f 0 = 0 := by
  rw [← opD_apply]
  exact apply_zero _

/-- **`T` has no eigenvector in `𝓓((0, L), ℝ)`**: `T f = μ f` forces `f = 0`. -/
theorem eq_zero_of_opT_eq_smul {f : 𝓓(win L, ℝ)} {μ : ℝ} (h : opT L f = μ • f) : f = 0 := by
  have h2 : ∀ u, deriv (deriv f) u = (1 / 4 - μ) * f u := by
    intro u
    have hu := congrArg (fun g : 𝓓(win L, ℝ) => g u) h
    rw [opT_apply] at hu
    have : (μ • f) u = μ * f u := rfl
    rw [this] at hu
    linarith
  have hd' : Differentiable ℝ (deriv f) := by
    rw [show deriv ⇑f = ⇑(opD L f) from funext fun u => (opD_apply f u).symm]
    exact differentiable _
  obtain ⟨κ, hκ⟩ := IsAlgClosed.exists_eq_mul_self (((1 / 4 - μ : ℝ)) : ℂ)
  have hF : ∀ u, HasDerivAt (fun t : ℝ => (f t : ℂ)) ((deriv f u : ℝ) : ℂ) u :=
    fun u => ((differentiable f u).hasDerivAt).ofReal_comp
  have hF' : ∀ u, HasDerivAt (fun t : ℝ => ((deriv f t : ℝ) : ℂ)) ((deriv (deriv f) u : ℝ) : ℂ) u :=
    fun u => ((hd' u).hasDerivAt).ofReal_comp
  -- `g = F' − κF` solves `g' = −κ g` and vanishes at `0`
  set g : ℝ → ℂ := fun t => ((deriv f t : ℝ) : ℂ) - κ * (f t : ℂ) with hg
  have hgd : ∀ u, HasDerivAt g (-κ * g u) u := fun u => by
    refine ((hF' u).sub ((hF u).const_mul κ)).congr_deriv ?_
    have hκ' : (1 / 4 - (μ : ℂ)) = κ * κ := by rw [← hκ]; push_cast; ring
    rw [h2 u, hg]
    push_cast
    linear_combination ((f u : ℝ) : ℂ) * hκ'
  have hG : ∀ u, HasDerivAt (fun t => g t * cexp (κ * t)) 0 u := fun u => by
    refine ((hgd u).mul (hasDerivAt_cexp_mul κ u)).congr_deriv ?_
    ring
  have hg0 : ∀ u, g u = 0 := fun u => by
    have hc := is_const_of_deriv_eq_zero (fun t => (hG t).differentiableAt)
      (fun t => (hG t).deriv) u 0
    simp only [hg, deriv_apply_zero, apply_zero, ofReal_zero, mul_zero, sub_zero, ofReal_zero,
      zero_mul] at hc
    exact (mul_eq_zero.1 hc).resolve_right (Complex.exp_ne_zero _)
  -- then `F e^{−κu}` is constant, and `F(0) = 0`
  have hH : ∀ u, HasDerivAt (fun t => (f t : ℂ) * cexp (-κ * t)) 0 u := fun u => by
    refine ((hF u).mul (hasDerivAt_cexp_mul (-κ) u)).congr_deriv ?_
    have := hg0 u
    simp only [hg] at this
    linear_combination (cexp (-κ * u)) * this
  ext u
  have hc := is_const_of_deriv_eq_zero (fun t => (hH t).differentiableAt) (fun t => (hH t).deriv) u 0
  simp only [apply_zero, ofReal_zero, zero_mul] at hc
  have := (mul_eq_zero.1 hc).resolve_right (Complex.exp_ne_zero _)
  exact_mod_cast this

/-- **`T` has no eigenvalue on `𝓓((0, L), ℝ)`.** -/
theorem not_hasEigenvalue_opT (μ : ℝ) : ¬ Module.End.HasEigenvalue (opT L).toLinearMap μ := fun hμ => by
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  exact hv.2 (eq_zero_of_opT_eq_smul hv.apply_eq_smul)

end Cvs.WeilForm.WindowTestOperators
