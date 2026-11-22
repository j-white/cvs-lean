import Mathlib
import Cvs.StepA.Edge.WindowCoshTransformDuality
import Cvs.Upstream.ExpSumBlaschkeProduct
import Cvs.Upstream.ExpSumContourInterpolation
import Cvs.Upstream.ExpSumTwoEndedError
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.Zeta.RectArgument

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The window class of an exponential sum, and the transplant on a rectangle

With `L = log x`, `T = L/2` and `g = Re h_a`, the window class `v(s) = g(T − |s − T|)` on `(0, L]` has
`F_v(w) = (e^{wT}Ψ(w) + conj(e^{w̄T}Ψ(w̄)))/2`, `Ψ = L_a + err`, and `‖v‖² ≤ 2 Re G(a)` (caseinf-attack Theorem 4
(e)). With Cvs.Upstream.ExpSumContourInterpolation this gives `Transplant` for any conjugation-closed finite set inside a rectangle on whose boundary
the Blaschke product is bounded below.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology Finset
open scoped Interval ComplexConjugate InnerProductSpace
open Cvs.Upstream.ExpSumBlaschkeProduct (lap gram blaschke)
open Cvs.Upstream.ExpSumTwoEndedError (err shift expSum rint)
open Cvs.Upstream.ExpSumContourInterpolation (OnBd Inside)
open Cvs.Zeta (closedRect)

namespace Cvs.StepA.Edge.ExpSumWindowTransplant
open Cvs.ZeroCounting

set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The window class -/

/-- The profile `s ↦ Re h_a(T − |s − T|)` on `(0, L]`, `T = L/2`. -/
def prof (p a : ι → ℂ) (L : ℝ) (s : ℝ) : ℝ :=
  (Ioc 0 L).indicator (fun s => (expSum p a (L / 2 - |s - L / 2|)).re) s

theorem continuous_core (p a : ι → ℂ) (L : ℝ) :
    Continuous fun s : ℝ => (expSum p a (L / 2 - |s - L / 2|)).re :=
  Complex.continuous_re.comp ((Cvs.Upstream.ExpSumTwoEndedError.continuous_expSum p a).comp (by fun_prop))

theorem memLp_prof (p a : ι → ℂ) (L : ℝ) : MemLp (prof p a L) 2 (volume : Measure ℝ) := by
  have hc := continuous_core p a L
  have hm : AEStronglyMeasurable (prof p a L) volume :=
    (hc.aestronglyMeasurable.indicator measurableSet_Ioc)
  refine (memLp_two_iff_integrable_sq hm).2 ?_
  have h : (fun s => prof p a L s ^ 2)
      = (Ioc 0 L).indicator (fun s => ((expSum p a (L / 2 - |s - L / 2|)).re) ^ 2) := by
    funext s
    unfold prof
    by_cases hs : s ∈ Ioc 0 L <;> simp [hs]
  rw [h, integrable_indicator_iff measurableSet_Ioc]
  exact ((hc.pow 2).integrableOn_Icc).mono_set Ioc_subset_Icc_self

/-- The window class of `h_a`. -/
def winVec (x : ℕ) (p a : ι → ℂ) : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x) :=
  ⟨(memLp_prof p a (Real.log x)).toLp _, by
    filter_upwards [(memLp_prof p a (Real.log x)).coeFn_toLp] with s hs hsn
    rw [hs]; unfold prof; simp [hsn]⟩

theorem coe_winVec_ae (x : ℕ) (p a : ι → ℂ) :
    (((winVec x p a : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)) : Lp ℝ 2 (volume : Measure ℝ)) : ℝ → ℝ)
      =ᵐ[volume] prof p a (Real.log x) :=
  (memLp_prof p a (Real.log x)).coeFn_toLp

/-- `‖v‖² = ∫ prof²`. -/
theorem norm_sq_winVec (x : ℕ) (p a : ι → ℂ) :
    ‖winVec x p a‖ ^ 2 = ∫ s, prof p a (Real.log x) s ^ 2 := by
  have h1 : ‖winVec x p a‖ ^ 2
      = ⟪((winVec x p a : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)) : Lp ℝ 2 (volume : Measure ℝ)),
          ((winVec x p a : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)) : Lp ℝ 2 (volume : Measure ℝ))⟫_ℝ := by
    rw [real_inner_self_eq_norm_sq]; rfl
  rw [h1, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coe_winVec_ae x p a] with s hs
  rw [hs]; simp [pow_two]

/-- **The norm of the window class**: `‖v‖² ≤ 2 Re G(a)`. -/
theorem norm_sq_winVec_le {p : ι → ℂ} {ε : ℝ} (hε0 : 0 < ε) (hε : ∀ i, ε ≤ (p i).re) (x : ℕ) (a : ι → ℂ) :
    ‖winVec x p a‖ ^ 2 ≤ 2 * (gram p a).re := by
  set L := Real.log x with hLdef
  have hL : 0 ≤ L := Real.log_natCast_nonneg x
  set T := L / 2 with hT
  have hT0 : 0 ≤ T := by positivity
  set g : ℝ → ℝ := fun u => (expSum p a u).re with hg
  have hgc : Continuous g := Complex.continuous_re.comp (Cvs.Upstream.ExpSumTwoEndedError.continuous_expSum p a)
  have hGc := continuous_core p a L
  rw [norm_sq_winVec]
  have h1 : ∫ s, prof p a L s ^ 2 = ∫ s in (0 : ℝ)..L, (g (T - |s - T|)) ^ 2 := by
    rw [intervalIntegral.integral_of_le hL, ← integral_indicator measurableSet_Ioc]
    congr 1; funext s
    unfold prof
    by_cases hs : s ∈ Ioc 0 L <;> simp [hs, hg, hT]
  have hsplit : ∫ s in (0 : ℝ)..L, (g (T - |s - T|)) ^ 2
      = (∫ s in (0 : ℝ)..T, (g (T - |s - T|)) ^ 2) + ∫ s in T..L, (g (T - |s - T|)) ^ 2 :=
    (intervalIntegral.integral_add_adjacent_intervals ((hGc.pow 2).intervalIntegrable _ _)
      ((hGc.pow 2).intervalIntegrable _ _)).symm
  have hA : ∫ s in (0 : ℝ)..T, (g (T - |s - T|)) ^ 2 = ∫ s in (0 : ℝ)..T, (g s) ^ 2 := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [Set.uIcc_of_le hT0] at hs
    rw [abs_of_nonpos (by linarith [hs.2]), show T - -(s - T) = s by ring]
  have hB : ∫ s in T..L, (g (T - |s - T|)) ^ 2 = ∫ s in (0 : ℝ)..T, (g s) ^ 2 := by
    have e1 : ∫ s in T..L, (g (T - |s - T|)) ^ 2 = ∫ s in T..L, (g (L - s)) ^ 2 := by
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [Set.uIcc_of_le (by linarith)] at hs
      rw [abs_of_nonneg (by linarith [hs.1]), show T - (s - T) = L - s by rw [hT]; ring]
    rw [e1, intervalIntegral.integral_comp_sub_left (fun u => (g u) ^ 2) L, sub_self,
      show L - T = T by rw [hT]; ring]
  have hle : ∫ s in (0 : ℝ)..T, (g s) ^ 2 ≤ (gram p a).re := by
    refine le_trans (intervalIntegral.integral_mono_on hT0 ((hgc.pow 2).intervalIntegrable _ _)
      (((Cvs.Upstream.ExpSumTwoEndedError.continuous_expSum p a).norm.pow 2).intervalIntegrable _ _) fun u _ => ?_)
      (Cvs.Upstream.ExpSumTwoEndedError.integral_norm_sq_expSum_le hε0 hε a T)
    have := Complex.re_sq_le_normSq (expSum p a u)
    rw [Complex.normSq_eq_norm_sq] at this
    show g u ^ 2 ≤ ‖expSum p a u‖ ^ 2
    simp only [hg]; nlinarith
  rw [h1, hsplit, hA, hB]
  linarith

/-! ### The cosh transform of the window class -/

/-- `∫_0^T h_a(u)(e^{w(T−u)} + e^{−w(T−u)}) du = e^{wT}(L_a(w) + err(w))`. -/
theorem integral_expSum_mul_cosh (p a : ι → ℂ) {w : ℂ} (hw : ∀ i, w + conj (p i) ≠ 0) (T : ℝ) :
    ∫ u in (0 : ℝ)..T, expSum p a u * (cexp (w * (T - u)) + cexp (-(w * (T - u))))
      = cexp (w * T) * (lap p a w + err p T a w) := by
  have e : (fun u : ℝ => expSum p a u * (cexp (w * (T - u)) + cexp (-(w * (T - u)))))
      = fun u : ℝ => cexp (w * T) * (expSum p a u * cexp (-w * u))
          + cexp (-(w * T)) * (expSum p a u * cexp (w * u)) := by
    funext u
    have h1 : cexp (w * (T - u)) = cexp (w * T) * cexp (-w * u) := by
      rw [← Complex.exp_add]; congr 1; ring
    have h2 : cexp (-(w * (T - u))) = cexp (-(w * T)) * cexp (w * u) := by
      rw [← Complex.exp_add]; congr 1; ring
    rw [h1, h2]; ring
  have hc1 : Continuous fun u : ℝ => expSum p a u * cexp (-w * u) := by
    have := Cvs.Upstream.ExpSumTwoEndedError.continuous_expSum p a; fun_prop
  have hc2 : Continuous fun u : ℝ => expSum p a u * cexp (w * u) := by
    have := Cvs.Upstream.ExpSumTwoEndedError.continuous_expSum p a; fun_prop
  rw [e, intervalIntegral.integral_add ((hc1.intervalIntegrable _ _).const_mul _)
      ((hc2.intervalIntegrable _ _).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    Cvs.Upstream.ExpSumTwoEndedError.integral_expSum_mul_exp_neg p a hw T, Cvs.Upstream.ExpSumTwoEndedError.integral_expSum_mul_exp]
  unfold err
  have hE : cexp (w * T) * cexp (-(w * T)) = 1 := by rw [← Complex.exp_add]; simp
  have hE2 : cexp (w * T) * cexp (-(2 * w * T)) = cexp (-(w * T)) := by
    rw [← Complex.exp_add]; congr 1; ring
  linear_combination (-(∑ i, a i * rint (w - conj (p i)) T)) * hE2

/-- The conjugate half: `∫_0^T conj h_a(u)(e^{w(T−u)} + e^{−w(T−u)}) du = conj(e^{w̄T}(L_a + err)(w̄))`. -/
theorem integral_conj_expSum_mul_cosh (p a : ι → ℂ) {w : ℂ} (hw : ∀ i, conj w + conj (p i) ≠ 0) {T : ℝ}
    (hT : 0 ≤ T) :
    ∫ u in (0 : ℝ)..T, conj (expSum p a u) * (cexp (w * (T - u)) + cexp (-(w * (T - u))))
      = conj (cexp (conj w * T) * (lap p a (conj w) + err p T a (conj w))) := by
  rw [← integral_expSum_mul_cosh p a hw T, intervalIntegral.integral_of_le hT,
    intervalIntegral.integral_of_le hT, ← integral_conj]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [map_mul, map_add, Complex.conj_conj, ← Complex.exp_conj, map_neg, map_sub,
    Complex.conj_ofReal]

/-- **The cosh transform of the window class**: `F_v(w) = (e^{wT}Ψ(w) + conj(e^{w̄T}Ψ(w̄)))/2`,
`Ψ = L_a + err`, `T = log x/2`. -/
theorem coshT_winVec (x : ℕ) (p a : ι → ℂ) {w : ℂ} (hw : ∀ i, w + conj (p i) ≠ 0)
    (hw' : ∀ i, conj w + conj (p i) ≠ 0) :
    Cvs.StepA.Edge.WindowCoshTransformDuality.coshT x (winVec x p a) w
      = (cexp (w * (Real.log x / 2 : ℝ)) * (lap p a w + err p (Real.log x / 2) a w)
        + conj (cexp (conj w * (Real.log x / 2 : ℝ))
          * (lap p a (conj w) + err p (Real.log x / 2) a (conj w)))) / 2 := by
  set L := Real.log x with hLdef
  have hL : 0 ≤ L := Real.log_natCast_nonneg x
  set T := L / 2 with hT
  have hT0 : 0 ≤ T := by positivity
  set g : ℝ → ℝ := fun u => (expSum p a u).re with hg
  have hgc : Continuous g := Complex.continuous_re.comp (Cvs.Upstream.ExpSumTwoEndedError.continuous_expSum p a)
  -- the representative
  have hrep : Cvs.StepA.Edge.WindowCoshTransformDuality.rep x (winVec x p a) =ᵐ[volume] fun t => prof p a L (t + T) := by
    have h := (coe_winVec_ae x p a).comp_tendsto
      (measurePreserving_add_right (volume : Measure ℝ) T).quasiMeasurePreserving.tendsto_ae
    exact h
  set φ : ℝ → ℂ := fun t => ((g (T - |t|) : ℝ) : ℂ) * Complex.cosh (w * t) with hφ
  have hφc : Continuous φ := by
    simp only [hφ]
    exact (Complex.continuous_ofReal.comp (hgc.comp (by fun_prop))).mul (by fun_prop)
  have h1 : Cvs.StepA.Edge.WindowCoshTransformDuality.coshT x (winVec x p a) w = ∫ t in -T..T, φ t := by
    unfold Cvs.StepA.Edge.WindowCoshTransformDuality.coshT
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hrep] with t ht htI
    rw [Set.uIoc_of_le (by linarith)] at htI
    rw [ht]
    simp only [hφ, prof]
    have htI' : -T < t ∧ t ≤ T := htI
    have hmem : t + T ∈ Ioc 0 L := ⟨by linarith [htI'.1], by rw [hT] at htI' ⊢; linarith [htI'.2]⟩
    rw [Set.indicator_of_mem hmem]
    have e : t + T - L / 2 = t := by rw [hT]; ring
    rw [e]
  have h2 : ∫ t in -T..T, φ t = 2 * ∫ t in (0 : ℝ)..T, φ t := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0) (hφc.intervalIntegrable _ _)
      (hφc.intervalIntegrable _ _)]
    have hneg : ∫ t in -T..0, φ t = ∫ t in (0 : ℝ)..T, φ t := by
      have := intervalIntegral.integral_comp_neg (a := 0) (b := T) φ
      rw [neg_zero] at this
      rw [← this]
      refine intervalIntegral.integral_congr fun t _ => ?_
      simp only [hφ, abs_neg]
      rw [Complex.ofReal_neg, mul_neg, Complex.cosh_neg]
    rw [hneg]; ring
  set ψ : ℝ → ℂ := fun u => ((g u : ℝ) : ℂ) * Complex.cosh (w * (T - u)) with hψ
  have h3 : ∫ t in (0 : ℝ)..T, φ t = ∫ u in (0 : ℝ)..T, ψ u := by
    have := intervalIntegral.integral_comp_sub_left (a := 0) (b := T) ψ T
    rw [sub_self, sub_zero] at this
    rw [← this]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le hT0] at ht
    simp only [hφ, hψ, abs_of_nonneg ht.1]
    congr 2
    push_cast; ring
  have h4 : (fun u : ℝ => 2 * ψ u) = fun u : ℝ => (expSum p a u * (cexp (w * (T - u)) + cexp (-(w * (T - u))))
      + conj (expSum p a u) * (cexp (w * (T - u)) + cexp (-(w * (T - u))))) / 2 := by
    funext u
    simp only [hψ, hg]
    rw [Complex.re_eq_add_conj, ← Complex.two_cosh]
    ring
  have hc5 : Continuous fun u : ℝ => expSum p a u * (cexp (w * (T - u)) + cexp (-(w * (T - u)))) := by
    have := Cvs.Upstream.ExpSumTwoEndedError.continuous_expSum p a; fun_prop
  have hc6 : Continuous fun u : ℝ => conj (expSum p a u) * (cexp (w * (T - u)) + cexp (-(w * (T - u)))) := by
    have := Cvs.Upstream.ExpSumTwoEndedError.continuous_expSum p a; fun_prop
  rw [h1, h2, h3, ← intervalIntegral.integral_const_mul, h4, intervalIntegral.integral_div,
    intervalIntegral.integral_add (hc5.intervalIntegrable _ _) (hc6.intervalIntegrable _ _),
    integral_expSum_mul_cosh p a hw T, integral_conj_expSum_mul_cosh p a hw' hT0]

/-! ### The transplant on a rectangle -/

/-- `(x : ℂ)^(w/2) = e^{w log x/2}` for `x ≥ 1`. -/
theorem natCast_cpow_half {x : ℕ} (hx : 1 ≤ x) (w : ℂ) :
    (x : ℂ) ^ (w / 2) = cexp (w * (Real.log x / 2 : ℝ)) := by
  have hx0 : (x : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  rw [Complex.cpow_def_of_ne_zero hx0, show (x : ℂ) = ((x : ℝ) : ℂ) by norm_cast,
    ← Complex.ofReal_log (Nat.cast_nonneg x)]
  congr 1; push_cast; ring

/-- **The transplant on a rectangle** (caseinf-attack Theorem 4, by contour): conjugation-closed `Λ` inside the
rectangle, `|B_Λ| ≥ m` on its boundary, `|B_Λ(½)| ≥ β` and `q < 1` give `Transplant` with constants
`2^{1/2}K_c/(1 − q)` and `2^{1/2}/(β(1 − q))`. -/
theorem transplant_of_rect {x : ℕ} (hx : 1 ≤ x) {Λ : Finset ℂ} (hconj : ∀ ζ ∈ Λ, conj ζ ∈ Λ) {z w : ℂ}
    (hz : 0 < z.re) (hre : z.re ≤ w.re) (him : z.im ≤ w.im) (hin : ∀ ζ ∈ Λ, Inside z w ζ) {m : ℝ}
    (hm0 : 0 < m) (hm : ∀ u, OnBd z w u → m ≤ ‖blaschke (fun ζ : Λ => (ζ : ℂ)) u‖) {β : ℝ} (hβ0 : 0 < β)
    (hβ : β ≤ ‖blaschke (fun ζ : Λ => (ζ : ℂ)) (1 / 2)‖) (hhalf : (1 / 2 : ℂ) ∉ Λ) {Ω Tset : Set ℂ}
    (hΩ : IsOpen Ω) (hrΩ : closedRect z w ⊆ Ω) (hbdT : ∀ u, OnBd z w u → u ∈ Tset)
    (hq : (2 * (w.re - z.re) + 2 * (w.im - z.im)) / (2 * Real.pi * m * √(2 * z.re))
      * (2 * Real.exp (-(z.re * (Real.log x / 2))) / √(2 * z.re)) < 1) :
    Cvs.StepA.Edge.WindowCoshTransformDuality.Transplant x (Λ : Set ℂ) Ω Tset
      (√2 * ((2 * (w.re - z.re) + 2 * (w.im - z.im)) / (2 * Real.pi * m * √(2 * z.re)))
        / (1 - (2 * (w.re - z.re) + 2 * (w.im - z.im)) / (2 * Real.pi * m * √(2 * z.re))
          * (2 * Real.exp (-(z.re * (Real.log x / 2))) / √(2 * z.re))))
      (√2 / (β * (1 - (2 * (w.re - z.re) + 2 * (w.im - z.im)) / (2 * Real.pi * m * √(2 * z.re))
          * (2 * Real.exp (-(z.re * (Real.log x / 2))) / √(2 * z.re))))) := by
  classical
  intro d M c hd hsym hdM
  set Kc := (2 * (w.re - z.re) + 2 * (w.im - z.im)) / (2 * Real.pi * m * √(2 * z.re)) with hKc
  set q := Kc * (2 * Real.exp (-(z.re * (Real.log x / 2))) / √(2 * z.re)) with hqdef
  set p : Λ → ℂ := fun ζ => (ζ : ℂ) with hp
  have hpi : Function.Injective p := Subtype.val_injective
  have hpin : ∀ k, Inside z w (p k) := fun k => hin k.1 k.2
  have hT0 : 0 ≤ Real.log x / 2 := by have := Real.log_natCast_nonneg x; positivity
  have hc₀ : (0 : ℝ) < (1 / 2 : ℂ).re := by norm_num
  have hc₀p : ∀ i, (1 / 2 : ℂ) ≠ p i := fun i h => hhalf (h ▸ i.2)
  obtain ⟨a, ha, hbound⟩ := Cvs.Upstream.ExpSumContourInterpolation.exists_solution hpi hz hre him hpin hm0 hm hΩ hrΩ hT0 hq hd
    (fun u hu => hdM u (hbdT u hu)) (c : ℂ) hc₀ hc₀p hβ0 hβ
  have hε : ∀ i, z.re ≤ (p i).re := fun i => (hpin i).1.le
  have hpos : ∀ i, 0 < (p i).re := fun i => hz.trans_le (hε i)
  refine ⟨winVec x p a, fun ζ hζ => ?_, ?_⟩
  · have hζre : 0 < ζ.re := hz.trans (hin ζ hζ).1
    have hw : ∀ i, ζ + conj (p i) ≠ 0 := fun i => Cvs.Upstream.ExpSumBlaschkeProduct.add_conj_ne_zero (hpos i) hζre.le
    have hw' : ∀ i, conj ζ + conj (p i) ≠ 0 := fun i =>
      Cvs.Upstream.ExpSumBlaschkeProduct.add_conj_ne_zero (hpos i) (by rw [Complex.conj_re]; exact hζre.le)
    have hΩζ : ζ ∈ Ω := hrΩ (by
      obtain ⟨h1, h2, h3, h4⟩ := hin ζ hζ
      exact ⟨by rw [Set.mem_preimage, Set.uIcc_of_le hre]; exact ⟨h1.le, h2.le⟩,
        by rw [Set.mem_preimage, Set.uIcc_of_le him]; exact ⟨h3.le, h4.le⟩⟩)
    rw [coshT_winVec x p a hw hw', natCast_cpow_half hx]
    have h1 := ha ⟨ζ, hζ⟩
    have h2 := ha ⟨conj ζ, hconj ζ hζ⟩
    simp only [hp] at h1 h2
    rw [h1, h2, hsym ζ hΩζ]
    have h2c : (starRingEnd ℂ) (2 : ℂ) = 2 := map_ofNat _ 2
    simp only [map_mul, map_add, map_div₀, map_sub, Complex.conj_conj, Complex.conj_ofReal, ← Complex.exp_conj,
      map_one, h2c]
    ring_nf
  · have hG := Cvs.Upstream.ExpSumBlaschkeProduct.gram_re_nonneg hz hε a
    have hn := norm_sq_winVec_le hz hε x a
    have hq1 : 0 < 1 - q := by linarith
    have hv : ‖winVec x p a‖ ≤ √2 * √((gram p a).re) := by
      rw [← Real.sqrt_mul (by norm_num)]
      exact Real.le_sqrt_of_sq_le hn
    have hc : ‖(c : ℂ)‖ / (β * √(2 * (1 / 2 : ℂ).re)) = |c| / β := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      norm_num
    rw [hc] at hbound
    have hS : √((gram p a).re) ≤ (Kc * M + |c| / β) / (1 - q) := by
      rw [le_div_iff₀ hq1]; linarith
    calc ‖winVec x p a‖ ≤ √2 * √((gram p a).re) := hv
      _ ≤ √2 * ((Kc * M + |c| / β) / (1 - q)) := mul_le_mul_of_nonneg_left hS (by positivity)
      _ = √2 * Kc / (1 - q) * M + √2 / (β * (1 - q)) * |c| := by field_simp

end Cvs.StepA.Edge.ExpSumWindowTransplant

end
