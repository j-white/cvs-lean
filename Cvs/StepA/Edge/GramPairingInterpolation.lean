import Mathlib
import Cvs.StepA.Edge.ExpSumWindowTransplant
import Cvs.StepA.Edge.WindowCoshTransformDuality
import Cvs.Upstream.ExpSumBlaschkeProduct
import Cvs.Upstream.ExpSumContourInterpolation
import Cvs.Upstream.ExpSumTwoEndedError
import Cvs.Upstream.HardyCorrectedInterpolation
import Cvs.WeilForm.WeilFormOnWindowL2

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The corrected interpolation for data with a Gram-pairing bound, and its window class

If `|Σ_k ā_k d_k| ≤ K(Re G(a))^{1/2}` for every coefficient vector, the system `L_a + err = d` on the points has a
solution with `(1 − q)(Re G(a))^{1/2} ≤ K`. For a conjugation-closed finite `Λ` and conjugation-symmetric data `f`,
the window class of the solution has `F_v(ζ) = e^{ζT}f(ζ)` on `Λ` and `‖v‖ ≤ 2^{1/2}K/(1 − q)`.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology Finset
open scoped Interval ComplexConjugate
open Cvs.Upstream.ExpSumBlaschkeProduct (lap gram blaschke)
open Cvs.Upstream.ExpSumTwoEndedError (err)
open Cvs.Upstream.ExpSumContourInterpolation (OnBd Inside evalMap)
open Cvs.Zeta (closedRect)

namespace Cvs.StepA.Edge.GramPairingInterpolation
open Cvs.ZeroCounting

set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The corrected interpolation of data with a pairing bound**: with `q < 1` and
`|Σ_k ā_k d_k| ≤ K(Re G(a))^{1/2}` for all `a`, the system `L_a + err = d` has a solution with
`(1 − q)(Re G(a))^{1/2} ≤ K`. -/
theorem exists_solution_gen {p : ι → ℂ} (hpi : Function.Injective p) {z w : ℂ} (hz : 0 < z.re)
    (hre : z.re ≤ w.re) (him : z.im ≤ w.im) (hpin : ∀ k, Inside z w (p k)) {m : ℝ} (hm0 : 0 < m)
    (hm : ∀ u, OnBd z w u → m ≤ ‖blaschke p u‖) {T : ℝ} (hT : 0 ≤ T)
    (hq : (2 * (w.re - z.re) + 2 * (w.im - z.im)) / (2 * Real.pi * m * √(2 * z.re))
      * (2 * Real.exp (-(z.re * T)) / √(2 * z.re)) < 1)
    (d : ι → ℂ) {K : ℝ} (hK0 : 0 ≤ K) (hK : ∀ a : ι → ℂ, ‖∑ k, conj (a k) * d k‖ ≤ K * √((gram p a).re)) :
    ∃ a : ι → ℂ, (∀ k, lap p a (p k) + err p T a (p k) = d k)
      ∧ (1 - (2 * (w.re - z.re) + 2 * (w.im - z.im)) / (2 * Real.pi * m * √(2 * z.re))
          * (2 * Real.exp (-(z.re * T)) / √(2 * z.re))) * √((gram p a).re) ≤ K := by
  set q := (2 * (w.re - z.re) + 2 * (w.im - z.im)) / (2 * Real.pi * m * √(2 * z.re))
      * (2 * Real.exp (-(z.re * T)) / √(2 * z.re)) with hqdef
  have hε' : ∀ i, z.re ≤ (p i).re := fun i => (hpin i).1.le
  have herr := Cvs.Upstream.HardyCorrectedInterpolation.norm_sum_err_le hz hre him hpin hm0 hm hT
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
    have hG := Cvs.Upstream.ExpSumBlaschkeProduct.gram_re_nonneg hz hε' a
    have h1 : (gram p a).re ≤ q * (gram p a).re := by
      have := herr a
      rw [← norm_neg, ← hgram] at this
      exact (Complex.re_le_norm _).trans this
    have h0 : (gram p a).re = 0 := by nlinarith
    exact Cvs.Upstream.ExpSumBlaschkeProduct.eq_zero_of_gram_re_eq_zero hpi hz hε' h0
  have hsurj : Function.Surjective (evalMap p T) := LinearMap.injective_iff_surjective.1 hinj
  obtain ⟨a, ha⟩ := hsurj d
  refine ⟨a, fun k => congrFun ha k, ?_⟩
  have hk : ∀ k, lap p a (p k) = d k - err p T a (p k) := fun k => by
    have := congrFun ha k
    simp only [evalMap, LinearMap.coe_mk, AddHom.coe_mk] at this
    linear_combination this
  have hG := Cvs.Upstream.ExpSumBlaschkeProduct.gram_re_nonneg hz hε' a
  set S := √((gram p a).re) with hS
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hSS : S * S = (gram p a).re := Real.mul_self_sqrt hG
  have hgram : gram p a = (∑ k, conj (a k) * d k) - ∑ k, conj (a k) * err p T a (p k) := by
    rw [Cvs.Upstream.ExpSumBlaschkeProduct.gram, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hk k]; ring
  have hnorm : ‖gram p a‖ ≤ K * S + q * (gram p a).re := by
    calc ‖gram p a‖ = ‖(∑ k, conj (a k) * d k) - ∑ k, conj (a k) * err p T a (p k)‖ := by rw [hgram]
      _ ≤ _ := (norm_sub_le _ _).trans (add_le_add (hK a) (herr a))
  have hbound : S * S ≤ K * S + q * (S * S) := by
    rw [hSS]; exact (Complex.re_le_norm _).trans hnorm
  rcases hS0.lt_or_eq with hSp | hSz
  · have : S * ((1 - q) * S) ≤ S * K := by nlinarith
    exact le_of_mul_le_mul_left this hSp
  · rw [← hSz, mul_zero]; exact hK0

/-- **The window class reproducing conjugation-symmetric data**: for conjugation-closed `Λ` inside the rectangle and
`f(ζ̄) = conj f(ζ)` on `Λ` with a pairing bound `K`, some window class has `F_v(ζ) = e^{ζ log x/2}f(ζ)` on `Λ` and
`‖v‖ ≤ 2^{1/2}K/(1 − q)`. -/
theorem exists_window {x : ℕ} {Λ : Finset ℂ} (hconj : ∀ ζ ∈ Λ, conj ζ ∈ Λ) {z w : ℂ} (hz : 0 < z.re)
    (hre : z.re ≤ w.re) (him : z.im ≤ w.im) (hin : ∀ ζ ∈ Λ, Inside z w ζ) {m : ℝ} (hm0 : 0 < m)
    (hm : ∀ u, OnBd z w u → m ≤ ‖blaschke (fun ζ : Λ => (ζ : ℂ)) u‖)
    (hq : (2 * (w.re - z.re) + 2 * (w.im - z.im)) / (2 * Real.pi * m * √(2 * z.re))
      * (2 * Real.exp (-(z.re * (Real.log x / 2))) / √(2 * z.re)) < 1)
    (f : ℂ → ℂ) (hf : ∀ ζ ∈ Λ, f (conj ζ) = conj (f ζ)) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ a : Λ → ℂ, ‖∑ k, conj (a k) * f k‖ ≤ K * √((gram (fun ζ : Λ => (ζ : ℂ)) a).re)) :
    ∃ v : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x), (∀ ζ ∈ Λ, Cvs.StepA.Edge.WindowCoshTransformDuality.coshT x v ζ = cexp (ζ * (Real.log x / 2 : ℝ)) * f ζ)
      ∧ ‖v‖ ≤ √2 * K / (1 - (2 * (w.re - z.re) + 2 * (w.im - z.im)) / (2 * Real.pi * m * √(2 * z.re))
          * (2 * Real.exp (-(z.re * (Real.log x / 2))) / √(2 * z.re))) := by
  classical
  set q := (2 * (w.re - z.re) + 2 * (w.im - z.im)) / (2 * Real.pi * m * √(2 * z.re))
      * (2 * Real.exp (-(z.re * (Real.log x / 2))) / √(2 * z.re)) with hqdef
  set p : Λ → ℂ := fun ζ => (ζ : ℂ) with hp
  have hT0 : 0 ≤ Real.log x / 2 := by have := Real.log_natCast_nonneg x; positivity
  have hpin : ∀ k, Inside z w (p k) := fun k => hin k.1 k.2
  obtain ⟨a, ha, hb⟩ := exists_solution_gen (p := p) Subtype.val_injective hz hre him hpin hm0 hm hT0 hq
    (fun k => f k) hK0 hK
  have hε : ∀ i, z.re ≤ (p i).re := fun i => (hpin i).1.le
  have hpos : ∀ i, 0 < (p i).re := fun i => hz.trans_le (hε i)
  refine ⟨Cvs.StepA.Edge.ExpSumWindowTransplant.winVec x p a, fun ζ hζ => ?_, ?_⟩
  · have hζre : 0 < ζ.re := hz.trans (hin ζ hζ).1
    rw [Cvs.StepA.Edge.ExpSumWindowTransplant.coshT_winVec x p a (fun i => Cvs.Upstream.ExpSumBlaschkeProduct.add_conj_ne_zero (hpos i) hζre.le)
      (fun i => Cvs.Upstream.ExpSumBlaschkeProduct.add_conj_ne_zero (hpos i) (by rw [Complex.conj_re]; exact hζre.le))]
    have e1 : lap p a ζ + err p (Real.log x / 2) a ζ = f ζ := ha ⟨ζ, hζ⟩
    have e2 : lap p a (conj ζ) + err p (Real.log x / 2) a (conj ζ) = f (conj ζ) := ha ⟨conj ζ, hconj ζ hζ⟩
    rw [e1, e2, hf ζ hζ, map_mul, Complex.conj_conj, ← Complex.exp_conj, map_mul, Complex.conj_conj,
      Complex.conj_ofReal]
    ring
  · have hq1 : 0 < 1 - q := by linarith
    have hG := Cvs.Upstream.ExpSumBlaschkeProduct.gram_re_nonneg hz hε a
    have hn := Cvs.StepA.Edge.ExpSumWindowTransplant.norm_sq_winVec_le hz hε x a
    have hv : ‖Cvs.StepA.Edge.ExpSumWindowTransplant.winVec x p a‖ ≤ √2 * √((gram p a).re) := by
      rw [← Real.sqrt_mul (by norm_num)]
      exact Real.le_sqrt_of_sq_le hn
    have hS : √((gram p a).re) ≤ K / (1 - q) := by rw [le_div_iff₀ hq1]; linarith
    calc ‖Cvs.StepA.Edge.ExpSumWindowTransplant.winVec x p a‖ ≤ √2 * √((gram p a).re) := hv
      _ ≤ √2 * (K / (1 - q)) := mul_le_mul_of_nonneg_left hS (by positivity)
      _ = √2 * K / (1 - q) := by ring

end Cvs.StepA.Edge.GramPairingInterpolation

end
