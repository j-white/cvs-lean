import Mathlib
import Cvs.Approximant.SpineSubspace
import Cvs.Finite.ConstantModeLevyDeficit
import Cvs.Finite.ConstantModeWindowDamped
import Cvs.Finite.WindowMatrixSymbolKernel
import Cvs.Route.OneCellLaplaceTransform
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.LevyDensity
import Cvs.WeilForm.AutocorrSelfConvolution
import Cvs.WeilForm.InfimumAttainedSphere
import Cvs.WeilForm.PositivityOfRH
import Cvs.WeilForm.PrimeSideExplicitIndex
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.WeilForm.WindowSetNonempty
import Cvs.Zeta.WeilPositivityStatement

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The one-cell function is the window form of the box, so RH makes it nonnegative

`weilForm P R (flat L) = G L` for every complete `(P, R)` (`e^L ≤ P`, `L ≤ R log 2`): the pairing is
`16(cosh(L/2) − 1)`, the box's self-convolution is the tent `(L − |τ|)₊`, the archimedean deficit integrates
to `2·ladder L` through the geometric series of `densityU`, and the prime side is `2·primeSide L`. The box
is in the form domain (Cvs.WeilForm.WindowSetNonempty), so `PositivityOfRH`'s window positivity under RH gives `0 ≤ G L` for every `L > 0`.
-/

noncomputable section

open MeasureTheory Real Set Filter Topology Cvs.Zeta.Explicit.Weil
open scoped ArithmeticFunction

namespace Cvs.Route.OneCellBoxWindowForm
open Cvs.ZeroCounting

open Cvs.Finite.WindowMatrixSymbolKernel (bk bk_pos)
open Cvs.Route.OneCellLaplaceTransform (ladder primeSide G laplace_ramp laplace_ramp_plus integrableOn_ramp integrable_tsum_of_nonneg summable_inv_bk_sq)

/-! ### The box's self-convolution is the tent -/

theorem conv_even (f : ℝ → ℝ) (t : ℝ) : selfConvolution f (-t) = selfConvolution f t := by
  show (∫ x : ℝ, f x * f (x + -t)) = ∫ x : ℝ, f x * f (x + t)
  rw [← integral_add_right_eq_self (fun x : ℝ => f x * f (x + -t)) t]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show f (x + t) * f (x + t + -t) = f x * f (x + t)
  rw [show x + t + -t = x from by ring, mul_comm]

/-- `selfConvolution (flat L) τ = (L − |τ|)₊`. -/
theorem conv_flat {L : ℝ} (hL : 0 ≤ L) (τ : ℝ) :
    selfConvolution (Cvs.WeilForm.WindowSetNonempty.flat L) τ = max (L - |τ|) 0 := by
  unfold Cvs.WeilForm.WindowSetNonempty.flat
  rcases le_or_gt L |τ| with h | h
  · rw [Cvs.WeilForm.AutocorrSelfConvolution.selfConvolution_indicator_eq_zero L _ h, max_eq_right (by linarith)]
  · rw [max_eq_left (by linarith)]
    rcases le_or_gt 0 τ with hτ | hτ
    · rw [abs_of_nonneg hτ] at h ⊢
      exact Cvs.Finite.ConstantModeWindowDamped.selfConvolution_indicator_one hτ h.le
    · rw [abs_of_neg hτ] at h ⊢
      rw [← conv_even, Cvs.Finite.ConstantModeWindowDamped.selfConvolution_indicator_one (by linarith) h.le]

/-! ### The pairing -/

theorem integral_flat_exp {L c : ℝ} (hL : 0 ≤ L) (hc : c ≠ 0) :
    ∫ x : ℝ, Cvs.WeilForm.WindowSetNonempty.flat L x * Real.exp (c * x) = (Real.exp (c * L) - 1) / c := by
  have hfun : (fun x => Cvs.WeilForm.WindowSetNonempty.flat L x * Real.exp (c * x))
      = Set.indicator (Set.Ioc (0:ℝ) L) (fun x => Real.exp (c * x)) := by
    funext x; unfold Cvs.WeilForm.WindowSetNonempty.flat
    by_cases hx : x ∈ Set.Ioc (0:ℝ) L <;> simp [hx]
  rw [hfun, integral_indicator measurableSet_Ioc, ← intervalIntegral.integral_of_le hL]
  have hd : ∀ x ∈ uIcc (0:ℝ) L, HasDerivAt (fun x => Real.exp (c * x) / c) (Real.exp (c * x)) x := by
    intro x _
    have := ((hasDerivAt_id x).const_mul c).exp.div_const c
    simpa [mul_comm, mul_div_assoc, mul_div_cancel_left₀ _ hc] using this
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (((continuous_const.mul continuous_id).rexp).intervalIntegrable _ _)]
  simp [mul_zero, Real.exp_zero, sub_div]

theorem pairing_flat {L : ℝ} (hL : 0 ≤ L) :
    2 * (∫ x : ℝ, Cvs.WeilForm.WindowSetNonempty.flat L x * Real.exp (x / 2)) * (∫ x : ℝ, Cvs.WeilForm.WindowSetNonempty.flat L x * Real.exp (-(x / 2)))
      = 16 * (Real.cosh (L / 2) - 1) := by
  have h1 : (fun x : ℝ => Cvs.WeilForm.WindowSetNonempty.flat L x * Real.exp (x / 2)) = fun x => Cvs.WeilForm.WindowSetNonempty.flat L x * Real.exp ((1/2) * x) := by
    funext x; congr 2; ring
  have h2 : (fun x : ℝ => Cvs.WeilForm.WindowSetNonempty.flat L x * Real.exp (-(x / 2)))
      = fun x => Cvs.WeilForm.WindowSetNonempty.flat L x * Real.exp ((-1/2) * x) := by
    funext x; congr 2; ring
  rw [h1, h2, integral_flat_exp hL (by norm_num), integral_flat_exp hL (by norm_num), Real.cosh_eq]
  have e1 : Real.exp ((1/2) * L) = Real.exp (L / 2) := by congr 1; ring
  have e2 : Real.exp ((-1/2) * L) = Real.exp (-(L / 2)) := by congr 1; ring
  have e3 : Real.exp (L / 2) * Real.exp (-(L / 2)) = 1 := by rw [← Real.exp_add]; simp
  rw [e1, e2]
  field_simp
  nlinarith [e3]

/-! ### The archimedean deficit -/

/-- `densityU u = Σ_k e^{−(k+¼)u}` for `u > 0`. -/
theorem hasSum_densityU {u : ℝ} (hu : 0 < u) :
    HasSum (fun k : ℕ => Real.exp (-(((k:ℝ) + 1/4) * u))) (Cvs.WeilForm.Archimedean.LevyDensity.densityU u) := by
  have hr0 : 0 ≤ Real.exp (-u) := (Real.exp_pos _).le
  have hr1 : Real.exp (-u) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have h := (hasSum_geometric_of_lt_one hr0 hr1).mul_left (Real.exp (-(u/4)))
  have hd : Cvs.WeilForm.Archimedean.LevyDensity.densityU u = Real.exp (-(u/4)) * (1 - Real.exp (-u))⁻¹ := by
    unfold Cvs.WeilForm.Archimedean.LevyDensity.densityU; rw [div_eq_mul_inv]
  have hfun : (fun k : ℕ => Real.exp (-(((k:ℝ) + 1/4) * u)))
      = fun k : ℕ => Real.exp (-(u/4)) * Real.exp (-u) ^ k := by
    funext k
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1; ring
  rw [hfun, hd]; exact h

/-- One rung of the deficit: `∫₀^∞ e^{−au} min(u/2, L) du = (1 − e^{−2aL})/(2a²)` for `a > 0`, `L ≥ 0`. -/
theorem integral_exp_min {a L : ℝ} (ha : 0 < a) (hL : 0 ≤ L) :
    IntegrableOn (fun u => Real.exp (-(a * u)) * max (min (u / 2) L) 0) (Ioi 0) ∧
    ∫ u in Ioi (0:ℝ), Real.exp (-(a * u)) * max (min (u / 2) L) 0
      = (1 - Real.exp (-(2 * a * L))) / (2 * a ^ 2) := by
  have hfun : ∀ u ∈ Ioi (0:ℝ), Real.exp (-(a * u)) * max (min (u / 2) L) 0
      = (1/2) * ((u - 0) * Real.exp (-(a * u))) - (1/2) * (max (u - 2 * L) 0 * Real.exp (-(a * u))) := by
    intro u hu
    have hu' : 0 < u := hu
    have : max (min (u / 2) L) 0 = u / 2 - max (u - 2 * L) 0 / 2 := by
      rcases le_or_gt (u / 2) L with h | h
      · rw [min_eq_left h, max_eq_left (by linarith), max_eq_right (by linarith)]; ring
      · rw [min_eq_right h.le, max_eq_left hL, max_eq_left (by linarith)]; ring
    rw [this]; ring
  obtain ⟨hI2, hE2⟩ := laplace_ramp_plus ha (by linarith : (0:ℝ) ≤ 2 * L)
  have hI1 := integrableOn_ramp (c := 0) ha
  have hI : IntegrableOn (fun u => (1/2) * ((u - 0) * Real.exp (-(a * u)))
      - (1/2) * (max (u - 2 * L) 0 * Real.exp (-(a * u)))) (Ioi 0) :=
    (hI1.const_mul _).sub (hI2.const_mul _)
  refine ⟨hI.congr_fun (fun u hu => (hfun u hu).symm) measurableSet_Ioi, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi hfun, integral_sub (hI1.const_mul _) (hI2.const_mul _),
    integral_const_mul, integral_const_mul, laplace_ramp ha, hE2]
  simp only [mul_zero, neg_zero, Real.exp_zero]
  have : Real.exp (-(a * (2 * L))) = Real.exp (-(2 * a * L)) := by congr 1; ring
  rw [this]; field_simp

/-- **The archimedean deficit of the box is twice the ladder**:
`∫₀^∞ densityU u · (L − selfConv(u/2)) du = 2·Σ_k (1 − e^{−b_k L})/b_k²`. -/
theorem deficit_flat_eq {L : ℝ} (hL : 0 < L) :
    ∫ u in Ioi (0:ℝ), Cvs.WeilForm.Archimedean.LevyDensity.densityU u
      * (selfConvolution (Cvs.WeilForm.WindowSetNonempty.flat L) 0 - selfConvolution (Cvs.WeilForm.WindowSetNonempty.flat L) (u / 2)) = 2 * ladder L := by
  set F : ℕ → ℝ → ℝ := fun k u => Real.exp (-(((k:ℝ) + 1/4) * u)) * max (min (u / 2) L) 0 with hF
  have hak : ∀ k : ℕ, (0:ℝ) < (k:ℝ) + 1/4 := fun k => by positivity
  have h0 : selfConvolution (Cvs.WeilForm.WindowSetNonempty.flat L) 0 = L := by
    rw [conv_flat hL.le, abs_zero, sub_zero, max_eq_left hL.le]
  have hagree : ∀ u ∈ Ioi (0:ℝ), Cvs.WeilForm.Archimedean.LevyDensity.densityU u
      * (selfConvolution (Cvs.WeilForm.WindowSetNonempty.flat L) 0 - selfConvolution (Cvs.WeilForm.WindowSetNonempty.flat L) (u / 2)) = ∑' k, F k u := by
    intro u hu
    have hu' : 0 < u := hu
    have hmin : selfConvolution (Cvs.WeilForm.WindowSetNonempty.flat L) 0 - selfConvolution (Cvs.WeilForm.WindowSetNonempty.flat L) (u / 2) = min (u / 2) L := by
      rw [h0]; exact Cvs.Finite.ConstantModeLevyDeficit.deficit_eq_min hL.le hu'.le
    have hmax : max (min (u / 2) L) 0 = min (u / 2) L := max_eq_left (le_min (by linarith) hL.le)
    rw [hmin, ← (hasSum_densityU hu').tsum_eq, ← tsum_mul_right]
    simp only [hF, hmax]
  have hm : ∀ k, Measurable (F k) := fun k =>
    (by fun_prop : Continuous fun u : ℝ =>
      Real.exp (-(((k:ℝ) + 1/4) * u)) * max (min (u / 2) L) 0).measurable
  have hnn : ∀ k u, 0 ≤ F k u := fun k u => mul_nonneg (Real.exp_pos _).le (le_max_right _ _)
  have hpt : ∀ u, Summable fun k => F k u := by
    intro u
    rcases le_or_gt u 0 with hu | hu
    · have hz : (fun k => F k u) = fun _ => 0 := by
        funext k; simp only [hF]
        rw [max_eq_right (min_le_of_left_le (by linarith)), mul_zero]
      rw [hz]; exact summable_zero
    · exact (hasSum_densityU hu).summable.mul_right _
  have hval : ∀ k, ∫ u in Ioi (0:ℝ), F k u
      = (1 - Real.exp (-(2 * ((k:ℝ) + 1/4) * L))) / (2 * ((k:ℝ) + 1/4) ^ 2) :=
    fun k => (integral_exp_min (hak k) hL.le).2
  have hint : ∀ k, Integrable (F k) (volume.restrict (Ioi 0)) :=
    fun k => (integral_exp_min (hak k) hL.le).1
  have hbk : ∀ k : ℕ, bk k = 2 * ((k:ℝ) + 1/4) := fun k => by unfold bk; ring
  have hterm : ∀ k : ℕ, (1 - Real.exp (-(2 * ((k:ℝ) + 1/4) * L))) / (2 * ((k:ℝ) + 1/4) ^ 2)
      = 2 * ((1 - Real.exp (-(bk k * L))) / bk k ^ 2) := by
    intro k; rw [hbk]; have := hak k; field_simp
  have hsum : Summable fun k => ∫ u in Ioi (0:ℝ), F k u := by
    simp_rw [hval, hterm]
    refine (summable_inv_bk_sq.mul_left 2).of_nonneg_of_le (fun k => ?_) fun k => ?_
    · have := bk_pos k
      have : Real.exp (-(bk k * L)) ≤ 1 := by rw [Real.exp_le_one_iff]; nlinarith
      have : 0 ≤ 1 - Real.exp (-(bk k * L)) := by linarith
      positivity
    · have := bk_pos k
      gcongr
      linarith [Real.exp_pos (-(bk k * L))]
  obtain ⟨_, hE⟩ := integrable_tsum_of_nonneg hm hnn hpt hint hsum
  rw [setIntegral_congr_fun measurableSet_Ioi hagree, hE]
  simp_rw [hval, hterm]
  rw [tsum_mul_left]
  rfl

/-! ### The prime side -/

/-- The prime side of the box is `2·primeSide L`: the tent at `±log n` is `2(L − log n)₊`. -/
theorem primeSum_flat_eq {L : ℝ} (hL : 0 ≤ L) :
    ∑ n ∈ Finset.range ⌈Real.exp L⌉₊,
        (Λ n * (n : ℝ) ^ (-(1/2) : ℝ))
          * (selfConvolution (Cvs.WeilForm.WindowSetNonempty.flat L) (Real.log n) + selfConvolution (Cvs.WeilForm.WindowSetNonempty.flat L) (-(Real.log n)))
      = 2 * primeSide L := by
  have hterm : ∀ n : ℕ, (Λ n * (n : ℝ) ^ (-(1/2) : ℝ))
      * (selfConvolution (Cvs.WeilForm.WindowSetNonempty.flat L) (Real.log n) + selfConvolution (Cvs.WeilForm.WindowSetNonempty.flat L) (-(Real.log n)))
      = 2 * (Λ n / Real.sqrt n * max (L - Real.log n) 0) := by
    intro n
    rw [conv_flat hL, conv_flat hL, abs_neg]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    have h1 : (1:ℝ) ≤ n := by exact_mod_cast hn
    have hlog : 0 ≤ Real.log n := Real.log_nonneg h1
    rw [abs_of_nonneg hlog, Real.sqrt_eq_rpow, Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]
    ring
  rw [Finset.sum_congr rfl fun n _ => hterm n, ← Finset.mul_sum]
  congr 1
  unfold primeSide
  symm
  refine tsum_eq_sum fun n hn => ?_
  rw [Finset.mem_range, not_lt] at hn
  have h1 : Real.exp L ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hn)
  have hnpos : (0:ℝ) < n := (Real.exp_pos L).trans_le h1
  have h2 : L ≤ Real.log n := (Real.le_log_iff_exp_le hnpos).2 h1
  rw [max_eq_right (by linarith), mul_zero]

/-! ### Assembly -/

/-- **The window form of the box is the one-cell function**, for every complete `(P, R)`:
`e^L ≤ P` and `L ≤ R log 2`. -/
theorem weilForm_flat_eq {L : ℝ} (hL : 0 < L) {P R : ℕ}
    (hP : Real.exp L ≤ P) (hR : L ≤ R * Real.log 2) :
    Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (Cvs.WeilForm.WindowSetNonempty.flat L) = G L := by
  have h := Cvs.WeilForm.PrimeSideExplicitIndex.weilForm_eq_range hL.le hP hR (fun _ => (1:ℝ))
  rw [show Set.indicator (Set.Ioc 0 L) (fun _ => (1:ℝ)) = Cvs.WeilForm.WindowSetNonempty.flat L from rfl] at h
  rw [h, pairing_flat hL.le, deficit_flat_eq hL, primeSum_flat_eq hL.le]
  have h0 : selfConvolution (Cvs.WeilForm.WindowSetNonempty.flat L) 0 = L := by
    rw [conv_flat hL.le, abs_zero, sub_zero, max_eq_left hL.le]
  rw [h0]
  unfold G
  ring

/-- **RH makes the one-cell function nonnegative**: `0 ≤ G L` for every `L > 0`, by window positivity
(Cvs.WeilForm.PositivityOfRH) on the box, which lies in the form domain (Cvs.WeilForm.WindowSetNonempty). -/
theorem G_nonneg_of_RH (hRH : RiemannHypothesis) {L : ℝ} (hL : 0 < L) : 0 ≤ G L := by
  have hP : Real.exp L ≤ (⌈Real.exp L⌉₊ : ℕ) := Nat.le_ceil _
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hR : L ≤ (⌈L / Real.log 2⌉₊ : ℕ) * Real.log 2 := by
    have := Nat.le_ceil (L / Real.log 2)
    rwa [div_le_iff₀ hlog2] at this
  rw [← weilForm_flat_eq hL hP hR,
    ← Cvs.Approximant.SpineSubspace.Q_ofFun hL.le _ _ (Cvs.WeilForm.WindowSetNonempty.memLp_flat L) (ae_of_all _ (Cvs.WeilForm.WindowSetNonempty.support_flat L))
      (Cvs.WeilForm.WindowSetNonempty.integrableOn_levy_flat hL)]
  exact Cvs.WeilForm.PositivityOfRH.Q_nonneg_of_RH hRH hL hP hR _

end Cvs.Route.OneCellBoxWindowForm
