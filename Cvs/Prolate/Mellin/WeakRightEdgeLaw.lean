import Mathlib
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.Approximant.SpineCouplingTailPairing
import Cvs.Approximant.SpineSubspace
import Cvs.L2a.WindowChainInputsProlate
import Cvs.Prolate.EntireRungProlateEquation
import Cvs.Prolate.Envelope.RungExteriorLaw
import Cvs.Prolate.Envelope.RungProfileEdgePlunge
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.Mellin.CentreValueAliasSum
import Cvs.Prolate.Mellin.FarLineRungSizes
import Cvs.Prolate.Mellin.HigherAliasRayTransforms
import Cvs.Prolate.Mellin.ProlateAliasSumLaw
import Cvs.Prolate.Mellin.RayTransformEdgeSum
import Cvs.Prolate.Mellin.RightEdgeAliasLaw
import Cvs.Prolate.Mellin.RightEdgePoissonSplit
import Cvs.Prolate.Mellin.RungProfileOutsideCircle
import Cvs.Prolate.Mellin.RungTransformUnitCircle
import Cvs.Prolate.Mellin.RungUnitCircleLaw
import Cvs.Prolate.Mellin.RungWindowLawRightEdge
import Cvs.Prolate.Mellin.TrapezoidErrorFarLines
import Cvs.Prolate.Mellin.WeakRightEdgeWindowInput
import Cvs.Route.Visibility.ExtPairingRatesSubpoly
import Cvs.Route.Visibility.ExteriorFactorMTwo

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The weak right-edge law, and hV without `EdgeLawSum`

`B = T_{S_{H_{4j}}} − α_j T_{S_{H₀}}` up to `(4e⁶ + 4)E_j/√x` (Cvs.Prolate.Mellin.RightEdgeAliasLaw, Cvs.Prolate.Mellin.CentreValueAliasSum, Cvs.Prolate.Mellin.ProlateAliasSumLaw); Cvs.Prolate.Mellin.TrapezoidErrorFarLines with `y₀ = c⁻³` and the
sizes of Cvs.Prolate.Mellin.FarLineRungSizes give `g‖B(σ + ig)‖ ≤ W(x)(1 − λ_{4j})^{1/4}` with `W` subpolynomial, which is `Cvs.Prolate.Mellin.WeakRightEdgeWindowInput.WeakEdgeLaw`.
-/

noncomputable section

open Real Set MeasureTheory Filter Complex Topology
open Cvs.Prolate.Mellin.RayTransformEdgeSum (rayT)
open Cvs.Prolate.EntireRungProlateEquation (Hk)
open Cvs.Prolate.Mellin.RungTransformUnitCircle (Bw)
open Cvs.Prolate.EvenRungsByIndex (rung muR lamR lev IsLevelIdx)
open Cvs.Route.Visibility.ExtPairingRatesSubpoly (SubPoly)
open Cvs.Prolate.Mellin.RungProfileOutsideCircle (Mk)

namespace Cvs.Prolate.Mellin.WeakRightEdgeLaw
open Cvs.ZeroCounting

/-- `c² ≤ e^c` for `c ≥ 27`. -/
theorem sq_le_exp {c : ℝ} (hc : 27 ≤ c) : c ^ 2 ≤ Real.exp c := by
  have h1 : (1 + c / 3) ^ 3 ≤ Real.exp c := by
    have := pow_le_pow_left₀ (by linarith) (Real.add_one_le_exp (c / 3)) 3
    rw [← Real.exp_nat_mul] at this
    calc (1 + c / 3) ^ 3 = (c / 3 + 1) ^ 3 := by ring
      _ ≤ Real.exp (↑3 * (c / 3)) := this
      _ = Real.exp c := by congr 1; ring
  nlinarith

/-- **The alias constant at `y₀ = c⁻³`**: `Ω ≤ P(10 + 6 log c)/c` when `P′ ≤ c²P`, `c ≥ 80`. -/
theorem omega_le {c P P' : ℝ} (hc : 80 ≤ c) (hP : 0 ≤ P) (hP' : P' ≤ c ^ 2 * P) :
    Cvs.Prolate.Mellin.HigherAliasRayTransforms.omega c P P' (1 / c ^ 3) ≤ P * (10 + 6 * Real.log c) / c := by
  unfold Cvs.Prolate.Mellin.HigherAliasRayTransforms.omega
  have hc0 : 0 < c := by linarith
  have he := sq_le_exp (by linarith : (27 : ℝ) ≤ c)
  have he0 : Real.exp (-c) ≤ 1 / c ^ 2 := by
    rw [Real.exp_neg, ← one_div]; exact one_div_le_one_div_of_le (by positivity) he
  have he1 : Real.exp (-c) ≤ 1 / 2 := he0.trans (by rw [div_le_iff₀ (by positivity)]; nlinarith)
  have hden : 1 / 2 ≤ 1 - Real.exp (-c) := by linarith
  have h1 : 2 * P * Real.exp (-c) / (1 - Real.exp (-c)) ≤ 4 * P / c ^ 2 := by
    rw [div_le_div_iff₀ (by linarith) (by positivity)]
    have : P * Real.exp (-c) * c ^ 2 ≤ P := by
      have := mul_le_mul_of_nonneg_left he0 hP
      rw [mul_one_div, le_div_iff₀ (by positivity)] at this; linarith
    nlinarith
  have h2 : 6 * P' * (1 / c ^ 3) / c ≤ 6 * P / c ^ 2 := by
    have e : 6 * P' * (1 / c ^ 3) / c = 6 * P' / c ^ 4 := by field_simp
    rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
    have : P' * c ^ 2 ≤ c ^ 2 * P * c ^ 2 := mul_le_mul_of_nonneg_right hP' (by positivity)
    nlinarith
  have h3 : 2 * P / c * Real.log (1 / (1 / c ^ 3)) = 6 * P * Real.log c / c := by
    rw [one_div_one_div, Real.log_pow]; push_cast; ring
  have h4 : 4 * P / c ^ 2 + 6 * P / c ^ 2 ≤ 10 * P / c := by
    rw [← add_div, show 4 * P + 6 * P = 10 * P by ring]
    exact div_le_div_of_nonneg_left (by positivity) hc0 (by nlinarith)
  calc 2 * P * Real.exp (-c) / (1 - Real.exp (-c)) + 6 * P' * (1 / c ^ 3) / c
        + 2 * P / c * Real.log (1 / (1 / c ^ 3))
      ≤ 4 * P / c ^ 2 + 6 * P / c ^ 2 + 6 * P * Real.log c / c := by rw [h3]; linarith
    _ ≤ 10 * P / c + 6 * P * Real.log c / c := by linarith
    _ = P * (10 + 6 * Real.log c) / c := by ring

/-- `√(c²A e(cM + c²A)) ≤ c²√(A e(M + A))` for `c ≥ 1`. -/
theorem sqrt_deriv_le {c A M : ℝ} (hc : 1 ≤ c) (hA : 0 ≤ A) (hM : 0 ≤ M) :
    √(c ^ 2 * A * (Real.exp 1 * (c * M + c ^ 2 * A))) ≤ c ^ 2 * √(A * (Real.exp 1 * (M + A))) := by
  rw [show c ^ 2 * √(A * (Real.exp 1 * (M + A))) = √((c ^ 2) ^ 2 * (A * (Real.exp 1 * (M + A)))) by
    rw [Real.sqrt_mul (x := (c ^ 2) ^ 2) (by positivity) (A * (Real.exp 1 * (M + A))),
      Real.sqrt_sq (by positivity)]]
  refine Real.sqrt_le_sqrt ?_
  have h1 : c * M ≤ c ^ 2 * M := mul_le_mul_of_nonneg_right (by nlinarith) hM
  have : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
  have h2 : c ^ 2 * A * (Real.exp 1 * (c * M + c ^ 2 * A)) ≤ c ^ 2 * A * (Real.exp 1 * (c ^ 2 * M + c ^ 2 * A)) := by
    gcongr
  calc c ^ 2 * A * (Real.exp 1 * (c * M + c ^ 2 * A)) ≤ c ^ 2 * A * (Real.exp 1 * (c ^ 2 * M + c ^ 2 * A)) := h2
    _ = (c ^ 2) ^ 2 * (A * (Real.exp 1 * (M + A))) := by ring

/-- `√(A e(M + A)) ≤ √(20e)·c·ω^{1/4}` for `A ≤ 4cω^{1/2}`, `M ≤ √c`, `0 ≤ ω ≤ 1`, `c ≥ 1`. -/
theorem sqrt_P_le {c A M ω : ℝ} (hc : 1 ≤ c) (hA0 : 0 ≤ A) (hA : A ≤ 4 * c * ω ^ (1 / 2 : ℝ)) (hM0 : 0 ≤ M)
    (hM : M ≤ √c) (hω0 : 0 ≤ ω) (hω1 : ω ≤ 1) :
    √(A * (Real.exp 1 * (M + A))) ≤ √(20 * Real.exp 1) * c * ω ^ (1 / 4 : ℝ) := by
  have hh : ω ^ (1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one hω0 hω1 (by norm_num)
  have hh0 : 0 ≤ ω ^ (1 / 2 : ℝ) := Real.rpow_nonneg hω0 _
  have hsc : √c ≤ c := by rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have hMA : M + A ≤ 5 * c := by nlinarith
  have hq : (ω ^ (1 / 4 : ℝ)) ^ 2 = ω ^ (1 / 2 : ℝ) := Cvs.Prolate.Mellin.WeakRightEdgeWindowInput.rpow_quarter_sq hω0
  rw [show √(20 * Real.exp 1) * c * ω ^ (1 / 4 : ℝ) = √((√(20 * Real.exp 1) * c * ω ^ (1 / 4 : ℝ)) ^ 2) by
    rw [Real.sqrt_sq (by positivity)]]
  refine Real.sqrt_le_sqrt ?_
  rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), hq]
  have he : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
  calc A * (Real.exp 1 * (M + A)) ≤ (4 * c * ω ^ (1 / 2 : ℝ)) * (Real.exp 1 * (5 * c)) := by gcongr
    _ = 20 * Real.exp 1 * c ^ 2 * ω ^ (1 / 2 : ℝ) := by ring

/-- `|α|√(A₀e(M₀ + A₀)) ≤ c√(e(4 + Q))·ω^{1/4}` from `α²M₀ ≤ c`, `A₀ ≤ 4cω^{1/2}`, `(|α|A₀)² ≤ Qc²ω^{1/2}`. -/
theorem alpha_sqrt_P_le {c α A M ω Q : ℝ} (hc : 0 < c) (hA0 : 0 ≤ A) (hQ0 : 0 ≤ Q)
    (hαM : α ^ 2 * M ≤ c)
    (hA : A ≤ 4 * c * ω ^ (1 / 2 : ℝ)) (hE : (|α| * A) ^ 2 ≤ Q * c ^ 2 * ω ^ (1 / 2 : ℝ)) (hω0 : 0 ≤ ω) :
    |α| * √(A * (Real.exp 1 * (M + A))) ≤ c * √(Real.exp 1 * (4 + Q)) * ω ^ (1 / 4 : ℝ) := by
  have hq : (ω ^ (1 / 4 : ℝ)) ^ 2 = ω ^ (1 / 2 : ℝ) := Cvs.Prolate.Mellin.WeakRightEdgeWindowInput.rpow_quarter_sq hω0
  have hh0 : 0 ≤ ω ^ (1 / 2 : ℝ) := Real.rpow_nonneg hω0 _
  have hQ : 0 ≤ Q * c ^ 2 * ω ^ (1 / 2 : ℝ) := (sq_nonneg _).trans hE
  have he : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
  have hQ' : 0 ≤ 4 + Q := by linarith
  rw [show |α| * √(A * (Real.exp 1 * (M + A))) = √(α ^ 2 * (A * (Real.exp 1 * (M + A)))) by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs],
    show c * √(Real.exp 1 * (4 + Q)) * ω ^ (1 / 4 : ℝ) = √((c * √(Real.exp 1 * (4 + Q)) * ω ^ (1 / 4 : ℝ)) ^ 2) by
    rw [Real.sqrt_sq (by positivity)]]
  refine Real.sqrt_le_sqrt ?_
  rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), hq]
  have h1 : α ^ 2 * (A * (Real.exp 1 * (M + A))) = Real.exp 1 * ((α ^ 2 * M) * A + (|α| * A) ^ 2) := by
    rw [mul_pow, sq_abs]; ring
  rw [h1]
  have h2 : α ^ 2 * M * A ≤ c * (4 * c * ω ^ (1 / 2 : ℝ)) :=
    (mul_le_mul_of_nonneg_right hαM hA0).trans (mul_le_mul_of_nonneg_left hA hc.le)
  calc Real.exp 1 * ((α ^ 2 * M) * A + (|α| * A) ^ 2)
      ≤ Real.exp 1 * (c * (4 * c * ω ^ (1 / 2 : ℝ)) + Q * c ^ 2 * ω ^ (1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left (add_le_add h2 hE) he
    _ = c ^ 2 * (Real.exp 1 * (4 + Q)) * ω ^ (1 / 2 : ℝ) := by ring

/-- The weak-law factor `W(x) = (12e⁶ + 4)(1 + P(x)) + (4/3)(10 + 6 log 2πx)(√(20e) + 1 + e(4 + P(x)))`. -/
def weakW (x : ℕ) : ℝ :=
  (12 * Real.exp 6 + 4) * (1 + Cvs.Prolate.Envelope.RungProfileEdgePlunge.edgeP x)
    + 4 / 3 * (10 + 6 * Real.log (2 * π * x)) * (√(20 * Real.exp 1) + 1 + Real.exp 1 * (4 + Cvs.Prolate.Envelope.RungProfileEdgePlunge.edgeP x))

theorem subPoly_weakW : SubPoly weakW := by
  have hP := Cvs.Prolate.Envelope.RungProfileEdgePlunge.subPoly_edgeP
  have hP0 : ∀ x : ℕ, 0 ≤ Cvs.Prolate.Envelope.RungProfileEdgePlunge.edgeP x := Cvs.Prolate.Mellin.WeakRightEdgeWindowInput.edgeP_nonneg
  have hL : SubPoly fun x : ℕ => 10 + 6 * Real.log (2 * π * x) := by
    have h1 : SubPoly fun x : ℕ => 10 + 6 * (Real.log (2 * π) + Real.log x) :=
      (Cvs.Route.Visibility.ExtPairingRatesSubpoly.subPoly_const 10).add ((Cvs.Route.Visibility.ExtPairingRatesSubpoly.subPoly_const 6).mul ((Cvs.Route.Visibility.ExtPairingRatesSubpoly.subPoly_const _).add Cvs.Route.Visibility.ExtPairingRatesSubpoly.subPoly_log)
        (Eventually.of_forall fun _ => by norm_num)
        (Eventually.of_forall fun x => by
          have := Real.log_natCast_nonneg x
          have : 0 ≤ Real.log (2 * π) := Real.log_nonneg (by nlinarith [Real.pi_gt_three])
          linarith))
    refine h1.mono ((eventually_ge_atTop 1).mono fun x hx => le_of_eq ?_)
    have hx1 : (0 : ℝ) < x := by exact_mod_cast hx
    rw [Real.log_mul (by positivity) hx1.ne']
  have hL0 : ∀ᶠ x : ℕ in atTop, 0 ≤ 10 + 6 * Real.log (2 * π * x) :=
    (eventually_ge_atTop 1).mono fun x hx => by
      have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
      have := Real.log_nonneg (by nlinarith [Real.pi_gt_three] : (1 : ℝ) ≤ 2 * π * x); linarith
  unfold weakW
  refine ((Cvs.Route.Visibility.ExtPairingRatesSubpoly.subPoly_const _).mul ((Cvs.Route.Visibility.ExtPairingRatesSubpoly.subPoly_const 1).add hP)
    (Eventually.of_forall fun _ => by positivity) (Eventually.of_forall fun x => by linarith [hP0 x])).add ?_
  refine ((Cvs.Route.Visibility.ExtPairingRatesSubpoly.subPoly_const (4 / 3)).mul hL (Eventually.of_forall fun _ => by norm_num) hL0).mul
    ((Cvs.Route.Visibility.ExtPairingRatesSubpoly.subPoly_const _).add ((Cvs.Route.Visibility.ExtPairingRatesSubpoly.subPoly_const _).mul ((Cvs.Route.Visibility.ExtPairingRatesSubpoly.subPoly_const 4).add hP)
      (Eventually.of_forall fun _ => (Real.exp_pos 1).le) (Eventually.of_forall fun x => by linarith [hP0 x])))
    (hL0.mono fun x hx => by positivity) (Eventually.of_forall fun x => by
      have := hP0 x; have := Real.exp_pos 1; positivity)

/-- `2/(g − c) ≤ 1/√x` for `g ≥ 4c`, `c = 2πx ≥ 80`. -/
theorem two_div_le {x : ℕ} (hx : 80 ≤ 2 * π * x) {g : ℝ} (hg : 8 * π * x ≤ g) :
    2 / (g - 2 * π * x) ≤ 1 / √(x : ℝ) := by
  have hx0 : (0 : ℝ) < x := Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx
  have hs : 0 < √(x : ℝ) := Real.sqrt_pos.2 hx0
  have hx1 : (1 : ℝ) ≤ x := by
    have : (1 : ℕ) ≤ x := by exact_mod_cast hx0
    exact_mod_cast this
  have hsx : √(x : ℝ) ≤ x := by rw [Real.sqrt_le_left hx0.le]; nlinarith
  have hgc : 6 * π * x ≤ g - 2 * π * x := by linarith
  have hgc' : 0 < g - 2 * π * x := lt_of_lt_of_le (by positivity) hgc
  rw [div_le_div_iff₀ hgc' hs]
  nlinarith [Real.pi_gt_three]

/-- The first-alias term against the edge: `4e⁶A(|μ| + 2/(g − c)) ≤ 8e⁶A/√x`. -/
theorem strong_le {A μ d s : ℝ} (hA : 0 ≤ A) (hμ : |μ| ≤ 1 / s) (hd : d ≤ 1 / s) :
    4 * Real.exp 6 * A * (|μ| + d) ≤ 8 * Real.exp 6 * (A / s) := by
  have : |μ| + d ≤ 2 * (1 / s) := by linarith
  calc 4 * Real.exp 6 * A * (|μ| + d) ≤ 4 * Real.exp 6 * A * (2 * (1 / s)) := by gcongr
    _ = 8 * Real.exp 6 * (A / s) := by ring

/-- The tail term: `g Ω/(g − c) ≤ (4/3)LK ω₄` from `Ω ≤ PL/c`, `P ≤ Kcω₄`, `g ≥ 4c`. -/
theorem tail_le {g c Ω P L K ω₄ : ℝ} (hc : 0 < c) (hgc : 4 * c ≤ g) (hΩ0 : 0 ≤ Ω) (hΩ : Ω ≤ P * L / c)
    (hL : 0 ≤ L) (hP : P ≤ K * c * ω₄) : g * (Ω / (g - c)) ≤ 4 / 3 * (L * K) * ω₄ := by
  have hgc' : 0 < g - c := by linarith
  have hgr : g / (g - c) ≤ 4 / 3 := by rw [div_le_div_iff₀ hgc' (by norm_num)]; linarith
  have hgr0 : 0 ≤ g / (g - c) := div_nonneg (by linarith) hgc'.le
  calc g * (Ω / (g - c)) = Ω * (g / (g - c)) := by ring
    _ ≤ (P * L / c) * (4 / 3) := mul_le_mul hΩ hgr hgr0 (hΩ0.trans hΩ)
    _ ≤ (K * c * ω₄ * L / c) * (4 / 3) := by gcongr
    _ = 4 / 3 * (L * K) * ω₄ := by field_simp

/-- The ground tail term: `a·gΩ/(g − c) ≤ (4/3)LK ω₄` from `Ω ≤ PL/c`, `aP ≤ cKω₄`. -/
theorem tail0_le {g c Ω P L K ω₄ a : ℝ} (hc : 0 < c) (hgc : 4 * c ≤ g) (hΩ0 : 0 ≤ Ω) (hΩ : Ω ≤ P * L / c)
    (hL : 0 ≤ L) (ha : 0 ≤ a) (hP : a * P ≤ c * K * ω₄) : a * (g * (Ω / (g - c))) ≤ 4 / 3 * (L * K) * ω₄ := by
  have hgc' : 0 < g - c := by linarith
  have hgr : g / (g - c) ≤ 4 / 3 := by rw [div_le_div_iff₀ hgc' (by norm_num)]; linarith
  have hgr0 : 0 ≤ g / (g - c) := div_nonneg (by linarith) hgc'.le
  calc a * (g * (Ω / (g - c))) = a * Ω * (g / (g - c)) := by ring
    _ ≤ (a * (P * L / c)) * (4 / 3) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hΩ ha) hgr hgr0 (mul_nonneg ha (hΩ0.trans hΩ))
    _ = (a * P) * L / c * (4 / 3) := by ring
    _ ≤ (c * K * ω₄) * L / c * (4 / 3) := by gcongr
    _ = 4 / 3 * (L * K) * ω₄ := by field_simp

/-- The final combination of the pieces. -/
theorem combine {B Q S1 S0 a e u1 u0 T1 T0 X1 X0 Pd ω₄ : ℝ} (hB : B ≤ Q + (4 * Real.exp 6 + 4) * e)
    (hQ : Q ≤ S1 + a * S0) (ha : 0 ≤ a) (hS1 : S1 ≤ 8 * Real.exp 6 * u1 + T1)
    (hS0 : S0 ≤ 8 * Real.exp 6 * u0 + T0) (he : e = u1 + a * u0) (hT1 : T1 ≤ X1) (hT0 : a * T0 ≤ X0)
    (heω : e ≤ (1 + Pd) * ω₄) :
    B ≤ (12 * Real.exp 6 + 4) * ((1 + Pd) * ω₄) + X1 + X0 := by
  have h1 : a * S0 ≤ a * (8 * Real.exp 6 * u0 + T0) := mul_le_mul_of_nonneg_left hS0 ha
  have he6 : 0 ≤ Real.exp 6 := (Real.exp_pos 6).le
  nlinarith

/-- `√y ≤ 1 + y` for `y ≥ 0`. -/
theorem sqrt_le_one_add {y : ℝ} (hy : 0 ≤ y) : √y ≤ 1 + y := by
  rw [Real.sqrt_le_left (by linarith)]; nlinarith

/-- The last step: `√(e(4 + P)) ≤ 1 + e(4 + P)` inside the bound. -/
theorem final_le {B Pd L ω₄ s₁ s₂ : ℝ} (hB : B ≤ (12 * Real.exp 6 + 4) * ((1 + Pd) * ω₄)
      + 4 / 3 * (L * s₁) * ω₄ + 4 / 3 * (L * s₂) * ω₄)
    (hs : s₂ ≤ 1 + Real.exp 1 * (4 + Pd)) (hL : 0 ≤ L) (hω : 0 ≤ ω₄) :
    B ≤ ((12 * Real.exp 6 + 4) * (1 + Pd) + 4 / 3 * L * (s₁ + 1 + Real.exp 1 * (4 + Pd))) * ω₄ := by
  have : 4 / 3 * (L * s₂) * ω₄ ≤ 4 / 3 * (L * (1 + Real.exp 1 * (4 + Pd))) * ω₄ := by gcongr
  nlinarith

/-- **The weak right-edge law holds.** -/
theorem weakEdgeLaw : Cvs.Prolate.Mellin.WeakRightEdgeWindowInput.WeakEdgeLaw := by
  refine ⟨weakW, subPoly_weakW, ?_⟩
  filter_upwards [Cvs.Prolate.Mellin.RungWindowLawRightEdge.edgeE_sq_le, Cvs.Route.Visibility.ExteriorFactorMTwo.eventually_scale] with x hEx hx j σ hσ g hg
  set c := 2 * π * (x : ℝ) with hcd
  have hx0 : (0 : ℝ) < x := Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx
  have hj : (j : ℕ) < x := Cvs.Approximant.SpineSubspace.SF_lt x j j.2
  have hj0 : 0 < x := lt_of_le_of_lt (Nat.zero_le _) hj
  have hc0 : 0 < c := by linarith
  have hc1 : (1 : ℝ) ≤ c := by linarith
  have hgc : 4 * c ≤ g := by rw [hcd]; linarith
  have hg0 : 0 < g := by linarith
  obtain ⟨h1, -, hχ1'⟩ := Cvs.Prolate.Mellin.RungUnitCircleLaw.rung_data hx hj
  obtain ⟨h0, -, hχ0'⟩ := Cvs.Prolate.Mellin.RungUnitCircleLaw.rung_data (j := 0) hx hj0
  simp only [mul_zero] at h0 hχ0'
  have hχ1 := Cvs.Prolate.Mellin.TrapezoidErrorFarLines.lev_lt hx hj
  have hχ0 : lev c 0 < c ^ 2 := by have := Cvs.Prolate.Mellin.TrapezoidErrorFarLines.lev_lt hx hj0; simpa using this
  have hl1 := Cvs.L2a.WindowChainInputsProlate.half_le_lamR hx hj
  have hl0 : 1 / 2 ≤ lamR c 0 := by have := Cvs.L2a.WindowChainInputsProlate.half_le_lamR hx hj0; simpa using this
  set ω := 1 - lamR c (2 * (j : ℕ)) with hωd
  have hlr1 := Cvs.Prolate.Envelope.RungExteriorLaw.lamR_le_one hc0 h1
  have hlr0 := Cvs.Prolate.Envelope.RungExteriorLaw.lamR_le_one hc0 h0
  have hω0 : 0 ≤ ω := by rw [hωd]; linarith
  have hω1 : ω ≤ 1 := by rw [hωd]; linarith
  have hω₀0 : 0 ≤ 1 - lamR c 0 := by linarith
  have hωω : 1 - lamR c 0 ≤ ω := by
    rw [hωd]; linarith [Cvs.Prolate.EvenRungsByIndex.lamR_anti hc0 h1 (Nat.zero_le (2 * (j : ℕ)))]
  set Pd := Cvs.Prolate.Envelope.RungProfileEdgePlunge.edgeP x with hPd
  have hPd0 : 0 ≤ Pd := Cvs.Prolate.Mellin.WeakRightEdgeWindowInput.edgeP_nonneg x
  have hE0 : 0 ≤ Cvs.Prolate.Mellin.RungWindowLawRightEdge.edgeE x j := Cvs.Prolate.Mellin.RungWindowLawRightEdge.edgeE_nonneg x j
  set w : ℂ := σ + g * I with hwd
  have hw0 : 0 < w.im := by simp [hwd, hg0]
  -- the decomposition of `B`
  have hsplit : rayT (Cvs.Prolate.Mellin.CentreValueAliasSum.aliasSum x j) w = rayT (Cvs.Prolate.Mellin.ProlateAliasSumLaw.trapErr x (Hk c (2 * (j : ℕ)))) w
      - (Cvs.Approximant.DeepIndexSpineSpan.alpha c j : ℂ) * rayT (Cvs.Prolate.Mellin.ProlateAliasSumLaw.trapErr x (Hk c 0)) w := by
    rw [Cvs.Prolate.Mellin.ProlateAliasSumLaw.aliasSum_eq_sub hx hj]
    exact Cvs.Prolate.Mellin.ProlateAliasSumLaw.rayT_sub_smul (Cvs.Prolate.Mellin.ProlateAliasSumLaw.continuous_trapErr x (Cvs.Prolate.EntireRungProlateEquation.differentiable_Hk h1).continuous)
      (Cvs.Prolate.Mellin.ProlateAliasSumLaw.continuous_trapErr x (Cvs.Prolate.EntireRungProlateEquation.differentiable_Hk h0).continuous) _ hw0
  have hB1 := (abs_le.1 (Cvs.Prolate.Mellin.RightEdgeAliasLaw.abs_sub_le hx hj hσ hg)).2
  have hB2 := (abs_le.1 (Cvs.Prolate.Mellin.CentreValueAliasSum.abs_sub_le hx hj σ hg)).1
  have hBQ : g * ‖Bw x j w‖ ≤ g * ‖rayT (Cvs.Prolate.Mellin.CentreValueAliasSum.aliasSum x j) w‖
      + (4 * Real.exp 6 + 4) * (Cvs.Prolate.Mellin.RungWindowLawRightEdge.edgeE x j / √(x : ℝ)) := by
    have e1 : 4 * Real.exp 6 * Cvs.Prolate.Mellin.RungWindowLawRightEdge.edgeE x j / √(x : ℝ) + 4 * Cvs.Prolate.Mellin.RungWindowLawRightEdge.edgeE x j / √(x : ℝ)
        = (4 * Real.exp 6 + 4) * (Cvs.Prolate.Mellin.RungWindowLawRightEdge.edgeE x j / √(x : ℝ)) := by ring
    linarith
  have hQ : g * ‖rayT (Cvs.Prolate.Mellin.CentreValueAliasSum.aliasSum x j) w‖ ≤ g * ‖rayT (Cvs.Prolate.Mellin.ProlateAliasSumLaw.trapErr x (Hk c (2 * (j : ℕ)))) w‖
      + |Cvs.Approximant.DeepIndexSpineSpan.alpha c j| * (g * ‖rayT (Cvs.Prolate.Mellin.ProlateAliasSumLaw.trapErr x (Hk c 0)) w‖) := by
    rw [hsplit]
    calc g * ‖rayT (Cvs.Prolate.Mellin.ProlateAliasSumLaw.trapErr x (Hk c (2 * (j : ℕ)))) w - (Cvs.Approximant.DeepIndexSpineSpan.alpha c j : ℂ)
          * rayT (Cvs.Prolate.Mellin.ProlateAliasSumLaw.trapErr x (Hk c 0)) w‖
        ≤ g * (‖rayT (Cvs.Prolate.Mellin.ProlateAliasSumLaw.trapErr x (Hk c (2 * (j : ℕ)))) w‖
          + |Cvs.Approximant.DeepIndexSpineSpan.alpha c j| * ‖rayT (Cvs.Prolate.Mellin.ProlateAliasSumLaw.trapErr x (Hk c 0)) w‖) := by
          gcongr
          refine (norm_sub_le _ _).trans (le_of_eq ?_)
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ = _ := by ring
  -- the two profiles
  have hy₀ : 0 < 1 / c ^ 3 := by positivity
  have hy₁ : 1 / c ^ 3 ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith
  have h2g := two_div_le hx hg
  have hS1 := (Cvs.Prolate.Mellin.TrapezoidErrorFarLines.g_norm_rayT_trapErr_le hx hj hσ hg hy₀ hy₁).trans (add_le_add
    (strong_le (abs_nonneg _) (Cvs.Prolate.Mellin.RightEdgePoissonSplit.abs_muR_le hx h1) h2g) le_rfl)
  have hS0 := (Cvs.Prolate.Mellin.TrapezoidErrorFarLines.g_norm_rayT_trapErr_le hx hj0 hσ hg hy₀ hy₁).trans (add_le_add
    (strong_le (abs_nonneg _) (by simpa using Cvs.Prolate.Mellin.RightEdgePoissonSplit.abs_muR_le hx h0) h2g) le_rfl)
  simp only [mul_zero] at hS0
  rw [← hcd] at hS1 hS0
  -- the tails
  have hL0 : 0 ≤ 10 + 6 * Real.log c := by have := Real.log_nonneg hc1; linarith
  have hΩnn : ∀ k : ℕ, 0 ≤ Cvs.Prolate.Mellin.TrapezoidErrorFarLines.omegaK x k (1 / c ^ 3) := fun k => by
    unfold Cvs.Prolate.Mellin.TrapezoidErrorFarLines.omegaK; exact Cvs.Prolate.Mellin.HigherAliasRayTransforms.omega_nonneg hc0 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hy₀ hy₁
  have hT1 := tail_le (K := √(20 * Real.exp 1)) (ω₄ := ω ^ (1 / 4 : ℝ)) hc0 hgc (hΩnn _)
    (omega_le hx (Real.sqrt_nonneg _) (sqrt_deriv_le hc1 (abs_nonneg _) (Cvs.Prolate.Mellin.RungProfileOutsideCircle.Mk_nonneg c (2 * (j : ℕ)))))
    hL0 (sqrt_P_le hc1 (abs_nonneg _) (Cvs.Prolate.Mellin.FarLineRungSizes.abs_rung_one_le hx h1 hχ1 hχ1' hl1)
      (Cvs.Prolate.Mellin.RungProfileOutsideCircle.Mk_nonneg c (2 * (j : ℕ))) (Cvs.Prolate.Mellin.FarLineRungSizes.Mk_le hc0 h1 hl1) hω0 hω1)
  have hA0' : |rung c 0 1| ≤ 4 * c * ω ^ (1 / 2 : ℝ) :=
    (Cvs.Prolate.Mellin.FarLineRungSizes.abs_rung_one_le hx h0 hχ0 hχ0' hl0).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hω₀0 hωω (by norm_num)) (by positivity))
  have hαA : (|Cvs.Approximant.DeepIndexSpineSpan.alpha c j| * |rung c 0 1|) ^ 2 ≤ Pd * c ^ 2 * ω ^ (1 / 2 : ℝ) := by
    have h1' : |Cvs.Approximant.DeepIndexSpineSpan.alpha c j| * |rung c 0 1| ≤ Cvs.Prolate.Mellin.RungWindowLawRightEdge.edgeE x j := by
      unfold Cvs.Prolate.Mellin.RungWindowLawRightEdge.edgeE; rw [← hcd]; linarith [abs_nonneg (rung c (2 * (j : ℕ)) 1)]
    have h3' : (x : ℝ) ≤ c ^ 2 := by nlinarith [Real.pi_gt_three]
    calc (|Cvs.Approximant.DeepIndexSpineSpan.alpha c j| * |rung c 0 1|) ^ 2 ≤ Cvs.Prolate.Mellin.RungWindowLawRightEdge.edgeE x j ^ 2 := pow_le_pow_left₀ (by positivity) h1' 2
      _ ≤ Pd * x * ω ^ (3 / 4 : ℝ) := hEx j hj
      _ ≤ Pd * c ^ 2 * ω ^ (1 / 2 : ℝ) :=
          mul_le_mul (mul_le_mul_of_nonneg_left h3' hPd0) (Cvs.Prolate.Mellin.WeakRightEdgeWindowInput.rpow_three_quarter_le hω0 hω1)
            (Real.rpow_nonneg hω0 _) (by positivity)
  have hT0 := tail0_le (K := √(Real.exp 1 * (4 + Pd))) (ω₄ := ω ^ (1 / 4 : ℝ)) hc0 hgc (hΩnn _)
    (omega_le hx (Real.sqrt_nonneg _) (sqrt_deriv_le hc1 (abs_nonneg _) (Cvs.Prolate.Mellin.RungProfileOutsideCircle.Mk_nonneg c 0)))
    hL0 (abs_nonneg _) (alpha_sqrt_P_le hc0 (abs_nonneg _) hPd0 (Cvs.Prolate.Mellin.FarLineRungSizes.alpha_sq_mul_Mk_le hc0 h1 hl1) hA0' hαA hω0)
  have hED := Cvs.Prolate.Mellin.WeakRightEdgeWindowInput.div_sqrt_le hx0 hE0 hPd0 hω0 hω1 (hEx j hj)
  have he : Cvs.Prolate.Mellin.RungWindowLawRightEdge.edgeE x j / √(x : ℝ)
      = |rung c (2 * (j : ℕ)) 1| / √(x : ℝ) + |Cvs.Approximant.DeepIndexSpineSpan.alpha c j| * (|rung c 0 1| / √(x : ℝ)) := by
    unfold Cvs.Prolate.Mellin.RungWindowLawRightEdge.edgeE; rw [← hcd]; ring
  have hfin := combine hBQ hQ (abs_nonneg _) hS1 hS0 he hT1 hT0 hED
  have hsqrt : √(Real.exp 1 * (4 + Pd)) ≤ 1 + Real.exp 1 * (4 + Pd) :=
    sqrt_le_one_add (mul_nonneg (Real.exp_pos 1).le (by linarith))
  have hq0 : 0 ≤ ω ^ (1 / 4 : ℝ) := Real.rpow_nonneg hω0 _
  refine (final_le hfin hsqrt hL0 hq0).trans (le_of_eq ?_)
  unfold weakW
  rw [← hPd, ← hcd]

end Cvs.Prolate.Mellin.WeakRightEdgeLaw

end
