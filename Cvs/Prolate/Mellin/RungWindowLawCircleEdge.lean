import Mathlib
import Cvs.Approximant.SpineSubspace
import Cvs.Prolate.Mellin.RungTransformUnitCircle
import Cvs.Prolate.RungWindowProfileCells
import Cvs.Route.L1FloorFromBulkD0
import Cvs.Route.Visibility.ExtPairingRatesSubpoly
import Cvs.Route.Visibility.WindowLaplaceUPairing
import Cvs.Upstream.DirichletWeightedMeanValue
import Cvs.Upstream.LogTailFromDecay
import Cvs.WeilForm.WeilFormOnWindowL2

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The per-rung window law from the unit-circle and right-edge laws

With `F_f(w) = iA(w)J(w) − ie^{wL/2}B(w)` (Cvs.Prolate.Mellin.RungTransformUnitCircle), the laws `g‖A(σ + ig)‖ ≤ C(x)|G_j(1)|` and
`g‖B(σ + ig)‖ ≤ C(x)|G_j(1)|/√x` beyond `8πx`, the weighted mean value inequality for `J` (Cvs.Upstream.DirichletWeightedMeanValue) and the edge
bound `G_j(1)² ≤ P(x)·x·(1 − λ_{4j})^{3/4}` (Cvs.Prolate.Envelope.RungProfileEdgePlunge) give `WinTailProfile (1/4)`.
-/

noncomputable section

open Real Set MeasureTheory Filter Complex
open Cvs.Route.L1FloorFromBulkD0 (rung)
open Cvs.Route.Visibility.WindowLaplaceUPairing (winLaplace)
open Cvs.Prolate.EvenRungsByIndex (lamR)
open Cvs.Route.Visibility.ExtPairingRatesSubpoly (SubPoly)
open Cvs.Prolate.RungWindowProfileCells (Gr tn Ff)
open Cvs.Prolate.Mellin.RungTransformUnitCircle (Aw Bw Jw)
open Cvs.Upstream.DirichletWeightedMeanValue (expSum)

namespace Cvs.Prolate.Mellin.RungWindowLawCircleEdge
open Cvs.ZeroCounting

/-- **The unit-circle law**: some subpolynomial `C` has, at all large `x`, for every rung, `|σ| ≤ 1` and
`g ≥ 8πx`, `g‖A(σ + ig)‖ ≤ C(x)|G_j(1)|`, `A(w) = ∫_0^∞ G_j(e^{−is}) e^{−is/2} e^{iws} ds`. -/
def CircleLaw : Prop :=
  ∃ C : ℕ → ℝ, SubPoly C ∧ ∀ᶠ x : ℕ in atTop, ∀ j : Cvs.Approximant.SpineSubspace.SF x, ∀ σ : ℝ, |σ| ≤ 1 → ∀ g : ℝ, 8 * π * x ≤ g →
    g * ‖Aw x j (σ + g * I)‖ ≤ C x * |Gr x j 1|

/-! ### The jump sum as an exponential sum -/

/-- The jump coefficients `b_n = a e^{−(t_n − L/2)/2} e^{σ t_n}`. -/
def bco (x : ℕ) (σ : ℝ) (n : ℕ) : ℝ := 1 / x * Real.exp (-((tn x n - Real.log x / 2) / 2)) * Real.exp (σ * tn x n)

/-- `J(σ + ig) = Σ_n b_n e^{i t_n g}`. -/
theorem Jw_eq (x : ℕ) (σ g : ℝ) : Jw x (σ + g * I) = expSum x (bco x σ) (Real.log x / 2) g := by
  unfold Jw expSum bco
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [show ((σ : ℂ) + g * I) * (tn x n : ℝ) = ((σ * tn x n : ℝ) : ℂ) + (Real.log n - Real.log x / 2 : ℝ) * I * g by
    unfold tn; push_cast; ring, Complex.exp_add, ← Complex.ofReal_exp]
  push_cast; ring

/-- **The jump coefficients are square-summable at rate `x^{|σ|}(1 + log x)/x`**. -/
theorem sum_bco_sq_le {x : ℕ} (hx : 0 < x) (σ : ℝ) :
    ∑ n ∈ Finset.Icc 1 x, bco x σ n ^ 2 ≤ (x : ℝ) ^ |σ| * (1 + Real.log x) / x := by
  have hxr : (0 : ℝ) < x := by exact_mod_cast hx
  have hterm : ∀ n ∈ Finset.Icc 1 x, bco x σ n ^ 2 ≤ (x : ℝ) ^ |σ| / x * (1 / n) := fun n hn => by
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hn
    have hnr : (0 : ℝ) < n := by exact_mod_cast h1
    have hl0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast h1)
    have hl1 : Real.log n ≤ Real.log x := Real.log_le_log hnr (by exact_mod_cast h2)
    have hσ : 2 * σ * (Real.log n - Real.log x / 2) ≤ |σ| * Real.log x := by
      rcases le_total 0 σ with h | h
      · rw [abs_of_nonneg h]; nlinarith
      · rw [abs_of_nonpos h]; nlinarith
    unfold bco tn
    rw [mul_pow, mul_pow, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
    have e1 : ((2 : ℕ) : ℝ) * -((Real.log n - Real.log x / 2 - Real.log x / 2) / 2) = Real.log x - Real.log n := by
      push_cast; ring
    rw [e1, Real.exp_sub, Real.exp_log hxr, Real.exp_log hnr]
    have e2 : (x : ℝ) ^ |σ| = Real.exp (|σ| * Real.log x) := by
      rw [Real.rpow_def_of_pos hxr, mul_comm]
    rw [e2]
    have h3 : Real.exp (((2 : ℕ) : ℝ) * (σ * (Real.log n - Real.log x / 2))) ≤ Real.exp (|σ| * Real.log x) :=
      Real.exp_le_exp.2 (by push_cast; linarith)
    calc (1 / (x : ℝ)) ^ 2 * (x / n) * Real.exp (((2 : ℕ) : ℝ) * (σ * (Real.log n - Real.log x / 2)))
        ≤ (1 / (x : ℝ)) ^ 2 * (x / n) * Real.exp (|σ| * Real.log x) := by gcongr
      _ = Real.exp (|σ| * Real.log x) / x * (1 / n) := by field_simp
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  have hH : ∑ n ∈ Finset.Icc 1 x, 1 / (n : ℝ) ≤ 1 + Real.log x := by
    have := harmonic_le_one_add_log x
    rw [harmonic_eq_sum_Icc] at this; push_cast at this; simpa [one_div] using this
  calc (x : ℝ) ^ |σ| / x * ∑ n ∈ Finset.Icc 1 x, 1 / (n : ℝ) ≤ (x : ℝ) ^ |σ| / x * (1 + Real.log x) :=
        mul_le_mul_of_nonneg_left hH (by positivity)
    _ = _ := by ring

/-! ### The pointwise bound -/

/-- `‖e^{wL/2}‖ = e^{σL/2}` for `w = σ + ig`. -/
theorem norm_exp_half (x : ℕ) (σ g : ℝ) :
    ‖Complex.exp (((σ : ℂ) + g * I) * (Real.log x / 2 : ℝ))‖ = Real.exp (σ * (Real.log x / 2)) := by
  rw [Complex.norm_exp]; congr 1; simp [-Complex.natCast_log]

/-- `F_{r_j}(σ + ig) = (F_f(σ + ig) + conj F_f(−σ + ig))/2`. -/
theorem winLaplace_eq_conj {x : ℕ} (hx : 80 ≤ 2 * π * x) (j : Cvs.Approximant.SpineSubspace.SF x) (σ g : ℝ) :
    winLaplace (rung x j) (σ + g * I)
      = (Ff x j (σ + g * I) + (starRingEnd ℂ) (Ff x j (((-σ : ℝ) : ℂ) + g * I))) / 2 := by
  rw [Cvs.Prolate.RungWindowProfileCells.winLaplace_rung_eq hx j]
  have e : -((σ : ℂ) + g * I) = (starRingEnd ℂ) (((-σ : ℝ) : ℂ) + g * I) := by
    simp [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]; ring
  rw [e, Cvs.Prolate.Mellin.RungTransformUnitCircle.Ff_conj]

/-- The arithmetic of the pointwise bound: `F ≤ (a + b)/2`, `ga ≤ u₁ + v₁`, `gb ≤ u₂ + v₂` give
`g²F² ≤ u₁² + u₂² + v₁² + v₂²`. -/
theorem arith_sq {g F a b u₁ u₂ v₁ v₂ : ℝ} (hg : 0 ≤ g) (hF0 : 0 ≤ F) (hF : F ≤ (a + b) / 2) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (h1 : g * a ≤ u₁ + v₁) (h2 : g * b ≤ u₂ + v₂) :
    g ^ 2 * F ^ 2 ≤ u₁ ^ 2 + u₂ ^ 2 + v₁ ^ 2 + v₂ ^ 2 := by
  have hga : 0 ≤ g * a := mul_nonneg hg ha
  have hgb : 0 ≤ g * b := mul_nonneg hg hb
  have hgF : g * F ≤ (g * a + g * b) / 2 := by nlinarith
  have hsq : (g * F) ^ 2 ≤ ((g * a + g * b) / 2) ^ 2 := pow_le_pow_left₀ (mul_nonneg hg hF0) hgF 2
  have ha2 : (g * a) ^ 2 ≤ 2 * u₁ ^ 2 + 2 * v₁ ^ 2 := by
    have := pow_le_pow_left₀ hga h1 2; nlinarith [sq_nonneg (u₁ - v₁)]
  have hb2 : (g * b) ^ 2 ≤ 2 * u₂ ^ 2 + 2 * v₂ ^ 2 := by
    have := pow_le_pow_left₀ hgb h2 2; nlinarith [sq_nonneg (u₂ - v₂)]
  have hab : ((g * a + g * b) / 2) ^ 2 ≤ ((g * a) ^ 2 + (g * b) ^ 2) / 2 := by nlinarith [sq_nonneg (g * a - g * b)]
  rw [← mul_pow]; linarith

/-- `(e^{sL/2}C₂E/√x)² ≤ x^{|σ|}C₂²E²/x` for `|s| = |σ|`. -/
theorem edge_term_sq_le {x : ℕ} (hx0 : (0 : ℝ) < x) {s σ : ℝ} (hs : |s| = |σ|) (C₂ E : ℝ) :
    (Real.exp (s * (Real.log x / 2)) * (C₂ * |E| / √(x : ℝ))) ^ 2 ≤ (x : ℝ) ^ |σ| * C₂ ^ 2 * E ^ 2 / x := by
  have hsx : √(x : ℝ) ^ 2 = x := Real.sq_sqrt hx0.le
  have he : Real.exp (s * (Real.log x / 2)) ^ 2 ≤ (x : ℝ) ^ |σ| := by
    rw [← Real.exp_nat_mul, Real.rpow_def_of_pos hx0]
    refine Real.exp_le_exp.2 ?_
    push_cast
    have : s ≤ |σ| := hs ▸ le_abs_self s
    have hl := Real.log_natCast_nonneg x
    nlinarith
  rw [mul_pow, div_pow, mul_pow, hsx, sq_abs]
  calc Real.exp (s * (Real.log x / 2)) ^ 2 * (C₂ ^ 2 * E ^ 2 / x)
      ≤ (x : ℝ) ^ |σ| * (C₂ ^ 2 * E ^ 2 / x) := mul_le_mul_of_nonneg_right he (by positivity)
    _ = _ := by ring

/-! ### The window log tail at a fixed scale -/

/-- The window transform has an even modulus in `g`: `‖F_u(σ − ig)‖ = ‖F_u(σ + ig)‖`. -/
theorem norm_winLaplace_neg {x : ℕ} (u : Cvs.Route.L1FloorFromBulkD0.Dom x) (σ g : ℝ) :
    ‖winLaplace u (σ + (-g : ℝ) * I)‖ = ‖winLaplace u (σ + g * I)‖ := by
  have e : ((σ : ℂ) + ((-g : ℝ) : ℂ) * I) = (starRingEnd ℂ) ((σ : ℂ) + g * I) := by
    simp [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  rw [e, Cvs.Prolate.Mellin.RungTransformUnitCircle.winLaplace_conj, Complex.norm_conj]

/-- `log(y/T)/y² ≤ 2T^{−1/2} y^{−3/2}` for `y ≥ T > 0`. -/
theorem log_div_le_rpow {T y : ℝ} (hT : 0 < T) (hy : T ≤ y) :
    Real.log (y / T) ≤ 2 * T ^ (-(1 / 2) : ℝ) * y ^ (-(3 / 2) : ℝ) * y ^ 2 := by
  have hy0 : 0 < y := hT.trans_le hy
  have h1 : 1 ≤ y / T := by rw [le_div_iff₀ hT]; linarith
  refine (Cvs.Upstream.LogTailFromDecay.log_le_two_sqrt h1).trans (le_of_eq ?_)
  rw [Real.sqrt_div' _ hT.le, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, Real.rpow_neg hT.le, Real.rpow_neg hy0.le]
  have h32 : y ^ (3 / 2 : ℝ) = y ^ 2 * y ^ (-(1 / 2) : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hy0]; norm_num
  rw [h32, Real.rpow_neg hy0.le]
  have h1 : 0 < y ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hy0 _
  have h2 : 0 < T ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hT _
  field_simp

/-! ### The per-rung window law -/

/-- The positive part of a subpolynomial function is subpolynomial. -/
theorem subPoly_max {C : ℕ → ℝ} (hC : SubPoly C) : SubPoly fun x => max (C x) 0 := fun ε hε =>
  (hC ε hε).mono fun _ hx => max_le hx (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-- The window factor `Q(x) = 8C₁²(1 + log x)(1/(2π) + (1 + log x)/(8π²)) + (2/π)C₂²`. -/
def winQ (C₁ C₂ L : ℝ) : ℝ := 8 * C₁ ^ 2 * (1 + L) * (1 / (2 * π) + (1 + L) / (8 * π ^ 2)) + 2 / π * C₂ ^ 2

/-- **The fixed-scale bound in closed form**: the right side of `winTail_le_fixed` is `x^{|σ|}G²Q/x²`. -/
theorem fixed_rhs_eq {x : ℕ} (hx0 : (0 : ℝ) < x) (σ C₁ C₂ G : ℝ) :
    4 * (8 * π * x) ^ (-(1 / 2) : ℝ) * (C₁ ^ 2 * G ^ 2 * (2 * ((x : ℝ) ^ |σ| * (1 + Real.log x) / x)
        * (4 * (8 * π * x) ^ (-(1 / 2) : ℝ) + 2 * (4 * x * (1 + Real.log x)) * (8 * π * x) ^ (-(3 / 2) : ℝ)))
      + 2 * (x : ℝ) ^ |σ| * C₂ ^ 2 * G ^ 2 / x * (2 * (8 * π * x) ^ (-(1 / 2) : ℝ)))
      = (x : ℝ) ^ |σ| * G ^ 2 / x ^ 2 * winQ C₁ C₂ (Real.log x) := by
  set T := 8 * π * (x : ℝ) with hT
  have hT0 : 0 < T := by positivity
  have r1 : T ^ (-(1 / 2) : ℝ) * T ^ (-(1 / 2) : ℝ) = 1 / T := by
    rw [← Real.rpow_add hT0]; norm_num; exact Real.rpow_neg_one T
  have r2 : T ^ (-(1 / 2) : ℝ) * T ^ (-(3 / 2) : ℝ) = 1 / T ^ 2 := by
    rw [← Real.rpow_add hT0]; norm_num
  calc _ = 8 * C₁ ^ 2 * G ^ 2 * ((x : ℝ) ^ |σ| * (1 + Real.log x) / x)
          * (4 * (T ^ (-(1 / 2) : ℝ) * T ^ (-(1 / 2) : ℝ)) + 2 * (4 * x * (1 + Real.log x))
            * (T ^ (-(1 / 2) : ℝ) * T ^ (-(3 / 2) : ℝ)))
        + 8 * (2 * (x : ℝ) ^ |σ| * C₂ ^ 2 * G ^ 2 / x) * (T ^ (-(1 / 2) : ℝ) * T ^ (-(1 / 2) : ℝ)) := by ring
    _ = _ := by
        rw [r1, r2, hT, winQ]
        have hpi : π ≠ 0 := Real.pi_ne_zero
        field_simp
        ring

end Cvs.Prolate.Mellin.RungWindowLawCircleEdge

end
