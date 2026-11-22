import Mathlib
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.Approximant.SpineCouplingTailPairing
import Cvs.Approximant.SpineSubspace
import Cvs.L2a.WindowChainInputsProlate
import Cvs.Prolate.Envelope.RungDuhamelRemainder
import Cvs.Prolate.Envelope.RungExteriorLaw
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.RungFamilyRangePartners
import Cvs.Prolate.RungSpanBernsteinNikolskii
import Cvs.Route.Visibility.CaseFiniteFromWindowChain
import Cvs.Route.Visibility.ExtPairingRatesSubpoly
import Cvs.Route.Visibility.ExteriorFactorMTwo
import Cvs.Route.Visibility.PerRungBoxBound
import Cvs.Route.Visibility.RungBoxTunnellingSum
import Cvs.StepA.Edge.TransplantAngleHighZeros
import Cvs.WeilForm.ThetaSpaceParseval
import Cvs.Xi.WindowTransformExterior

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# `RungXBox η` for every `η ∈ (0, ½)` from the explicit per-rung exterior bound

caseinf-W Lemma 2_j bounds `X⁰_j = X_{e_j} + g0_j/(2(1 − s))` on the box of height `x` by `(2P/c)(3 + log(1 +
2√(1 + α_j²)/P))`, `P² = (1 − λ_j)/λ_j + α_j²(1 − λ_0)/λ_0`, `c = 2πx`. That bound is `≤ Q(x)x⁻¹√((1 − λ_j)^{½+η})`,
`Q` subpolynomial: `P·log(1/P) ≤ P^{1−δ}/δ`, subadditivity of `t^{(1−δ)/2}`, and `RungDuhamelRemainder`'s `ground_term_le`.
-/

noncomputable section

open Real Set Filter Complex Topology
open Cvs.WeilForm.ThetaSpaceParseval (mellinR)
open Cvs.Xi.WindowTransformExterior (ext)
open Cvs.Route.Visibility.ExtPairingRatesSubpoly (SubPoly)
open Cvs.StepA.Edge.TransplantAngleHighZeros (sbox g0)
open Cvs.Prolate.EvenRungsByIndex (lamR)

namespace Cvs.Route.Visibility.RungXBoxExplicit
open Cvs.ZeroCounting

/-! ### The explicit bound -/

/-- `P_j = √((1 − λ_j)/λ_j + α_j²(1 − λ_0)/λ_0)`, the exterior `L²` scale of the rung `G_j` (up to `√2`). -/
def pBar (x : ℕ) (j : Cvs.Approximant.SpineSubspace.SF x) : ℝ :=
  √((1 - lamR (2 * π * x) (2 * (j : ℕ))) / lamR (2 * π * x) (2 * (j : ℕ))
    + Cvs.Approximant.DeepIndexSpineSpan.alpha (2 * π * x) j ^ 2 * (1 - lamR (2 * π * x) 0) / lamR (2 * π * x) 0)

/-- The bound `(2P/c)(3 + log(1 + 2√(1 + α_j²)/P))` of caseinf-W Lemma 2_j on the box of height `x`. -/
def lemXBound (x : ℕ) (j : Cvs.Approximant.SpineSubspace.SF x) : ℝ :=
  2 * pBar x j / (2 * π * x) * (3 + Real.log (1 + 2 * √(1 + Cvs.Approximant.DeepIndexSpineSpan.alpha (2 * π * x) j ^ 2) / pBar x j))

/-- **The explicit per-rung exterior bound** (caseinf-W Lemma 2_j): eventually every rung's
`X_{e_j} + g0_j/(2(1 − s))` continues holomorphically to the box of height `x` with sup at most `lemXBound x j`. -/
def RungLemmaX : Prop :=
  ∀ᶠ x : ℕ in atTop, ∀ j : Cvs.Approximant.SpineSubspace.SF x, ∃ F : ℂ → ℂ,
    DifferentiableOn ℂ F (sbox x)
      ∧ (∀ s ∈ sbox x, s.re < 1 → F s = mellinR (ext (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) (Pi.single j 1))) s
          + (g0 x (Pi.single j 1) : ℂ) / (2 * (1 - s)))
      ∧ ∀ s ∈ sbox x, ‖F s‖ ≤ lemXBound x j

/-! ### The arithmetic -/

/-- **The scalar inequality**: for `P² ≤ 2w + Kw₀`, `0 ≤ w₀ ≤ w ≤ 1`, `(Kw₀)^p ≤ w₀^κ`, `p = (1 − δ)/2`,
`0 ≤ κ ≤ p`, `0 < δ < 1`, `B ≥ 0`: `P(3 + log(1 + B/P)) ≤ 3(2(3 + log(2 + B)) + 1/δ)w^κ`. -/
theorem arith_lemX {P w w₀ K B δ κ : ℝ} (hP0 : 0 ≤ P) (hP2 : P ^ 2 ≤ 2 * w + K * w₀) (hK : 0 ≤ K)
    (hw₀ : 0 ≤ w₀) (hw₀w : w₀ ≤ w) (hw1 : w ≤ 1) (hB : 0 ≤ B) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hκ0 : 0 ≤ κ) (hκp : κ ≤ (1 - δ) / 2) (hsmall : (K * w₀) ^ ((1 - δ) / 2) ≤ w₀ ^ κ) :
    P * (3 + Real.log (1 + B / P)) ≤ 3 * (2 * (3 + Real.log (2 + B)) + 1 / δ) * w ^ κ := by
  set p := (1 - δ) / 2 with hp
  have hp0 : 0 < p := by rw [hp]; linarith
  have hp1 : p ≤ 1 := by rw [hp]; linarith
  have hw0 : 0 ≤ w := hw₀.trans hw₀w
  have hlog2B : 0 ≤ Real.log (2 + B) := Real.log_nonneg (by linarith)
  have hwκ : 0 ≤ w ^ κ := Real.rpow_nonneg hw0 _
  rcases hP0.eq_or_lt with h0 | hPpos
  · rw [← h0, zero_mul]; positivity
  -- `Kw₀ ≤ 1`, so `P ≤ 2`
  have hKw : K * w₀ ≤ 1 := by
    by_contra hc
    push Not at hc
    have h1 : 1 < (K * w₀) ^ p := Real.one_lt_rpow hc hp0
    have h2 : w₀ ^ κ ≤ 1 := Real.rpow_le_one hw₀ (by linarith) hκ0
    linarith
  have hP2' : P ≤ 2 := by nlinarith
  -- the logarithm
  have hlog : Real.log (1 + B / P) ≤ Real.log (2 + B) + (1 / P) ^ δ / δ := by
    have e : 1 + B / P = (P + B) * (1 / P) := by field_simp
    rw [e, Real.log_mul (by positivity) (by positivity)]
    have h1 : Real.log (P + B) ≤ Real.log (2 + B) := Real.log_le_log (by positivity) (by linarith)
    have h2 := Real.log_le_rpow_div (by positivity : (0 : ℝ) ≤ 1 / P) hδ0
    linarith
  have hPδ : P * (1 / P) ^ δ = P ^ (1 - δ) := by
    rw [one_div, Real.inv_rpow hPpos.le, ← Real.rpow_neg hPpos.le, ← Real.rpow_one_add' hPpos.le (by linarith)]
    · ring_nf
  have hPle : P ≤ 2 * P ^ (1 - δ) := by
    have e : P = P ^ δ * P ^ (1 - δ) := by
      rw [← Real.rpow_add hPpos]; simp
    have h2 : P ^ δ ≤ 2 := (Real.rpow_le_rpow hPpos.le hP2' hδ0.le).trans
      (by rw [show (2 : ℝ) = 2 ^ (1 : ℝ) by simp]
          exact (Real.rpow_le_rpow_of_exponent_le (by norm_num) hδ1.le).trans (by simp))
    calc P = P ^ δ * P ^ (1 - δ) := e
      _ ≤ 2 * P ^ (1 - δ) := mul_le_mul_of_nonneg_right h2 (by positivity)
  have hstep1 : P * (3 + Real.log (1 + B / P)) ≤ (2 * (3 + Real.log (2 + B)) + 1 / δ) * P ^ (1 - δ) := by
    have h3 : 0 ≤ 3 + Real.log (2 + B) := by linarith
    calc P * (3 + Real.log (1 + B / P)) ≤ P * (3 + (Real.log (2 + B) + (1 / P) ^ δ / δ)) :=
          mul_le_mul_of_nonneg_left (by linarith) hPpos.le
      _ = P * (3 + Real.log (2 + B)) + (P * (1 / P) ^ δ) / δ := by ring
      _ ≤ 2 * P ^ (1 - δ) * (3 + Real.log (2 + B)) + P ^ (1 - δ) / δ := by
          rw [hPδ]; exact add_le_add (mul_le_mul_of_nonneg_right hPle h3) le_rfl
      _ = (2 * (3 + Real.log (2 + B)) + 1 / δ) * P ^ (1 - δ) := by ring
  -- `P^{1−δ} ≤ 3w^κ`
  have hP1 : P ^ (1 - δ) ≤ 3 * w ^ κ := by
    have e : P ^ (1 - δ) = (P ^ 2) ^ p := by
      rw [show P ^ 2 = P ^ (2 : ℝ) by norm_cast, ← Real.rpow_mul hPpos.le, hp]; ring_nf
    have hKw0 : 0 ≤ K * w₀ := mul_nonneg hK hw₀
    have h1 : (P ^ 2) ^ p ≤ (2 * w + K * w₀) ^ p := Real.rpow_le_rpow (sq_nonneg _) hP2 hp0.le
    have h2 : (2 * w + K * w₀) ^ p ≤ (2 * w) ^ p + (K * w₀) ^ p :=
      Real.rpow_add_le_add_rpow (by positivity) hKw0 hp0.le hp1
    have h3 : (2 * w) ^ p ≤ 2 * w ^ κ := by
      rw [Real.mul_rpow (by norm_num) hw0]
      have a1 : (2 : ℝ) ^ p ≤ 2 := by
        calc (2 : ℝ) ^ p ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hp1
          _ = 2 := by simp
      have a2 : w ^ p ≤ w ^ κ := Real.rpow_le_rpow_of_exponent_ge' hw0 hw1 hκ0 hκp
      exact mul_le_mul a1 a2 (Real.rpow_nonneg hw0 _) (by norm_num)
    have h4 : w₀ ^ κ ≤ w ^ κ := Real.rpow_le_rpow hw₀ hw₀w hκ0
    rw [e]; linarith
  calc P * (3 + Real.log (1 + B / P)) ≤ (2 * (3 + Real.log (2 + B)) + 1 / δ) * P ^ (1 - δ) := hstep1
    _ ≤ (2 * (3 + Real.log (2 + B)) + 1 / δ) * (3 * w ^ κ) :=
        mul_le_mul_of_nonneg_left hP1 (by positivity)
    _ = 3 * (2 * (3 + Real.log (2 + B)) + 1 / δ) * w ^ κ := by ring

/-! ### The per-rung exterior statement from the explicit bound -/

/-- The ground factor is eventually small: `((8c/π)(1 − λ_0))^{(1−δ)/2} ≤ (1 − λ_0)^{κ}` when
`(1 − δ)/2 = κ + δ/2`, `0 < δ ≤ ½`. -/
theorem eventually_ground_small {δ κ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2) (hκ : (1 - δ) / 2 = κ + δ / 2) :
    ∀ᶠ x : ℕ in atTop, (8 * (2 * π * x) / π * (1 - lamR (2 * π * x) 0)) ^ ((1 - δ) / 2)
      ≤ (1 - lamR (2 * π * x) 0) ^ κ := by
  set K₁ := 33 / 20 * Real.exp 5 with hK₁
  set a := δ / 2 * π / 6 with ha
  have ha0 : 0 < a := by positivity
  have hdecay : ∀ᶠ x : ℕ in atTop, (2 * π * x) ^ 6 * Real.exp (-(a * (2 * π * x))) ≤ 1 / (16 * K₁ + 1) := by
    have h1 : Tendsto (fun x : ℕ => a * (2 * π * x)) atTop atTop :=
      Tendsto.const_mul_atTop ha0 (Tendsto.const_mul_atTop (by positivity) tendsto_natCast_atTop_atTop)
    have h2 := ((tendsto_pow_mul_exp_neg_atTop_nhds_zero 6).comp h1).div_const (a ^ 6)
    rw [zero_div] at h2
    have hpos : (0 : ℝ) < 1 / (16 * K₁ + 1) := by positivity
    filter_upwards [h2.eventually (ge_mem_nhds hpos)] with x hx
    have e : (a * (2 * π * x)) ^ 6 * Real.exp (-(a * (2 * π * x))) / a ^ 6
        = (2 * π * x) ^ 6 * Real.exp (-(a * (2 * π * x))) := by
      rw [mul_pow]; field_simp
    simp only [Function.comp] at hx
    rwa [e] at hx
  filter_upwards [hdecay, Cvs.Route.Visibility.ExteriorFactorMTwo.eventually_scale] with x hdx hsc
  set c := 2 * π * (x : ℝ) with hc
  have hc0 : 0 < c := by linarith
  set w₀ := 1 - lamR c 0 with hw₀
  have hw₀0 : 0 ≤ w₀ := by rw [hw₀]; linarith [Cvs.Prolate.EvenRungsByIndex.lamR_zero_le_one hc0]
  have hp0 : 0 < (1 - δ) / 2 + δ / 2 := by linarith
  have hκ0 : 0 ≤ κ := by linarith
  rcases hw₀0.eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero, Real.zero_rpow (by linarith)]
    exact Real.rpow_nonneg le_rfl _
  have hK1 : 1 ≤ 8 * c / π := by rw [le_div_iff₀ Real.pi_pos]; linarith [Real.pi_lt_four]
  have hground := Cvs.Prolate.Envelope.RungDuhamelRemainder.ground_term_le (c := c) (C := 1) hsc (by linarith : 0 < δ / 2) (by linarith) zero_le_one
  have hlog : 1 ≤ 1 + Real.log c := by linarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ c)]
  have hKp : (8 * c / π) ^ ((1 - δ) / 2) ≤ (1 + Real.log c) * (c + 1) ^ 4 := by
    have h1 : (8 * c / π) ^ ((1 - δ) / 2) ≤ 8 * c / π := by
      calc (8 * c / π) ^ ((1 - δ) / 2) ≤ (8 * c / π) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hK1 (by linarith)
        _ = 8 * c / π := Real.rpow_one _
    have h2 : 8 * c / π ≤ (c + 1) ^ 4 := by
      rw [div_le_iff₀ Real.pi_pos]
      have hc1 : 1 ≤ c + 1 := by linarith
      have h4 : (c + 1) ^ 2 ≤ (c + 1) ^ 4 := pow_le_pow_right₀ hc1 (by norm_num)
      have h5 : 3 * c ≤ (c + 1) ^ 2 := by nlinarith
      nlinarith [Real.pi_gt_three]
    have h3 : (c + 1) ^ 4 ≤ (1 + Real.log c) * (c + 1) ^ 4 := le_mul_of_one_le_left (by positivity) hlog
    linarith
  have hsplit : (8 * c / π * w₀) ^ ((1 - δ) / 2) = (8 * c / π) ^ ((1 - δ) / 2) * w₀ ^ (δ / 2) * w₀ ^ κ := by
    rw [Real.mul_rpow (by positivity) hpos.le, mul_assoc, ← Real.rpow_add hpos, hκ]; ring_nf
  rw [hsplit]
  have hsmall : (8 * c / π) ^ ((1 - δ) / 2) * w₀ ^ (δ / 2) ≤ 1 := by
    have hw : 0 ≤ w₀ ^ (δ / 2) := Real.rpow_nonneg hpos.le _
    calc (8 * c / π) ^ ((1 - δ) / 2) * w₀ ^ (δ / 2) ≤ (1 + Real.log c) * (c + 1) ^ 4 * w₀ ^ (δ / 2) :=
          mul_le_mul_of_nonneg_right hKp hw
      _ = w₀ ^ (δ / 2) * (1 * (1 + Real.log c) * (c + 1) ^ 4) := by ring
      _ ≤ 16 * 1 * (33 / 20 * Real.exp 5) * (c ^ 6 * Real.exp (-(δ / 2 * π / 6 * c))) := hground
      _ ≤ 16 * K₁ * (1 / (16 * K₁ + 1)) := by
          rw [mul_one]; exact mul_le_mul_of_nonneg_left hdx (by positivity)
      _ ≤ 1 := by
          have : 0 < 16 * K₁ + 1 := by positivity
          rw [mul_one_div, div_le_one this]; linarith
  calc (8 * c / π) ^ ((1 - δ) / 2) * w₀ ^ (δ / 2) * w₀ ^ κ ≤ 1 * w₀ ^ κ :=
        mul_le_mul_of_nonneg_right hsmall (Real.rpow_nonneg hpos.le _)
    _ = w₀ ^ κ := one_mul _

/-- **`RungXBox η` for every `η ∈ (0, ½)` from the explicit per-rung exterior bound.** -/
theorem rungXBox_of_lemmaX (h : RungLemmaX) {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1 / 2) : Cvs.Route.Visibility.RungBoxTunnellingSum.RungXBox η := by
  set δ := (1 / 2 - η) / 2 with hδ
  set κ := (1 / 2 + η) / 2 with hκ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hδ1 : δ < 1 := by rw [hδ]; linarith
  have hκ0 : 0 ≤ κ := by rw [hκ]; linarith
  have hκp : κ ≤ (1 - δ) / 2 := by rw [hκ, hδ]; linarith
  have hκe : (1 - δ) / 2 = κ + δ / 2 := by rw [hκ, hδ]; ring
  have hL := Cvs.Prolate.Envelope.RungDuhamelRemainder.subPoly_one_add_two_log (K := 16 * π) (by positivity)
  have hL0 : ∀ᶠ x : ℕ in atTop, 0 ≤ 1 + 2 * Real.log (16 * π * x) := by
    filter_upwards [eventually_ge_atTop 1] with x hx
    have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
    have : 1 ≤ 16 * π * x := by nlinarith [Real.pi_gt_three]
    linarith [Real.log_nonneg this]
  have hQsub : SubPoly fun x : ℕ => 3 / π * (2 * (3 + Real.log (16 * π * x)) + 1 / δ) := by
    refine (Cvs.Route.Visibility.ExtPairingRatesSubpoly.SubPoly.add (Cvs.Route.Visibility.ExtPairingRatesSubpoly.subPoly_const (3 / π * (6 + 1 / δ)))
      (Cvs.Route.Visibility.ExtPairingRatesSubpoly.SubPoly.mul (Cvs.Route.Visibility.ExtPairingRatesSubpoly.subPoly_const (3 / π)) hL (Eventually.of_forall fun _ => by positivity) hL0)).mono
      (Eventually.of_forall fun x => ?_)
    have : 0 ≤ 3 / π := by positivity
    nlinarith
  refine ⟨_, hQsub, ?_⟩
  filter_upwards [h, eventually_ground_small hδ0 (by rw [hδ]; linarith) hκe, Cvs.Route.Visibility.ExteriorFactorMTwo.eventually_scale] with x hx hgr hsc j
  obtain ⟨F, hF, ha, hb⟩ := hx j
  refine ⟨F, hF, ha, fun s hs => (hb s hs).trans ?_⟩
  -- the objects
  set c := 2 * π * (x : ℝ) with hc
  have hc0 : 0 < c := by linarith
  have hx0 : (0 : ℝ) < x := Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hsc
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast Cvs.Prolate.RungSpanBernsteinNikolskii.one_le_of_scale hsc
  have hjx := Cvs.Approximant.SpineSubspace.SF_lt x j j.2
  have hex := Cvs.Prolate.RungFamilyRangePartners.exists_main hsc ⟨j, Finset.mem_range.2 hjx⟩
  have hl := Cvs.L2a.WindowChainInputsProlate.half_le_lamR hsc hjx
  have hl0 : 1 / 2 ≤ lamR c 0 := by simpa using Cvs.L2a.WindowChainInputsProlate.half_le_lamR hsc (lt_of_le_of_lt (Nat.zero_le _) hjx)
  have hl1 := Cvs.Prolate.Envelope.RungExteriorLaw.lamR_le_one hc0 hex
  have hl01 := Cvs.Prolate.EvenRungsByIndex.lamR_zero_le_one hc0
  have hanti := Cvs.Prolate.EvenRungsByIndex.lamR_anti hc0 hex (Nat.zero_le (2 * (j : ℕ)))
  have hα := Cvs.Prolate.Envelope.RungDuhamelRemainder.alpha_sq_le hc0 hex hl
  set α := Cvs.Approximant.DeepIndexSpineSpan.alpha c j with hαdef
  set w := 1 - lamR c (2 * (j : ℕ)) with hw
  set w₀ := 1 - lamR c 0 with hw₀
  set P := pBar x j with hP
  set B := 2 * √(1 + α ^ 2) with hB
  have hw0 : 0 ≤ w := by rw [hw]; linarith
  have hw1 : w ≤ 1 := by rw [hw]; linarith
  have hw₀0 : 0 ≤ w₀ := by rw [hw₀]; linarith
  have hw₀w : w₀ ≤ w := by rw [hw, hw₀]; linarith
  have hP2 : P ^ 2 ≤ 2 * w + 8 * c / π * w₀ := by
    have hin : 0 ≤ w / lamR c (2 * (j : ℕ)) + α ^ 2 * w₀ / lamR c 0 := by positivity
    rw [hP, pBar, Real.sq_sqrt hin]
    have h1 : w / lamR c (2 * (j : ℕ)) ≤ 2 * w := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    have h2 : α ^ 2 * w₀ / lamR c 0 ≤ 2 * (α ^ 2 * w₀) := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith [mul_nonneg (mul_nonneg (sq_nonneg α) hw₀0) (by linarith : (0 : ℝ) ≤ 2 * lamR c 0 - 1)]
    have h3 : 2 * (α ^ 2 * w₀) ≤ 8 * c / π * w₀ := by
      have : 2 * α ^ 2 ≤ 8 * c / π := by
        have e : 8 * c / π = 2 * (4 * c / π) := by ring
        rw [e]; linarith
      nlinarith
    linarith
  have hkey := arith_lemX (P := P) (B := B) (K := 8 * c / π) (Real.sqrt_nonneg _) hP2 (by positivity) hw₀0 hw₀w hw1
    (by positivity) hδ0 hδ1 hκ0 hκp hgr
  have hBle : 2 + B ≤ 16 * π * x := by
    have h1 : √(1 + α ^ 2) ≤ 1 + α ^ 2 :=
      Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith [sq_nonneg α]⟩
    have h2 : 1 + α ^ 2 ≤ 1 + 4 * c / π := by linarith
    have h3 : 4 * c / π = 8 * x := by rw [hc]; field_simp; ring
    have h4 : 16 * (x : ℝ) + 4 ≤ 16 * π * x := by
      have : (16 : ℝ) * x * 1 ≤ 16 * x * (π - 1) := mul_le_mul_of_nonneg_left (by linarith [Real.pi_gt_three])
        (by positivity)
      linarith
    have h5 : B ≤ 2 * (1 + 8 * x) := by rw [hB]; linarith
    linarith
  have hlogB : Real.log (2 + B) ≤ Real.log (16 * π * x) :=
    Real.log_le_log (by positivity) hBle
  have hsq : √(w ^ (1 / 2 + η)) = w ^ κ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hw0, hκ]; ring_nf
  rw [hsq]
  have hwκ : 0 ≤ w ^ κ := Real.rpow_nonneg hw0 _
  unfold lemXBound
  rw [← hP, ← hαdef]
  calc 2 * P / c * (3 + Real.log (1 + B / P)) = 1 / (π * x) * (P * (3 + Real.log (1 + B / P))) := by
        rw [hc]; field_simp
    _ ≤ 1 / (π * x) * (3 * (2 * (3 + Real.log (2 + B)) + 1 / δ) * w ^ κ) :=
        mul_le_mul_of_nonneg_left hkey (by positivity)
    _ ≤ 1 / (π * x) * (3 * (2 * (3 + Real.log (16 * π * x)) + 1 / δ) * w ^ κ) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ hwκ) (by positivity)
        linarith
    _ = 3 / π * (2 * (3 + Real.log (16 * π * x)) + 1 / δ) / x * w ^ κ := by
        rw [one_div, mul_inv, div_eq_mul_inv, div_eq_mul_inv]; ring

/-- **`RungBox 1` from the explicit per-rung exterior bound and the tunnelling sum.** -/
theorem rungBox_one_of_lemmaX (hT : ∃ η : ℝ, 0 < η ∧ η < 1 / 2 ∧ Cvs.Route.Visibility.CaseFiniteFromWindowChain.ExtTunnelSum η) (h : RungLemmaX) :
    Cvs.Route.Visibility.PerRungBoxBound.RungBox 1 :=
  Cvs.Route.Visibility.RungBoxTunnellingSum.rungBox_one_of_tunnel hT fun _ h0 h1 => rungXBox_of_lemmaX h h0 h1

end Cvs.Route.Visibility.RungXBoxExplicit

end
