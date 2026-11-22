import Mathlib
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.L2a.FullSpanIndexFloor
import Cvs.L2a.WindowChainInputsProlate
import Cvs.Prolate.EdgeCentreSign
import Cvs.Prolate.Envelope.RungDuhamelRemainder
import Cvs.Prolate.Envelope.RungExteriorLaw
import Cvs.Prolate.EvenLevelIndexLemma
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.EvenSpectrumGroundLevel
import Cvs.Prolate.RegularSolutionEdge
import Cvs.Prolate.RungWindowProfileCells
import Cvs.Prolate.SlepianEvenOrdering
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
# The edge value of a rung profile against `(1 − λ_{4j})^{3/4}`

Slepian's edge bound `λh(1)² ≤ (72/49)(2D + 3c)(1 − λ)` (Cvs.Prolate.Envelope.RungExteriorLaw) and the plunge `1 − λ ≤ K₁ c e^{−πD/(4c)}` (Cvs.Prolate.Envelope.RungDuhamelRemainder)
give `(2D + 3c)(1 − λ)^{1/4} ≤ c((8/π) log(K₁c) + 32/π + 13)`, since `−t log t ≤ 1`; with the exponentially small
ground term this yields `G_j(1)² ≤ P(x)·x·(1 − λ_{4j})^{3/4}` for a subpolynomial `P`.
-/

noncomputable section

open Real Filter
open Cvs.Prolate.EvenRungsByIndex (rung lamR lev IsLevelIdx)
open Cvs.Route.Visibility.ExtPairingRatesSubpoly (SubPoly)
open Cvs.Prolate.RungWindowProfileCells (Gr)

namespace Cvs.Prolate.Envelope.RungProfileEdgePlunge
open Cvs.ZeroCounting

/-- The plunge constant `K₁ = (33/20)e⁵`. -/
def K₁ : ℝ := 33 / 20 * Real.exp 5

theorem one_le_K₁ : 1 ≤ K₁ := by
  have : (20 : ℝ) / 33 ≤ Real.exp 5 := by linarith [Real.add_one_le_exp (5 : ℝ)]
  unfold K₁; linarith

/-- The depth factor `Q(c) = (8/π) log(K₁c) + 32/π + 13`. -/
def depthQ (c : ℝ) : ℝ := 8 / π * Real.log (K₁ * c) + 32 / π + 13

/-- `−t log t ≤ 1` on `[0, 1]`. -/
theorem neg_mul_log_le_one {t : ℝ} (h0 : 0 ≤ t) : -(t * Real.log t) ≤ 1 := by
  rcases h0.eq_or_lt with h | h
  · subst h; simp
  · have := Real.log_le_sub_one_of_pos (inv_pos.2 h)
    rw [Real.log_inv] at this
    have h2 : t * (-Real.log t) ≤ t * (t⁻¹ - 1) := mul_le_mul_of_nonneg_left this h.le
    rw [mul_sub, mul_inv_cancel₀ h.ne', mul_one] at h2
    linarith

/-- **The depth factor**: on a rung with `c ≥ 80` and `χ < c²`, `(2D + 3c)(1 − λ)^{1/4} ≤ c·Q(c)`. -/
theorem depth_mul_rpow_le {c : ℝ} {k : ℕ} (hc : 80 ≤ c) (h : ∃ χ, IsLevelIdx c k χ) (hχc : lev c k < c ^ 2) :
    (2 * (c ^ 2 - lev c k) + 3 * c) * (1 - lamR c k) ^ (1 / 4 : ℝ) ≤ c * depthQ c := by
  have hc0 : 0 < c := by linarith
  set D := c ^ 2 - lev c k with hD
  have hD0 : 0 < D := by rw [hD]; linarith
  have hl1 := Cvs.Prolate.Envelope.RungExteriorLaw.lamR_le_one hc0 h
  set t := (1 - lamR c k) ^ (1 / 4 : ℝ) with ht
  have ht0 : 0 ≤ t := Real.rpow_nonneg (by linarith) _
  have hlam0 : 0 ≤ lamR c k := by unfold Cvs.Prolate.EvenRungsByIndex.lamR; positivity
  have ht1 : t ≤ 1 := Real.rpow_le_one (by linarith) (by linarith) (by norm_num)
  have hK : 1 ≤ K₁ * c := by nlinarith [one_le_K₁]
  have hlogK : 0 ≤ Real.log (K₁ * c) := Real.log_nonneg hK
  have hpi : 0 < π := Real.pi_pos
  have hQ : 13 ≤ depthQ c := by
    unfold depthQ; have : 0 ≤ 8 / π * Real.log (K₁ * c) := by positivity
    have : 0 ≤ 32 / π := by positivity
    linarith
  rcases lt_or_ge D (5 * c) with hsm | hbig
  · calc (2 * D + 3 * c) * t ≤ (2 * D + 3 * c) * 1 := mul_le_mul_of_nonneg_left ht1 (by positivity)
      _ ≤ c * 13 := by linarith
      _ ≤ c * depthQ c := mul_le_mul_of_nonneg_left hQ hc0.le
  · rcases ht0.eq_or_lt with htz | htp
    · rw [← htz, mul_zero]; nlinarith
    · -- `t⁴ ≤ K₁ c e^{−πD/(4c)}` gives `πD/(16c) ≤ (1/4) log(K₁c) − log t`
      have hpl := Cvs.Prolate.Envelope.RungDuhamelRemainder.one_sub_lamR_le_exp hc h hbig
      have ht4 : t ^ (4 : ℕ) = 1 - lamR c k := by
        rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
      have hlog : 4 * Real.log t ≤ Real.log (K₁ * c) - π * D / (4 * c) := by
        have h1 : Real.log (t ^ (4 : ℕ)) ≤ Real.log (K₁ * c * Real.exp (-(π * D / (4 * c)))) :=
          Real.log_le_log (by positivity) (by rw [ht4]; unfold K₁; linarith)
        rw [Real.log_pow, Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp] at h1
        push_cast at h1; linarith
      have hDc : D / c ≤ 4 / π * Real.log (K₁ * c) - 16 / π * Real.log t := by
        have e : π * D / (4 * c) = π / 4 * (D / c) := by field_simp
        rw [e] at hlog
        have h3 : π / 4 * (D / c) ≤ Real.log (K₁ * c) - 4 * Real.log t := by linarith
        have h4 : D / c ≤ (Real.log (K₁ * c) - 4 * Real.log t) / (π / 4) := (le_div_iff₀' (by positivity)).2 h3
        calc D / c ≤ (Real.log (K₁ * c) - 4 * Real.log t) / (π / 4) := h4
          _ = 4 / π * Real.log (K₁ * c) - 16 / π * Real.log t := by field_simp; ring
      have hnl := neg_mul_log_le_one ht0
      have e2 : 2 * D + 3 * c = c * (2 * (D / c) + 3) := by field_simp
      rw [e2, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ hc0.le
      calc (2 * (D / c) + 3) * t ≤ (2 * (4 / π * Real.log (K₁ * c) - 16 / π * Real.log t) + 3) * t :=
            mul_le_mul_of_nonneg_right (by linarith) ht0
        _ = 8 / π * (Real.log (K₁ * c) * t) + 32 / π * (-(t * Real.log t)) + 3 * t := by ring
        _ ≤ 8 / π * Real.log (K₁ * c) + 32 / π * 1 + 3 * 1 := by
            gcongr
            · exact mul_le_of_le_one_right hlogK ht1
        _ ≤ depthQ c := by unfold depthQ; linarith

/-- **The edge value of a rung**: for `c ≥ 80`, `λ ≥ ½` and `χ < c²`,
`h(1)² ≤ (144/49)·c·Q(c)·(1 − λ)^{3/4}`. -/
theorem rung_one_sq_le {c : ℝ} {k : ℕ} (hc : 80 ≤ c) (h : ∃ χ, IsLevelIdx c k χ) (hχc : lev c k < c ^ 2)
    (hl : 1 / 2 ≤ lamR c k) :
    rung c k 1 ^ 2 ≤ 144 / 49 * (c * depthQ c) * (1 - lamR c k) ^ (3 / 4 : ℝ) := by
  have hc0 : 0 < c := by linarith
  have he := Cvs.Prolate.Envelope.RungExteriorLaw.edge_sq_le (by linarith) h hχc
  have hl1 := Cvs.Prolate.Envelope.RungExteriorLaw.lamR_le_one hc0 h
  have hω : 0 ≤ 1 - lamR c k := by linarith
  have hsplit : 1 - lamR c k = (1 - lamR c k) ^ (3 / 4 : ℝ) * (1 - lamR c k) ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_add' hω (by norm_num), show (3 / 4 : ℝ) + 1 / 4 = 1 by norm_num, Real.rpow_one]
  have hdf := depth_mul_rpow_le hc h hχc
  have h1 : rung c k 1 ^ 2 ≤ 144 / 49 * (2 * (c ^ 2 - lev c k) + 3 * c) * (1 - lamR c k) := by
    have hpos : 0 ≤ 72 / 49 * (2 * (c ^ 2 - lev c k) + 3 * c) * (1 - lamR c k) := by
      have : 0 ≤ 2 * (c ^ 2 - lev c k) + 3 * c := by nlinarith
      positivity
    nlinarith [sq_nonneg (rung c k 1)]
  calc rung c k 1 ^ 2 ≤ 144 / 49 * (2 * (c ^ 2 - lev c k) + 3 * c) * (1 - lamR c k) := h1
    _ = 144 / 49 * ((2 * (c ^ 2 - lev c k) + 3 * c) * (1 - lamR c k) ^ (1 / 4 : ℝ))
          * (1 - lamR c k) ^ (3 / 4 : ℝ) := by
        conv_lhs => rw [hsplit]
        ring
    _ ≤ 144 / 49 * (c * depthQ c) * (1 - lamR c k) ^ (3 / 4 : ℝ) := by
        gcongr

/-- `y e^{−κy} ≤ 1/κ` for `κ > 0`. -/
theorem mul_exp_neg_le {κ y : ℝ} (hκ : 0 < κ) : y * Real.exp (-(κ * y)) ≤ 1 / κ := by
  have h := Real.add_one_le_exp (κ * y)
  have he : 0 < Real.exp (κ * y) := Real.exp_pos _
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ he hκ]
  linarith

/-- `c⁶e^{−πc/24} = c(c e^{−πc/120})⁵`. -/
theorem pow_six_exp_eq (c : ℝ) :
    c ^ 6 * Real.exp (-(1 / 4 * π / 6 * c)) = c * (c * Real.exp (-(π / 120 * c))) ^ 5 := by
  rw [mul_pow, ← Real.exp_nat_mul]; push_cast; ring_nf

/-- **The ground term against the edge**: for `c ≥ 80`, `j < x`, `α_j² h₀(1)² ≤ 64K₁c(30/π)⁵(1 − λ_{4j})^{3/4}`. -/
theorem alpha_sq_ground_le {x j : ℕ} (hx : 80 ≤ 2 * π * x) (hj : j < x) :
    Cvs.Approximant.DeepIndexSpineSpan.alpha (2 * π * x) j ^ 2 * rung (2 * π * x) 0 1 ^ 2
      ≤ 64 * K₁ * (2 * π * x) * (120 / π) ^ 5 * (1 - lamR (2 * π * x) (2 * j)) ^ (3 / 4 : ℝ) := by
  set c := 2 * π * (x : ℝ) with hcdef
  have hc0 : 0 < c := by linarith
  have h1 := (Cvs.L2a.FullSpanIndexFloor.full_index x hx hj).1
  have h0 := Cvs.Prolate.EvenRungsByIndex.exists_isLevelIdx_zero c
  have hl := Cvs.L2a.WindowChainInputsProlate.half_le_lamR hx hj
  have hl0 : 1 / 2 ≤ lamR c 0 := by simpa using Cvs.L2a.WindowChainInputsProlate.half_le_lamR hx (j := 0) (by omega)
  have hα := Cvs.Prolate.Envelope.RungDuhamelRemainder.alpha_sq_le hc0 h1 hl
  have hlev0 : lev c 0 ≤ c ^ 2 / 3 := by
    rw [Cvs.Prolate.EvenRungsByIndex.lev_zero]; exact Cvs.Prolate.EvenSpectrumGroundLevel.groundLevel_le c
  have hχ0 : 0 ≤ lev c 0 := Cvs.Prolate.SlepianEvenOrdering.nonneg_of_mem_evenSpec c (Cvs.Prolate.EvenRungsByIndex.lev_spec h0).1
  have he := Cvs.Prolate.Envelope.RungExteriorLaw.edge_sq_le (by linarith) h0 (by nlinarith)
  have hω0 : 0 ≤ 1 - lamR c 0 := by linarith [Cvs.Prolate.EvenRungsByIndex.lamR_zero_le_one hc0]
  have hω : 0 ≤ 1 - lamR c (2 * j) := by linarith [Cvs.Prolate.Envelope.RungExteriorLaw.lamR_le_one hc0 h1]
  have hanti : lamR c (2 * j) ≤ lamR c 0 := Cvs.Prolate.EvenRungsByIndex.lamR_anti hc0 h1 (Nat.zero_le _)
  -- `h₀(1)² ≤ (144/49)(2c² + 3c)(1 − λ₀)`
  have hr0 : rung c 0 1 ^ 2 ≤ 144 / 49 * (2 * c ^ 2 + 3 * c) * (1 - lamR c 0) := by
    have : 72 / 49 * (2 * (c ^ 2 - lev c 0) + 3 * c) * (1 - lamR c 0)
        ≤ 72 / 49 * (2 * c ^ 2 + 3 * c) * (1 - lamR c 0) := by gcongr; linarith
    nlinarith [sq_nonneg (rung c 0 1)]
  -- the ground term at `η = ¼` with `C = 4`
  have hg := Cvs.Prolate.Envelope.RungDuhamelRemainder.ground_term_le (c := c) (η := 1 / 4) (C := 4) (by linarith) (by norm_num)
    (by norm_num) (by norm_num)
  have hpoly : 4 * c / π * (144 / 49 * (2 * c ^ 2 + 3 * c)) ≤ 4 * (1 + Real.log c) * (c + 1) ^ 4 := by
    have hL : 1 ≤ 1 + Real.log c := by linarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ c)]
    have hpi : 3 < π := Real.pi_gt_three
    have h1' : 4 * c / π * (144 / 49 * (2 * c ^ 2 + 3 * c)) ≤ 4 * c / 3 * (144 / 49 * (2 * c ^ 2 + 3 * c)) := by
      gcongr
    have h2' : 4 * c / 3 * (144 / 49 * (2 * c ^ 2 + 3 * c)) ≤ 4 * (c + 1) ^ 4 := by nlinarith
    calc _ ≤ 4 * (c + 1) ^ 4 := h1'.trans h2'
      _ ≤ 4 * (1 + Real.log c) * (c + 1) ^ 4 := by
          have : 0 ≤ (c + 1) ^ 4 := by positivity
          nlinarith
  have hsplit : 1 - lamR c 0 = (1 - lamR c 0) ^ (3 / 4 : ℝ) * (1 - lamR c 0) ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_add' hω0 (by norm_num), show (3 / 4 : ℝ) + 1 / 4 = 1 by norm_num, Real.rpow_one]
  have h34 : (1 - lamR c 0) ^ (3 / 4 : ℝ) ≤ (1 - lamR c (2 * j)) ^ (3 / 4 : ℝ) :=
    Real.rpow_le_rpow hω0 (by linarith) (by norm_num)
  have h14 : (1 - lamR c 0) ^ (1 / 4 : ℝ) * (4 * (1 + Real.log c) * (c + 1) ^ 4)
      ≤ 64 * K₁ * c * (120 / π) ^ 5 := by
    refine hg.trans ?_
    have hy := mul_exp_neg_le (κ := π / 120) (y := c) (by positivity)
    have hy5 : (c * Real.exp (-(π / 120 * c))) ^ 5 ≤ (1 / (π / 120)) ^ 5 :=
      pow_le_pow_left₀ (by positivity) hy 5
    rw [pow_six_exp_eq c]
    have : (1 / (π / 120)) = 120 / π := by field_simp
    rw [this] at hy5
    unfold K₁
    calc 16 * 4 * (33 / 20 * Real.exp 5) * (c * (c * Real.exp (-(π / 120 * c))) ^ 5)
        ≤ 16 * 4 * (33 / 20 * Real.exp 5) * (c * (120 / π) ^ 5) := by gcongr
      _ = _ := by ring
  have hr4 : 0 ≤ (1 - lamR c 0) ^ (1 / 4 : ℝ) := Real.rpow_nonneg hω0 _
  calc Cvs.Approximant.DeepIndexSpineSpan.alpha c j ^ 2 * rung c 0 1 ^ 2
      ≤ 4 * c / π * (144 / 49 * (2 * c ^ 2 + 3 * c) * (1 - lamR c 0)) :=
        mul_le_mul hα hr0 (sq_nonneg _) (by positivity)
    _ = (1 - lamR c 0) ^ (3 / 4 : ℝ)
          * ((1 - lamR c 0) ^ (1 / 4 : ℝ) * (4 * c / π * (144 / 49 * (2 * c ^ 2 + 3 * c)))) := by
        conv_lhs => rw [hsplit]
        ring
    _ ≤ (1 - lamR c (2 * j)) ^ (3 / 4 : ℝ) * (64 * K₁ * c * (120 / π) ^ 5) := by
        refine mul_le_mul h34 ((mul_le_mul_of_nonneg_left hpoly hr4).trans h14) (by positivity)
          (Real.rpow_nonneg hω _)
    _ = _ := by ring

/-- The subpolynomial edge factor `P(x) = 2(144/49)2π·Q(2πx) + 2·64K₁·2π(120/π)⁵`. -/
def edgeP (x : ℕ) : ℝ := 2 * (144 / 49) * (2 * π) * depthQ (2 * π * x) + 2 * (64 * K₁ * (2 * π) * (120 / π) ^ 5)

theorem subPoly_edgeP : SubPoly edgeP := by
  have hQ : SubPoly fun x : ℕ => depthQ (2 * π * x) := by
    unfold depthQ
    refine ((((Cvs.Route.Visibility.ExtPairingRatesSubpoly.subPoly_const (8 / π)).mul (Cvs.Route.Visibility.ExtPairingRatesSubpoly.subPoly_log.add (Cvs.Route.Visibility.ExtPairingRatesSubpoly.subPoly_const (Real.log (K₁ * 2 * π))))
      (Eventually.of_forall fun _ => by positivity) ?_)).add (Cvs.Route.Visibility.ExtPairingRatesSubpoly.subPoly_const (32 / π + 13))).mono ?_
    · filter_upwards [eventually_ge_atTop 1] with x hx
      have : (1 : ℝ) ≤ x := by exact_mod_cast hx
      have := Real.log_nonneg this
      have : 0 ≤ Real.log (K₁ * 2 * π) := Real.log_nonneg (by
        have h2 : (1 : ℝ) ≤ 2 * π := by nlinarith [Real.pi_gt_three]
        rw [mul_assoc]; exact one_le_mul_of_one_le_of_one_le one_le_K₁ h2)
      linarith
    · filter_upwards [eventually_ge_atTop 1] with x hx
      have hx1 : (0 : ℝ) < x := by exact_mod_cast hx
      have hK : 0 < K₁ * 2 * π := by have := one_le_K₁; positivity
      rw [show K₁ * (2 * π * x) = (K₁ * 2 * π) * x by ring, Real.log_mul hK.ne' hx1.ne']
      linarith
  unfold edgeP
  exact ((Cvs.Route.Visibility.ExtPairingRatesSubpoly.subPoly_const _).mul hQ (Eventually.of_forall fun _ => by positivity)
    (by
      filter_upwards [eventually_ge_atTop 1] with x hx
      have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
      unfold depthQ
      have h2 : (1 : ℝ) ≤ 2 * π * x := by nlinarith [Real.pi_gt_three]
      have : 1 ≤ K₁ * (2 * π * x) := one_le_mul_of_one_le_of_one_le one_le_K₁ h2
      have := Real.log_nonneg this
      have : 0 ≤ 8 / π * Real.log (K₁ * (2 * π * x)) := by positivity
      have : 0 ≤ 32 / π := by positivity
      linarith)).add (Cvs.Route.Visibility.ExtPairingRatesSubpoly.subPoly_const _)

/-- **The edge value of a rung profile**: eventually, for `j < x`, `G_j(1)² ≤ P(x)·x·(1 − λ_{4j})^{3/4}`. -/
theorem Gr_one_sq_le : ∀ᶠ x : ℕ in atTop, ∀ j : ℕ, j < x →
    Gr x j 1 ^ 2 ≤ edgeP x * x * (1 - lamR (2 * π * x) (2 * j)) ^ (3 / 4 : ℝ) := by
  filter_upwards [Cvs.Route.Visibility.ExteriorFactorMTwo.eventually_scale] with x hx j hj
  set c := 2 * π * (x : ℝ) with hcdef
  have hc0 : 0 < c := by linarith
  have h1 := (Cvs.L2a.FullSpanIndexFloor.full_index x hx hj)
  have hl := Cvs.L2a.WindowChainInputsProlate.half_le_lamR hx hj
  have hsl := Cvs.L2a.FullSpanIndexFloor.sigmaLow_pos (by linarith : 1 < c)
  have hχc : lev c (2 * j) < c ^ 2 := by linarith [h1.2]
  have hr := rung_one_sq_le (by linarith) h1.1 hχc hl
  have hg := alpha_sq_ground_le hx hj
  have hω : 0 ≤ (1 - lamR c (2 * j)) ^ (3 / 4 : ℝ) :=
    Real.rpow_nonneg (by linarith [Cvs.Prolate.Envelope.RungExteriorLaw.lamR_le_one hc0 h1.1]) _
  have hG : Gr x j 1 ^ 2 ≤ 2 * rung c (2 * j) 1 ^ 2 + 2 * (Cvs.Approximant.DeepIndexSpineSpan.alpha c j ^ 2 * rung c 0 1 ^ 2) := by
    unfold Gr; nlinarith [sq_nonneg (rung c (2 * j) 1 + Cvs.Approximant.DeepIndexSpineSpan.alpha c j * rung c 0 1)]
  refine hG.trans ?_
  unfold edgeP
  rw [← hcdef]
  calc 2 * rung c (2 * j) 1 ^ 2 + 2 * (Cvs.Approximant.DeepIndexSpineSpan.alpha c j ^ 2 * rung c 0 1 ^ 2)
      ≤ 2 * (144 / 49 * (c * depthQ c) * (1 - lamR c (2 * j)) ^ (3 / 4 : ℝ))
        + 2 * (64 * K₁ * c * (120 / π) ^ 5 * (1 - lamR c (2 * j)) ^ (3 / 4 : ℝ)) := by
        gcongr
    _ = _ := by rw [hcdef]; ring

end Cvs.Prolate.Envelope.RungProfileEdgePlunge

end
