import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.Prolate.EndpointLadder
import Cvs.Prolate.EndpointLadderFourEight
import Cvs.Prolate.EndpointLadderHermiteAmp
import Cvs.Prolate.EvenRungDavisKahan
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.HermiteTrialResiduals
import Cvs.Prolate.LadderRatioClosedForm
import Cvs.Prolate.SepticLevelComparison

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The ground rung below `h₄` at the endpoint, and `μ_k² ≤ 2π/c`

`0 < χ₀` (energy identity, Cvs.Prolate.EndpointLadderHermiteAmp), so `EndpointLadderHermiteAmp`'s ladder runs from `h₀` to `h₄` with `R ≥ 1`:
`C₀ h₀(1)² ≤ h₄(1)²`, `C₀ = e^{−2L} · 3/(80√10)`, `L = (4/3)(40 + 2/3 + 600)`, for `c ≥ 160`. With `λ_k ≤ 1`, `μ_k² ≤ 2π/c`.
-/

noncomputable section

open Real Set MeasureTheory Cvs.Prolate.EvenRungsByIndex

namespace Cvs.Prolate.GroundRungEndpoint
open Cvs.ZeroCounting

open Cvs.Prolate.EndpointLadder (aS startB ladR)

/-- **The ground level is positive**: `0 < χ₀` for `c ≠ 0`. -/
theorem lev_zero_pos {c : ℝ} (hc : c ≠ 0) : 0 < lev c 0 := by
  have h0 := exists_isLevelIdx_zero c
  obtain ⟨hg, hg₁, -, hang, heven, hnorm⟩ := rung_spec h0
  have hE := (Cvs.Prolate.EndpointLadderHermiteAmp.energy_bounds hg hg₁ hang heven hnorm).2.2
  have hI : uIcc (-1 : ℝ) 1 = Icc (-1) 1 := uIcc_of_le (by norm_num)
  have hgc : ContinuousOn (rung c 0) (Icc (0 : ℝ) 1) := fun s hs =>
    (hg s (by rw [hI]; exact ⟨by linarith [hs.1], hs.2⟩)).continuousAt.continuousWithinAt
  have hpos : 0 < ∫ s in (0 : ℝ)..1, c ^ 2 * s ^ 2 * rung c 0 s ^ 2 := by
    refine intervalIntegral.integral_pos zero_lt_one
      ((continuousOn_const.mul (continuousOn_id.pow 2)).mul (hgc.pow 2)) (fun s _ => by positivity)
      ⟨1, ⟨zero_le_one, le_rfl⟩, ?_⟩
    have h1 := rung_one_ne_zero h0
    have : 0 < c ^ 2 := by positivity
    have : 0 < rung c 0 1 ^ 2 := by positivity
    simp only [one_pow, mul_one]
    positivity
  linarith

/-- **`λ_k ≤ 1`** for every existing level index. -/
theorem lamR_le_one {c : ℝ} {k : ℕ} (hc : 0 < c) (h : ∃ χ, IsLevelIdx c k χ) : lamR c k ≤ 1 :=
  (lamR_anti hc h (Nat.zero_le k)).trans (lamR_zero_le_one hc)

/-- **`μ_k² ≤ 2π/c`** for every existing level index. -/
theorem muR_sq_le {c : ℝ} {k : ℕ} (hc : 0 < c) (h : ∃ χ, IsLevelIdx c k χ) : muR c k ^ 2 ≤ 2 * π / c := by
  have hl := lamR_le_one hc h
  have hpos : 0 < c / (2 * π) := by positivity
  have e : lamR c k = muR c k ^ 2 * (c / (2 * π)) := by unfold lamR; rw [mul_pow, Real.sq_sqrt hpos.le]
  rw [e] at hl
  rw [le_div_iff₀ hc]
  have : muR c k ^ 2 * c = 2 * π * (muR c k ^ 2 * (c / (2 * π))) := by field_simp
  rw [this]
  nlinarith [Real.pi_pos]

/-- **The edge value of a transform**: `ψ_k(1)² ≤ (2π/c) h_k(1)²`. -/
theorem psi_one_sq_le {c : ℝ} {k : ℕ} (hc : 0 < c) (h : ∃ χ, IsLevelIdx c k χ) :
    Cvs.L2a.AngularProlateTailPositive.psi c (rung c k) 1 ^ 2 ≤ 2 * π / c * rung c k 1 ^ 2 := by
  rw [psi_rung h 1 ⟨by norm_num, le_rfl⟩, mul_pow]
  exact mul_le_mul_of_nonneg_right (muR_sq_le hc h) (sq_nonneg _)

/-- The ground-ladder exponent bound `L = (4/3)(40 + 2/3 + 600)`. -/
def groundL : ℝ := 4 / 3 * (40 + 2 / 3 + 600)

/-- The ground-ladder constant `C₀ = e^{−2L} · 3/(80√10)`. -/
def groundC : ℝ := exp (-(2 * groundL)) * (3 / (80 * √10))

theorem groundC_pos : 0 < groundC := by unfold groundC; positivity

theorem groundC_le_one : groundC ≤ 1 := by
  unfold groundC groundL
  have h1 : exp (-(2 * (4 / 3 * (40 + 2 / 3 + 600) : ℝ))) ≤ 1 := exp_le_one_iff.2 (by norm_num)
  have h10 : (1 : ℝ) ≤ √10 := by rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
  have h2 : 3 / (80 * √10) ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith
  calc _ ≤ 1 * 1 := mul_le_mul h1 h2 (by positivity) zero_le_one
    _ = 1 := one_mul 1

set_option maxHeartbeats 1000000 in
/-- **The ground ladder**: `C₀ h₀(1)² ≤ h₄(1)²` for `c ≥ 160`. -/
theorem ground_ladder {c : ℝ} (hc : 160 ≤ c) : groundC * rung c 0 1 ^ 2 ≤ rung c 2 1 ^ 2 := by
  have hc0 : 0 < c := by linarith
  have hpi := Real.pi_gt_three
  have hpi' := Real.pi_lt_d2
  have h2 : ∃ χ, IsLevelIdx c 2 χ := Cvs.Prolate.SepticLevelComparison.exists_isLevelIdx_of_le_four (by linarith) (by norm_num)
  have h0 := exists_isLevelIdx_zero c
  set χa := lev c 0 with hχad
  set χb := lev c 2 with hχbd
  have hχa0 : 0 < χa := lev_zero_pos hc0.ne'
  have hχab : χa ≤ χb := lev_le h2 (by norm_num)
  have hχb9 : χb ≤ 9 * c + 1 / 4 := by
    have h := Cvs.Prolate.EvenRungDavisKahan.sq_lev_two_sub_le (c := c) (by linarith)
    rw [Cvs.Prolate.EvenRungDavisKahan.mu_two, Cvs.Prolate.HermiteTrialResiduals.kap2_values.2.2] at h
    have h11 : |χb - (9 * c - 43 / 4)| ≤ 11 := by
      rw [← Real.sqrt_sq_eq_abs, show (11 : ℝ) = √(11 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by linarith)
    rw [abs_le] at h11
    linarith
  have hχb10 : χb ≤ 10 * c := by linarith
  have hχb0 : 0 < χb := hχa0.trans_le hχab
  have hT : √χb / c ≤ 1 / 4 := by
    rw [div_le_iff₀ hc0]
    calc √χb ≤ √((1 / 4 * c) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = 1 / 4 * c := Real.sqrt_sq (by positivity)
  have ha2 : aS c χb ≤ 1 / 2 := by
    unfold aS; rw [show 2 * √χb / c = 2 * (√χb / c) by ring]; linarith
  have ha0 : 0 < aS c χb := by unfold aS; positivity
  obtain ⟨ha, ha₁, -, hanga, hevena, hnorma⟩ := rung_spec h0
  obtain ⟨hb, hb₁, -, hangb, hevenb, hnormb⟩ := rung_spec h2
  have H := Cvs.Prolate.EndpointLadderHermiteAmp.ladder_sq_sharp ha ha₁ hanga hevena hnorma (rung_one_ne_zero h0)
    hb hb₁ hangb hevenb hnormb (rung_one_ne_zero h2) hc0 hχa0 hχab ha2
  -- the peak loss
  have hL : Cvs.Prolate.EndpointLadderFourEight.startL c χb ≤ groundL := by
    unfold Cvs.Prolate.EndpointLadderFourEight.startL groundL
    have hr : χb / c ≤ 10 := by rw [div_le_iff₀ hc0]; linarith
    have hr0 : 0 ≤ χb / c := by positivity
    have e1 : 4 * χb / c = 4 * (χb / c) := by ring
    have e2 : 6 * χb ^ 2 / c ^ 2 = 6 * (χb / c) ^ 2 := by ring
    rw [e1, e2]
    nlinarith
  have hB : exp (-groundL) ≤ startB c χb :=
    (exp_le_exp.2 (neg_le_neg hL)).trans (Cvs.Prolate.EndpointLadderFourEight.exp_neg_startL_le hc0 hχb0 hT)
  -- the ladder base is at least one
  have hR : 1 ≤ ladR c χb := by
    unfold ladR
    have hk : 0 < 2 / aS c χb + Cvs.Prolate.LadderRatioClosedForm.kap c χb (aS c χb) := by
      unfold Cvs.Prolate.LadderRatioClosedForm.kap; positivity
    rw [one_le_div (by positivity)]
    nlinarith
  have hy0 : 0 ≤ (χb - χa) / c := div_nonneg (by linarith) hc0.le
  have hRy : 1 ≤ ladR c χb ^ ((χb - χa) / c) := Real.one_le_rpow hR hy0
  -- the amplitude ratio
  set s := √c with hsd
  have hs0 : 0 < s := Real.sqrt_pos.2 hc0
  have hs2 : s ^ 2 = c := Real.sq_sqrt hc0.le
  have hamp : 3 / (80 * √10) ≤ 3 * c / (16 * √χb) / (1 + 2 * √(χa / 3)) := by
    have hχbs : √χb ≤ √10 * s := by
      rw [hsd, ← Real.sqrt_mul (by positivity)]; exact Real.sqrt_le_sqrt (by linarith)
    have hχas : √(χa / 3) ≤ 2 * s := by
      calc √(χa / 3) ≤ √((2 * s) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
        _ = 2 * s := Real.sqrt_sq (by positivity)
    have hs1 : 1 ≤ s := by nlinarith
    have hU : 1 + 2 * √(χa / 3) ≤ 5 * s := by linarith
    have hr10 : 0 < √10 := by positivity
    have hχbpos : 0 < √χb := Real.sqrt_pos.2 hχb0
    rw [div_div, le_div_iff₀ (by positivity)]
    calc 3 / (80 * √10) * (16 * √χb * (1 + 2 * √(χa / 3)))
        ≤ 3 / (80 * √10) * (16 * (√10 * s) * (5 * s)) := by gcongr
      _ = 3 * c := by rw [← hs2]; field_simp; ring
  have hcoef : groundC ≤ startB c χb ^ 2 * (3 * c / (16 * √χb)) / (1 + 2 * √(χa / 3))
      * ladR c χb ^ ((χb - χa) / c) := by
    have hB2 : exp (-groundL) ^ 2 ≤ startB c χb ^ 2 := pow_le_pow_left₀ (exp_pos _).le hB 2
    have e : groundC = exp (-groundL) ^ 2 * (3 / (80 * √10)) * 1 := by
      unfold groundC; rw [← Real.exp_nat_mul]; push_cast; ring_nf
    rw [e, show startB c χb ^ 2 * (3 * c / (16 * √χb)) / (1 + 2 * √(χa / 3)) * ladR c χb ^ ((χb - χa) / c)
        = startB c χb ^ 2 * (3 * c / (16 * √χb) / (1 + 2 * √(χa / 3))) * ladR c χb ^ ((χb - χa) / c) by ring]
    exact mul_le_mul (mul_le_mul hB2 hamp (by positivity) (by positivity)) hRy zero_le_one (by positivity)
  calc groundC * rung c 0 1 ^ 2
      ≤ startB c χb ^ 2 * (3 * c / (16 * √χb)) / (1 + 2 * √(χa / 3)) * ladR c χb ^ ((χb - χa) / c)
          * rung c 0 1 ^ 2 := mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)
    _ ≤ rung c 2 1 ^ 2 := H

end Cvs.Prolate.GroundRungEndpoint
