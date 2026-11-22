import Mathlib
import Cvs.Prolate.EndpointLadder
import Cvs.Prolate.LadderRatioClosedForm
import Cvs.Prolate.LiouvilleGreen.WkbEndpointLower
import Cvs.Prolate.LiouvilleGreen.WkbRiccatiBarrier

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The endpoint ladder on the rungs `h₄`, `h₈`

Cvs.Prolate.EndpointLadder at `g_a = rung c 2` (`h₄`, level `≤ 9c + 1/4`, Cvs.Prolate.EvenRungDavisKahan; `λ ≥ 1/2`, Cvs.L2a.WindowChainInputsProlate) and `g_b = rung c 4` (`h₈`, level in
`[15c − 241/2, 10πc]`, Cvs.Prolate.SepticLevelComparison, Cvs.Prolate.LevelsBelowLinearBound). The peak loss is `B ≥ e^{−L(χ)}`, `L = (4/3)(4χ/c + 2/3 + 6χ²/c²)`, the ladder
base `R ≥ √c/18` and the exponent `(χ₄ − χ₂)/c ≥ 11/2`, so at `c = 2πx`, `x ≥ 80`:
`C c^{7/4} h₄(1)² ≤ h₈(1)²` with `C = e^{−2L₀}π/(4·18^{11/2})`, `L₀ = (4/3)(40π + 2/3 + 600π²)`.
-/

noncomputable section

open Real Set

namespace Cvs.Prolate.EndpointLadderFourEight

open Cvs.Prolate.LiouvilleGreen.WkbRiccatiBarrier (pp qq Bb gam)
open Cvs.Prolate.LiouvilleGreen.WkbEndpointLower (Kl)
open Cvs.Prolate.LadderRatioClosedForm (kap)
open Cvs.Prolate.EndpointLadder (aS startB ladR)

/-- The peak loss exponent `L = (4/3)(4χ/c + 2/3 + 6χ²/c²)`. -/
def startL (c χ : ℝ) : ℝ := 4 / 3 * (4 * χ / c + 2 / 3 + 6 * χ ^ 2 / c ^ 2)

/-- **The peak loss in closed form**: `e^{−L} ≤ B` for `0 < χ`, `√χ/c ≤ 1/4`. -/
theorem exp_neg_startL_le {c χ : ℝ} (hc : 0 < c) (hχ : 0 < χ) (hT : √χ / c ≤ 1 / 4) :
    exp (-startL c χ) ≤ startB c χ := by
  unfold startB Kl
  apply exp_le_exp.2
  apply neg_le_neg
  set T := √χ / c with hTd
  have hT0 : 0 < T := by positivity
  have hT2 : T ^ 2 = χ / c ^ 2 := by rw [hTd, div_pow, Real.sq_sqrt hχ.le]
  have hcT : c ^ 2 * T ^ 2 = χ := by rw [hT2]; field_simp
  rw [show T + T = 2 * T by ring]
  have hp : 3 / 4 ≤ pp (2 * T) := by unfold pp; nlinarith
  have hB : Bb c χ (2 * T) ≤ c * (2 * T) := by
    have h := Cvs.Prolate.LadderRatioClosedForm.Bb_le hc hχ.le (s := 2 * T) (by positivity) (by linarith)
    have hr : √(1 - (2 * T) ^ 2) ≤ 1 := by
      exact (Real.sqrt_le_sqrt (show 1 - (2 * T) ^ 2 ≤ 1 by nlinarith)).trans_eq Real.sqrt_one
    calc Bb c χ (2 * T) ≤ c * (2 * T) * √(1 - (2 * T) ^ 2) := h
      _ ≤ c * (2 * T) * 1 := mul_le_mul_of_nonneg_left hr (by positivity)
      _ = c * (2 * T) := mul_one _
  have hγ : gam c χ (2 * T) ≤ 2 / (3 * (2 * T)) :=
    Cvs.Prolate.LadderRatioClosedForm.gam_le hc hχ (by positivity) (by linarith) (by nlinarith)
  have hq : qq c χ (2 * T) = 3 * χ := by unfold qq; linear_combination 4 * hcT
  set V := c * (2 * T) + 2 / (3 * (2 * T)) + 3 * χ * T with hVd
  have hK : Bb c χ (2 * T) + gam c χ (2 * T) + qq c χ (2 * T) * T ≤ V := by rw [hq]; linarith
  have hV0 : 0 ≤ V := by positivity
  have hpp : 0 < pp (2 * T) := by linarith
  have hVe : V * (2 * T) / (3 / 4) = startL c χ := by
    unfold startL
    have e : V * (2 * T) = 4 * c * T ^ 2 + 2 / 3 + 6 * χ * T ^ 2 := by rw [hVd]; field_simp; ring
    rw [e, hT2]; field_simp
  calc (Bb c χ (2 * T) + gam c χ (2 * T) + qq c χ (2 * T) * T) * (2 * T) / pp (2 * T)
      ≤ V * (2 * T) / pp (2 * T) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hK (by positivity)) hpp.le
    _ ≤ V * (2 * T) / (3 / 4) := div_le_div_of_nonneg_left (by positivity) (by norm_num) hp
    _ = startL c χ := hVe

/-- **The ladder base is at least `√c/18`** for `c ≥ 4`, `14c ≤ χ ≤ 36c`. -/
theorem sqrt_div_le_ladR {c χ : ℝ} (hc : 4 ≤ c) (h1 : 14 * c ≤ χ) (h2 : χ ≤ 36 * c) : √c / 18 ≤ ladR c χ := by
  have hc0 : 0 < c := by linarith
  have hχ : 0 < χ := by linarith
  set s := √c with hsd
  have hs2 : s ^ 2 = c := Real.sq_sqrt hc0.le
  have hs : 2 ≤ s := by
    rw [hsd, show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hc
  have hχ6 : √χ ≤ 6 * s := by
    calc √χ ≤ √(6 ^ 2 * c) := Real.sqrt_le_sqrt (by linarith)
      _ = 6 * s := by rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
  have hχ3 : 3 * s ≤ √χ := by
    calc 3 * s = √(3 ^ 2 * c) := by rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
      _ ≤ √χ := Real.sqrt_le_sqrt (by linarith)
  have hsq : √χ ^ 2 = χ := Real.sq_sqrt hχ.le
  have hr0 : 0 < √χ := Real.sqrt_pos.2 hχ
  have ha : aS c χ = 2 * √χ / c := rfl
  have h2ca : 2 * c * aS c χ = 4 * √χ := by rw [ha]; field_simp; ring
  have h2a : 2 / aS c χ = c / √χ := by rw [ha]; field_simp
  have h2a' : c / √χ ≤ s / 3 := by
    rw [div_le_div_iff₀ hr0 (by norm_num)]; nlinarith
  have hia : 1 / aS c χ ^ 2 ≤ c / 56 := by
    rw [ha, div_pow, mul_pow, hsq, one_div_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hkap : kap c χ (aS c χ) ≤ 2 + 9 * s := by
    unfold kap
    have : √(2 * (2 * c + 1 / aS c χ ^ 2 + χ)) ≤ 9 * s := by
      calc √(2 * (2 * c + 1 / aS c χ ^ 2 + χ)) ≤ √(9 ^ 2 * c) := Real.sqrt_le_sqrt (by nlinarith)
        _ = 9 * s := by rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
    linarith
  have hkap0 : 0 < kap c χ (aS c χ) := by unfold kap; positivity
  have hD : 2 * c * aS c χ + (2 / aS c χ + kap c χ (aS c χ)) ≤ 36 * s := by
    rw [h2ca, h2a]; linarith
  have hD0 : 0 < 2 * c * aS c χ + (2 / aS c χ + kap c χ (aS c χ)) := by
    rw [h2ca, h2a]; positivity
  have hK0 : 0 ≤ 2 / aS c χ + kap c χ (aS c χ) := by rw [h2a]; positivity
  unfold ladR
  rw [le_div_iff₀ hD0]
  calc s / 18 * (2 * c * aS c χ + (2 / aS c χ + kap c χ (aS c χ))) ≤ s / 18 * (36 * s) :=
        mul_le_mul_of_nonneg_left hD (by positivity)
    _ = 2 * c := by rw [← hs2]; ring
    _ ≤ 2 * c + (2 / aS c χ + kap c χ (aS c χ)) := by linarith

/-- The loss constant `L₀ = (4/3)(40π + 2/3 + 600π²)`, `L` at `χ = 10πc`. -/
def ladL : ℝ := 4 / 3 * (40 * π + 2 / 3 + 600 * π ^ 2)

end Cvs.Prolate.EndpointLadderFourEight
