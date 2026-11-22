import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.BandECouplingCollar
import Cvs.L2a.BandRungOutgoingWave
import Cvs.L2a.CollarTransferConstant
import Cvs.Prolate.BandMassLaw

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The clause-(6) residual of `BandInputs` at `K_r = 1`
With `q = c^{1/24}`, `F ≤ K_Aψ`, `‖g‖₁ ≤ 2K_A√(c/π)ψ`, `K₀^c ≤ 23‖g‖₁/c²`, `K_b ≤ 64F/c + 1040‖g‖₁/c²`,
`T ≤ 10⁶K_Aψc^{−3/4}`, `η_B ≤ 700F/c`, `J ≤ c/4 + 1` and `τ̄ ≤ 64c^{−1/3}` (Cvs.L2a.CollarTransferConstant), the residual sum is at most
`548868K_Aψ/q¹⁶` and the main term at least `ψ/(15q¹⁵)`; `q ≥ 2³¹e²⁵` (`c ≥ e¹³⁶⁰`) and `K_A ≤ √2e²⁵` give ratio `≤ 1`.
-/

noncomputable section

open Real Cvs.L2a.AngularProlateTailPositive

namespace Cvs.L2a.BandInputsClauseSixResidual

open Cvs.L2a.BandRungOutgoingWave (gL1 collarK tauBar lamHat cE)
open Cvs.L2a.BandECouplingCollar (deltaS mainA)

/-- `2³¹e²⁵ ≤ c^{1/24}` for `c ≥ e¹³⁶⁰`. -/
theorem rpow_24_ge {c : ℝ} (hc : exp 1360 ≤ c) : 2 ^ 31 * exp 25 ≤ c ^ (1 / 24 : ℝ) := by
  have h1 : (exp 1360) ^ (1 / 24 : ℝ) ≤ c ^ (1 / 24 : ℝ) :=
    Real.rpow_le_rpow (exp_pos _).le hc (by norm_num)
  rw [← Real.exp_mul] at h1
  have h2 : exp 56 ≤ exp (1360 * (1 / 24)) := exp_le_exp.2 (by norm_num)
  have h3 : exp 56 = exp 31 * exp 25 := by rw [← exp_add]; norm_num
  have h4 : (2 : ℝ) ^ 31 ≤ exp 31 := by
    have h21 : (2 : ℝ) ≤ exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
    have : exp 31 = exp 1 ^ 31 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]; exact pow_le_pow_left₀ (by norm_num) h21 31
  have h5 : 2 ^ 31 * exp 25 ≤ exp 31 * exp 25 := mul_le_mul_of_nonneg_right h4 (exp_pos _).le
  linarith

/-- `8(1 + Q)(Q³/4 + 1) ≤ 16Q⁴` for `Q ≥ 2`. -/
theorem quartic_le {Q : ℝ} (hQ : 2 ≤ Q) : 8 * (1 + Q) * (Q * Q * Q / 4 + 1) ≤ 16 * (Q * Q * Q * Q) := by
  have hQ2 : 4 ≤ Q * Q := by nlinarith
  have hQ3 : 8 ≤ Q * Q * Q := by nlinarith
  have hQ4 : 2 * (Q * Q * Q) ≤ Q * Q * Q * Q := by nlinarith
  have hQ5 : 8 * Q ≤ Q * Q * Q * Q := by nlinarith
  have hQ6 : 16 ≤ Q * Q * Q * Q := by nlinarith
  nlinarith

/-- The main term from below: `ψ/(15q¹⁵) ≤ q^{−3}√(ψ²LE/q²⁴)` for `q > 0`, `L ≥ 1`, `E ≥ 1/200`. -/
theorem main_ge {ψ1 L E q : ℝ} (hL : 1 ≤ L) (hE : 1 / 200 ≤ E) (hq0 : 0 < q) :
    ψ1 / (15 * q ^ 15) ≤ 1 * (1 / q ^ 3) * √(ψ1 ^ 2 * L * E / q ^ 24) := by
  have hLE : 1 / 200 ≤ L * E := by
    have := mul_le_mul hL hE (by norm_num) (by linarith); linarith
  have hs : ψ1 / (15 * q ^ 12) ≤ √(ψ1 ^ 2 * L * E / q ^ 24) := by
    apply Real.le_sqrt_of_sq_le
    rw [div_pow, show (15 * q ^ 12) ^ 2 = 225 * q ^ 24 by ring,
      show ψ1 ^ 2 * L * E / q ^ 24 = ψ1 ^ 2 * (L * E) / q ^ 24 by ring,
      div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 := mul_le_mul_of_nonneg_left hLE (sq_nonneg ψ1)
    have h2 : ψ1 ^ 2 ≤ 225 * (ψ1 ^ 2 * (L * E)) := by nlinarith [sq_nonneg ψ1]
    have h3 := mul_le_mul_of_nonneg_right h2 (pow_pos hq0 24).le
    linarith
  calc ψ1 / (15 * q ^ 15) = 1 * (1 / q ^ 3) * (ψ1 / (15 * q ^ 12)) := by field_simp
    _ ≤ 1 * (1 / q ^ 3) * √(ψ1 ^ 2 * L * E / q ^ 24) := mul_le_mul_of_nonneg_left hs (by positivity)

/-- The final comparison: `548868·K_Aψ/q¹⁶ ≤ ψ/(15q¹⁵)` for `K_A ≤ √2e²⁵` and `q ≥ 2³¹e²⁵`. -/
theorem fin_le {KA ψ1 q : ℝ} (hψ : 0 ≤ ψ1) (hKA : KA ≤ √2 * exp 25) (hq : 2 ^ 31 * exp 25 ≤ q)
    (hq0 : 0 < q) : 548868 * (KA * ψ1) / q ^ 16 ≤ ψ1 / (15 * q ^ 15) := by
  have hA : KA * ψ1 ≤ 2 * exp 25 * ψ1 := by
    have hs2 : √2 ≤ 2 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
    have : KA ≤ 2 * exp 25 := hKA.trans (mul_le_mul_of_nonneg_right hs2 (exp_pos 25).le)
    exact mul_le_mul_of_nonneg_right this hψ
  rw [div_le_div_iff₀ (by positivity) (by positivity),
    show ψ1 * q ^ 16 = ψ1 * q * q ^ 15 by ring,
    show 548868 * (KA * ψ1) * (15 * q ^ 15) = 548868 * 15 * (KA * ψ1) * q ^ 15 by ring]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  have h2 : 548868 * 15 * (2 * exp 25) ≤ q := by
    have := mul_le_mul_of_nonneg_right (show (548868 * 15 * 2 : ℝ) ≤ 2 ^ 31 by norm_num) (exp_pos 25).le
    linarith
  have h4 := mul_le_mul_of_nonneg_right h2 hψ
  linarith

/-- `K·A/qⁿ ≤ A/qᵐ` for `A ≥ 0`, `q > 0`, `m ≤ n` and `K ≤ q^{n−m}`. -/
theorem mul_div_pow_le {A K q : ℝ} {m n : ℕ} (hA : 0 ≤ A) (hq : 0 < q) (hmn : m ≤ n)
    (hK : K ≤ q ^ (n - m)) : K * A / q ^ n ≤ A / q ^ m := by
  rw [div_le_div_iff₀ (pow_pos hq n) (pow_pos hq m), ← pow_sub_mul_pow q hmn]
  calc K * A * q ^ m = K * (A * q ^ m) := by ring
    _ ≤ q ^ (n - m) * (A * q ^ m) := mul_le_mul_of_nonneg_right hK (mul_nonneg hA (pow_pos hq m).le)
    _ = A * (q ^ (n - m) * q ^ m) := by ring

/-- **The clause-(6) residual at `K_r = 1`**, pure real arithmetic: for `c ≥ e¹³⁶⁰`, `K_A ≤ √2e²⁵` and the cut-input
bounds, `‖g‖₁√(54(π²/12 − 11/16)/(πc³)) + K₀^c√(cK_col(δ, δ)) + K_bτ̄√(8(1 + 1/δ)J) + T + η_B` is at most
`c^{−1/8}√(ψ²LE/c)` whenever `L ≥ 1`, `E ≥ 1/200`, `δ = c^{−1/3}`. -/
theorem residual_le {c J ψ1 L E F G KA K0c Kb T ηB : ℝ}
    (hc : exp 1360 ≤ c) (hJ : J ≤ c / 4 + 1) (hψ : 0 ≤ ψ1) (hL : 1 ≤ L) (hE : 1 / 200 ≤ E)
    (hKA : KA ≤ √2 * exp 25)
    (hF : F ≤ KA * ψ1) (hG : G ≤ 2 * KA * √(c / π) * ψ1)
    (hK0 : K0c ≤ 23 * G / c ^ 2)
    (hKb0 : 0 ≤ Kb) (hKb : Kb ≤ 64 * F / c + 1040 * G / c ^ 2)
    (hT : T ≤ 10 ^ 6 * KA * ψ1 * c ^ (-(3 / 4 : ℝ)))
    (hη0 : 0 ≤ ηB) (hη : ηB ≤ 700 * F / c) :
    G * √(54 * (π ^ 2 / 12 - 11 / 16) / (π * c ^ 3))
        + K0c * √(c * collarK (deltaS c) (deltaS c))
        + Kb * tauBar c (1 / 2) (deltaS c) (1 / 4) * √(8 * (1 + 1 / deltaS c) * J)
        + T + ηB
      ≤ 1 * c ^ (-(1 / 8 : ℝ)) * √(ψ1 ^ 2 * L * E / c) := by
  have hc0 : 0 < c := lt_of_lt_of_le (exp_pos _) hc
  have hqge := rpow_24_ge hc
  set q := c ^ (1 / 24 : ℝ) with hqdef
  have hq0 : 0 < q := Real.rpow_pos_of_pos hc0 _
  have hpow : ∀ n : ℕ, q ^ n = c ^ ((n : ℝ) / 24) := fun n => by
    rw [hqdef, ← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; ring_nf
  have hinv : ∀ (n : ℕ) (r : ℝ), r = -((n : ℝ) / 24) → c ^ r = 1 / q ^ n := fun n r hr => by
    rw [hpow, hr, Real.rpow_neg hc0.le, one_div]
  have hcq : c = q ^ 24 := by rw [hpow]; norm_num
  have h8 : c ^ (-(1 / 8 : ℝ)) = 1 / q ^ 3 := hinv 3 _ (by norm_num)
  have h34 : c ^ (-(3 / 4 : ℝ)) = 1 / q ^ 18 := hinv 18 _ (by norm_num)
  have hδ : deltaS c = 1 / q ^ 8 := hinv 8 _ (by norm_num)
  have he25 : 1 ≤ exp 25 := Real.one_le_exp (by norm_num)
  have hq1 : (2 : ℝ) ^ 31 ≤ q := by nlinarith
  have hc6 : (10 : ℝ) ^ 6 ≤ c := by
    rw [hcq]
    calc (10 : ℝ) ^ 6 ≤ 2 ^ 31 := by norm_num
      _ ≤ q := hq1
      _ ≤ q ^ 24 := le_self_pow₀ (by linarith) (by norm_num)
  have htau := Cvs.L2a.CollarTransferConstant.tauBar_schedule_le hc6
  rw [hinv 8 _ (by norm_num), hδ] at htau
  have hd0 : 0 ≤ deltaS c := (Cvs.L2a.BandECouplingCollar.deltaS_pos hc0).le
  have hd1 : deltaS c ≤ 1 := (Cvs.L2a.BandECouplingCollar.deltaS_lt_one (by linarith)).le
  have hKd : collarK (deltaS c) (deltaS c) ≤ deltaS c := by
    refine (Cvs.L2a.BandECouplingCollar.collarK_diag_le hd0 hd1).trans ?_
    rw [div_le_iff₀ pi_pos]; nlinarith [pi_gt_three]
  rw [hδ] at hKd
  rw [hδ, h8]
  rw [h34] at hT
  have hsc' : √c = q ^ 12 := by rw [hcq, show q ^ 24 = (q ^ 12) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have hsc : √(c / π) ≤ q ^ 12 :=
    (Real.sqrt_le_sqrt (div_le_self hc0.le (by linarith [pi_gt_three]))).trans_eq hsc'
  clear_value q
  clear hpow hinv h8 h34 hδ hsc' hd0 hd1 hqdef
  subst hcq
  -- the amplitude `A = K_Aψ`
  set A := KA * ψ1 with hAdef
  have hF0 : 0 ≤ F := by
    have h := mul_nonneg (hη0.trans hη) hc0.le
    rw [div_mul_cancel₀ _ hc0.ne'] at h; linarith
  have hA0 : 0 ≤ A := hF0.trans hF
  have hG2 : G ≤ 2 * A * q ^ 12 := by
    rw [show 2 * KA * √(q ^ 24 / π) * ψ1 = 2 * A * √(q ^ 24 / π) by rw [hAdef]; ring] at hG
    exact hG.trans (mul_le_mul_of_nonneg_left hsc (by positivity))
  have hq8 : (2 : ℝ) ^ 31 ≤ q ^ 8 := hq1.trans (le_self_pow₀ (by linarith) (by norm_num))
  have hq2 : (10 : ℝ) ^ 6 ≤ q ^ 2 := by nlinarith
  have hqk : ∀ k : ℕ, 1 ≤ k → q ≤ q ^ k := fun k hk => le_self_pow₀ (by linarith) (by omega)
  -- each term against `A/q¹⁶`
  have t1 : G * √(54 * (π ^ 2 / 12 - 11 / 16) / (π * (q ^ 24) ^ 3)) ≤ A / q ^ 16 := by
    have hX : 54 * (π ^ 2 / 12 - 11 / 16) / (π * (q ^ 24) ^ 3) ≤ (8 / q ^ 36) ^ 2 := by
      rw [div_le_iff₀ (by positivity),
        show (8 / q ^ 36) ^ 2 * (π * (q ^ 24) ^ 3) = 64 * π by field_simp; ring]
      nlinarith [pi_gt_three, pi_lt_d2]
    have hs : √(54 * (π ^ 2 / 12 - 11 / 16) / (π * (q ^ 24) ^ 3)) ≤ 8 / q ^ 36 :=
      (Real.sqrt_le_sqrt hX).trans_eq (Real.sqrt_sq (by positivity))
    calc G * √(54 * (π ^ 2 / 12 - 11 / 16) / (π * (q ^ 24) ^ 3)) ≤ 2 * A * q ^ 12 * (8 / q ^ 36) :=
          mul_le_mul hG2 hs (Real.sqrt_nonneg _) (by positivity)
      _ = 16 * A / q ^ 24 := by field_simp; ring
      _ ≤ A / q ^ 16 := mul_div_pow_le hA0 hq0 (by norm_num) (by norm_num; linarith [hqk 8 (by norm_num)])
  have t2 : K0c * √(q ^ 24 * collarK (1 / q ^ 8) (1 / q ^ 8)) ≤ A / q ^ 16 := by
    have hX : q ^ 24 * collarK (1 / q ^ 8) (1 / q ^ 8) ≤ (q ^ 8) ^ 2 := by
      calc q ^ 24 * collarK (1 / q ^ 8) (1 / q ^ 8) ≤ q ^ 24 * (1 / q ^ 8) :=
            mul_le_mul_of_nonneg_left hKd (by positivity)
        _ = (q ^ 8) ^ 2 := by field_simp
    have hs : √(q ^ 24 * collarK (1 / q ^ 8) (1 / q ^ 8)) ≤ q ^ 8 :=
      (Real.sqrt_le_sqrt hX).trans_eq (Real.sqrt_sq (by positivity))
    have hK0' : K0c ≤ 23 * (2 * A * q ^ 12) / (q ^ 24) ^ 2 :=
      hK0.trans (div_le_div_of_nonneg_right (by linarith) (by positivity))
    calc K0c * √(q ^ 24 * collarK (1 / q ^ 8) (1 / q ^ 8)) ≤ 23 * (2 * A * q ^ 12) / (q ^ 24) ^ 2 * q ^ 8 :=
          mul_le_mul hK0' hs (Real.sqrt_nonneg _) (by positivity)
      _ = 46 * A / q ^ 28 := by field_simp; ring
      _ ≤ A / q ^ 16 := mul_div_pow_le hA0 hq0 (by norm_num) (by norm_num; linarith [hqk 12 (by norm_num)])
  have t3 : Kb * tauBar (q ^ 24) (1 / 2) (1 / q ^ 8) (1 / 4) * √(8 * (1 + 1 / (1 / q ^ 8)) * J)
      ≤ 548864 * A / q ^ 16 := by
    have hX : 8 * (1 + 1 / (1 / q ^ 8)) * J ≤ (4 * q ^ 16) ^ 2 := by
      rw [one_div_one_div]
      have h1 : 8 * (1 + q ^ 8) * J ≤ 8 * (1 + q ^ 8) * (q ^ 24 / 4 + 1) :=
        mul_le_mul_of_nonneg_left hJ (by positivity)
      refine h1.trans ?_
      have hQ : 2 ≤ q ^ 8 := by linarith [show (2 : ℝ) ≤ 2 ^ 31 by norm_num]
      have e1 : (q ^ 24 : ℝ) = q ^ 8 * q ^ 8 * q ^ 8 := by ring
      have e2 : (4 * q ^ 16) ^ 2 = 16 * (q ^ 8 * q ^ 8 * q ^ 8 * q ^ 8) := by ring
      rw [e1, e2]
      exact quartic_le hQ
    have hs : √(8 * (1 + 1 / (1 / q ^ 8)) * J) ≤ 4 * q ^ 16 :=
      (Real.sqrt_le_sqrt hX).trans_eq (Real.sqrt_sq (by positivity))
    have hKb' : Kb ≤ 2144 * A / q ^ 24 := by
      refine hKb.trans ?_
      have hF' : 64 * F / q ^ 24 ≤ 64 * A / q ^ 24 :=
        div_le_div_of_nonneg_right (by linarith) (by positivity)
      have hG' : 1040 * G / (q ^ 24) ^ 2 ≤ 2080 * A / q ^ 24 := by
        calc 1040 * G / (q ^ 24) ^ 2 ≤ 1040 * (2 * A * q ^ 12) / (q ^ 24) ^ 2 :=
              div_le_div_of_nonneg_right (by linarith) (by positivity)
          _ = 2080 * A / q ^ 36 := by field_simp; ring
          _ ≤ 2080 * A / q ^ 24 :=
              div_le_div_of_nonneg_left (by positivity) (by positivity)
                (pow_le_pow_right₀ (by linarith) (by norm_num))
      have e : 2144 * A / q ^ 24 = 64 * A / q ^ 24 + 2080 * A / q ^ 24 := by ring
      linarith
    have hτs : tauBar (q ^ 24) (1 / 2) (1 / q ^ 8) (1 / 4) * √(8 * (1 + 1 / (1 / q ^ 8)) * J)
        ≤ 64 * (1 / q ^ 8) * (4 * q ^ 16) := by
      have := mul_le_mul_of_nonneg_right htau (Real.sqrt_nonneg (8 * (1 + 1 / (1 / q ^ 8)) * J))
      exact this.trans (mul_le_mul_of_nonneg_left hs (by positivity))
    calc Kb * tauBar (q ^ 24) (1 / 2) (1 / q ^ 8) (1 / 4) * √(8 * (1 + 1 / (1 / q ^ 8)) * J)
        = Kb * (tauBar (q ^ 24) (1 / 2) (1 / q ^ 8) (1 / 4) * √(8 * (1 + 1 / (1 / q ^ 8)) * J)) := by ring
      _ ≤ Kb * (64 * (1 / q ^ 8) * (4 * q ^ 16)) := mul_le_mul_of_nonneg_left hτs hKb0
      _ ≤ 2144 * A / q ^ 24 * (64 * (1 / q ^ 8) * (4 * q ^ 16)) :=
          mul_le_mul_of_nonneg_right hKb' (by positivity)
      _ = 548864 * A / q ^ 16 := by field_simp; ring
  have t4 : T ≤ A / q ^ 16 := by
    refine hT.trans ?_
    rw [show 10 ^ 6 * KA * ψ1 * (1 / q ^ 18) = 10 ^ 6 * A / q ^ 18 by rw [hAdef]; ring]
    exact mul_div_pow_le hA0 hq0 (by norm_num) (by have h := hq2; norm_num at h ⊢; exact h)
  have t5 : ηB ≤ A / q ^ 16 := by
    refine hη.trans ((div_le_div_of_nonneg_right (show 700 * F ≤ 700 * A by linarith) (by positivity)).trans ?_)
    exact mul_div_pow_le hA0 hq0 (by norm_num) (by norm_num; linarith [hqk 8 (by norm_num)])
  have hmain := main_ge (ψ1 := ψ1) hL hE hq0
  have hfin : 548868 * A / q ^ 16 ≤ ψ1 / (15 * q ^ 15) := fin_le hψ hKA hqge hq0
  have e : 548868 * A / q ^ 16 = 548864 * A / q ^ 16 + A / q ^ 16 + A / q ^ 16 + A / q ^ 16 + A / q ^ 16 := by
    ring
  linarith

/-- **The residual against `mainA`**: `residual_le` with `ψ = |ψ(1)|`, `L = Λ̂(w(c, 2))`, `E = C_E`, whose right side is
`c^{−1/8}·mainA c g`. -/
theorem residual_le_mainA {c J KA K0c Kb T ηB F G : ℝ} {g : ℝ → ℝ}
    (hc : exp 1360 ≤ c) (hJ : J ≤ c / 4 + 1) (hKA : KA ≤ √2 * exp 25)
    (hF : F ≤ KA * |psi c g 1|) (hG : G ≤ 2 * KA * √(c / π) * |psi c g 1|)
    (hK0 : K0c ≤ 23 * G / c ^ 2) (hKb0 : 0 ≤ Kb) (hKb : Kb ≤ 64 * F / c + 1040 * G / c ^ 2)
    (hT : T ≤ 10 ^ 6 * KA * |psi c g 1| * c ^ (-(3 / 4 : ℝ)))
    (hη0 : 0 ≤ ηB) (hη : ηB ≤ 700 * F / c) :
    G * √(54 * (π ^ 2 / 12 - 11 / 16) / (π * c ^ 3))
        + K0c * √(c * collarK (deltaS c) (deltaS c))
        + Kb * tauBar c (1 / 2) (deltaS c) (1 / 4) * √(8 * (1 + 1 / deltaS c) * J)
        + T + ηB
      ≤ 1 * c ^ (-(1 / 8 : ℝ)) * mainA c g := by
  have hc0 : 0 < c := lt_of_lt_of_le (exp_pos _) hc
  have hc1 : 2 ≤ c := by linarith [Real.add_one_le_exp (1360 : ℝ)]
  have hw : 0 ≤ Cvs.Prolate.BandMassLaw.wUp c 2 ∧ Cvs.Prolate.BandMassLaw.wUp c 2 ≤ 1 := by
    rw [Cvs.L2a.BandECouplingCollar.wUp_two_eq]
    exact ⟨by positivity, by rw [div_le_iff₀ (by positivity)]; linarith⟩
  have h := residual_le (ψ1 := |psi c g 1|) (L := lamHat (Cvs.Prolate.BandMassLaw.wUp c 2)) (E := cE)
    hc hJ (abs_nonneg _) (Cvs.L2a.BandECouplingCollar.one_le_lamHat hw.1 hw.2) Cvs.L2a.BandECouplingCollar.cE_ge hKA
    hF hG hK0 hKb0 hKb hT hη0 hη
  rwa [sq_abs] at h

/-- **The clause-(6) residual on the span** at `c = 2πx ≥ e¹³⁶⁰`, `J = x`, `F = K_A|ψ(1)|`, `G = ‖g‖₁`, in the form of
`BandInputs`' last clause at `K_r = 1`. -/
theorem residual_span {x : ℕ} {g : ℝ → ℝ} {KA K0c Kb T ηB : ℝ}
    (hx : exp 1360 ≤ 2 * π * x) (hKA : KA ≤ √2 * exp 25)
    (hG : gL1 g ≤ 2 * KA * √((2 * π * x) / π) * |psi (2 * π * x) g 1|)
    (hK0 : K0c ≤ 23 * gL1 g / (2 * π * x) ^ 2) (hKb0 : 0 ≤ Kb)
    (hKb : Kb ≤ 64 * (KA * |psi (2 * π * x) g 1|) / (2 * π * x) + 1040 * gL1 g / (2 * π * x) ^ 2)
    (hT : T ≤ 10 ^ 6 * KA * |psi (2 * π * x) g 1| * (2 * π * x) ^ (-(3 / 4 : ℝ)))
    (hη0 : 0 ≤ ηB) (hη : ηB ≤ 700 * (KA * |psi (2 * π * x) g 1|) / (2 * π * x)) :
    gL1 g * √(54 * (π ^ 2 / 12 - 11 / 16) / (π * (2 * π * x) ^ 3))
        + K0c * √((2 * π * x) * collarK (deltaS (2 * π * x)) (deltaS (2 * π * x)))
        + Kb * tauBar (2 * π * x) (1 / 2) (deltaS (2 * π * x)) (1 / 4)
          * √(8 * (1 + 1 / deltaS (2 * π * x)) * (Fintype.card (Finset.range x) : ℝ))
        + T + ηB
      ≤ 1 * (2 * π * x) ^ (-(1 / 8 : ℝ)) * mainA (2 * π * x) g := by
  have hJ : (Fintype.card (Finset.range x) : ℝ) ≤ 2 * π * x / 4 + 1 := by
    rw [Fintype.card_coe, Finset.card_range]
    have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg x
    nlinarith [pi_gt_three]
  exact residual_le_mainA hx hJ hKA le_rfl hG hK0 hKb0 hKb hT hη0 hη

end Cvs.L2a.BandInputsClauseSixResidual
