import Mathlib
import Cvs.Prolate.Mellin.ForcingSmallBound
import Cvs.Prolate.Mellin.FrozenRootErrorIdentity
import Cvs.Prolate.Mellin.NearRegionBetaStep

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Exact identities for the frozen forcing

With `r = (s+2)/(s+1)`, `ρ = ρ*(s)`, `ρ′ = ρ*(s+2)`, `A = rρρ′`, `β = B/(1+A)`, `p = 1 + rρ²`, `q = 1 + rρ′²`:
`(1 − β)(1 + A) = p`, `(1 + A)² = pq − r(ρ′ − ρ)²`, and with `r′ = r(s+2)`, `p′ = 1 + r′ρ′²`:
`q(1 + r′) − p′(1 + r) = (r − r′)(ρ′² − 1)`.
-/

noncomputable section

namespace Cvs.Prolate.Mellin.FrozenForcingIdentities

open Cvs.Prolate.Mellin.FrozenRootErrorIdentity Cvs.Prolate.Mellin.ForcingSmallBound Cvs.Prolate.Mellin.NearRegionBetaStep

/-- `r(s) = (s+2)/(s+1)`. -/
def rr (s : ℂ) : ℂ := (s + 2) / (s + 1)

/-- `p = 1 + rρ²`. -/
def pp (c χ : ℝ) (s : ℂ) : ℂ := 1 + rr s * rhoStar c χ s ^ 2

/-- `q = 1 + rρ′²`. -/
def qq (c χ : ℝ) (s : ℂ) : ℂ := 1 + rr s * rhoStar c χ (s + 2) ^ 2

theorem Af_eq (c χ : ℝ) (s : ℂ) : Af c χ s = rr s * rhoStar c χ s * rhoStar c χ (s + 2) := by
  unfold Af rr; ring

theorem Bf_eq (c χ : ℝ) (s : ℂ) :
    Bf c χ s = rr s * rhoStar c χ s * rhoStar c χ (s + 2) - rr s * rhoStar c χ s ^ 2 := by
  unfold Bf rr; ring

/-- `(1 − β)(1 + A) = p`. -/
theorem one_sub_betaf_mul {c χ : ℝ} {s : ℂ} (hA : 1 + Af c χ s ≠ 0) :
    (1 - betaf c χ s) * (1 + Af c χ s) = pp c χ s := by
  unfold betaf pp
  rw [Bf_eq, Af_eq] at *
  field_simp
  ring

/-- `(1 + A)² = pq − r(ρ′ − ρ)²`. -/
theorem one_add_Af_sq (c χ : ℝ) (s : ℂ) :
    (1 + Af c χ s) ^ 2 = pp c χ s * qq c χ s - rr s * (rhoStar c χ (s + 2) - rhoStar c χ s) ^ 2 := by
  unfold pp qq; rw [Af_eq]; ring

/-- The `r`-shift identity. -/
theorem shift_identity (c χ : ℝ) (s : ℂ) :
    qq c χ s * (1 + rr (s + 2)) - pp c χ (s + 2) * (1 + rr s)
      = (rr s - rr (s + 2)) * (rhoStar c χ (s + 2) ^ 2 - 1) := by
  unfold pp qq; ring

theorem rr_sub {s : ℂ} (h1 : s + 1 ≠ 0) (h3 : s + 3 ≠ 0) : rr s - rr (s + 2) = 2 / ((s + 1) * (s + 3)) := by
  unfold rr
  rw [show s + 2 + 2 = s + 4 by ring, show s + 2 + 1 = s + 3 by ring]
  field_simp; ring

/-- `|log ‖1 + z‖| ≤ (3/2)‖z‖` for `‖z‖ ≤ 1/2`. -/
theorem abs_log_norm_one_add_le {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) : |Real.log ‖1 + z‖| ≤ 3 / 2 * ‖z‖ := by
  have h := Complex.norm_log_one_add_sub_self_le (z := z) (by linarith)
  have hre : Real.log ‖1 + z‖ = (Complex.log (1 + z)).re := (Complex.log_re _).symm
  rw [hre]
  have h1 : ‖Complex.log (1 + z)‖ ≤ ‖z‖ + ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 := by
    have := norm_add_le (Complex.log (1 + z) - z) z
    rw [sub_add_cancel] at this; linarith
  have h2 : ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 ≤ ‖z‖ / 2 := by
    have hz0 := norm_nonneg z
    have : (1 - ‖z‖)⁻¹ ≤ 2 := by rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    calc ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 ≤ ‖z‖ ^ 2 * 2 / 2 := by gcongr
      _ = ‖z‖ * ‖z‖ := by ring
      _ ≤ ‖z‖ * (1 / 2) := by gcongr
      _ = ‖z‖ / 2 := by ring
  exact (Complex.abs_re_le_norm _).trans (by linarith)

/-- **One step of the forcing in modulus.** If `(1 − β)(1 + A) = p` and `(1 + A)² = pq − e` with `‖β‖ ≤ 1/2`,
`‖e/(pq)‖ ≤ 1/2`, then `|Re β − ½(log‖q‖ − log‖p‖)| ≤ ‖β‖² + (3/4)‖e/(pq)‖`. -/
theorem step_re {β A p q e : ℂ} (h1 : (1 - β) * (1 + A) = p) (h2 : (1 + A) ^ 2 = p * q - e) (hA : 1 + A ≠ 0)
    (hp : p ≠ 0) (hq : q ≠ 0) (hβ : ‖β‖ ≤ 1 / 2) (hw : ‖e / (p * q)‖ ≤ 1 / 2) :
    |β.re - 1 / 2 * (Real.log ‖q‖ - Real.log ‖p‖)| ≤ ‖β‖ ^ 2 + 3 / 4 * ‖e / (p * q)‖ := by
  have hβ1 : 1 - β ≠ 0 := by
    intro h0; have : ‖β‖ = 1 := by rw [show β = 1 by linear_combination -h0]; simp
    linarith
  -- `log‖1 − β‖ = log‖p‖ − log‖1 + A‖`
  have e1 : Real.log ‖1 - β‖ = Real.log ‖p‖ - Real.log ‖1 + A‖ := by
    rw [← h1, norm_mul, Real.log_mul (norm_ne_zero_iff.mpr hβ1) (norm_ne_zero_iff.mpr hA)]; ring
  -- `2 log‖1 + A‖ = log‖p‖ + log‖q‖ + log‖1 − e/(pq)‖`
  have e2 : 2 * Real.log ‖1 + A‖ = Real.log ‖p‖ + Real.log ‖q‖ + Real.log ‖1 + -(e / (p * q))‖ := by
    have : (1 + A) ^ 2 = p * q * (1 + -(e / (p * q))) := by rw [h2]; field_simp; ring
    have hne : 1 + -(e / (p * q)) ≠ 0 := by
      intro h0; rw [h0, mul_zero] at this; exact hA (pow_eq_zero_iff two_ne_zero |>.mp this)
    rw [show (2 : ℝ) * Real.log ‖1 + A‖ = Real.log (‖1 + A‖ ^ 2) by rw [Real.log_pow]; norm_num,
      ← norm_pow, this, norm_mul, norm_mul,
      Real.log_mul (by positivity) (norm_ne_zero_iff.mpr hne),
      Real.log_mul (norm_ne_zero_iff.mpr hp) (norm_ne_zero_iff.mpr hq)]
  -- `Re β + log‖1 − β‖` is small
  have e3 : |β.re + Real.log ‖1 - β‖| ≤ ‖β‖ ^ 2 := by
    have h := Complex.norm_log_one_add_sub_self_le (z := -β) (by rw [norm_neg]; linarith)
    rw [norm_neg, sub_neg_eq_add, ← sub_eq_add_neg] at h
    have hre : Real.log ‖1 - β‖ = (Complex.log (1 - β)).re := (Complex.log_re _).symm
    rw [hre, show β.re + (Complex.log (1 - β)).re = (Complex.log (1 - β) + β).re by simp; ring]
    refine (Complex.abs_re_le_norm _).trans (h.trans ?_)
    have : (1 - ‖β‖)⁻¹ ≤ 2 := by rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    calc ‖β‖ ^ 2 * (1 - ‖β‖)⁻¹ / 2 ≤ ‖β‖ ^ 2 * 2 / 2 := by gcongr
      _ = ‖β‖ ^ 2 := by ring
  have e4 := abs_log_norm_one_add_le (z := -(e / (p * q))) (by rw [norm_neg]; exact hw)
  rw [norm_neg] at e4
  have : β.re - 1 / 2 * (Real.log ‖q‖ - Real.log ‖p‖)
      = (β.re + Real.log ‖1 - β‖) + 1 / 2 * Real.log ‖1 + -(e / (p * q))‖ := by
    rw [e1]; linarith
  rw [this]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  linarith

/-- **The shift step in modulus.** -/
theorem step_shift {q p' r r' D : ℂ} (h : q * (1 + r') - p' * (1 + r) = D) (hq : q ≠ 0) (hp' : p' ≠ 0)
    (hr : 1 + r ≠ 0) (hr' : 1 + r' ≠ 0) (hD : ‖D / (p' * (1 + r))‖ ≤ 1 / 2) :
    |Real.log ‖q‖ - Real.log ‖p'‖ - Real.log ‖1 + r‖ + Real.log ‖1 + r'‖| ≤ 3 / 2 * ‖D / (p' * (1 + r))‖ := by
  have e : q * (1 + r') / (p' * (1 + r)) = 1 + D / (p' * (1 + r)) := by
    rw [← h]; field_simp; ring
  have hl := abs_log_norm_one_add_le hD
  rw [← e, norm_div, norm_mul, norm_mul,
    Real.log_div (by positivity) (by positivity),
    Real.log_mul (norm_ne_zero_iff.mpr hq) (norm_ne_zero_iff.mpr hr'),
    Real.log_mul (norm_ne_zero_iff.mpr hp') (norm_ne_zero_iff.mpr hr)] at hl
  have : Real.log ‖q‖ - Real.log ‖p'‖ - Real.log ‖1 + r‖ + Real.log ‖1 + r'‖
      = Real.log ‖q‖ + Real.log ‖1 + r'‖ - (Real.log ‖p'‖ + Real.log ‖1 + r‖) := by ring
  rw [this]; exact hl

/-- **Summing the forcing in modulus.** -/
theorem sum_re_le {β p q r : ℕ → ℂ} {e1 e2 : ℕ → ℝ} (K : ℕ)
    (hstep : ∀ k < K, |(β k).re - 1 / 2 * (Real.log ‖q k‖ - Real.log ‖p k‖)| ≤ e1 k)
    (hshift : ∀ k < K, |Real.log ‖q k‖ - Real.log ‖p (k + 1)‖ - Real.log ‖1 + r k‖ + Real.log ‖1 + r (k + 1)‖|
      ≤ e2 k) :
    |∑ k ∈ Finset.range K, (β k).re - 1 / 2 * (Real.log ‖p K‖ - Real.log ‖p 0‖)
        + 1 / 2 * (Real.log ‖1 + r K‖ - Real.log ‖1 + r 0‖)| ≤ ∑ k ∈ Finset.range K, (e1 k + 1 / 2 * e2 k) := by
  induction K with
  | zero => simp
  | succ K ih =>
    have ih' := ih (fun k hk => hstep k (by omega)) (fun k hk => hshift k (by omega))
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have a1 := hstep K (by omega)
    have a2 := hshift K (by omega)
    have e : ∑ k ∈ Finset.range K, (β k).re + (β K).re - 1 / 2 * (Real.log ‖p (K + 1)‖ - Real.log ‖p 0‖)
          + 1 / 2 * (Real.log ‖1 + r (K + 1)‖ - Real.log ‖1 + r 0‖)
        = (∑ k ∈ Finset.range K, (β k).re - 1 / 2 * (Real.log ‖p K‖ - Real.log ‖p 0‖)
            + 1 / 2 * (Real.log ‖1 + r K‖ - Real.log ‖1 + r 0‖))
          + ((β K).re - 1 / 2 * (Real.log ‖q K‖ - Real.log ‖p K‖))
          + 1 / 2 * (Real.log ‖q K‖ - Real.log ‖p (K + 1)‖ - Real.log ‖1 + r K‖ + Real.log ‖1 + r (K + 1)‖) := by
      ring
    rw [e]
    set X := ∑ k ∈ Finset.range K, (β k).re - 1 / 2 * (Real.log ‖p K‖ - Real.log ‖p 0‖)
        + 1 / 2 * (Real.log ‖1 + r K‖ - Real.log ‖1 + r 0‖)
    set Y := (β K).re - 1 / 2 * (Real.log ‖q K‖ - Real.log ‖p K‖)
    set Z := Real.log ‖q K‖ - Real.log ‖p (K + 1)‖ - Real.log ‖1 + r K‖ + Real.log ‖1 + r (K + 1)‖
    have t1 := abs_add_le (X + Y) (1 / 2 * Z)
    have t2 := abs_add_le X Y
    have t3 : |1 / 2 * Z| = 1 / 2 * |Z| := by rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    linarith

end Cvs.Prolate.Mellin.FrozenForcingIdentities
