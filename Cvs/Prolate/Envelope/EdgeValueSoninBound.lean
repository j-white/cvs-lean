import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyLower
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay
import Cvs.Prolate.LiouvilleGreen.SoninFunction

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The prolate's edge value is bounded by its Sonin function one step out

For a solution of `((ξ²−1)ψ')' + (c²ξ² − χ)ψ = 0` on `[1, ξ₁]` with `χ < c²`: the flux obeys
`|(ξ²−1)ψ'| ≤ (ξ−1) q |ψ(1)|`, so `|ψ'| ≤ q|ψ(1)|/2`, and Sonin's `S = ψ² + p ψ'²/q` satisfies
`S(ξ) ≥ ψ(1)² (1 − p(ξ)q(ξ)/4)`: the edge value is controlled by `S` wherever `pq < 4`, with no Bessel asymptotics.
-/

namespace Cvs.Prolate.Envelope.EdgeValueSoninBound

open Set Cvs.Prolate.LiouvilleGreen.SoninFunction

variable {ψ v v' : ℝ → ℝ} {c χ ξ₁ : ℝ}

/-- **The flux bound**: `|(ξ²−1)ψ'(ξ)| ≤ (ξ−1)(c²ξ²−χ)|ψ(1)|` on `[1, ξ₁]`. -/
theorem flux_le (hχ : χ < c ^ 2)
    (hψ : ∀ r ∈ Icc 1 ξ₁, HasDerivAt ψ (v r) r) (hv : ∀ r ∈ Icc 1 ξ₁, HasDerivAt v (v' r) r)
    (hode : ∀ r ∈ Icc 1 ξ₁, (r ^ 2 - 1) * v' r + 2 * r * v r + (c ^ 2 * r ^ 2 - χ) * ψ r = 0)
    {ξ : ℝ} (hξ : ξ ∈ Icc 1 ξ₁) :
    |(ξ ^ 2 - 1) * v ξ| ≤ (ξ - 1) * (c ^ 2 * ξ ^ 2 - χ) * |ψ 1| := by
  have hq : ∀ r ∈ Icc (1 : ℝ) ξ₁, 0 < c ^ 2 * r ^ 2 - χ := fun r hr => by
    have : 1 ≤ r ^ 2 := by nlinarith [hr.1]
    nlinarith [sq_nonneg c]
  have hbound : ∀ r ∈ Icc (1 : ℝ) ξ₁, |ψ r| ≤ |ψ 1| := fun r hr =>
    sq_le_sq.mp (prolate_sq_le_edge hχ hr hψ hv hode)
  -- h± = (ξ−1) q |ψ(1)| ∓ (ξ²−1) v is monotone with h±(1) = 0
  have key : ∀ s : ℝ, s = 1 ∨ s = -1 →
      0 ≤ (ξ - 1) * (c ^ 2 * ξ ^ 2 - χ) * |ψ 1| - s * ((ξ ^ 2 - 1) * v ξ) := by
    intro s hs
    set h := fun r => (r - 1) * (c ^ 2 * r ^ 2 - χ) * |ψ 1| - s * ((r ^ 2 - 1) * v r)
    have hd : ∀ r ∈ Icc 1 ξ₁, HasDerivAt h
        ((c ^ 2 * r ^ 2 - χ) * |ψ 1| + (r - 1) * (2 * c ^ 2 * r) * |ψ 1|
          - s * (2 * r * v r + (r ^ 2 - 1) * v' r)) r := fun r hr => by
      have h1 := (((hasDerivAt_id r).sub_const 1).mul
        (((hasDerivAt_pow 2 r).const_mul (c ^ 2)).sub_const χ)).mul_const |ψ 1|
      have h2 := (((hasDerivAt_pow 2 r).sub_const 1).mul (hv r hr)).const_mul s
      refine (h1.sub h2).congr_deriv ?_
      simp; ring
    have hmono : MonotoneOn h (Icc 1 ξ₁) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc 1 ξ₁)
        (fun r hr => (hd r hr).continuousAt.continuousWithinAt)
      · rw [interior_Icc]; exact fun r hr => (hd r (Ioo_subset_Icc_self hr)).differentiableAt.differentiableWithinAt
      · rw [interior_Icc]; intro r hr
        have hr' := Ioo_subset_Icc_self hr
        rw [(hd r hr').deriv]
        have ho := hode r hr'
        have e : 2 * r * v r + (r ^ 2 - 1) * v' r = -((c ^ 2 * r ^ 2 - χ) * ψ r) := by linarith
        rw [e]
        have hqr := hq r hr'
        have hb := hbound r hr'
        have : 0 ≤ (r - 1) * (2 * c ^ 2 * r) * |ψ 1| := by
          have : 0 ≤ r - 1 := by linarith [hr'.1]
          have : 0 ≤ r := by linarith [hr'.1]
          positivity
        have hsψ : -(s * ψ r) ≤ |ψ 1| := by
          rcases hs with rfl | rfl
          · have := neg_abs_le (ψ r); linarith
          · have := le_abs_self (ψ r); linarith
        nlinarith [mul_le_mul_of_nonneg_left hsψ hqr.le]
    have h1 : h 1 = 0 := by simp [h]
    have := hmono (left_mem_Icc.mpr (le_trans hξ.1 hξ.2)) hξ hξ.1
    rw [h1] at this
    exact this
  rw [abs_le]
  have hp := key 1 (Or.inl rfl)
  have hn := key (-1) (Or.inr rfl)
  constructor <;> linarith

/-- **The derivative bound**: `|ψ'(ξ)| ≤ (c²ξ² − χ)|ψ(1)|/2` on `[1, ξ₁]`. -/
theorem deriv_le (hχ : χ < c ^ 2)
    (hψ : ∀ r ∈ Icc 1 ξ₁, HasDerivAt ψ (v r) r) (hv : ∀ r ∈ Icc 1 ξ₁, HasDerivAt v (v' r) r)
    (hode : ∀ r ∈ Icc 1 ξ₁, (r ^ 2 - 1) * v' r + 2 * r * v r + (c ^ 2 * r ^ 2 - χ) * ψ r = 0)
    {ξ : ℝ} (hξ : ξ ∈ Icc 1 ξ₁) : |v ξ| ≤ (c ^ 2 * ξ ^ 2 - χ) * |ψ 1| / 2 := by
  have hq : 0 < c ^ 2 * ξ ^ 2 - χ := by
    have : 1 ≤ ξ ^ 2 := by nlinarith [hξ.1]
    nlinarith [sq_nonneg c]
  rcases eq_or_lt_of_le hξ.1 with h1 | h1
  · subst h1
    have := hode 1 hξ
    have e : v 1 = -((c ^ 2 * 1 ^ 2 - χ) * ψ 1) / 2 := by linarith
    rw [e, abs_div, abs_neg, abs_mul, abs_of_pos hq, abs_two]
  · have hf := flux_le hχ hψ hv hode hξ
    have hp : 0 < ξ ^ 2 - 1 := by nlinarith
    rw [abs_mul, abs_of_pos hp] at hf
    rw [le_div_iff₀ two_pos]
    have hξ1 : 0 < ξ - 1 := by linarith
    have : (ξ ^ 2 - 1) * |v ξ| * 2 ≤ (ξ ^ 2 - 1) * ((c ^ 2 * ξ ^ 2 - χ) * |ψ 1|) := by
      have e : ξ ^ 2 - 1 = (ξ - 1) * (ξ + 1) := by ring
      have h2 : (ξ - 1) * (c ^ 2 * ξ ^ 2 - χ) * |ψ 1| * 2 ≤ (ξ - 1) * (ξ + 1) * ((c ^ 2 * ξ ^ 2 - χ) * |ψ 1|) := by
        have hQ : 0 ≤ (c ^ 2 * ξ ^ 2 - χ) * |ψ 1| := by positivity
        have k : 0 ≤ (ξ - 1) * ((c ^ 2 * ξ ^ 2 - χ) * |ψ 1|) * (ξ - 1) := by positivity
        have e2 : (ξ - 1) * (ξ + 1) * ((c ^ 2 * ξ ^ 2 - χ) * |ψ 1|) - (ξ - 1) * (c ^ 2 * ξ ^ 2 - χ) * |ψ 1| * 2
            = (ξ - 1) * ((c ^ 2 * ξ ^ 2 - χ) * |ψ 1|) * (ξ - 1) := by ring
        linarith
      rw [e] at hf ⊢; nlinarith
    nlinarith

/-- **Sonin bounded below by the edge**: `S(ξ) ≥ ψ(1)² (1 − p(ξ)q(ξ)/4)` on `[1, ξ₁]`. -/
theorem sonin_ge (hχ : χ < c ^ 2)
    (hψ : ∀ r ∈ Icc 1 ξ₁, HasDerivAt ψ (v r) r) (hv : ∀ r ∈ Icc 1 ξ₁, HasDerivAt v (v' r) r)
    (hode : ∀ r ∈ Icc 1 ξ₁, (r ^ 2 - 1) * v' r + 2 * r * v r + (c ^ 2 * r ^ 2 - χ) * ψ r = 0)
    {ξ : ℝ} (hξ : ξ ∈ Icc 1 ξ₁) :
    ψ 1 ^ 2 * (1 - (ξ ^ 2 - 1) * (c ^ 2 * ξ ^ 2 - χ) / 4)
      ≤ sonin ψ v (fun r => r ^ 2 - 1) (fun r => c ^ 2 * r ^ 2 - χ) ξ := by
  have hq : ∀ r ∈ Icc (1 : ℝ) ξ₁, 0 < c ^ 2 * r ^ 2 - χ := fun r hr => by
    have : 1 ≤ r ^ 2 := by nlinarith [hr.1]
    nlinarith [sq_nonneg c]
  set Φ := fun r => sonin ψ v (fun r => r ^ 2 - 1) (fun r => c ^ 2 * r ^ 2 - χ) r
    + ψ 1 ^ 2 * ((r ^ 2 - 1) * (c ^ 2 * r ^ 2 - χ)) / 4
  have hd : ∀ r ∈ Icc 1 ξ₁, HasDerivAt Φ
      (-(v r ^ 2 * (2 * r * (c ^ 2 * r ^ 2 - χ) + (r ^ 2 - 1) * (2 * c ^ 2 * r))) / (c ^ 2 * r ^ 2 - χ) ^ 2
        + ψ 1 ^ 2 * (2 * r * (c ^ 2 * r ^ 2 - χ) + (r ^ 2 - 1) * (2 * c ^ 2 * r)) / 4) r := fun r hr => by
    have hS := hasDerivAt_sonin (p := fun r => r ^ 2 - 1) (p' := fun r => 2 * r)
      (q := fun r => c ^ 2 * r ^ 2 - χ) (q' := fun r => 2 * c ^ 2 * r) (hq r hr).ne' (hψ r hr) (hv r hr)
      (by simpa using (hasDerivAt_pow 2 r).sub_const 1)
      (by have := ((hasDerivAt_pow 2 r).const_mul (c ^ 2)).sub_const χ; exact this.congr_deriv (by ring))
      (hode r hr)
    have hpq := (((hasDerivAt_pow 2 r).sub_const 1).mul
      (((hasDerivAt_pow 2 r).const_mul (c ^ 2)).sub_const χ)).const_mul (ψ 1 ^ 2) |>.div_const 4
    refine (hS.add hpq).congr_deriv ?_
    simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, mul_one]; ring
  have hmono : MonotoneOn Φ (Icc 1 ξ₁) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 1 ξ₁) (fun r hr => (hd r hr).continuousAt.continuousWithinAt)
    · rw [interior_Icc]; exact fun r hr => (hd r (Ioo_subset_Icc_self hr)).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]; intro r hr
      have hr' := Ioo_subset_Icc_self hr
      rw [(hd r hr').deriv]
      have hqr := hq r hr'
      have hvb := deriv_le hχ hψ hv hode hr'
      have hdpq : 0 ≤ 2 * r * (c ^ 2 * r ^ 2 - χ) + (r ^ 2 - 1) * (2 * c ^ 2 * r) := by
        have : 1 ≤ r := hr'.1
        have : 0 ≤ r ^ 2 - 1 := by nlinarith
        have : 0 ≤ r := by linarith
        positivity
      have hv2 : v r ^ 2 ≤ ψ 1 ^ 2 * (c ^ 2 * r ^ 2 - χ) ^ 2 / 4 := by
        have := pow_le_pow_left₀ (abs_nonneg _) hvb 2
        rw [sq_abs, div_pow, mul_pow, sq_abs] at this
        linarith
      have : v r ^ 2 * (2 * r * (c ^ 2 * r ^ 2 - χ) + (r ^ 2 - 1) * (2 * c ^ 2 * r)) / (c ^ 2 * r ^ 2 - χ) ^ 2
          ≤ ψ 1 ^ 2 * (2 * r * (c ^ 2 * r ^ 2 - χ) + (r ^ 2 - 1) * (2 * c ^ 2 * r)) / 4 := by
        rw [div_le_iff₀ (by positivity)]
        have := mul_le_mul_of_nonneg_right hv2 hdpq
        calc v r ^ 2 * (2 * r * (c ^ 2 * r ^ 2 - χ) + (r ^ 2 - 1) * (2 * c ^ 2 * r))
            ≤ ψ 1 ^ 2 * (c ^ 2 * r ^ 2 - χ) ^ 2 / 4 * (2 * r * (c ^ 2 * r ^ 2 - χ) + (r ^ 2 - 1) * (2 * c ^ 2 * r)) := this
          _ = _ := by ring
      rw [neg_div]; linarith
  have h1 : Φ 1 = ψ 1 ^ 2 := by simp [Φ, sonin]
  have := hmono (left_mem_Icc.mpr (hξ.1.trans hξ.2)) hξ hξ.1
  rw [h1] at this
  simp only [Φ] at this
  nlinarith [this]

open Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval in
/-- **The edge value is bounded by the energy.** For a solution on `[1, ξ₁]` with `0 ≤ χ < c²`, `0 < c`,
`1 < ξ₀ ≤ ξ ≤ ξ₁`, `a(ξ₀)² < 4` and `w(ξ₀) < 2`:
`ψ(1)² ≤ Fac(ξ₀)/(a(ξ₀)(1 − a(ξ₀)²/4)) · G(ξ)`, `G` the Liouville–Green energy of `(ψ, (ξ²−1)ψ')`. -/
theorem edge_le_energy (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχ : χ < c ^ 2)
    (hψ : ∀ r ∈ Icc 1 ξ₁, HasDerivAt ψ (v r) r) (hv : ∀ r ∈ Icc 1 ξ₁, HasDerivAt v (v' r) r)
    (hode : ∀ r ∈ Icc 1 ξ₁, (r ^ 2 - 1) * v' r + 2 * r * v r + (c ^ 2 * r ^ 2 - χ) * ψ r = 0)
    {ξ₀ ξ : ℝ} (h1 : 1 < ξ₀) (h0ξ : ξ₀ ≤ ξ) (hξ₁ : ξ ≤ ξ₁)
    (ha4 : pP ξ₀ * qP c χ ξ₀ < 4) (hW : wP c χ ξ₀ < 2) :
    ψ 1 ^ 2 ≤ Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay.fac c χ ξ₀ / (aP c χ ξ₀ * (1 - pP ξ₀ * qP c χ ξ₀ / 4))
      * energy (aP c χ) ψ (fun r => pP r * v r) ξ := by
  have hc2 : 0 < c ^ 2 := by positivity
  have gt1 : ∀ t ∈ Icc ξ₀ ξ, 1 < t := fun t ht => lt_of_lt_of_le h1 ht.1
  have sub : ∀ t ∈ Icc ξ₀ ξ, t ∈ Icc 1 ξ₁ := fun t ht => ⟨(gt1 t ht).le, ht.2.trans hξ₁⟩
  -- the (ψ, u = p v) system on [ξ₀, ξ]
  have hψu : ∀ t ∈ Icc ξ₀ ξ, HasDerivAt ψ (pP t * v t / pP t) t := fun t ht => by
    have hp : pP t ≠ 0 := (pP_pos (gt1 t ht)).ne'
    rw [mul_div_cancel_left₀ _ hp]; exact hψ t (sub t ht)
  have huu : ∀ t ∈ Icc ξ₀ ξ, HasDerivAt (fun r => pP r * v r) (-(qP c χ t * ψ t)) t := fun t ht => by
    have hp : HasDerivAt pP (2 * t) t := by
      have := (hasDerivAt_pow 2 t).sub_const 1; unfold pP; simpa using this
    refine (hp.mul (hv t (sub t ht))).congr_deriv ?_
    have := hode t (sub t ht); unfold pP qP; linarith
  have hge := Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyLower.prolate_energy_ge h1 h0ξ hc2 hχ0 hχ hψu huu hW
  -- G(ξ₀) = a(ξ₀) S(ξ₀) ≥ a(ξ₀) ψ(1)² (1 − pq/4)
  have hmem : ξ₀ ∈ Icc 1 ξ₁ := ⟨h1.le, h0ξ.trans hξ₁⟩
  have hS := sonin_ge hχ hψ hv hode hmem
  have ha := aP_pos h1 hc2 hχ
  have hq := qP_pos h1 hc2 hχ
  have hpP := pP_pos h1
  have hGS : energy (aP c χ) ψ (fun r => pP r * v r) ξ₀
      = aP c χ ξ₀ * sonin ψ v (fun r => r ^ 2 - 1) (fun r => c ^ 2 * r ^ 2 - χ) ξ₀ := by
    unfold energy sonin
    have hsq := aP_sq h1 hc2 hχ
    simp only [pP, qP] at hsq ⊢
    have hq' : 0 < c ^ 2 * ξ₀ ^ 2 - χ := by simpa [qP] using hq
    have hq'' : ξ₀ ^ 2 * c ^ 2 - χ ≠ 0 := by nlinarith
    field_simp
    rw [hsq]
    field_simp
  have hlow : aP c χ ξ₀ * (ψ 1 ^ 2 * (1 - pP ξ₀ * qP c χ ξ₀ / 4))
      ≤ energy (aP c χ) ψ (fun r => pP r * v r) ξ₀ := by
    rw [hGS]; apply mul_le_mul_of_nonneg_left _ ha.le
    simpa [pP, qP] using hS
  -- G(ξ₀) ≤ Fac G(ξ)
  have hW0 := wP_pos h1 hc2 hχ
  have hd1 : 0 < 1 - wP c χ ξ₀ / 2 := by linarith
  have hfac : energy (aP c χ) ψ (fun r => pP r * v r) ξ₀
      ≤ Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay.fac c χ ξ₀ * energy (aP c χ) ψ (fun r => pP r * v r) ξ := by
    unfold Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay.fac
    have e : energy (aP c χ) ψ (fun r => pP r * v r) ξ₀
        = energy (aP c χ) ψ (fun r => pP r * v r) ξ₀ * (1 - wP c χ ξ₀ / 2) / (1 + wP c χ ξ₀ / 2)
          * Real.exp (-(wP c χ ξ₀ / (2 - wP c χ ξ₀)))
          * ((1 + wP c χ ξ₀ / 2) / (1 - wP c χ ξ₀ / 2) * Real.exp (wP c χ ξ₀ / (2 - wP c χ ξ₀))) := by
      have h2 : 2 - wP c χ ξ₀ ≠ 0 := by linarith
      rw [Real.exp_neg]; field_simp
    rw [e, mul_comm (((1 + _) / _) * _) (energy _ _ _ ξ)]
    exact mul_le_mul_of_nonneg_right hge (by positivity)
  have hden : 0 < aP c χ ξ₀ * (1 - pP ξ₀ * qP c χ ξ₀ / 4) := mul_pos ha (by linarith)
  rw [div_mul_eq_mul_div, le_div_iff₀ hden]
  nlinarith [hlow, hfac]

end Cvs.Prolate.Envelope.EdgeValueSoninBound
