import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.L1FullTailWinfBound
import Cvs.Prolate.RungTailIntegralMass
import Cvs.Prolate.RungTailMassLower
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The cut levels of L1 carry the endpoint exponent `3πc/2` and nothing else

Cvs.Prolate.RungTailMassLower at each rung, `Mᵢ ≥ |μᵢ|³e^{−3πc/2}/(64c)`, and the floor `κP ≤ N` give `N ≥ κe^{−3πc/2}W/(64c)`,
`W = Σ bᵢ²|μᵢ|³`. Hence `log K ≤ 3πc + 2 log(64cD/(κW))` and `log Θ ≤ 3πc/2 + log max(1, 64cB_G²/(κW))`, with `D`
and `B_G` the profile quantities of Cvs.L2a.L1FullTailWinfBound, and `L1SpineDeepSpanUpper`'s bound holds with `B̄` evaluated at these levels.
-/

namespace Cvs.L2a.L1CutLevelExponent

open Real Set MeasureTheory
open Cvs.L2a.AngularProlateTailPositive (psi)
open Cvs.L2a.FullTailConvergence (fullTail BG K1b)

variable {ι : Type} [Fintype ι]

/-! ### The cut levels -/

/-- `log(max(1, x²)) ≤ 2 log y` for `0 ≤ x ≤ y`, `1 ≤ y`. -/
theorem log_max_sq_le {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : 1 ≤ y) :
    Real.log (max 1 (x ^ 2)) ≤ 2 * Real.log y := by
  have h : max 1 (x ^ 2) ≤ y ^ 2 := max_le (by nlinarith) (pow_le_pow_left₀ hx hxy 2)
  calc Real.log (max 1 (x ^ 2)) ≤ Real.log (y ^ 2) := Real.log_le_log (by positivity) h
    _ = 2 * Real.log y := by rw [Real.log_pow]; norm_num

/-- **A level against an exponentially small floor**: if `N ≥ e^{−x}V`, `V > 0`, `0 < N ≤ D`, then
`log max(1, (D/N)²) ≤ 2x + 2 log(D/V)`. -/
theorem log_cutK_le {D N V x : ℝ} (hN : 0 < N) (hV : 0 < V) (hND : N ≤ D) (hfl : exp (-x) * V ≤ N) :
    Real.log (Cvs.L2a.L1FullTailWinfBound.cutK D N) ≤ 2 * x + 2 * Real.log (D / V) := by
  have hD : 0 < D := lt_of_lt_of_le hN hND
  have hy : D / N ≤ exp x * (D / V) := by
    rw [div_le_iff₀ hN]
    have : exp x * (D / V) * N ≥ exp x * (D / V) * (exp (-x) * V) :=
      mul_le_mul_of_nonneg_left hfl (by positivity)
    have e : exp x * (D / V) * (exp (-x) * V) = D := by
      rw [show exp x * (D / V) * (exp (-x) * V) = (exp x * exp (-x)) * D * (V / V) by ring, ← exp_add,
        add_neg_cancel, exp_zero, div_self hV.ne']; ring
    linarith
  have h1 : 1 ≤ D / N := by rw [le_div_iff₀ hN]; linarith
  unfold Cvs.L2a.L1FullTailWinfBound.cutK
  refine (log_max_sq_le (by positivity) hy (h1.trans hy)).trans (le_of_eq ?_)
  rw [Real.log_mul (exp_pos x).ne' (by positivity), Real.log_exp]; ring

/-- **The position level**: if `N ≥ e^{−x}V`, `V > 0`, then `log max(1, B²/N) ≤ x + log max(1, B²/V)`. -/
theorem log_cutΘ_le {B N V x : ℝ} (hN : 0 < N) (hV : 0 < V) (hx : 0 ≤ x) (hfl : exp (-x) * V ≤ N) :
    Real.log (Cvs.L2a.L1FullTailWinfBound.cutΘ B N) ≤ x + Real.log (max 1 (B ^ 2 / V)) := by
  have hy : max 1 (B ^ 2 / N) ≤ exp x * max 1 (B ^ 2 / V) := by
    refine max_le ((one_le_exp hx).trans (le_mul_of_one_le_right (exp_pos x).le (le_max_left _ _))) ?_
    rw [div_le_iff₀ hN]
    have h2 : B ^ 2 / V * V = B ^ 2 := div_mul_cancel₀ _ hV.ne'
    calc B ^ 2 = exp x * (B ^ 2 / V) * (exp (-x) * V) := by
          rw [show exp x * (B ^ 2 / V) * (exp (-x) * V) = (exp x * exp (-x)) * (B ^ 2 / V * V) by ring, ← exp_add,
            add_neg_cancel, exp_zero, one_mul, h2]
      _ ≤ exp x * max 1 (B ^ 2 / V) * N :=
          mul_le_mul (mul_le_mul_of_nonneg_left (le_max_right _ _) (exp_pos x).le) hfl (by positivity)
            (by positivity)
  unfold Cvs.L2a.L1FullTailWinfBound.cutΘ
  calc Real.log (max 1 (B ^ 2 / N)) ≤ Real.log (exp x * max 1 (B ^ 2 / V)) :=
        Real.log_le_log (by positivity) hy
    _ = x + Real.log (max 1 (B ^ 2 / V)) := by
        rw [Real.log_mul (exp_pos x).ne' (by positivity), Real.log_exp]

/-- `B̄` at given level bounds: `2C_π/√κ + a(2c) + 57/c + 8J(1 + ℓ_K)³/κ + 10 + 2ℓ_Θ`. -/
noncomputable def L1sym (c κ J ℓK ℓΘ : ℝ) : ℝ :=
  2 * Cvs.Prolate.RungTailIntegralMass.piConst J c / √κ + Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol (2 * c) + 57 / c
    + 8 * J * (1 + ℓK) ^ 3 / κ + 10 + 2 * ℓΘ

theorem L1const_le {c κ J K Θ ℓK ℓΘ : ℝ} (hκ : 0 < κ) (hJ : 0 ≤ J) (hK : 1 ≤ K)
    (hlK : Real.log K ≤ ℓK) (hlΘ : Real.log Θ ≤ ℓΘ) :
    Cvs.L2a.L1FullTailWinfBound.L1const c κ J K Θ ≤ L1sym c κ J ℓK ℓΘ := by
  unfold Cvs.L2a.L1FullTailWinfBound.L1const L1sym
  have h0 : 0 ≤ 1 + Real.log K := by linarith [Real.log_nonneg hK]
  have h3 : (1 + Real.log K) ^ 3 ≤ (1 + ℓK) ^ 3 := pow_le_pow_left₀ h0 (by linarith) 3
  have h4 : 8 * J * (1 + Real.log K) ^ 3 / κ ≤ 8 * J * (1 + ℓK) ^ 3 / κ :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h3 (by positivity)) hκ.le
  linarith

/-- The tail norm against the endpoint: `e^{−3πc/2}·κW/(64c) ≤ N`, `W = Σ bᵢ²|μᵢ|³`, from Cvs.Prolate.RungTailMassLower at each rung and a
floor `κP ≤ N`. -/
theorem tail_ge_endpoint (b : ι → ℝ) {h h₁ h₂ : ι → ℝ → ℝ} {c κ N : ℝ} {χ μ : ι → ℝ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (h i) (h₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (h₁ i) (h₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (h₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * h₂ i s - 2 * s * h₁ i s - c ^ 2 * s ^ 2 * h i s + χ i * h i s = 0)
    (hc : 1 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hχ : ∀ i, χ i ≤ c ^ 2) (heven : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, h i (-s) = h i s)
    (hnorm : ∀ i, ∫ s in (-1 : ℝ)..1, h i s ^ 2 = 1) (hμ0 : ∀ i, μ i ≠ 0)
    (hμ : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, psi c (h i) s = μ i * h i s) (hκ : 0 ≤ κ)
    (hfloor : κ * ∑ i, b i ^ 2 * (∫ ξ in Ioi 1, psi c (h i) ξ ^ 2) ≤ N) :
    exp (-(3 * π * c / 2)) * (κ * (∑ i, b i ^ 2 * |μ i| ^ 3) / (64 * c)) ≤ N := by
  have hc0 : 0 < c := by linarith
  have hs2 : √2 ^ 3 = 2 * √2 := by rw [pow_succ, Real.sq_sqrt (by norm_num)]
  have hss : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have he : exp (-(π * c / 2)) ^ 3 = exp (-(3 * π * c / 2)) := by
    rw [← exp_nat_mul]; congr 1; push_cast; ring
  have key : ∀ i, exp (-(3 * π * c / 2)) * (κ * (b i ^ 2 * |μ i| ^ 3) / (64 * c))
      = κ * (b i ^ 2 * ((|μ i| * exp (-(π * c / 2)) / √2) ^ 3 / (16 * √2 * c))) := fun i => by
    rw [div_pow, mul_pow, hs2, he]; field_simp; rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; ring
  calc exp (-(3 * π * c / 2)) * (κ * (∑ i, b i ^ 2 * |μ i| ^ 3) / (64 * c))
      = ∑ i, exp (-(3 * π * c / 2)) * (κ * (b i ^ 2 * |μ i| ^ 3) / (64 * c)) := by
        rw [Finset.mul_sum, Finset.sum_div, Finset.mul_sum]
    _ = κ * ∑ i, b i ^ 2 * ((|μ i| * exp (-(π * c / 2)) / √2) ^ 3 / (16 * √2 * c)) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => key i
    _ ≤ κ * ∑ i, b i ^ 2 * (∫ ξ in Ioi 1, psi c (h i) ξ ^ 2) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
          (Cvs.Prolate.RungTailMassLower.mass_ge (hg i) (hg₁ i) (hg₂c i) (hang i) hc (hχ0 i) (hχ i) (heven i) (hnorm i)
            (hμ0 i) (hμ i)) (sq_nonneg (b i))) hκ
    _ ≤ N := hfloor

variable [DecidableEq ι]

end Cvs.L2a.L1CutLevelExponent
