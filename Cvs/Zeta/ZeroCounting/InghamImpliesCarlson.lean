import Mathlib
import Cvs.Zeta.ZeroCounting.CarlsonBoundUpperHalf

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Ingham's density exponent implies Carlson's

On `½ ≤ α ≤ 1`, `3(1 − α)/(2 − α) ≤ 4α(1 − α)`, since the difference is `(1 − α)(2α − 1)(2α − 3)/(2 − α) ≤ 0`.
So `N(α, T) = O(T^{3(1−α)/(2−α)} log⁵ T)` gives `CarlsonDensity`, the logarithm going into `T^ε`.
-/

noncomputable section

open Filter Asymptotics Real
open Cvs.Zeta.ZeroCounting.CarlsonBoundUpperHalf (upperCount CarlsonDensity)

namespace Cvs.Zeta.ZeroCounting.InghamImpliesCarlson

/-- Ingham's density theorem `N(α, T) = O(T^{3(1−α)/(2−α)} log⁵ T)` for fixed `½ < α < 1`. -/
def InghamDensity : Prop :=
  ∀ α : ℝ, 1 / 2 < α → α < 1 →
    (fun T : ℝ ↦ (upperCount α T : ℝ)) =O[atTop] (fun T : ℝ ↦ T ^ (3 * (1 - α) / (2 - α)) * Real.log T ^ 5)

/-- **The exponents compare**: `3(1 − α)/(2 − α) ≤ 4α(1 − α)` on `½ ≤ α ≤ 1`. -/
theorem ingham_exp_le {α : ℝ} (h1 : 1 / 2 ≤ α) (h2 : α ≤ 1) :
    3 * (1 - α) / (2 - α) ≤ 4 * α * (1 - α) := by
  rw [div_le_iff₀ (by linarith)]
  nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 h2) (by linarith : (0 : ℝ) ≤ 2 * α - 1))
    (by linarith : (0 : ℝ) ≤ 3 - 2 * α)]

/-- `log⁵ T = O(T^ε)` for every `ε > 0`. -/
theorem log_pow_five_isBigO {ε : ℝ} (hε : 0 < ε) :
    (fun T : ℝ ↦ Real.log T ^ 5) =O[atTop] (fun T : ℝ ↦ T ^ ε) := by
  have h := ((isLittleO_log_rpow_atTop (by positivity : (0 : ℝ) < ε / 5)).isBigO).pow 5
  refine h.congr' (Eventually.of_forall fun _ => rfl) ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  rw [← Real.rpow_natCast, ← Real.rpow_mul hT.le]
  norm_num

/-- **Carlson's density theorem from Ingham's.** -/
theorem carlsonDensity_of_inghamDensity (h : InghamDensity) : CarlsonDensity := by
  intro α ε h1 h2 hε
  refine (h α h1 h2).trans ?_
  have hlog := (isBigO_refl (fun T : ℝ ↦ T ^ (3 * (1 - α) / (2 - α))) atTop).mul (log_pow_five_isBigO hε)
  refine hlog.trans (IsBigO.of_bound 1 ?_)
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
  have hT0 : (0 : ℝ) < T := by linarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity), one_mul,
    ← Real.rpow_add hT0]
  exact Real.rpow_le_rpow_of_exponent_le hT (by linarith [ingham_exp_le h1.le h2.le])

end Cvs.Zeta.ZeroCounting.InghamImpliesCarlson

end
