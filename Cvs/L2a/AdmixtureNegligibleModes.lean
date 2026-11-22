import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.ModeEnergyArcsineLaw

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The admixture is negligible in the mode energies

`(x + y)² ≤ (1 + δ)x² + (1 + δ⁻¹)y²`, so two-sided bounds of this form for every `δ > 0` give `|X/Y − 1| ≤ 2√q + q`,
`q = Z/Y`. With `ψ_G = ψ_m − αψ₀` (`G = h_m − αh₀`), `Z = α² Σ_M T₀(M)/M`, `|α|` bounded (an earlier result) and
`(1 − λ₀)/(1 − λ_m) → 0` (an earlier result): `Σ_M T_G(M)/M ∼ Σ_M T_m(M)/M ∼ (2/c)(1 − λ_m)S₀` for `m = 2, 4`.
-/

noncomputable section

open Real Set Filter Topology MeasureTheory

namespace Cvs.L2a.AdmixtureNegligibleModes
open Cvs.ZeroCounting

open Cvs.L2a.AngularProlateTailPositive (psi)
open Cvs.Prolate.EvenRungsByIndex (IsLevelIdx lev rung lamR rung_spec)
open Cvs.Prolate.ModeEnergyArcsineLaw (sZero)

/-! ### Two-sided `δ`-bounds -/

/-! ### The mode sums -/

/-- The weighted mode sum `Σ_M w_M ∫_{M+1}^∞ f²`. -/
def modeSum (w : ℕ → ℝ) (f : ℝ → ℝ) : ℝ := ∑' M : ℕ, w M * ∫ t in Ioi ((M : ℝ) + 1), f t ^ 2

/-! ### The rungs -/

/-- The mode weights `1/M`. -/
def wInv (M : ℕ) : ℝ := 1 / ((M : ℝ) + 1)

theorem modeSum_wInv (f : ℝ → ℝ) :
    modeSum wInv f = ∑' M : ℕ, (∫ t in Ioi ((M : ℝ) + 1), f t ^ 2) / ((M : ℝ) + 1) := by
  unfold modeSum wInv; congr 1; funext M; ring

theorem sZero_pos : 0 < sZero :=
  Cvs.Prolate.ModeEnergyArcsineLaw.summable_sZero.tsum_pos (fun M => div_nonneg (arcsin_nonneg.mpr (by positivity))
    (by positivity)) 0 (by norm_num [Real.arcsin_one, Real.pi_pos])

/-- The mode sums of `h₀, h₄, h₈` converge, eventually. -/
theorem eventually_summable {j : ℕ} (hj : j = 0 ∨ j = 2 ∨ j = 4) :
    ∀ᶠ c : ℝ in atTop, Summable fun M : ℕ => wInv M * ∫ t in Ioi ((M : ℝ) + 1), psi c (rung c j) t ^ 2 := by
  filter_upwards [Cvs.Prolate.ModeEnergyArcsineLaw.arcsine_law_even hj one_pos, eventually_gt_atTop 0] with c hA hc
  have hlaw : ∀ M : ℕ, |(∫ t in Ioi ((M : ℝ) + 1), psi c (rung c j) t ^ 2)
      - 2 / π * arcsin (1 / ((M : ℝ) + 1)) * (π / c * (1 - lamR c j))|
        ≤ 1 * (π / c * (1 - lamR c j)) / ((M : ℝ) + 1) := by
    intro M
    have e : 2 / π * arcsin (1 / ((M : ℝ) + 1)) * (π / c * (1 - lamR c j))
        = 2 / c * (1 - lamR c j) * arcsin (1 / ((M : ℝ) + 1)) := by field_simp
    rw [e]; exact hA _ (by linarith [M.cast_nonneg (α := ℝ)])
  have h := (Cvs.Prolate.ModeEnergyArcsineLaw.modeSum_le (T := fun Y => ∫ t in Ioi Y, psi c (rung c j) t ^ 2) hlaw).1
  refine h.congr fun M => ?_
  unfold wInv; ring

end Cvs.L2a.AdmixtureNegligibleModes

end
