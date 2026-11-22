import Mathlib
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.Mellin.ComplexXiLawPastTurning
import Cvs.Prolate.Mellin.GroundRatioLineModulus
import Cvs.Prolate.Mellin.GroundXiLaw
import Cvs.Prolate.Mellin.GroundXiLawModulus
import Cvs.Prolate.Mellin.LawRatioRecurrence
import Cvs.Prolate.Mellin.PastTurningErrorsSummed
import Cvs.Prolate.Mellin.PastTurningForcingSum
import Cvs.Prolate.Mellin.PastTurningRatioComplex
import Cvs.Prolate.Mellin.WkbPhaseLineStart

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The complex Ξ law for the ground prolate past the turning point

For every `0 < ε ≤ 1/16` and `η > 0`, for all large `c`, uniformly in `z ≥ (2 + ε)c`, with `z = 2c cosh φ`:
`|P(½ + iz)/P(½) · e^{−L(c, z)} − 1| ≤ η`, where
`L(c, z) = c(π/2 cosh φ − 1) − ½ log sinh φ + i(c(sinh φ − φ cosh φ) − π/4) − ¼ log((1 + i sinh φ)/2)`.
-/

noncomputable section

open Complex Filter Topology

namespace Cvs.Prolate.Mellin.GroundComplexXiLaw
open Cvs.ZeroCounting

open Cvs.Prolate.Mellin.LawRatioRecurrence (lawRatio)
open Cvs.Prolate.Mellin.PastTurningRatioComplex (EU)
open Cvs.Prolate.Mellin.ComplexXiLawPastTurning (lawU Es law_bound)

variable {ε : ℝ}

theorem tendsto_EU (hε : 0 < ε) : Tendsto (EU ε) atTop (𝓝 0) := by
  set r := Real.sqrt ε
  have hr : 0 < r := Real.sqrt_pos.mpr hε
  set K := 871200 / ε ^ 2 * (1 + 40 / (7 * r)) + (1 + 4 / r) * (660 / ε) + 660 / ε * (16 / ε) * (335 / r)
    + (254100 / ε ^ 2 + 6 / r) + 35 / (2 * ε * r) + 189 / (ε * r)
  have e : ∀ᶠ c : ℝ in atTop, K * (1 / c) = EU ε c := by
    filter_upwards [eventually_gt_atTop 0] with c hc
    unfold EU Cvs.Prolate.Mellin.PastTurningErrorsSummed.E1U Cvs.Prolate.Mellin.PastTurningForcingSum.E2U
    simp only [K, r]
    field_simp
  have := Cvs.Prolate.Mellin.GroundXiLaw.tendsto_inv.const_mul K
  rw [mul_zero] at this
  exact this.congr' e

theorem tendsto_Es (hε : 0 < ε) : Tendsto (Es ε) atTop (𝓝 0) := by
  set r := Real.sqrt ε
  have hr : 0 < r := Real.sqrt_pos.mpr hε
  set K := 3 * (13 / (2 * ε * r)) + 1 / (8 * r) + 41 / ε + 3 / ε
  have e : ∀ᶠ c : ℝ in atTop, K * (1 / c) + 3 * Cvs.Prolate.Mellin.WkbPhaseLineStart.G1 ε c
      + 3 / ε * Cvs.Prolate.Mellin.WkbPhaseLineStart.gam ε c = Es ε c := by
    filter_upwards [eventually_gt_atTop 0] with c hc
    unfold Es
    simp only [K, r]
    field_simp
    ring
  have t := ((Cvs.Prolate.Mellin.GroundXiLaw.tendsto_inv.const_mul K).add
    ((Cvs.Prolate.Mellin.GroundXiLaw.tendsto_G1 hε).const_mul 3)).add
    ((Cvs.Prolate.Mellin.GroundXiLaw.tendsto_gam hε).const_mul (3 / ε))
  simp only [mul_zero, add_zero] at t
  exact t.congr' e

/-- **The complex Ξ law for the ground prolate past the turning point.** -/
theorem xi_law_up (hε : 0 < ε) (hε16 : ε ≤ 1 / 16) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ c : ℝ in atTop, ∀ z : ℝ, (2 + ε) * c ≤ z →
      ‖lawRatio c (Cvs.Prolate.EvenRungsByIndex.rung c 0) ((1 / 2 : ℂ) + I * z) / lawRatio c (Cvs.Prolate.EvenRungsByIndex.rung c 0) (1 / 2)
        * Complex.exp (-lawU c z) - 1‖ ≤ η := by
  set E := fun c => EU ε c + Cvs.Prolate.Mellin.GroundRatioLineModulus.Etot ε c
  have hE : Tendsto E atTop (𝓝 0) := by
    have := (tendsto_EU hε).add (Cvs.Prolate.Mellin.GroundXiLaw.tendsto_Etot hε)
    rwa [add_zero] at this
  have hS := tendsto_Es hε
  have hB : Tendsto (fun c => 2 * E c + (1 + 2 * E c) * (2 * Es ε c)) atTop (𝓝 (2 * 0 + (1 + 2 * 0) * (2 * 0))) :=
    (hE.const_mul 2).add (((hE.const_mul 2).const_add 1).mul (hS.const_mul 2))
  simp only [mul_zero, add_zero] at hB
  have h1 := hB.eventually (ge_mem_nhds hη)
  have h2 := hE.eventually (ge_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))
  have h3 := hS.eventually (ge_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  have h4 := Cvs.Prolate.Mellin.GroundXiLaw.eventually_large hε hε16
  have h5 : ∀ᶠ c : ℝ in atTop, 108 / ε ≤ c := eventually_ge_atTop _
  have h6 : ∀ᶠ c : ℝ in atTop, 2 ≤ ε * c ^ 2 := by
    have : Tendsto (fun c : ℝ => ε * c ^ 2) atTop atTop :=
      (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).const_mul_atTop hε
    exact this.eventually_ge_atTop 2
  filter_upwards [h1, h2, h3, h4, h5, h6] with c hc1 hc2 hc3 hc4 hc5 hc6
  intro z hz
  exact (law_bound hc4 hz hc5 hc6 hc2 hc3).trans hc1

end Cvs.Prolate.Mellin.GroundComplexXiLaw
