import Mathlib
import Cvs.Prolate.Hardy.CarrierNegativeFrequencies
import Cvs.Prolate.Hardy.ColumnTwoCarrierWave
import Cvs.Prolate.Hardy.ExteriorSincColumns
import Cvs.Prolate.Hardy.LipPieceHardyLoss
import Cvs.Upstream.JordanArcIntegral

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The column amplitude `A_u` is bounded by `1/(π(u − 3/5))` with its derivative

On `|z| ≤ 3/5 < u`, `|A_u| ≤ 1/(π(u − 3/5))` and `|A_u'| ≤ 1/(π(u − 3/5)²) ≤ (5/2)/(π(u − 3/5))`, from the
partial fractions `A_u = ((sin cu + i cos cu)/(u − z) + (sin cu − i cos cu)/(u + z))/(2π)`; the same bound holds on
the ellipse `cosh(η₀ + iθ)/2`.
-/

noncomputable section

open Real Set
open Complex (I)

namespace Cvs.Prolate.Hardy.ColumnAmplitudeBound
open Cvs.ZeroCounting

open Cvs.Prolate.Hardy.CarrierNegativeFrequencies (eta0)

/-- The partial-fraction form of `A_u`. -/
def ampPF (c u : ℝ) (z : ℂ) : ℂ :=
  ((Real.sin (c * u) + I * Real.cos (c * u)) / (u - z) + (Real.sin (c * u) - I * Real.cos (c * u)) / (u + z)) /
    (2 * π)

/-- Its derivative. -/
def ampPF' (c u : ℝ) (z : ℂ) : ℂ :=
  ((Real.sin (c * u) + I * Real.cos (c * u)) / (u - z) ^ 2 -
    (Real.sin (c * u) - I * Real.cos (c * u)) / (u + z) ^ 2) / (2 * π)

theorem sub_ne {u : ℝ} {z : ℂ} (h : ‖z‖ < u) : (u : ℂ) - z ≠ 0 := fun e => by
  have : z = u := by linear_combination -e
  rw [this, Complex.norm_real, Real.norm_eq_abs] at h
  exact absurd h (not_lt.2 (le_abs_self u))

theorem add_ne {u : ℝ} {z : ℂ} (h : ‖z‖ < u) : (u : ℂ) + z ≠ 0 := fun e => by
  have : z = -u := by linear_combination e
  rw [this, norm_neg, Complex.norm_real, Real.norm_eq_abs] at h
  exact absurd h (not_lt.2 (le_abs_self u))

theorem amp_eq_PF (c u : ℝ) {z : ℂ} (h : ‖z‖ < u) : Cvs.Prolate.Hardy.ExteriorSincColumns.amp c u z = ampPF c u z :=
  Cvs.Prolate.Hardy.ExteriorSincColumns.amp_eq (sub_ne h) (add_ne h)

theorem hasDerivAt_ampPF (c u : ℝ) {z : ℂ} (h : ‖z‖ < u) : HasDerivAt (ampPF c u) (ampPF' c u z) z := by
  have h1 := sub_ne h
  have h2 := add_ne h
  have d1 : HasDerivAt (fun z : ℂ => (u : ℂ) - z) (-1) z := by simpa using (hasDerivAt_id z).const_sub (u : ℂ)
  have d2 : HasDerivAt (fun z : ℂ => (u : ℂ) + z) 1 z := by simpa using (hasDerivAt_id z).const_add (u : ℂ)
  have e1 := (hasDerivAt_const z ((Real.sin (c * u) : ℂ) + I * Real.cos (c * u))).div d1 h1
  have e2 := (hasDerivAt_const z ((Real.sin (c * u) : ℂ) - I * Real.cos (c * u))).div d2 h2
  have := (e1.add e2).div_const (2 * π : ℂ)
  refine this.congr_deriv ?_
  unfold ampPF'
  field_simp
  ring

theorem deriv_amp (c u : ℝ) {z : ℂ} (h : ‖z‖ < u) : deriv (Cvs.Prolate.Hardy.ExteriorSincColumns.amp c u) z = ampPF' c u z := by
  have hev : Cvs.Prolate.Hardy.ExteriorSincColumns.amp c u =ᶠ[nhds z] ampPF c u := by
    have : IsOpen {w : ℂ | ‖w‖ < u} := isOpen_lt continuous_norm continuous_const
    filter_upwards [this.mem_nhds h] with w hw using amp_eq_PF c u hw
  rw [hev.deriv_eq]
  exact (hasDerivAt_ampPF c u h).deriv

theorem le_norm_sub {u L : ℝ} {z : ℂ} (hz : ‖z‖ ≤ L) : u - L ≤ ‖(u : ℂ) - z‖ := by
  have := norm_sub_norm_le (u : ℂ) z
  rw [Complex.norm_real, Real.norm_eq_abs] at this
  linarith [le_abs_self u]

theorem le_norm_add {u L : ℝ} {z : ℂ} (hz : ‖z‖ ≤ L) : u - L ≤ ‖(u : ℂ) + z‖ := by
  have := norm_sub_norm_le (u : ℂ) (-z)
  rw [Complex.norm_real, Real.norm_eq_abs, norm_neg, sub_neg_eq_add] at this
  linarith [le_abs_self u]

/-- `|A_u'(z)| ≤ 1/(π(u − L)²)` on `|z| ≤ L < u`. -/
theorem norm_ampPF'_le {c u L : ℝ} {z : ℂ} (hz : ‖z‖ ≤ L) (hL : L < u) :
    ‖ampPF' c u z‖ ≤ 1 / (π * (u - L) ^ 2) := by
  have hp : 0 < u - L := by linarith
  have hd1 := le_norm_sub (u := u) hz
  have hd2 := le_norm_add (u := u) hz
  unfold ampPF'
  rw [norm_div, show ‖(2 : ℂ) * π‖ = 2 * π by
    rw [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]]
  have ht := norm_sub_le ((Real.sin (c * u) + I * Real.cos (c * u)) / ((u : ℂ) - z) ^ 2)
    ((Real.sin (c * u) - I * Real.cos (c * u)) / ((u : ℂ) + z) ^ 2)
  rw [norm_div, norm_div, Cvs.Prolate.Hardy.ExteriorSincColumns.norm_sin_add_I_mul_cos, Cvs.Prolate.Hardy.ExteriorSincColumns.norm_sin_sub_I_mul_cos, norm_pow, norm_pow] at ht
  have e1 : 1 / ‖(u : ℂ) - z‖ ^ 2 ≤ 1 / (u - L) ^ 2 :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hp.le hd1 2)
  have e2 : 1 / ‖(u : ℂ) + z‖ ^ 2 ≤ 1 / (u - L) ^ 2 :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hp.le hd2 2)
  have hπ := Real.pi_pos
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have : ‖(Real.sin (c * u) + I * Real.cos (c * u)) / ((u : ℂ) - z) ^ 2 -
      (Real.sin (c * u) - I * Real.cos (c * u)) / ((u : ℂ) + z) ^ 2‖ ≤ 2 / (u - L) ^ 2 := by
    calc _ ≤ 1 / ‖(u : ℂ) - z‖ ^ 2 + 1 / ‖(u : ℂ) + z‖ ^ 2 := ht
      _ ≤ 1 / (u - L) ^ 2 + 1 / (u - L) ^ 2 := add_le_add e1 e2
      _ = 2 / (u - L) ^ 2 := by ring
  rw [le_div_iff₀ (by positivity)] at this
  nlinarith

/-- The column amplitude bound `g_u = 1/(π(u − 3/5))`. -/
def gU (u : ℝ) : ℝ := 1 / (π * (u - 3 / 5))

theorem gU_pos {u : ℝ} (hu : 1 < u) : 0 < gU u := by unfold gU; have := Real.pi_pos; apply div_pos one_pos; nlinarith

/-- **`A_u` satisfies the amplitude hypotheses** with `G₀ = g_u`, `G₁ = (5/2)g_u`. -/
theorem ampBound (c : ℝ) {u : ℝ} (hu : 1 < u) : Cvs.Prolate.Hardy.LipPieceHardyLoss.AmpBound (Cvs.Prolate.Hardy.ExteriorSincColumns.amp c u) (gU u) (5 / 2 * gU u) where
  diff := Cvs.Prolate.Hardy.ColumnTwoCarrierWave.differentiableOn_amp c hu
  bound x hx := by
    have : ‖(x : ℂ)‖ ≤ 3 / 5 := by rw [Complex.norm_real, Real.norm_eq_abs, abs_le]; exact hx
    exact Cvs.Prolate.Hardy.ExteriorSincColumns.norm_amp_le this (by linarith)
  dbound x hx := by
    have hx' : ‖(x : ℂ)‖ ≤ 3 / 5 := by rw [Complex.norm_real, Real.norm_eq_abs, abs_le]; exact hx
    rw [deriv_amp c u (by linarith)]
    refine (norm_ampPF'_le hx' (by linarith)).trans ?_
    unfold gU
    have hp : (2 : ℝ) / 5 ≤ u - 3 / 5 := by linarith
    have hπ := Real.pi_pos
    rw [show 5 / 2 * (1 / (π * (u - 3 / 5))) = 5 / 2 / (π * (u - 3 / 5)) by ring,
      div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hp (show 0 ≤ 5 / 2 * π * (u - 3 / 5) by positivity)]

/-- On the ellipse `cosh(η₀ + iθ)/2`, `|A_u| ≤ g_u`. -/
theorem norm_amp_arc_le (c : ℝ) {u : ℝ} (hu : 1 < u) (θ : ℝ) :
    ‖Cvs.Prolate.Hardy.ExteriorSincColumns.amp c u ((1 / 2 : ℂ) * Complex.cosh (eta0 + θ * I))‖ ≤ gU u := by
  have h := Cvs.Upstream.JordanArcIntegral.norm_cosh_arc_le (a := 1 / 2) (η₀ := eta0) (by norm_num) θ
  rw [Cvs.Prolate.Hardy.CarrierNegativeFrequencies.cosh_eta0] at h
  push_cast at h
  exact Cvs.Prolate.Hardy.ExteriorSincColumns.norm_amp_le (by linarith) (by linarith)

end Cvs.Prolate.Hardy.ColumnAmplitudeBound

end
