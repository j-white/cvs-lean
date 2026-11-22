import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.NumberTheory.Harmonic.Bounds
import Cvs.L2a.NonresonantCrossIntegral
import Cvs.L2a.NonstationaryCrossPairClosed
import Cvs.Prolate.Envelope.PointwiseEnergyEnvelopes
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.Mellin.MellinKernelSturmLiouville
import Cvs.Prolate.Mellin.ModeMellinBelowGap

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# One mode's Mellin transform on a dyadic piece, below the gap

For the mode `ψ(m·)` on `[s, 2s]` with `ms ≥ 2`, an Euler solution `(y, v)` with `|y| ≤ Y/√τ`, `|v| ≤ V√τ`,
`w + χ ≤ c²` and energy `≤ G` on `[ms, 2ms]`, with `α = (√3/2)√(c²−χ)`:
`|∫_s^{2s} ψ(mτ) y(τ)| ≤ (8/3)(V √(G/(α s))/m + Y √(2cGs))/(c² m² s²)`.
-/

namespace Cvs.Prolate.Mellin.ModeMellinDyadicPiece

open Real Set Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.NonresonantCrossIntegral Cvs.Prolate.Mellin.MellinKernelSturmLiouville

/-- `D ≥ (3/4) c² m² s⁴` at `ms ≥ 2` when `w + χ ≤ c²`. -/
theorem DE_ge {c χ m w s : ℝ} (hm : 0 < m) (hms : 2 ≤ m * s) (hw : 0 ≤ w) (hgap : w + χ ≤ c ^ 2) :
    3 / 4 * c ^ 2 * m ^ 2 * s ^ 4 ≤ DE c χ m w s := by
  unfold DE qm pm
  have hs : 0 < s := by by_contra h; push_neg at h; nlinarith
  have h4 : 4 ≤ m ^ 2 * s ^ 2 := by nlinarith
  have hp : (m ^ 2 * s ^ 2 - 1) / m ^ 2 ≤ s ^ 2 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hpw : (m ^ 2 * s ^ 2 - 1) / m ^ 2 * w ≤ s ^ 2 * w := mul_le_mul_of_nonneg_right hp hw
  have hc : 0 ≤ c ^ 2 := sq_nonneg c
  have : s ^ 2 * (c ^ 2 * m ^ 2 * s ^ 2 - χ) - s ^ 2 * w - 3 / 4 * c ^ 2 * m ^ 2 * s ^ 4
      = s ^ 2 * (c ^ 2 * (m ^ 2 * s ^ 2 / 4) - (w + χ)) := by ring
  have h2 : c ^ 2 ≤ c ^ 2 * (m ^ 2 * s ^ 2 / 4) := by nlinarith
  nlinarith [sq_nonneg s]

/-- `|ψ(ξ)| ≤ √(G/(αξ²))` at `ξ ≥ 2`, `α = (√3/2)√(c²−χ)`. -/
theorem abs_psi_le {c χ G ξ : ℝ} {ψ u : ℝ → ℝ} (hχ0 : 0 ≤ χ) (hχ : χ < c ^ 2) (hξ : 2 ≤ ξ)
    (hG : energy (aP c χ) ψ u ξ ≤ G) :
    |ψ ξ| ≤ √(G / (√3 / 2 * √(c ^ 2 - χ) * ξ ^ 2)) := by
  have hd : 0 < c ^ 2 - χ := by linarith
  have hla := Cvs.Prolate.Envelope.PointwiseEnergyEnvelopes.le_aP hχ0 hχ hξ
  have hb : 0 < √3 / 2 * √(c ^ 2 - χ) * ξ ^ 2 := by
    have : 0 < ξ := by linarith
    positivity
  have ha : 0 < aP c χ ξ := lt_of_lt_of_le hb hla
  have hG0 : 0 ≤ G := le_trans (by unfold energy; positivity) hG
  apply Real.abs_le_sqrt
  calc ψ ξ ^ 2 ≤ energy (aP c χ) ψ u ξ / aP c χ ξ := Cvs.Prolate.Envelope.PointwiseEnergyEnvelopes.sq_le_energy_div ha
    _ ≤ G / aP c χ ξ := div_le_div_of_nonneg_right hG ha.le
    _ ≤ G / (√3 / 2 * √(c ^ 2 - χ) * ξ ^ 2) := div_le_div_of_nonneg_left hG0 hb hla

/-- `|u(ξ)| ≤ ξ √(cG)` at `ξ ≥ 1`. -/
theorem abs_u_le {c χ G ξ : ℝ} {ψ u : ℝ → ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχ : χ < c ^ 2) (hξ : 1 < ξ)
    (hG : energy (aP c χ) ψ u ξ ≤ G) :
    |u ξ| ≤ ξ * √(c * G) := by
  have ha : 0 < aP c χ ξ := aP_pos hξ (by positivity) hχ
  have hle := Cvs.Prolate.Envelope.PointwiseEnergyEnvelopes.aP_le hc hχ0 hξ.le
  have h1 := Cvs.Prolate.Envelope.PointwiseEnergyEnvelopes.flux_sq_le (ψ := ψ) (u := u) ha
  have hE0 : 0 ≤ energy (aP c χ) ψ u ξ := by unfold energy; positivity
  have hG0 : 0 ≤ G := hE0.trans hG
  have h2 : u ξ ^ 2 ≤ c * ξ ^ 2 * G := h1.trans (mul_le_mul hle hG hE0 (by positivity))
  have e : ξ * √(c * G) = √(c * ξ ^ 2 * G) := by
    rw [show c * ξ ^ 2 * G = ξ ^ 2 * (c * G) by ring, sqrt_mul (sq_nonneg _), sqrt_sq (by linarith)]
  rw [e]; exact Real.abs_le_sqrt h2

/-- **One dyadic piece of one mode.** -/
theorem piece_le {c χ m w s G Y V : ℝ} {ψ u y v : ℝ → ℝ}
    (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχ : χ < c ^ 2) (hm : 0 < m) (hms : 2 ≤ m * s) (hw : 0 ≤ w)
    (hgap : w + χ ≤ c ^ 2) (hY : 0 ≤ Y) (hV : 0 ≤ V)
    (hψ : ∀ ξ ∈ Icc (m * s) (m * (2 * s)), HasDerivAt ψ (u ξ / pP ξ) ξ)
    (hu : ∀ ξ ∈ Icc (m * s) (m * (2 * s)), HasDerivAt u (-(qP c χ ξ * ψ ξ)) ξ)
    (hG : ∀ ξ ∈ Icc (m * s) (m * (2 * s)), energy (aP c χ) ψ u ξ ≤ G)
    (hy : ∀ τ ∈ Icc s (2 * s), HasDerivAt y (v τ / τ ^ 2) τ)
    (hv : ∀ τ ∈ Icc s (2 * s), HasDerivAt v (-(w * y τ)) τ)
    (hyb : ∀ τ ∈ Icc s (2 * s), |y τ| ≤ Y / √τ) (hvb : ∀ τ ∈ Icc s (2 * s), |v τ| ≤ V * √τ) :
    |∫ τ in s..2 * s, ψ (m * τ) * y τ|
      ≤ 8 / 3 * (V * √(G / (√3 / 2 * √(c ^ 2 - χ) * s)) / m + Y * √(2 * c * G * s)) / (c ^ 2 * m ^ 2 * s ^ 2) := by
  have hs : 0 < s := by by_contra h; push_neg at h; nlinarith
  have hss : s ≤ 2 * s := by linarith
  set α := √3 / 2 * √(c ^ 2 - χ) with hα
  have hd : 0 < c ^ 2 - χ := by linarith
  have hα0 : 0 < α := by positivity
  have hmem : ∀ τ ∈ Icc s (2 * s), m * τ ∈ Icc (m * s) (m * (2 * s)) := fun τ hτ =>
    ⟨mul_le_mul_of_nonneg_left hτ.1 hm.le, mul_le_mul_of_nonneg_left hτ.2 hm.le⟩
  have hτ0 : ∀ τ ∈ Icc s (2 * s), 0 < τ := fun τ hτ => lt_of_lt_of_le hs hτ.1
  have hmτ : ∀ τ ∈ Icc s (2 * s), 2 ≤ m * τ := fun τ hτ => hms.trans (mul_le_mul_of_nonneg_left hτ.1 hm.le)
  have hsys : ∀ τ ∈ Icc s (2 * s), HasDerivAt (fun r => ψ (m * r)) ((u (m * τ) / m) / pm m τ) τ ∧
      HasDerivAt (fun r => u (m * r) / m) (-(qm c χ m τ * ψ (m * τ))) τ := fun τ hτ =>
    Cvs.L2a.NonstationaryCrossPairClosed.scale_system hm (hψ _ (hmem τ hτ)) (hu _ (hmem τ hτ))
  -- the two sups
  have hZ : ∀ τ ∈ Icc s (2 * s), |ψ (m * τ) * v τ| ≤ V * √(G / (α * s)) / m := fun τ hτ => by
    have hτp := hτ0 τ hτ
    have hG0 : 0 ≤ G := le_trans (by
      have := aP_pos (by linarith [hmτ τ hτ] : 1 < m * τ) (by positivity : 0 < c ^ 2) hχ
      unfold energy; positivity) (hG _ (hmem τ hτ))
    have h1 := abs_psi_le hχ0 hχ (hmτ τ hτ) (hG _ (hmem τ hτ))
    have h2 := hvb τ hτ
    rw [abs_mul]
    calc |ψ (m * τ)| * |v τ| ≤ √(G / (α * (m * τ) ^ 2)) * (V * √τ) :=
          mul_le_mul h1 h2 (abs_nonneg _) (sqrt_nonneg _)
      _ = V * √(G / (α * (m * τ) ^ 2) * τ) := by rw [sqrt_mul (by positivity)]; ring
      _ = V * (√(G / (α * τ)) / m) := by
          rw [show G / (α * (m * τ) ^ 2) * τ = G / (α * τ) / m ^ 2 by field_simp,
            sqrt_div' _ (sq_nonneg m), sqrt_sq hm.le]
      _ ≤ V * (√(G / (α * s)) / m) := by
          apply mul_le_mul_of_nonneg_left _ hV
          apply div_le_div_of_nonneg_right _ hm.le
          exact Real.sqrt_le_sqrt (div_le_div_of_nonneg_left hG0 (by positivity)
            (mul_le_mul_of_nonneg_left hτ.1 hα0.le))
      _ = V * √(G / (α * s)) / m := by ring
  have hV' : ∀ τ ∈ Icc s (2 * s), |u (m * τ) / m * y τ| ≤ Y * √(2 * c * G * s) := fun τ hτ => by
    have hτp := hτ0 τ hτ
    have hG0 : 0 ≤ G := le_trans (by
      have := aP_pos (by linarith [hmτ τ hτ] : 1 < m * τ) (by positivity : 0 < c ^ 2) hχ
      unfold energy; positivity) (hG _ (hmem τ hτ))
    have h1 := abs_u_le hc hχ0 hχ (by linarith [hmτ τ hτ] : 1 < m * τ) (hG _ (hmem τ hτ))
    have h2 := hyb τ hτ
    have hsτ : 0 < √τ := sqrt_pos.mpr hτp
    rw [abs_mul, abs_div, abs_of_pos hm]
    calc |u (m * τ)| / m * |y τ| ≤ m * τ * √(c * G) / m * (Y / √τ) :=
          mul_le_mul (div_le_div_of_nonneg_right h1 hm.le) h2 (abs_nonneg _) (by positivity)
      _ = Y * (√τ * √(c * G)) := by
          have hq := mul_self_sqrt hτp.le
          field_simp
          linear_combination (-(√(c * G) * Y)) * hq
      _ ≤ Y * (√(2 * s) * √(c * G)) := by
          apply mul_le_mul_of_nonneg_left _ hY
          exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hτ.2) (sqrt_nonneg _)
      _ = Y * √(2 * c * G * s) := by
          rw [← sqrt_mul (by linarith)]; ring_nf
  have hDs := DE_ge (c := c) (χ := χ) hm hms hw hgap
  have key := Cvs.Prolate.Mellin.ModeMellinBelowGap.euler_cross_le (c := c) (χ := χ) (m := m) (w := w)
    (f := fun r => ψ (m * r)) (u := fun r => u (m * r) / m) (y := y) (v := v) hss hm (by linarith)
    (fun τ hτ => lt_of_lt_of_le (by have := hτ0 τ hτ; positivity) (DE_ge hm (hmτ τ hτ) hw hgap))
    (fun τ hτ => by
      have h := hmτ τ hτ
      have h4 : 4 ≤ m ^ 2 * τ ^ 2 := by nlinarith
      have : 9 ≤ (m ^ 2 * τ ^ 2 - 1) ^ 2 := by nlinarith
      nlinarith [sq_nonneg c])
    (fun τ hτ => by
      have h := hmτ τ hτ
      have h4 : 4 ≤ m ^ 2 * τ ^ 2 := by nlinarith
      have : 1 ≤ m ^ 4 * τ ^ 4 := by nlinarith
      nlinarith [sq_nonneg c])
    (fun τ hτ => (hsys τ hτ).1) (fun τ hτ => (hsys τ hτ).2) hy hv hZ hV'
  have hpm : pm m s ≤ s ^ 2 := by unfold pm; rw [div_le_iff₀ (by positivity)]; nlinarith
  have hMz : 0 ≤ V * √(G / (α * s)) / m := by positivity
  have hMv : 0 ≤ Y * √(2 * c * G * s) := by positivity
  have hD0 : 0 < 3 / 4 * c ^ 2 * m ^ 2 * s ^ 4 := by positivity
  calc |∫ τ in s..2 * s, ψ (m * τ) * y τ|
      ≤ 2 * (pm m s * (V * √(G / (α * s)) / m) + s ^ 2 * (Y * √(2 * c * G * s))) / DE c χ m w s := key
    _ ≤ 2 * (s ^ 2 * (V * √(G / (α * s)) / m) + s ^ 2 * (Y * √(2 * c * G * s)))
          / (3 / 4 * c ^ 2 * m ^ 2 * s ^ 4) := by
        apply div_le_div₀ (by positivity) _ hD0 hDs
        have := mul_le_mul_of_nonneg_right hpm hMz
        linarith
    _ = 8 / 3 * (V * √(G / (α * s)) / m + Y * √(2 * c * G * s)) / (c ^ 2 * m ^ 2 * s ^ 2) := by
        field_simp; ring

end Cvs.Prolate.Mellin.ModeMellinDyadicPiece
