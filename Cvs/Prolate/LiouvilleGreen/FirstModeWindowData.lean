import Mathlib
import Cvs.Prolate.LiouvilleGreen.DilatedPhaseRates
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.MismatchAboveWindow
import Cvs.Prolate.LiouvilleGreen.MismatchOutsideWindow
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.LiouvilleGreen.RungProfileStationaryPoint
import Cvs.Upstream.SturmLiouvillePrufer

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The window data of a first-mode profile pairing

For the first mode of a prolate rung against the profile of order `m′`, with the window `[c₁, c₂]` around the
stationary point (`c₁² ≤ θ*² − Δ`, `θ*² + Δ ≤ c₂²`), the difference rate `cm′ − Θ'` is at most `−min(L, R)` on
`[p, c₁]` and at least `min(L, R)` on `[c₂, q]` (`L`, `R` the closed forms of Cvs.Prolate.LiouvilleGreen.MismatchOutsideWindow, Cvs.Prolate.LiouvilleGreen.MismatchAboveWindow), and the sum rate
`Θ' + cm′` is at least `c(m′ + 1 − ξ₀/(c(ξ₀² − 1)))` on `[p, q]`: the sign data of Cvs.Upstream.SecondDerivativeWindowTest and Cvs.Upstream.FirstDerivativeTestVariation for Cvs.Prolate.Envelope.RungPairPruferEnvelope.
-/

namespace Cvs.Prolate.LiouvilleGreen.FirstModeWindowData

open Real Set Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.Upstream.SturmLiouvillePrufer Cvs.Prolate.LiouvilleGreen.DilatedPhaseRates Cvs.Prolate.LiouvilleGreen.RungProfileStationaryPoint Cvs.Prolate.LiouvilleGreen.MismatchOutsideWindow Cvs.Prolate.LiouvilleGreen.MismatchAboveWindow

/-- The left mismatch bound of Cvs.Prolate.LiouvilleGreen.MismatchOutsideWindow: `c(m′² − 1)Δ√(p² − 1)/(2p(θ*² − 1)) − (p/√(p² − 1))(p/(p² − 1))`. -/
noncomputable def leftGap (c χ p Δ : ℝ) (m' : ℕ) : ℝ :=
  c * ((m' : ℝ) ^ 2 - 1) * Δ * √(p ^ 2 - 1) / (2 * p * (statSq c χ m' - 1)) - p / √(p ^ 2 - 1) * (p / (p ^ 2 - 1))

/-- The right mismatch bound of Cvs.Prolate.LiouvilleGreen.MismatchAboveWindow: `c(m′² − 1)Δ/(2m′(q² − 1)) − (c₂/√(c₂² − 1))(c₂/(c₂² − 1))`. -/
noncomputable def rightGap (c c₂ q Δ : ℝ) (m' : ℕ) : ℝ :=
  c * ((m' : ℝ) ^ 2 - 1) * Δ / (2 * m' * (q ^ 2 - 1)) - c₂ / √(c₂ ^ 2 - 1) * (c₂ / (c₂ ^ 2 - 1))

/-- **The window data**: the difference rate is at most `−min(L, R)` left of the window and at least `min(L, R)`
right of it, and the sum rate at least `c(m′ + 1 − ξ₀/(c(ξ₀² − 1)))` throughout. -/
theorem window_rates {c χ ξ₀ p c₁ c₂ q Δ : ℝ} {m' : ℕ} {ψ u : ℝ → ℝ} (h0 : 1 < ξ₀) (hp : ξ₀ ≤ p)
    (hpc : p ≤ c₁) (hcc : c₁ ≤ c₂) (hcq : c₂ ≤ q) (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχc : χ < c ^ 2) (hm' : 2 ≤ m')
    (hΔ : 0 ≤ Δ) (hleft : c₁ ^ 2 ≤ statSq c χ m' - Δ) (hright : statSq c χ m' + Δ ≤ c₂ ^ 2)
    (hs : ξ₀ / (c * (ξ₀ ^ 2 - 1)) ≤ 1) (hE : ∀ t ∈ Icc p q, 0 < energy (aP c χ) ψ u t) :
    (∀ t ∈ Icc p c₁, c * m' - rate pP (aP c χ) (wP c χ) (qP c χ) ψ u t
        ≤ -(min (leftGap c χ p Δ m') (rightGap c c₂ q Δ m')))
      ∧ (∀ t ∈ Icc c₂ q, min (leftGap c χ p Δ m') (rightGap c c₂ q Δ m')
        ≤ c * m' - rate pP (aP c χ) (wP c χ) (qP c χ) ψ u t)
      ∧ ∀ t ∈ Icc p q, c * (m' + 1 * (1 - ξ₀ / (c * (ξ₀ ^ 2 - 1))))
        ≤ rate pP (aP c χ) (wP c χ) (qP c χ) ψ u t + c * m' := by
  have hp1 : 1 < p := lt_of_lt_of_le h0 hp
  have hc2' : 1 < c₂ := lt_of_lt_of_le hp1 (hpc.trans hcc)
  refine ⟨fun t ht => ?_, fun t ht => ?_, fun t ht => ?_⟩
  · -- left of the window
    have hpt : p ≤ t := ht.1
    have ht1 : 1 < t := lt_of_lt_of_le hp1 hpt
    have htc : t ≤ c₁ := ht.2
    have hbelow : t ^ 2 ≤ statSq c χ m' - Δ :=
      le_trans (pow_le_pow_left₀ (by linarith) htc 2) hleft
    have hEt := hE t ⟨hpt, htc.trans (hcc.trans hcq)⟩
    have hL : leftGap c χ p Δ m' ≤ rate pP (aP c χ) (wP c χ) (qP c χ) ψ u t - c * m' := by
      unfold leftGap
      exact rate_sub_profile_ge_explicit (χ := χ) (ψ := ψ) (u := u) hp1 hpt hc hχ0 hχc hm' hΔ hbelow hEt
    have hmin : min (leftGap c χ p Δ m') (rightGap c c₂ q Δ m') ≤ leftGap c χ p Δ m' := min_le_left _ _
    linarith
  · -- right of the window
    have hct : c₂ ≤ t := ht.1
    have htq : t ≤ q := ht.2
    have habove : statSq c χ m' + Δ ≤ t ^ 2 :=
      le_trans hright (pow_le_pow_left₀ (by linarith) hct 2)
    have hEt := hE t ⟨(hpc.trans hcc).trans hct, htq⟩
    have hR : rightGap c c₂ q Δ m' ≤ c * m' - rate pP (aP c χ) (wP c χ) (qP c χ) ψ u t := by
      unfold rightGap
      exact profile_sub_rate_ge_explicit (χ := χ) (ψ := ψ) (u := u) hc2' hct htq hc hχ0 hχc hm' hΔ habove hEt
    have hmin : min (leftGap c χ p Δ m') (rightGap c c₂ q Δ m') ≤ rightGap c c₂ q Δ m' := min_le_right _ _
    linarith
  · -- the sum phase never stalls
    have hpt : p ≤ t := ht.1
    have hθ : ξ₀ ≤ (1 : ℕ) * t := by simp only [Nat.cast_one, one_mul]; linarith
    have hEt := hE t ht
    have hE1 : 0 < energy (aP c χ) ψ u ((1 : ℕ) * t) := by simpa using hEt
    have := (dilate_rate_bounds (ψ := ψ) (u := u) (m := 1) le_rfl h0 hθ hc hχ0 hχc hs hE1).1
    simp only [Nat.cast_one, one_mul] at this
    linarith

end Cvs.Prolate.LiouvilleGreen.FirstModeWindowData
