import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.SpanPoleMellinFromRungs
import Cvs.Prolate.Envelope.PointwiseEnergyEnvelopes
import Cvs.Prolate.Gram.RungGramFloorAtInfinity
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.LiouvilleGreen.RungFrequencyWindow
import Cvs.Prolate.ProlateWindowMassIdentity
import Cvs.Prolate.RungConnectionIdentity

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The count envelope

With `R(ξ) = √(E/a)`: `|ψ| ≤ R`, `|u|/p ≤ cξ/√(ξ² − 1)·R`, and `ProlateWindowMassIdentity`'s `E ≤ 6c∫₁^X ψ²` with `RungConnectionIdentity`'s `a ≥ c(ξ² − 1)` give
`Σᵢ Rᵢ(ξ)²/∫₁^X ψᵢ² ≤ 6J/(ξ² − 1)` on `[6/5, X]` for rungs with `0 ≤ χᵢ < c²`; `SpanPoleMellinFromRungs`'s mass-weighted Cauchy–Schwarz
then bounds `Σᵢⱼ|aᵢaⱼ|Rᵢ(ξ)Rⱼ(η)` by `6J/√((ξ² − 1)(η² − 1))·Σ aᵢ²∫₁^X ψᵢ²`.
-/

namespace Cvs.Prolate.Envelope.RungCountEnvelope

open Real Set Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.AngularProlateTailPositive Cvs.Prolate.Gram.RungGramFloorAtInfinity Cvs.L2a.SpanPoleMellinFromRungs

/-- The rung amplitude `R(ξ) = √(E(ξ)/a(ξ))`. -/
noncomputable def rungAmp (c χ : ℝ) (g : ℝ → ℝ) (ξ : ℝ) : ℝ :=
  √(energy (aP c χ) (psi c g) (rungU c g) ξ / aP c χ ξ)

theorem abs_psi_le_rungAmp {c χ ξ : ℝ} {g : ℝ → ℝ} (hξ : 1 < ξ) (hc : 0 < c) (hχc : χ < c ^ 2) :
    |psi c g ξ| ≤ rungAmp c χ g ξ := by
  have hc2 : 0 < c ^ 2 := by positivity
  have ha := aP_pos hξ hc2 hχc
  unfold rungAmp
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (Cvs.Prolate.Envelope.PointwiseEnergyEnvelopes.sq_le_energy_div (ψ := psi c g) (u := rungU c g) ha)

theorem abs_rungU_le_rungAmp {c χ ξ : ℝ} {g : ℝ → ℝ} (hξ : 1 < ξ) (hc : 0 < c) (hχ0 : 0 ≤ χ)
    (hχc : χ < c ^ 2) : |rungU c g ξ| ≤ c * ξ * √(ξ ^ 2 - 1) * rungAmp c χ g ξ := by
  have hc2 : 0 < c ^ 2 := by positivity
  have ha := aP_pos hξ hc2 hχc
  have hp : 0 < ξ ^ 2 - 1 := by nlinarith
  have hE : 0 ≤ energy (aP c χ) (psi c g) (rungU c g) ξ :=
    le_trans (by positivity) (two_mul_abs_le_energy (ψ := psi c g) (u := rungU c g) ha)
  -- `|u| ≤ a R`
  have h1 : |rungU c g ξ| ≤ aP c χ ξ * rungAmp c χ g ξ := by
    have hsq := Cvs.Prolate.Envelope.PointwiseEnergyEnvelopes.flux_sq_le (ψ := psi c g) (u := rungU c g) ha
    unfold rungAmp
    have e : aP c χ ξ * energy (aP c χ) (psi c g) (rungU c g) ξ
        = (aP c χ ξ * √(energy (aP c χ) (psi c g) (rungU c g) ξ / aP c χ ξ)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (div_nonneg hE ha.le)]; field_simp
    rw [e] at hsq
    exact abs_le_of_sq_le_sq' hsq (by positivity) |>.2 |> fun h2 =>
      abs_le.mpr ⟨(abs_le_of_sq_le_sq' hsq (by positivity)).1, h2⟩ |> fun h => by
        rw [abs_le]; exact abs_le.mp h
  -- `a ≤ cξ√(ξ² − 1)` from the frequency bound
  have hfreq := (Cvs.Prolate.LiouvilleGreen.RungFrequencyWindow.freq_bounds hξ hc hχ0 hχc).2
  have hpP : pP ξ = ξ ^ 2 - 1 := rfl
  have hs : 0 < √(ξ ^ 2 - 1) := Real.sqrt_pos.mpr hp
  have ha2 : aP c χ ξ ≤ c * ξ * √(ξ ^ 2 - 1) := by
    rw [hpP, div_le_div_iff₀ hp hs] at hfreq
    have hss : √(ξ ^ 2 - 1) * √(ξ ^ 2 - 1) = ξ ^ 2 - 1 := Real.mul_self_sqrt hp.le
    have h3 : aP c χ ξ * √(ξ ^ 2 - 1) ≤ c * ξ * √(ξ ^ 2 - 1) * √(ξ ^ 2 - 1) := by
      rw [mul_assoc (c * ξ), hss]; exact hfreq
    exact le_of_mul_le_mul_right h3 hs
  have hR : 0 ≤ rungAmp c χ g ξ := Real.sqrt_nonneg _
  exact h1.trans (mul_le_mul_of_nonneg_right ha2 hR)

theorem abs_rungU_div_le_rungAmp {c χ ξ : ℝ} {g : ℝ → ℝ} (hξ : 1 < ξ) (hc : 0 < c) (hχ0 : 0 ≤ χ)
    (hχc : χ < c ^ 2) : |rungU c g ξ| / pP ξ ≤ c * (ξ / √(ξ ^ 2 - 1)) * rungAmp c χ g ξ := by
  have hp : 0 < ξ ^ 2 - 1 := by nlinarith
  have hs : 0 < √(ξ ^ 2 - 1) := Real.sqrt_pos.mpr hp
  have h := abs_rungU_le_rungAmp (g := g) hξ hc hχ0 hχc
  have hpP : pP ξ = ξ ^ 2 - 1 := rfl
  rw [hpP, div_le_iff₀ hp]
  have e : c * (ξ / √(ξ ^ 2 - 1)) * rungAmp c χ g ξ * (ξ ^ 2 - 1) = c * ξ * √(ξ ^ 2 - 1) * rungAmp c χ g ξ := by
    have hss : √(ξ ^ 2 - 1) * √(ξ ^ 2 - 1) = ξ ^ 2 - 1 := Real.mul_self_sqrt hp.le
    calc c * (ξ / √(ξ ^ 2 - 1)) * rungAmp c χ g ξ * (ξ ^ 2 - 1)
        = c * (ξ / √(ξ ^ 2 - 1)) * rungAmp c χ g ξ * (√(ξ ^ 2 - 1) * √(ξ ^ 2 - 1)) := by rw [hss]
      _ = c * ξ * √(ξ ^ 2 - 1) * rungAmp c χ g ξ := by field_simp
  rw [e]; exact h

theorem rungAmp_sq_le {g g₁ g₂ : ℝ → ℝ} {c χ X ξ : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hc : 80 ≤ c) (hχ0 : 0 ≤ χ) (hχc : χ < c ^ 2) (hX : 2 ≤ X) (hξ : ξ ∈ Icc (6 / 5 : ℝ) X) :
    rungAmp c χ g ξ ^ 2 ≤ 6 * (∫ t in (1 : ℝ)..X, psi c g t ^ 2) / (ξ ^ 2 - 1) := by
  have hξ1 : 1 < ξ := by linarith [hξ.1]
  have hc0 : 0 < c := by linarith
  have hc2 : 0 < c ^ 2 := by positivity
  have ha := aP_pos hξ1 hc2 hχc
  have hE : 0 ≤ energy (aP c χ) (psi c g) (rungU c g) ξ :=
    le_trans (by positivity) (two_mul_abs_le_energy (ψ := psi c g) (u := rungU c g) ha)
  have hfar := Cvs.Prolate.ProlateWindowMassIdentity.far_energy_le_rung hg hg₁ hg₂c hang hc hχ0 hχc hX ξ hξ
  have hlo := Cvs.Prolate.RungConnectionIdentity.le_aP_far (c := c) (χ := χ) hχc.le hξ1.le
  have hp : 0 < ξ ^ 2 - 1 := by nlinarith
  unfold rungAmp
  rw [Real.sq_sqrt (div_nonneg hE ha.le)]
  have hm : 0 ≤ ∫ t in (1 : ℝ)..X, psi c g t ^ 2 :=
    intervalIntegral.integral_nonneg (by linarith) fun _ _ => sq_nonneg _
  rw [div_le_div_iff₀ ha hp]
  calc energy (aP c χ) (psi c g) (rungU c g) ξ * (ξ ^ 2 - 1)
      ≤ 6 * c * (∫ t in (1 : ℝ)..X, psi c g t ^ 2) * (ξ ^ 2 - 1) := mul_le_mul_of_nonneg_right hfar hp.le
    _ = 6 * (∫ t in (1 : ℝ)..X, psi c g t ^ 2) * (c * (ξ ^ 2 - 1)) := by ring
    _ ≤ 6 * (∫ t in (1 : ℝ)..X, psi c g t ^ 2) * aP c χ ξ := mul_le_mul_of_nonneg_left hlo (by positivity)

variable {ι : Type} [Fintype ι]

/-- **The count envelope**: `Σᵢ Rᵢ(ξ)²/∫₁^X ψᵢ² ≤ 6J/(ξ² − 1)` on `[6/5, X]`. -/
theorem count_envelope {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} {X ξ : ℝ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2) (hX : 2 ≤ X)
    (hM : ∀ i, 0 < ∫ t in (1 : ℝ)..X, psi c (g i) t ^ 2) (hξ : ξ ∈ Icc (6 / 5 : ℝ) X) :
    massSum (fun i => rungAmp c (χ i) (g i) ξ) (fun i => ∫ t in (1 : ℝ)..X, psi c (g i) t ^ 2)
      ≤ 6 * (Fintype.card ι : ℝ) / (ξ ^ 2 - 1) := by
  have hξ1 : 1 < ξ := by linarith [hξ.1]
  have hp : 0 < ξ ^ 2 - 1 := by nlinarith
  unfold massSum
  have h : ∀ i, rungAmp c (χ i) (g i) ξ ^ 2 / (∫ t in (1 : ℝ)..X, psi c (g i) t ^ 2) ≤ 6 / (ξ ^ 2 - 1) := by
    intro i
    rw [div_le_iff₀ (hM i)]
    have := rungAmp_sq_le (hg i) (hg₁ i) (hg₂c i) (hang i) hc (hχ0 i) (hχc i) hX hξ
    calc _ ≤ _ := this
      _ = 6 / (ξ ^ 2 - 1) * ∫ t in (1 : ℝ)..X, psi c (g i) t ^ 2 := by ring
  calc ∑ i, rungAmp c (χ i) (g i) ξ ^ 2 / (∫ t in (1 : ℝ)..X, psi c (g i) t ^ 2)
      ≤ ∑ _i : ι, 6 / (ξ ^ 2 - 1) := Finset.sum_le_sum fun i _ => h i
    _ = 6 * (Fintype.card ι : ℝ) / (ξ ^ 2 - 1) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

theorem two_point_le {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ) {X ξ η : ℝ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2) (hX : 2 ≤ X)
    (hM : ∀ i, 0 < ∫ t in (1 : ℝ)..X, psi c (g i) t ^ 2)
    (hξ : ξ ∈ Icc (6 / 5 : ℝ) X) (hη : η ∈ Icc (6 / 5 : ℝ) X) :
    (∑ i, |a i| * rungAmp c (χ i) (g i) ξ) * (∑ j, |a j| * rungAmp c (χ j) (g j) η)
      ≤ 6 * (Fintype.card ι : ℝ) / √((ξ ^ 2 - 1) * (η ^ 2 - 1))
        * ∑ i, a i ^ 2 * ∫ t in (1 : ℝ)..X, psi c (g i) t ^ 2 := by
  set m : ι → ℝ := fun i => ∫ t in (1 : ℝ)..X, psi c (g i) t ^ 2 with hmdef
  have hm : ∀ i, 0 < m i := hM
  have hR : ∀ ζ i, 0 ≤ rungAmp c (χ i) (g i) ζ := fun _ _ => Real.sqrt_nonneg _
  have hS : ∀ ζ, |∑ i, |a i| * rungAmp c (χ i) (g i) ζ|
      ≤ √(∑ i, |a i| ^ 2 * m i) * √(massSum (fun i => rungAmp c (χ i) (g i) ζ) m) := fun ζ =>
    abs_sum_le_mass (fun i => |a i|) (fun i => rungAmp c (χ i) (g i) ζ) (fun i => rungAmp c (χ i) (g i) ζ) m hm
      fun i => (abs_of_nonneg (hR ζ i)).le
  have hA : ∑ i, |a i| ^ 2 * m i = ∑ i, a i ^ 2 * m i := Finset.sum_congr rfl fun i _ => by rw [sq_abs]
  set P := ∑ i, a i ^ 2 * m i with hP
  have hP0 : 0 ≤ P := Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (hm i).le
  have hξ1 : 1 < ξ := by linarith [hξ.1]
  have hη1 : 1 < η := by linarith [hη.1]
  have hpξ : 0 < ξ ^ 2 - 1 := by nlinarith
  have hpη : 0 < η ^ 2 - 1 := by nlinarith
  have hMξ := count_envelope hg hg₁ hg₂c hang hc hχ0 hχc hX hM hξ
  have hMη := count_envelope hg hg₁ hg₂c hang hc hχ0 hχc hX hM hη
  have h0ξ : 0 ≤ ∑ i, |a i| * rungAmp c (χ i) (g i) ξ :=
    Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (hR ξ i)
  have h0η : 0 ≤ ∑ j, |a j| * rungAmp c (χ j) (g j) η :=
    Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (hR η i)
  have h1 := hS ξ
  have h2 := hS η
  rw [abs_of_nonneg h0ξ, hA] at h1
  rw [abs_of_nonneg h0η, hA] at h2
  have hsξ : √(massSum (fun i => rungAmp c (χ i) (g i) ξ) m) ≤ √(6 * (Fintype.card ι : ℝ) / (ξ ^ 2 - 1)) :=
    Real.sqrt_le_sqrt hMξ
  have hsη : √(massSum (fun i => rungAmp c (χ i) (g i) η) m) ≤ √(6 * (Fintype.card ι : ℝ) / (η ^ 2 - 1)) :=
    Real.sqrt_le_sqrt hMη
  have hJ : 0 ≤ 6 * (Fintype.card ι : ℝ) := by positivity
  have hprod : √(6 * (Fintype.card ι : ℝ) / (ξ ^ 2 - 1)) * √(6 * (Fintype.card ι : ℝ) / (η ^ 2 - 1))
      = 6 * (Fintype.card ι : ℝ) / √((ξ ^ 2 - 1) * (η ^ 2 - 1)) := by
    rw [← Real.sqrt_mul (div_nonneg hJ hpξ.le), Real.sqrt_mul hpξ.le]
    rw [show 6 * (Fintype.card ι : ℝ) / (ξ ^ 2 - 1) * (6 * (Fintype.card ι : ℝ) / (η ^ 2 - 1))
        = (6 * (Fintype.card ι : ℝ)) ^ 2 / ((ξ ^ 2 - 1) * (η ^ 2 - 1)) by field_simp]
    rw [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq hJ, Real.sqrt_mul hpξ.le]
  calc (∑ i, |a i| * rungAmp c (χ i) (g i) ξ) * (∑ j, |a j| * rungAmp c (χ j) (g j) η)
      ≤ (√P * √(massSum (fun i => rungAmp c (χ i) (g i) ξ) m))
          * (√P * √(massSum (fun i => rungAmp c (χ i) (g i) η) m)) :=
        mul_le_mul h1 h2 h0η (by positivity)
    _ = P * (√(massSum (fun i => rungAmp c (χ i) (g i) ξ) m) * √(massSum (fun i => rungAmp c (χ i) (g i) η) m)) := by
        rw [show √P * √(massSum (fun i => rungAmp c (χ i) (g i) ξ) m)
            * (√P * √(massSum (fun i => rungAmp c (χ i) (g i) η) m))
            = (√P * √P) * (√(massSum (fun i => rungAmp c (χ i) (g i) ξ) m)
              * √(massSum (fun i => rungAmp c (χ i) (g i) η) m)) by ring, Real.mul_self_sqrt hP0]
    _ ≤ P * (√(6 * (Fintype.card ι : ℝ) / (ξ ^ 2 - 1)) * √(6 * (Fintype.card ι : ℝ) / (η ^ 2 - 1))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hsξ hsη (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hP0
    _ = _ := by rw [hprod]; ring

end Cvs.Prolate.Envelope.RungCountEnvelope
