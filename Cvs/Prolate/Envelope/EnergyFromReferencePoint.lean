import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Cvs.Prolate.Envelope.EdgeValueSoninBound
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
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
# The prolate energy on all of `(1, Ξ]`, from one reference point

`G = a S` with `S` Sonin's function, so `G(ξ) ≤ a(ξ) ψ(1)²` near the edge; above `ξ₀` the Liouville–Green factor
`fac` holds. With `EdgeValueSoninBound`'s `ψ(1)² ≤ K_edge G(ξ₀)`: `G(ξ) ≤ max(a(ξ₀) K_edge, fac) G(ξ₀)` for every `ξ ∈ (1, Ξ]`.
-/

namespace Cvs.Prolate.Envelope.EnergyFromReferencePoint

open Real Set Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.Prolate.LiouvilleGreen.SoninFunction

variable {ψ v v' : ℝ → ℝ} {c χ Ξ : ℝ}

/-- **`G = a S`**: the Liouville–Green energy is `a` times Sonin's function. -/
theorem energy_eq {ξ : ℝ} (h1 : 1 < ξ) (hc2 : 0 < c ^ 2) (hχ : χ < c ^ 2) :
    energy (aP c χ) ψ (fun r => pP r * v r) ξ
      = aP c χ ξ * sonin ψ v (fun r => r ^ 2 - 1) (fun r => c ^ 2 * r ^ 2 - χ) ξ := by
  have ha := aP_pos h1 hc2 hχ
  have hq := qP_pos h1 hc2 hχ
  unfold energy sonin
  have hsq := aP_sq h1 hc2 hχ
  simp only [pP, qP] at hsq ⊢
  have hq' : 0 < c ^ 2 * ξ ^ 2 - χ := by simpa [qP] using hq
  have hq'' : ξ ^ 2 * c ^ 2 - χ ≠ 0 := by nlinarith
  field_simp
  rw [hsq]
  field_simp

/-- **Near the edge**, `G(ξ) ≤ a(ξ) ψ(1)²`. -/
theorem energy_le_edge {ξ : ℝ} (hc2 : 0 < c ^ 2) (hχ : χ < c ^ 2) (hξ : ξ ∈ Ioc 1 Ξ)
    (hψ : ∀ r ∈ Icc 1 Ξ, HasDerivAt ψ (v r) r) (hv : ∀ r ∈ Icc 1 Ξ, HasDerivAt v (v' r) r)
    (hode : ∀ r ∈ Icc 1 Ξ, (r ^ 2 - 1) * v' r + 2 * r * v r + (c ^ 2 * r ^ 2 - χ) * ψ r = 0) :
    energy (aP c χ) ψ (fun r => pP r * v r) ξ ≤ aP c χ ξ * ψ 1 ^ 2 := by
  have hq : ∀ r ∈ Icc (1 : ℝ) ξ, 0 < c ^ 2 * r ^ 2 - χ := fun r hr => by
    have : 1 ≤ r ^ 2 := by nlinarith [hr.1]
    nlinarith
  have sub : ∀ r ∈ Icc (1 : ℝ) ξ, r ∈ Icc 1 Ξ := fun r hr => ⟨hr.1, hr.2.trans hξ.2⟩
  have h := sonin_antitone (ψ := ψ) (v := v) (v' := v') (p := fun r => r ^ 2 - 1) (p' := fun r => 2 * r)
    (q := fun r => c ^ 2 * r ^ 2 - χ) (q' := fun r => 2 * c ^ 2 * r) hξ.1.le hq
    (fun r hr => by
      have hr1 : 1 ≤ r := hr.1
      have := hq r hr
      have : 0 ≤ r ^ 2 - 1 := by nlinarith
      positivity)
    (fun r hr => hψ r (sub r hr)) (fun r hr => hv r (sub r hr))
    (fun r _ => by simpa using (hasDerivAt_pow 2 r).sub_const 1)
    (fun r _ => by
      have := ((hasDerivAt_pow 2 r).const_mul (c ^ 2)).sub_const χ
      exact this.congr_deriv (by ring))
    (fun r hr => hode r (sub r hr))
  have h1 : sonin ψ v (fun r => r ^ 2 - 1) (fun r => c ^ 2 * r ^ 2 - χ) 1 = ψ 1 ^ 2 := by
    unfold sonin; simp
  rw [energy_eq hξ.1 hc2 hχ]
  exact mul_le_mul_of_nonneg_left (h.trans h1.le) (aP_pos hξ.1 hc2 hχ).le

/-- `a = √(pq)` increases on `[1, ∞)`. -/
theorem aP_mono {ξ η : ℝ} (hχ : χ < c ^ 2) (h1 : 1 ≤ ξ) (h : ξ ≤ η) : aP c χ ξ ≤ aP c χ η := by
  unfold aP pP qP
  apply Real.sqrt_le_sqrt
  have hc : 0 ≤ c ^ 2 := sq_nonneg c
  have a1 : 0 ≤ ξ ^ 2 - 1 := by nlinarith
  have a2 : ξ ^ 2 ≤ η ^ 2 := by nlinarith
  have a3 : 0 ≤ c ^ 2 * ξ ^ 2 - χ := by nlinarith
  exact mul_le_mul (by linarith) (by nlinarith) a3 (by linarith)

/-- **The energy on `(1, Ξ]`** is at most `max(a(ξ₀) K_edge, fac)` times its value at `ξ₀`. -/
theorem energy_sup_le {ξ₀ : ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχ : χ < c ^ 2)
    (hψ : ∀ r ∈ Icc 1 Ξ, HasDerivAt ψ (v r) r) (hv : ∀ r ∈ Icc 1 Ξ, HasDerivAt v (v' r) r)
    (hode : ∀ r ∈ Icc 1 Ξ, (r ^ 2 - 1) * v' r + 2 * r * v r + (c ^ 2 * r ^ 2 - χ) * ψ r = 0)
    (h1 : 1 < ξ₀) (h0 : ξ₀ ≤ Ξ) (ha4 : pP ξ₀ * qP c χ ξ₀ < 4) (hW : wP c χ ξ₀ < 2) :
    ∀ ξ ∈ Ioc 1 Ξ, energy (aP c χ) ψ (fun r => pP r * v r) ξ
      ≤ max (aP c χ ξ₀ * (Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay.fac c χ ξ₀
              / (aP c χ ξ₀ * (1 - pP ξ₀ * qP c χ ξ₀ / 4))))
            (Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay.fac c χ ξ₀)
          * energy (aP c χ) ψ (fun r => pP r * v r) ξ₀ := by
  intro ξ hξ
  have hc2 : 0 < c ^ 2 := by positivity
  set E₀ := energy (aP c χ) ψ (fun r => pP r * v r) ξ₀ with hE₀
  set F := Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay.fac c χ ξ₀ with hF
  set Ke := F / (aP c χ ξ₀ * (1 - pP ξ₀ * qP c χ ξ₀ / 4)) with hKe
  have ha0 := aP_pos h1 hc2 hχ
  have hE0 : 0 ≤ E₀ := by
    rw [hE₀, energy_eq h1 hc2 hχ]
    apply mul_nonneg ha0.le
    unfold sonin
    have hx : 1 ≤ ξ₀ ^ 2 := by nlinarith
    have : 0 < c ^ 2 * ξ₀ ^ 2 - χ := by nlinarith
    have : 0 ≤ ξ₀ ^ 2 - 1 := by nlinarith
    positivity
  have hedge := Cvs.Prolate.Envelope.EdgeValueSoninBound.edge_le_energy hc hχ0 hχ hψ hv hode h1 le_rfl h0 ha4 hW
  rcases le_total ξ ξ₀ with hle | hge
  · calc energy (aP c χ) ψ (fun r => pP r * v r) ξ ≤ aP c χ ξ * ψ 1 ^ 2 :=
          energy_le_edge hc2 hχ hξ hψ hv hode
      _ ≤ aP c χ ξ₀ * (Ke * E₀) :=
          mul_le_mul (aP_mono hχ hξ.1.le hle) hedge (sq_nonneg _) ha0.le
      _ = aP c χ ξ₀ * Ke * E₀ := by ring
      _ ≤ max (aP c χ ξ₀ * Ke) F * E₀ := mul_le_mul_of_nonneg_right (le_max_left _ _) hE0
  · have gt1 : ∀ t ∈ Icc ξ₀ ξ, 1 < t := fun t ht => lt_of_lt_of_le h1 ht.1
    have sub : ∀ t ∈ Icc ξ₀ ξ, t ∈ Icc 1 Ξ := fun t ht => ⟨(gt1 t ht).le, ht.2.trans hξ.2⟩
    have hψu : ∀ t ∈ Icc ξ₀ ξ, HasDerivAt ψ (pP t * v t / pP t) t := fun t ht => by
      have hp : pP t ≠ 0 := (pP_pos (gt1 t ht)).ne'
      rw [mul_div_cancel_left₀ _ hp]; exact hψ t (sub t ht)
    have huu : ∀ t ∈ Icc ξ₀ ξ, HasDerivAt (fun r => pP r * v r) (-(qP c χ t * ψ t)) t := fun t ht => by
      have hp : HasDerivAt pP (2 * t) t := by
        have := (hasDerivAt_pow 2 t).sub_const 1; unfold pP; simpa using this
      refine (hp.mul (hv t (sub t ht))).congr_deriv ?_
      have := hode t (sub t ht); unfold pP qP; linarith
    have key := prolate_energy_le h1 hge hc2 hχ0 hχ hψu huu hW
    have eF : E₀ * F = energy (aP c χ) ψ (fun r => pP r * v r) ξ₀ * (1 + wP c χ ξ₀ / 2) / (1 - wP c χ ξ₀ / 2)
        * exp (wP c χ ξ₀ / (2 - wP c χ ξ₀)) := by
      rw [hF, hE₀]; unfold Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay.fac; ring
    calc energy (aP c χ) ψ (fun r => pP r * v r) ξ ≤ E₀ * F := by rw [eF]; exact key
      _ = F * E₀ := by ring
      _ ≤ max (aP c χ ξ₀ * Ke) F * E₀ := mul_le_mul_of_nonneg_right (le_max_right _ _) hE0

end Cvs.Prolate.Envelope.EnergyFromReferencePoint
