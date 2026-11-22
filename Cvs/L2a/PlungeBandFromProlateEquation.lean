import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.ModeTailPlungeBandPositive
import Cvs.L2a.TailLogScaleTest
import Cvs.L2a.TailModesFromProlateEquation
import Cvs.L2a.TailOfModes
import Cvs.Prolate.Envelope.EdgeValueSoninBound
import Cvs.Prolate.Envelope.EnergyFromReferencePoint
import Cvs.Prolate.LiouvilleGreen.LGFactorsShiftedEdge
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyLower
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay
import Cvs.Prolate.LiouvilleGreen.SoninFunction
import Cvs.Prolate.SlepianCommutingRelation
import Cvs.WeilForm.PrimePowerIndexed
import Cvs.WeilForm.SelfConvolutionFunctional

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# L2a across the plunge band from the prolate equation alone, radial and angular

If `ψ` solves `((ξ²−1)ψ')' + (c²ξ² − χ)ψ = 0` regularly on `[1, Ξ]` with `ψ(1) ≠ 0`, `0 ≤ χ`, then there is `C` such
that for every large `c` and every `χ` with `C c ≤ c² − χ` the Weil form of every tail of `M` modes of `ψ` is
positive: Cvs.L2a.ModeTailPlungeBandPositive with `K = 12e`, `Γ = 72e²`, discharged at `ξ₀ = 1 + 1/(c² − χ)` by Cvs.Prolate.LiouvilleGreen.LGFactorsShiftedEdge at `ℓ = (c² − χ)/c²`.
-/

namespace Cvs.L2a.PlungeBandFromProlateEquation

open Real Set MeasureTheory Filter Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.TailLogScaleTest Cvs.L2a.TailOfModes
open Cvs.L2a.TailModesFromProlateEquation (contDiffOn_of_deriv)
open Cvs.L2a.AngularProlateTailPositive (psi psi_system)

set_option maxHeartbeats 4000000 in
/-- **L2a across the plunge band, from the prolate equation alone**: there is `C ≥ 100` such that for every large
`c` and every `χ ≥ 0` with `C c ≤ c² − χ`, the Weil form of every tail of `M` modes of a regular solution with
`ψ(1) ≠ 0` is positive. -/
theorem weilForm_tailF_plunge_pos (Kf : ℕ) (hKf : 1 ≤ Kf) :
    ∃ C : ℝ, 100 ≤ C ∧ ∀ᶠ c in atTop, ∀ (χ Ξ : ℝ) (ψ v v' : ℝ → ℝ) (P R N M J : ℕ),
      0 ≤ χ → C * c ≤ c ^ 2 - χ →
      (∀ r ∈ Icc 1 Ξ, HasDerivAt ψ (v r) r) → (∀ r ∈ Icc 1 Ξ, HasDerivAt v (v' r) r) →
      (∀ r ∈ Icc 1 Ξ, (r ^ 2 - 1) * v' r + 2 * r * v r + (c ^ 2 * r ^ 2 - χ) * ψ r = 0) →
      ψ 1 ≠ 0 →
      1 ≤ J → 1 ≤ M → (M : ℝ) * 2 ^ (J + 1) ≤ Ξ →
      Cvs.WeilForm.PrimePowerIndexed.primePowIndex P R ⊆ Finset.Icc 2 N → (N : ℝ) + 2 ≤ 2 ^ (J + 1) →
      0 < Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (logScale (tailF ψ M (2 ^ (J + 1)))) := by
  obtain ⟨C₀, hC₀, hmain⟩ := Cvs.L2a.ModeTailPlungeBandPositive.weilForm_tailF_plunge_pos (12 * exp 1) (72 * exp 1 ^ 2) Kf
    (by nlinarith [add_one_le_exp (1 : ℝ)]) hKf
  refine ⟨max C₀ 100, le_max_right _ _, ?_⟩
  filter_upwards [hmain, eventually_gt_atTop 0] with c hc hc0
  intro χ Ξ ψ v v' P R N M J hχ0 hband hψ hv hode hψ1 hJ hM hΞ hidx hrb
  have hc2 : 0 < c ^ 2 := by positivity
  have hbC : C₀ * c ≤ c ^ 2 - χ := (mul_le_mul_of_nonneg_right (le_max_left _ _) hc0.le).trans hband
  have hb100 : 100 * c ≤ c ^ 2 - χ := (mul_le_mul_of_nonneg_right (le_max_right _ _) hc0.le).trans hband
  have hd : 0 < c ^ 2 - χ := by linarith
  have hχc : χ < c ^ 2 := by linarith
  set ℓ := (c ^ 2 - χ) / c ^ 2 with hℓdef
  have hℓ0 : 0 < ℓ := by positivity
  have hσ : ℓ * c ^ 2 ≤ c ^ 2 - χ := by rw [hℓdef, div_mul_cancel₀ _ hc2.ne']
  have hℓc : 100 ≤ ℓ * c := by
    rw [hℓdef, div_mul_eq_mul_div, le_div_iff₀ hc2]
    calc 100 * c ^ 2 = 100 * c * c := by ring
      _ ≤ (c ^ 2 - χ) * c := mul_le_mul_of_nonneg_right hb100 hc0.le
  obtain ⟨hD0, heD, he0', he1', heX, hX, hD4⟩ := Cvs.Prolate.LiouvilleGreen.LGFactorsShiftedEdge.sizes (c := c) (χ := χ) hℓ0 hχ0 hσ hℓc
  set u : ℝ → ℝ := fun r => pP r * v r with hudef
  set ξ₀ : ℝ := 1 + 1 / (c ^ 2 - χ) with hξ₀
  have he : 0 < 1 / (c ^ 2 - χ) := he0'
  have h1ξ : 1 < ξ₀ := by linarith
  have hb4 : (4 : ℝ) ≤ 2 ^ (J + 1) := by
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (J + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hbΞ : (2 : ℝ) ^ (J + 1) ≤ Ξ := le_trans (by nlinarith) hΞ
  have hΞ1 : 1 < Ξ := by linarith
  have he1 : 1 / (c ^ 2 - χ) ≤ 1 := by linarith
  have hξΞ : ξ₀ ≤ Ξ := by linarith
  obtain ⟨hpq1, hpq3⟩ := Cvs.Prolate.LiouvilleGreen.LGFactorsShiftedEdge.pq_bounds hℓ0 hχ0 hσ hℓc
  obtain ⟨ha1, ha2⟩ := Cvs.Prolate.LiouvilleGreen.LGFactorsShiftedEdge.a_bounds hℓ0 hχ0 hσ hℓc
  have hw1 := Cvs.Prolate.LiouvilleGreen.LGFactorsShiftedEdge.w_le hℓ0 hχ0 hσ hℓc
  have hfac := Cvs.Prolate.LiouvilleGreen.LGFactorsShiftedEdge.fac_le hℓ0 hχ0 hσ hℓc
  have hlow := Cvs.Prolate.LiouvilleGreen.LGFactorsShiftedEdge.lower_ge hℓ0 hχ0 hσ hℓc
  have hKe := Cvs.Prolate.LiouvilleGreen.LGFactorsShiftedEdge.edge_const_le hℓ0 hχ0 hσ hℓc
  rw [← hξ₀] at hpq1 hpq3 ha1 ha2 hw1 hfac hlow hKe
  set E₀ := energy (aP c χ) ψ u ξ₀ with hE₀
  -- the (ψ, u) system
  have hψu : ∀ ξ ∈ Ioc 1 Ξ, HasDerivAt ψ (u ξ / pP ξ) ξ := fun ξ hξ => by
    have hp : pP ξ ≠ 0 := (pP_pos hξ.1).ne'
    simp only [hudef]; rw [mul_div_cancel_left₀ _ hp]; exact hψ ξ ⟨hξ.1.le, hξ.2⟩
  have huu : ∀ ξ ∈ Icc 1 Ξ, HasDerivAt u (-(qP c χ ξ * ψ ξ)) ξ := fun ξ hξ => by
    have hp : HasDerivAt pP (2 * ξ) ξ := by
      have := (hasDerivAt_pow 2 ξ).sub_const 1; unfold pP; simpa using this
    refine (hp.mul (hv ξ hξ)).congr_deriv ?_
    have := hode ξ hξ; unfold pP qP; linarith
  have hu1 : u 1 = 0 := by simp [hudef, pP]
  have hC1 : ContDiffOn ℝ 1 ψ (Icc 1 Ξ) :=
    contDiffOn_of_deriv hΞ1 hψ (fun r hr => (hv r hr).continuousAt.continuousWithinAt)
  -- `E₀ > 0`
  have hE₀pos : 0 < E₀ := by
    rw [hE₀, Cvs.Prolate.Envelope.EnergyFromReferencePoint.energy_eq h1ξ hc2 hχc]
    have hS := Cvs.Prolate.Envelope.EdgeValueSoninBound.sonin_ge hχc hψ hv hode (ξ := ξ₀) ⟨h1ξ.le, hξΞ⟩
    have hpq : (ξ₀ ^ 2 - 1) * (c ^ 2 * ξ₀ ^ 2 - χ) = pP ξ₀ * qP c χ ξ₀ := by unfold pP qP; ring
    rw [hpq] at hS
    have h1 : 0 < ψ 1 ^ 2 * (1 - pP ξ₀ * qP c χ ξ₀ / 4) := by
      have : 0 < ψ 1 ^ 2 := by positivity
      nlinarith
    have := mul_le_mul_of_nonneg_left hS (by linarith : (0 : ℝ) ≤ aP c χ ξ₀)
    nlinarith
  -- the energy from above
  have hGup := Cvs.Prolate.Envelope.EnergyFromReferencePoint.energy_sup_le hc0 hχ0 hχc hψ hv hode h1ξ hξΞ (by linarith) (by linarith)
  have hmax : max (aP c χ ξ₀ * (Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay.fac c χ ξ₀ / (aP c χ ξ₀ * (1 - pP ξ₀ * qP c χ ξ₀ / 4))))
      (Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay.fac c χ ξ₀) ≤ 24 * exp 1 := by
    apply max_le
    · calc aP c χ ξ₀ * (Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay.fac c χ ξ₀ / (aP c χ ξ₀ * (1 - pP ξ₀ * qP c χ ξ₀ / 4)))
          ≤ 2 * (12 * exp 1) := mul_le_mul ha2 hKe (by
            have : 0 < Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay.fac c χ ξ₀ := by
              unfold Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay.fac
              have := wP_pos h1ξ hc2 hχc
              apply mul_pos (div_pos (by linarith) (by linarith)) (exp_pos _)
            have : 0 < aP c χ ξ₀ * (1 - pP ξ₀ * qP c χ ξ₀ / 4) := mul_pos (by linarith) (by linarith)
            positivity) (by norm_num)
        _ = 24 * exp 1 := by ring
    · nlinarith [exp_pos 1]
  set G := 24 * exp 1 * E₀ with hGdef
  set Gm := E₀ / (3 * exp 1) with hGmdef
  have hG : ∀ ξ ∈ Ioc 1 Ξ, energy (aP c χ) ψ u ξ ≤ G := fun ξ hξ =>
    (hGup ξ hξ).trans (mul_le_mul_of_nonneg_right hmax hE₀pos.le)
  -- Sonin
  have hedge : ∀ ξ ∈ Icc 1 Ξ, |ψ ξ| ≤ |ψ 1| := fun ξ hξ => by
    have := Cvs.Prolate.LiouvilleGreen.SoninFunction.prolate_sq_le_edge hχc hξ hψ hv hode
    rw [← sqrt_sq_eq_abs, ← sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt this
  -- the edge ratio
  have hedge1 : ψ 1 ^ 2 ≤ 12 * exp 1 * G := by
    have h := Cvs.Prolate.Envelope.EdgeValueSoninBound.edge_le_energy (ξ₁ := Ξ) hc0 hχ0 hχc hψ hv hode h1ξ le_rfl hξΞ
      (by linarith) (by linarith)
    have h2 : ψ 1 ^ 2 ≤ 12 * exp 1 * E₀ := h.trans (mul_le_mul_of_nonneg_right hKe hE₀pos.le)
    have h3 : 12 * exp 1 * E₀ ≤ 12 * exp 1 * G := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [hGdef]; nlinarith [add_one_le_exp (1 : ℝ)]
    linarith
  -- the energy from below on `[√2, b]`
  have hGm : ∀ t ∈ Icc (√2) (2 ^ (J + 1)), Gm ≤ energy (aP c χ) ψ u t := by
    intro t ht
    have hs2 : ξ₀ ≤ √2 := by
      have : (1 : ℝ) + 1 / 10000 ≤ √2 := Real.le_sqrt_of_sq_le (by norm_num)
      linarith
    have hξt : ξ₀ ≤ t := hs2.trans ht.1
    have htΞ : t ≤ Ξ := ht.2.trans hbΞ
    have gt1 : ∀ r ∈ Icc ξ₀ t, 1 < r := fun r hr => lt_of_lt_of_le h1ξ hr.1
    have hge := Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyLower.prolate_energy_ge h1ξ hξt hc2 hχ0 hχc
      (fun r hr => hψu r ⟨gt1 r hr, hr.2.trans htΞ⟩) (fun r hr => huu r ⟨(gt1 r hr).le, hr.2.trans htΞ⟩)
      (by linarith)
    calc Gm = E₀ * (1 / (3 * exp 1)) := by rw [hGmdef]; ring
      _ ≤ E₀ * ((1 - wP c χ ξ₀ / 2) / (1 + wP c χ ξ₀ / 2) * exp (-(wP c χ ξ₀ / (2 - wP c χ ξ₀)))) :=
          mul_le_mul_of_nonneg_left hlow hE₀pos.le
      _ = E₀ * (1 - wP c χ ξ₀ / 2) / (1 + wP c χ ξ₀ / 2) * exp (-(wP c χ ξ₀ / (2 - wP c χ ξ₀))) := by ring
      _ ≤ _ := hge
  have hGm0 : 0 < Gm := by positivity
  have hGΓ : G ≤ 72 * exp 1 ^ 2 * Gm := by
    rw [hGdef, hGmdef]; field_simp; ring_nf; rfl
  exact hc χ G Gm Ξ ψ u P R N M J hχ0 hbC hψu huu hu1 hC1 hG hedge hedge1 hGm hGm0 hGΓ hJ hM hΞ hidx hrb

/-- **L2a across the plunge band for the tail of an angular prolate**: there is `C ≥ 100` such that for every large
`c` and every `χ ≥ 0` with `C c ≤ c² − χ`, the Weil form of every tail of the cosine transform of an angular solution
with `ψ(1) ≠ 0` is positive. -/
theorem weilForm_angular_plunge_pos (Kf : ℕ) (hKf : 1 ≤ Kf) :
    ∃ C : ℝ, 100 ≤ C ∧ ∀ᶠ c in atTop, ∀ (χ Ξ : ℝ) (g g₁ g₂ : ℝ → ℝ) (P R N M J : ℕ),
      0 ≤ χ → C * c ≤ c ^ 2 - χ →
      (∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) → (∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) →
      ContinuousOn g₂ (uIcc (-1) 1) →
      (∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0) →
      psi c g 1 ≠ 0 →
      1 ≤ J → 1 ≤ M → (M : ℝ) * 2 ^ (J + 1) ≤ Ξ →
      Cvs.WeilForm.PrimePowerIndexed.primePowIndex P R ⊆ Finset.Icc 2 N → (N : ℝ) + 2 ≤ 2 ^ (J + 1) →
      0 < Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (logScale (tailF (psi c g) M (2 ^ (J + 1)))) := by
  obtain ⟨C, hC, h⟩ := weilForm_tailF_plunge_pos Kf hKf
  refine ⟨C, hC, ?_⟩
  filter_upwards [h] with c hc
  intro χ Ξ g g₁ g₂ P R N M J hχ0 hχs hg hg₁ hg₂c hang hψ1 hJ hM hΞ hidx hrb
  obtain ⟨h1, h2, h3⟩ := psi_system hg hg₁ hg₂c hang
  exact hc χ Ξ (psi c g) _ _ P R N M J hχ0 hχs (fun r _ => h1 r) (fun r _ => h2 r) (fun r _ => h3 r) hψ1
    hJ hM hΞ hidx hrb

end Cvs.L2a.PlungeBandFromProlateEquation
