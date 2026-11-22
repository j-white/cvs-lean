import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.Prolate.CosineTransformSecondOrder
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.ProlateWronskianIntegral
import Cvs.Prolate.SlepianCommutingRelation

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Two rungs are orthogonal on `[1, ∞)`: the Wronskian at infinity is `O(1/t)`

Every finite cosine transform has the same phases at infinity, `ψ ≈ A sin(cξ)/(cξ)` and `u ≈ Aξ cos(cξ)` (Cvs.Prolate.CosineTransformSecondOrder),
so for two of them the leading term of `u_iψ_j − ψ_iu_j` cancels and `|u_iψ_j − ψ_iu_j| ≤ K/ξ` with an explicit `K`.
By the Wronskian identity (Cvs.Prolate.ProlateWronskianIntegral), `|∫₁ᵗ ψ_iψ_j| ≤ K/(|χ_i − χ_j| t)` for angular solutions with `χ_i ≠ χ_j`.
-/

namespace Cvs.Prolate.RungOrthogonalityAtInfinity

open Real Set intervalIntegral Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.Prolate.SlepianCommutingRelation Cvs.L2a.AngularProlateTailPositive Cvs.Prolate.CosineTransformSecondOrder
open scoped Interval

/-- `A = g(1) + g(−1)`, the amplitude of the transform at infinity. -/
def ampl (g : ℝ → ℝ) : ℝ := g 1 + g (-1)

/-- `C₁ = |g₁(1) − g₁(−1)| + ∫|g₂|`, the second-order constant of `ψ`. -/
noncomputable def cst₁ (g₁ g₂ : ℝ → ℝ) : ℝ := |g₁ 1 - g₁ (-1)| + ∫ s in (-1 : ℝ)..1, |g₂ s|

/-- `Σ = |A| + (|h'(1) + h'(−1)| + ∫(2|g₁| + |g₂|))/c`, a bound for `|u − Aξ cos(cξ)|` on `ξ ≥ 1`. -/
noncomputable def cstU (c : ℝ) (g g₁ g₂ : ℝ → ℝ) : ℝ :=
  |ampl g| + (|g 1 + g₁ 1 + (g (-1) - g₁ (-1))| + ∫ s in (-1 : ℝ)..1, 2 * |g₁ s| + |g₂ s|) / c

/-- The Wronskian constant of two transforms. -/
noncomputable def wronskianConst (c : ℝ) (gi gi₁ gi₂ gj gj₁ gj₂ : ℝ → ℝ) : ℝ :=
  (|ampl gi| * cst₁ gj₁ gj₂ + |ampl gj| * cst₁ gi₁ gi₂
      + cstU c gi gi₁ gi₂ * cst₁ gj₁ gj₂ + cstU c gj gj₁ gj₂ * cst₁ gi₁ gi₂) / c ^ 2
    + (|ampl gj| * cstU c gi gi₁ gi₂ + |ampl gi| * cstU c gj gj₁ gj₂) / c

theorem cst₁_nonneg {g₁ g₂ : ℝ → ℝ} : 0 ≤ cst₁ g₁ g₂ :=
  add_nonneg (abs_nonneg _) (integral_nonneg (by norm_num) fun s _ => abs_nonneg _)

theorem cstU_nonneg {c : ℝ} (hc : 0 < c) {g g₁ g₂ : ℝ → ℝ} : 0 ≤ cstU c g g₁ g₂ := by
  unfold cstU
  have : 0 ≤ ∫ s in (-1 : ℝ)..1, 2 * |g₁ s| + |g₂ s| :=
    integral_nonneg (by norm_num) fun s _ => by positivity
  positivity

/-- **The algebra of the Wronskian**: with `ψ = A sin(cξ)/(cξ) + ρ`, `u = Aξ cos(cξ) + σ` for two rungs,
`|ρ| ≤ C₁/(cξ)²`, `|σ| ≤ Σ`, `c > 0`, `ξ ≥ 1`: `|u_iψ_j − ψ_iu_j| ≤ K/ξ`. -/
theorem wronskian_abs_le {c ξ Ai Aj C1i C1j Si Sj ψi ψj ui uj : ℝ} (hc : 0 < c) (hξ : 1 ≤ ξ)
    (hC1i : 0 ≤ C1i) (hC1j : 0 ≤ C1j) (hSi : 0 ≤ Si) (hSj : 0 ≤ Sj)
    (hψi : |ψi - Ai * sin (c * ξ) / (c * ξ)| ≤ C1i / (c * ξ) ^ 2)
    (hψj : |ψj - Aj * sin (c * ξ) / (c * ξ)| ≤ C1j / (c * ξ) ^ 2)
    (hui : |ui - Ai * ξ * cos (c * ξ)| ≤ Si) (huj : |uj - Aj * ξ * cos (c * ξ)| ≤ Sj) :
    |ui * ψj - ψi * uj|
      ≤ ((|Ai| * C1j + |Aj| * C1i + Si * C1j + Sj * C1i) / c ^ 2 + (|Aj| * Si + |Ai| * Sj) / c) / ξ := by
  have hξ0 : 0 < ξ := by linarith
  have hcξ : 0 < c * ξ := mul_pos hc hξ0
  have hsq : 0 < (c * ξ) ^ 2 := by positivity
  set ρi := ψi - Ai * sin (c * ξ) / (c * ξ) with hρi
  set ρj := ψj - Aj * sin (c * ξ) / (c * ξ) with hρj
  set σi := ui - Ai * ξ * cos (c * ξ) with hσi
  set σj := uj - Aj * ξ * cos (c * ξ) with hσj
  have e : ui * ψj - ψi * uj
      = ξ * cos (c * ξ) * (Ai * ρj - Aj * ρi) + sin (c * ξ) / (c * ξ) * (Aj * σi - Ai * σj)
        + (σi * ρj - ρi * σj) := by
    rw [hρi, hρj, hσi, hσj]; ring
  rw [e]
  have hS : |sin (c * ξ) / (c * ξ)| ≤ 1 / (c * ξ) := by
    rw [abs_div, abs_of_pos hcξ]; exact div_le_div_of_nonneg_right (abs_sin_le_one _) hcξ.le
  have hC : |cos (c * ξ)| ≤ 1 := abs_cos_le_one _
  have p1 : |Ai * ρj - Aj * ρi| ≤ (|Ai| * C1j + |Aj| * C1i) / (c * ξ) ^ 2 := by
    calc |Ai * ρj - Aj * ρi| ≤ |Ai * ρj| + |Aj * ρi| := abs_sub _ _
      _ = |Ai| * |ρj| + |Aj| * |ρi| := by rw [abs_mul, abs_mul]
      _ ≤ |Ai| * (C1j / (c * ξ) ^ 2) + |Aj| * (C1i / (c * ξ) ^ 2) :=
          add_le_add (mul_le_mul_of_nonneg_left hψj (abs_nonneg _))
            (mul_le_mul_of_nonneg_left hψi (abs_nonneg _))
      _ = (|Ai| * C1j + |Aj| * C1i) / (c * ξ) ^ 2 := by ring
  have p2 : |Aj * σi - Ai * σj| ≤ |Aj| * Si + |Ai| * Sj := by
    calc |Aj * σi - Ai * σj| ≤ |Aj * σi| + |Ai * σj| := abs_sub _ _
      _ = |Aj| * |σi| + |Ai| * |σj| := by rw [abs_mul, abs_mul]
      _ ≤ |Aj| * Si + |Ai| * Sj :=
          add_le_add (mul_le_mul_of_nonneg_left hui (abs_nonneg _))
            (mul_le_mul_of_nonneg_left huj (abs_nonneg _))
  have p3 : |σi * ρj - ρi * σj| ≤ (Si * C1j + Sj * C1i) / (c * ξ) ^ 2 := by
    calc |σi * ρj - ρi * σj| ≤ |σi * ρj| + |ρi * σj| := abs_sub _ _
      _ = |σi| * |ρj| + |ρi| * |σj| := by rw [abs_mul, abs_mul]
      _ ≤ Si * (C1j / (c * ξ) ^ 2) + (C1i / (c * ξ) ^ 2) * Sj :=
          add_le_add (mul_le_mul hui hψj (abs_nonneg _) hSi)
            (mul_le_mul hψi huj (abs_nonneg _) (by positivity))
      _ = (Si * C1j + Sj * C1i) / (c * ξ) ^ 2 := by ring
  have t1 : |ξ * cos (c * ξ) * (Ai * ρj - Aj * ρi)| ≤ (|Ai| * C1j + |Aj| * C1i) / (c ^ 2 * ξ) := by
    rw [abs_mul, abs_mul, abs_of_pos hξ0]
    calc ξ * |cos (c * ξ)| * |Ai * ρj - Aj * ρi|
        ≤ ξ * 1 * ((|Ai| * C1j + |Aj| * C1i) / (c * ξ) ^ 2) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hC hξ0.le) p1 (abs_nonneg _) (by positivity)
      _ = (|Ai| * C1j + |Aj| * C1i) / (c ^ 2 * ξ) := by field_simp
  have t2 : |sin (c * ξ) / (c * ξ) * (Aj * σi - Ai * σj)| ≤ (|Aj| * Si + |Ai| * Sj) / (c * ξ) := by
    rw [abs_mul]
    calc |sin (c * ξ) / (c * ξ)| * |Aj * σi - Ai * σj| ≤ 1 / (c * ξ) * (|Aj| * Si + |Ai| * Sj) :=
          mul_le_mul hS p2 (abs_nonneg _) (by positivity)
      _ = (|Aj| * Si + |Ai| * Sj) / (c * ξ) := by ring
  have t3 : |σi * ρj - ρi * σj| ≤ (Si * C1j + Sj * C1i) / (c ^ 2 * ξ) := by
    refine p3.trans ?_
    rw [div_le_div_iff₀ hsq (by positivity)]
    have hX : 0 ≤ Si * C1j + Sj * C1i := by positivity
    nlinarith [mul_nonneg hX (mul_nonneg (sq_nonneg c) (mul_nonneg hξ0.le (by linarith : (0:ℝ) ≤ ξ - 1)))]
  calc |ξ * cos (c * ξ) * (Ai * ρj - Aj * ρi) + sin (c * ξ) / (c * ξ) * (Aj * σi - Ai * σj)
        + (σi * ρj - ρi * σj)|
      ≤ |ξ * cos (c * ξ) * (Ai * ρj - Aj * ρi)| + |sin (c * ξ) / (c * ξ) * (Aj * σi - Ai * σj)|
        + |σi * ρj - ρi * σj| := by
        refine (abs_add_le _ _).trans ?_; exact add_le_add (abs_add_le _ _) le_rfl
    _ ≤ (|Ai| * C1j + |Aj| * C1i) / (c ^ 2 * ξ) + (|Aj| * Si + |Ai| * Sj) / (c * ξ)
        + (Si * C1j + Sj * C1i) / (c ^ 2 * ξ) := add_le_add (add_le_add t1 t2) t3
    _ = _ := by field_simp; ring

/-- **Two rungs are nearly orthogonal on `[1, t]`**: for angular solutions `g_i, g_j` with `χ_i ≠ χ_j`, `c > 0`
and `t ≥ 1`, `|∫₁ᵗ ψ_iψ_j| ≤ K/(|χ_i − χ_j| t)`, `K` the Wronskian constant. -/
theorem integral_psi_mul_le {gi gi₁ gi₂ gj gj₁ gj₂ : ℝ → ℝ} {c χi χj t : ℝ}
    (hgi : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt gi (gi₁ s) s)
    (hgi₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt gi₁ (gi₂ s) s) (hgi₂c : ContinuousOn gi₂ (uIcc (-1) 1))
    (hangi : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * gi₂ s - 2 * s * gi₁ s - c ^ 2 * s ^ 2 * gi s + χi * gi s = 0)
    (hgj : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt gj (gj₁ s) s)
    (hgj₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt gj₁ (gj₂ s) s) (hgj₂c : ContinuousOn gj₂ (uIcc (-1) 1))
    (hangj : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * gj₂ s - 2 * s * gj₁ s - c ^ 2 * s ^ 2 * gj s + χj * gj s = 0)
    (hc : 0 < c) (hχ : χi ≠ χj) (ht : 1 ≤ t) :
    |∫ ξ in (1 : ℝ)..t, psi c gi ξ * psi c gj ξ|
      ≤ wronskianConst c gi gi₁ gi₂ gj gj₁ gj₂ / (|χi - χj| * t) := by
  obtain ⟨hψi, hvi, hodei⟩ := psi_system hgi hgi₁ hgi₂c hangi
  obtain ⟨hψj, hvj, hodej⟩ := psi_system hgj hgj₁ hgj₂c hangj
  set vi := kint gi (fun ξ s => -(c * s * sin (c * ξ * s))) with hvi_def
  set vj := kint gj (fun ξ s => -(c * s * sin (c * ξ * s))) with hvj_def
  set ui : ℝ → ℝ := fun ξ => pP ξ * vi ξ with hui_def
  set uj : ℝ → ℝ := fun ξ => pP ξ * vj ξ with huj_def
  have hp' : ∀ ξ : ℝ, HasDerivAt pP (2 * ξ) ξ := fun ξ => by
    have := (hasDerivAt_pow 2 ξ).sub_const 1; unfold pP; simpa using this
  have hpc : Continuous pP := by unfold pP; fun_prop
  -- the two `(ψ, u)` systems
  have hψui : ∀ ξ ∈ Ioo (1 : ℝ) t, HasDerivAt (psi c gi) (ui ξ / pP ξ) ξ := fun ξ hξ => by
    have hp : pP ξ ≠ 0 := (pP_pos hξ.1).ne'
    simp only [hui_def]; rw [mul_div_cancel_left₀ _ hp]; exact hψi ξ
  have hψuj : ∀ ξ ∈ Ioo (1 : ℝ) t, HasDerivAt (psi c gj) (uj ξ / pP ξ) ξ := fun ξ hξ => by
    have hp : pP ξ ≠ 0 := (pP_pos hξ.1).ne'
    simp only [huj_def]; rw [mul_div_cancel_left₀ _ hp]; exact hψj ξ
  have huui : ∀ ξ ∈ Ioo (1 : ℝ) t, HasDerivAt ui (-(qP c χi ξ * psi c gi ξ)) ξ := fun ξ _ => by
    refine ((hp' ξ).mul (hvi ξ)).congr_deriv ?_
    have := hodei ξ; unfold pP qP; linarith
  have huuj : ∀ ξ ∈ Ioo (1 : ℝ) t, HasDerivAt uj (-(qP c χj ξ * psi c gj ξ)) ξ := fun ξ _ => by
    refine ((hp' ξ).mul (hvj ξ)).congr_deriv ?_
    have := hodej ξ; unfold pP qP; linarith
  have hcψi : ContinuousOn (psi c gi) (Icc 1 t) := fun ξ _ => (hψi ξ).continuousAt.continuousWithinAt
  have hcψj : ContinuousOn (psi c gj) (Icc 1 t) := fun ξ _ => (hψj ξ).continuousAt.continuousWithinAt
  have hcui : ContinuousOn ui (Icc 1 t) :=
    hpc.continuousOn.mul fun ξ _ => (hvi ξ).continuousAt.continuousWithinAt
  have hcuj : ContinuousOn uj (Icc 1 t) :=
    hpc.continuousOn.mul fun ξ _ => (hvj ξ).continuousAt.continuousWithinAt
  have hui1 : ui 1 = 0 := by simp [hui_def, pP]
  have huj1 : uj 1 = 0 := by simp [huj_def, pP]
  have hW := Cvs.Prolate.ProlateWronskianIntegral.wronskian_integral (c := c) (χa := χi) (χb := χj) ht hψui huui hψuj huuj
    hcψi hcui hcψj hcuj hui1 huj1
  -- the Wronskian at `t`
  have ht0 : 0 < t := by linarith
  have hct : c * t ≠ 0 := by positivity
  have bψi := psi_sub_le hgi hgi₁ hgi₂c hct
  have bψj := psi_sub_le hgj hgj₁ hgj₂c hct
  have bui := u_sub_le hgi hgi₁ hgi₂c hc ht
  have buj := u_sub_le hgj hgj₁ hgj₂c hc ht
  have hAi : |ampl gi| / t ≤ |ampl gi| := div_le_self (abs_nonneg _) ht
  have hAj : |ampl gj| / t ≤ |ampl gj| := div_le_self (abs_nonneg _) ht
  have bui' : |ui t - ampl gi * t * cos (c * t)| ≤ cstU c gi gi₁ gi₂ := by
    simp only [hui_def, hvi_def]; unfold pP cstU
    refine bui.trans ?_; unfold ampl at hAi ⊢; linarith
  have buj' : |uj t - ampl gj * t * cos (c * t)| ≤ cstU c gj gj₁ gj₂ := by
    simp only [huj_def, hvj_def]; unfold pP cstU
    refine buj.trans ?_; unfold ampl at hAj ⊢; linarith
  have hWb := wronskian_abs_le (Ai := ampl gi) (Aj := ampl gj) hc ht
    (cst₁_nonneg (g₁ := gi₁) (g₂ := gi₂)) (cst₁_nonneg (g₁ := gj₁) (g₂ := gj₂))
    (cstU_nonneg hc (g := gi) (g₁ := gi₁) (g₂ := gi₂)) (cstU_nonneg hc (g := gj) (g₁ := gj₁) (g₂ := gj₂))
    bψi bψj bui' buj'
  have hne : |χi - χj| ≠ 0 := abs_ne_zero.mpr (sub_ne_zero.mpr hχ)
  have hpos : 0 < |χi - χj| := lt_of_le_of_ne (abs_nonneg _) hne.symm
  rw [show ∫ ξ in (1 : ℝ)..t, psi c gi ξ * psi c gj ξ = (ui t * psi c gj t - psi c gi t * uj t) / (χi - χj) by
    rw [eq_div_iff (sub_ne_zero.mpr hχ), mul_comm]; exact hW]
  rw [abs_div, div_le_div_iff₀ hpos (by positivity)]
  have hWt : |ui t * psi c gj t - psi c gi t * uj t| * t ≤ wronskianConst c gi gi₁ gi₂ gj gj₁ gj₂ := by
    unfold wronskianConst; rw [← le_div_iff₀ ht0]; exact hWb
  calc |ui t * psi c gj t - psi c gi t * uj t| * (|χi - χj| * t)
      = |ui t * psi c gj t - psi c gi t * uj t| * t * |χi - χj| := by ring
    _ ≤ wronskianConst c gi gi₁ gi₂ gj gj₁ gj₂ * |χi - χj| := mul_le_mul_of_nonneg_right hWt hpos.le

end Cvs.Prolate.RungOrthogonalityAtInfinity
