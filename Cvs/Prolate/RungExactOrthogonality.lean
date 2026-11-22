import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.Prolate.Gram.RungGramFloorAtInfinity
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.RungDecayBeyondEdge
import Cvs.Prolate.RungOrthogonalityAtInfinity

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Rungs with distinct eigenvalues are exactly orthogonal on `(1, ∞)`

Each rung `ψ = psi c g` decays like `1/ξ` (Cvs.Prolate.RungDecayBeyondEdge), so products of rungs are integrable on `Ioi 1` and `ψ ∈ L²(Ioi 1)`.
For `χ_i ≠ χ_j` the bound `|∫₁ᵗ ψ_iψ_j| ≤ K/(|χ_i − χ_j| t)` (Cvs.Prolate.RungOrthogonalityAtInfinity) gives `∫_{Ioi 1} ψ_iψ_j = 0` as `t → ∞`, hence
`∫_{Ioi 1} (Σ a_iψ_i)² = Σ a_i² ∫_{Ioi 1} ψ_i²` for rungs with pairwise distinct `χ`.
-/

namespace Cvs.Prolate.RungExactOrthogonality

open Real Set Filter Topology MeasureTheory Cvs.L2a.AngularProlateTailPositive

/-- The decay constant `D = |g(1) + g(−1)|/c + (|g₁(1) − g₁(−1)| + ∫|g₂|)/c²` of Cvs.Prolate.RungDecayBeyondEdge: `|ψ(ξ)| ≤ D/ξ` on `ξ ≥ 1`. -/
noncomputable def decayConst (c : ℝ) (g g₁ g₂ : ℝ → ℝ) : ℝ :=
  |g 1 + g (-1)| / c + (|g₁ 1 - g₁ (-1)| + ∫ s in (-1 : ℝ)..1, |g₂ s|) / c ^ 2

/-- The product of two rungs is integrable on `Ioi 1`, being continuous and bounded by `D_iD_j/ξ²`. -/
theorem integrableOn_psi_mul {gi gi₁ gi₂ gj gj₁ gj₂ : ℝ → ℝ} {c χi χj : ℝ}
    (hgi : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt gi (gi₁ s) s)
    (hgi₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt gi₁ (gi₂ s) s) (hgi₂c : ContinuousOn gi₂ (uIcc (-1) 1))
    (hangi : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * gi₂ s - 2 * s * gi₁ s - c ^ 2 * s ^ 2 * gi s + χi * gi s = 0)
    (hgj : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt gj (gj₁ s) s)
    (hgj₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt gj₁ (gj₂ s) s) (hgj₂c : ContinuousOn gj₂ (uIcc (-1) 1))
    (hangj : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * gj₂ s - 2 * s * gj₁ s - c ^ 2 * s ^ 2 * gj s + χj * gj s = 0)
    (hc : 0 < c) :
    IntegrableOn (fun ξ => psi c gi ξ * psi c gj ξ) (Ioi 1) := by
  have hci := (Cvs.Prolate.Gram.RungGramFloorAtInfinity.rung_system hgi hgi₁ hgi₂c hangi).2.2.1
  have hcj := (Cvs.Prolate.Gram.RungGramFloorAtInfinity.rung_system hgj hgj₁ hgj₂c hangj).2.2.1
  have hpow : IntegrableOn (fun ξ : ℝ => ξ ^ (-2 : ℝ)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos
  refine Integrable.mono' (hpow.const_mul (decayConst c gi gi₁ gi₂ * decayConst c gj gj₁ gj₂))
    (hci.mul hcj).aestronglyMeasurable ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi fun ξ hξ => ?_
  have hξ1 : 1 ≤ ξ := le_of_lt hξ
  have hξ0 : 0 < ξ := by linarith
  have bi := Cvs.Prolate.RungDecayBeyondEdge.abs_psi_le hgi hgi₁ hgi₂c hc hξ1
  have bj := Cvs.Prolate.RungDecayBeyondEdge.abs_psi_le hgj hgj₁ hgj₂c hc hξ1
  have hDj : 0 ≤ decayConst c gj gj₁ gj₂ / ξ := (abs_nonneg _).trans bj
  rw [Real.norm_eq_abs, abs_mul, Real.rpow_neg hξ0.le, Real.rpow_two]
  calc |psi c gi ξ| * |psi c gj ξ|
      ≤ decayConst c gi gi₁ gi₂ / ξ * (decayConst c gj gj₁ gj₂ / ξ) :=
        mul_le_mul bi bj (abs_nonneg _) ((abs_nonneg _).trans bi)
    _ = decayConst c gi gi₁ gi₂ * decayConst c gj gj₁ gj₂ * (ξ ^ 2)⁻¹ := by field_simp

/-- A rung lies in `L²(Ioi 1)`. -/
theorem memLp_psi {g g₁ g₂ : ℝ → ℝ} {c χ : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hc : 0 < c) :
    MemLp (psi c g) 2 (volume.restrict (Ioi 1)) := by
  have hψc := (Cvs.Prolate.Gram.RungGramFloorAtInfinity.rung_system hg hg₁ hg₂c hang).2.2.1
  rw [memLp_two_iff_integrable_sq hψc.aestronglyMeasurable]
  have h := integrableOn_psi_mul hg hg₁ hg₂c hang hg hg₁ hg₂c hang hc
  refine (integrableOn_congr_fun (fun ξ _ => ?_) measurableSet_Ioi).mp h
  ring

/-- **Exact orthogonality on `(1, ∞)`**: two rungs with `χ_i ≠ χ_j` satisfy `∫_{Ioi 1} ψ_iψ_j = 0`. -/
theorem integral_psi_mul_eq_zero {gi gi₁ gi₂ gj gj₁ gj₂ : ℝ → ℝ} {c χi χj : ℝ}
    (hgi : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt gi (gi₁ s) s)
    (hgi₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt gi₁ (gi₂ s) s) (hgi₂c : ContinuousOn gi₂ (uIcc (-1) 1))
    (hangi : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * gi₂ s - 2 * s * gi₁ s - c ^ 2 * s ^ 2 * gi s + χi * gi s = 0)
    (hgj : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt gj (gj₁ s) s)
    (hgj₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt gj₁ (gj₂ s) s) (hgj₂c : ContinuousOn gj₂ (uIcc (-1) 1))
    (hangj : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * gj₂ s - 2 * s * gj₁ s - c ^ 2 * s ^ 2 * gj s + χj * gj s = 0)
    (hc : 0 < c) (hχ : χi ≠ χj) :
    ∫ ξ in Ioi 1, psi c gi ξ * psi c gj ξ = 0 := by
  have hI := integrableOn_psi_mul hgi hgi₁ hgi₂c hangi hgj hgj₁ hgj₂c hangj hc
  have hlim := intervalIntegral_tendsto_integral_Ioi 1 hI tendsto_id
  set K := Cvs.Prolate.RungOrthogonalityAtInfinity.wronskianConst c gi gi₁ gi₂ gj gj₁ gj₂
  have hd : 0 < |χi - χj| := abs_pos.mpr (sub_ne_zero.mpr hχ)
  have hzero : Tendsto (fun t : ℝ => ∫ ξ in (1 : ℝ)..id t, psi c gi ξ * psi c gj ξ) atTop (𝓝 0) := by
    have hK : Tendsto (fun t : ℝ => K / |χi - χj| * t⁻¹) atTop (𝓝 0) := by
      simpa using tendsto_inv_atTop_zero.const_mul (K / |χi - χj|)
    refine squeeze_zero_norm' ?_ hK
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    rw [Real.norm_eq_abs]
    have h := Cvs.Prolate.RungOrthogonalityAtInfinity.integral_psi_mul_le hgi hgi₁ hgi₂c hangi hgj hgj₁ hgj₂c hangj hc hχ ht
    calc |∫ ξ in (1 : ℝ)..id t, psi c gi ξ * psi c gj ξ| ≤ K / (|χi - χj| * t) := h
      _ = K / |χi - χj| * t⁻¹ := by rw [div_mul_eq_div_div, div_eq_mul_inv]
  exact tendsto_nhds_unique hlim hzero

/-- **The mass of a combination on `(1, ∞)` is diagonal**: for rungs with pairwise distinct `χ_i`,
`∫_{Ioi 1} (Σ a_iψ_i)² = Σ a_i² ∫_{Ioi 1} ψ_i²`. -/
theorem integral_span_sq {ι : Type*} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 0 < c) (hχ : Function.Injective χ) :
    ∫ ξ in Ioi 1, (∑ i, a i * psi c (g i) ξ) ^ 2 = ∑ i, a i ^ 2 * ∫ ξ in Ioi 1, psi c (g i) ξ ^ 2 := by
  classical
  have hI : ∀ i j, IntegrableOn (fun ξ => psi c (g i) ξ * psi c (g j) ξ) (Ioi 1) := fun i j =>
    integrableOn_psi_mul (hg i) (hg₁ i) (hg₂c i) (hang i) (hg j) (hg₁ j) (hg₂c j) (hang j) hc
  have e : ∀ ξ, (∑ i, a i * psi c (g i) ξ) ^ 2
      = ∑ i, ∑ j, a i * a j * (psi c (g i) ξ * psi c (g j) ξ) := by
    intro ξ
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  simp_rw [e]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hI i j).const_mul _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => (hI i j).const_mul _]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have hoff : ∑ j ∈ Finset.univ.erase i, ∫ ξ in Ioi 1, a i * a j * (psi c (g i) ξ * psi c (g j) ξ) = 0 := by
    refine Finset.sum_eq_zero fun j hj => ?_
    have hij : χ i ≠ χ j := fun h => (Finset.ne_of_mem_erase hj) (hχ h).symm
    rw [integral_const_mul, integral_psi_mul_eq_zero (hg i) (hg₁ i) (hg₂c i) (hang i) (hg j) (hg₁ j) (hg₂c j)
      (hang j) hc hij, mul_zero]
  rw [hoff, add_zero, integral_const_mul]
  congr 1
  · ring
  · exact integral_congr_ae (ae_of_all _ fun ξ => by simp only; ring)

end Cvs.Prolate.RungExactOrthogonality
