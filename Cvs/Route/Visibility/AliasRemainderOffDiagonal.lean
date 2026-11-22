import Mathlib
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.Approximant.SpineSubspace
import Cvs.L2a.AngularProlateTailPositive
import Cvs.Prolate.Gram.ProlateCellGramHalfUnit
import Cvs.Route.Visibility.AliasDiagonalWeight
import Cvs.Route.Visibility.AliasRemainderCentreBound
import Cvs.Route.Visibility.AliasRemainderSplit
import Cvs.Route.Visibility.AliasTailThroughWindow
import Cvs.Route.Visibility.AliasWindowCornerCut
import Cvs.Route.Visibility.LayerFloorDeepRemainderB
import Cvs.Route.Visibility.WindowChainCellFloors
import Cvs.Xi.EImageWindowPoisson

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# AL-R at `W̃ = 57/60` from P5 and the off-diagonal incoherence bound

The diagonal of `∫ρS_K²` with the AM–GM corner is `x∫ψ_G²W̃_K ≤ (19/20)·x∫_{(1,∞)}ψ_G² = (19/40)E(b)`;
with `OffDiag C₁` this gives `∫_{(1/2,1]} S_K² ≤ (19/40 + C₁/(2c))E(b)` for `K ≥ 4`, Fatou gives the same bound on
`T₃`, and Cvs.Route.Visibility.AliasRemainderCentreBound turns it into `ALR (57/60) C₁`.
-/

noncomputable section

open Real Set MeasureTheory Filter Topology Finset

namespace Cvs.Route.Visibility.AliasRemainderOffDiagonal
open Cvs.ZeroCounting

open Cvs.L2a.AngularProlateTailPositive (psi)
open Cvs.Approximant.DeepIndexSpineSpan (spineG)
open Cvs.Prolate.Gram.ProlateCellGramHalfUnit (energyE)
open Cvs.Route.Visibility.AliasWindowCornerCut (rho tau rho_nonneg)
open Cvs.Route.Visibility.AliasDiagonalWeight (wDiag wDiag_le wDiag_eq_zero)
open Cvs.Route.Visibility.AliasTailThroughWindow (yk partialTail pairJ offP OffDiag rhoC rhoT continuous_rho hasCompactSupport_rho continuous_psiG continuous_yk pairJ_diag rhoC_spec)

variable {x : ℕ} (b : Cvs.Approximant.SpineSubspace.SF x → ℝ)

/-! ### The diagonal -/

/-- A dilated window term `s ↦ w(s/k)/k·ψ_G(s)²` is integrable for continuous compactly supported `w`. -/
theorem integrable_dil {w : ℝ → ℝ} (hw : Continuous w) (hs : HasCompactSupport w) (k : ℕ) :
    Integrable fun s => w (s / k) / k * psi (2 * π * x) (spineG (2 * π * x) b) s ^ 2 := by
  by_cases hk : (k : ℝ) = 0
  · simp [hk]
  have hc : Continuous fun s : ℝ => w (s / k) := hw.comp (continuous_id.div_const _)
  have hsupp : HasCompactSupport fun s : ℝ => w (s / k) := by
    have e : (fun s : ℝ => w (s / k)) = fun s => w ((k : ℝ)⁻¹ • s) := by
      funext s; simp [smul_eq_mul, div_eq_inv_mul]
    rw [e]
    exact hs.comp_smul (inv_ne_zero hk)
  refine ((hc.div_const _).mul ((continuous_psiG b).pow 2)).integrable_of_hasCompactSupport
    (hsupp.mono fun s hs h0 => hs (by simp [h0]))

/-- `W̃_Kψ_G²` as a sum of dilated window terms. -/
theorem wDiag_mul_eq (K : ℕ) :
    (fun s => wDiag K s * psi (2 * π * x) (spineG (2 * π * x) b) s ^ 2)
      = fun s => (∑ k ∈ Icc 3 K, rho (s / k) / k * psi (2 * π * x) (spineG (2 * π * x) b) s ^ 2
        + rhoC (s / (3 : ℕ)) / (3 : ℕ) * psi (2 * π * x) (spineG (2 * π * x) b) s ^ 2)
        + rhoC (s / (4 : ℕ)) / (4 : ℕ) * psi (2 * π * x) (spineG (2 * π * x) b) s ^ 2 := by
  funext s
  simp only [wDiag, rhoC, add_mul, Finset.sum_mul, Nat.cast_ofNat]

/-- `W̃_Kψ_G²` is integrable. -/
theorem integrable_wDiag (K : ℕ) :
    Integrable fun s => wDiag K s * psi (2 * π * x) (spineG (2 * π * x) b) s ^ 2 := by
  rw [wDiag_mul_eq]
  exact ((integrable_finsetSum _ fun k _ => integrable_dil b continuous_rho hasCompactSupport_rho k).add
    (integrable_dil b rhoC_spec.1 rhoC_spec.2 3)).add (integrable_dil b rhoC_spec.1 rhoC_spec.2 4)

/-- **The diagonal is the weighted exterior energy**: `Σ_k J_{kk}(ρ) + J₃₃(ρ(1 − τ)) + J₄₄(ρ(1 − τ))
= x∫ W̃_K ψ_G²`. -/
theorem diag_eq (K : ℕ) :
    ∑ k ∈ Icc 3 K, pairJ x b rho k k + pairJ x b rhoC 3 3 + pairJ x b rhoC 4 4
      = (x : ℝ) * ∫ s, wDiag K s * psi (2 * π * x) (spineG (2 * π * x) b) s ^ 2 := by
  have hJ : ∀ (w : ℝ → ℝ) (k : ℕ), 1 ≤ k →
      pairJ x b w k k = (x : ℝ) * ∫ s, w (s / k) / k * psi (2 * π * x) (spineG (2 * π * x) b) s ^ 2 := by
    intro w k hk
    rw [pairJ_diag b w hk, div_eq_mul_inv (x : ℝ), mul_assoc, ← integral_const_mul]
    congr 1
    congr 1; funext s; ring
  rw [Finset.sum_congr rfl fun k hk => hJ rho k (by have := (Finset.mem_Icc.1 hk).1; omega),
    hJ rhoC 3 (by norm_num), hJ rhoC 4 (by norm_num), ← Finset.mul_sum, ← mul_add, ← mul_add]
  congr 1
  have hi := fun k : ℕ => integrable_dil b continuous_rho hasCompactSupport_rho k
  have hc := fun k : ℕ => integrable_dil b rhoC_spec.1 rhoC_spec.2 k
  have h1 : Integrable (fun s => ∑ k ∈ Finset.Icc 3 K,
      rho (s / k) / k * psi (2 * π * x) (spineG (2 * π * x) b) s ^ 2) :=
    integrable_finsetSum _ fun k _ => hi k
  have h12 : Integrable (fun s => ∑ k ∈ Finset.Icc 3 K,
      rho (s / k) / k * psi (2 * π * x) (spineG (2 * π * x) b) s ^ 2
      + rhoC (s / (3 : ℕ)) / (3 : ℕ) * psi (2 * π * x) (spineG (2 * π * x) b) s ^ 2) := h1.add (hc 3)
  rw [wDiag_mul_eq, integral_add h12 (hc 4), integral_add h1 (hc 3), integral_finsetSum _ fun k _ => hi k]

/-- **The diagonal bound**: `x∫W̃_Kψ_G² ≤ (19/20)·x∫_{(1,∞)}ψ_G²`. -/
theorem diag_le (hx : 80 ≤ 2 * π * x) (K : ℕ) :
    (x : ℝ) * ∫ s, wDiag K s * psi (2 * π * x) (spineG (2 * π * x) b) s ^ 2
      ≤ 19 / 20 * ((x : ℝ) * ∫ s in Ioi 1, psi (2 * π * x) (spineG (2 * π * x) b) s ^ 2) := by
  set ψ := psi (2 * π * x) (spineG (2 * π * x) b)
  have hI := Cvs.Route.Visibility.AliasRemainderSplit.integrableOn_psi_spineG_sq hx b
  have e : ∫ s, wDiag K s * ψ s ^ 2 = ∫ s in Ioi 1, wDiag K s * ψ s ^ 2 := by
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun s hs => ?_).symm
    simp only [Set.mem_Ioi, not_lt] at hs
    rw [wDiag_eq_zero (by linarith), zero_mul]
  have hle : ∫ s in Ioi 1, wDiag K s * ψ s ^ 2 ≤ ∫ s in Ioi 1, 19 / 20 * ψ s ^ 2 :=
    setIntegral_mono_on (integrable_wDiag b K).integrableOn (hI.const_mul _) measurableSet_Ioi
      fun s _ => mul_le_mul_of_nonneg_right (wDiag_le K s) (sq_nonneg _)
  rw [integral_const_mul] at hle
  rw [e]
  have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg x
  nlinarith [mul_le_mul_of_nonneg_left hle hx0]

/-! ### The window bound on partial sums -/

/-- The double sum over `Icc 3 K` splits into the diagonal, `P′` and the two corner entries. -/
theorem sum_pair_split (w : ℝ → ℝ) {K : ℕ} (hK : 4 ≤ K) :
    ∑ k ∈ Icc 3 K, ∑ l ∈ Icc 3 K, pairJ x b w k l
      = ∑ k ∈ Icc 3 K, pairJ x b w k k + ∑ k ∈ Icc 3 K, ∑ l ∈ Icc 3 K, (if offP k l then pairJ x b w k l else 0)
        + pairJ x b w 3 4 + pairJ x b w 4 3 := by
  have hpt : ∀ k l : ℕ, pairJ x b w k l = (if k = l then pairJ x b w k l else 0)
      + (if offP k l then pairJ x b w k l else 0) + (if k = 3 then (if l = 4 then pairJ x b w k l else 0) else 0)
      + (if k = 4 then (if l = 3 then pairJ x b w k l else 0) else 0) := by
    intro k l
    by_cases h1 : k = l <;> by_cases h3 : k = 3 <;> by_cases h4 : l = 4 <;> by_cases h5 : k = 4 <;>
      by_cases h6 : l = 3 <;> simp_all [offP]
  have h3 : (3 : ℕ) ∈ Finset.Icc 3 K := Finset.mem_Icc.2 ⟨le_rfl, by omega⟩
  have h4 : (4 : ℕ) ∈ Finset.Icc 3 K := Finset.mem_Icc.2 ⟨by norm_num, hK⟩
  rw [Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => hpt k l]
  simp only [Finset.sum_add_distrib]
  have hd : (∑ k ∈ Finset.Icc 3 K, ∑ l ∈ Finset.Icc 3 K, if k = l then pairJ x b w k l else 0)
      = ∑ k ∈ Finset.Icc 3 K, pairJ x b w k k :=
    Finset.sum_congr rfl fun k hk => by rw [Finset.sum_ite_eq, ite_eq_left hk]
  have c3 : (∑ k ∈ Finset.Icc 3 K, ∑ l ∈ Finset.Icc 3 K,
      if k = 3 then (if l = 4 then pairJ x b w k l else 0) else 0) = pairJ x b w 3 4 := by
    rw [Finset.sum_eq_single 3 (fun k _ hk => by simp [hk]) (fun h => absurd h3 h)]
    simp [h4]
  have c4 : (∑ k ∈ Finset.Icc 3 K, ∑ l ∈ Finset.Icc 3 K,
      if k = 4 then (if l = 3 then pairJ x b w k l else 0) else 0) = pairJ x b w 4 3 := by
    rw [Finset.sum_eq_single 4 (fun k _ hk => by simp [hk]) (fun h => absurd h4 h)]
    simp [h3]
  rw [hd, c3, c4]

/-- **The window bound**: for `K ≥ 4`, `∫_{(1/2,1]} S_K² ≤ (19/20)‖g‖² + Σ_{P′}J_{kl}(ρ) + 2J₃₄(ρτ)`. -/
theorem integral_partial_sq_le_diag (hx : 80 ≤ 2 * π * x) {K : ℕ} (hK : 4 ≤ K) :
    ∫ θ in Ioc (1 / 2 : ℝ) 1, partialTail x b K θ ^ 2
      ≤ 19 / 20 * ((x : ℝ) * ∫ s in Ioi 1, psi (2 * π * x) (spineG (2 * π * x) b) s ^ 2)
        + (∑ k ∈ Icc 3 K, ∑ l ∈ Icc 3 K, (if offP k l then pairJ x b rho k l else 0) + 2 * pairJ x b rhoT 3 4) := by
  have h1 := Cvs.Route.Visibility.AliasTailThroughWindow.integral_partial_sq_le b K
  rw [Cvs.Route.Visibility.AliasTailThroughWindow.integral_rho_partial_sq, sum_pair_split b rho hK, Cvs.Route.Visibility.AliasTailThroughWindow.pairJ_comm b rho 4 3] at h1
  have h2 := Cvs.Route.Visibility.AliasTailThroughWindow.corner_le (x := x) b
  have h3 := diag_eq b K
  have h4 := diag_le b hx K
  linarith

/-! ### Fatou and AL-R -/

/-- `S_K → T₃` almost everywhere on `(1/2, 1]`. -/
theorem ae_tendsto_partial (hx : 80 ≤ 2 * π * x) :
    ∀ᵐ θ ∂(volume.restrict (Ioc (1 / 2 : ℝ) 1)),
      Tendsto (fun K => partialTail x b K θ) atTop (𝓝 (Cvs.Route.Visibility.AliasRemainderSplit.aliasTail x b θ)) := by
  rw [ae_restrict_iff' measurableSet_Ioc]
  filter_upwards [Cvs.Xi.EImageWindowPoisson.ae_notMem_lattice (1 / (x : ℝ))] with θ hlat hθ
  refine (Cvs.Route.Visibility.AliasRemainderSplit.tendsto_aliasTail hx b hθ hlat).congr fun K => ?_
  simp only [partialTail, yk, Finset.mul_sum]

/-- **Fatou for the alias tail**: a bound on every `∫_{(1/2,1]} S_K²`, `K ≥ 4`, bounds `∫_{(1/2,1]} T₃²`. -/
theorem integral_aliasTail_sq_le (hx : 80 ≤ 2 * π * x) {B : ℝ}
    (h : ∀ K, 4 ≤ K → ∫ θ in Ioc (1 / 2 : ℝ) 1, partialTail x b K θ ^ 2 ≤ B) :
    ∫ θ in Ioc (1 / 2 : ℝ) 1, Cvs.Route.Visibility.AliasRemainderSplit.aliasTail x b θ ^ 2 ≤ B := by
  set μ := volume.restrict (Ioc (1 / 2 : ℝ) 1)
  have hc : ∀ K, Continuous (partialTail x b K) := fun K =>
    continuous_finsetSum _ fun k _ => continuous_yk b k
  have hB : 0 ≤ B := (setIntegral_nonneg measurableSet_Ioc fun _ _ => sq_nonneg _).trans (h 4 le_rfl)
  have hT := (Cvs.Route.Visibility.AliasRemainderSplit.memLp_aliasTail hx b).integrable_sq
  have hS : ∀ K, Integrable (fun θ => partialTail x b K θ ^ 2) μ := fun K =>
    (Cvs.Route.Visibility.AliasRemainderSplit.memLp_of_continuousOn (hc K).continuousOn).integrable_sq
  have e1 : ENNReal.ofReal (∫ θ, Cvs.Route.Visibility.AliasRemainderSplit.aliasTail x b θ ^ 2 ∂μ)
      = ∫⁻ θ, liminf (fun K => ENNReal.ofReal (partialTail x b K θ ^ 2)) atTop ∂μ := by
    rw [ofReal_integral_eq_lintegral_ofReal hT (Eventually.of_forall fun _ => sq_nonneg _)]
    refine lintegral_congr_ae ?_
    filter_upwards [ae_tendsto_partial b hx] with θ hθ
    exact (((ENNReal.continuous_ofReal.tendsto _).comp (hθ.pow 2)).liminf_eq).symm
  have hm : ∀ K, AEMeasurable (fun θ => ENNReal.ofReal (partialTail x b K θ ^ 2)) μ := fun K => by
    have hK : Continuous fun θ => partialTail x b K θ ^ 2 := (hc K).pow 2
    exact hK.measurable.ennreal_ofReal.aemeasurable
  have h2 := lintegral_liminf_le' (μ := μ) (u := atTop)
    (f := fun K θ => ENNReal.ofReal (partialTail x b K θ ^ 2)) hm
  have h3 : liminf (fun K => ∫⁻ θ, ENNReal.ofReal (partialTail x b K θ ^ 2) ∂μ) atTop ≤ ENNReal.ofReal B := by
    calc liminf (fun K => ∫⁻ θ, ENNReal.ofReal (partialTail x b K θ ^ 2) ∂μ) atTop
        ≤ liminf (fun _ : ℕ => ENNReal.ofReal B) atTop := by
          refine liminf_le_liminf ?_
          filter_upwards [eventually_ge_atTop 4] with K hK
          rw [← ofReal_integral_eq_lintegral_ofReal (hS K) (Eventually.of_forall fun _ => sq_nonneg _)]
          exact ENNReal.ofReal_le_ofReal (h K hK)
      _ = ENNReal.ofReal B := liminf_const _
  have := e1.trans_le (h2.trans h3)
  exact (ENNReal.ofReal_le_ofReal_iff hB).1 this

/-- **The alias-tail bound at `W̃ = 57/60`** from the off-diagonal incoherence bound. -/
theorem aliasTail_of_offDiag {C₁ : ℝ} (hO : OffDiag C₁) : Cvs.Route.Visibility.AliasRemainderCentreBound.AliasTail (57 / 60) C₁ := by
  filter_upwards [hO, Cvs.Route.Visibility.LayerFloorDeepRemainderB.eventually_scale] with x hO hx b
  have hE := Cvs.Route.Visibility.AliasRemainderSplit.ext_energy hx b
  refine integral_aliasTail_sq_le b hx fun K hK => ?_
  have h1 := integral_partial_sq_le_diag b hx hK
  have h2 := hO b K hK
  have hc : (2 * π * (x : ℝ)) ≠ 0 := by positivity
  calc ∫ θ in Ioc (1 / 2 : ℝ) 1, partialTail x b K θ ^ 2
      ≤ 19 / 20 * (energyE x b / 2) + C₁ / (2 * π * x) * (energyE x b / 2) := by rw [← hE]; linarith
    _ = (57 / 60 / 2 + C₁ / (2 * (2 * π * x))) * energyE x b := by field_simp; ring

/-- **AL-R at `W̃ = 57/60`**: P5 and the off-diagonal incoherence bound give `ALR (57/60) C₁`. -/
theorem alr_of_offDiag {C₁ : ℝ} (hZ : Cvs.Route.Visibility.AliasRemainderCentreBound.ZBound) (hO : OffDiag C₁) : Cvs.Route.Visibility.WindowChainCellFloors.ALR (57 / 60) C₁ :=
  Cvs.Route.Visibility.AliasRemainderCentreBound.alr_of_aliasTail hZ (aliasTail_of_offDiag hO)

end Cvs.Route.Visibility.AliasRemainderOffDiagonal
