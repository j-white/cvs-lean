import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.LeftRight
import Cvs.L2a.BumpVNorm
import Cvs.L2a.RungChiHierarchy
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Upstream.SineSquaredBump

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The dilated combination as the centred system, and its `V`-norm through the bump

The dilation `f = G_k(m·)`, `u = mU_k(m·)` of the `χ`-hierarchy (Cvs.L2a.RungChiHierarchy) solves `f' = u/(m²θ² − 1)`,
`u' = −q̄f + r̄` with `q̄ = c²m⁴θ² − m²χ̄` and the centred source `r̄ = m²(G_{k+1}(m·) − χ̄ G_k(m·))` for any centre
`χ̄`, so Cvs.L2a.BumpVNorm bounds its `V`-norm through the bump on `[α, β]` with `mα > 1`, `c²m²α² > χ̄`: no boundary term, the
majorant `W₂ = 2(m²θ² − 1)((π/h)²/q̄ + (2c²m⁴θ)²/q̄³)` and the centred source.
-/

namespace Cvs.L2a.DilatedCombinationVNorm

open Real Set intervalIntegral Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.RungChiHierarchy Cvs.Upstream.SineSquaredBump

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **The centred dilated system**: `u' = −(c²m⁴θ² − m²χ̄) f + m²(G_{k+1}(mθ) − χ̄ G_k(mθ))`. -/
theorem hasDerivAt_Gk_dilate_centred {c m χb : ℝ} {a χ : ι → ℝ} {ψ u : ι → ℝ → ℝ} {θ : ℝ} (k : ℕ)
    (hψ : ∀ i, HasDerivAt (ψ i) (u i (m * θ) / pP (m * θ)) (m * θ))
    (hu : ∀ i, HasDerivAt (u i) (-(qP c (χ i) (m * θ) * ψ i (m * θ))) (m * θ)) :
    HasDerivAt (fun θ => Gk a χ ψ k (m * θ)) (m * Gk a χ u k (m * θ) / (m ^ 2 * θ ^ 2 - 1)) θ ∧
    HasDerivAt (fun θ => m * Gk a χ u k (m * θ))
      (-((c ^ 2 * m ^ 4 * θ ^ 2 - m ^ 2 * χb) * Gk a χ ψ k (m * θ))
        + m ^ 2 * (Gk a χ ψ (k + 1) (m * θ) - χb * Gk a χ ψ k (m * θ))) θ := by
  obtain ⟨h1, h2⟩ := hasDerivAt_Gk_dilate (c := c) (a := a) (χ := χ) (ψ := ψ) (u := u) (m := m) (θ := θ) k hψ hu
  exact ⟨h1, h2.congr_deriv (by ring)⟩

/-- **The `V`-norm of a dilated combination through the bump on `[α, β]`**, `mα > 1`, `c²m²α² > χ̄`, `m > 0`. -/
theorem V_norm_dilate_le {c m χb α β h ε : ℝ} {a χ : ι → ℝ} {ψ u : ι → ℝ → ℝ} (k : ℕ)
    (hm : 0 < m) (hα : 1 < m * α) (hχ : χb < c ^ 2 * m ^ 2 * α ^ 2) (hh : 0 < h) (hαβ : α + h ≤ β - h) (hε : 0 < ε)
    (hψ : ∀ i, ∀ ξ, 1 < ξ → HasDerivAt (ψ i) (u i ξ / pP ξ) ξ)
    (hu : ∀ i, ∀ ξ, HasDerivAt (u i) (-(qP c (χ i) ξ * ψ i ξ)) ξ)
    (hψc : ∀ i, Continuous (ψ i)) :
    (1 - ε / 2) * ∫ θ in α..β, bump α β h θ / (c ^ 2 * m ^ 4 * θ ^ 2 - m ^ 2 * χb)
        * ((m * Gk a χ u k (m * θ)) ^ 2 / (m ^ 2 * θ ^ 2 - 1))
      ≤ 1 / (2 * ε) * (∫ θ in α..β, 2 * (m ^ 2 * θ ^ 2 - 1)
            * ((Real.pi / h) ^ 2 / (c ^ 2 * m ^ 4 * θ ^ 2 - m ^ 2 * χb)
              + (2 * c ^ 2 * m ^ 4 * θ) ^ 2 / (c ^ 2 * m ^ 4 * θ ^ 2 - m ^ 2 * χb) ^ 3) * Gk a χ ψ k (m * θ) ^ 2)
        + ∫ θ in α..β, bump α β h θ / (c ^ 2 * m ^ 4 * θ ^ 2 - m ^ 2 * χb)
            * ((c ^ 2 * m ^ 4 * θ ^ 2 - m ^ 2 * χb) * Gk a χ ψ k (m * θ) ^ 2
              - Gk a χ ψ k (m * θ) * (m ^ 2 * (Gk a χ ψ (k + 1) (m * θ) - χb * Gk a χ ψ k (m * θ)))) := by
  have hα0 : 0 < α := by nlinarith
  have hp : ∀ θ ∈ Icc α β, 0 < m ^ 2 * θ ^ 2 - 1 := fun θ hθ => by
    have : m * α ≤ m * θ := mul_le_mul_of_nonneg_left hθ.1 hm.le
    nlinarith
  have hqb : ∀ θ ∈ Icc α β, 0 < c ^ 2 * m ^ 4 * θ ^ 2 - m ^ 2 * χb := fun θ hθ => by
    have h1 : α ^ 2 ≤ θ ^ 2 := pow_le_pow_left₀ hα0.le hθ.1 2
    have h2 : c ^ 2 * m ^ 2 * α ^ 2 ≤ c ^ 2 * m ^ 2 * θ ^ 2 := mul_le_mul_of_nonneg_left h1 (by positivity)
    have hm2 : 0 < m ^ 2 := by positivity
    have : m ^ 2 * χb < m ^ 2 * (c ^ 2 * m ^ 2 * θ ^ 2) := mul_lt_mul_of_pos_left (by linarith) hm2
    nlinarith
  have hsys : ∀ θ ∈ Icc α β,
      HasDerivAt (fun θ => Gk a χ ψ k (m * θ)) (m * Gk a χ u k (m * θ) / (m ^ 2 * θ ^ 2 - 1)) θ ∧
      HasDerivAt (fun θ => m * Gk a χ u k (m * θ))
        (-((c ^ 2 * m ^ 4 * θ ^ 2 - m ^ 2 * χb) * Gk a χ ψ k (m * θ))
          + m ^ 2 * (Gk a χ ψ (k + 1) (m * θ) - χb * Gk a χ ψ k (m * θ))) θ := fun θ hθ => by
    have hmθ : 1 < m * θ := by
      have : m * α ≤ m * θ := mul_le_mul_of_nonneg_left hθ.1 hm.le
      linarith
    exact hasDerivAt_Gk_dilate_centred k (fun i => hψ i (m * θ) hmθ) (fun i => hu i (m * θ))
  have hqb' : ∀ θ ∈ Icc α β, HasDerivAt (fun θ => c ^ 2 * m ^ 4 * θ ^ 2 - m ^ 2 * χb) (2 * c ^ 2 * m ^ 4 * θ) θ :=
    fun θ _ => by
      have := ((hasDerivAt_pow 2 θ).const_mul (c ^ 2 * m ^ 4)).sub_const (m ^ 2 * χb)
      refine this.congr_deriv ?_
      simp <;> ring
  have hGk1c : Continuous fun θ => Gk a χ ψ (k + 1) (m * θ) := by
    unfold Gk; exact continuous_finsetSum _ fun i _ => continuous_const.mul ((hψc i).comp (continuous_const.mul continuous_id))
  have hGkc : Continuous fun θ => Gk a χ ψ k (m * θ) := by
    unfold Gk; exact continuous_finsetSum _ fun i _ => continuous_const.mul ((hψc i).comp (continuous_const.mul continuous_id))
  have hrc : ContinuousOn (fun θ => m ^ 2 * (Gk a χ ψ (k + 1) (m * θ) - χb * Gk a χ ψ k (m * θ))) (Icc α β) :=
    (continuous_const.mul (hGk1c.sub (continuous_const.mul hGkc))).continuousOn
  exact Cvs.L2a.BumpVNorm.V_norm_bump_le (f := fun θ => Gk a χ ψ k (m * θ)) (u := fun θ => m * Gk a χ u k (m * θ))
    (p := fun θ => m ^ 2 * θ ^ 2 - 1) (qb := fun θ => c ^ 2 * m ^ 4 * θ ^ 2 - m ^ 2 * χb)
    (qb' := fun θ => 2 * c ^ 2 * m ^ 4 * θ)
    (rb := fun θ => m ^ 2 * (Gk a χ ψ (k + 1) (m * θ) - χb * Gk a χ ψ k (m * θ)))
    hh hαβ hε hp hqb (fun θ hθ => (hsys θ hθ).1) (fun θ hθ => (hsys θ hθ).2) hqb' (by fun_prop) (by fun_prop) hrc

end Cvs.L2a.DilatedCombinationVNorm
