import Mathlib
import Cvs.L2a.BumpVNorm
import Cvs.L2a.DilatedCombinationVNorm
import Cvs.L2a.HierarchyLeafMasses
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
# The `V`-norm of a dilated combination by the masses

The right side of Cvs.L2a.DilatedCombinationVNorm by masses: `∫ W₂ G_k(m·)² ≤ A (1/m) Σ a_i²χ_i^{2k} M_i` when `W₂ ≤ A`, and
`∫ (bump/q̄)(q̄f² − f r̄) ≤ (1 + δ/2)∫ f² + (B/2δ)∫ r̄²` when `1/q̄² ≤ B`, the centred source having `∫ r̄² ≤ m³ Σ a_i²χ_i^{2k}(χ_i − χ̄)² M_i`;
so `(1 − ε/2)` times the `V`-norm on the inner interval is at most `(A/2ε + 1 + δ/2)(1/m)Σ a_i²χ_i^{2k}M_i + (Bm³/2δ)Σ a_i²χ_i^{2k}(χ_i − χ̄)²M_i`,
from orthogonality at infinity (Cvs.Prolate.Gram.RungCombinationNormInterval) and nothing else about the rungs.
-/

namespace Cvs.L2a.DilatedVNormMasses

open Real Set Finset intervalIntegral Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.RungChiHierarchy Cvs.Upstream.SineSquaredBump

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The centred source is a dilated combination with coefficients `m² a_i χ_i^k (χ_i − χ̄)`. -/
theorem centred_source_eq (a χ : ι → ℝ) (ψ : ι → ℝ → ℝ) (k : ℕ) (m χb ξ : ℝ) :
    m ^ 2 * (Gk a χ ψ (k + 1) ξ - χb * Gk a χ ψ k ξ) = ∑ i, (m ^ 2 * (a i * χ i ^ k * (χ i - χb))) * ψ i ξ := by
  unfold Gk
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _; ring

/-- **The `V`-norm on the inner interval by the masses.** With `hcross`, `hmass` the orthogonality-at-infinity data of
the rungs (Cvs.Prolate.Gram.RungCombinationNormInterval) beyond `mβ`, `W₂ ≤ A` and `1/q̄² ≤ B` on `[α, β]`, and `δ > 0`:
`(1 − ε/2) ∫_{α+h}^{β−h} (mU_k(m·))²/((m²θ² − 1) q̄) ≤ (A/2ε + 1 + δ/2)(1/m)Σ a_i²χ_i^{2k}M_i + (B m³/2δ) Σ a_i²χ_i^{2k}(χ_i − χ̄)²M_i`. -/
theorem V_norm_masses {c m χb α β h ε δ A B : ℝ} {a χ : ι → ℝ} {ψ u : ι → ℝ → ℝ} (K : ι → ι → ℝ) (Mm : ι → ℝ) (k : ℕ)
    (hm : 0 < m) (hα : 1 < m * α) (hχ : χb < c ^ 2 * m ^ 2 * α ^ 2) (hh : 0 < h) (hαβ : α + h ≤ β - h) (hε : 0 < ε) (hε2 : ε < 2)
    (hδ : 0 < δ)
    (hψ : ∀ i, ∀ ξ, 1 < ξ → HasDerivAt (ψ i) (u i ξ / pP ξ) ξ)
    (hu : ∀ i, ∀ ξ, HasDerivAt (u i) (-(qP c (χ i) ξ * ψ i ξ)) ξ)
    (hψc : ∀ i, Continuous (ψ i)) (huc : ∀ i, Continuous (u i))
    (hcross : ∀ i j, i ≠ j → ∀ t, m * β ≤ t → |∫ ξ in (1 : ℝ)..t, ψ i ξ * ψ j ξ| ≤ K i j / t)
    (hmass : ∀ i, ∀ t, m * β ≤ t → ∫ ξ in (1 : ℝ)..t, ψ i ξ ^ 2 ≤ Mm i)
    (hA : ∀ θ ∈ Icc α β, 2 * (m ^ 2 * θ ^ 2 - 1)
      * ((Real.pi / h) ^ 2 / (c ^ 2 * m ^ 4 * θ ^ 2 - m ^ 2 * χb)
        + (2 * c ^ 2 * m ^ 4 * θ) ^ 2 / (c ^ 2 * m ^ 4 * θ ^ 2 - m ^ 2 * χb) ^ 3) ≤ A)
    (hB : ∀ θ ∈ Icc α β, 1 / (c ^ 2 * m ^ 4 * θ ^ 2 - m ^ 2 * χb) ^ 2 ≤ B) :
    (1 - ε / 2) * ∫ θ in (α + h)..(β - h),
        (m * Gk a χ u k (m * θ)) ^ 2 / ((m ^ 2 * θ ^ 2 - 1) * (c ^ 2 * m ^ 4 * θ ^ 2 - m ^ 2 * χb))
      ≤ (A / (2 * ε) + 1 + δ / 2) * (1 / m * ∑ i, (a i * χ i ^ k) ^ 2 * Mm i)
        + B * m ^ 3 / (2 * δ) * ∑ i, (a i * χ i ^ k * (χ i - χb)) ^ 2 * Mm i := by
  have hα0 : 0 < α := by nlinarith
  have hab : α ≤ β := by linarith
  have hp : ∀ θ ∈ Icc α β, 0 < m ^ 2 * θ ^ 2 - 1 := fun θ hθ => by
    have : m * α ≤ m * θ := mul_le_mul_of_nonneg_left hθ.1 hm.le
    nlinarith
  have hqb : ∀ θ ∈ Icc α β, 0 < c ^ 2 * m ^ 4 * θ ^ 2 - m ^ 2 * χb := fun θ hθ => by
    have h1 : α ^ 2 ≤ θ ^ 2 := pow_le_pow_left₀ hα0.le hθ.1 2
    have h2 : c ^ 2 * m ^ 2 * α ^ 2 ≤ c ^ 2 * m ^ 2 * θ ^ 2 := mul_le_mul_of_nonneg_left h1 (by positivity)
    have hm2 : 0 < m ^ 2 := by positivity
    have : m ^ 2 * χb < m ^ 2 * (c ^ 2 * m ^ 2 * θ ^ 2) := mul_lt_mul_of_pos_left (by linarith) hm2
    nlinarith
  set f : ℝ → ℝ := fun θ => Gk a χ ψ k (m * θ) with hf
  set r : ℝ → ℝ := fun θ => m ^ 2 * (Gk a χ ψ (k + 1) (m * θ) - χb * Gk a χ ψ k (m * θ)) with hr
  set qb : ℝ → ℝ := fun θ => c ^ 2 * m ^ 4 * θ ^ 2 - m ^ 2 * χb with hqbdef
  have hfc : Continuous f := by
    simp only [hf]; unfold Gk
    exact continuous_finsetSum _ fun i _ => continuous_const.mul ((hψc i).comp (continuous_const.mul continuous_id))
  have hrc : Continuous r := by
    simp only [hr]; unfold Gk
    exact continuous_const.mul ((continuous_finsetSum _ fun i _ =>
      continuous_const.mul ((hψc i).comp (continuous_const.mul continuous_id))).sub (continuous_const.mul
      (continuous_finsetSum _ fun i _ => continuous_const.mul ((hψc i).comp (continuous_const.mul continuous_id)))))
  have hUc : Continuous fun θ => m * Gk a χ u k (m * θ) := by
    unfold Gk
    exact continuous_const.mul (continuous_finsetSum _ fun i _ =>
      continuous_const.mul ((huc i).comp (continuous_const.mul continuous_id)))
  -- the norms by the masses
  have hcont : ∀ i, ContinuousOn (ψ i) (Ici 1) := fun i => (hψc i).continuousOn
  have hn1 : ∫ θ in α..β, f θ ^ 2 ≤ 1 / m * ∑ i, (a i * χ i ^ k) ^ 2 * Mm i := by
    have := Cvs.L2a.HierarchyLeafMasses.dilated_norm_le (L := α) (R := β) hm hα.le hab ψ (fun i => a i * χ i ^ k) K Mm hcont
      hcross hmass
    simpa only [hf, Gk] using this
  have hn2 : ∫ θ in α..β, r θ ^ 2 ≤ 1 / m * ∑ i, (m ^ 2 * (a i * χ i ^ k * (χ i - χb))) ^ 2 * Mm i := by
    have := Cvs.L2a.HierarchyLeafMasses.dilated_norm_le (L := α) (R := β) hm hα.le hab ψ
      (fun i => m ^ 2 * (a i * χ i ^ k * (χ i - χb))) K Mm hcont hcross hmass
    have e : (fun θ => r θ ^ 2) = fun θ => (∑ i, (m ^ 2 * (a i * χ i ^ k * (χ i - χb))) * ψ i (m * θ)) ^ 2 := by
      funext θ; simp only [hr]; rw [centred_source_eq]
    rw [e]; exact this
  -- the V-norm through the bump (Cvs.L2a.DilatedCombinationVNorm) and the inner interval (Cvs.L2a.BumpVNorm)
  have hV := Cvs.L2a.DilatedCombinationVNorm.V_norm_dilate_le (a := a) (χ := χ) (ψ := ψ) (u := u) (χb := χb) k hm hα hχ hh hαβ
    hε hψ hu hψc
  have hinner := Cvs.L2a.BumpVNorm.V_norm_inner_le (u := fun θ => m * Gk a χ u k (m * θ))
    (p := fun θ => m ^ 2 * θ ^ 2 - 1) (qb := qb) hh hαβ hp hqb hUc.continuousOn (by fun_prop) (by fun_prop)
  -- the two integrals on the right of Cvs.L2a.DilatedCombinationVNorm
  have hI1 : IntervalIntegrable (fun θ => f θ ^ 2) MeasureTheory.volume α β := (hfc.pow 2).intervalIntegrable α β
  have hI2 : IntervalIntegrable (fun θ => r θ ^ 2) MeasureTheory.volume α β := (hrc.pow 2).intervalIntegrable α β
  have hW : ∫ θ in α..β, 2 * (m ^ 2 * θ ^ 2 - 1)
      * ((Real.pi / h) ^ 2 / (c ^ 2 * m ^ 4 * θ ^ 2 - m ^ 2 * χb)
        + (2 * c ^ 2 * m ^ 4 * θ) ^ 2 / (c ^ 2 * m ^ 4 * θ ^ 2 - m ^ 2 * χb) ^ 3) * f θ ^ 2
      ≤ A * ∫ θ in α..β, f θ ^ 2 := by
    rw [← integral_const_mul]
    apply integral_mono_on hab _ (hI1.const_mul _)
    · intro θ hθ
      exact mul_le_mul_of_nonneg_right (hA θ hθ) (sq_nonneg _)
    · have hqbc : ContinuousOn (fun θ => c ^ 2 * m ^ 4 * θ ^ 2 - m ^ 2 * χb) (Icc α β) := by fun_prop
      have hne : ∀ θ ∈ Icc α β, c ^ 2 * m ^ 4 * θ ^ 2 - m ^ 2 * χb ≠ 0 := fun θ hθ => (hqb θ hθ).ne'
      have hp1 : ContinuousOn (fun θ : ℝ => 2 * (m ^ 2 * θ ^ 2 - 1)) (Icc α β) := by fun_prop
      have hn2 : ContinuousOn (fun θ : ℝ => (2 * c ^ 2 * m ^ 4 * θ) ^ 2) (Icc α β) := by fun_prop
      have h1 : ContinuousOn (fun θ : ℝ => (Real.pi / h) ^ 2 / (c ^ 2 * m ^ 4 * θ ^ 2 - m ^ 2 * χb))
          (Icc α β) := continuousOn_const.div hqbc hne
      have h2 : ContinuousOn (fun θ : ℝ => (2 * c ^ 2 * m ^ 4 * θ) ^ 2
          / (c ^ 2 * m ^ 4 * θ ^ 2 - m ^ 2 * χb) ^ 3) (Icc α β) :=
        hn2.div (hqbc.pow 3) fun θ hθ => pow_ne_zero 3 (hne θ hθ)
      have hall : ContinuousOn (fun θ : ℝ => 2 * (m ^ 2 * θ ^ 2 - 1)
          * ((Real.pi / h) ^ 2 / (c ^ 2 * m ^ 4 * θ ^ 2 - m ^ 2 * χb)
            + (2 * c ^ 2 * m ^ 4 * θ) ^ 2 / (c ^ 2 * m ^ 4 * θ ^ 2 - m ^ 2 * χb) ^ 3) * f θ ^ 2)
          (Icc α β) := (hp1.mul (h1.add h2)).mul (hfc.pow 2).continuousOn
      exact hall.intervalIntegrable_of_Icc hab
  have hS : ∫ θ in α..β, bump α β h θ / qb θ * (qb θ * f θ ^ 2 - f θ * r θ)
      ≤ (1 + δ / 2) * (∫ θ in α..β, f θ ^ 2) + B / (2 * δ) * ∫ θ in α..β, r θ ^ 2 := by
    have hpt : ∀ θ ∈ Icc α β, bump α β h θ / qb θ * (qb θ * f θ ^ 2 - f θ * r θ)
        ≤ (1 + δ / 2) * f θ ^ 2 + B / (2 * δ) * r θ ^ 2 := by
      intro θ hθ
      have hQ := hqb θ hθ
      have hb0 := bump_nonneg α β h θ
      have hb1 := bump_le_one α β h θ
      have hBθ := hB θ hθ
      -- `(b/Q)(Q f² − f r) = b f² − b f r/Q ≤ f² + |f r|/Q ≤ f² + (δ/2) f² + (1/2δ) r²/Q²`
      have hQne : qb θ ≠ 0 := hQ.ne'
      have e : bump α β h θ / qb θ * (qb θ * f θ ^ 2 - f θ * r θ)
          = bump α β h θ * f θ ^ 2 - bump α β h θ * (f θ * (r θ / qb θ)) := by
        field_simp
      rw [e]
      have h1 : bump α β h θ * f θ ^ 2 ≤ f θ ^ 2 := mul_le_of_le_one_left (sq_nonneg _) hb1
      have h2 : -(f θ * (r θ / qb θ)) ≤ δ / 2 * f θ ^ 2 + 1 / (2 * δ) * (r θ / qb θ) ^ 2 := by
        have := sq_nonneg (δ * f θ + r θ / qb θ)
        have e2 : (δ * f θ + r θ / qb θ) ^ 2 / δ
            = 2 * (δ / 2 * f θ ^ 2 + 1 / (2 * δ) * (r θ / qb θ) ^ 2) + 2 * (f θ * (r θ / qb θ)) := by
          field_simp; ring
        have : 0 ≤ (δ * f θ + r θ / qb θ) ^ 2 / δ := by positivity
        linarith
      have h3 : (r θ / qb θ) ^ 2 ≤ B * r θ ^ 2 := by
        rw [div_pow]
        have : r θ ^ 2 / qb θ ^ 2 = 1 / qb θ ^ 2 * r θ ^ 2 := by ring
        rw [this]
        exact mul_le_mul_of_nonneg_right (by simpa only [hqbdef] using hBθ) (sq_nonneg _)
      have h4 : -(bump α β h θ * (f θ * (r θ / qb θ))) ≤ bump α β h θ * (δ / 2 * f θ ^ 2 + 1 / (2 * δ) * (r θ / qb θ) ^ 2) := by
        rw [← mul_neg]; exact mul_le_mul_of_nonneg_left h2 hb0
      have h5 : bump α β h θ * (δ / 2 * f θ ^ 2 + 1 / (2 * δ) * (r θ / qb θ) ^ 2)
          ≤ δ / 2 * f θ ^ 2 + 1 / (2 * δ) * (r θ / qb θ) ^ 2 := mul_le_of_le_one_left (by positivity) hb1
      have h6 : 1 / (2 * δ) * (r θ / qb θ) ^ 2 ≤ 1 / (2 * δ) * (B * r θ ^ 2) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
      have e3 : 1 / (2 * δ) * (B * r θ ^ 2) = B / (2 * δ) * r θ ^ 2 := by ring
      linarith
    have hbc : Continuous (bump α β h) := continuous_iff_continuousAt.mpr fun θ => (hasDerivAt_bump hh θ).continuousAt
    have hqbc : ContinuousOn qb (Icc α β) := by simp only [hqbdef]; fun_prop
    have hne : ∀ θ ∈ Icc α β, qb θ ≠ 0 := fun θ hθ => (hqb θ hθ).ne'
    have hIL : IntervalIntegrable (fun θ => bump α β h θ / qb θ * (qb θ * f θ ^ 2 - f θ * r θ)) MeasureTheory.volume α β :=
      ((hbc.continuousOn.div hqbc hne).mul ((hqbc.mul (hfc.pow 2).continuousOn).sub
        (hfc.continuousOn.mul hrc.continuousOn))).intervalIntegrable_of_Icc hab
    have := integral_mono_on hab hIL ((hI1.const_mul _).add (hI2.const_mul _)) hpt
    rwa [integral_add (hI1.const_mul _) (hI2.const_mul _), integral_const_mul, integral_const_mul] at this
  -- assemble
  have hsum := hV.trans (add_le_add (mul_le_mul_of_nonneg_left hW (by positivity)) hS)
  have hleft : (1 - ε / 2) * ∫ θ in (α + h)..(β - h),
      (m * Gk a χ u k (m * θ)) ^ 2 / ((m ^ 2 * θ ^ 2 - 1) * (c ^ 2 * m ^ 4 * θ ^ 2 - m ^ 2 * χb))
      ≤ (1 - ε / 2) * ∫ θ in α..β, bump α β h θ / (c ^ 2 * m ^ 4 * θ ^ 2 - m ^ 2 * χb)
          * ((m * Gk a χ u k (m * θ)) ^ 2 / (m ^ 2 * θ ^ 2 - 1)) :=
    mul_le_mul_of_nonneg_left hinner (by linarith)
  calc (1 - ε / 2) * ∫ θ in (α + h)..(β - h),
        (m * Gk a χ u k (m * θ)) ^ 2 / ((m ^ 2 * θ ^ 2 - 1) * (c ^ 2 * m ^ 4 * θ ^ 2 - m ^ 2 * χb))
      ≤ _ := hleft
    _ ≤ 1 / (2 * ε) * (A * ∫ θ in α..β, f θ ^ 2)
          + ((1 + δ / 2) * (∫ θ in α..β, f θ ^ 2) + B / (2 * δ) * ∫ θ in α..β, r θ ^ 2) := hsum
    _ ≤ 1 / (2 * ε) * (A * (1 / m * ∑ i, (a i * χ i ^ k) ^ 2 * Mm i))
          + ((1 + δ / 2) * (1 / m * ∑ i, (a i * χ i ^ k) ^ 2 * Mm i)
            + B / (2 * δ) * (1 / m * ∑ i, (m ^ 2 * (a i * χ i ^ k * (χ i - χb))) ^ 2 * Mm i)) := by
        have hA0 : 0 ≤ A := by
          have := hA α ⟨le_rfl, hab⟩
          have hP := hp α ⟨le_rfl, hab⟩; have hQ := hqb α ⟨le_rfl, hab⟩
          exact le_trans (by positivity) this
        have hB0 : 0 ≤ B := le_trans (by positivity) (hB α ⟨le_rfl, hab⟩)
        gcongr
    _ = _ := by
        have e : ∑ i, (m ^ 2 * (a i * χ i ^ k * (χ i - χb))) ^ 2 * Mm i
            = m ^ 4 * ∑ i, (a i * χ i ^ k * (χ i - χb)) ^ 2 * Mm i := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
        rw [e]; field_simp; ring

end Cvs.L2a.DilatedVNormMasses
