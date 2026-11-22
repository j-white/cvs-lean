import Mathlib
import Cvs.L2a.ProlateAdmixturePositive
import Cvs.L2a.TailLogScaleTest
import Cvs.L2a.TailModesPrimeSideBound
import Cvs.L2a.TailOfModes
import Cvs.WeilForm.PrimePowerIndexed
import Cvs.Zeta.PrimePowerSideTruncated
import Cvs.Zeta.WeilPositivityStatement

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The prime side of any tail, bounded by its norm alone

For every `F` vanishing on `(−∞, 1]` with `F²` integrable, `∫F(θ)F(kθ) ≤ ∫F²/√k` (Young at `s = √k`, then
`∫F(kθ)² = ∫F²/k`), so `primePowerSideTruncated ≤ (Σ_{k ∈ idx} 2Λ(k)/√k) ∫F²`, with no hypothesis on the shape of `F`:
for a tail of any combination of prolates the prime side is at most this multiple of the combination's own norm.
-/

namespace Cvs.L2a.TailPrimeSideByNorm

open Real Set MeasureTheory ArithmeticFunction Cvs.L2a.TailOfModes

variable {F : ℝ → ℝ}

/-- The dilation `θ ↦ kθ` is quasi-measure-preserving on `ℝ`. -/
theorem quasiMeasurePreserving_mul {k : ℝ} (hk : k ≠ 0) :
    QuasiMeasurePreserving (fun θ : ℝ => k * θ) volume volume :=
  ⟨(measurable_const_mul k).aemeasurable, by rw [Real.map_volume_mul_left hk]; exact Measure.smul_absolutelyContinuous⟩

/-- **`∫F(kθ)² = ∫F²/k`.** -/
theorem integral_dilate_sq {k : ℝ} (hk : 0 < k) : ∫ θ, F (k * θ) ^ 2 = k⁻¹ * ∫ θ, F θ ^ 2 := by
  have := MeasureTheory.Measure.integral_comp_mul_left (fun θ => F θ ^ 2) k
  simpa [abs_of_pos (inv_pos.mpr hk)] using this

/-- **Young at `s = √k`**: `∫F(θ)F(kθ) ≤ ∫F²/√k`. -/
theorem integral_mul_dilate_le {k : ℝ} (hk : 0 < k) (hFm : AEStronglyMeasurable F volume)
    (hF2 : Integrable (fun θ => F θ ^ 2) volume) :
    ∫ θ, F θ * F (k * θ) ≤ (∫ θ, F θ ^ 2) / √k := by
  have hsk : 0 < √k := sqrt_pos.mpr hk
  have hkm : AEStronglyMeasurable (fun θ => F (k * θ)) volume :=
    hFm.comp_quasiMeasurePreserving (quasiMeasurePreserving_mul hk.ne')
  have hFk2 : Integrable (fun θ => F (k * θ) ^ 2) volume := hF2.comp_mul_left' hk.ne'
  have hprod : Integrable (fun θ => F θ * F (k * θ)) volume := by
    refine Integrable.mono' ((hF2.add hFk2).const_mul (1 / 2)) (hFm.mul hkm) (Filter.Eventually.of_forall fun θ => ?_)
    show ‖F θ * F (k * θ)‖ ≤ 1 / 2 * (F θ ^ 2 + F (k * θ) ^ 2)
    rw [Real.norm_eq_abs, abs_mul]
    nlinarith [sq_nonneg (|F θ| - |F (k * θ)|), sq_abs (F θ), sq_abs (F (k * θ))]
  -- `2ab ≤ a²/s + s b²`, `s = √k`
  have hpt : ∀ θ, F θ * F (k * θ) ≤ 1 / 2 * (F θ ^ 2 / √k + √k * F (k * θ) ^ 2) := fun θ => by
    have h := sq_nonneg (F θ - √k * F (k * θ))
    have key : 2 * (F θ * F (k * θ)) * √k ≤ F θ ^ 2 + √k ^ 2 * F (k * θ) ^ 2 := by nlinarith [h]
    rw [show 1 / 2 * (F θ ^ 2 / √k + √k * F (k * θ) ^ 2) = (F θ ^ 2 + √k ^ 2 * F (k * θ) ^ 2) / (2 * √k) by
      field_simp]
    rw [le_div_iff₀ (by positivity)]
    linarith [key]
  have hint : Integrable (fun θ => 1 / 2 * (F θ ^ 2 / √k + √k * F (k * θ) ^ 2)) volume :=
    ((hF2.div_const _).add (hFk2.const_mul _)).const_mul _
  calc ∫ θ, F θ * F (k * θ) ≤ ∫ θ, 1 / 2 * (F θ ^ 2 / √k + √k * F (k * θ) ^ 2) := integral_mono hprod hint hpt
    _ = 1 / 2 * ((∫ θ, F θ ^ 2) / √k + √k * ∫ θ, F (k * θ) ^ 2) := by
        rw [integral_const_mul, integral_add (hF2.div_const _) (hFk2.const_mul _), integral_div, integral_const_mul]
    _ = (∫ θ, F θ ^ 2) / √k := by
        rw [integral_dilate_sq hk]
        have hk2 : √k ^ 2 = k := sq_sqrt hk.le
        have e : √k * k⁻¹ = (√k)⁻¹ := by field_simp; nlinarith [hk2]
        rw [show √k * (k⁻¹ * ∫ θ, F θ ^ 2) = (√k * k⁻¹) * ∫ θ, F θ ^ 2 by ring, e]
        ring

/-- Every prime power in the index is at least `1`. -/
theorem one_le_of_mem_primePowIndex {P R k : ℕ} (hk : k ∈ Cvs.WeilForm.PrimePowerIndexed.primePowIndex P R) : 1 ≤ k := by
  unfold Cvs.WeilForm.PrimePowerIndexed.primePowIndex at hk
  obtain ⟨⟨p, r⟩, hmem, rfl⟩ := Finset.mem_image.mp hk
  have hp : p.Prime := (Finset.mem_filter.mp (Finset.mem_product.mp hmem).1).2
  exact Nat.one_le_pow _ _ hp.pos

/-- **The prime side of any tail is at most `(Σ_{k ∈ idx} 2Λ(k)/√k)` times its norm.** -/
theorem primeSide_le_norm (hF0 : ∀ θ ≤ 1, F θ = 0) (hFm : AEStronglyMeasurable F volume)
    (hF2 : IntegrableOn (fun θ => F θ ^ 2) (Ioi 1)) (P R : ℕ) :
    Cvs.Zeta.Explicit.Weil.primePowerSideTruncated P R (Cvs.Zeta.Explicit.Weil.selfConvolution (Cvs.L2a.TailLogScaleTest.logScale F))
      ≤ (∑ k ∈ Cvs.WeilForm.PrimePowerIndexed.primePowIndex P R, 2 * Λ k / √(k : ℝ)) * ∫ θ in Ioi 1, F θ ^ 2 := by
  rw [Cvs.L2a.TailModesPrimeSideBound.primeSide_eq_image F hF0, Finset.sum_mul]
  have hzero : ∀ θ, θ ∉ Ioi (1 : ℝ) → F θ ^ 2 = 0 := fun θ hθ => by
    rw [hF0 θ (by simpa using hθ)]; ring
  have hF2' : Integrable (fun θ => F θ ^ 2) volume := hF2.integrable_of_forall_notMem_eq_zero hzero
  have hN : ∫ θ in Ioi 1, F θ ^ 2 = ∫ θ, F θ ^ 2 := setIntegral_eq_integral_of_forall_compl_eq_zero hzero
  apply Finset.sum_le_sum
  intro k hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast one_le_of_mem_primePowIndex hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hΛ : 0 ≤ Λ k := vonMangoldt_nonneg
  have hset : ∫ θ in Ioi 1, F θ * F (k * θ) = ∫ θ, F θ * F (k * θ) :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun θ hθ => by
      rw [hF0 θ (by simpa using hθ)]; ring
  rw [hset, hN]
  have h := integral_mul_dilate_le (F := F) hk0 hFm hF2'
  calc 2 * Λ k * ∫ θ, F θ * F (k * θ) ≤ 2 * Λ k * ((∫ θ, F θ ^ 2) / √(k : ℝ)) := by gcongr
    _ = 2 * Λ k / √(k : ℝ) * ∫ θ, F θ ^ 2 := by ring

/-- A tail of `M` modes of a function continuous on `[1, Mb]` is measurable. -/
theorem tailF_aestronglyMeasurable {ψ : ℝ → ℝ} {M : ℕ} {b : ℝ}
    (hcont : ContinuousOn ψ (Icc 1 (M * b))) : AEStronglyMeasurable (tailF ψ M b) volume := by
  unfold tailF
  rw [aestronglyMeasurable_indicator_iff measurableSet_Ioc]
  apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioc
  apply continuousOn_finsetSum; intro m hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
  have hmM : (m : ℝ) ≤ M := by exact_mod_cast (Finset.mem_Icc.mp hm).2
  exact hcont.comp (continuousOn_const.mul continuousOn_id) (fun θ hθ =>
    ⟨one_le_mul_of_one_le_of_one_le hm1 hθ.1.le,
      mul_le_mul hmM hθ.2 (show (0 : ℝ) ≤ θ by linarith [hθ.1]) (Nat.cast_nonneg M)⟩)

/-- **The prime side of the tail of `M` modes of any function continuous on `[1, Mb]`**, in particular of any
combination of prolates, is at most `(Σ_{k ∈ idx} 2Λ(k)/√k)` times the tail's norm. -/
theorem primeSide_tailF_le_norm {ψ : ℝ → ℝ} {M : ℕ} {b : ℝ}
    (hcont : ContinuousOn ψ (Icc 1 (M * b))) (P R : ℕ) :
    Cvs.Zeta.Explicit.Weil.primePowerSideTruncated P R
        (Cvs.Zeta.Explicit.Weil.selfConvolution (Cvs.L2a.TailLogScaleTest.logScale (tailF ψ M b)))
      ≤ (∑ k ∈ Cvs.WeilForm.PrimePowerIndexed.primePowIndex P R, 2 * Λ k / √(k : ℝ)) * ∫ θ in Ioi 1, tailF ψ M b θ ^ 2 :=
  primeSide_le_norm (tailF_zero ψ M b) (tailF_aestronglyMeasurable hcont)
    (Cvs.L2a.ProlateAdmixturePositive.tailF_sq_integrableOn hcont) P R

end Cvs.L2a.TailPrimeSideByNorm
