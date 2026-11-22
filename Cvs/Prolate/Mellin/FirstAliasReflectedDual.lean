import Mathlib
import Cvs.Prolate.Mellin.FirstAliasProfileDual
import Cvs.Prolate.Mellin.HigherAliasRayTransforms
import Cvs.Prolate.Mellin.RayTransformEdgeSum
import Cvs.Upstream.RayTransformPowerSeries

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The first alias is the reflected dual minus a product of two transforms

For even series `H`, `C` on the closed unit disk, `T_W(w) = T_{rĤ}(w) − 2i T_H(w) T_{rC}(w)` on `Im w > 0`, where
`W(ζ) = ∫_{−1}^{1} H(tζ)C(t) dt`, `Ĥ(τ) = ∫_{−1}^{1} H(t)C(τt) dt` and `rF(ζ) = ζ⁻¹F(ζ⁻¹)`.
-/

noncomputable section

open Real Set MeasureTheory Filter Complex Topology
open Cvs.Prolate.Mellin.RayTransformEdgeSum (rayT)

namespace Cvs.Prolate.Mellin.FirstAliasReflectedDual
open Cvs.ZeroCounting

variable {b d : ℕ → ℂ} {H C : ℂ → ℂ}

/-- The reflection `rF(ζ) = ζ⁻¹F(ζ⁻¹)`. -/
def refl (F : ℂ → ℂ) (ζ : ℂ) : ℂ := ζ⁻¹ * F ζ⁻¹

theorem circle_inv (s : ℝ) : (Complex.exp (-(s * I)))⁻¹ = Complex.exp (s * I) := by
  rw [← Complex.exp_neg, neg_neg]

theorem norm_circle' (s : ℝ) : ‖Complex.exp (s * I)‖ = 1 := Complex.norm_exp_ofReal_mul_I s

/-- The reflection of an even series has the odd exponentials `e^{i(2l + 1)s}` on the circle. -/
theorem hasSum_refl {F : ℂ → ℂ} (hF : ∀ z : ℂ, ‖z‖ ≤ 1 → HasSum (fun l => d l * z ^ (2 * l)) (F z)) (s : ℝ) :
    HasSum (fun l => d l * Complex.exp (s * I) ^ (2 * l + 1)) (refl F (Complex.exp (-(s * I)))) := by
  unfold refl
  rw [circle_inv]
  have := (hF _ (norm_circle' s).le).mul_left (Complex.exp (s * I))
  refine this.congr_fun fun l => ?_
  ring

/-- `‖Σ_l d_l·2/(2j + 2l + 1)‖ ≤ 2Σ|d_l|`. -/
theorem norm_kernel_le (hd : Summable fun l => ‖d l‖) (j : ℕ) :
    ‖∑' l, d l * (2 / (2 * (j : ℂ) + 2 * l + 1))‖ ≤ 2 * ∑' l, ‖d l‖ := by
  have h3 : ∀ l : ℕ, ‖d l * (2 / (2 * (j : ℂ) + 2 * l + 1))‖ ≤ 2 * ‖d l‖ := fun l => by
    rw [norm_mul, norm_div, Complex.norm_ofNat]
    have : 1 ≤ ‖(2 * (j : ℂ) + 2 * l + 1)‖ := by
      have := Complex.abs_re_le_norm (2 * (j : ℂ) + 2 * l + 1)
      simp at this
      have h0 : (0 : ℝ) ≤ 2 * j + 2 * l := by positivity
      rw [abs_of_nonneg (by linarith)] at this; linarith
    calc ‖d l‖ * (2 / ‖(2 * (j : ℂ) + 2 * l + 1)‖) ≤ ‖d l‖ * (2 / 1) := by gcongr
      _ = 2 * ‖d l‖ := by ring
  have hs : Summable fun l => ‖d l * (2 / (2 * (j : ℂ) + 2 * l + 1))‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) h3 (hd.mul_left 2)
  calc ‖∑' l, d l * (2 / (2 * (j : ℂ) + 2 * l + 1))‖ ≤ ∑' l, ‖d l * (2 / (2 * (j : ℂ) + 2 * l + 1))‖ :=
        norm_tsum_le_tsum_norm hs
    _ ≤ ∑' l, 2 * ‖d l‖ := hs.tsum_le_tsum h3 (hd.mul_left 2)
    _ = 2 * ∑' l, ‖d l‖ := tsum_mul_left

theorem summable_mul_kernel (hb : Summable fun j => ‖b j‖) (hd : Summable fun l => ‖d l‖) :
    Summable fun j => ‖b j * ∑' l, d l * (2 / (2 * (j : ℂ) + 2 * l + 1))‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun j => by
    rw [norm_mul]; exact mul_le_mul_of_nonneg_left (norm_kernel_le hd j) (norm_nonneg _))
    (hb.mul_right _)

/-- **The first alias through the dual**: `T_W = T_{rĤ} − 2i T_H T_{rC}`. -/
theorem rayT_alias_eq (hb : Summable fun j => ‖b j‖) (hd : Summable fun l => ‖d l‖) (hHc : Continuous H)
    (hCc : Continuous C) (hH : ∀ z : ℂ, ‖z‖ ≤ 1 → HasSum (fun j => b j * z ^ (2 * j)) (H z))
    (hC : ∀ z : ℂ, ‖z‖ ≤ 1 → HasSum (fun l => d l * z ^ (2 * l)) (C z)) {w : ℂ} (hw : 0 < w.im) :
    rayT (fun ζ => ∫ t in (-1 : ℝ)..1, H (t * ζ) * C t) w
      = rayT (refl fun τ => ∫ t in (-1 : ℝ)..1, H t * C (τ * t)) w
        - 2 * I * rayT H w * rayT (refl C) w := by
  set cc : ℕ → ℂ := fun j => ∑' l, d l * (2 / (2 * j + 2 * l + 1)) with hcc
  set MM : ℕ → ℂ := fun l => ∑' j, b j * (2 / (2 * j + 2 * l + 1)) with hMM
  have hMMs : Summable fun l => ‖d l * MM l‖ := by
    have := summable_mul_kernel (b := d) (d := b) hd hb
    refine this.congr fun l => ?_
    simp only [hMM]
    refine congrArg (fun x => ‖d l * x‖) (tsum_congr fun j => ?_)
    ring_nf
  have hW := Cvs.Upstream.RayTransformPowerSeries.hasSum_rayT (b := fun j => b j * cc j) (summable_mul_kernel hb hd)
    (F := fun ζ => ∫ t in (-1 : ℝ)..1, H (t * ζ) * C t)
    (fun s => Cvs.Prolate.Mellin.FirstAliasProfileDual.hasSum_alias hb hd hCc hH hC (Cvs.Prolate.Mellin.HigherAliasRayTransforms.norm_circle s).le) hw
  have hHt := Cvs.Upstream.RayTransformPowerSeries.hasSum_rayT hb (fun s => hH _ (Cvs.Prolate.Mellin.HigherAliasRayTransforms.norm_circle s).le) hw
  have hCr := Cvs.Upstream.RayTransformPowerSeries.hasSum_rayT_refl hd (hasSum_refl hC) hw
  have hDr := Cvs.Upstream.RayTransformPowerSeries.hasSum_rayT_refl (b := fun l => d l * MM l) hMMs
    (G := refl fun τ => ∫ t in (-1 : ℝ)..1, H t * C (τ * t))
    (hasSum_refl (d := fun l => d l * MM l) (fun z hz => Cvs.Prolate.Mellin.FirstAliasProfileDual.hasSum_dual hb hd hHc hH hC hz)) hw
  set p : ℂ := 1 / 2 - w with hp
  have hpim : p.im ≠ 0 := by simp [hp]; linarith
  have e1 : ∀ j : ℕ, I / (w - (2 * j + 1 / 2)) = -I * (1 / (2 * j + p)) := fun j => by
    have : (2 * (j : ℂ) + p) ≠ 0 := fun h => hpim (by have := congrArg Complex.im h; simpa using this)
    rw [hp]
    have : w - (2 * j + 1 / 2) = -(2 * j + (1 / 2 - w)) := by ring
    rw [this]; field_simp
  have e2 : ∀ l : ℕ, I / (2 * l + 1 / 2 + w) = I * (1 / (2 * l + 1 - p)) := fun l => by
    rw [hp]; ring_nf
  rw [← hW.tsum_eq, ← hHt.tsum_eq, ← hCr.tsum_eq, ← hDr.tsum_eq]
  simp only [e1, e2]
  have key := Cvs.Prolate.Mellin.FirstAliasProfileDual.ml_identity hb hd hpim
  have hA : ∑' j, b j * cc j * (-I * (1 / (2 * (j : ℂ) + p))) = -I * ∑' j, b j * cc j / (2 * j + p) := by
    rw [← tsum_mul_left]; congr 1; funext j; ring
  have hB : ∑' j, b j * (-I * (1 / (2 * (j : ℂ) + p))) = -I * ∑' j, b j / (2 * j + p) := by
    rw [← tsum_mul_left]; congr 1; funext j; ring
  have hC' : ∑' l, d l * (I * (1 / (2 * (l : ℂ) + 1 - p))) = I * ∑' l, d l / (2 * l + 1 - p) := by
    rw [← tsum_mul_left]; congr 1; funext l; ring
  have hD : ∑' l, d l * MM l * (I * (1 / (2 * (l : ℂ) + 1 - p))) = I * ∑' l, d l * MM l / (2 * l + 1 - p) := by
    rw [← tsum_mul_left]; congr 1; funext l; ring
  rw [hA, hB, hC', hD, key]
  simp only [hMM]
  linear_combination (-2 * I * (∑' j, b j / (2 * (j : ℂ) + p)) * (∑' l, d l / (2 * (l : ℂ) + 1 - p)))
    * Complex.I_sq

end Cvs.Prolate.Mellin.FirstAliasReflectedDual

end
