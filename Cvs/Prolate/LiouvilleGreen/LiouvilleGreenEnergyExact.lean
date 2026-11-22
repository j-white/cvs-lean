import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The Liouville–Green energy of a Sturm–Liouville solution, exactly

For `ψ' = u/p`, `u' = −qψ` (that is `(pψ')' + qψ = 0`), `a > 0` with `a² = pq` and `a' = w q`, the energy
`G = aψ² + u²/a` satisfies `G' = −w (ψu)'`, so `(G + wψu)' = w'ψu`, and `2|ψu| ≤ G`. Integrated, `G` moves
by at most the edge terms `|w|G/2` and `∫|w'|G/2`: the amplitude invariance behind WKB, with its error.
-/

namespace Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact

open intervalIntegral

variable {ψ u p q a w w' : ℝ → ℝ}

/-- The Liouville–Green energy `aψ² + u²/a`. -/
noncomputable def energy (a ψ u : ℝ → ℝ) (t : ℝ) : ℝ := a t * ψ t ^ 2 + u t ^ 2 / a t

/-- **`2|ψu| ≤ G`** for `a > 0`. -/
theorem two_mul_abs_le_energy {t : ℝ} (ha : 0 < a t) : 2 * |ψ t * u t| ≤ energy a ψ u t := by
  unfold energy
  have key : 0 ≤ (a t * |ψ t| - |u t|) ^ 2 / a t := div_nonneg (sq_nonneg _) ha.le
  have e : (a t * |ψ t| - |u t|) ^ 2 / a t = a t * ψ t ^ 2 + u t ^ 2 / a t - 2 * |ψ t * u t| := by
    rw [abs_mul]
    field_simp
    rw [sub_sq, mul_pow, sq_abs, sq_abs]
    ring
  linarith

/-- **The energy identity**: `(G + wψu)' = w'ψu` at every point where the system holds. -/
theorem hasDerivAt_energy_add {t : ℝ} (ha : 0 < a t) (hp : p t ≠ 0) (hapq : a t ^ 2 = p t * q t)
    (hψ : HasDerivAt ψ (u t / p t) t) (hu : HasDerivAt u (-(q t * ψ t)) t)
    (haw : HasDerivAt a (w t * q t) t) (hw : HasDerivAt w (w' t) t) :
    HasDerivAt (fun s => energy a ψ u s + w s * (ψ s * u s)) (w' t * (ψ t * u t)) t := by
  have h1 := haw.fun_mul (hψ.fun_mul hψ)
  have h2 := (hu.fun_mul hu).fun_div haw ha.ne'
  have hc := hw.fun_mul (hψ.fun_mul hu)
  have hsum := (h1.fun_add h2).fun_add hc
  have hf : (fun s => energy a ψ u s + w s * (ψ s * u s))
      = fun s => a s * (ψ s * ψ s) + u s * u s / a s + w s * (ψ s * u s) := by
    funext s; unfold energy; ring
  rw [hf]
  refine hsum.congr_deriv ?_
  have hq : q t = a t ^ 2 / p t := by rw [hapq]; field_simp
  rw [hq]
  field_simp
  ring

/-- **The energy moves by `∫ w'ψu`**: `G t₁ + wψu(t₁) − (G t₀ + wψu(t₀)) = ∫_{t₀}^{t₁} w'ψu`. -/
theorem energy_add_sub_eq {t₀ t₁ : ℝ}
    (ha : ∀ t ∈ Set.uIcc t₀ t₁, 0 < a t) (hp : ∀ t ∈ Set.uIcc t₀ t₁, p t ≠ 0)
    (hapq : ∀ t ∈ Set.uIcc t₀ t₁, a t ^ 2 = p t * q t)
    (hψ : ∀ t ∈ Set.uIcc t₀ t₁, HasDerivAt ψ (u t / p t) t)
    (hu : ∀ t ∈ Set.uIcc t₀ t₁, HasDerivAt u (-(q t * ψ t)) t)
    (haw : ∀ t ∈ Set.uIcc t₀ t₁, HasDerivAt a (w t * q t) t)
    (hw : ∀ t ∈ Set.uIcc t₀ t₁, HasDerivAt w (w' t) t)
    (hint : IntervalIntegrable (fun t => w' t * (ψ t * u t)) MeasureTheory.volume t₀ t₁) :
    energy a ψ u t₁ + w t₁ * (ψ t₁ * u t₁) - (energy a ψ u t₀ + w t₀ * (ψ t₀ * u t₀))
      = ∫ t in t₀..t₁, w' t * (ψ t * u t) := by
  rw [integral_eq_sub_of_hasDerivAt (fun t ht => hasDerivAt_energy_add (ha t ht) (hp t ht)
    (hapq t ht) (hψ t ht) (hu t ht) (haw t ht) (hw t ht)) hint]

/-- **One-sided control of the energy**: for `t₀ ≤ t₁`, under `energy_add_sub_eq`'s hypotheses,
`G t₁ ≤ G t₀ + |w t₀| G t₀ / 2 + |w t₁| G t₁ / 2 + ∫_{t₀}^{t₁} |w'| G / 2`. -/
theorem energy_le {t₀ t₁ : ℝ} (hle : t₀ ≤ t₁)
    (ha : ∀ t ∈ Set.uIcc t₀ t₁, 0 < a t) (hp : ∀ t ∈ Set.uIcc t₀ t₁, p t ≠ 0)
    (hapq : ∀ t ∈ Set.uIcc t₀ t₁, a t ^ 2 = p t * q t)
    (hψ : ∀ t ∈ Set.uIcc t₀ t₁, HasDerivAt ψ (u t / p t) t)
    (hu : ∀ t ∈ Set.uIcc t₀ t₁, HasDerivAt u (-(q t * ψ t)) t)
    (haw : ∀ t ∈ Set.uIcc t₀ t₁, HasDerivAt a (w t * q t) t)
    (hw : ∀ t ∈ Set.uIcc t₀ t₁, HasDerivAt w (w' t) t)
    (hint : IntervalIntegrable (fun t => w' t * (ψ t * u t)) MeasureTheory.volume t₀ t₁)
    (hint' : IntervalIntegrable (fun t => |w' t| * energy a ψ u t / 2) MeasureTheory.volume t₀ t₁) :
    energy a ψ u t₁ ≤ energy a ψ u t₀ + |w t₀| * energy a ψ u t₀ / 2
      + |w t₁| * energy a ψ u t₁ / 2 + ∫ t in t₀..t₁, |w' t| * energy a ψ u t / 2 := by
  have heq := energy_add_sub_eq ha hp hapq hψ hu haw hw hint
  have hmem0 : t₀ ∈ Set.uIcc t₀ t₁ := Set.left_mem_uIcc
  have hmem1 : t₁ ∈ Set.uIcc t₀ t₁ := Set.right_mem_uIcc
  have edge : ∀ t ∈ Set.uIcc t₀ t₁, |w t * (ψ t * u t)| ≤ |w t| * energy a ψ u t / 2 := by
    intro t ht
    rw [abs_mul]
    have := two_mul_abs_le_energy (ψ := ψ) (u := u) (ha t ht)
    nlinarith [abs_nonneg (w t)]
  have hmono : ∫ t in t₀..t₁, w' t * (ψ t * u t) ≤ ∫ t in t₀..t₁, |w' t| * energy a ψ u t / 2 := by
    apply integral_mono_on hle hint hint'
    intro t ht
    have ht' : t ∈ Set.uIcc t₀ t₁ := by rw [Set.uIcc_of_le hle]; exact ht
    have := two_mul_abs_le_energy (ψ := ψ) (u := u) (ha t ht')
    calc w' t * (ψ t * u t) ≤ |w' t * (ψ t * u t)| := le_abs_self _
      _ = |w' t| * |ψ t * u t| := abs_mul _ _
      _ ≤ |w' t| * energy a ψ u t / 2 := by nlinarith [abs_nonneg (w' t)]
  have e0 := edge t₀ hmem0
  have e1 := edge t₁ hmem1
  have l0 := le_abs_self (w t₀ * (ψ t₀ * u t₀))
  have l1 := neg_abs_le (w t₁ * (ψ t₁ * u t₁))
  linarith

end Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
