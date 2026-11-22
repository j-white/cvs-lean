import Mathlib
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.Approximant.SpineCouplingTailPairing
import Cvs.Approximant.SpineFormOwnTailPairing
import Cvs.Approximant.SpineSubspace
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.FullTailConvergence
import Cvs.L2a.ProlateFamilySpine
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Route.Visibility.EvenFirstCellProfile
import Cvs.Upstream.CoefficientFloorLinearBound
import Cvs.Xi.EImageWindowPoisson
import Cvs.Xi.OddWindowPoissonLeakage

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The even first cell in Poisson form

A relative perturbation `‖R b‖ ≤ η‖M b‖`, `η ≤ 1`, keeps a unit-coefficient floor `d j ≤ ‖M b‖` up to the factor
`1 − η`, so `CoefficientFloorLinearBound`'s coefficient bound applies to `κ‖M b + R b‖²`. On `θ ∈ (1/2, 1]`, where `⌊1/θ⌋₊ = 1`, Poisson
splits `EvenFirstCellProfile`'s even cell profile of a spine class as
`G + √x E_G = Σ_j b_j((1 + √λ_{2j})h_{2j} − α_j(1 + √λ₀)h₀) + √x(t_G − G(0)/(2xθ))`.
-/

noncomputable section

open Real Set MeasureTheory Filter Topology

namespace Cvs.Route.Visibility.EvenFirstCellPoisson
open Cvs.ZeroCounting

open Cvs.Xi.EImageWindowPoisson (eimage)
open Cvs.L2a.AngularProlateTailPositive (psi)
open Cvs.Prolate.EvenRungsByIndex (rung lamR)
open Cvs.Approximant.DeepIndexSpineSpan (spineG alpha)
open Cvs.Xi.OddWindowPoissonLeakage (leak)

section General

variable {E : Type*} [SeminormedAddCommGroup E]

/-- A relative perturbation `‖r‖ ≤ η‖m‖` costs at most the factor `1 − η`: `(1 − η)‖m‖ ≤ ‖m + r‖`. -/
theorem one_sub_mul_norm_le_norm_add {m r : E} {η : ℝ} (hr : ‖r‖ ≤ η * ‖m‖) :
    (1 - η) * ‖m‖ ≤ ‖m + r‖ := by
  have h := norm_sub_norm_le m (-r)
  rw [norm_neg, sub_neg_eq_add] at h
  linarith

/-- **A floor survives a relative perturbation**: if `d j² ≤ ‖M b‖²` whenever `b j = 1` and `‖R b‖ ≤ η‖M b‖` with
`η ≤ 1`, then `((1 − η) d j)² ≤ ‖M b + R b‖²` whenever `b j = 1`. -/
theorem floor_add_of_rel {V ι : Type*} {M R : V → E} {coef : V → ι → ℝ} {d : ι → ℝ} {η : ℝ} (hη1 : η ≤ 1)
    (hd : ∀ j b, coef b j = 1 → d j ^ 2 ≤ ‖M b‖ ^ 2) (hR : ∀ b, ‖R b‖ ≤ η * ‖M b‖) (j : ι) (b : V)
    (hb : coef b j = 1) : ((1 - η) * d j) ^ 2 ≤ ‖M b + R b‖ ^ 2 := by
  have h1 : 0 ≤ 1 - η := sub_nonneg.mpr hη1
  have h2 := one_sub_mul_norm_le_norm_add (hR b)
  calc ((1 - η) * d j) ^ 2 = (1 - η) ^ 2 * d j ^ 2 := by ring
    _ ≤ (1 - η) ^ 2 * ‖M b‖ ^ 2 := mul_le_mul_of_nonneg_left (hd j b hb) (sq_nonneg _)
    _ = ((1 - η) * ‖M b‖) ^ 2 := by ring
    _ ≤ ‖M b + R b‖ ^ 2 := pow_le_pow_left₀ (mul_nonneg h1 (norm_nonneg _)) h2 2

variable [NormedSpace ℝ E] {ι : Type*} [Fintype ι]

/-- **The coefficient bound under a relative perturbation**: for linear `M, R`, `κ > 0`, `η < 1`, `d j > 0`, a floor
`d j² ≤ ‖M b‖²` on `b j = 1` and `‖R b‖ ≤ η‖M b‖` give `|b j| ≤ √(κ‖M b + R b‖²)/√(κ((1 − η) d j)²)`. -/
theorem abs_coef_le_of_rel (M R : (ι → ℝ) →ₗ[ℝ] E) {d : ι → ℝ} {η κ : ℝ} (hκ : 0 < κ) (hη1 : η < 1)
    (hd0 : ∀ j, 0 < d j) (hd : ∀ j (b : ι → ℝ), b j = 1 → d j ^ 2 ≤ ‖M b‖ ^ 2)
    (hR : ∀ b, ‖R b‖ ≤ η * ‖M b‖) (b : ι → ℝ) (j : ι) :
    |b j| ≤ √(κ * ‖M b + R b‖ ^ 2) / √(κ * ((1 - η) * d j) ^ 2) := by
  refine Cvs.Upstream.CoefficientFloorLinearBound.abs_coef_le (F := fun b => κ * ‖M b + R b‖ ^ 2) (δ := fun j => κ * ((1 - η) * d j) ^ 2)
    (fun t b => ?_) (fun j => ?_) (fun j b hb => ?_) b j
  · simp only [map_smul, ← smul_add, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  · have : 0 < 1 - η := sub_pos.mpr hη1
    have := hd0 j
    positivity
  · exact mul_le_mul_of_nonneg_left (floor_add_of_rel hη1.le hd hR j b hb) hκ.le

end General

section Spine

/-- The even cell main profile `Σ_j b_j((1 + √λ_{2j})h_{2j} − α_j(1 + √λ₀)h₀)` at `c = 2πx`. -/
def cellMain (x : ℕ) (b : Cvs.Approximant.SpineSubspace.SF x → ℝ) (s : ℝ) : ℝ :=
  ∑ j, b j * ((1 + √(lamR (2 * π * x) (2 * (j : ℕ)))) * rung (2 * π * x) (2 * (j : ℕ)) s
    - alpha (2 * π * x) j * (1 + √(lamR (2 * π * x) 0)) * rung (2 * π * x) 0 s)

/-- The even cell remainder `t_G(θ) − G(0)/(2xθ)` of the spine profile at `c = 2πx`. -/
def cellRem (x : ℕ) (b : Cvs.Approximant.SpineSubspace.SF x → ℝ) (θ : ℝ) : ℝ :=
  leak (2 * π * x) (spineG (2 * π * x) b) θ - 1 / x * spineG (2 * π * x) b 0 / (2 * θ)

/-- **The main profile in prolate form**: on `[−1, 1]`, `G_b + √x·ψ_b = Σ_j b_j((1 + √λ_{2j})h_{2j}
− α_j(1 + √λ₀)h₀)`. -/
theorem spineG_add_psi {x : ℕ} (hx : 80 ≤ 2 * π * x) (b : Cvs.Approximant.SpineSubspace.SF x → ℝ) {s : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1) :
    spineG (2 * π * x) b s + psi (2 * π * x) (spineG (2 * π * x) b) s / √(1 / x) = cellMain x b s := by
  have hx0 : (0 : ℝ) < x := Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx
  have hsx : √(1 / (x : ℝ)) ≠ 0 := (sqrt_pos.mpr (one_div_pos.mpr hx0)).ne'
  have hev : ∀ i : Option (Cvs.Approximant.SpineSubspace.SF x), Even (Cvs.L2a.ProlateFamilySpine.kOf i) := by
    rintro (_ | j)
    · exact ⟨0, rfl⟩
    · exact even_two_mul _
  have h2 : ∀ i : Option (Cvs.Approximant.SpineSubspace.SF x),
      Cvs.L2a.ProlateFamilySpine.bOf (2 * π * x) b i * rung (2 * π * x) (Cvs.L2a.ProlateFamilySpine.kOf i) s
          + Cvs.L2a.ProlateFamilySpine.bOf (2 * π * x) b i * psi (2 * π * x) (rung (2 * π * x) (Cvs.L2a.ProlateFamilySpine.kOf i)) s / √(1 / x)
        = Cvs.L2a.ProlateFamilySpine.bOf (2 * π * x) b i
          * ((1 + √(lamR (2 * π * x) (Cvs.L2a.ProlateFamilySpine.kOf i))) * rung (2 * π * x) (Cvs.L2a.ProlateFamilySpine.kOf i) s) := by
    intro i
    rw [Cvs.Prolate.EvenRungsByIndex.psi_rung (Cvs.Xi.OddWindowPoissonLeakage.exists_level hx i) s hs,
      Cvs.Xi.OddWindowPoissonLeakage.sqrt_lamR_eq hx (Cvs.Xi.OddWindowPoissonLeakage.exists_level hx i) (hev i)]
    field_simp
  rw [← Cvs.L2a.ProlateFamilySpine.sum_option_eq_spineG (2 * π * x) b,
    Cvs.L2a.FullTailConvergence.psi_sum _ _ _ (fun i _ => Cvs.Approximant.DeepIndexSpineSpan.intervalIntegrable_rung (2 * π * x) _), Finset.sum_div,
    ← Finset.sum_add_distrib]
  simp only [h2]
  rw [Fintype.sum_option]
  simp only [Cvs.L2a.ProlateFamilySpine.bOf, Cvs.L2a.ProlateFamilySpine.kOf, Option.elim, cellMain]
  rw [neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- `⌊1/θ⌋₊ = 1` on `(1/2, 1]`. -/
theorem floor_inv_eq_one {θ : ℝ} (hθ : θ ∈ Ioc (1 / 2 : ℝ) 1) : ⌊1 / θ⌋₊ = 1 := by
  have hθ0 : 0 < θ := by linarith [hθ.1]
  rw [Nat.floor_eq_iff (by positivity)]
  constructor
  · rw [Nat.cast_one, le_div_iff₀ hθ0]; linarith [hθ.2]
  · rw [div_lt_iff₀ hθ0]; norm_num; linarith [hθ.1]

/-- **The even cell profile in Poisson form**: at `80 ≤ 2πx`, for `θ ∈ (1/2, 1]` off the lattice `x⁻¹ℕ`,
`G_b(θ) + E_{G_b}(θ)/√(1/x) = Σ_j b_j((1 + √λ_{2j})h_{2j}(θ) − α_j(1 + √λ₀)h₀(θ)) + √x(t_{G_b}(θ) − G_b(0)/(2xθ))`. -/
theorem cellProfile_eq {x : ℕ} (hx : 80 ≤ 2 * π * x) (b : Cvs.Approximant.SpineSubspace.SF x → ℝ) {θ : ℝ}
    (hθ : θ ∈ Ioc (1 / 2 : ℝ) 1) (hlat : ∀ k : ℕ, θ ≠ k * (1 / x)) :
    Cvs.Route.Visibility.EvenFirstCellProfile.cellProfile (1 / x) (spineG (2 * π * x) b) θ = cellMain x b θ + √x * cellRem x b θ := by
  have hc : (0 : ℝ) < 2 * π * x := by linarith
  have hx0 : (0 : ℝ) < x := Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx
  have hθ0 : 0 < θ := by linarith [hθ.1]
  have hsc := Cvs.Approximant.SpineFormOwnTailPairing.scale_inv hx
  obtain ⟨G₁, G₂, hg, hg₁, hg₂c, heven, hGi⟩ := Cvs.Approximant.SpineCouplingTailPairing.spine_profile_data hx (Cvs.Approximant.SpineSubspace.SF_lt x) b
  have hT := Cvs.Xi.OddWindowPoissonLeakage.tendsto_sum_psi hg hg₁ hg₂c heven hc hθ0 (by rw [hsc]; exact hlat)
  have hL := Cvs.Xi.OddWindowPoissonLeakage.leak_eq_of_tendsto hθ0 hT
  rw [floor_inv_eq_one hθ, Finset.Icc_self, Finset.sum_singleton, Nat.cast_one, one_mul, hsc, hGi] at hL
  have hmain := spineG_add_psi hx b (s := θ) ⟨by linarith [hθ.1], hθ.2⟩
  have hs : √(1 / (x : ℝ)) ≠ 0 := (sqrt_pos.mpr (one_div_pos.mpr hx0)).ne'
  have hsx : √(x : ℝ) = 1 / √(1 / (x : ℝ)) := by rw [sqrt_div' _ hx0.le, sqrt_one, one_div_one_div]
  have hE : eimage (1 / x) (spineG (2 * π * x) b) θ
      = psi (2 * π * x) (spineG (2 * π * x) b) θ + cellRem x b θ := by
    unfold cellRem
    rw [hL]
    ring
  rw [Cvs.Route.Visibility.EvenFirstCellProfile.cellProfile, hE, ← hmain, hsx]
  field_simp
  ring

/-- Almost everywhere on `(1/2, 1]`, the even cell profile is `cellMain + √x·cellRem`. -/
theorem cellProfile_ae_eq {x : ℕ} (hx : 80 ≤ 2 * π * x) (b : Cvs.Approximant.SpineSubspace.SF x → ℝ) :
    ∀ᵐ θ : ℝ, θ ∈ Ioc (1 / 2 : ℝ) 1 →
      Cvs.Route.Visibility.EvenFirstCellProfile.cellProfile (1 / x) (spineG (2 * π * x) b) θ = cellMain x b θ + √x * cellRem x b θ := by
  filter_upwards [Cvs.Xi.EImageWindowPoisson.ae_notMem_lattice (1 / (x : ℝ))] with θ hlat hθ
  exact cellProfile_eq hx b hθ hlat

/-- **The even first-cell energy in Poisson form**: `cellEnergy x b = (1/(2x))∫_{(1/2,1]} (cellMain + √x·cellRem)²`. -/
theorem cellEnergy_eq {x : ℕ} (hx : 80 ≤ 2 * π * x) (b : Cvs.Approximant.SpineSubspace.SF x → ℝ) :
    Cvs.Upstream.CoefficientFloorLinearBound.cellEnergy x b
      = 1 / (x : ℝ) / 2 * ∫ θ in Ioc (1 / 2 : ℝ) 1, (cellMain x b θ + √x * cellRem x b θ) ^ 2 := by
  unfold Cvs.Upstream.CoefficientFloorLinearBound.cellEnergy
  congr 1
  refine setIntegral_congr_ae measurableSet_Ioc ?_
  filter_upwards [cellProfile_ae_eq hx b] with θ h hθ
  rw [← h hθ, Cvs.Route.Visibility.EvenFirstCellProfile.cellProfile]

end Spine

end Cvs.Route.Visibility.EvenFirstCellPoisson
