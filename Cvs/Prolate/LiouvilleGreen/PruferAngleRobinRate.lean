import Mathlib
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.RegularSolutionChiVariation
import Cvs.Prolate.RegularSolutionEdge
import Cvs.Prolate.TopRungDepthBound

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The Prüfer and energy angles at `t = ½`, and the exact Robin-node rate

For the solution `y = regSol (sqC c) σ` of `((1 − t²)y')' + (σ − c²t²)y = 0` regular at `1`, the Prüfer angle `θ` of
`(c y(½), y'(½))` has `θ_σ (c²y² + y'²) = (4c/3) ∫_{½}^1 y²`, the energy angle `ϑ` of `(√a₀ y, u/√a₀)` has
`ϑ_σ G₀ = N − yu/(2q₀)`, and `θ_σ G₀ = Γ(r, θ) N` exactly, with `Γ(r, θ) = r cos²θ + r⁻¹ sin²θ` and `r = 4a₀/(3c)`.
Here `q₀ = σ − c²/4`, `a₀ = √(¾ q₀)`, `G₀ = a₀y² + u²/a₀` and `N = ∫_{½}^1 y²`.
-/

noncomputable section

open Real Set Filter Topology intervalIntegral Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.Prolate.RegularSolutionEdge Cvs.Prolate.RegularSolutionChiVariation

namespace Cvs.Prolate.LiouvilleGreen.PruferAngleRobinRate

/-! ### The Robin factor -/

/-! ### Lemma 3.1: the two angles -/

/-! ### The derivative of an angle -/

/-- **The angle derivative**: if `Y cos ϑ = X sin ϑ` near `σ`, then `ϑ'(X² + Y²) = XY' − YX'` at `σ`. -/
theorem hasDerivAt_angle {X Y ϑ : ℝ → ℝ} {X' Y' ϑ' σ : ℝ} (hX : HasDerivAt X X' σ) (hY : HasDerivAt Y Y' σ)
    (hϑ : HasDerivAt ϑ ϑ' σ) (hrel : ∀ᶠ s in 𝓝 σ, Y s * cos (ϑ s) = X s * sin (ϑ s)) :
    ϑ' * (X σ ^ 2 + Y σ ^ 2) = X σ * Y' - Y σ * X' := by
  have hf := (hY.mul (hϑ.cos)).sub (hX.mul (hϑ.sin))
  have h0 : HasDerivAt (fun s => Y s * cos (ϑ s) - X s * sin (ϑ s)) 0 σ :=
    (hasDerivAt_const σ (0 : ℝ)).congr_of_eventuallyEq (hrel.mono fun s hs => by simp [hs])
  have e := hf.unique h0
  have e0 : Y σ * cos (ϑ σ) = X σ * sin (ϑ σ) := hrel.self_of_nhds
  have hp := sin_sq_add_cos_sq (ϑ σ)
  set R := X σ * cos (ϑ σ) + Y σ * sin (ϑ σ)
  have hX2 : X σ = R * cos (ϑ σ) := by
    simp only [R]; linear_combination (-X σ) * hp - sin (ϑ σ) * e0
  have hY2 : Y σ = R * sin (ϑ σ) := by
    simp only [R]; linear_combination (-Y σ) * hp + cos (ϑ σ) * e0
  have e' : Y' * cos (ϑ σ) - X' * sin (ϑ σ) = ϑ' * R := by
    simp only [R]; linear_combination e
  rw [hX2, hY2]
  linear_combination (-R) * e' + ϑ' * R ^ 2 * hp

/-! ### The regular solution at `t = ½` -/

variable {c σ : ℝ}

/-- `N(σ) = ∫_{½}^1 y²` for `y = regSol (sqC c) σ`. -/
def nodeMass (c σ : ℝ) : ℝ := ∫ t in (1 / 2 : ℝ)..1, regSol (sqC c) σ t ^ 2

/-- The energy `G₀ = a₀y² + U²/a₀` of `y = regSol (sqC c) σ` at `t = ½`, with `a = Cvs.Prolate.TopRungDepthBound.af` at `χ = σ`. -/
def energyHalf (c σ : ℝ) : ℝ :=
  Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact.energy (Cvs.Prolate.TopRungDepthBound.af c ((c ^ 2 - σ) / c)) (regSol (sqC c) σ) (regU (sqC c) σ) (1 / 2)

/-- `a(½) = √(¾(σ − c²/4))` at `χ = σ`. -/
theorem af_half (hc : c ≠ 0) : Cvs.Prolate.TopRungDepthBound.af c ((c ^ 2 - σ) / c) (1 / 2) = √(3 / 4 * (σ - c ^ 2 / 4)) := by
  unfold Cvs.Prolate.TopRungDepthBound.af Cvs.Prolate.TopRungDepthBound.qf; congr 1; field_simp; ring

/-- `y'(½) = −(4/3) U(½)`. -/
theorem regV_half (c σ : ℝ) : regV (sqC c) σ (1 / 2) = -(4 / 3) * regU (sqC c) σ (1 / 2) := by
  have h := pP_mul_regV (sqC c) σ (show (-1 : ℝ) < 1 / 2 by norm_num)
  unfold pP at h
  linarith

/-- **Lemma 1.1 (Christoffel–Green)**: `N = U ẏ − y U̇` at `½`, with `ẏ = ∂_σ y`, `U̇ = ∂_σ U`. -/
theorem nodeMass_eq (c σ : ℝ) : nodeMass c σ =
    regU (sqC c) σ (1 / 2) * regDot (sqC c) σ (1 / 2) - regSol (sqC c) σ (1 / 2) * regUDot (sqC c) σ (1 / 2) := by
  have h := mass_identity (sqC c) σ (show (-1 : ℝ) < 1 / 2 by norm_num)
  unfold nodeMass; rw [integral_symm]; linarith

/-- **The Prüfer rate**: for a differentiable Prüfer angle `θ` of `(c y(½), y'(½))`,
`θ_σ (c²y(½)² + y'(½)²) = (4c/3) N`. -/
theorem prufer_rate {θ : ℝ → ℝ} {θ' : ℝ} (hθ : HasDerivAt θ θ' σ)
    (hrel : ∀ᶠ s in 𝓝 σ, regV (sqC c) s (1 / 2) * cos (θ s) = c * regSol (sqC c) s (1 / 2) * sin (θ s)) :
    θ' * ((c * regSol (sqC c) σ (1 / 2)) ^ 2 + regV (sqC c) σ (1 / 2) ^ 2) = 4 * c / 3 * nodeMass c σ := by
  have hX := (hasDerivAt_regSol_regDot (sqC c) σ (1 / 2)).const_mul c
  have hY : HasDerivAt (fun s => regV (sqC c) s (1 / 2)) (-(4 / 3) * regUDot (sqC c) σ (1 / 2)) σ := by
    have := (hasDerivAt_regU_chi (sqC c) σ (show (-1 : ℝ) < 1 / 2 by norm_num)).const_mul (-(4 / 3 : ℝ))
    refine this.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
    exact regV_half c s
  have h := hasDerivAt_angle hX hY hθ hrel
  rw [h, nodeMass_eq, regV_half]
  ring

end Cvs.Prolate.LiouvilleGreen.PruferAngleRobinRate
