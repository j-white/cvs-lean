import Mathlib
import Cvs.Prolate.ExteriorMassArcsineFinite
import Cvs.Prolate.ExteriorMassEdgeLayer
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The pole channel is negligible

For a radial solution with `u = (ξ² − 1)ψ'`, `ψ = −u'/q` gives `∫_t^Y ψφ = u(t)φ(t)/q(t) − u(Y)φ(Y)/q(Y) + ∫ u (φ/q)'`,
and `|u(t)| ≤ √(cG₀F)·t` past `ξ₀`; so `|∫F_X|, |∫F_X/θ| ≤ √(ξ₀ − 1)√T₁ + 5D`, `D = A/κ + 2c²A/κ²`, and
`2|∫F_X||∫F_X/θ| ≤ ρ T₁` with `ρ = 4(ξ₀ − 1) + 20000 F/(c²(π/2 L − e)) → 0`. For `h₀, h₄, h₈`:
`|2Π₊∫τ/θ| ≤ η(π/c)(1 − λ) ≤ η Σ_M T(M)/M` eventually.
-/

noncomputable section

open Real Set Filter Topology MeasureTheory
open Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.Prolate.ExteriorMassEdgeLayer Cvs.Prolate.ExteriorMassArcsineFinite

namespace Cvs.L2a.PoleChannelNegligible


/-! ### Elementary integrals -/

/-! ### The exterior flux `u = (ξ² − 1)ψ'` -/

section Exterior

variable {ψ v v' : ℝ → ℝ} {c χ : ℝ}

theorem qP_ge_sq (hχ0 : 0 ≤ χ) {s : ℝ} (hs : 1 ≤ s) : (c ^ 2 - χ) * s ^ 2 ≤ qP c χ s := by
  unfold qP; nlinarith [mul_nonneg hχ0 (by nlinarith : (0 : ℝ) ≤ s ^ 2 - 1)]

theorem qP_pos' (hχ0 : 0 ≤ χ) (hκ : 0 < c ^ 2 - χ) {s : ℝ} (hs : 1 ≤ s) : 0 < qP c χ s :=
  lt_of_lt_of_le (by positivity) (qP_ge_sq hχ0 hs)

variable (hψ : ∀ r ∈ Ici (1 : ℝ), HasDerivAt ψ (v r) r)
    (hv : ∀ r ∈ Ici (1 : ℝ), HasDerivAt v (v' r) r)
    (hode : ∀ r ∈ Ici (1 : ℝ), (r ^ 2 - 1) * v' r + 2 * r * v r + (c ^ 2 * r ^ 2 - χ) * ψ r = 0)
include hψ hv hode

end Exterior

/-! ### The edge layer and the truncated pole integrals -/

section Truncated

variable {ψ v v' : ℝ → ℝ} {c χ : ℝ}
    (hψ : ∀ r ∈ Ici (1 : ℝ), HasDerivAt ψ (v r) r)
    (hv : ∀ r ∈ Ici (1 : ℝ), HasDerivAt v (v' r) r)
    (hode : ∀ r ∈ Ici (1 : ℝ), (r ^ 2 - 1) * v' r + 2 * r * v r + (c ^ 2 * r ^ 2 - χ) * ψ r = 0)
    (hint : IntegrableOn (fun t => ψ t ^ 2) (Ioi 1))
include hψ hv hode hint

/-- **The exterior energy is bounded by the mass**: `G₀ ≤ 2cT₁/(π/2·L − e)`. -/
theorem enG_le_mass (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχ : χ < c ^ 2) {ξ₀ : ℝ} (h1 : 1 < ξ₀)
    (hW : wP c χ ξ₀ < 2) (hden : errE c χ ξ₀ < π / 2 * lowL c χ ξ₀) :
    enG c χ ψ v ξ₀ ≤ 2 * c * (∫ t in Ioi 1, ψ t ^ 2) / (π / 2 * lowL c χ ξ₀ - errE c χ ξ₀) := by
  obtain ⟨lo, -⟩ := tail_mass_bounds hψ hv hode hint hc hχ0 hχ h1 le_rfl hW
  set F := Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay.fac c χ ξ₀ with hFd
  set G₀ := enG c χ ψ v ξ₀ with hG₀
  have hF0 : 0 < F := fac_pos h1 hc hχ hW
  have hG0 : 0 ≤ G₀ := enG_nonneg h1 hc hχ
  have hq : 0 < qP c χ ξ₀ := qP_pos' hχ0 (by linarith) h1.le
  have hT : ∫ t in Ioi ξ₀, ψ t ^ 2 ≤ ∫ t in Ioi 1, ψ t ^ 2 :=
    setIntegral_mono_set hint (ae_of_all _ fun s => sq_nonneg _) (Eventually.of_forall (Ioi_subset_Ioi h1.le))
  have e1 : G₀ / F * arcsin (1 / ξ₀) / (2 * c) = G₀ / (2 * c) * (π / 2 * lowL c χ ξ₀) := by
    unfold lowL ellA; rw [← hFd]; field_simp
  have hfq := fac_div_qP_le hc hχ0 hχ h1.le hF0.le (ξ₀ := ξ₀)
  have he0 : 0 ≤ errE c χ ξ₀ := by unfold errE; positivity
  have he1 : errE c χ ξ₀ / ξ₀ ≤ errE c χ ξ₀ := div_le_self he0 h1.le
  have e2 : G₀ * F / (2 * qP c χ ξ₀) = G₀ / (2 * c) * (F * (c / qP c χ ξ₀)) := by field_simp
  have h2 : G₀ * F / (2 * qP c χ ξ₀) ≤ G₀ / (2 * c) * errE c χ ξ₀ := by
    rw [e2]; exact mul_le_mul_of_nonneg_left (hfq.trans he1) (by positivity)
  have hden' : 0 < π / 2 * lowL c χ ξ₀ - errE c χ ξ₀ := by linarith
  rw [le_div_iff₀ hden']
  have hk : G₀ / (2 * c) * (π / 2 * lowL c χ ξ₀ - errE c χ ξ₀) ≤ ∫ t in Ioi 1, ψ t ^ 2 := by
    rw [e1] at lo; nlinarith
  have e3 : G₀ * (π / 2 * lowL c χ ξ₀ - errE c χ ξ₀)
      = 2 * c * (G₀ / (2 * c) * (π / 2 * lowL c χ ξ₀ - errE c χ ξ₀)) := by field_simp
  rw [e3]
  exact mul_le_mul_of_nonneg_left hk (by positivity)

end Truncated

section Relative

variable {ψ v v' : ℝ → ℝ} {c χ : ℝ}
    (hψ : ∀ r ∈ Ici (1 : ℝ), HasDerivAt ψ (v r) r)
    (hv : ∀ r ∈ Ici (1 : ℝ), HasDerivAt v (v' r) r)
    (hode : ∀ r ∈ Ici (1 : ℝ), (r ^ 2 - 1) * v' r + 2 * r * v r + (c ^ 2 * r ^ 2 - χ) * ψ r = 0)
    (hint : IntegrableOn (fun t => ψ t ^ 2) (Ioi 1))
include hψ hv hode hint

end Relative

/-! ### Along `c → ∞` -/


/-! ### The rungs -/


end Cvs.L2a.PoleChannelNegligible
