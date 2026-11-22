import Mathlib
import Cvs.L2a.ExplicitTreeBoundPlateau
import Cvs.L2a.ExplicitTreeBoundRamp
import Cvs.L2a.RungChiHierarchy
import Cvs.L2a.TailFloorFromPairNodes
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Upstream.SineSquaredBump
import Cvs.Upstream.SineSquaredRamp

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The explicit tail floor of the cutoff route

With the plateau `bump (19/20) (3/2) h₂` and the ramp `ramp (4/3) h_η` as the weights, the floor of Cvs.L2a.TailFloorFromPairNodes holds with
the explicit pair bounds `T_m` (Cvs.L2a.ExplicitTreeBoundPlateau) and `T_f` (Cvs.L2a.ExplicitTreeBoundRamp): for `G = Σ a_iψ_i` and `T₂ = Σ_{m=2}^{M} G(m·)`,
`∫₁ᵇ (G + T₂)² ≥ ∫₁ᵇ G² − s∫ (1 − η)²G² − (1/s)[(5/6)∫_{19/10}^{3M/2} G² + N₀ Σ_{m≠m'} T_m] − 2N₀ Σ_m T_f`, every
constant explicit in `c, b, M, h, h₂, h_η, ε, δ, μ₁, μ₂, N`, the centre `χ̄`, the spread `Sp` and the rung sums.
-/

namespace Cvs.L2a.ExplicitCutoffTailFloor

open Real Set Finset Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.RungChiHierarchy Cvs.Upstream.SineSquaredRamp Cvs.Upstream.SineSquaredBump Cvs.L2a.TailFloorFromPairNodes Cvs.L2a.ExplicitTreeBoundPlateau Cvs.L2a.ExplicitTreeBoundRamp

variable {ι : Type} [Fintype ι] [DecidableEq ι]

set_option maxHeartbeats 800000 in
/-- **The explicit tail floor of the cutoff route.** -/
theorem tail_floor_explicit {c χb χm Sp h h₂ hη b s ε δ μ₁ μ₂ : ℝ} {M : ℕ} {a χ Mm Kψ Ku : ι → ℝ}
    {ψ u : ι → ℝ → ℝ} (K : ι → ι → ℝ) (N : ℕ)
    (hM : 2 ≤ M) (hc : 0 < c) (hs : 0 < s) (hh : 0 < h) (hh' : h ≤ 1 / 4) (hh₂ : 0 < h₂) (hh₂' : h₂ ≤ 1 / 20)
    (hη0 : 0 < hη) (hη' : 4 / 3 + hη ≤ 3 / 2 - h₂) (hb : 2 ≤ b)
    (hχb : χb < c ^ 2 * (19 / 20 - h) ^ 2) (hχb0 : 0 ≤ χb)
    (hχ : ∀ i, 0 ≤ χ i ∧ χ i ≤ χm) (hχm : 0 < χm) (hMm : ∀ i, 0 < Mm i) (hS : ∀ i, |χ i - χb| ≤ Sp)
    (hε : 0 < ε) (hε2 : ε < 2) (hδ : 0 < δ) (hμ₁ : 0 < μ₁) (hμ₂ : 0 < μ₂)
    (hψ : ∀ i, ∀ ξ, 1 < ξ → HasDerivAt (ψ i) (u i ξ / pP ξ) ξ)
    (hu : ∀ i, ∀ ξ, HasDerivAt (u i) (-(qP c (χ i) ξ * ψ i ξ)) ξ)
    (hψc : ∀ i, Continuous (ψ i)) (huc : ∀ i, Continuous (u i))
    (hcross : ∀ i j, i ≠ j → ∀ t, 1 ≤ t → |∫ ξ in (1 : ℝ)..t, ψ i ξ * ψ j ξ| ≤ K i j / t)
    (hmass : ∀ i, ∀ t, 1 ≤ t → ∫ ξ in (1 : ℝ)..t, ψ i ξ ^ 2 ≤ Mm i)
    (hψK : ∀ i, ∀ ξ, 1 ≤ ξ → |ψ i ξ| ≤ Kψ i / ξ) (huK : ∀ i, ∀ ξ, 1 ≤ ξ → |u i ξ| ≤ Ku i * ξ)
    (hN₀ : 0 < ∑ i, a i ^ 2 * Mm i) :
    (∫ θ in (1 : ℝ)..b, Gk a χ ψ 0 θ ^ 2) - s * (∫ θ in (1 : ℝ)..b, (1 - ramp (4 / 3) hη θ) ^ 2 * Gk a χ ψ 0 θ ^ 2)
        - 1 / s * (5 / 6 * (∫ v in (19 / 10 : ℝ)..(3 * M / 2), Gk a χ ψ 0 v ^ 2)
            + (∑ i, a i ^ 2 * Mm i) * ∑ m ∈ Finset.Icc 2 M, ∑ m' ∈ Finset.Icc 2 M,
              (if m = m' then 0 else Tsym (fun m m' => Tm c m m' χb χm Sp h h₂ ε δ μ₁ μ₂ N) m m'))
        - 2 * ((∑ i, a i ^ 2 * Mm i) * ∑ m ∈ Finset.Icc 2 M,
            Tf c m χb χm Sp h hη b ε δ μ₁ μ₂ (∑ i, Kψ i ^ 2 / Mm i) (∑ i, Ku i ^ 2 / Mm i) N)
      ≤ ∫ θ in (1 : ℝ)..b, (Gk a χ ψ 0 θ + ∑ m ∈ Finset.Icc 2 M, Gk a χ ψ 0 (m * θ)) ^ 2 := by
  have hbc : Continuous (bump (19 / 20) (3 / 2) h₂) :=
    continuous_iff_continuousAt.mpr fun θ => (hasDerivAt_bump hh₂ θ).continuousAt
  have hθ₀ : (4 / 3 : ℝ) + hη ≤ 3 / 2 := by linarith
  refine floor_of_pair_bounds (c := c) (θ₀ := 4 / 3 + hη) (b := b) (s := s) (M := M) (a := a) (χ := χ) (ψ := ψ)
    (η := ramp (4 / 3) hη) (σ := bump (19 / 20) (3 / 2) h₂) (N₀ := ∑ i, a i ^ 2 * Mm i)
    (T := fun m m' => Tm c m m' χb χm Sp h h₂ ε δ μ₁ μ₂ N)
    (T₁ := fun m => Tf c m χb χm Sp h hη b ε δ μ₁ μ₂ (∑ i, Kψ i ^ 2 / Mm i) (∑ i, Ku i ^ 2 / Mm i) N)
    hM (by linarith) hθ₀ (by linarith) hs hN₀.le hψc (continuous_ramp hη0) ?_ ?_ hbc ?_ ?_ ?_ ?_ ?_ ?_
  · intro θ hθ; exact ramp_of_le hθ.2
  · intro θ hθ; exact ramp_of_ge hη0 hθ.1
  · intro θ; exact bump_nonneg _ _ _ _
  · intro θ; exact bump_le_one _ _ _ _
  · intro θ hθ; exact bump_eq_one hh₂ (by linarith [hθ.1]) (by linarith [hθ.2])
  · intro θ hθ
    rcases hθ with h1 | h1
    · exact bump_of_le h1
    · exact bump_of_ge h1
  · intro m m' hm hmm' hm'M
    exact mode_pair_bound (a := a) (χ := χ) (Mm := Mm) (ψ := ψ) (u := u) K hm hmm' N hc hh (by linarith) hh₂ hχb hχb0 hχ hχm
      hMm hS hε hε2 hδ hμ₁ hμ₂ hψ hu hψc huc hcross hmass hN₀
  · intro m hm hmM
    exact first_pair_bound (a := a) (χ := χ) (Mm := Mm) (Kψ := Kψ) (Ku := Ku) (ψ := ψ) (u := u) K hm N hc hh hh' hη0 hb
      (by linarith) hχb hχb0 hχ hχm hMm hS hε hε2 hδ hμ₁ hμ₂ hψ hu hψc huc hcross hmass hψK huK hN₀

end Cvs.L2a.ExplicitCutoffTailFloor
