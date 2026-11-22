import Mathlib
import Cvs.L2a.CutoffCrossTermsAsNodes
import Cvs.L2a.ExplicitCutoffTailFloor
import Cvs.L2a.ExplicitTreeBoundPlateau
import Cvs.L2a.ExplicitTreeBoundRamp
import Cvs.L2a.RungChiHierarchy
import Cvs.L2a.SpanTailFloorMassSum
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
# The span floor with the edge pieces against the first-mode square

The edge pieces `∫₁^{θ₀} G²` and `∫_{19/10}^{3M/2} G²` of the cutoff route are parts of `∫₁ᵇ G²` once `b ≥ 3M/2`,
so the loss `max(s, 5/(6s))` multiplies the first-mode square itself and not the mass sum `N₀`: from any first-mode
floor `L ≤ ∫₁ᵇ G²`, `∫₁ᵇ (G + T₂)² ≥ (1 − max(s, 5/(6s))) L − N₀ ((1/s) Σ_{m≠m'} T_m + 2 Σ_m T_f)`. A first-mode
floor with a loss of order one now leaves a positive constant.
-/

namespace Cvs.L2a.SpanFloorEdgePieces

open Real Set Finset intervalIntegral Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.RungChiHierarchy Cvs.Upstream.SineSquaredRamp Cvs.L2a.TailFloorFromPairNodes Cvs.L2a.ExplicitTreeBoundPlateau Cvs.L2a.ExplicitTreeBoundRamp Cvs.L2a.SpanTailFloorMassSum

variable {ι : Type} [Fintype ι] [DecidableEq ι]

set_option maxHeartbeats 800000 in
/-- **The span tail Gram floor with the edge pieces against the first-mode square**: for `b ≥ 3M/2`,
`∫₁ᵇ (G + T₂)² ≥ (1 − max(s, 5/(6s))) L − N₀ ((1/s) Σ_{m≠m'} T_m + 2 Σ_m T_f)` from any `L ≤ ∫₁ᵇ G²`. -/
theorem span_floor_of_low' {c χb χm Sp h h₂ hη b s ε δ μ₁ μ₂ L : ℝ} {M : ℕ} {a χ Mm Kψ Ku : ι → ℝ}
    {ψ u : ι → ℝ → ℝ} (K : ι → ι → ℝ) (N : ℕ)
    (hM : 2 ≤ M) (hc : 0 < c) (hs : 0 < s) (hsmax : max s (5 / (6 * s)) ≤ 1) (hh : 0 < h) (hh' : h ≤ 1 / 4) (hh₂ : 0 < h₂) (hh₂' : h₂ ≤ 1 / 20)
    (hη0 : 0 < hη) (hη' : 4 / 3 + hη ≤ 3 / 2 - h₂) (hb : 2 ≤ b) (hbM : 3 * M / 2 ≤ b)
    (hχb : χb < c ^ 2 * (19 / 20 - h) ^ 2) (hχb0 : 0 ≤ χb)
    (hχ : ∀ i, 0 ≤ χ i ∧ χ i ≤ χm) (hχm : 0 < χm) (hMm : ∀ i, 0 < Mm i) (hS : ∀ i, |χ i - χb| ≤ Sp)
    (hε : 0 < ε) (hε2 : ε < 2) (hδ : 0 < δ) (hμ₁ : 0 < μ₁) (hμ₂ : 0 < μ₂)
    (hψ : ∀ i, ∀ ξ, 1 < ξ → HasDerivAt (ψ i) (u i ξ / pP ξ) ξ)
    (hu : ∀ i, ∀ ξ, HasDerivAt (u i) (-(qP c (χ i) ξ * ψ i ξ)) ξ)
    (hψc : ∀ i, Continuous (ψ i)) (huc : ∀ i, Continuous (u i))
    (hcross : ∀ i j, i ≠ j → ∀ t, 1 ≤ t → |∫ ξ in (1 : ℝ)..t, ψ i ξ * ψ j ξ| ≤ K i j / t)
    (hmass : ∀ i, ∀ t, 1 ≤ t → ∫ ξ in (1 : ℝ)..t, ψ i ξ ^ 2 ≤ Mm i)
    (hL : L ≤ ∫ ξ in (1 : ℝ)..b, (∑ i, a i * ψ i ξ) ^ 2)
    (hψK : ∀ i, ∀ ξ, 1 ≤ ξ → |ψ i ξ| ≤ Kψ i / ξ) (huK : ∀ i, ∀ ξ, 1 ≤ ξ → |u i ξ| ≤ Ku i * ξ)
    (hN₀ : 0 < ∑ i, a i ^ 2 * Mm i) :
    (1 - max s (5 / (6 * s))) * L - (∑ i, a i ^ 2 * Mm i)
          * (1 / s * ∑ m ∈ Finset.Icc 2 M, ∑ m' ∈ Finset.Icc 2 M,
                (if m = m' then 0 else Tsym (fun m m' => Tm c m m' χb χm Sp h h₂ ε δ μ₁ μ₂ N) m m')
            + 2 * ∑ m ∈ Finset.Icc 2 M,
                Tf c m χb χm Sp h hη b ε δ μ₁ μ₂ (∑ i, Kψ i ^ 2 / Mm i) (∑ i, Ku i ^ 2 / Mm i) N)
      ≤ ∫ θ in (1 : ℝ)..b, (Gk a χ ψ 0 θ + ∑ m ∈ Finset.Icc 2 M, Gk a χ ψ 0 (m * θ)) ^ 2 := by
  have hfloor := Cvs.L2a.ExplicitCutoffTailFloor.tail_floor_explicit (a := a) (χ := χ) (Mm := Mm) (Kψ := Kψ) (Ku := Ku)
    (ψ := ψ) (u := u) K N hM hc hs hh hh' hh₂ hh₂' hη0 hη' hb hχb hχb0 hχ hχm hMm hS hε hε2 hδ hμ₁ hμ₂ hψ hu hψc huc
    hcross hmass hψK huK hN₀
  set N₀ := ∑ i, a i ^ 2 * Mm i with hN₀def
  set G := Gk a χ ψ 0 with hG
  have hGc : Continuous G := by
    rw [hG]; unfold Gk; exact continuous_finsetSum _ fun i _ => continuous_const.mul (hψc i)
  have hcont : ∀ i, ContinuousOn (ψ i) (Ici 1) := fun i => (hψc i).continuousOn
  -- the first-mode norm from below: the hypothesis
  have hlow : L ≤ ∫ ξ in (1 : ℝ)..b, G ξ ^ 2 := by
    have e : (fun ξ => G ξ ^ 2) = fun ξ => (∑ i, a i * ψ i ξ) ^ 2 := by
      funext ξ; rw [hG, Cvs.L2a.CutoffCrossTermsAsNodes.Gk_zero]
    rw [e]; exact hL
  -- the two edge pieces from above (Cvs.Prolate.Gram.RungCombinationNormInterval)
  have hθ₀1 : (1 : ℝ) ≤ 4 / 3 + hη := by linarith
  have hedge := edge_sq_le (G := G) (η := ramp (4 / 3) hη) (θ₀ := 4 / 3 + hη) (b := b) hθ₀1 (by linarith) hGc
    (Cvs.Upstream.SineSquaredBump.continuous_ramp hη0) (fun θ => ramp_nonneg _ _ _) (fun θ => ramp_le_one _ _ _)
    (fun θ hθ => ramp_of_ge hη0 hθ.1)
  -- the two edge pieces are parts of the first-mode square on `[1, b]`
  have hM' : (2:ℝ) ≤ M := by exact_mod_cast hM
  have hI : ∀ s t : ℝ, IntervalIntegrable (fun ξ => G ξ ^ 2) MeasureTheory.volume s t := fun s t =>
    (hGc.pow 2).intervalIntegrable s t
  have hpieces : (∫ ξ in (1 : ℝ)..(4 / 3 + hη), G ξ ^ 2) + ∫ v in (19 / 10 : ℝ)..(3 * M / 2), G v ^ 2
      ≤ ∫ ξ in (1 : ℝ)..b, G ξ ^ 2 := by
    have h1 : (4 / 3 + hη : ℝ) ≤ 19 / 10 := by linarith
    have h2 : (19 / 10 : ℝ) ≤ 3 * M / 2 := by linarith
    rw [← integral_add_adjacent_intervals (hI 1 (4 / 3 + hη)) (hI (4 / 3 + hη) b),
      ← integral_add_adjacent_intervals (hI (4 / 3 + hη) (19 / 10)) (hI (19 / 10) b),
      ← integral_add_adjacent_intervals (hI (19 / 10) (3 * M / 2)) (hI (3 * M / 2) b)]
    have h3 : 0 ≤ ∫ ξ in (4 / 3 + hη : ℝ)..(19 / 10), G ξ ^ 2 := integral_nonneg h1 fun ξ _ => sq_nonneg _
    have h4 : 0 ≤ ∫ ξ in (3 * M / 2 : ℝ)..b, G ξ ^ 2 := integral_nonneg hbM fun ξ _ => sq_nonneg _
    linarith
  -- weights: `s X + (5/6s) Y ≤ max(s, 5/6s)(X + Y)`
  have hX : 0 ≤ ∫ ξ in (1 : ℝ)..(4 / 3 + hη), G ξ ^ 2 := integral_nonneg hθ₀1 fun ξ _ => sq_nonneg _
  have hY : 0 ≤ ∫ v in (19 / 10 : ℝ)..(3 * M / 2), G v ^ 2 := by
    have hM' : (2:ℝ) ≤ M := by exact_mod_cast hM
    exact integral_nonneg (by linarith) fun ξ _ => sq_nonneg _
  have hedge' : 0 ≤ ∫ θ in (1 : ℝ)..b, (1 - ramp (4 / 3) hη θ) ^ 2 * G θ ^ 2 :=
    integral_nonneg (by linarith) fun θ _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hmax1 : s ≤ max s (5 / (6 * s)) := le_max_left _ _
  have hmax2 : 5 / (6 * s) ≤ max s (5 / (6 * s)) := le_max_right _ _
  have hs' : 0 < 1 / s := by positivity
  have hcomb : s * (∫ θ in (1 : ℝ)..b, (1 - ramp (4 / 3) hη θ) ^ 2 * G θ ^ 2)
      + 1 / s * (5 / 6 * ∫ v in (19 / 10 : ℝ)..(3 * M / 2), G v ^ 2)
      ≤ max s (5 / (6 * s)) * ∫ ξ in (1 : ℝ)..b, G ξ ^ 2 := by
    have e1 : 1 / s * (5 / 6 * ∫ v in (19 / 10 : ℝ)..(3 * M / 2), G v ^ 2)
        = 5 / (6 * s) * ∫ v in (19 / 10 : ℝ)..(3 * M / 2), G v ^ 2 := by field_simp
    rw [e1]
    calc s * (∫ θ in (1 : ℝ)..b, (1 - ramp (4 / 3) hη θ) ^ 2 * G θ ^ 2)
          + 5 / (6 * s) * ∫ v in (19 / 10 : ℝ)..(3 * M / 2), G v ^ 2
        ≤ max s (5 / (6 * s)) * (∫ ξ in (1 : ℝ)..(4 / 3 + hη), G ξ ^ 2)
          + max s (5 / (6 * s)) * ∫ v in (19 / 10 : ℝ)..(3 * M / 2), G v ^ 2 := by
          have h1 : s * (∫ θ in (1 : ℝ)..b, (1 - ramp (4 / 3) hη θ) ^ 2 * G θ ^ 2)
              ≤ max s (5 / (6 * s)) * (∫ ξ in (1 : ℝ)..(4 / 3 + hη), G ξ ^ 2) :=
            mul_le_mul hmax1 hedge hedge' (by positivity)
          have h2 : 5 / (6 * s) * ∫ v in (19 / 10 : ℝ)..(3 * M / 2), G v ^ 2
              ≤ max s (5 / (6 * s)) * ∫ v in (19 / 10 : ℝ)..(3 * M / 2), G v ^ 2 :=
            mul_le_mul_of_nonneg_right hmax2 hY
          linarith
      _ = max s (5 / (6 * s)) * ((∫ ξ in (1 : ℝ)..(4 / 3 + hη), G ξ ^ 2)
          + ∫ v in (19 / 10 : ℝ)..(3 * M / 2), G v ^ 2) := by ring
      _ ≤ max s (5 / (6 * s)) * ∫ ξ in (1 : ℝ)..b, G ξ ^ 2 := mul_le_mul_of_nonneg_left hpieces (by positivity)
  -- assemble
  have e2 : 1 / s * (5 / 6 * (∫ v in (19 / 10 : ℝ)..(3 * M / 2), G v ^ 2)
      + N₀ * ∑ m ∈ Finset.Icc 2 M, ∑ m' ∈ Finset.Icc 2 M,
        (if m = m' then 0 else Tsym (fun m m' => Tm c m m' χb χm Sp h h₂ ε δ μ₁ μ₂ N) m m'))
      = 1 / s * (5 / 6 * ∫ v in (19 / 10 : ℝ)..(3 * M / 2), G v ^ 2)
        + N₀ * (1 / s * ∑ m ∈ Finset.Icc 2 M, ∑ m' ∈ Finset.Icc 2 M,
          (if m = m' then 0 else Tsym (fun m m' => Tm c m m' χb χm Sp h h₂ ε δ μ₁ μ₂ N) m m')) := by ring
  rw [e2] at hfloor
  have hLG : (1 - max s (5 / (6 * s))) * L ≤ (1 - max s (5 / (6 * s))) * ∫ ξ in (1 : ℝ)..b, G ξ ^ 2 :=
    mul_le_mul_of_nonneg_left hlow (by linarith)
  nlinarith [hfloor, hcomb, hLG]

end Cvs.L2a.SpanFloorEdgePieces
