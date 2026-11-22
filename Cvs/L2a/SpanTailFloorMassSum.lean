import Mathlib
import Cvs.L2a.CutoffCrossTermsAsNodes
import Cvs.L2a.ExplicitCutoffTailFloor
import Cvs.L2a.ExplicitTreeBoundPlateau
import Cvs.L2a.ExplicitTreeBoundRamp
import Cvs.L2a.RungChiHierarchy
import Cvs.L2a.TailFloorFromPairNodes
import Cvs.Prolate.Gram.GramFloorTailOrthogonality
import Cvs.Prolate.Gram.RungCombinationNormInterval
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
# The span tail Gram floor against the mass sum

The two diagonal edge integrals of Cvs.L2a.ExplicitCutoffTailFloor live on the disjoint pieces `[1, θ₀]` and `[19/10, 3M/2]` of `[1, 3M/2]`,
so together they are at most `max(s, 5/6s) N₀` by orthogonality at infinity (Cvs.Prolate.Gram.RungCombinationNormInterval), and `∫₁ᵇ G²` is at least
`Σ a_i²(∫₁ᵇ ψ_i² − Σ_j T_j)` (Cvs.Prolate.Gram.GramFloorTailOrthogonality); hence `∫₁ᵇ (Σ_{m≤M} G(m·))² ≥ Σ a_i²(∫₁ᵇ ψ_i² − Σ_j T_j)
− N₀ (max(s, 5/6s) + (1/s)Σ_{m≠m'} T_m + 2Σ_m T_f)`: the tail Gram of the rung span, margin `1 − √(5/6)` at `s = √(5/6)`.
-/

namespace Cvs.L2a.SpanTailFloorMassSum

open Real Set Finset intervalIntegral Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.RungChiHierarchy Cvs.Upstream.SineSquaredRamp Cvs.L2a.TailFloorFromPairNodes Cvs.L2a.ExplicitTreeBoundPlateau Cvs.L2a.ExplicitTreeBoundRamp

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The edge square under `(1 − η)²` is at most the square on `[1, θ₀]`. -/
theorem edge_sq_le {G η : ℝ → ℝ} {θ₀ b : ℝ} (h1 : 1 ≤ θ₀) (hb : θ₀ ≤ b) (hGc : Continuous G) (hηc : Continuous η)
    (hη0 : ∀ θ, 0 ≤ η θ) (hη1 : ∀ θ, η θ ≤ 1) (hη : ∀ θ ∈ Icc θ₀ b, η θ = 1) :
    ∫ θ in (1 : ℝ)..b, (1 - η θ) ^ 2 * G θ ^ 2 ≤ ∫ θ in (1 : ℝ)..θ₀, G θ ^ 2 := by
  have hI : ∀ s t : ℝ, IntervalIntegrable (fun θ => (1 - η θ) ^ 2 * G θ ^ 2) MeasureTheory.volume s t := fun s t =>
    (((continuous_const.sub hηc).pow 2).mul (hGc.pow 2)).intervalIntegrable s t
  rw [← integral_add_adjacent_intervals (hI 1 θ₀) (hI θ₀ b)]
  have z : ∫ θ in θ₀..b, (1 - η θ) ^ 2 * G θ ^ 2 = ∫ θ in θ₀..b, (0 : ℝ) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun θ hθ => ?_)
    rw [uIoc_of_le hb] at hθ
    rw [hη θ ⟨hθ.1.le, hθ.2⟩]; ring
  rw [z, integral_zero, add_zero]
  apply integral_mono_on h1 (hI 1 θ₀) ((hGc.pow 2).intervalIntegrable 1 θ₀)
  intro θ _
  have : (1 - η θ) ^ 2 ≤ 1 := by
    have := hη0 θ; have := hη1 θ; nlinarith
  exact mul_le_of_le_one_left (sq_nonneg _) this

/-- **The two edge pieces against the mass sum**: `∫₁^{θ₀} G² + ∫_{19/10}^{3M/2} G² ≤ N₀` for `θ₀ ≤ 3/2`, `M ≥ 2`. -/
theorem edge_pieces_le {θ₀ : ℝ} {M : ℕ} {a : ι → ℝ} {ψ : ι → ℝ → ℝ} (K : ι → ι → ℝ) (Mm : ι → ℝ)
    (hθ₀ : θ₀ ≤ 3 / 2) (hM : 2 ≤ M) (hcont : ∀ i, ContinuousOn (ψ i) (Ici 1))
    (hψc : ∀ i, Continuous (ψ i))
    (hcross : ∀ i j, i ≠ j → ∀ t, 1 ≤ t → |∫ ξ in (1 : ℝ)..t, ψ i ξ * ψ j ξ| ≤ K i j / t)
    (hmass : ∀ i, ∀ t, 1 ≤ t → ∫ ξ in (1 : ℝ)..t, ψ i ξ ^ 2 ≤ Mm i) :
    (∫ θ in (1 : ℝ)..θ₀, (∑ i, a i * ψ i θ) ^ 2) + ∫ v in (19 / 10 : ℝ)..(3 * M / 2), (∑ i, a i * ψ i v) ^ 2
      ≤ ∑ i, a i ^ 2 * Mm i := by
  have hM' : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hGc : Continuous fun ξ => ∑ i, a i * ψ i ξ := continuous_finsetSum _ fun i _ => continuous_const.mul (hψc i)
  have hI : ∀ s t : ℝ, IntervalIntegrable (fun ξ => (∑ i, a i * ψ i ξ) ^ 2) MeasureTheory.volume s t := fun s t =>
    (hGc.pow 2).intervalIntegrable s t
  have hwhole := Cvs.Prolate.Gram.RungCombinationNormInterval.span_norm_le (lo := 1) (hi := 3 * M / 2) le_rfl (by linarith) ψ a K Mm hcont
    (fun i j hij t ht => hcross i j hij t (by linarith)) (fun i t ht => hmass i t (by linarith))
  have hsplit : ∫ ξ in (1 : ℝ)..(3 * M / 2), (∑ i, a i * ψ i ξ) ^ 2
      = (∫ ξ in (1 : ℝ)..θ₀, (∑ i, a i * ψ i ξ) ^ 2) + (∫ ξ in θ₀..(19 / 10), (∑ i, a i * ψ i ξ) ^ 2)
        + ∫ ξ in (19 / 10 : ℝ)..(3 * M / 2), (∑ i, a i * ψ i ξ) ^ 2 := by
    rw [integral_add_adjacent_intervals (hI 1 θ₀) (hI θ₀ (19 / 10)),
      integral_add_adjacent_intervals (hI 1 (19 / 10)) (hI (19 / 10) (3 * M / 2))]
  have hmid : 0 ≤ ∫ ξ in θ₀..(19 / 10), (∑ i, a i * ψ i ξ) ^ 2 :=
    integral_nonneg (by linarith) fun ξ _ => sq_nonneg _
  linarith

set_option maxHeartbeats 800000 in
/-- **The span tail Gram floor against the mass sum.** With `T_j` the tail bounds beyond `b` (Cvs.Prolate.Gram.GramFloorTailOrthogonality) and `N₀ = Σ a_i²M_i`,
`∫₁ᵇ (G + T₂)² ≥ Σ a_i²(∫₁ᵇ ψ_i² − Σ_j T_j) − N₀ (max(s, 5/(6s)) + (1/s) Σ_{m≠m'} T_m + 2 Σ_m T_f)`. -/
theorem span_floor {c χb χm Sp h h₂ hη b s ε δ μ₁ μ₂ : ℝ} {M : ℕ} {a χ Mm Kψ Ku T : ι → ℝ}
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
    (htail : ∀ j, ∀ t, b ≤ t → ∫ ξ in b..t, ψ j ξ ^ 2 ≤ T j)
    (hψK : ∀ i, ∀ ξ, 1 ≤ ξ → |ψ i ξ| ≤ Kψ i / ξ) (huK : ∀ i, ∀ ξ, 1 ≤ ξ → |u i ξ| ≤ Ku i * ξ)
    (hN₀ : 0 < ∑ i, a i ^ 2 * Mm i) :
    (∑ i, a i ^ 2 * ((∫ ξ in (1 : ℝ)..b, ψ i ξ ^ 2) - ∑ j, T j))
        - (∑ i, a i ^ 2 * Mm i)
          * (max s (5 / (6 * s))
            + 1 / s * ∑ m ∈ Finset.Icc 2 M, ∑ m' ∈ Finset.Icc 2 M,
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
  -- the first-mode norm from below (Cvs.Prolate.Gram.GramFloorTailOrthogonality)
  have hlow : ∑ i, a i ^ 2 * ((∫ ξ in (1 : ℝ)..b, ψ i ξ ^ 2) - ∑ j, T j) ≤ ∫ ξ in (1 : ℝ)..b, G ξ ^ 2 := by
    have := Cvs.Prolate.Gram.GramFloorTailOrthogonality.gram_floor_tail (by linarith) ψ a K T hcont
      (fun i j hij t ht => hcross i j hij t (by linarith)) htail
    have e : (fun ξ => G ξ ^ 2) = fun ξ => (∑ i, a i * ψ i ξ) ^ 2 := by
      funext ξ; rw [hG, Cvs.L2a.CutoffCrossTermsAsNodes.Gk_zero]
    rw [e]; exact this
  -- the two edge pieces from above (Cvs.Prolate.Gram.RungCombinationNormInterval)
  have hθ₀1 : (1 : ℝ) ≤ 4 / 3 + hη := by linarith
  have hedge := edge_sq_le (G := G) (η := ramp (4 / 3) hη) (θ₀ := 4 / 3 + hη) (b := b) hθ₀1 (by linarith) hGc
    (Cvs.Upstream.SineSquaredBump.continuous_ramp hη0) (fun θ => ramp_nonneg _ _ _) (fun θ => ramp_le_one _ _ _)
    (fun θ hθ => ramp_of_ge hη0 hθ.1)
  have hpieces := edge_pieces_le (a := a) (θ₀ := 4 / 3 + hη) (M := M) K Mm (by linarith) hM hcont hψc hcross hmass
  have eG : ∀ s t : ℝ, ∫ ξ in s..t, G ξ ^ 2 = ∫ ξ in s..t, (∑ i, a i * ψ i ξ) ^ 2 := fun s t => by
    congr 1; funext ξ; rw [hG, Cvs.L2a.CutoffCrossTermsAsNodes.Gk_zero]
  rw [← eG, ← eG] at hpieces
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
      + 1 / s * (5 / 6 * ∫ v in (19 / 10 : ℝ)..(3 * M / 2), G v ^ 2) ≤ max s (5 / (6 * s)) * N₀ := by
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
      _ ≤ max s (5 / (6 * s)) * N₀ := mul_le_mul_of_nonneg_left hpieces (by positivity)
  -- assemble
  have e2 : 1 / s * (5 / 6 * (∫ v in (19 / 10 : ℝ)..(3 * M / 2), G v ^ 2)
      + N₀ * ∑ m ∈ Finset.Icc 2 M, ∑ m' ∈ Finset.Icc 2 M,
        (if m = m' then 0 else Tsym (fun m m' => Tm c m m' χb χm Sp h h₂ ε δ μ₁ μ₂ N) m m'))
      = 1 / s * (5 / 6 * ∫ v in (19 / 10 : ℝ)..(3 * M / 2), G v ^ 2)
        + N₀ * (1 / s * ∑ m ∈ Finset.Icc 2 M, ∑ m' ∈ Finset.Icc 2 M,
          (if m = m' then 0 else Tsym (fun m m' => Tm c m m' χb χm Sp h h₂ ε δ μ₁ μ₂ N) m m')) := by ring
  rw [e2] at hfloor
  nlinarith [hfloor, hlow, hcomb]

end Cvs.L2a.SpanTailFloorMassSum
