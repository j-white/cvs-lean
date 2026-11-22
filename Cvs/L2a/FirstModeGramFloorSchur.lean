import Mathlib
import Cvs.L2a.CutoffCrossTermsAsNodes
import Cvs.L2a.ExplicitCutoffTailFloor
import Cvs.L2a.ExplicitTreeBoundPlateau
import Cvs.L2a.ExplicitTreeBoundRamp
import Cvs.L2a.RungChiHierarchy
import Cvs.L2a.SpanTailFloorMassSum
import Cvs.L2a.TailFloorFromPairNodes
import Cvs.Prolate.Gram.GramFloorTailOrthogonality
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
# The Schur form of the first-mode Gram floor, and the span floor from any first-mode floor

With `|∫₁ᵇ ψ_iψ_j| ≤ K_ij/b` for `i ≠ j` and the Schur sums `Σ_{j≠i}(K_ij + K_ji)/2 ≤ S`,
`∫₁ᵇ (Σ a_iψ_i)² ≥ Σ_i a_i² (∫₁ᵇ ψ_i² − S/b)`: no tail sum over the rungs. The span tail Gram floor (Cvs.L2a.SpanTailFloorMassSum) is
restated from any first-mode floor `L ≤ ∫₁ᵇ G²`.
-/

namespace Cvs.L2a.FirstModeGramFloorSchur

open Real Set Finset intervalIntegral Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.RungChiHierarchy Cvs.Upstream.SineSquaredRamp Cvs.L2a.TailFloorFromPairNodes Cvs.L2a.ExplicitTreeBoundPlateau Cvs.L2a.ExplicitTreeBoundRamp Cvs.L2a.SpanTailFloorMassSum

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The symmetrisation of an off-diagonal double sum: `Σ_{i≠j} (f_i + f_j) K_ij = Σ_i f_i Σ_{j≠i} (K_ij + K_ji)`. -/
theorem sym_sum (f : ι → ℝ) (K : ι → ι → ℝ) :
    ∑ i, ∑ j, (if i = j then 0 else (f i + f j) * K i j) = ∑ i, f i * ∑ j, (if i = j then 0 else K i j + K j i) := by
  have h1 : ∀ i j, (if i = j then 0 else (f i + f j) * K i j)
      = (if i = j then 0 else f i * K i j) + (if i = j then 0 else f j * K i j) := by
    intro i j; split_ifs <;> ring
  simp_rw [h1, Finset.sum_add_distrib]
  have h2 : ∑ i, ∑ j, (if i = j then 0 else f j * K i j) = ∑ i, ∑ j, (if i = j then 0 else f i * K j i) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _
    by_cases h : i = j
    · simp [h]
    · simp [h, Ne.symm h]
  rw [h2]
  simp_rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _
  split_ifs <;> ring

/-- **The Schur form of the Gram floor**: `Σ_i a_i² (∫₁ᵇ ψ_i² − S/b) ≤ ∫₁ᵇ (Σ_i a_iψ_i)²`. -/
theorem gram_floor_schur {b S : ℝ} (hb : 1 ≤ b) (ψ : ι → ℝ → ℝ) (a : ι → ℝ) (K : ι → ι → ℝ)
    (hcont : ∀ i, ContinuousOn (ψ i) (Icc 1 b))
    (hcross : ∀ i j, i ≠ j → |∫ ξ in (1 : ℝ)..b, ψ i ξ * ψ j ξ| ≤ K i j / b)
    (hS : ∀ i, ∑ j, (if i = j then 0 else (K i j + K j i) / 2) ≤ S) :
    ∑ i, a i ^ 2 * ((∫ ξ in (1 : ℝ)..b, ψ i ξ ^ 2) - S / b) ≤ ∫ ξ in (1 : ℝ)..b, (∑ i, a i * ψ i ξ) ^ 2 := by
  have hb0 : 0 < b := by linarith
  have hI : ∀ i j, IntervalIntegrable (fun ξ => ψ i ξ * ψ j ξ) MeasureTheory.volume 1 b := fun i j =>
    ((hcont i).mul (hcont j)).intervalIntegrable_of_Icc hb
  have esq : ∀ i, (∫ ξ in (1 : ℝ)..b, ψ i ξ ^ 2) = ∫ ξ in (1 : ℝ)..b, ψ i ξ * ψ i ξ := fun i => by
    simp only [pow_two]
  simp_rw [esq]
  rw [Cvs.Prolate.Gram.GramFloorTailOrthogonality.integral_sq_sum ψ a hI]
  have hK0 : ∀ i j, i ≠ j → 0 ≤ K i j := fun i j hij => by
    by_contra h
    push_neg at h
    have h1 : K i j / b < 0 := div_neg_of_neg_of_pos h hb0
    linarith [abs_nonneg (∫ ξ in (1 : ℝ)..b, ψ i ξ * ψ j ξ), hcross i j hij]
  -- termwise: the diagonal exactly, the off-diagonal by the Schur bound
  have hlow : ∀ i j, (if i = j then a i ^ 2 * ∫ ξ in (1 : ℝ)..b, ψ i ξ * ψ i ξ
        else -((a i ^ 2 + a j ^ 2) * K i j / (2 * b)))
      ≤ a i * a j * ∫ ξ in (1 : ℝ)..b, ψ i ξ * ψ j ξ := by
    intro i j
    by_cases hij : i = j
    · subst hij; simp only [if_true]; ring_nf; exact le_rfl
    · simp only [hij, if_false]
      have h1 := hcross i j hij
      have hab : |a i * a j| ≤ (a i ^ 2 + a j ^ 2) / 2 := by
        rw [abs_mul]; nlinarith [sq_nonneg (|a i| - |a j|), sq_abs (a i), sq_abs (a j)]
      have h2 : |a i * a j * ∫ ξ in (1 : ℝ)..b, ψ i ξ * ψ j ξ| ≤ (a i ^ 2 + a j ^ 2) / 2 * (K i j / b) := by
        rw [abs_mul]
        exact mul_le_mul hab h1 (abs_nonneg _) (by positivity)
      have h3 := neg_abs_le (a i * a j * ∫ ξ in (1 : ℝ)..b, ψ i ξ * ψ j ξ)
      have e : (a i ^ 2 + a j ^ 2) / 2 * (K i j / b) = (a i ^ 2 + a j ^ 2) * K i j / (2 * b) := by ring
      linarith
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hlow i j
  refine le_trans ?_ hsum
  -- the double sum of the lower bounds
  have hsplit : ∀ i j, (if i = j then a i ^ 2 * ∫ ξ in (1 : ℝ)..b, ψ i ξ * ψ i ξ
        else -((a i ^ 2 + a j ^ 2) * K i j / (2 * b)))
      = (if i = j then a i ^ 2 * ∫ ξ in (1 : ℝ)..b, ψ i ξ * ψ i ξ else 0)
        - 1 / (2 * b) * (if i = j then 0 else (a i ^ 2 + a j ^ 2) * K i j) := by
    intro i j; split_ifs <;> ring
  simp_rw [hsplit, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [sym_sum (fun i => a i ^ 2) K]
  have hrow : ∀ i, a i ^ 2 * ∑ j, (if i = j then 0 else K i j + K j i) ≤ a i ^ 2 * (2 * S) := fun i => by
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    have := hS i
    have e : ∑ j, (if i = j then 0 else K i j + K j i) = 2 * ∑ j, (if i = j then 0 else (K i j + K j i) / 2) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; split_ifs <;> ring
    rw [e]; linarith
  have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hrow i
  have e2 : ∑ i, a i ^ 2 * ((∫ ξ in (1 : ℝ)..b, ψ i ξ * ψ i ξ) - S / b)
      = ∑ i, a i ^ 2 * (∫ ξ in (1 : ℝ)..b, ψ i ξ * ψ i ξ) - 1 / (2 * b) * ∑ i, a i ^ 2 * (2 * S) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro i _; field_simp
  rw [e2]
  have hb' : 0 ≤ 1 / (2 * b) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left this hb']

set_option maxHeartbeats 800000 in
/-- **The span tail Gram floor against the mass sum, from any first-mode floor `L ≤ ∫₁ᵇ G²`**:
`∫₁ᵇ (G + T₂)² ≥ L − N₀ (max(s, 5/(6s)) + (1/s) Σ_{m≠m'} T_m + 2 Σ_m T_f)`, `N₀ = Σ a_i²M_i`. -/
theorem span_floor_of_low {c χb χm Sp h h₂ hη b s ε δ μ₁ μ₂ L : ℝ} {M : ℕ} {a χ Mm Kψ Ku : ι → ℝ}
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
    (hL : L ≤ ∫ ξ in (1 : ℝ)..b, (∑ i, a i * ψ i ξ) ^ 2)
    (hψK : ∀ i, ∀ ξ, 1 ≤ ξ → |ψ i ξ| ≤ Kψ i / ξ) (huK : ∀ i, ∀ ξ, 1 ≤ ξ → |u i ξ| ≤ Ku i * ξ)
    (hN₀ : 0 < ∑ i, a i ^ 2 * Mm i) :
    L - (∑ i, a i ^ 2 * Mm i)
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

end Cvs.L2a.FirstModeGramFloorSchur
