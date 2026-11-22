import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.CutoffFactorSupNorms
import Cvs.L2a.ExplicitTreeBoundPlateau
import Cvs.L2a.ExplicitTreeBoundRamp
import Cvs.L2a.HierarchyFactorDecay
import Cvs.L2a.HierarchyNodeWeight
import Cvs.L2a.RungChiHierarchy
import Cvs.L2a.SpanFloorEdgePieces
import Cvs.L2a.SpanFloorPairSums
import Cvs.L2a.SpanFloorSchurUniformB
import Cvs.L2a.SpanTailFloorLargeC
import Cvs.L2a.SpanTailFloorPositive
import Cvs.L2a.SpanTailFloorProlateLargeC
import Cvs.L2a.SpanTailFloorProlateRungs
import Cvs.L2a.TailFloorFromPairNodes
import Cvs.L2a.TreeBoundInverseScaling
import Cvs.L2a.TreeConstantSupBounds
import Cvs.L2a.TreeStepModePair
import Cvs.Prolate.Gram.RungGramFloorAtInfinity
import Cvs.Prolate.Gram.RungGramFloorHilbert
import Cvs.Prolate.Gram.RungGramFloorPerRung
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.RungDecayBeyondEdge
import Cvs.Prolate.RungOrthogonalityAtInfinity
import Cvs.Prolate.SlepianCommutingRelation

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The prolate span floor at short `b` with its explicit constant

With the edge pieces against the first-mode square (Cvs.L2a.SpanFloorEdgePieces) and the Hilbert first-mode floor (Cvs.Prolate.Gram.RungGramFloorHilbert, Cvs.Prolate.Gram.RungGramFloorPerRung), the
span tail Gram floor for the prolate rungs reads `∫₁ᵇ (G + Σ_{m ≤ M} G(m·))² ≥ ((1 − max(s, 5/(6s)))(1 − θ)
− (K/c + Λ)(1 + τ)) Σ a_i² ∫₁ᵇ ψ_i²`, `θ` bounding each rung's Hilbert loss against its mass; every quantity is
explicit and `b` is free of `c`. The unit level sums `K` are nonnegative.
-/

namespace Cvs.L2a.SpanFloorShortExplicit

open Real Finset Set intervalIntegral Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.Prolate.SlepianCommutingRelation Cvs.L2a.AngularProlateTailPositive Cvs.Prolate.RungOrthogonalityAtInfinity Cvs.Prolate.Gram.RungGramFloorAtInfinity Cvs.L2a.RungChiHierarchy Cvs.L2a.HierarchyNodeWeight Cvs.L2a.TreeStepModePair Cvs.L2a.TailFloorFromPairNodes Cvs.L2a.ExplicitTreeBoundPlateau Cvs.L2a.ExplicitTreeBoundRamp Cvs.L2a.SpanTailFloorProlateRungs Cvs.L2a.TreeBoundInverseScaling Cvs.L2a.SpanFloorPairSums Cvs.L2a.SpanTailFloorLargeC Cvs.L2a.SpanTailFloorPositive Cvs.Prolate.RungTailMassEnergyAtTwo Cvs.L2a.SpanTailFloorProlateLargeC Cvs.L2a.FirstModeGramFloorSchur

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem Vc_nonneg {m ε δ A B Sp : ℝ} (hm : 0 < m) (hε : 0 < ε) (hε2 : ε < 2) (hδ : 0 < δ) (hA : 0 ≤ A)
    (hB : 0 ≤ B) : 0 ≤ Vc m ε δ A B Sp := by
  unfold Vc
  have : 0 < 1 - ε / 2 := by linarith
  positivity

theorem Ecost_nonneg {m₁ m₂ μ₁ μ₂ S' κ₁ κ₂ κ₁' κ₂' C₁ C₂ V₁ V₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hμ₁ : 0 < μ₁)
    (hμ₂ : 0 < μ₂) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hV₁ : 0 ≤ V₁) (hV₂ : 0 ≤ V₂) (k l : ℕ) :
    0 ≤ Ecost m₁ m₂ μ₁ μ₂ S' κ₁ κ₂ κ₁' κ₂' C₁ C₂ V₁ V₂ k l := by
  unfold Ecost; positivity

theorem Bconst_nonneg (c m χb α : ℝ) : 0 ≤ Bconst c m χb α := by unfold Bconst; positivity

theorem Lm_nonneg {m₁ m₂ χh χm Sh h h₂ ε δ μ₁ μ₂ c₀ : ℝ} (hm₁ : 2 ≤ m₁) (hm₁₂ : m₁ + 1 ≤ m₂) (hχm : 0 ≤ χm)
    (hε : 0 < ε) (hε2 : ε < 2) (hδ : 0 < δ) (hμ₁ : 0 < μ₁) (hμ₂ : 0 < μ₂) (hc₀ : 0 < c₀)
    (hq₁ : 0 ≤ m₁ ^ 2 - χh / (19 / 20 - h) ^ 2) (hq₂ : 0 ≤ m₂ ^ 2 - χh / (19 / 20 - h) ^ 2) (N : ℕ) :
    0 ≤ Lm m₁ m₂ χh χm Sh h h₂ ε δ μ₁ μ₂ c₀ N := by
  unfold Lm
  apply Finset.sum_nonneg; intro j _
  apply mul_nonneg (pow_nonneg (ρm_nonneg hm₁ hm₁₂ hχm) j)
  apply Ecost_nonneg (by linarith) (by linarith) hμ₁ hμ₂ (Cf_nonneg _ _ _ _ _ _) (Cf_nonneg _ _ _ _ _ _)
  · exact Vc_nonneg (by linarith) hε hε2 hδ (div_nonneg (Ac_unit_nonneg hq₁) (by positivity)) (Bconst_nonneg _ _ _ _)
  · exact Vc_nonneg (by linarith) hε hε2 hδ (div_nonneg (Ac_unit_nonneg hq₂) (by positivity)) (Bconst_nonneg _ _ _ _)

theorem Lf_nonneg {m χh χm Sh h hη b ε δ μ₁ μ₂ c₀ : ℝ} (hm : 2 ≤ m) (hχm : 0 ≤ χm)
    (hε : 0 < ε) (hε2 : ε < 2) (hδ : 0 < δ) (hμ₁ : 0 < μ₁) (hμ₂ : 0 < μ₂) (hc₀ : 0 < c₀)
    (hq₁ : 0 ≤ 1 ^ 2 - χh / (4 / 3 - h) ^ 2) (hq₂ : 0 ≤ m ^ 2 - χh / (4 / 3 - h) ^ 2) (N : ℕ) :
    0 ≤ Lf m χh χm Sh h hη b ε δ μ₁ μ₂ c₀ N := by
  unfold Lf
  apply Finset.sum_nonneg; intro j _
  apply mul_nonneg (pow_nonneg (ρf_nonneg hm hχm) j)
  apply Ecost_nonneg one_pos (by linarith) hμ₁ hμ₂ (Cf_nonneg _ _ _ _ _ _) (Cf_nonneg _ _ _ _ _ _)
  · exact Vc_nonneg one_pos hε hε2 hδ (div_nonneg (Ac_unit_nonneg hq₁) (by positivity)) (Bconst_nonneg _ _ _ _)
  · exact Vc_nonneg (by linarith) hε hε2 hδ (div_nonneg (Ac_unit_nonneg hq₂) (by positivity)) (Bconst_nonneg _ _ _ _)

/-- The unit level sums `K` are nonnegative. -/
theorem Kpair_nonneg {s χh χm Sh h h₂ hη b ε δ μ₁ μ₂ c₀ : ℝ} {M N : ℕ} (hs : 0 < s) (hχm : 0 ≤ χm)
    (hε : 0 < ε) (hε2 : ε < 2) (hδ : 0 < δ) (hμ₁ : 0 < μ₁) (hμ₂ : 0 < μ₂) (hc₀ : 0 < c₀)
    (hq : ∀ m : ℝ, 1 ≤ m → 0 ≤ m ^ 2 - χh / (19 / 20 - h) ^ 2)
    (hq' : ∀ m : ℝ, 1 ≤ m → 0 ≤ m ^ 2 - χh / (4 / 3 - h) ^ 2) :
    0 ≤ Kpair s χh χm Sh h h₂ hη b ε δ μ₁ μ₂ c₀ M N := by
  unfold Kpair
  have hmem : ∀ n ∈ Finset.Icc 2 M, (2 : ℝ) ≤ n := fun n hn => by
    have := (Finset.mem_Icc.mp hn).1; exact_mod_cast this
  apply add_nonneg
  · apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg; intro m hm
    apply Finset.sum_nonneg; intro m' hm'
    split_ifs with hmm
    · exact le_rfl
    · unfold Tsym
      have hm2 := hmem m hm
      have hm'2 := hmem m' hm'
      split_ifs with hlt
      · have h12 : (m : ℝ) + 1 ≤ m' := by exact_mod_cast hlt
        exact Lm_nonneg hm2 h12 hχm hε hε2 hδ hμ₁ hμ₂ hc₀ (hq _ (by linarith)) (hq _ (by linarith)) N
      · have hlt' : m' < m := lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hmm)
        have h12 : (m' : ℝ) + 1 ≤ m := by exact_mod_cast hlt'
        exact Lm_nonneg hm'2 h12 hχm hε hε2 hδ hμ₁ hμ₂ hc₀ (hq _ (by linarith)) (hq _ (by linarith)) N
  · apply mul_nonneg (by norm_num)
    apply Finset.sum_nonneg; intro m hm
    exact Lf_nonneg (hmem m hm) hχm hε hε2 hδ hμ₁ hμ₂ hc₀ (hq' 1 le_rfl) (hq' _ (by linarith [hmem m hm])) N

set_option maxHeartbeats 1600000 in
/-- **The span tail Gram floor for the prolate rungs at short `b`, for every large `c`, with its constant**:
`∫₁ᵇ (G + Σ_{m ≤ M} G(m·))² ≥ ((1 − max(s, 5/(6s)))(1 − θ) − (K/c + Λ)(1 + τ)) Σ a_i² ∫₁ᵇ ψ_i²` when every rung's
Hilbert loss `(π/D)(b/√(b² − 1)) E_i(b)` is at most `θ` times its mass. -/
theorem span_floor_prolate_const {c c₀ h h₂ hη b s ε δ μ₁ μ₂ D θ : ℝ} {M : ℕ} (N : ℕ)
    (g g₁ g₂ : ι → ℝ → ℝ) (χ : ι → ℝ) (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2) (hinj : Function.Injective χ)
    (hM : 2 ≤ M) (hc₀ : 1 ≤ c₀) (hc : c₀ ≤ c) (hc8 : 8 ≤ c) (hs : 0 < s) (hsmax : max s (5 / (6 * s)) ≤ 1)
    (hh : 0 < h) (hh' : h ≤ 1 / 5)
    (hh₂ : 0 < h₂) (hh₂' : h₂ ≤ 1 / 20) (hη0 : 0 < hη) (hη' : 4 / 3 + hη ≤ 3 / 2 - h₂) (hb : 4 ≤ b)
    (hbM : 3 * M / 2 ≤ b)
    (hε : 0 < ε) (hε2 : ε < 2) (hδ : 0 < δ) (hμ₁ : 0 < μ₁) (hμ₂ : 0 < μ₂)
    (hMpos : ∀ i, 0 < ∫ ξ in (1 : ℝ)..b, psi c (g i) ξ ^ 2)
    (hN₀ : 0 < ∑ i, a i ^ 2 * massB c (χ i) (g i) b)
    (hD : 0 < D) (hgap : ∀ i j, i ≠ j → D ≤ |χ i - χ j|) (hθ : 0 ≤ θ)
    (ht : ∀ i, Real.pi / D * (b / √(b ^ 2 - 1)) * energy (aP c (χ i)) (psi c (g i)) (rungU c (g i)) b
      ≤ θ * ∫ ξ in (1 : ℝ)..b, psi c (g i) ξ ^ 2) :
    ((1 - max s (5 / (6 * s))) * (1 - θ)
        - (Kpair s (1 / 2) 1 (1 / 2) h h₂ hη b ε δ μ₁ μ₂ c₀ M N / c
            + Λpair s 1 b (Qpsi c g g₁ g₂ χ b / c) (Qu c g g₁ g₂ χ b / c ^ 3) M N) * (1 + τtail c b))
        * ∑ i, a i ^ 2 * ∫ ξ in (1 : ℝ)..b, psi c (g i) ξ ^ 2
      ≤ ∫ θ in (1 : ℝ)..b, (Gk a χ (fun i => psi c (g i)) 0 θ
          + ∑ m ∈ Finset.Icc 2 M, Gk a χ (fun i => psi c (g i)) 0 (m * θ)) ^ 2 := by
  have hc1 : 1 ≤ c := hc₀.trans hc
  have hc0 : 0 < c := by linarith
  have hc2 : 0 < c ^ 2 := by positivity
  have hb1 : 1 < b := by linarith
  have hb2 : 2 ≤ b := by linarith
  have hsys := fun i => rung_system (hg i) (hg₁ i) (hg₂c i) (hang i)
  -- the tails beyond `b` (Cvs.Prolate.Gram.RungGramFloorAtInfinity)
  have htail : ∀ j, ∀ t, b ≤ t → ∫ ξ in b..t, psi c (g j) ξ ^ 2 ≤ tailBound c (χ j) (g j) b := by
    intro j t hbt
    obtain ⟨hψu, huu, hcψ, hcu⟩ := hsys j
    have hW := wP_lt_two hb2 hc1 (hχ0 j) (hχc j)
    have hG : ∀ ξ ∈ Icc b t, energy (aP c (χ j)) (psi c (g j)) (rungU c (g j)) ξ
        ≤ energy (aP c (χ j)) (psi c (g j)) (rungU c (g j)) b * (1 + wP c (χ j) b / 2) / (1 - wP c (χ j) b / 2)
          * exp (wP c (χ j) b / (2 - wP c (χ j) b)) := fun ξ hξ =>
      prolate_energy_le hb1 hξ.1 (by positivity) (hχ0 j) (hχc j)
        (fun r hr => hψu r (lt_of_lt_of_le hb1 hr.1)) (fun r _ => huu r) hW
    unfold tailBound
    exact tail_mass_le hc0 (hχc j) hb1 hbt hcψ.continuousOn hG
  have hT0 : ∀ j, 0 ≤ tailBound c (χ j) (g j) b := fun j => by
    have := htail j b le_rfl
    simpa using this
  -- the masses
  have hmass : ∀ i, ∀ t, 1 ≤ t → ∫ ξ in (1 : ℝ)..t, psi c (g i) ξ ^ 2 ≤ massB c (χ i) (g i) b := by
    intro i t ht
    obtain ⟨-, -, hcψ, -⟩ := hsys i
    have hI : ∀ s t : ℝ, IntervalIntegrable (fun ξ => psi c (g i) ξ ^ 2) MeasureTheory.volume s t := fun s t =>
      (hcψ.pow 2).intervalIntegrable s t
    unfold massB
    rcases le_or_gt t b with htb | htb
    · have : ∫ ξ in (1 : ℝ)..t, psi c (g i) ξ ^ 2 ≤ ∫ ξ in (1 : ℝ)..b, psi c (g i) ξ ^ 2 := by
        rw [← integral_add_adjacent_intervals (hI 1 t) (hI t b)]
        have : 0 ≤ ∫ ξ in t..b, psi c (g i) ξ ^ 2 := integral_nonneg htb fun ξ _ => sq_nonneg _
        linarith
      linarith [hT0 i]
    · rw [← integral_add_adjacent_intervals (hI 1 b) (hI b t)]
      linarith [htail i t htb.le]
  have hMm : ∀ i, 0 < massB c (χ i) (g i) b := fun i => by unfold massB; linarith [hMpos i, hT0 i]
  -- orthogonality at infinity (Cvs.Prolate.RungOrthogonalityAtInfinity)
  have hcross : ∀ i j, i ≠ j → ∀ t, 1 ≤ t →
      |∫ ξ in (1 : ℝ)..t, psi c (g i) ξ * psi c (g j) ξ| ≤ Cvs.L2a.SpanFloorSchurUniformB.Kcross c g g₁ g₂ χ i j / t := by
    intro i j hij t ht
    have hχ : χ i ≠ χ j := fun e => hij (hinj e)
    unfold Cvs.L2a.SpanFloorSchurUniformB.Kcross
    rw [div_div]
    exact integral_psi_mul_le (hg i) (hg₁ i) (hg₂c i) (hang i) (hg j) (hg₁ j) (hg₂c j) (hang j) hc0 hχ ht
  -- the decay (Cvs.Prolate.RungDecayBeyondEdge)
  have hψK : ∀ i, ∀ ξ, 1 ≤ ξ → |psi c (g i) ξ| ≤ Kpsi c (g i) (g₁ i) (g₂ i) / ξ := fun i ξ hξ =>
    Cvs.Prolate.RungDecayBeyondEdge.abs_psi_le (hg i) (hg₁ i) (hg₂c i) hc0 hξ
  have huK : ∀ i, ∀ ξ, 1 ≤ ξ → |rungU c (g i) ξ| ≤ Ku c (g i) (g₁ i) (g₂ i) * ξ := fun i ξ hξ =>
    Cvs.Prolate.RungDecayBeyondEdge.abs_rungU_le (hg i) (hg₁ i) (hg₂c i) hc0 hξ
  -- the first-mode floor from Hilbert's inequality (Cvs.Prolate.Gram.RungGramFloorHilbert) with the bracket at `A = cb√(b² − 1)` (Cvs.Prolate.Gram.RungGramFloorPerRung)
  have hA0 : 0 < c * b * √(b ^ 2 - 1) := by
    have : 0 < b ^ 2 - 1 := by nlinarith
    positivity
  have hu1 : ∀ i, rungU c (g i) 1 = 0 := fun i => by unfold rungU pP; norm_num
  have hL0 := Cvs.Prolate.Gram.RungGramFloorHilbert.gram_floor_hilbert (c := c) (A := c * b * √(b ^ 2 - 1)) hb1.le hD hA0 χ
    (fun i => psi c (g i)) (fun i => rungU c (g i)) a hgap (fun i ξ hξ => (hsys i).1 ξ hξ.1)
    (fun i ξ _ => (hsys i).2.1 ξ) (fun i => (hsys i).2.2.1.continuousOn) (fun i => (hsys i).2.2.2.continuousOn) hu1
  have hL : ∑ i, a i ^ 2 * ((∫ ξ in (1 : ℝ)..b, psi c (g i) ξ ^ 2)
        - Real.pi / D * (b / √(b ^ 2 - 1)) * energy (aP c (χ i)) (psi c (g i)) (rungU c (g i)) b)
      ≤ ∫ ξ in (1 : ℝ)..b, (∑ i, a i * psi c (g i) ξ) ^ 2 := by
    refine le_trans (Finset.sum_le_sum fun i _ => ?_) hL0
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    have hbr := Cvs.Prolate.Gram.RungGramFloorPerRung.bracket_le (ψ := psi c (g i)) (u := rungU c (g i)) hc0 (hχ0 i) (hχc i) hb1
    have := mul_le_mul_of_nonneg_left hbr (by positivity : 0 ≤ Real.pi / D)
    linarith
  -- the span floor at the large-`c` instantiation (Cvs.L2a.FirstModeGramFloorSchur, Cvs.L2a.SpanTailFloorMassSum)
  have hα : (3 / 4 : ℝ) ≤ 19 / 20 - h := by linarith
  have hχb : c ^ 2 * (1 / 2) < c ^ 2 * (19 / 20 - h) ^ 2 := by
    apply mul_lt_mul_of_pos_left _ hc2
    nlinarith
  have hSp : ∀ i, |χ i - c ^ 2 * (1 / 2)| ≤ c ^ 2 * (1 / 2) := fun i => by
    rw [abs_le]; constructor <;> linarith [hχ0 i, hχc i]
  have hfloor := Cvs.L2a.SpanFloorEdgePieces.span_floor_of_low' (a := a) (χ := χ) (Mm := fun i => massB c (χ i) (g i) b)
    (Kψ := fun i => Kpsi c (g i) (g₁ i) (g₂ i)) (Ku := fun i => Ku c (g i) (g₁ i) (g₂ i))
    (ψ := fun i => psi c (g i)) (u := fun i => rungU c (g i))
    (χb := c ^ 2 * (1 / 2)) (χm := c ^ 2 * 1) (Sp := c ^ 2 * (1 / 2)) (μ₁ := c * μ₁) (μ₂ := c * μ₂)
    (L := ∑ i, a i ^ 2 * ((∫ ξ in (1 : ℝ)..b, psi c (g i) ξ ^ 2)
      - Real.pi / D * (b / √(b ^ 2 - 1)) * energy (aP c (χ i)) (psi c (g i)) (rungU c (g i)) b))
    (Cvs.L2a.SpanFloorSchurUniformB.Kcross c g g₁ g₂ χ) N hM hc0 hs hsmax hh (by linarith) hh₂ hh₂' hη0 hη' hb2 hbM hχb
    (by positivity)
    (fun i => ⟨hχ0 i, by linarith [hχc i]⟩) (by positivity) hMm hSp hε hε2 hδ (by positivity) (by positivity)
    (fun i => (hsys i).1) (fun i => (hsys i).2.1) (fun i => (hsys i).2.2.1) (fun i => (hsys i).2.2.2)
    hcross hmass hL hψK huK hN₀
  -- the pair sums (Cvs.L2a.SpanFloorPairSums)
  have hq : ∀ m : ℝ, 1 ≤ m → 0 ≤ m ^ 2 - (1 / 2) / (19 / 20 - h) ^ 2 := fun m hm => by
    have hm2 : 1 ≤ m ^ 2 := one_le_pow₀ hm
    have hα2 : (9 / 16 : ℝ) ≤ (19 / 20 - h) ^ 2 := by nlinarith
    have : (1 / 2 : ℝ) / (19 / 20 - h) ^ 2 ≤ 1 := by
      rw [div_le_one (by linarith)]; linarith
    linarith
  have hq' : ∀ m : ℝ, 1 ≤ m → 0 ≤ m ^ 2 - (1 / 2) / (4 / 3 - h) ^ 2 := fun m hm => by
    have hm2 : 1 ≤ m ^ 2 := one_le_pow₀ hm
    have hα2 : (1 : ℝ) ≤ (4 / 3 - h) ^ 2 := by nlinarith
    have : (1 / 2 : ℝ) / (4 / 3 - h) ^ 2 ≤ 1 := by
      rw [div_le_one (by linarith)]; linarith
    linarith
  have hpair := pair_sums_le (c := c) (s := s) (χh := 1 / 2) (χm := 1) (Sh := 1 / 2) (h := h) (h₂ := h₂) (hη := hη)
    (b := b) (ε := ε) (δ := δ) (μ₁ := μ₁) (μ₂ := μ₂) (M := M) (N := N) (Qψ := Qpsi c g g₁ g₂ χ b)
    (Qu := Qu c g g₁ g₂ χ b) (q₁ := Qpsi c g g₁ g₂ χ b / c) (q₂ := Qu c g g₁ g₂ χ b / c ^ 3) (by linarith) hc hs
    zero_le_one hε hε2 hδ hμ₁ hμ₂ hq hq' (by field_simp) (by field_simp)
  set Kp := Kpair s (1 / 2) 1 (1 / 2) h h₂ hη b ε δ μ₁ μ₂ c₀ M N with hKdef
  set Λ := Λpair s 1 b (Qpsi c g g₁ g₂ χ b / c) (Qu c g g₁ g₂ χ b / c ^ 3) M N with hΛdef
  set Pb := Kp / c + Λ with hPbdef
  set S := ∑ i, a i ^ 2 * ∫ ξ in (1 : ℝ)..b, psi c (g i) ξ ^ 2 with hSdef
  set N₀ := ∑ i, a i ^ 2 * massB c (χ i) (g i) b with hN₀def
  unfold Qpsi Qu at hpair
  -- the pieces
  have hmax0 : 0 ≤ 1 - max s (5 / (6 * s)) := by linarith
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (hMpos i).le
  have hLS : (1 - θ) * S ≤ ∑ i, a i ^ 2 * ((∫ ξ in (1 : ℝ)..b, psi c (g i) ξ ^ 2)
      - Real.pi / D * (b / √(b ^ 2 - 1)) * energy (aP c (χ i)) (psi c (g i)) (rungU c (g i)) b) := by
    rw [hSdef, Finset.mul_sum]
    apply Finset.sum_le_sum; intro i _
    have := ht i
    have hm := (hMpos i).le
    nlinarith [sq_nonneg (a i)]
  have hτ0 : 0 ≤ τtail c b := τtail_nonneg hc8 hb
  have hTi : ∀ i, tailBound c (χ i) (g i) b ≤ τtail c b * ∫ ξ in (1 : ℝ)..b, psi c (g i) ξ ^ 2 := fun i => by
    obtain ⟨hψi, hui, hci, -⟩ := hsys i
    unfold tailBound
    have := tail_le_mass_of_energy_ratio (κ := 1) hc8 hb (hχ0 i) (hχc i) (hχ0 i) (hχc i) hψi hui hci hψi hui
      zero_le_one (by linarith)
    linarith
  have hN₀S : N₀ ≤ (1 + τtail c b) * S := by
    rw [hN₀def, hSdef, Finset.mul_sum]
    apply Finset.sum_le_sum; intro i _
    have hmB : massB c (χ i) (g i) b = (∫ ξ in (1 : ℝ)..b, psi c (g i) ξ ^ 2) + tailBound c (χ i) (g i) b := rfl
    rw [hmB]
    have := hTi i
    nlinarith [sq_nonneg (a i)]
  have hPb0 : 0 ≤ Pb := by
    rw [hPbdef]
    have hΛ0 := Λpair_nonneg (s := s) (χm := 1) (q₁ := Qpsi c g g₁ g₂ χ b / c) (q₂ := Qu c g g₁ g₂ χ b / c ^ 3)
      hs zero_le_one hb2 M N
    have hK0 := Kpair_nonneg (s := s) (χh := 1 / 2) (χm := 1) (Sh := 1 / 2) (h := h) (h₂ := h₂) (hη := hη) (b := b)
      (ε := ε) (δ := δ) (μ₁ := μ₁) (μ₂ := μ₂) (c₀ := c₀) (M := M) (N := N) hs zero_le_one hε hε2 hδ hμ₁ hμ₂
      (by linarith) hq hq'
    have : 0 ≤ Kp / c := div_nonneg hK0 hc0.le
    linarith
  -- the pair sums bound the pair terms; assemble
  have h1 := mul_le_mul_of_nonneg_left hLS hmax0
  have h2 : Pb * N₀ ≤ Pb * ((1 + τtail c b) * S) := mul_le_mul_of_nonneg_left hN₀S hPb0
  have hN₀0 : 0 ≤ N₀ := hN₀.le
  have h3 := mul_le_mul_of_nonneg_left hpair hN₀0
  have e : ((1 - max s (5 / (6 * s))) * (1 - θ) - Pb * (1 + τtail c b)) * S
      = (1 - max s (5 / (6 * s))) * ((1 - θ) * S) - Pb * ((1 + τtail c b) * S) := by ring
  rw [e]
  linarith [hfloor, h1, h2, h3]

end Cvs.L2a.SpanFloorShortExplicit
