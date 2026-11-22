import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.ExplicitTreeBoundPlateau
import Cvs.L2a.ExplicitTreeBoundRamp
import Cvs.L2a.RungChiHierarchy
import Cvs.L2a.SpanTailFloorMassSum
import Cvs.L2a.TailFloorFromPairNodes
import Cvs.Prolate.Gram.RungGramFloorAtInfinity
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.RungDecayBeyondEdge
import Cvs.Prolate.RungOrthogonalityAtInfinity

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The span tail Gram floor for the prolate rungs

For rungs `ψ_i = psi c g_i` of angular solutions with distinct `χ_i ∈ [0, c²)`, `c ≥ 1`, `b ≥ 2`, the hypotheses of
Cvs.L2a.SpanTailFloorMassSum hold with `u_i = rungU c g_i` (Cvs.Prolate.Gram.RungGramFloorAtInfinity), `K_ij` the Wronskian constants over `|χ_i − χ_j|` (Cvs.Prolate.RungOrthogonalityAtInfinity), the masses
`M_i = ∫₁ᵇ ψ_i² + T_i` with `T_i` the tail bounds (Cvs.Prolate.Gram.RungGramFloorAtInfinity), and the decay constants of Cvs.Prolate.RungDecayBeyondEdge: the floor
`∫₁ᵇ (Σ_{m≤M} ψ(m·))² ≥ Σ a_i²(∫₁ᵇ ψ_i² − Σ_j T_j) − N₀(max(s, 5/6s) + (1/s)Σ T_m + 2Σ T_f)` for the rung span.
-/

namespace Cvs.L2a.SpanTailFloorProlateRungs

open Real Set Finset intervalIntegral Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.Prolate.SlepianCommutingRelation Cvs.L2a.AngularProlateTailPositive Cvs.Prolate.RungOrthogonalityAtInfinity Cvs.Prolate.Gram.RungGramFloorAtInfinity Cvs.L2a.RungChiHierarchy Cvs.L2a.TailFloorFromPairNodes Cvs.L2a.ExplicitTreeBoundPlateau Cvs.L2a.ExplicitTreeBoundRamp Cvs.L2a.SpanTailFloorMassSum

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The decay constant of a rung: `|ψ(ξ)| ≤ Kψ/ξ` (Cvs.Prolate.RungDecayBeyondEdge). -/
noncomputable def Kpsi (c : ℝ) (g g₁ g₂ : ℝ → ℝ) : ℝ :=
  |g 1 + g (-1)| / c + (|g₁ 1 - g₁ (-1)| + ∫ s in (-1 : ℝ)..1, |g₂ s|) / c ^ 2
/-- The growth constant of `u`: `|u(ξ)| ≤ Ku ξ` (Cvs.Prolate.RungDecayBeyondEdge). -/
noncomputable def Ku (c : ℝ) (g g₁ g₂ : ℝ → ℝ) : ℝ :=
  2 * |g 1 + g (-1)| + (|g 1 + g₁ 1 + (g (-1) - g₁ (-1))| + ∫ s in (-1 : ℝ)..1, 2 * |g₁ s| + |g₂ s|) / c
/-- The mass of a rung: its square on `[1, b]` plus its tail bound. -/
noncomputable def massB (c χ : ℝ) (g : ℝ → ℝ) (b : ℝ) : ℝ :=
  (∫ ξ in (1 : ℝ)..b, psi c g ξ ^ 2) + tailBound c χ g b

set_option maxHeartbeats 800000 in
/-- **The span tail Gram floor for the prolate rungs.** -/
theorem span_floor_prolate {c χb χm Sp h h₂ hη b s ε δ μ₁ μ₂ : ℝ} {M : ℕ} (N : ℕ)
    (g g₁ g₂ : ι → ℝ → ℝ) (χ : ι → ℝ) (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2) (hinj : Function.Injective χ)
    (hM : 2 ≤ M) (hc : 1 ≤ c) (hs : 0 < s) (hh : 0 < h) (hh' : h ≤ 1 / 4) (hh₂ : 0 < h₂) (hh₂' : h₂ ≤ 1 / 20)
    (hη0 : 0 < hη) (hη' : 4 / 3 + hη ≤ 3 / 2 - h₂) (hb : 2 ≤ b)
    (hχb : χb < c ^ 2 * (19 / 20 - h) ^ 2) (hχb0 : 0 ≤ χb) (hχm' : ∀ i, χ i ≤ χm) (hχm : 0 < χm) (hS : ∀ i, |χ i - χb| ≤ Sp)
    (hε : 0 < ε) (hε2 : ε < 2) (hδ : 0 < δ) (hμ₁ : 0 < μ₁) (hμ₂ : 0 < μ₂)
    (hMpos : ∀ i, 0 < ∫ ξ in (1 : ℝ)..b, psi c (g i) ξ ^ 2)
    (hN₀ : 0 < ∑ i, a i ^ 2 * massB c (χ i) (g i) b) :
    (∑ i, a i ^ 2 * ((∫ ξ in (1 : ℝ)..b, psi c (g i) ξ ^ 2) - ∑ j, tailBound c (χ j) (g j) b))
        - (∑ i, a i ^ 2 * massB c (χ i) (g i) b)
          * (max s (5 / (6 * s))
            + 1 / s * ∑ m ∈ Finset.Icc 2 M, ∑ m' ∈ Finset.Icc 2 M,
                (if m = m' then 0 else Tsym (fun m m' => Tm c m m' χb χm Sp h h₂ ε δ μ₁ μ₂ N) m m')
            + 2 * ∑ m ∈ Finset.Icc 2 M,
                Tf c m χb χm Sp h hη b ε δ μ₁ μ₂ (∑ i, Kpsi c (g i) (g₁ i) (g₂ i) ^ 2 / massB c (χ i) (g i) b)
                  (∑ i, Ku c (g i) (g₁ i) (g₂ i) ^ 2 / massB c (χ i) (g i) b) N)
      ≤ ∫ θ in (1 : ℝ)..b, (Gk a χ (fun i => psi c (g i)) 0 θ
          + ∑ m ∈ Finset.Icc 2 M, Gk a χ (fun i => psi c (g i)) 0 (m * θ)) ^ 2 := by
  have hc0 : 0 < c := by linarith
  have hb1 : 1 < b := by linarith
  have hsys := fun i => rung_system (hg i) (hg₁ i) (hg₂c i) (hang i)
  -- the tails beyond `b` (Cvs.Prolate.Gram.RungGramFloorAtInfinity)
  have htail : ∀ j, ∀ t, b ≤ t → ∫ ξ in b..t, psi c (g j) ξ ^ 2 ≤ tailBound c (χ j) (g j) b := by
    intro j t hbt
    obtain ⟨hψu, huu, hcψ, hcu⟩ := hsys j
    have hW := wP_lt_two hb hc (hχ0 j) (hχc j)
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
      |∫ ξ in (1 : ℝ)..t, psi c (g i) ξ * psi c (g j) ξ|
        ≤ wronskianConst c (g i) (g₁ i) (g₂ i) (g j) (g₁ j) (g₂ j) / |χ i - χ j| / t := by
    intro i j hij t ht
    have hχ : χ i ≠ χ j := fun e => hij (hinj e)
    rw [div_div]
    exact integral_psi_mul_le (hg i) (hg₁ i) (hg₂c i) (hang i) (hg j) (hg₁ j) (hg₂c j) (hang j) hc0 hχ ht
  -- the decay (Cvs.Prolate.RungDecayBeyondEdge)
  have hψK : ∀ i, ∀ ξ, 1 ≤ ξ → |psi c (g i) ξ| ≤ Kpsi c (g i) (g₁ i) (g₂ i) / ξ := fun i ξ hξ =>
    Cvs.Prolate.RungDecayBeyondEdge.abs_psi_le (hg i) (hg₁ i) (hg₂c i) hc0 hξ
  have huK : ∀ i, ∀ ξ, 1 ≤ ξ → |rungU c (g i) ξ| ≤ Ku c (g i) (g₁ i) (g₂ i) * ξ := fun i ξ hξ =>
    Cvs.Prolate.RungDecayBeyondEdge.abs_rungU_le (hg i) (hg₁ i) (hg₂c i) hc0 hξ
  exact span_floor (a := a) (χ := χ) (Mm := fun i => massB c (χ i) (g i) b) (Kψ := fun i => Kpsi c (g i) (g₁ i) (g₂ i))
    (Ku := fun i => Ku c (g i) (g₁ i) (g₂ i)) (T := fun j => tailBound c (χ j) (g j) b)
    (ψ := fun i => psi c (g i)) (u := fun i => rungU c (g i))
    (fun i j => wronskianConst c (g i) (g₁ i) (g₂ i) (g j) (g₁ j) (g₂ j) / |χ i - χ j|) N
    hM hc0 hs hh hh' hh₂ hh₂' hη0 hη' hb hχb hχb0 (fun i => ⟨hχ0 i, hχm' i⟩) hχm hMm hS hε hε2 hδ hμ₁ hμ₂
    (fun i => (hsys i).1) (fun i => (hsys i).2.1) (fun i => (hsys i).2.2.1) (fun i => (hsys i).2.2.2)
    hcross hmass htail hψK huK hN₀

end Cvs.L2a.SpanTailFloorProlateRungs
