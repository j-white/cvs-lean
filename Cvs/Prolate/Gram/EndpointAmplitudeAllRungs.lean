import Mathlib
import Cvs.Prolate.EdgeCentreSign
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.Gram.DeepCellFloorAmplitude
import Cvs.Prolate.Gram.DirichletDualFloorShifted
import Cvs.Prolate.Gram.EndpointAmplitudeFloor
import Cvs.Prolate.Gram.PotentialFloorFromCounts
import Cvs.Prolate.Gram.ProlateCellGramHalfUnit
import Cvs.Prolate.Gram.RobinNodeLatticeDualFloor
import Cvs.Prolate.Gram.RungCellGramDisplacement
import Cvs.Prolate.RegularSolutionAllowedRegion
import Cvs.Prolate.RegularSolutionEdge
import Cvs.Prolate.RegularSolutionEnergyComparability
import Cvs.Prolate.SlepianEvenOrdering
import Cvs.Route.Visibility.LayerFloorDeepRemainderB

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The endpoint amplitude on every rung

The window case of the endpoint amplitude holds at every level `θ² ≤ 1`; so `Y_j(a)² ≥ e^{−2c·Ag(T_j, a) − δc}`
at some `a ∈ [½, ½ + ρ]` holds on every rung `j < x`, with `EndpointAmplitudeFloor`'s amplitude on the rungs with `T_j ≤ ¾`.
-/

noncomputable section

open Real Set Filter Topology MeasureTheory
open Cvs.Prolate.RegularSolutionEdge (regSol regU sqC)

namespace Cvs.Prolate.Gram.EndpointAmplitudeAllRungs
open Cvs.ZeroCounting

/-- **The window case at any level `θ² ≤ 1`**: with `½ + ρ < θ`, `0 < ρ ≤ 1/10`, `c²ρ³ ≥ 50` and
`16(1 + c²) ≤ e^{δc}`, some `a ∈ [½, ½ + ρ/2]` has `e^{−δc}∫_0^1 y² ≤ y(a)²`. -/
theorem window_case {c σ θ ρ δ : ℝ} (hc : 1 ≤ c) (hθ : 1 / 2 + ρ < θ) (hθ1 : θ ^ 2 ≤ 1)
    (hσθ : σ = c ^ 2 * θ ^ 2) (hev : regU (sqC c) σ 0 = 0) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1 / 10)
    (hcρ : 50 ≤ c ^ 2 * ρ ^ 3) (hpoly : 16 * (1 + c ^ 2) ≤ Real.exp (δ * c)) :
    ∃ a ∈ Icc (1 / 2 : ℝ) (1 / 2 + ρ / 2),
      Real.exp (-(δ * c)) * (∫ s in (0 : ℝ)..1, regSol (sqC c) σ s ^ 2) ≤ regSol (sqC c) σ a ^ 2 := by
  have hc0 : 0 < c := by linarith
  have hθ0 : 0 < θ := by linarith
  have hσpos : 0 < σ := by rw [hσθ]; positivity
  have hm : ∀ t ∈ Icc (1 / 2 : ℝ) (1 / 2 + ρ / 2), 8 / 25 * c ^ 2 * ρ ≤ Cvs.Prolate.RegularSolutionAllowedRegion.pq c σ t := by
    intro t ht
    unfold Cvs.Prolate.RegularSolutionAllowedRegion.pq
    have hp : 16 / 25 ≤ 1 - t ^ 2 := by nlinarith [ht.2, ht.1]
    have hq : c ^ 2 * (ρ / 2) ≤ σ - c ^ 2 * t ^ 2 := by
      rw [hσθ]
      have : ρ / 2 ≤ θ ^ 2 - t ^ 2 := by nlinarith [ht.2, ht.1]
      nlinarith [mul_le_mul_of_nonneg_left this (sq_nonneg c)]
    have := mul_le_mul hp hq (by positivity) (by linarith)
    nlinarith
  have hbig : 4 ≤ (1 / 2 + ρ / 2 - 1 / 2) ^ 2 * (8 / 25 * c ^ 2 * ρ) := by nlinarith
  have hq : c ^ 2 * (1 / 2 + ρ / 2) ^ 2 < σ := by
    rw [hσθ]
    exact mul_lt_mul_of_pos_left (pow_lt_pow_left₀ (by linarith) (by positivity) two_ne_zero) (by positivity)
  obtain ⟨a, ha, hya⟩ := Cvs.Prolate.RegularSolutionAllowedRegion.exists_sq_ge (c := c) hσpos hev (by norm_num) (by linarith) (by linarith) hq hm
    hbig
  refine ⟨a, ha, ?_⟩
  have h7 := Cvs.Prolate.RegularSolutionEnergyComparability.integral_sq_le (c := c) (σ := σ) (b := 0) le_rfl one_pos (by simp [hσpos.le])
  rw [hev] at h7
  have hσc : σ ≤ c ^ 2 := by rw [hσθ]; nlinarith [sq_nonneg c]
  generalize ∫ s in (0 : ℝ)..1, regSol (sqC c) σ s ^ 2 = I at h7 ⊢
  generalize regSol (sqC c) σ 0 = y0 at h7 hya
  generalize regSol (sqC c) σ a = ya at hya ⊢
  have hI : I ≤ 8 * (1 + c ^ 2) * ya ^ 2 := by nlinarith [sq_nonneg y0]
  rw [Real.exp_neg, inv_mul_le_iff₀ (Real.exp_pos _)]
  nlinarith [sq_nonneg ya, mul_le_mul_of_nonneg_right hpoly (sq_nonneg ya)]

/-- **The endpoint amplitude on every rung**: for every `ρ, δ > 0`, eventually every `j < x` has an endpoint
`a ∈ [½, ½ + ρ]` with `Y_j(a)² ≥ e^{−2c·Ag(T_j, a) − δc}`. -/
theorem ampFloor_all : ∀ ρ > 0, ∀ δ > 0, ∀ᶠ x : ℕ in atTop, ∀ j : Fin x,
    ∃ a ∈ Icc (1 / 2 : ℝ) (1 / 2 + ρ),
      Real.exp (-(2 * (2 * π * x) * Cvs.Prolate.Gram.DeepCellFloorAmplitude.agmonInt (Cvs.Prolate.Gram.ProlateCellGramHalfUnit.levT x j) a) - δ * (2 * π * x))
        ≤ Cvs.Prolate.Gram.ProlateCellGramHalfUnit.cellFun x j a ^ 2 := by
  intro ρ hρ δ hδ
  set ρ' := min ρ (1 / 10) with hρ'
  have hρ'0 : 0 < ρ' := lt_min hρ (by norm_num)
  have hρ'1 : ρ' ≤ 1 / 10 := min_le_right _ _
  have hρ'ρ : ρ' ≤ ρ := min_le_left _ _
  have hc : Tendsto (fun x : ℕ => 2 * π * (x : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity)
  filter_upwards [Cvs.Prolate.Gram.EndpointAmplitudeFloor.ampFloor ρ hρ δ hδ, Cvs.Route.Visibility.LayerFloorDeepRemainderB.eventually_scale, hc.eventually_ge_atTop (50 / ρ' ^ 3),
    Cvs.Prolate.Gram.EndpointAmplitudeFloor.eventually_pow_le_exp 32 (k := δ) hδ 2] with x hA hx hcρ hpoly2
  intro j
  by_cases hj : Cvs.Prolate.Gram.ProlateCellGramHalfUnit.levT x j ≤ 3 / 4
  · exact hA j hj
  push Not at hj
  have hc1 : 1 ≤ 2 * π * (x : ℝ) := by linarith
  have hc0 : 0 < 2 * π * (x : ℝ) := by linarith
  have hσ0 : 0 ≤ Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.chi x j := Cvs.Prolate.SlepianEvenOrdering.nonneg_of_mem_evenSpec _ (Cvs.Prolate.EvenRungsByIndex.lev_spec (Cvs.Prolate.Gram.RungCellGramDisplacement.rungIdx_level hx j)).1
  have hev : regU (sqC (2 * π * x)) (Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.chi x j) 0 = 0 := (Cvs.Prolate.EvenRungsByIndex.lev_spec (Cvs.Prolate.Gram.RungCellGramDisplacement.rungIdx_level hx j)).1
  have hlevT : Cvs.Prolate.Gram.ProlateCellGramHalfUnit.levT x j = Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.chi x j / (2 * π * x) ^ 2 := rfl
  have hT0 : 0 ≤ Cvs.Prolate.Gram.ProlateCellGramHalfUnit.levT x j := by rw [hlevT]; positivity
  have hθ2 : √(Cvs.Prolate.Gram.ProlateCellGramHalfUnit.levT x j) ^ 2 = Cvs.Prolate.Gram.ProlateCellGramHalfUnit.levT x j := Real.sq_sqrt hT0
  have hσθ : Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.chi x j = (2 * π * x) ^ 2 * √(Cvs.Prolate.Gram.ProlateCellGramHalfUnit.levT x j) ^ 2 := by
    have hx0 : (x : ℝ) ≠ 0 := by intro h; rw [h] at hc0; simp at hc0
    rw [hθ2, hlevT]; field_simp
  have hθ1 : √(Cvs.Prolate.Gram.ProlateCellGramHalfUnit.levT x j) ^ 2 ≤ 1 := by rw [hθ2]; exact (Cvs.Prolate.Gram.PotentialFloorFromCounts.levT_lt_one hx j).le
  have hint_pos : 0 < ∫ s in (0 : ℝ)..1, regSol (sqC (2 * π * x)) (Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.chi x j) s ^ 2 := by
    simpa [Cvs.Prolate.Gram.DirichletDualFloorShifted.dirMass] using Cvs.Prolate.Gram.DirichletDualFloorShifted.dirMass_pos (2 * π * x) (Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.chi x j) (a := 0) (by norm_num) (by norm_num)
  have hnorm : ∀ a ∈ Icc (0 : ℝ) 1, Cvs.Prolate.Gram.ProlateCellGramHalfUnit.cellFun x j a ^ 2 =
      regSol (sqC (2 * π * x)) (Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.chi x j) a ^ 2 /
        ∫ s in (0 : ℝ)..1, regSol (sqC (2 * π * x)) (Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.chi x j) s ^ 2 :=
    fun a ha => by rw [eq_div_iff hint_pos.ne']; exact Cvs.Prolate.Gram.EndpointAmplitudeFloor.cellFun_sq_mul hx j ha
  have hθa : 1 / 2 + ρ' < √(Cvs.Prolate.Gram.ProlateCellGramHalfUnit.levT x j) := by
    have h1 : (1 / 2 + ρ') ^ 2 < Cvs.Prolate.Gram.ProlateCellGramHalfUnit.levT x j := by nlinarith
    rw [← Real.sqrt_sq (by linarith : (0 : ℝ) ≤ 1 / 2 + ρ')]
    exact Real.sqrt_lt_sqrt (by positivity) h1
  have hcρ' : 50 ≤ (2 * π * x) ^ 2 * ρ' ^ 3 := by
    rw [div_le_iff₀ (by positivity)] at hcρ
    have h1 : (2 * π * (x : ℝ)) * ρ' ^ 3 ≤ (2 * π * x) ^ 2 * ρ' ^ 3 := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      rw [sq]; exact le_mul_of_one_le_left hc0.le hc1
    linarith
  have hp2 : 16 * (1 + (2 * π * x) ^ 2) ≤ Real.exp (δ * (2 * π * x)) := by
    have h1 : 1 ≤ (2 * π * (x : ℝ)) ^ 2 := one_le_pow₀ hc1
    linarith
  obtain ⟨a, ha, key⟩ := window_case (c := 2 * π * x) hc1 hθa hθ1 hσθ hev hρ'0 hρ'1 hcρ' hp2
  refine ⟨a, ⟨ha.1, ha.2.trans (by linarith)⟩, ?_⟩
  have ha0 : 0 ≤ a := by linarith [ha.1]
  have hag : Cvs.Prolate.Gram.DeepCellFloorAmplitude.agmonInt (Cvs.Prolate.Gram.ProlateCellGramHalfUnit.levT x j) a = 0 := by
    rw [Cvs.Prolate.Gram.DeepCellFloorAmplitude.agmonInt, intervalIntegral.integral_symm,
      Cvs.Prolate.Gram.DeepCellFloorAmplitude.integral_zero_of_le (by linarith [ha.2]) (by rw [hθ2]) ha0, neg_zero]
  rw [hnorm a ⟨ha0, by linarith [ha.2]⟩, le_div_iff₀ hint_pos, hag, mul_zero, neg_zero, zero_sub]
  exact key

end Cvs.Prolate.Gram.EndpointAmplitudeAllRungs

end
