import Mathlib
import Cvs.Prolate.EdgeCentreSign
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.Gram.DeepCellFloorAmplitude
import Cvs.Prolate.Gram.DeepRemainderCellFloors
import Cvs.Prolate.Gram.DirichletDualFloorShifted
import Cvs.Prolate.Gram.ProlateCellGramHalfUnit
import Cvs.Prolate.Gram.RobinNodeLatticeDualFloor
import Cvs.Prolate.Gram.RungCellGramDisplacement
import Cvs.Prolate.RegularSolutionAllowedRegion
import Cvs.Prolate.RegularSolutionEdge
import Cvs.Prolate.RegularSolutionEnergyComparability
import Cvs.Prolate.RegularSolutionForbiddenRegion
import Cvs.Prolate.RungEqRegularSolution
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
# The endpoint amplitude `AmpFloor` (eq-cpb Lemma 9)

`Y_j(a)² = y(a)²/∫_0^1 y²`. If the turning point `θ = √T_j` is at most `½ + ρ`, take `a = ½ + ρ`: Cvs.Prolate.RegularSolutionAllowedRegion bounds
`∫_0^1 y² ≤ 50(1 + c²)²y(θ)²` and Cvs.Prolate.RegularSolutionForbiddenRegion bounds `log y(θ) ≤ log y(a) + c√η + (1 + ε)c·Ag + 2`. Otherwise some
`a ∈ [½, ½ + ρ/2]` has `y(a)² ≥ y(0)²/2` while `∫_0^1 y² ≤ 4(1 + σ)y(0)²`.
-/

noncomputable section

open Real Set Filter Topology MeasureTheory
open Cvs.Prolate.RegularSolutionEdge (regSol regU sqC)

namespace Cvs.Prolate.Gram.EndpointAmplitudeFloor
open Cvs.ZeroCounting

/-- **The normalisation**: `Y_j(a)²∫_0^1 y_{χ_j}² = y_{χ_j}(a)²` for `a ∈ [0, 1]`. -/
theorem cellFun_sq_mul {x : ℕ} (hx : 80 ≤ 2 * π * x) (j : Fin x) {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) :
    Cvs.Prolate.Gram.ProlateCellGramHalfUnit.cellFun x j a ^ 2 * ∫ s in (0 : ℝ)..1, regSol (sqC (2 * π * x)) (Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.chi x j) s ^ 2 =
      regSol (sqC (2 * π * x)) (Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.chi x j) a ^ 2 := by
  have hlev : ∃ χ, Cvs.Prolate.EvenRungsByIndex.IsLevelIdx (2 * π * x) (2 * (j : ℕ)) χ := Cvs.Prolate.Gram.RungCellGramDisplacement.rungIdx_level hx j
  obtain ⟨-, -, -, -, heven, hnorm⟩ := Cvs.Prolate.EvenRungsByIndex.rung_spec hlev
  obtain ⟨-, hr⟩ := Cvs.Prolate.RungEqRegularSolution.rung_eq_mul_regSol hlev
  set r1 := Cvs.Prolate.EvenRungsByIndex.rung (2 * π * x) (2 * (j : ℕ)) 1
  set R : ℝ → ℝ := Cvs.Prolate.EvenRungsByIndex.rung (2 * π * x) (2 * (j : ℕ)) with hR
  set y := regSol (sqC (2 * π * x)) (Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.chi x j)
  have hrc : ContinuousOn (fun s => R s ^ 2) (Icc (-1) 1) := (Cvs.Prolate.Gram.ProlateCellGramHalfUnit.continuousOn_rung _ _).pow 2
  have hi : ∀ a b : ℝ, a ∈ Icc (-1 : ℝ) 1 → b ∈ Icc (-1 : ℝ) 1 →
      IntervalIntegrable (fun s => R s ^ 2) volume a b := fun a b ha hb =>
    (hrc.mono (Set.uIcc_subset_Icc ha hb)).intervalIntegrable
  have hm1 : (-1 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨le_rfl, by norm_num⟩
  have hz : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hp1 : (1 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, le_rfl⟩
  have h1 : ∫ s in (-1 : ℝ)..1, R s ^ 2 = (∫ s in (-1 : ℝ)..0, R s ^ 2) + ∫ s in (0 : ℝ)..1, R s ^ 2 :=
    (intervalIntegral.integral_add_adjacent_intervals (hi _ _ hm1 hz) (hi _ _ hz hp1)).symm
  have h2 : ∫ s in (-1 : ℝ)..0, R s ^ 2 = ∫ s in (0 : ℝ)..1, R s ^ 2 := by
    have := intervalIntegral.integral_comp_neg (a := 0) (b := 1) (fun s => R s ^ 2)
    rw [neg_zero] at this
    rw [← this]
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le zero_le_one] at hs
    show R (-s) ^ 2 = R s ^ 2
    rw [heven s ⟨by linarith [hs.1], hs.2⟩]
  have h3 : ∫ s in (0 : ℝ)..1, R s ^ 2 = r1 ^ 2 * ∫ s in (0 : ℝ)..1, y s ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le zero_le_one] at hs
    show R s ^ 2 = r1 ^ 2 * y s ^ 2
    rw [hr s ⟨by linarith [hs.1], hs.2⟩]
    ring
  have hnorm' : 2 * r1 ^ 2 * ∫ s in (0 : ℝ)..1, y s ^ 2 = 1 := by
    rw [mul_assoc, ← h3, two_mul]
    nth_rewrite 1 [← h2]
    rw [← h1]
    exact hnorm
  have hra : Cvs.Prolate.EvenRungsByIndex.rung (2 * π * x) (2 * (j : ℕ)) a = r1 * y a := hr a ⟨by linarith [ha.1], ha.2⟩
  rw [Cvs.Prolate.Gram.ProlateCellGramHalfUnit.cellFun, hra, mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  calc 2 * (r1 ^ 2 * y a ^ 2) * ∫ s in (0 : ℝ)..1, y s ^ 2
        = (2 * r1 ^ 2 * ∫ s in (0 : ℝ)..1, y s ^ 2) * y a ^ 2 := by ring
    _ = y a ^ 2 := by rw [hnorm', one_mul]

/-- `K(2πx)ⁿ ≤ e^{k·2πx}` eventually, for `k > 0`. -/
theorem eventually_pow_le_exp (K : ℝ) {k : ℝ} (hk : 0 < k) (n : ℕ) :
    ∀ᶠ x : ℕ in atTop, K * (2 * π * x) ^ n ≤ Real.exp (k * (2 * π * x)) := by
  have hc : Tendsto (fun x : ℕ => 2 * π * (x : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity)
  have h := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n).comp (hc.const_mul_atTop hk)).const_mul
    ((|K| + 1) / k ^ n)
  rw [mul_zero] at h
  filter_upwards [h.eventually (gt_mem_nhds one_pos), hc.eventually_gt_atTop 0] with x hx hx0
  simp only [Function.comp] at hx
  have e : (|K| + 1) / k ^ n * ((k * (2 * π * x)) ^ n * Real.exp (-(k * (2 * π * x)))) =
      (|K| + 1) * (2 * π * x) ^ n / Real.exp (k * (2 * π * x)) := by
    rw [Real.exp_neg, mul_pow]; field_simp
  rw [e, div_lt_one (Real.exp_pos _)] at hx
  have : K * (2 * π * x) ^ n ≤ (|K| + 1) * (2 * π * x) ^ n :=
    mul_le_mul_of_nonneg_right (by linarith [le_abs_self K]) (by positivity)
  linarith

/-- **The forbidden case**: for `c ≥ 4`, `σ = c²θ²`, `θ² ≤ ¾`, `θ ≤ a ≤ 3/5` and parameters with `√η = δ/8`,
`ε ≤ min(δ/8, 1)`, `c⁴ ≤ ε²(c²η)³`, `50(1 + c²)²e⁴ ≤ e^{δc/2}`, the mass obeys `e^{−2cA − δc}∫_0^1 y² ≤ y(a)²`,
`A = ∫_θ^a √(t² − θ²)/√(1 − t²) dt`. -/
theorem turning_case {c σ θ a δ ε η : ℝ} (hc : 4 ≤ c) (hθ0 : 0 ≤ θ) (hθ3 : θ ^ 2 ≤ 3 / 4)
    (hσθ : σ = c ^ 2 * θ ^ 2) (hθa : θ ≤ a) (ha35 : a ≤ 3 / 5) (hδ : 0 < δ) (hη0 : 0 < η) (hsη : √η = δ / 8)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hεδ : ε ≤ δ / 8) (hw : c ^ 4 ≤ ε ^ 2 * (c ^ 2 * η) ^ 3)
    (hpoly : 50 * (1 + c ^ 2) ^ 2 * Real.exp 4 ≤ Real.exp (δ / 2 * c)) :
    Real.exp (-(2 * c * ∫ t in θ..a, √(t ^ 2 - θ ^ 2) / √(1 - t ^ 2)) - δ * c) *
      (∫ s in (0 : ℝ)..1, regSol (sqC c) σ s ^ 2) ≤ regSol (sqC c) σ a ^ 2 := by
  have hc0 : 0 < c := by linarith
  have hI := Cvs.Prolate.RegularSolutionAllowedRegion.integral_sq_le_turning (c := c) (σ := σ) hc hθ0 hθ3 hσθ
  have hlog := Cvs.Prolate.RegularSolutionForbiddenRegion.log_le_tunnel (c := c) (σ := σ) hc0 hθ0 hσθ hθa ha35 hη0 hε0 hε1 hw
  have hA0 : 0 ≤ ∫ t in θ..a, √(t ^ 2 - θ ^ 2) / √(1 - t ^ 2) :=
    intervalIntegral.integral_nonneg hθa fun t _ => by positivity
  have hA1 : (∫ t in θ..a, √(t ^ 2 - θ ^ 2) / √(1 - t ^ 2)) ≤ 1 := by
    have := intervalIntegral.integral_mono_on hθa
      (Cvs.Prolate.Gram.DeepCellFloorAmplitude.intervalIntegrable_f (T := θ ^ 2) hθ0 hθa (by linarith)) (intervalIntegrable_const (c := (5 / 4 : ℝ)))
      fun t ht => by
        have hp : 16 / 25 ≤ 1 - t ^ 2 := by nlinarith [ht.1, ht.2, hθ0.trans ht.1]
        have hs : (4 / 5 : ℝ) ≤ √(1 - t ^ 2) := by
          rw [show (4 / 5 : ℝ) = √((4 / 5) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
          exact Real.sqrt_le_sqrt (by linarith)
        have hn : √(t ^ 2 - θ ^ 2) ≤ 1 := by
          rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt (by nlinarith [ht.2, hθ0.trans ht.1])
        rw [div_le_iff₀ (by linarith)]; nlinarith
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    nlinarith
  have hyθ : 1 ≤ regSol (sqC c) σ θ := Cvs.Prolate.RegularSolutionForbiddenRegion.one_le_forbidden hθ0 hσθ.le θ ⟨le_rfl, by nlinarith⟩
  have hya : 1 ≤ regSol (sqC c) σ a := Cvs.Prolate.RegularSolutionForbiddenRegion.one_le_forbidden hθ0 hσθ.le a ⟨hθa, by linarith⟩
  generalize ∫ t in θ..a, √(t ^ 2 - θ ^ 2) / √(1 - t ^ 2) = A at hlog hA0 hA1 ⊢
  generalize ∫ s in (0 : ℝ)..1, regSol (sqC c) σ s ^ 2 = I at hI ⊢
  generalize regSol (sqC c) σ θ = Y at hI hlog hyθ
  generalize regSol (sqC c) σ a = Ya at hlog hya ⊢
  have hY : Y ≤ Ya * Real.exp (c * √η + (1 + ε) * c * A + 2) := by
    rw [← Real.exp_log (by linarith : 0 < Y), ← Real.exp_log (by linarith : 0 < Ya), ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  have hY2 : Y ^ 2 ≤ Ya ^ 2 * Real.exp (2 * (c * √η + (1 + ε) * c * A + 2)) := by
    have h2 := pow_le_pow_left₀ (by linarith) hY 2
    have e : (Ya * Real.exp (c * √η + (1 + ε) * c * A + 2)) ^ 2 =
        Ya ^ 2 * Real.exp (2 * (c * √η + (1 + ε) * c * A + 2)) := by
      rw [mul_pow, ← Real.exp_nat_mul]; push_cast; ring_nf
    linarith
  have hE : Real.exp (-(2 * c * A) - δ * c) * Real.exp (2 * (c * √η + (1 + ε) * c * A + 2)) =
      Real.exp 4 * Real.exp (-(δ * c) + 2 * c * √η + 2 * ε * c * A) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hsmall : Real.exp (δ / 2 * c) * Real.exp (-(δ * c) + 2 * c * √η + 2 * ε * c * A) ≤ 1 := by
    rw [← Real.exp_add, Real.exp_le_one_iff, hsη]
    have : 2 * ε * c * A ≤ 2 * (δ / 8) * c * 1 :=
      mul_le_mul (mul_le_mul_of_nonneg_right (by linarith) hc0.le) hA1 hA0 (by positivity)
    nlinarith
  have hP : 0 ≤ 50 * (1 + c ^ 2) ^ 2 := by positivity
  calc Real.exp (-(2 * c * A) - δ * c) * I ≤ Real.exp (-(2 * c * A) - δ * c) * (50 * (1 + c ^ 2) ^ 2 * Y ^ 2) :=
        mul_le_mul_of_nonneg_left hI (Real.exp_pos _).le
    _ ≤ Real.exp (-(2 * c * A) - δ * c) * (50 * (1 + c ^ 2) ^ 2 *
          (Ya ^ 2 * Real.exp (2 * (c * √η + (1 + ε) * c * A + 2)))) := by gcongr
    _ = Ya ^ 2 * (50 * (1 + c ^ 2) ^ 2 * (Real.exp (-(2 * c * A) - δ * c) *
          Real.exp (2 * (c * √η + (1 + ε) * c * A + 2)))) := by ring
    _ = Ya ^ 2 * (50 * (1 + c ^ 2) ^ 2 * Real.exp 4 * Real.exp (-(δ * c) + 2 * c * √η + 2 * ε * c * A)) := by
        rw [hE]; ring
    _ ≤ Ya ^ 2 * (Real.exp (δ / 2 * c) * Real.exp (-(δ * c) + 2 * c * √η + 2 * ε * c * A)) := by gcongr
    _ ≤ Ya ^ 2 * 1 := by gcongr
    _ = Ya ^ 2 := mul_one _

/-- **The window case**: at an even level `σ = c²θ²` with `½ + ρ < θ`, `0 < ρ ≤ 1/10`, `c²ρ³ ≥ 50` and
`16(1 + c²) ≤ e^{δc}`, some `a ∈ [½, ½ + ρ/2]` has `e^{−δc}∫_0^1 y² ≤ y(a)²`. -/
theorem window_case {c σ θ ρ δ : ℝ} (hc : 1 ≤ c) (hθ : 1 / 2 + ρ < θ) (hθ3 : θ ^ 2 ≤ 3 / 4)
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

/-- **The endpoint amplitude** (eq-cpb Lemma 9) holds. -/
theorem ampFloor : Cvs.Prolate.Gram.DeepCellFloorAmplitude.AmpFloor := by
  intro ρ hρ δ hδ
  set ρ' := min ρ (1 / 10) with hρ'
  have hρ'0 : 0 < ρ' := lt_min hρ (by norm_num)
  have hρ'1 : ρ' ≤ 1 / 10 := min_le_right _ _
  have hρ'ρ : ρ' ≤ ρ := min_le_left _ _
  set ε := min (δ / 8) 1 with hε
  have hε0 : 0 < ε := lt_min (by positivity) one_pos
  have hε1 : ε ≤ 1 := min_le_right _ _
  have hεδ : ε ≤ δ / 8 := min_le_left _ _
  set η := (δ / 8) ^ 2 with hη
  have hη0 : 0 < η := by positivity
  have hsη : √η = δ / 8 := by rw [hη, Real.sqrt_sq (by positivity)]
  have hc : Tendsto (fun x : ℕ => 2 * π * (x : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity)
  filter_upwards [Cvs.Route.Visibility.LayerFloorDeepRemainderB.eventually_scale, hc.eventually_ge_atTop (1 / (ε ^ 2 * η ^ 3)),
    hc.eventually_ge_atTop (50 / ρ' ^ 3), eventually_pow_le_exp (200 * Real.exp 4) (k := δ / 2) (by positivity) 4,
    eventually_pow_le_exp 32 (k := δ) hδ 2] with x hx hcη hcρ hpoly hpoly2
  intro j hj
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
  have hθ3 : √(Cvs.Prolate.Gram.ProlateCellGramHalfUnit.levT x j) ^ 2 ≤ 3 / 4 := by rw [hθ2]; exact hj
  have hint_pos : 0 < ∫ s in (0 : ℝ)..1, regSol (sqC (2 * π * x)) (Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.chi x j) s ^ 2 := by
    simpa [Cvs.Prolate.Gram.DirichletDualFloorShifted.dirMass] using Cvs.Prolate.Gram.DirichletDualFloorShifted.dirMass_pos (2 * π * x) (Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.chi x j) (a := 0) (by norm_num) (by norm_num)
  have hnorm : ∀ a ∈ Icc (0 : ℝ) 1, Cvs.Prolate.Gram.ProlateCellGramHalfUnit.cellFun x j a ^ 2 =
      regSol (sqC (2 * π * x)) (Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.chi x j) a ^ 2 /
        ∫ s in (0 : ℝ)..1, regSol (sqC (2 * π * x)) (Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.chi x j) s ^ 2 :=
    fun a ha => by rw [eq_div_iff hint_pos.ne']; exact cellFun_sq_mul hx j ha
  rcases le_or_gt (√(Cvs.Prolate.Gram.ProlateCellGramHalfUnit.levT x j)) (1 / 2 + ρ') with hθa | hθa
  · refine ⟨1 / 2 + ρ', ⟨by linarith, by linarith⟩, ?_⟩
    have hw : (2 * π * x) ^ 4 ≤ ε ^ 2 * ((2 * π * x) ^ 2 * η) ^ 3 := by
      rw [div_le_iff₀ (by positivity)] at hcη
      have h1 : 1 ≤ ε ^ 2 * η ^ 3 * (2 * π * x) ^ 2 := by nlinarith
      have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ (2 * π * x) ^ 4)
      nlinarith
    have hpoly' : 50 * (1 + (2 * π * x) ^ 2) ^ 2 * Real.exp 4 ≤ Real.exp (δ / 2 * (2 * π * x)) := by
      have h1 : (1 + (2 * π * (x : ℝ)) ^ 2) ^ 2 ≤ 4 * (2 * π * x) ^ 4 := by
        nlinarith [sq_nonneg ((2 * π * (x : ℝ)) ^ 2 - 1)]
      have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 50 * Real.exp 4)
      nlinarith [Real.exp_pos 4]
    have key := turning_case (c := 2 * π * x) (by linarith) (Real.sqrt_nonneg _) hθ3 hσθ hθa (by linarith) hδ hη0
      hsη hε0 hε1 hεδ hw hpoly'
    have hAeq : Cvs.Prolate.Gram.DeepCellFloorAmplitude.agmonInt (Cvs.Prolate.Gram.ProlateCellGramHalfUnit.levT x j) (1 / 2 + ρ') =
        ∫ t in √(Cvs.Prolate.Gram.ProlateCellGramHalfUnit.levT x j)..(1 / 2 + ρ'), √(t ^ 2 - √(Cvs.Prolate.Gram.ProlateCellGramHalfUnit.levT x j) ^ 2) / √(1 - t ^ 2) := by
      rw [Cvs.Prolate.Gram.DeepCellFloorAmplitude.agmonInt, hθ2]
    rw [hnorm _ ⟨by linarith, by linarith⟩, le_div_iff₀ hint_pos, hAeq]
    exact key
  · have hcρ' : 50 ≤ (2 * π * x) ^ 2 * ρ' ^ 3 := by
      rw [div_le_iff₀ (by positivity)] at hcρ
      have h1 : (2 * π * (x : ℝ)) * ρ' ^ 3 ≤ (2 * π * x) ^ 2 * ρ' ^ 3 := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        rw [sq]; exact le_mul_of_one_le_left hc0.le hc1
      linarith
    have hp2 : 16 * (1 + (2 * π * x) ^ 2) ≤ Real.exp (δ * (2 * π * x)) := by
      have h1 : 1 ≤ (2 * π * (x : ℝ)) ^ 2 := one_le_pow₀ hc1
      linarith
    obtain ⟨a, ha, key⟩ := window_case (c := 2 * π * x) hc1 hθa hθ3 hσθ hev hρ'0 hρ'1 hcρ' hp2
    refine ⟨a, ⟨ha.1, ha.2.trans (by linarith)⟩, ?_⟩
    have ha0 : 0 ≤ a := by linarith [ha.1]
    have hag : Cvs.Prolate.Gram.DeepCellFloorAmplitude.agmonInt (Cvs.Prolate.Gram.ProlateCellGramHalfUnit.levT x j) a = 0 := by
      rw [Cvs.Prolate.Gram.DeepCellFloorAmplitude.agmonInt, intervalIntegral.integral_symm,
        Cvs.Prolate.Gram.DeepCellFloorAmplitude.integral_zero_of_le (by linarith [ha.2]) (by rw [hθ2]) ha0, neg_zero]
    rw [hnorm a ⟨ha0, by linarith [ha.2]⟩, le_div_iff₀ hint_pos, hag, mul_zero, neg_zero, zero_sub]
    exact key

/-- **The deep cell floor from the discrete potential alone.** -/
theorem deepCellFloor_of_potFloor (hP : Cvs.Prolate.Gram.DeepCellFloorAmplitude.PotFloor) : Cvs.Prolate.Gram.DeepRemainderCellFloors.DeepCellFloor :=
  Cvs.Prolate.Gram.DeepCellFloorAmplitude.deepCellFloor_of_amp_pot ampFloor hP

end Cvs.Prolate.Gram.EndpointAmplitudeFloor

end
