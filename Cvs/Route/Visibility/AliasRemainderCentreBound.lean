import Mathlib
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.Approximant.SpineSubspace
import Cvs.L2a.SpectralMassLevelLeak
import Cvs.Prolate.Gram.ProlateCellGramHalfUnit
import Cvs.Route.Visibility.AliasRemainderSplit
import Cvs.Route.Visibility.EvenFirstCellPoisson
import Cvs.Route.Visibility.LayerFloorDeepRemainderB
import Cvs.Route.Visibility.WindowChainCellFloors

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# AL-R from the centre bound (P5) and the alias-tail bound, and the (WF′) threshold at `W̃ = 57/60`

`‖R b‖ ≤ ‖y₂‖ + ‖T₃‖ + ‖Z‖` with `‖y₂‖² ≤ E/4` (Cvs.Route.Visibility.AliasRemainderSplit), `‖Z‖² ≤ E/(πcλ_t)` and `‖T₃‖² ≤ (W̃/2 + C₁/(2c))E` gives
`‖R b‖² ≤ C₀(x)E(b)`, which is `Cvs.Route.Visibility.WindowChainCellFloors.ALR`.  At `W̃ = 57/60` the (WF′) threshold `μ*C₀∞(W̃)/2` is
`(12 − 8√2)(1/2 + √(19/40))²/2 ∈ (0.4852775, 0.4852776)`.
-/

noncomputable section

open Real Set MeasureTheory Filter Topology

namespace Cvs.Route.Visibility.AliasRemainderCentreBound
open Cvs.ZeroCounting

open Cvs.Approximant.DeepIndexSpineSpan (spineG)
open Cvs.Prolate.Gram.ProlateCellGramHalfUnit (energyE lamTop)
open Cvs.Route.Visibility.LayerFloorDeepRemainderB (C0 C0inf muStar eventually_scale)

/-! ### The `L²` triangle inequality in integral form -/

/-- **Minkowski in integral form**: `√∫(f + g)² ≤ √∫f² + √∫g²` for square integrable `f, g`. -/
theorem sqrt_integral_add_sq_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    √(∫ a, (f a + g a) ^ 2 ∂μ) ≤ √(∫ a, f a ^ 2 ∂μ) + √(∫ a, g a ^ 2 ∂μ) := by
  have h1 : ∫ a, (f a + g a) ^ 2 ∂μ ≤ ∫ a, (|f a| + |g a|) ^ 2 ∂μ := by
    refine integral_mono (hf.add hg).integrable_sq (hf.abs.add hg.abs).integrable_sq fun a => ?_
    have := abs_mul_abs_self (f a)
    have := abs_mul_abs_self (g a)
    have : f a * g a ≤ |f a| * |g a| := by rw [← abs_mul]; exact le_abs_self _
    nlinarith
  have h2 := Cvs.L2a.SpectralMassLevelLeak.sqrt_integral_add_sq_le (p := fun a => |f a|) (q := fun a => |g a|) (μ := μ)
    (fun a => abs_nonneg _) (fun a => abs_nonneg _) hf.aestronglyMeasurable.norm hg.aestronglyMeasurable.norm hf.abs.integrable_sq hg.abs.integrable_sq
  simp only [sq_abs] at h2
  exact (Real.sqrt_le_sqrt h1).trans h2

/-- **Minkowski for three terms**: `√∫(f + g + h)² ≤ √∫f² + √∫g² + √∫h²`. -/
theorem sqrt_integral_add3_sq_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g h : α → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) (hh : MemLp h 2 μ) :
    √(∫ a, (f a + g a + h a) ^ 2 ∂μ) ≤ √(∫ a, f a ^ 2 ∂μ) + √(∫ a, g a ^ 2 ∂μ) + √(∫ a, h a ^ 2 ∂μ) := by
  have h1 := sqrt_integral_add_sq_le (hf.add hg) hh
  have h2 := sqrt_integral_add_sq_le hf hg
  simp only [Pi.add_apply] at h1
  linarith

/-! ### The two analytic inputs -/

/-- **P5**: eventually `‖Z‖² = G_b(0)²/(4x) ≤ E(b)/(πcλ_t)` for every spine class `b`, at `c = 2πx`. -/
def ZBound : Prop :=
  ∀ᶠ x : ℕ in atTop, ∀ b : Cvs.Approximant.SpineSubspace.SF x → ℝ,
    spineG (2 * π * x) b 0 ^ 2 / (4 * x) ≤ energyE x b / (π * (2 * π * x) * lamTop x)

/-- **The alias-tail bound**: eventually `‖T₃‖² = ∫_{(1/2,1]}T₃² ≤ (W̃/2 + C₁/(2c))E(b)` for every spine class `b`,
at `c = 2πx`. -/
def AliasTail (Wt C₁ : ℝ) : Prop :=
  ∀ᶠ x : ℕ in atTop, ∀ b : Cvs.Approximant.SpineSubspace.SF x → ℝ,
    ∫ θ in Ioc (1 / 2 : ℝ) 1, Cvs.Route.Visibility.AliasRemainderSplit.aliasTail x b θ ^ 2 ≤ (Wt / 2 + C₁ / (2 * (2 * π * x))) * energyE x b

/-! ### AL-R -/

/-- **AL-R from P5 and the alias-tail bound**: `‖R b‖² ≤ C₀(x)E(b)` eventually. -/
theorem alr_of_aliasTail {Wt C₁ : ℝ} (hZ : ZBound) (hT : AliasTail Wt C₁) : Cvs.Route.Visibility.WindowChainCellFloors.ALR Wt C₁ := by
  filter_upwards [hZ, hT, eventually_scale] with x hz ht hx b
  have hx1 : 1 ≤ x := by have := Cvs.Prolate.Gram.ProlateCellGramHalfUnit.two_le_of_scale hx; omega
  have hE := Cvs.Prolate.Gram.ProlateCellGramHalfUnit.energyE_nonneg hx b
  set E := energyE x b
  set c := 2 * π * (x : ℝ)
  set q := Wt / 2 + C₁ / (2 * c)
  set P := π * c * lamTop x
  have hP : 0 < P := by
    have := Cvs.Prolate.Gram.ProlateCellGramHalfUnit.half_le_lamTop hx
    have : 0 < c := by simp only [c]; linarith
    positivity
  have hsplit : (x : ℝ) * ∫ θ in Ioc (1 / 2 : ℝ) 1, Cvs.Route.Visibility.EvenFirstCellPoisson.cellRem x b θ ^ 2
      = ∫ θ in Ioc (1 / 2 : ℝ) 1, (Cvs.Route.Visibility.AliasRemainderSplit.alias2 x b θ + Cvs.Route.Visibility.AliasRemainderSplit.aliasTail x b θ + Cvs.Route.Visibility.AliasRemainderSplit.zTerm x b θ) ^ 2 := by
    rw [← Cvs.Route.Visibility.WindowChainCellFloors.integral_sqrt_mul_sq]
    simp only [Cvs.Route.Visibility.AliasRemainderSplit.sqrt_mul_cellRem_eq]
  have hM := sqrt_integral_add3_sq_le (Cvs.Route.Visibility.AliasRemainderSplit.memLp_alias2 x b) (Cvs.Route.Visibility.AliasRemainderSplit.memLp_aliasTail hx b)
    (Cvs.Route.Visibility.AliasRemainderSplit.memLp_zTerm x b)
  have hy : √(∫ θ in Ioc (1 / 2 : ℝ) 1, Cvs.Route.Visibility.AliasRemainderSplit.alias2 x b θ ^ 2) ≤ √E * (1 / 2) := by
    refine (Real.sqrt_le_sqrt (Cvs.Route.Visibility.AliasRemainderSplit.integral_alias2_sq_le hx b)).trans_eq ?_
    rw [div_eq_mul_inv, Real.sqrt_mul' _ (by norm_num), show (4 : ℝ)⁻¹ = (1 / 2) ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
  have hT3 : √(∫ θ in Ioc (1 / 2 : ℝ) 1, Cvs.Route.Visibility.AliasRemainderSplit.aliasTail x b θ ^ 2) ≤ √E * √q := by
    refine (Real.sqrt_le_sqrt (ht b)).trans_eq ?_
    rw [Real.sqrt_mul' _ hE, mul_comm]
  have hz' : √(∫ θ in Ioc (1 / 2 : ℝ) 1, Cvs.Route.Visibility.AliasRemainderSplit.zTerm x b θ ^ 2) ≤ √E * (1 / √P) := by
    rw [Cvs.Route.Visibility.AliasRemainderSplit.integral_zTerm_sq hx1]
    refine (Real.sqrt_le_sqrt (hz b)).trans_eq ?_
    rw [Real.sqrt_div hE, div_eq_mul_one_div]
  have hK : 0 ≤ √E * (1 / 2 + √q + 1 / √P) := by positivity
  have hle : √((x : ℝ) * ∫ θ in Ioc (1 / 2 : ℝ) 1, Cvs.Route.Visibility.EvenFirstCellPoisson.cellRem x b θ ^ 2)
      ≤ √E * (1 / 2 + √q + 1 / √P) := by
    rw [hsplit]; linarith
  have h0 : 0 ≤ (x : ℝ) * ∫ θ in Ioc (1 / 2 : ℝ) 1, Cvs.Route.Visibility.EvenFirstCellPoisson.cellRem x b θ ^ 2 :=
    mul_nonneg (Nat.cast_nonneg _) (setIntegral_nonneg measurableSet_Ioc fun _ _ => sq_nonneg _)
  calc (x : ℝ) * ∫ θ in Ioc (1 / 2 : ℝ) 1, Cvs.Route.Visibility.EvenFirstCellPoisson.cellRem x b θ ^ 2
      = √((x : ℝ) * ∫ θ in Ioc (1 / 2 : ℝ) 1, Cvs.Route.Visibility.EvenFirstCellPoisson.cellRem x b θ ^ 2) ^ 2 := (Real.sq_sqrt h0).symm
    _ ≤ (√E * (1 / 2 + √q + 1 / √P)) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hle 2
    _ = C0 Wt C₁ x * E := by
        rw [mul_pow, Real.sq_sqrt hE, C0, mul_comm]

/-! ### The (WF′) threshold at `W̃ = 57/60` -/

/-- `C₀∞(57/60) = (1/2 + √(19/40))²`. -/
theorem C0inf_57_60 : C0inf (57 / 60) = (1 / 2 + √(19 / 40)) ^ 2 := by
  rw [C0inf]; norm_num

/-- **The (WF′) threshold at `W̃ = 57/60`**: `0.4852775 < μ*C₀∞(57/60)/2 < 0.4852776`. -/
theorem threshold_57_60_mem : 4852775 / 10000000 < muStar * C0inf (57 / 60) / 2 ∧
    muStar * C0inf (57 / 60) / 2 < 4852776 / 10000000 := by
  rw [C0inf_57_60, muStar]
  have ha1 : (1414213562 / 1000000000 : ℝ) < √2 := Real.lt_sqrt (by norm_num) |>.2 (by norm_num)
  have ha2 : √2 < (1414213563 / 1000000000 : ℝ) := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  have hb1 : (6892024376 / 10000000000 : ℝ) < √(19 / 40) := Real.lt_sqrt (by norm_num) |>.2 (by norm_num)
  have hb2 : √(19 / 40) < (6892024377 / 10000000000 : ℝ) := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  set a := √2
  set b := √(19 / 40)
  have hu1 : (1 / 2 + 6892024376 / 10000000000 : ℝ) ^ 2 < (1 / 2 + b) ^ 2 := by gcongr
  have hu2 : (1 / 2 + b) ^ 2 < (1 / 2 + 6892024377 / 10000000000 : ℝ) ^ 2 := by gcongr
  have hm1 : (12 - 8 * (1414213563 / 1000000000) : ℝ) < 12 - 8 * a := by linarith
  have hm2 : 12 - 8 * a < (12 - 8 * (1414213562 / 1000000000) : ℝ) := by linarith
  constructor
  · have := mul_lt_mul'' hm1 hu1 (by norm_num) (by norm_num)
    linarith
  · have := mul_lt_mul'' hm2 hu2 (by linarith) (by positivity)
    linarith

end Cvs.Route.Visibility.AliasRemainderCentreBound
