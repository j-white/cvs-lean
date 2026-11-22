import Mathlib
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.L2a.AngularProlateTailPositive
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.Gram.CentralSquareInverseForm
import Cvs.Prolate.Gram.FullTwistOuterCell
import Cvs.Prolate.Gram.InverseFormConvexSplit
import Cvs.Prolate.Gram.ProlateCellGramHalfUnit

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The per-rung inverse bound from the norm of the central transform

If the central transform satisfies `‖Sz‖² ≤ σ‖z‖²` on `[−½, ½]` with `0 ≤ σ < 1`, then on a single rung
`b = α(√λ_j h_j + S h_j)`, so completing the square in `z` gives `invForm x (α e_j) z ≤ α²(1 + 2/(1 − σ))`, and
`invForm x 0 z ≤ 0`. The norm bound with `σ = 1 − e^{−πx}` is the Slepian–Fuchs asymptotics
`1 − λ₀(c′) ∼ 4√(πc′)e^{−2c′}` at `c′ = πx/2`, taken as the hypothesis `CentralGapFrom`.
-/

noncomputable section

open Real Filter Finset Set MeasureTheory
open Cvs.ZeroCounting
open Cvs.Prolate.Gram.ProlateCellGramHalfUnit (lam levT)
open Cvs.Prolate.Gram.FullTwistOuterCell (rungSum)
open Cvs.L2a.AngularProlateTailPositive (psi)
open Cvs.Prolate.Gram.CentralSquareInverseForm (cut centralT invForm InverseBound)

namespace Cvs.Prolate.Gram.CentralTransformInverseBound
open Cvs.ZeroCounting

/-- **The central gap** `σ`: `∫_{−½}^{½} (Sz)² ≤ σ ∫_{−½}^{½} z²` for every `z` continuous on `[−½, ½]`. -/
def CentralGap (x : ℕ) (σ : ℝ) : Prop :=
  ∀ z : ℝ → ℝ, ContinuousOn z (Icc (-(1 / 2)) (1 / 2)) →
    ∫ t in (-(1 / 2 : ℝ))..(1 / 2), centralT x z t ^ 2 ≤ σ * ∫ t in (-(1 / 2 : ℝ))..(1 / 2), z t ^ 2

/-- **The Slepian–Fuchs gap at `c′ = πx/2`** (Fuchs, J. Math. Anal. Appl. 9 (1964) 317–330; Slepian, J. Math. Phys.
44 (1965) 99–140: `1 − λ₀(c′) ∼ 4√(πc′)e^{−2c′}`): eventually `CentralGap x (1 − e^{−πx})`. -/
def CentralGapFrom : Prop := ∀ᶠ x : ℕ in atTop, CentralGap x (1 - Real.exp (-(π * x)))

/-- The central transform of a function continuous on `[−½, ½]` is continuous. -/
theorem continuous_centralT (x : ℕ) {z : ℝ → ℝ} (hz : ContinuousOn z (Icc (-(1 / 2)) (1 / 2))) :
    Continuous (centralT x z) := by
  have hi : Integrable (cut z) := (integrable_indicator_iff measurableSet_Icc).2 (hz.integrableOn_Icc)
  exact continuous_const.mul (Cvs.Prolate.Gram.InverseFormConvexSplit.continuous_psi_of_intervalIntegrable (hi.intervalIntegrable))

/-- A single rung combination is the scaled rung. -/
theorem rungSum_single (x : ℕ) (j : Fin x) (α u : ℝ) :
    rungSum x (Pi.single j α) u = α * Cvs.Prolate.EvenRungsByIndex.rung (2 * π * x) (2 * (j : ℕ)) u := by
  simp only [rungSum, Pi.single_apply]
  rw [Finset.sum_eq_single j (fun b _ hb => by simp [hb]) (by simp)]
  simp

/-- On `[−1, 1]` the cross-term vector of a single rung is `b = α(√λ_j h_j + S h_j)`. -/
theorem bv_single {x : ℕ} (hx : 80 ≤ 2 * π * x) (j : Fin x) (α : ℝ) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    Cvs.Prolate.Gram.InverseFormConvexSplit.bv x (Pi.single j α) t
      = α * (√(lam x j) * Cvs.Prolate.EvenRungsByIndex.rung (2 * π * x) (2 * (j : ℕ)) t
        + centralT x (Cvs.Prolate.EvenRungsByIndex.rung (2 * π * x) (2 * (j : ℕ))) t) := by
  set h := Cvs.Prolate.EvenRungsByIndex.rung (2 * π * x) (2 * (j : ℕ))
  have hi : IntervalIntegrable h volume (-1) 1 := Cvs.Approximant.DeepIndexSpineSpan.intervalIntegrable_rung _ _
  have e : Cvs.Prolate.Gram.InverseFormConvexSplit.prof x (Pi.single j α) = fun u => α * h u + α * cut h u := by
    funext u
    simp only [Cvs.Prolate.Gram.InverseFormConvexSplit.prof, cut, Set.indicator_apply, rungSum_single]
    split_ifs <;> ring
  rw [Cvs.Prolate.Gram.InverseFormConvexSplit.bv, e, Cvs.Prolate.Gram.InverseFormConvexSplit.psi_comb hi (Cvs.Prolate.Gram.InverseFormConvexSplit.intervalIntegrable_cut hi), Cvs.Prolate.EvenRungsByIndex.psi_rung (Cvs.Prolate.Gram.ProlateCellGramHalfUnit.exists_level hx j) t ht,
    Cvs.Prolate.Gram.FullTwistOuterCell.sqrt_lam_eq hx j, centralT]
  ring

/-- `∫_{−½}^{½} h_j² ≤ 1`. -/
theorem integral_rung_sq_le (x : ℕ) (j : Fin x) (hx : 80 ≤ 2 * π * x) :
    ∫ t in (-(1 / 2 : ℝ))..(1 / 2), Cvs.Prolate.EvenRungsByIndex.rung (2 * π * x) (2 * (j : ℕ)) t ^ 2 ≤ 1 := by
  have h1 := (Cvs.Prolate.EvenRungsByIndex.rung_spec (Cvs.Prolate.Gram.ProlateCellGramHalfUnit.exists_level hx j)).2.2.2.2.2
  refine le_trans ?_ h1.le
  refine intervalIntegral.integral_mono_interval (by norm_num) (by norm_num) (by norm_num)
    (Filter.Eventually.of_forall fun t => sq_nonneg _) ?_
  exact ((Cvs.Prolate.Gram.ProlateCellGramHalfUnit.continuousOn_rung _ _).pow 2).intervalIntegrable_of_Icc (by norm_num)

/-- The square of `z` integrates to a nonnegative number on `[−½, ½]`. -/
theorem integral_sq_nonneg (z : ℝ → ℝ) : 0 ≤ ∫ t in (-(1 / 2 : ℝ))..(1 / 2), z t ^ 2 :=
  intervalIntegral.integral_nonneg (by norm_num) fun _ _ => sq_nonneg _

/-- **The zero vector**: under a central gap `σ ≤ 1`, `invForm x 0 z ≤ 0` for continuous `z`. -/
theorem invForm_zero_le {x : ℕ} {σ : ℝ} (hσ : σ ≤ 1) (hG : CentralGap x σ) {z : ℝ → ℝ} (hz : Continuous z) :
    invForm x 0 z ≤ 0 := by
  have hS := hG z hz.continuousOn
  have hZ := integral_sq_nonneg z
  have e0 : rungSum x 0 = fun _ => 0 := funext fun u => by simp [rungSum]
  have eb : Cvs.Prolate.Gram.InverseFormConvexSplit.bv x 0 = fun _ => 0 := funext fun t => by
    simp [Cvs.Prolate.Gram.InverseFormConvexSplit.bv, Cvs.Prolate.Gram.InverseFormConvexSplit.prof, e0, cut, psi, Cvs.Prolate.SlepianCommutingRelation.kint]
  rw [Cvs.Prolate.Gram.InverseFormConvexSplit.invForm_eq, e0, eb]
  simp only [dotProduct_zero, zero_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    intervalIntegral.integral_zero, mul_zero, add_zero]
  nlinarith

/-- **The per-rung inverse bound** under a central gap `0 ≤ σ < 1`: `invForm x (α e_j) z ≤ α²(1 + 2/(1 − σ))`. -/
theorem rungInverseBound_of_centralGap {x : ℕ} (hx : 80 ≤ 2 * π * x) {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ < 1)
    (hG : CentralGap x σ) (j : Fin x) : Cvs.Prolate.Gram.InverseFormConvexSplit.RungInverseBound x j (1 + 2 / (1 - σ)) := by
  intro α z hz
  set h := Cvs.Prolate.EvenRungsByIndex.rung (2 * π * x) (2 * (j : ℕ))
  set l := lam x j
  have hl0 : 0 ≤ l := Cvs.Prolate.Gram.ProlateCellGramHalfUnit.lam_nonneg x j
  have hl1 : l ≤ 1 := Cvs.Prolate.Gram.ProlateCellGramHalfUnit.lam_le_one hx j.2
  have hhc : ContinuousOn h (Icc (-1) 1) := Cvs.Prolate.Gram.ProlateCellGramHalfUnit.continuousOn_rung _ _
  have hhalf : ContinuousOn h (Icc (-(1 / 2)) (1 / 2)) :=
    hhc.mono fun u hu => ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hSh := continuous_centralT x hhalf
  have hsub : ∀ t ∈ Icc (-(1 / 2) : ℝ) (1 / 2), t ∈ Icc (-1 : ℝ) 1 := fun t ht =>
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hd : 0 < 1 - σ := by linarith
  set P := ∫ t in (-(1 / 2 : ℝ))..(1 / 2), h t ^ 2
  set Z := ∫ t in (-(1 / 2 : ℝ))..(1 / 2), z t ^ 2
  set B := ∫ t in (-(1 / 2 : ℝ))..(1 / 2), Cvs.Prolate.Gram.InverseFormConvexSplit.bv x (Pi.single j α) t ^ 2
  set X := ∫ t in (-(1 / 2 : ℝ))..(1 / 2), Cvs.Prolate.Gram.InverseFormConvexSplit.bv x (Pi.single j α) t * z t
  have hP1 : P ≤ 1 := integral_rung_sq_le x j hx
  have hP0 : 0 ≤ P := integral_sq_nonneg h
  have hZ0 : 0 ≤ Z := integral_sq_nonneg z
  have hbv := Cvs.Prolate.Gram.InverseFormConvexSplit.continuous_bv x (Pi.single j α)
  have hII : ∀ {f : ℝ → ℝ}, Continuous f → IntervalIntegrable f volume (-(1 / 2)) (1 / 2) :=
    fun hf => hf.intervalIntegrable _ _
  have hIh : IntervalIntegrable (fun t => h t ^ 2) volume (-(1 / 2)) (1 / 2) :=
    (hhalf.pow 2).intervalIntegrable_of_Icc (by norm_num)
  -- the cross term by completing the square
  have hX : 2 * X ≤ B / (1 - σ) + (1 - σ) * Z := by
    have i1 : IntervalIntegrable (fun t => Cvs.Prolate.Gram.InverseFormConvexSplit.bv x (Pi.single j α) t ^ 2 / (1 - σ)) volume (-(1 / 2)) (1 / 2) :=
      hII ((hbv.pow 2).div_const _)
    have i2 : IntervalIntegrable (fun t => (1 - σ) * z t ^ 2) volume (-(1 / 2)) (1 / 2) :=
      hII (continuous_const.mul (hz.pow 2))
    have e : B / (1 - σ) + (1 - σ) * Z = ∫ t in (-(1 / 2 : ℝ))..(1 / 2),
        (Cvs.Prolate.Gram.InverseFormConvexSplit.bv x (Pi.single j α) t ^ 2 / (1 - σ) + (1 - σ) * z t ^ 2) := by
      rw [intervalIntegral.integral_add i1 i2, intervalIntegral.integral_div, intervalIntegral.integral_const_mul]
    rw [e, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on (by norm_num) (hII (continuous_const.mul (hbv.mul hz)))
      (hII (((hbv.pow 2).div_const _).add (continuous_const.mul (hz.pow 2)))) fun t _ => ?_
    set b := Cvs.Prolate.Gram.InverseFormConvexSplit.bv x (Pi.single j α) t
    rw [div_add' _ _ _ hd.ne', le_div_iff₀ hd]
    nlinarith [sq_nonneg (b - (1 - σ) * z t)]
  -- the size of the cross-term vector
  have hB : B ≤ 2 * α ^ 2 * (l + σ) * P := by
    have hS := hG h hhalf
    have e : 2 * α ^ 2 * (l + σ) * P ≥ 2 * α ^ 2 * (l * P + ∫ t in (-(1 / 2 : ℝ))..(1 / 2), centralT x h t ^ 2) := by
      have : 0 ≤ 2 * α ^ 2 := by positivity
      nlinarith
    refine le_trans ?_ e
    have e2 : 2 * α ^ 2 * (l * P + ∫ t in (-(1 / 2 : ℝ))..(1 / 2), centralT x h t ^ 2)
        = ∫ t in (-(1 / 2 : ℝ))..(1 / 2), 2 * α ^ 2 * (l * h t ^ 2 + centralT x h t ^ 2) := by
      have i3 : IntervalIntegrable (fun t => centralT x h t ^ 2) volume (-(1 / 2)) (1 / 2) := hII (hSh.pow 2)
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add (hIh.const_mul l) i3,
        intervalIntegral.integral_const_mul]
    rw [e2]
    refine intervalIntegral.integral_mono_on (by norm_num) (hII (hbv.pow 2))
      (((hIh.const_mul l).add (hII (hSh.pow 2))).const_mul _) fun t ht => ?_
    rw [bv_single hx j α (hsub t ht)]
    show (α * (√l * h t + centralT x h t)) ^ 2 ≤ 2 * α ^ 2 * (l * h t ^ 2 + centralT x h t ^ 2)
    have hsl := Real.sq_sqrt hl0
    have e4 : (α * (√l * h t + centralT x h t)) ^ 2
        = 2 * α ^ 2 * (l * h t ^ 2 + centralT x h t ^ 2) - α ^ 2 * (√l * h t - centralT x h t) ^ 2 := by
      linear_combination (2 * α ^ 2 * h t ^ 2) * hsl
    rw [e4]
    linarith [mul_nonneg (sq_nonneg α) (sq_nonneg (√l * h t - centralT x h t))]
  have hSz := hG z hz.continuousOn
  have hdot : (Pi.single j α : Fin x → ℝ) ⬝ᵥ Pi.single j α = α ^ 2 := by
    simp [dotProduct, Pi.single_apply, sq]
  have hrs : (∫ t in (-(1 / 2 : ℝ))..(1 / 2), rungSum x (Pi.single j α) t ^ 2) = α ^ 2 * P := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [rungSum_single]
    ring
  rw [Cvs.Prolate.Gram.InverseFormConvexSplit.invForm_eq, hdot, hrs]
  -- assemble: the `z`-terms cancel exactly
  have hBd : B / (1 - σ) ≤ 2 * α ^ 2 * (l + σ) * P / (1 - σ) := div_le_div_of_nonneg_right hB hd.le
  have hq : 2 * α ^ 2 * (l + σ) * P / (1 - σ) ≤ α ^ 2 * (4 / (1 - σ)) := by
    have e5 : α ^ 2 * (4 / (1 - σ)) * (1 - σ) = 4 * α ^ 2 := by field_simp
    rw [div_le_iff₀ hd, e5]
    have : (l + σ) * P ≤ 2 := by nlinarith
    nlinarith [sq_nonneg α]
  have hfin : α ^ 2 + α ^ 2 * P + 2 * X - Z + ∫ t in (-(1 / 2 : ℝ))..(1 / 2), centralT x z t ^ 2
      ≤ α ^ 2 * (2 + 4 / (1 - σ)) := by
    nlinarith [sq_nonneg α, mul_le_mul_of_nonneg_left hP1 (sq_nonneg α)]
  have e3 : α ^ 2 * (1 + 2 / (1 - σ)) = α ^ 2 * (2 + 4 / (1 - σ)) / 2 := by ring
  rw [e3]
  linarith

/-- **Every rung below the gap at `σ = 1 − e^{−πx}`**: `RungInverseBound x j (1 + 2e^{πx})`. -/
theorem rungInverseBound_exp {x : ℕ} (hx : 80 ≤ 2 * π * x) (hG : CentralGap x (1 - Real.exp (-(π * x))))
    (j : Fin x) : Cvs.Prolate.Gram.InverseFormConvexSplit.RungInverseBound x j (1 + 2 * Real.exp (π * x)) := by
  have he := Real.exp_pos (-(π * x))
  have he1 : Real.exp (-(π * x)) ≤ 1 := Real.exp_le_one_iff.2 (by
    have := Real.pi_pos; have : (0 : ℝ) ≤ x := Nat.cast_nonneg x; nlinarith)
  have h := rungInverseBound_of_centralGap hx (by linarith) (by linarith) hG j
  have e : 1 + 2 / (1 - (1 - Real.exp (-(π * x)))) = 1 + 2 * Real.exp (π * x) := by
    rw [sub_sub_cancel, Real.exp_neg, div_inv_eq_mul]
  rwa [e] at h

end Cvs.Prolate.Gram.CentralTransformInverseBound

end
