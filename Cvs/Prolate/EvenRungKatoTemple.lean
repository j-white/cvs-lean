import Mathlib
import Cvs.Prolate.EvenRungDavisKahan
import Cvs.Prolate.EvenRungParseval
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.HermiteTrialResiduals

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Kato–Temple for the even rungs: `χ₀ = c − 3/4 + O(1/c)`, `χ₄ = 9c − 43/4 + O(1/c)`

With `a_k = ∫ F h_k`, the Green identity `(χ_k − μ)a_k = ∫ R h_k` gives `Σ (χ_k − μ)a_k² = ∫ F R`. If the other
levels are `δ` from `μ`, then `|χ_k − μ|(∫F² − ∫R²/δ²) ≤ |∫ F R| + ∫R²/δ`. For the Hermite trials `∫_ℝ F R = 0`.
-/

noncomputable section

open Real Set MeasureTheory Filter Polynomial
open scoped Interval

namespace Cvs.Prolate.EvenRungKatoTemple
open Cvs.ZeroCounting

open Cvs.Prolate.EvenRungsByIndex (IsLevelIdx lev rung rung_spec lev_spec lev_eq)
open Cvs.Prolate.EvenRungParseval (LevelIdx)
open Cvs.Prolate.HermiteTrialResiduals (pg pg₁ pg₂ herm rq mu kap2 gE)

/-! ### Weighted sums -/

section Sums

variable {ι : Type*} {a χ : ι → ℝ} {A B M μ : ℝ}

/-- **Kato–Temple for weighted sums.** If `Σ aᵢ² = A`, `Σ (χᵢ − μ)² aᵢ² = B`, `Σ (χᵢ − μ) aᵢ² = M` and every
`i ≠ i₀` has `δ ≤ |χᵢ − μ|`, then `|χ_{i₀} − μ| (A − B/δ²) ≤ |M| + B/δ`. -/
theorem abs_sub_mul_le (ha : HasSum (fun i => a i ^ 2) A)
    (hb : HasSum (fun i => (χ i - μ) ^ 2 * a i ^ 2) B) (hm : HasSum (fun i => (χ i - μ) * a i ^ 2) M)
    {i₀ : ι} {δ : ℝ} (hδ : 0 < δ) (hgap : ∀ i, i ≠ i₀ → δ ≤ |χ i - μ|) :
    |χ i₀ - μ| * (A - B / δ ^ 2) ≤ |M| + B / δ := by
  classical
  have hdk := Cvs.Prolate.EvenRungDavisKahan.sq_mul_sub_sq_le ha hb hδ.le hgap
  have ha0 : A - B / δ ^ 2 ≤ a i₀ ^ 2 := by
    rw [sub_le_iff_le_add, ← sub_le_iff_le_add', div_eq_mul_inv]
    have hδ2 : 0 < δ ^ 2 := by positivity
    rw [le_mul_inv_iff₀ hδ2]
    linarith
  -- the off-diagonal part of `M` is at most `B/δ` in absolute value
  set f := fun i => (χ i - μ) * a i ^ 2
  set g := fun i => (χ i - μ) ^ 2 * a i ^ 2 / δ
  have hg : HasSum g (B / δ) := hb.div_const δ
  have hfu := hm.update i₀ 0
  have hgu := hg.update i₀ 0
  have hpt : ∀ i, |Function.update f i₀ 0 i| ≤ Function.update g i₀ 0 i := by
    intro i
    by_cases hi : i = i₀
    · subst hi; simp
    · rw [Function.update_of_ne hi, Function.update_of_ne hi]
      simp only [f, g, abs_mul, abs_of_nonneg (sq_nonneg (a i))]
      have h1 := hgap i hi
      rw [le_div_iff₀ hδ, ← sq_abs (χ i - μ)]
      have : |χ i - μ| * δ ≤ |χ i - μ| ^ 2 := by nlinarith [abs_nonneg (χ i - μ)]
      nlinarith [sq_nonneg (a i)]
  have hup := hasSum_le (fun i => (abs_le.mp (hpt i)).2) hfu hgu
  have hlo := hasSum_le (fun i => (abs_le.mp (hpt i)).1) (hgu.neg) hfu
  have hgi : 0 ≤ g i₀ := by simp only [g]; positivity
  have hfi : |f i₀| ≤ |M| + B / δ := by
    have : |M - f i₀| ≤ B / δ - g i₀ := abs_le.mpr ⟨by linarith, by linarith⟩
    calc |f i₀| = |M - (M - f i₀)| := by ring_nf
      _ ≤ |M| + |M - f i₀| := abs_sub _ _
      _ ≤ |M| + B / δ := by linarith
  have hfa : |f i₀| = |χ i₀ - μ| * a i₀ ^ 2 := by
    simp only [f, abs_mul, abs_of_nonneg (sq_nonneg (a i₀))]
  calc |χ i₀ - μ| * (A - B / δ ^ 2) ≤ |χ i₀ - μ| * a i₀ ^ 2 :=
        mul_le_mul_of_nonneg_left ha0 (abs_nonneg _)
    _ = |f i₀| := hfa.symm
    _ ≤ |M| + B / δ := hfi

end Sums

/-! ### The Green identity, summed -/

section Green

variable {c μ : ℝ} {F F₁ F₂ R : ℝ → ℝ}

/-- **Parseval for products**: `Σ_k (∫ F h_k)(∫ R h_k) = ∫ F R` for continuous even `F`, `R`. -/
theorem hasSum_mul_integral (hc : c ≠ 0) (hF : ContinuousOn F (Icc (-1) 1))
    (hR : ContinuousOn R (Icc (-1) 1)) (hFe : ∀ s ∈ Icc (-1 : ℝ) 1, F (-s) = F s)
    (hRe : ∀ s ∈ Icc (-1 : ℝ) 1, R (-s) = R s) :
    HasSum (fun k : LevelIdx c => (∫ s in (-1 : ℝ)..1, F s * rung c k s) * ∫ s in (-1 : ℝ)..1, R s * rung c k s)
      (∫ s in (-1 : ℝ)..1, F s * R s) := by
  have hp := Cvs.Prolate.EvenRungParseval.hasSum_sq_integral_mul_rung hc (hF.add hR)
    (fun s hs => by simp only [Pi.add_apply, hFe s hs, hRe s hs])
  have hm := Cvs.Prolate.EvenRungParseval.hasSum_sq_integral_mul_rung hc (hF.sub hR)
    (fun s hs => by simp only [Pi.sub_apply, hFe s hs, hRe s hs])
  have hFu : ContinuousOn F [[(-1 : ℝ), 1]] := by rwa [uIcc_of_le (by norm_num)]
  have hRu : ContinuousOn R [[(-1 : ℝ), 1]] := by rwa [uIcc_of_le (by norm_num)]
  have iF : IntervalIntegrable F volume (-1) 1 := hFu.intervalIntegrable
  have iR : IntervalIntegrable R volume (-1) 1 := hRu.intervalIntegrable
  have key := (hp.sub hm).div_const 4
  have hfun : (fun k : LevelIdx c => (∫ s in (-1 : ℝ)..1, F s * rung c k s) * ∫ s in (-1 : ℝ)..1, R s * rung c k s)
      = fun k : LevelIdx c => ((∫ s in (-1 : ℝ)..1, (F + R) s * rung c k s) ^ 2
          - (∫ s in (-1 : ℝ)..1, (F - R) s * rung c k s) ^ 2) / 4 := by
    funext k
    have hh : ContinuousOn (rung c k) [[(-1 : ℝ), 1]] := by
      rw [uIcc_of_le (by norm_num)]; exact Cvs.Prolate.EvenRungsByIndex.continuousOn_rung k.2
    have i1 : IntervalIntegrable (fun s => F s * rung c k s) volume (-1) 1 :=
      (hFu.mul hh).intervalIntegrable
    have i2 : IntervalIntegrable (fun s => R s * rung c k s) volume (-1) 1 :=
      (hRu.mul hh).intervalIntegrable
    simp only [Pi.add_apply, Pi.sub_apply, add_mul, sub_mul]
    rw [intervalIntegral.integral_add i1 i2, intervalIntegral.integral_sub i1 i2]
    ring
  have hval : (∫ s in (-1 : ℝ)..1, F s * R s)
      = ((∫ s in (-1 : ℝ)..1, (F + R) s ^ 2) - ∫ s in (-1 : ℝ)..1, (F - R) s ^ 2) / 4 := by
    have i1 : IntervalIntegrable (fun s => F s ^ 2) volume (-1) 1 := (hFu.pow 2).intervalIntegrable
    have i2 : IntervalIntegrable (fun s => R s ^ 2) volume (-1) 1 := (hRu.pow 2).intervalIntegrable
    have i3 : IntervalIntegrable (fun s => F s * R s) volume (-1) 1 := (hFu.mul hRu).intervalIntegrable
    have e1 : (fun s => (F + R) s ^ 2) = fun s => F s ^ 2 + 2 * (F s * R s) + R s ^ 2 := by
      funext s; simp only [Pi.add_apply]; ring
    have e2 : (fun s => (F - R) s ^ 2) = fun s => F s ^ 2 - 2 * (F s * R s) + R s ^ 2 := by
      funext s; simp only [Pi.sub_apply]; ring
    rw [e1, e2, intervalIntegral.integral_add (i1.add (i3.const_mul 2)) i2,
      intervalIntegral.integral_add i1 (i3.const_mul 2), intervalIntegral.integral_add
        (i1.sub (i3.const_mul 2)) i2, intervalIntegral.integral_sub i1 (i3.const_mul 2),
      intervalIntegral.integral_const_mul]
    ring
  rw [hfun, hval]
  exact key

/-- **The first moment of the levels**: `Σ_k (χ_k − μ)(∫ F h_k)² = ∫ F R`. -/
theorem hasSum_sub_mul_sq (hc : c ≠ 0) (hF : ∀ s ∈ [[(-1 : ℝ), 1]], HasDerivAt F (F₁ s) s)
    (hF₁ : ∀ s ∈ [[(-1 : ℝ), 1]], HasDerivAt F₁ (F₂ s) s) (hF₂ : ContinuousOn F₂ [[(-1 : ℝ), 1]])
    (hode : ∀ s ∈ [[(-1 : ℝ), 1]],
      (1 - s ^ 2) * F₂ s - 2 * s * F₁ s - c ^ 2 * s ^ 2 * F s + μ * F s = -R s)
    (hFe : ∀ s ∈ Icc (-1 : ℝ) 1, F (-s) = F s) (hRe : ∀ s ∈ Icc (-1 : ℝ) 1, R (-s) = R s) :
    HasSum (fun k : LevelIdx c => (lev c k - μ) * (∫ s in (-1 : ℝ)..1, F s * rung c k s) ^ 2)
      (∫ s in (-1 : ℝ)..1, F s * R s) := by
  have hFc : ContinuousOn F (Icc (-1) 1) := by
    rw [← uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    exact fun s hs => (hF s hs).continuousAt.continuousWithinAt
  have hRc : ContinuousOn R (Icc (-1) 1) := by
    rw [← uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    exact Cvs.Prolate.EvenRungDavisKahan.continuousOn_of_ode hF hF₁ hF₂ hode
  convert hasSum_mul_integral hc hFc hRc hFe hRe using 1
  funext k
  rw [← Cvs.Prolate.EvenRungDavisKahan.sub_mul_integral_mul_rung k.2 hF hF₁ hF₂ hode]
  ring

/-- **Kato–Temple for the rungs**: if every even level other than `χ_k` is at least `δ > 0` from `μ`, then
`|χ_k − μ| (∫ F² − ∫ R²/δ²) ≤ |∫ F R| + ∫ R²/δ`. -/
theorem abs_lev_sub_mul_le (hc : c ≠ 0) (hF : ∀ s ∈ [[(-1 : ℝ), 1]], HasDerivAt F (F₁ s) s)
    (hF₁ : ∀ s ∈ [[(-1 : ℝ), 1]], HasDerivAt F₁ (F₂ s) s) (hF₂ : ContinuousOn F₂ [[(-1 : ℝ), 1]])
    (hode : ∀ s ∈ [[(-1 : ℝ), 1]],
      (1 - s ^ 2) * F₂ s - 2 * s * F₁ s - c ^ 2 * s ^ 2 * F s + μ * F s = -R s)
    (hFe : ∀ s ∈ Icc (-1 : ℝ) 1, F (-s) = F s) (hRe : ∀ s ∈ Icc (-1 : ℝ) 1, R (-s) = R s)
    {k : ℕ} (hk : ∃ χ, IsLevelIdx c k χ) {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ j χ, IsLevelIdx c j χ → j ≠ k → δ ≤ |χ - μ|) :
    |lev c k - μ| * ((∫ s in (-1 : ℝ)..1, F s ^ 2) - (∫ s in (-1 : ℝ)..1, R s ^ 2) / δ ^ 2)
      ≤ |∫ s in (-1 : ℝ)..1, F s * R s| + (∫ s in (-1 : ℝ)..1, R s ^ 2) / δ := by
  have hFc : ContinuousOn F (Icc (-1) 1) := by
    rw [← uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    exact fun s hs => (hF s hs).continuousAt.continuousWithinAt
  exact abs_sub_mul_le (a := fun k : LevelIdx c => ∫ s in (-1 : ℝ)..1, F s * rung c k s)
    (χ := fun k => lev c k) (i₀ := (⟨k, hk⟩ : LevelIdx c))
    (Cvs.Prolate.EvenRungParseval.hasSum_sq_integral_mul_rung hc hFc hFe)
    (Cvs.Prolate.EvenRungDavisKahan.hasSum_sq_sub_mul_sq hc hF hF₁ hF₂ hode hRe)
    (hasSum_sub_mul_sq hc hF hF₁ hF₂ hode hFe hRe) hδ
    fun j hj => hgap j (lev c j) (lev_spec j.2) fun h => hj (Subtype.ext h)

end Green

/-! ### The Hermite trials are orthogonal to their residuals -/

section Trials

variable {c : ℝ} {m : ℕ}

theorem pg_mul (c : ℝ) (Q Q' : ℝ[X]) (w : ℝ) :
    pg c Q w * pg c Q' w = (Q * Q').eval (c * w ^ 2) * exp (-c * w ^ 2) := by
  simp only [pg, eval_mul]
  rw [show (Q.eval (c * w ^ 2) * exp (-(c / 2) * w ^ 2)) * (Q'.eval (c * w ^ 2) * exp (-(c / 2) * w ^ 2))
      = Q.eval (c * w ^ 2) * Q'.eval (c * w ^ 2) * (exp (-(c / 2) * w ^ 2) * exp (-(c / 2) * w ^ 2)) by ring,
    ← exp_add]
  congr 2
  ring

theorem gE_herm_mul_rq_zero (r : ℝ) : gE r (herm 0 * rq 0) = 3 / 4 * r ^ 2 - 3 / 2 * r + 3 / 4 := by
  rw [Cvs.Prolate.HermiteTrialResiduals.gE_eq_of_eval (Finset.range 3) (fun k => ([3 / 4, -3, 1] : List ℝ).getD k 0)
    (fun t => by simp [rq, herm, Finset.sum_range_succ, Nat.descFactorial]; ring)]
  simp [Cvs.Prolate.HermiteTrialResiduals.gm, Finset.sum_range_succ, Nat.factorial]; ring

theorem gE_herm_mul_rq_two (r : ℝ) : gE r (herm 2 * rq 2) =
    41580 * r ^ 6 - 128520 * r ^ 5 + 160020 * r ^ 4 - 105840 * r ^ 3 + 39348 * r ^ 2 - 8136 * r + 1548 := by
  rw [Cvs.Prolate.HermiteTrialResiduals.gE_eq_of_eval (Finset.range 7)
    (fun k => ([1548, -16272, 52464, -56448, 24384, -4352, 256] : List ℝ).getD k 0)
    (fun t => by simp [rq, herm, Finset.sum_range_succ, Nat.descFactorial]; ring)]
  simp [Cvs.Prolate.HermiteTrialResiduals.gm, Finset.sum_range_succ, Nat.factorial]; ring

/-- **The trial is orthogonal to its residual over `ℝ`**: `∫_ℝ F_{2m} R_{2m} = 0` for `m = 0, 2`. -/
theorem integral_trial_mul_resid {c : ℝ} (hc : 0 < c) {m : ℕ} (hm : m = 0 ∨ m = 2) :
    ∫ w, pg c (herm m) w * pg c (rq m) w = 0 := by
  simp_rw [pg_mul]
  rw [Cvs.Prolate.HermiteTrialResiduals.integral_eval_mul_gaussian hc, div_self hc.ne']
  rcases hm with rfl | rfl
  · rw [gE_herm_mul_rq_zero]; norm_num
  · rw [gE_herm_mul_rq_two]; norm_num

/-- **The cut product is controlled by the two cut masses**:
`|∫_{−1}^{1} F R| ≤ ½((∫_ℝ F² − ∫_{−1}^{1} F²) + (∫_ℝ R² − ∫_{−1}^{1} R²))` when `∫_ℝ F R = 0`. -/
theorem abs_intervalIntegral_mul_le {c : ℝ} (hc : 0 < c) (Q Q' : ℝ[X])
    (h0 : ∫ w, pg c Q w * pg c Q' w = 0) :
    |∫ w in (-1 : ℝ)..1, pg c Q w * pg c Q' w|
      ≤ ((∫ w, pg c Q w ^ 2) - (∫ w in (-1 : ℝ)..1, pg c Q w ^ 2)
          + ((∫ w, pg c Q' w ^ 2) - ∫ w in (-1 : ℝ)..1, pg c Q' w ^ 2)) / 2 := by
  have hint : ∀ P : ℝ[X], Integrable fun w => P.eval (c * w ^ 2) * exp (-c * w ^ 2) :=
    fun P => Cvs.Prolate.HermiteTrialResiduals.integrable_eval_mul_gaussian hc c P
  have iQ : Integrable fun w => pg c Q w ^ 2 := Cvs.Prolate.HermiteTrialResiduals.integrable_pg_sq hc Q
  have iQ' : Integrable fun w => pg c Q' w ^ 2 := Cvs.Prolate.HermiteTrialResiduals.integrable_pg_sq hc Q'
  have iX : Integrable fun w => pg c Q w * pg c Q' w := by
    simp_rw [pg_mul]; exact hint _
  have cont : ∀ P : ℝ[X], Continuous (pg c P) := fun P => Cvs.Prolate.HermiteTrialResiduals.continuous_pg c P
  have jQ : IntervalIntegrable (fun w => pg c Q w ^ 2) volume (-1) 1 :=
    ((cont Q).pow 2).intervalIntegrable _ _
  have jQ' : IntervalIntegrable (fun w => pg c Q' w ^ 2) volume (-1) 1 :=
    ((cont Q').pow 2).intervalIntegrable _ _
  have jX : IntervalIntegrable (fun w => pg c Q w * pg c Q' w) volume (-1) 1 :=
    ((cont Q).mul (cont Q')).intervalIntegrable _ _
  -- a nonnegative integrand has at most its full integral on `[−1, 1]`
  have cut : ∀ g : ℝ → ℝ, Integrable g → (∀ w, 0 ≤ g w) → ∫ w in (-1 : ℝ)..1, g w ≤ ∫ w, g w := by
    intro g hg hg0
    rw [intervalIntegral.integral_of_le (by norm_num)]
    exact setIntegral_le_integral hg (Eventually.of_forall hg0)
  have hp := cut (fun w => (pg c Q w + pg c Q' w) ^ 2)
    (by
      have : (fun w => (pg c Q w + pg c Q' w) ^ 2)
          = fun w => pg c Q w ^ 2 + 2 * (pg c Q w * pg c Q' w) + pg c Q' w ^ 2 := by funext w; ring
      rw [this]; exact (iQ.add (iX.const_mul 2)).add iQ') (fun w => sq_nonneg _)
  have hm := cut (fun w => (pg c Q w - pg c Q' w) ^ 2)
    (by
      have : (fun w => (pg c Q w - pg c Q' w) ^ 2)
          = fun w => pg c Q w ^ 2 - 2 * (pg c Q w * pg c Q' w) + pg c Q' w ^ 2 := by funext w; ring
      rw [this]; exact (iQ.sub (iX.const_mul 2)).add iQ') (fun w => sq_nonneg _)
  have ep : (fun w => (pg c Q w + pg c Q' w) ^ 2)
      = fun w => pg c Q w ^ 2 + 2 * (pg c Q w * pg c Q' w) + pg c Q' w ^ 2 := by funext w; ring
  have em : (fun w => (pg c Q w - pg c Q' w) ^ 2)
      = fun w => pg c Q w ^ 2 - 2 * (pg c Q w * pg c Q' w) + pg c Q' w ^ 2 := by funext w; ring
  rw [ep] at hp
  rw [em] at hm
  have eRp : ∫ w, (pg c Q w ^ 2 + 2 * (pg c Q w * pg c Q' w) + pg c Q' w ^ 2)
      = (∫ w, pg c Q w ^ 2) + 2 * (∫ w, pg c Q w * pg c Q' w) + ∫ w, pg c Q' w ^ 2 := by
    have h1 := integral_add (iQ.add (iX.const_mul 2)) iQ'
    have h2 := integral_add iQ (iX.const_mul 2)
    simp only [Pi.add_apply] at h1 h2
    rw [h1, h2, integral_const_mul]
  have eRm : ∫ w, (pg c Q w ^ 2 - 2 * (pg c Q w * pg c Q' w) + pg c Q' w ^ 2)
      = (∫ w, pg c Q w ^ 2) - 2 * (∫ w, pg c Q w * pg c Q' w) + ∫ w, pg c Q' w ^ 2 := by
    have h1 := integral_add (iQ.sub (iX.const_mul 2)) iQ'
    have h2 := integral_sub iQ (iX.const_mul 2)
    simp only [Pi.add_apply, Pi.sub_apply] at h1 h2
    rw [h1, h2, integral_const_mul]
  have eIp : ∫ w in (-1 : ℝ)..1, (pg c Q w ^ 2 + 2 * (pg c Q w * pg c Q' w) + pg c Q' w ^ 2)
      = (∫ w in (-1 : ℝ)..1, pg c Q w ^ 2) + 2 * (∫ w in (-1 : ℝ)..1, pg c Q w * pg c Q' w)
        + ∫ w in (-1 : ℝ)..1, pg c Q' w ^ 2 := by
    rw [intervalIntegral.integral_add (jQ.add (jX.const_mul 2)) jQ',
      intervalIntegral.integral_add jQ (jX.const_mul 2), intervalIntegral.integral_const_mul]
  have eIm : ∫ w in (-1 : ℝ)..1, (pg c Q w ^ 2 - 2 * (pg c Q w * pg c Q' w) + pg c Q' w ^ 2)
      = (∫ w in (-1 : ℝ)..1, pg c Q w ^ 2) - 2 * (∫ w in (-1 : ℝ)..1, pg c Q w * pg c Q' w)
        + ∫ w in (-1 : ℝ)..1, pg c Q' w ^ 2 := by
    rw [intervalIntegral.integral_add (jQ.sub (jX.const_mul 2)) jQ',
      intervalIntegral.integral_sub jQ (jX.const_mul 2), intervalIntegral.integral_const_mul]
  rw [eRp, eIp, h0] at hp
  rw [eRm, eIm, h0] at hm
  rw [abs_le]
  constructor <;> linarith

/-- **Kato–Temple at the Hermite trials**: for `m = 0` (level `0`) and `m = 2` (level `2`), with every other level
`δ > 0` from `μ_{2m}`, `|χ − μ_{2m}| (∫F² − ∫R²/δ²) ≤ ½(cut masses of F² and R²) + ∫R²/δ` on `[−1, 1]`. -/
theorem abs_lev_sub_mu_mul_le (hc : 0 < c) {m : ℕ} (hm : m = 0 ∨ m = 2)
    (hk : ∃ χ, IsLevelIdx c m χ) {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ j χ, IsLevelIdx c j χ → j ≠ m → δ ≤ |χ - mu c m|) :
    |lev c m - mu c m| * ((∫ s in (-1 : ℝ)..1, pg c (herm m) s ^ 2) - (∫ s in (-1 : ℝ)..1, pg c (rq m) s ^ 2) / δ ^ 2)
      ≤ ((∫ w, pg c (herm m) w ^ 2) - (∫ w in (-1 : ℝ)..1, pg c (herm m) w ^ 2)
          + ((∫ w, pg c (rq m) w ^ 2) - ∫ w in (-1 : ℝ)..1, pg c (rq m) w ^ 2)) / 2
        + (∫ s in (-1 : ℝ)..1, pg c (rq m) s ^ 2) / δ := by
  have hm2 : m ≤ 2 := by rcases hm with rfl | rfl <;> norm_num
  have h := abs_lev_sub_mul_le hc.ne' (fun s _ => Cvs.Prolate.HermiteTrialResiduals.hasDerivAt_pg c _ s)
    (fun s _ => Cvs.Prolate.HermiteTrialResiduals.hasDerivAt_pg₁ c _ s) (Cvs.Prolate.HermiteTrialResiduals.continuous_pg₂ c _).continuousOn
    (fun s _ => Cvs.Prolate.HermiteTrialResiduals.trial_ode hm2 c s) (fun s _ => Cvs.Prolate.HermiteTrialResiduals.pg_neg c _ s) (fun s _ => Cvs.Prolate.HermiteTrialResiduals.pg_neg c _ s)
    hk hδ hgap
  have ht := abs_intervalIntegral_mul_le hc (herm m) (rq m) (integral_trial_mul_resid hc hm)
  linarith

end Trials

/-! ### Explicit `O(1/c)` -/

section Explicit

theorem gE_rq_sq_zero (r : ℝ) :
    gE r (rq 0 ^ 2) = 105 / 16 * r ^ 4 - 45 / 4 * r ^ 3 + 63 / 8 * r ^ 2 - 9 / 4 * r + 9 / 16 := by
  rw [Cvs.Prolate.HermiteTrialResiduals.gE_eq_of_eval (Finset.range 5) (fun k => ([9/16, -9/2, 21/2, -6, 1] : List ℝ).getD k 0)
    (fun t => by simp [rq, herm, Finset.sum_range_succ]; ring)]
  simp [Cvs.Prolate.HermiteTrialResiduals.gm, Finset.sum_range_succ, Nat.factorial]; ring

theorem gE_rq_sq_two (r : ℝ) :
    gE r (rq 2 ^ 2) = 2027025 * r ^ 8 - 7567560 * r ^ 7 + 12515580 * r ^ 6 - 11907000 * r ^ 5
      + 7127190 * r ^ 4 - 2754360 * r ^ 3 + 691740 * r ^ 2 - 108360 * r + 16641 := by
  rw [Cvs.Prolate.HermiteTrialResiduals.gE_eq_of_eval (Finset.range 9) (fun k => ([16641, -216720, 922320, -1468992, 1086048,
      -403200, 77056, -7168, 256] : List ℝ).getD k 0)
    (fun t => by simp [rq, herm, Finset.sum_range_succ, Nat.descFactorial]; ring)]
  simp [Cvs.Prolate.HermiteTrialResiduals.gm, Finset.sum_range_succ, Nat.factorial]; ring

/-- The real-arithmetic core of the explicit bound. -/
theorem le_of_temple {x a b S K κ gF gR E δ : ℝ} (hx : 0 ≤ x) (hS : 0 < S)
    (hT : x * (a - b / δ ^ 2) ≤ ((K * S - a) + (κ * K * S - b)) / 2 + b / δ)
    (ha1 : K * S - a ≤ E * gF * S) (hb1 : κ * K * S - b ≤ E * gR * S) (hb : b ≤ κ * K * S)
    (hδ : 0 < δ) (hD : 0 < K - E * gF - κ * K / δ ^ 2) :
    x ≤ (E * (gF + gR) / 2 + κ * K / δ) / (K - E * gF - κ * K / δ ^ 2) := by
  rw [le_div_iff₀ hD]
  have hδ2 : 0 < δ ^ 2 := by positivity
  have h1 : S * (K - E * gF - κ * K / δ ^ 2) ≤ a - b / δ ^ 2 := by
    have : b / δ ^ 2 ≤ κ * K * S / δ ^ 2 := div_le_div_of_nonneg_right hb hδ2.le
    have e : S * (K - E * gF - κ * K / δ ^ 2) = K * S - E * gF * S - κ * K * S / δ ^ 2 := by
      field_simp
    rw [e]; linarith
  have h2 : ((K * S - a) + (κ * K * S - b)) / 2 + b / δ ≤ S * (E * (gF + gR) / 2 + κ * K / δ) := by
    have : b / δ ≤ κ * K * S / δ := div_le_div_of_nonneg_right hb hδ.le
    have e : S * (E * (gF + gR) / 2 + κ * K / δ) = (E * gF * S + E * gR * S) / 2 + κ * K * S / δ := by
      field_simp
    rw [e]; linarith
  have h3 : x * (S * (K - E * gF - κ * K / δ ^ 2)) ≤ S * (E * (gF + gR) / 2 + κ * K / δ) :=
    (mul_le_mul_of_nonneg_left h1 hx).trans (hT.trans h2)
  have h4 : S * (x * (K - E * gF - κ * K / δ ^ 2)) ≤ S * (E * (gF + gR) / 2 + κ * K / δ) := by
    linarith [show x * (S * (K - E * gF - κ * K / δ ^ 2)) = S * (x * (K - E * gF - κ * K / δ ^ 2)) by ring]
  exact le_of_mul_le_mul_left h4 hS

/-- `e^{−c/2} ≤ 46080/c⁶` for `c ≥ 0`, from `x⁶/6! ≤ eˣ`. -/
theorem exp_neg_half_le {c : ℝ} (hc : 0 < c) : exp (-(c / 2)) ≤ 46080 / c ^ 6 := by
  have h := Real.pow_div_factorial_le_exp (c / 2) (by positivity) 6
  have hf : ((Nat.factorial 6 : ℕ) : ℝ) = 720 := by norm_num [Nat.factorial]
  rw [hf] at h
  rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (exp_pos _) (by positivity)]
  have : (c / 2) ^ 6 / 720 = c ^ 6 / 46080 := by ring
  rw [this] at h
  nlinarith [exp_pos (c / 2)]

/-- The cut masses at `μ = c/2`: `∫_ℝ (pg c Q)² − ∫_{−1}^{1} (pg c Q)² ≤ e^{−c/2} gE 2 (Q²) √2 √(π/c)`. -/
theorem cut_le {c : ℝ} (hc : 0 < c) (Q : ℝ[X]) :
    (∫ w, pg c Q w ^ 2) - (∫ w in (-1 : ℝ)..1, pg c Q w ^ 2)
      ≤ exp (-(c / 2)) * (gE 2 (Q ^ 2) * √2) * √(π / c) := by
  have h := Cvs.Prolate.HermiteTrialResiduals.integral_pg_sq_sub_le (half_pos hc) (half_le_self hc.le) Q
  have h2 : c / (c / 2) = 2 := by field_simp
  have hs : √(π / (c / 2)) = √2 * √(π / c) := by
    rw [← Real.sqrt_mul (by norm_num)]; congr 1; field_simp
  rw [h2, hs, show c - c / 2 = c / 2 by ring] at h
  linarith [show exp (-(c / 2)) * (gE 2 (Q ^ 2) * (√2 * √(π / c)))
    = exp (-(c / 2)) * (gE 2 (Q ^ 2) * √2) * √(π / c) by ring]

theorem cut_nonneg {c : ℝ} (hc : 0 < c) (Q : ℝ[X]) :
    (∫ w in (-1 : ℝ)..1, pg c Q w ^ 2) ≤ ∫ w, pg c Q w ^ 2 := by
  rw [intervalIntegral.integral_of_le (by norm_num)]
  exact setIntegral_le_integral (Cvs.Prolate.HermiteTrialResiduals.integrable_pg_sq hc Q) (Eventually.of_forall fun w => sq_nonneg _)

theorem sqrt_two_le : √2 ≤ 1415 / 1000 := by
  calc √2 ≤ √((1415 / 1000) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
    _ = 1415 / 1000 := Real.sqrt_sq (by norm_num)

/-- `e^{−c/2} ≤ 10^{−9}` and `c e^{−c/2} ≤ 2·10^{−7}` for `c ≥ 200`. -/
theorem exp_small {c : ℝ} (hc : 200 ≤ c) : exp (-(c / 2)) * c ≤ 2 / 10 ^ 7 ∧ exp (-(c / 2)) ≤ 1 / 10 ^ 9 := by
  have hc0 : 0 < c := by linarith
  have hE := exp_neg_half_le hc0
  have hE0 : 0 < exp (-(c / 2)) := exp_pos _
  have hc5 : (200 : ℝ) ^ 5 ≤ c ^ 5 := pow_le_pow_left₀ (by norm_num) hc 5
  have h1 : exp (-(c / 2)) * c ^ 6 ≤ 46080 := by
    rw [le_div_iff₀ (by positivity)] at hE; exact hE
  have h2 : exp (-(c / 2)) * c * 200 ^ 5 ≤ 46080 := by
    have : exp (-(c / 2)) * c * 200 ^ 5 ≤ exp (-(c / 2)) * c * c ^ 5 :=
      mul_le_mul_of_nonneg_left hc5 (by positivity)
    nlinarith
  have h3 : exp (-(c / 2)) * c ≤ 2 / 10 ^ 7 := by
    have : exp (-(c / 2)) * c ≤ 46080 / 200 ^ 5 := by rw [le_div_iff₀ (by norm_num)]; linarith
    linarith [show (46080 : ℝ) / 200 ^ 5 ≤ 2 / 10 ^ 7 by norm_num]
  refine ⟨h3, ?_⟩
  have : exp (-(c / 2)) * 200 ≤ exp (-(c / 2)) * c := mul_le_mul_of_nonneg_left hc hE0.le
  linarith

/-- **The ground level to `O(1/c)`**: `|χ₀ − (c − 3/4)| ≤ 1/c` for `c ≥ 200`. -/
theorem abs_lev_zero_sub_le {c : ℝ} (hc : 200 ≤ c) : |lev c 0 - mu c 0| ≤ 1 / c := by
  have hc0 : 0 < c := by linarith
  have hδ : 0 < 2 * c - 19 / 4 := by linarith
  have hT := abs_lev_sub_mu_mul_le hc0 (m := 0) (Or.inl rfl) (Cvs.Prolate.EvenRungsByIndex.exists_isLevelIdx_zero c)
    hδ fun _ _ hχ hj => Cvs.Prolate.EvenRungDavisKahan.le_abs_sub_mu_zero hc0 hχ hj
  have hS : 0 < √(π / c) := Real.sqrt_pos.mpr (by positivity)
  have hFR : ∫ w, pg c (herm 0) w ^ 2 = 1 * √(π / c) := by
    rw [Cvs.Prolate.HermiteTrialResiduals.integral_trial_sq hc0 (by norm_num)]; simp
  have hRR : ∫ w, pg c (rq 0) w ^ 2 = 3 / 2 * 1 * √(π / c) := by
    rw [Cvs.Prolate.HermiteTrialResiduals.integral_resid_sq hc0 (by norm_num), hFR, Cvs.Prolate.HermiteTrialResiduals.kap2_values.1]; ring
  have hcF := cut_le hc0 (herm 0)
  have hcR := cut_le hc0 (rq 0)
  rw [Cvs.Prolate.HermiteTrialResiduals.gE_herm_sq_zero] at hcF
  rw [gE_rq_sq_zero] at hcR
  rw [hFR] at hcF hT
  rw [hRR] at hcR hT
  have hb := cut_nonneg hc0 (rq 0)
  rw [hRR] at hb
  obtain ⟨hEc, hE9⟩ := exp_small hc
  have hE0 : 0 < exp (-(c / 2)) := exp_pos _
  have hs2 := sqrt_two_le
  have hs20 : 0 ≤ √2 := Real.sqrt_nonneg 2
  have hgR : (105 / 16 * 2 ^ 4 - 45 / 4 * 2 ^ 3 + 63 / 8 * 2 ^ 2 - 9 / 4 * 2 + 9 / 16 : ℝ) * √2 = 681 / 16 * √2 := by
    norm_num
  rw [hgR] at hcR
  have hδc : 195 / 100 * c ≤ 2 * c - 19 / 4 := by linarith
  have hδ2 : 380 ^ 2 ≤ (2 * c - 19 / 4) ^ 2 := pow_le_pow_left₀ (by norm_num) (by linarith) 2
  have hK : 3 / 2 * 1 / (2 * c - 19 / 4) ^ 2 ≤ 1 / 10000 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hEF : exp (-(c / 2)) * (1 * √2) ≤ 1 / 10000 := by nlinarith
  have hD : 0 < 1 - exp (-(c / 2)) * (1 * √2) - 3 / 2 * 1 / (2 * c - 19 / 4) ^ 2 := by linarith
  have key := le_of_temple (gF := 1 * √2) (gR := 681 / 16 * √2) (abs_nonneg _) hS hT
    (by linarith) (by linarith) hb hδ hD
  refine key.trans ?_
  rw [div_le_div_iff₀ hD hc0]
  have h1 : exp (-(c / 2)) * (1 * √2 + 681 / 16 * √2) / 2 * c ≤ 2 / 10 ^ 7 * 32 := by
    have : exp (-(c / 2)) * (1 * √2 + 681 / 16 * √2) / 2 * c = exp (-(c / 2)) * c * (697 / 32 * √2) := by ring
    rw [this]; nlinarith
  have h2 : 3 / 2 * 1 / (2 * c - 19 / 4) * c ≤ 100 / 195 * (3 / 2) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hδ]; nlinarith
  nlinarith

/-- **The level `χ₄` to `O(1/c)`**: `|χ₄ − (9c − 43/4)| ≤ 64/c` for `c ≥ 200`. -/
theorem abs_lev_two_sub_le {c : ℝ} (hc : 200 ≤ c) : |lev c 2 - mu c 2| ≤ 64 / c := by
  have hc0 : 0 < c := by linarith
  have hδ : 0 < 2 * c - 203 / 4 := by linarith
  have hT := abs_lev_sub_mu_mul_le hc0 (m := 2) (Or.inr rfl)
    (Cvs.Prolate.EvenRungDavisKahan.exists_isLevelIdx_of_le_three (by linarith) (by norm_num))
    hδ fun _ _ hχ hj => Cvs.Prolate.EvenRungDavisKahan.le_abs_sub_mu_two (by linarith) hχ hj
  have hS : 0 < 384 * √(π / c) := by have := Real.sqrt_pos.mpr (show 0 < π / c by positivity); positivity
  have hFR : ∫ w, pg c (herm 2) w ^ 2 = 1 * (384 * √(π / c)) := by
    rw [Cvs.Prolate.HermiteTrialResiduals.integral_trial_sq hc0 (by norm_num)]; norm_num [Nat.factorial]
  have hRR : ∫ w, pg c (rq 2) w ^ 2 = 213 / 2 * 1 * (384 * √(π / c)) := by
    rw [Cvs.Prolate.HermiteTrialResiduals.integral_resid_sq hc0 (by norm_num), hFR, Cvs.Prolate.HermiteTrialResiduals.kap2_values.2.2]; ring
  have hcF := cut_le hc0 (herm 2)
  have hcR := cut_le hc0 (rq 2)
  rw [Cvs.Prolate.HermiteTrialResiduals.gE_herm_sq_two] at hcF
  rw [gE_rq_sq_two] at hcR
  rw [hFR] at hT
  rw [hRR] at hT
  have hb := cut_nonneg hc0 (rq 2)
  rw [hRR] at hb
  rw [hFR] at hcF
  rw [hRR] at hcR
  obtain ⟨hEc, hE9⟩ := exp_small hc
  have hE0 : 0 < exp (-(c / 2)) := exp_pos _
  have hs2 := sqrt_two_le
  have hs20 : 0 ≤ √2 := Real.sqrt_nonneg 2
  have hcF' : 1 * (384 * √(π / c)) - ∫ w in (-1 : ℝ)..1, pg c (herm 2) w ^ 2
      ≤ exp (-(c / 2)) * (227 / 8 * √2) * (384 * √(π / c)) := by
    have : exp (-(c / 2)) * ((144 - 576 * 2 + 2016 * 2 ^ 2 - 2880 * 2 ^ 3 + 1680 * 2 ^ 4 : ℝ) * √2) * √(π / c)
        = exp (-(c / 2)) * (227 / 8 * √2) * (384 * √(π / c)) := by ring
    linarith
  have hcR' : 213 / 2 * 1 * (384 * √(π / c)) - ∫ w in (-1 : ℝ)..1, pg c (rq 2) w ^ 2
      ≤ exp (-(c / 2)) * (21603627 / 128 * √2) * (384 * √(π / c)) := by
    have : exp (-(c / 2)) * ((2027025 * 2 ^ 8 - 7567560 * 2 ^ 7 + 12515580 * 2 ^ 6 - 11907000 * 2 ^ 5
      + 7127190 * 2 ^ 4 - 2754360 * 2 ^ 3 + 691740 * 2 ^ 2 - 108360 * 2 + 16641 : ℝ) * √2) * √(π / c)
        = exp (-(c / 2)) * (21603627 / 128 * √2) * (384 * √(π / c)) := by ring
    linarith
  have hδc : 174 / 100 * c ≤ 2 * c - 203 / 4 := by linarith
  have hδ2 : 349 ^ 2 ≤ (2 * c - 203 / 4) ^ 2 := pow_le_pow_left₀ (by norm_num) (by linarith) 2
  have hK : 213 / 2 * 1 / (2 * c - 203 / 4) ^ 2 ≤ 1 / 1000 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hEF : exp (-(c / 2)) * (227 / 8 * √2) ≤ 1 / 10000 := by nlinarith
  have hD : 0 < 1 - exp (-(c / 2)) * (227 / 8 * √2) - 213 / 2 * 1 / (2 * c - 203 / 4) ^ 2 := by linarith
  have key := le_of_temple (gF := 227 / 8 * √2) (gR := 21603627 / 128 * √2) (abs_nonneg _) hS hT
    hcF' hcR' (by linarith) hδ hD
  refine key.trans ?_
  rw [div_le_div_iff₀ hD hc0]
  have h1 : exp (-(c / 2)) * (227 / 8 * √2 + 21603627 / 128 * √2) / 2 * c ≤ 2 / 10 ^ 7 * 120000 := by
    have : exp (-(c / 2)) * (227 / 8 * √2 + 21603627 / 128 * √2) / 2 * c
        = exp (-(c / 2)) * c * (21607259 / 256 * √2) := by ring
    rw [this]; nlinarith
  have h2 : 213 / 2 * 1 / (2 * c - 203 / 4) * c ≤ 100 / 174 * (213 / 2) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hδ]; nlinarith
  nlinarith

end Explicit

end Cvs.Prolate.EvenRungKatoTemple
