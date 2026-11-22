import Mathlib
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.Gram.ProlateCellGramHalfUnit
import Cvs.Route.Visibility.LayerFloorDeepRemainderB
import Cvs.Route.Visibility.ScalarTraceBudget

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The central resolvent trace `T_c` of the cosine transform

`F` has kernel `√(c/2π) cos(cst)` and eigenfunctions `h_{2k}` with `σ_k = √(c/2π)·μ_k`; with `A = QFQ` on
`I = [−1/2, 1/2]` and `g(s) = s²(1 − s²)(1 + s)`, `T_c = Σ_k g(σ_k)⟨Qh_{2k}, (I − A)⁻¹Qh_{2k}⟩`, entries variational;
on the selected rungs `Σ_j μ_j B_jj ≤ a_t T_c` and `Σ_j (1 − √λ_j)B_jj ≤ μ* T_c`.
-/

noncomputable section

open Real Set MeasureTheory Filter Finset

namespace Cvs.Prolate.Gram.CentralResolventTrace
open Cvs.ZeroCounting

open Cvs.Prolate.EvenRungsByIndex (rung muR lamR IsLevelIdx)
open Cvs.Prolate.Gram.ProlateCellGramHalfUnit (lam lamTop mu)
open Cvs.Route.Visibility.LayerFloorDeepRemainderB (muStar)

/-! ### The objects -/

/-- The central interval `I = [−1/2, 1/2]`. -/
abbrev cI : Set ℝ := Icc (-1 / 2) (1 / 2)

/-- `L²(I)`. -/
abbrev L2I : Type := Lp ℝ 2 (volume.restrict cI)

/-- The cosine-transform eigenvalue `σ_k = √(c/2π)·μ_k` of the even rung `h_{2k}`. -/
def sigma (c : ℝ) (k : ℕ) : ℝ := √(c / (2 * π)) * muR c k

/-- The spectral weight `g(s) = s²(1 − s²)(1 + s)`. -/
def gpoly (s : ℝ) : ℝ := s ^ 2 * (1 - s ^ 2) * (1 + s)

/-- The central form `⟨f, Af⟩ = √(c/2π)∫_I∫_I f(s) cos(cst) f(t)` of `A = QFQ`. -/
def centralForm (c : ℝ) (f : ℝ → ℝ) : ℝ :=
  √(c / (2 * π)) * ∫ s in cI, ∫ t in cI, f s * cos (c * s * t) * f t

/-- The resolvent objective `2⟨Qh, f⟩ − ‖f‖² + ⟨f, Af⟩` on `f ∈ L²(I)`. -/
def resObj (c : ℝ) (h : ℝ → ℝ) (f : L2I) : ℝ :=
  2 * (∫ s in cI, h s * f s) - (∫ s in cI, f s ^ 2) + centralForm c f

/-- The resolvent entry `⟨Qh, (I − A)⁻¹Qh⟩` as the supremum of the objective. -/
def resQuad (c : ℝ) (h : ℝ → ℝ) : ℝ := ⨆ f : L2I, resObj c h f

open Classical in
/-- The `k`-th term `g(σ_k)⟨Qh_{2k}, (I − A)⁻¹Qh_{2k}⟩` of the trace, over the even levels that exist. -/
def traceTerm (c : ℝ) (k : ℕ) : ℝ :=
  if ∃ χ, IsLevelIdx c k χ then gpoly (sigma c k) * resQuad c (rung c k) else 0

/-- `T_c = Tr((I − A)⁻¹QGQ)` on the even space. -/
def traceT (c : ℝ) : ℝ := ∑' k, traceTerm c k

/-- `T_c` at `c = 2πx`. -/
def Tc (x : ℕ) : ℝ := traceT (2 * π * x)

/-- The trace is well posed: the resolvent objective at every existing level is bounded above and the series
converges. -/
def WellPosed (c : ℝ) : Prop :=
  (∀ k, (∃ χ, IsLevelIdx c k χ) → BddAbove (range (resObj c (rung c k)))) ∧ Summable (traceTerm c)

/-- The top weight `a_t = 2/((1 − λ_t)λ_t(1 + √λ_t)³)`. -/
def aTop (x : ℕ) : ℝ := 2 / ((1 - lamTop x) * lamTop x * (1 + √(lamTop x)) ^ 3)

/-! ### Signs -/

/-- `σ_k² = λ_k`. -/
theorem sigma_sq (c : ℝ) (k : ℕ) : sigma c k ^ 2 = lamR c k := by
  unfold sigma lamR; ring

/-- `|σ_k| ≤ 1` at every existing level. -/
theorem abs_sigma_le_one {c : ℝ} (hc : 0 < c) {k : ℕ} (h : ∃ χ, IsLevelIdx c k χ) : |sigma c k| ≤ 1 := by
  have hl : lamR c k ≤ 1 := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact Cvs.Prolate.EvenRungsByIndex.lamR_zero_le_one hc
    · exact (Cvs.Prolate.EvenRungsByIndex.lamR_lt_one hc h hk).le
  rw [← sigma_sq] at hl
  exact abs_le_one_iff_mul_self_le_one.2 (by nlinarith)

/-- `g ≥ 0` on `[−1, 1]`. -/
theorem gpoly_nonneg {s : ℝ} (hs : |s| ≤ 1) : 0 ≤ gpoly s := by
  have h1 := abs_le.1 hs
  have hs2 : s ^ 2 ≤ 1 := by nlinarith [sq_abs s, abs_nonneg s]
  unfold gpoly
  exact mul_nonneg (mul_nonneg (sq_nonneg s) (by linarith)) (by linarith)

/-- The objective vanishes at `f = 0`. -/
theorem resObj_zero (c : ℝ) (h : ℝ → ℝ) : resObj c h 0 = 0 := by
  suffices H : ∀ f : L2I, (∀ᵐ s ∂(volume.restrict cI), f s = 0) → resObj c h f = 0 from
    H 0 (Lp.coeFn_zero ℝ 2 (volume.restrict cI))
  intro f hz
  unfold resObj centralForm
  rw [integral_eq_zero_of_ae (hz.mono fun s hs => by simp [hs]),
    integral_eq_zero_of_ae (hz.mono fun s hs => by simp [hs]),
    integral_eq_zero_of_ae (hz.mono fun s hs => by simp [hs])]
  simp

/-- `⟨Qh, (I − A)⁻¹Qh⟩ ≥ 0` when the objective is bounded above. -/
theorem resQuad_nonneg {c : ℝ} {h : ℝ → ℝ} (hb : BddAbove (range (resObj c h))) : 0 ≤ resQuad c h :=
  (resObj_zero c h).symm.le.trans (le_ciSup hb 0)

/-- Every trace term is nonnegative when the trace is well posed. -/
theorem traceTerm_nonneg {c : ℝ} (hc : 0 < c) (hW : WellPosed c) (k : ℕ) : 0 ≤ traceTerm c k := by
  unfold traceTerm
  split_ifs with h
  · exact mul_nonneg (gpoly_nonneg (abs_sigma_le_one hc h)) (resQuad_nonneg (hW.1 k h))
  · exact le_rfl

/-! ### The selected rungs -/

/-- `σ_{2j} = √λ_j` on the selected rungs at `c = 2πx`. -/
theorem sigma_two_mul {x : ℕ} (hx : 80 ≤ 2 * π * x) (j : Fin x) :
    sigma (2 * π * x) (2 * (j : ℕ)) = √(lam x j) := by
  have hc : 0 < 2 * π * x := by linarith
  have hμ := Cvs.Prolate.EvenRungsByIndex.muR_pos_of_even hc (Cvs.Prolate.Gram.ProlateCellGramHalfUnit.exists_level hx j) (even_two_mul _)
  have hs : 0 ≤ sigma (2 * π * x) (2 * (j : ℕ)) := mul_nonneg (Real.sqrt_nonneg _) hμ.le
  rw [Cvs.Prolate.Gram.ProlateCellGramHalfUnit.lam, ← sigma_sq, Real.sqrt_sq hs]

/-- `a_t ≥ 0` at `80 ≤ 2πx`. -/
theorem aTop_nonneg {x : ℕ} (hx : 80 ≤ 2 * π * x) : 0 ≤ aTop x := by
  have := Cvs.Prolate.Gram.ProlateCellGramHalfUnit.lamTop_lt_one hx
  have := Cvs.Prolate.Gram.ProlateCellGramHalfUnit.half_le_lamTop hx
  unfold aTop
  apply div_nonneg (by norm_num)
  exact mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by positivity)

/-- `a_t ≤ 5/3` once `λ_t ≤ 3/4`. -/
theorem aTop_le {x : ℕ} (hx : 80 ≤ 2 * π * x) (h : lamTop x ≤ 3 / 4) : aTop x ≤ 5 / 3 :=
  Cvs.Route.Visibility.ScalarTraceBudget.topWeight_le (Cvs.Prolate.Gram.ProlateCellGramHalfUnit.half_le_lamTop hx) h

/-- The positive majorant `μ_j ≤ a_t g(√λ_j)` on every selected rung. -/
theorem mu_le_aTop_mul {x : ℕ} (hx : 80 ≤ 2 * π * x) (j : Fin x) : mu x j ≤ aTop x * gpoly (√(lam x j)) := by
  have hj := j.2
  have ht1 := Cvs.Prolate.Gram.ProlateCellGramHalfUnit.lamTop_lt_one hx
  have ht2 := Cvs.Prolate.Gram.ProlateCellGramHalfUnit.half_le_lamTop hx
  have hl1 := Cvs.Prolate.Gram.ProlateCellGramHalfUnit.lam_le_one hx hj
  have h2 := Cvs.Prolate.Gram.ProlateCellGramHalfUnit.two_le_of_scale hx
  have htl : lamTop x ≤ lam x j := Cvs.Prolate.Gram.ProlateCellGramHalfUnit.lam_anti hx (by omega) (by omega : (j : ℕ) ≤ x - 1)
  set l := lam x j
  set t := lamTop x
  have hl0 : 0 ≤ l := by linarith
  have hs := Real.sq_sqrt hl0
  have hst : √t ≤ √l := Real.sqrt_le_sqrt htl
  have hs0 := Real.sqrt_nonneg t
  have hpow : t * (1 + √t) ^ 3 ≤ l * (1 + √l) ^ 3 :=
    mul_le_mul htl (pow_le_pow_left₀ (by positivity) (by linarith) 3) (by positivity) hl0
  have hd1 : 0 < (1 - t) * (1 + √l) ^ 2 := by
    have : 0 < (1 + √l) ^ 2 := by positivity
    exact mul_pos (by linarith) this
  have hd2 : 0 < (1 - t) * t * (1 + √t) ^ 3 := mul_pos (mul_pos (by linarith) (by linarith)) (by positivity)
  have hg : gpoly (√l) = l * (1 - l) * (1 + √l) := by rw [gpoly, hs]
  rw [Cvs.Prolate.Gram.ProlateCellGramHalfUnit.mu, aTop, hg, ← mul_div_right_comm, div_le_div_iff₀ hd1 hd2]
  have hk := mul_le_mul_of_nonneg_left hpow (mul_nonneg (sub_nonneg.2 hl1) (sub_nonneg.2 ht1.le))
  nlinarith [Real.sqrt_nonneg l]

/-- The positive majorant `1 − √λ_j ≤ μ* g(√λ_j)` on every selected rung. -/
theorem delta_le_muStar_mul {x : ℕ} (hx : 80 ≤ 2 * π * x) (j : Fin x) :
    1 - √(lam x j) ≤ muStar * gpoly (√(lam x j)) := by
  have h2 := Cvs.Prolate.Gram.ProlateCellGramHalfUnit.two_le_of_scale hx
  have hl1 := Cvs.Prolate.Gram.ProlateCellGramHalfUnit.lam_le_one hx j.2
  have htl : lamTop x ≤ lam x j := Cvs.Prolate.Gram.ProlateCellGramHalfUnit.lam_anti hx (by omega) (by omega : (j : ℕ) ≤ x - 1)
  have hl2 : 1 / 2 ≤ lam x j := (Cvs.Prolate.Gram.ProlateCellGramHalfUnit.half_le_lamTop hx).trans htl
  set l := lam x j
  have hs := Real.sq_sqrt (show 0 ≤ l by linarith)
  set s := √l
  have hs1 : s ≤ 1 := by nlinarith [Real.sqrt_nonneg l]
  have hr := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hr0 := Real.sqrt_nonneg (2 : ℝ)
  have hsr : √2 / 2 ≤ s := by nlinarith [Real.sqrt_nonneg l]
  have hkey : 1 ≤ muStar * (l * (1 + s) ^ 2) := by
    have hm : muStar * (1 / 2 * (1 + √2 / 2) ^ 2) = 1 := by unfold muStar; nlinarith
    have hmono : 1 / 2 * (1 + √2 / 2) ^ 2 ≤ l * (1 + s) ^ 2 :=
      mul_le_mul hl2 (pow_le_pow_left₀ (by positivity) (by linarith) 2) (by positivity) (by linarith)
    calc (1 : ℝ) = muStar * (1 / 2 * (1 + √2 / 2) ^ 2) := hm.symm
      _ ≤ muStar * (l * (1 + s) ^ 2) := mul_le_mul_of_nonneg_left hmono Cvs.Route.Visibility.LayerFloorDeepRemainderB.muStar_pos.le
  have hg : gpoly s = (1 - s) * (l * (1 + s) ^ 2) := by rw [gpoly]; linear_combination (1 - s) * (1 + s) ^ 2 * hs
  rw [hg, ← mul_assoc, mul_comm muStar, mul_assoc]
  nlinarith [mul_le_mul_of_nonneg_left hkey (sub_nonneg.2 hs1)]

/-- The selected-rung resolvent entry `B_jj = ⟨Qh_{4j}, (I − A)⁻¹Qh_{4j}⟩`. -/
def selB (x : ℕ) (j : Fin x) : ℝ := resQuad (2 * π * x) (rung (2 * π * x) (2 * (j : ℕ)))

end Cvs.Prolate.Gram.CentralResolventTrace

end
