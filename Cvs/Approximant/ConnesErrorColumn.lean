import Mathlib
import Cvs.Approximant.ConnesFormTruncation
import Cvs.Approximant.ConnesVectorRealScale
import Cvs.Approximant.CosineColumnTailPairing
import Cvs.Approximant.SpineCouplingTailPairing
import Cvs.Approximant.TailRetainedModeCoupling
import Cvs.Finite.DiscreteTwoGap
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationQuadraticForm
import Cvs.Route.JointGapFromResidual
import Cvs.Upstream.SymmetricMatrixBottom
import Cvs.WeilForm.EvenOddSplitForm
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.SymmetricBilinearForm
import Cvs.WeilForm.ThetaSpaceParseval
import Cvs.WeilForm.WeilFormOnWindowL2

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The actual truncation error column and its centered projection

The error pairings are represented by an even coefficient column.
Its norm and the norm of its orthogonal projection are controlled by the unit-test budget.
-/

noncomputable section

open Real Matrix Finset Filter

namespace Cvs.Approximant.ConnesErrorColumn
open Cvs.ZeroCounting

open Cvs.Finite.SymmetricModeSet (Idx negI)

/-- The signed coordinate row is unchanged on negating its index. -/
theorem cosineRow_neg (N : ℕ) (i : Idx N) :
    Cvs.Approximant.CosineColumnTailPairing.cosineRow N (negI N i) = Cvs.Approximant.CosineColumnTailPairing.cosineRow N i := by
  funext j
  have he : j = negI N i ↔ negI N j = i := by
    constructor
    · intro h
      rw [h, Cvs.Finite.SymmetricModeSet.negI_involutive N i]
    · intro h
      rw [← h, Cvs.Finite.SymmetricModeSet.negI_involutive N j]
  have he' : negI N j = negI N i ↔ j = i := (Cvs.Finite.SymmetricModeSet.negI_involutive N).injective.eq_iff
  simp only [Cvs.Approximant.CosineColumnTailPairing.cosineRow, Cvs.Finite.TruncationQuadraticForm.evenPart, Pi.single_apply, he, he']
  ring

/-- Every even coefficient vector is the sum of its even signed coordinate rows. -/
theorem sum_smul_cosineRow (N : ℕ) (f : Idx N → ℝ)
    (hf : ∀ i, f (negI N i) = f i) : ∑ i, f i • Cvs.Approximant.CosineColumnTailPairing.cosineRow N i = f := by
  funext j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Cvs.Approximant.CosineColumnTailPairing.cosineRow, Cvs.Finite.TruncationQuadraticForm.evenPart]
  have ht (i : Idx N) : f i * (((Pi.single i (1 : ℝ) : Idx N → ℝ) j
      + (Pi.single i (1 : ℝ) : Idx N → ℝ) (negI N j)) / 2)
      = (if j = i then f i / 2 else 0) + (if negI N j = i then f i / 2 else 0) := by
    simp only [Pi.single_apply]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun i _ => ht i), Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq, mem_univ, if_true, hf j]
  ring

/-- The actual omitted Connes class paired with an even signed cosine row. -/
def errorColumn {x : ℕ} (hx : 80 ≤ 2 * π * x) (N : ℕ) (i : Idx N) : ℝ :=
  Cvs.WeilForm.SymmetricBilinearForm.QWbil (Real.log_natCast_nonneg x) x (Nat.clog 2 x)
    (Cvs.Approximant.ConnesFormTruncation.connesError hx N)
    (Cvs.Approximant.CosineColumnTailPairing.modeMap (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) N (Cvs.Approximant.CosineColumnTailPairing.cosineRow N i))

/-- The actual truncation error column is even. -/
theorem errorColumn_even {x : ℕ} (hx : 80 ≤ 2 * π * x) (N : ℕ) (i : Idx N) :
    errorColumn hx N (negI N i) = errorColumn hx N i := by
  rw [errorColumn, cosineRow_neg]
  rfl

/-- The actual error pairing is exactly the dot product against its column. -/
theorem QWbil_error_eq_dot {x : ℕ} (hx : 80 ≤ 2 * π * x) (N : ℕ)
    (f : Idx N → ℝ) (hf : ∀ i, f (negI N i) = f i) :
    Cvs.WeilForm.SymmetricBilinearForm.QWbil (Real.log_natCast_nonneg x) x (Nat.clog 2 x) (Cvs.Approximant.ConnesFormTruncation.connesError hx N)
      (Cvs.Approximant.CosineColumnTailPairing.modeMap (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) N f) = errorColumn hx N ⬝ᵥ f := by
  conv_lhs => rw [← sum_smul_cosineRow N f hf]
  simp only [map_sum, map_smul, smul_eq_mul]
  unfold dotProduct errorColumn
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- The arithmetic tail paired with each signed cosine row. -/
def tailColumn (x N : ℕ) (i : Idx N) : ℝ :=
  -Cvs.WeilForm.ThetaSpaceParseval.weilθ (Cvs.Approximant.CosineColumnTailPairing.connesTail x) (Cvs.Approximant.CosineColumnTailPairing.modeTest x N (Cvs.Approximant.CosineColumnTailPairing.cosineRow N i))

/-- The actual matrix column is its arithmetic tail column minus its form truncation column. -/
theorem connesColumn_eq_tail_sub_error {x : ℕ} (hx : 80 ≤ 2 * π * x) (N : ℕ) :
    Cvs.Approximant.CosineColumnTailPairing.connesColumn hx N = tailColumn x N - errorColumn hx N := by
  funext i
  unfold Cvs.Approximant.CosineColumnTailPairing.connesColumn tailColumn errorColumn
  rw [Cvs.Approximant.CosineColumnTailPairing.QWbil_connesTruncError_eq_evenPart hx N (Cvs.Approximant.CosineColumnTailPairing.cosineRow N i)]
  rfl

/-- The orthogonal removal of a coefficient direction, with zero direction allowed. -/
def center {ι : Type*} [Fintype ι] (u α : ι → ℝ) : ι → ℝ :=
  u - ((u ⬝ᵥ α) / (α ⬝ᵥ α)) • α

/-- Orthogonal removal is linear in the column being centered. -/
theorem center_sub {ι : Type*} [Fintype ι] (u v α : ι → ℝ) :
    center (u - v) α = center u α - center v α := by
  funext i
  simp only [center, sub_dotProduct, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_div]
  ring

/-- Centering removes the coefficient direction exactly. -/
theorem center_dot {ι : Type*} [Fintype ι] (u α : ι → ℝ) : center u α ⬝ᵥ α = 0 := by
  by_cases hα : α ⬝ᵥ α = 0
  · have hz : α = 0 := dotProduct_self_eq_zero.mp hα
    simp [center, hz]
  · simp only [center, sub_dotProduct, smul_dotProduct, smul_eq_mul]
    rw [div_mul_cancel₀ _ hα, sub_self]

/-- Orthogonal centering contracts the squared coefficient norm. -/
theorem center_sq_le {ι : Type*} [Fintype ι] (u α : ι → ℝ) :
    center u α ⬝ᵥ center u α ≤ u ⬝ᵥ u := by
  by_cases hα : α ⬝ᵥ α = 0
  · have hz : α = 0 := dotProduct_self_eq_zero.mp hα
    simp [center, hz]
  · have hα0 : 0 < α ⬝ᵥ α := lt_of_le_of_ne
      (Cvs.Upstream.SymmetricMatrixBottom.dotProduct_self_nonneg' α) (Ne.symm hα)
    have he : center u α ⬝ᵥ center u α = u ⬝ᵥ u - (u ⬝ᵥ α) ^ 2 / (α ⬝ᵥ α) := by
      simp only [center, sub_dotProduct, dotProduct_sub, smul_dotProduct,
        dotProduct_smul, smul_eq_mul, dotProduct_comm α u]
      field_simp
      ring
    rw [he]
    exact sub_le_self _ (div_nonneg (sq_nonneg _) hα0.le)

/-- Centering does not change pairing against a vector orthogonal to the removed direction. -/
theorem center_dot_of_perp {ι : Type*} [Fintype ι] (u α f : ι → ℝ)
    (hf : α ⬝ᵥ f = 0) : center u α ⬝ᵥ f = u ⬝ᵥ f := by
  simp only [center, sub_dotProduct, smul_dotProduct, smul_eq_mul, hf, mul_zero, sub_zero]

/-- The error column centered orthogonally to the actual Connes coefficient direction. -/
def centeredErrorColumn {x : ℕ} (hx : 80 ≤ 2 * π * x) (N : ℕ) : Idx N → ℝ :=
  center (errorColumn hx N) (Cvs.Approximant.ConnesVectorRealScale.connesCoef x N)

/-- The centered error column is even. -/
theorem centeredErrorColumn_even {x : ℕ} (hx : 80 ≤ 2 * π * x) (N : ℕ) (i : Idx N) :
    centeredErrorColumn hx N (negI N i) = centeredErrorColumn hx N i := by
  simp only [centeredErrorColumn, center, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    errorColumn_even, Cvs.Approximant.ConnesVectorRealScale.connesCoef_even]

/-- Centering makes the actual error column orthogonal to the actual coefficient direction. -/
theorem centeredErrorColumn_dot {x : ℕ} (hx : 80 ≤ 2 * π * x) (N : ℕ) :
    centeredErrorColumn hx N ⬝ᵥ Cvs.Approximant.ConnesVectorRealScale.connesCoef x N = 0 := center_dot _ _

/-- On the actual coefficient hyperplane, the centered column represents the same error pairing. -/
theorem QWbil_error_eq_centered_dot {x : ℕ} (hx : 80 ≤ 2 * π * x) (N : ℕ)
    (f : Idx N → ℝ) (hf : ∀ i, f (negI N i) = f i)
    (hperp : Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ⬝ᵥ f = 0) :
    Cvs.WeilForm.SymmetricBilinearForm.QWbil (Real.log_natCast_nonneg x) x (Nat.clog 2 x) (Cvs.Approximant.ConnesFormTruncation.connesError hx N)
      (Cvs.Approximant.CosineColumnTailPairing.modeMap (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) N f) = centeredErrorColumn hx N ⬝ᵥ f := by
  rw [QWbil_error_eq_dot hx N f hf, centeredErrorColumn, center_dot_of_perp _ _ _ hperp]

/-- The actual centered matrix column differs from the centered arithmetic tail by the centered error. -/
theorem centered_connesColumn_eq {x : ℕ} (hx : 80 ≤ 2 * π * x) (N : ℕ) :
    center (Cvs.Approximant.CosineColumnTailPairing.connesColumn hx N) (Cvs.Approximant.ConnesVectorRealScale.connesCoef x N)
      = center (tailColumn x N) (Cvs.Approximant.ConnesVectorRealScale.connesCoef x N) - centeredErrorColumn hx N := by
  rw [connesColumn_eq_tail_sub_error, center_sub]
  rfl

/-- Centering the actual matrix column removes exactly its normalized Rayleigh coefficient. -/
theorem center_connesColumn_eq_rayleigh {x : ℕ} (hx : 80 ≤ 2 * π * x) (N : ℕ)
    (hs : Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ⬝ᵥ Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ≠ 0) :
    let α := Cvs.Approximant.ConnesVectorRealScale.connesCoef x N
    let v := Cvs.Approximant.ConnesVectorRealScale.connesVec (fun _ => N) x
    let q := v ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M x (Nat.clog 2 x) (Real.log x) (Cvs.Finite.SymmetricModeSet.mode N) *ᵥ v)
    center (Cvs.Approximant.CosineColumnTailPairing.connesColumn hx N) α = Cvs.Approximant.CosineColumnTailPairing.connesColumn hx N - (Real.log x * q) • α := by
  dsimp only
  let α := Cvs.Approximant.ConnesVectorRealScale.connesCoef x N
  let v := Cvs.Approximant.ConnesVectorRealScale.connesVec (fun _ => N) x
  let M := Cvs.Finite.TruncationQuadraticForm.M x (Nat.clog 2 x) (Real.log x) (Cvs.Finite.SymmetricModeSet.mode N)
  let t := (Real.sqrt (α ⬝ᵥ α))⁻¹
  have hv : v = t • α := by
    simp only [v, Cvs.Approximant.ConnesVectorRealScale.connesVec, if_neg hs]
    rfl
  have ht : t ^ 2 * (α ⬝ᵥ α) = 1 := by
    dsimp only [t]
    rw [inv_pow, Real.sq_sqrt (Cvs.Upstream.SymmetricMatrixBottom.dotProduct_self_nonneg' α), inv_mul_cancel₀ hs]
  have hq : v ⬝ᵥ (M *ᵥ v) = t ^ 2 * (α ⬝ᵥ (M *ᵥ α)) := by
    rw [hv, Cvs.Finite.DiscreteTwoGap.quad_smul]
  have hC : Cvs.Approximant.CosineColumnTailPairing.connesColumn hx N = Real.log x • (M *ᵥ α) := by
    funext i
    exact Cvs.Approximant.CosineColumnTailPairing.connesColumn_eq_mulVec hx N i
  have hc : (Cvs.Approximant.CosineColumnTailPairing.connesColumn hx N ⬝ᵥ α) / (α ⬝ᵥ α)
      = Real.log x * (v ⬝ᵥ (M *ᵥ v)) := by
    rw [hC, smul_dotProduct, smul_eq_mul, dotProduct_comm (M *ᵥ α) α, hq]
    apply (div_eq_iff hs).mpr
    calc Real.log x * (α ⬝ᵥ (M *ᵥ α))
        = (Real.log x * (α ⬝ᵥ (M *ᵥ α))) * (t ^ 2 * (α ⬝ᵥ α)) := by rw [ht, mul_one]
      _ = _ := by ring
  change center (Cvs.Approximant.CosineColumnTailPairing.connesColumn hx N) α = _
  rw [center, hc]

/-- The normalized actual residual is exactly the squared orthogonally centered matrix column. -/
theorem connes_residual_eq_centered {x : ℕ} (hx : 80 ≤ 2 * π * x) (N : ℕ)
    (hs : Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ⬝ᵥ Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ≠ 0) :
    let α := Cvs.Approximant.ConnesVectorRealScale.connesCoef x N
    let v := Cvs.Approximant.ConnesVectorRealScale.connesVec (fun _ => N) x
    Real.log x ^ 2 * (α ⬝ᵥ α) * Cvs.Route.JointGapFromResidual.residualSq x (Nat.clog 2 x) (Real.log x) N v
      = center (Cvs.Approximant.CosineColumnTailPairing.connesColumn hx N) α ⬝ᵥ center (Cvs.Approximant.CosineColumnTailPairing.connesColumn hx N) α := by
  dsimp only
  rw [center_connesColumn_eq_rayleigh hx N hs]
  simpa only [dotProduct, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sq] using
    Cvs.Approximant.CosineColumnTailPairing.connes_residual_eq_column hx N hs

/-- The actual normalized residual is exactly the centered arithmetic tail minus its centered error. -/
theorem connes_residual_eq_tail_error {x : ℕ} (hx : 80 ≤ 2 * π * x) (N : ℕ)
    (hs : Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ⬝ᵥ Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ≠ 0) :
    let α := Cvs.Approximant.ConnesVectorRealScale.connesCoef x N
    let v := Cvs.Approximant.ConnesVectorRealScale.connesVec (fun _ => N) x
    Real.log x ^ 2 * (α ⬝ᵥ α) * Cvs.Route.JointGapFromResidual.residualSq x (Nat.clog 2 x) (Real.log x) N v
      = (center (tailColumn x N) α - centeredErrorColumn hx N) ⬝ᵥ
        (center (tailColumn x N) α - centeredErrorColumn hx N) := by
  dsimp only
  rw [connes_residual_eq_centered hx N hs, centered_connesColumn_eq]

/-- The actual truncation error column obeys the whole unit-test budget in squared norm. -/
theorem errorColumn_sq_le_budget {x : ℕ} (hx : 80 ≤ 2 * π * x) (N : ℕ) :
    ∑ i, errorColumn hx N i ^ 2 ≤ Cvs.Approximant.TailRetainedModeCoupling.columnBudget x N ^ 2 := by
  let u := errorColumn hx N
  let m := u ⬝ᵥ u
  have hm0 : 0 ≤ m := Cvs.Upstream.SymmetricMatrixBottom.dotProduct_self_nonneg' u
  have hsum : ∑ i, u i ^ 2 = m := by simp only [m, dotProduct, sq]
  change ∑ i, u i ^ 2 ≤ _
  rw [hsum]
  by_cases hm : m = 0
  · rw [hm]
    exact sq_nonneg _
  · have hmpos : 0 < m := lt_of_le_of_ne hm0 (Ne.symm hm)
    let t := (Real.sqrt m)⁻¹
    let f := t • u
    have ht : t ^ 2 * m = 1 := by
      dsimp [t]
      rw [inv_pow, Real.sq_sqrt hm0, inv_mul_cancel₀ hm]
    have hf : ∀ i, f (negI N i) = f i := by
      intro i
      simp only [f, u, Pi.smul_apply, smul_eq_mul, errorColumn_even]
    have hunit : ∑ i, f i ^ 2 = 1 := by
      simp only [f, Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
      rw [hsum, ht]
    have hb := Cvs.Approximant.TailRetainedModeCoupling.abs_QWbil_connesError_unit_le hx N f hf hunit
    rw [QWbil_error_eq_dot hx N f hf] at hb
    have he : u ⬝ᵥ f = Real.sqrt m := by
      change u ⬝ᵥ (t • u) = _
      rw [dotProduct_smul, smul_eq_mul]
      change t * m = _
      dsimp [t]
      field_simp [(Real.sqrt_pos.mpr hmpos).ne']
      nlinarith [Real.sq_sqrt hm0]
    change |u ⬝ᵥ f| ≤ _ at hb
    rw [he, abs_of_nonneg (Real.sqrt_nonneg m)] at hb
    have hsq := pow_le_pow_left₀ (Real.sqrt_nonneg m) hb 2
    rwa [Real.sq_sqrt hm0] at hsq

/-- The norm of the actual truncation column vanishes despite the growing number of coordinates. -/
theorem tendsto_errorColumn_sq_zero {x : ℕ} (hx : 80 ≤ 2 * π * x) :
    Tendsto (fun N => ∑ i, errorColumn hx N i ^ 2) atTop (nhds 0) := by
  have hb : Tendsto (fun N => Cvs.Approximant.TailRetainedModeCoupling.columnBudget x N ^ 2) atTop (nhds 0) := by
    simpa using (Cvs.Approximant.TailRetainedModeCoupling.tendsto_columnBudget_zero hx).pow 2
  exact squeeze_zero (fun N => sum_nonneg fun i _ => sq_nonneg _)
    (errorColumn_sq_le_budget hx) hb

/-- The centered actual truncation column has the same squared error budget. -/
theorem centeredErrorColumn_sq_le_budget {x : ℕ} (hx : 80 ≤ 2 * π * x) (N : ℕ) :
    ∑ i, centeredErrorColumn hx N i ^ 2 ≤ Cvs.Approximant.TailRetainedModeCoupling.columnBudget x N ^ 2 := by
  have h : ∑ i, centeredErrorColumn hx N i ^ 2 ≤ ∑ i, errorColumn hx N i ^ 2 := by
    simpa only [dotProduct, sq, centeredErrorColumn] using
      center_sq_le (errorColumn hx N) (Cvs.Approximant.ConnesVectorRealScale.connesCoef x N)
  exact h.trans (errorColumn_sq_le_budget hx N)

/-- Orthogonally centering the actual error column preserves vanishing of its squared norm. -/
theorem tendsto_centeredErrorColumn_sq_zero {x : ℕ} (hx : 80 ≤ 2 * π * x) :
    Tendsto (fun N => ∑ i, centeredErrorColumn hx N i ^ 2) atTop (nhds 0) := by
  have hb : Tendsto (fun N => Cvs.Approximant.TailRetainedModeCoupling.columnBudget x N ^ 2) atTop (nhds 0) := by
    simpa using (Cvs.Approximant.TailRetainedModeCoupling.tendsto_columnBudget_zero hx).pow 2
  exact squeeze_zero (fun N => sum_nonneg fun i _ => sq_nonneg _)
    (centeredErrorColumn_sq_le_budget hx) hb

end Cvs.Approximant.ConnesErrorColumn
