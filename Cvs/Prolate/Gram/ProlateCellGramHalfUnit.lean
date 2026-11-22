import Mathlib
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.Approximant.SpineSubspace
import Cvs.L2a.PlaneBridgePlateau
import Cvs.L2a.WindowChainInputsProlate
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.Gram.EvenFirstCellEnergyGram
import Cvs.Prolate.LadderWronskian
import Cvs.Prolate.RungFamilyRangePartners
import Cvs.Route.Visibility.EvenFirstCellPoisson
import Cvs.Upstream.CellFloorSandwichPosDef
import Cvs.Upstream.PencilLayerBound
import Cvs.Upstream.SchurLayerFloors

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The prolate cell Gram `C` on `(1/2, 1]`, its definiteness, edge displacement and the weights `μ_j`

`C_nm = 2∫_{(1/2,1]} h_{4n}h_{4m}` for `n, m < x` at `c = 2πx`; `C ≻ 0` at `80 ≤ c` (Vandermonde in the levels);
`diag χ·C − C·diag χ = qpᵀ − pqᵀ` with `(p, q) = √(3/2)(h, h′)(1/2)`, inherited by every Schur layer; the main
cell energy is `½ wᵀCw`; `μ_j = 2(1 − λ_j)/((1 − λ_t)(1 + √λ_j)²)` is nondecreasing and `μ_t ≤ 12 − 8√2`.
-/

noncomputable section

open Real Set MeasureTheory Matrix Finset

namespace Cvs.Prolate.Gram.ProlateCellGramHalfUnit
open Cvs.ZeroCounting

open Cvs.Prolate.EvenRungsByIndex (rung rung₁ rung₂ lev lamR IsLevelIdx)
open Cvs.Prolate.Gram.EvenFirstCellEnergyGram (L2c)

/-! ### The cell vectors and the cell Gram -/

/-- The cell function `√2·h_{4n}` at `c = 2πx`. -/
def cellFun (x : ℕ) (n : Fin x) (u : ℝ) : ℝ := √2 * rung (2 * π * x) (2 * (n : ℕ)) u

/-- Every rung is continuous on `[−1, 1]`. -/
theorem continuousOn_rung (c : ℝ) (k : ℕ) : ContinuousOn (rung c k) (Icc (-1) 1) :=
  (Cvs.Approximant.DeepIndexSpineSpan.continuousOn_rawRung c (lev c k)).div_const _

/-- The cell function is square integrable on `(1/2, 1]`. -/
theorem memLp_cellFun (x : ℕ) (n : Fin x) :
    MemLp (cellFun x n) 2 (volume.restrict (Ioc (1 / 2 : ℝ) 1)) := by
  have hsub : Ioc (1 / 2 : ℝ) 1 ⊆ Icc (-1) 1 := fun u hu => ⟨by linarith [hu.1], hu.2⟩
  have hc : ContinuousOn (cellFun x n) (Icc (-1) 1) := (continuousOn_rung _ _).const_smul (√2)
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine MemLp.of_bound ((hc.mono hsub).aestronglyMeasurable measurableSet_Ioc) M ?_
  rw [ae_restrict_iff' measurableSet_Ioc]
  exact Filter.Eventually.of_forall fun u hu => hM u (hsub hu)

/-- The cell vector `Y_n = √2·h_{4n}` in `L²((1/2, 1])`. -/
def cellVec (x : ℕ) (n : Fin x) : L2c := (memLp_cellFun x n).toLp (cellFun x n)

/-- **The cell Gram** `C = gram Y`, `C_nm = ⟨Y_n, Y_m⟩_{L²(1/2,1)}`. -/
def cellGram (x : ℕ) : Matrix (Fin x) (Fin x) ℝ := gram ℝ (cellVec x)

/-- The quadratic form of the cell Gram: `wᵀCw = 2∫_{(1/2,1]} (Σ_n w_n h_{4n})²`. -/
theorem quad_cellGram (x : ℕ) (w : Fin x → ℝ) :
    w ⬝ᵥ (cellGram x *ᵥ w)
      = 2 * ∫ u in Ioc (1 / 2 : ℝ) 1, (∑ n, w n * rung (2 * π * x) (2 * (n : ℕ)) u) ^ 2 := by
  rw [cellGram, Cvs.Upstream.CellFloorSandwichPosDef.quad_gram, ← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  have hae : (fun u => inner ℝ ((∑ n, w n • cellVec x n) u) ((∑ n, w n • cellVec x n) u))
      =ᵐ[volume.restrict (Ioc (1 / 2 : ℝ) 1)]
        fun u => 2 * (∑ n, w n * rung (2 * π * x) (2 * (n : ℕ)) u) ^ 2 := by
    filter_upwards [Cvs.L2a.PlaneBridgePlateau.coeFn_sum_smul_toLp _ (memLp_cellFun x) w] with u hu
    rw [real_inner_self_eq_norm_sq]
    erw [hu]
    rw [Real.norm_eq_abs, sq_abs]
    simp only [cellFun]
    rw [show (∑ n, w n * (√2 * rung (2 * π * x) (2 * (n : ℕ)) u))
      = √2 * ∑ n, w n * rung (2 * π * x) (2 * (n : ℕ)) u by rw [Finset.mul_sum]; congr 1; ext; ring,
      mul_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [integral_congr_ae hae, integral_const_mul]

/-- The entries of the cell Gram: `C_nm = 2∫_{(1/2,1]} h_{4n}h_{4m}`. -/
theorem cellGram_apply (x : ℕ) (n m : Fin x) :
    cellGram x n m = 2 * ∫ u in Ioc (1 / 2 : ℝ) 1, rung (2 * π * x) (2 * (n : ℕ)) u
      * rung (2 * π * x) (2 * (m : ℕ)) u := by
  rw [cellGram, gram_apply, MeasureTheory.L2.inner_def, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_cellFun x n).coeFn_toLp, (memLp_cellFun x m).coeFn_toLp] with u h1 h2
  simp only [cellVec] at *
  rw [h1, h2, real_inner_eq_re_inner, RCLike.inner_apply, conj_trivial, RCLike.re_to_real, cellFun, cellFun]
  have : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  linear_combination (rung (2 * π * x) (2 * (n : ℕ)) u * rung (2 * π * x) (2 * (m : ℕ)) u) * this

/-! ### Definiteness: a combination vanishing on `(1/2, 1)` has zero coefficients -/

section Vanish

variable {ι : Type*} [Fintype ι]

/-- One application of the angular operator: if `Σ_n a_n r_n = 0` on an open `U` and each `r_n` solves the angular
equation at `χ_n` there, then `Σ_n a_n χ_n r_n = 0` on `U`. -/
theorem sum_mul_chi_eq_zero {U : Set ℝ} (hU : IsOpen U) {c : ℝ} {r r₁ r₂ : ι → ℝ → ℝ} {χ : ι → ℝ}
    (hd : ∀ n, ∀ s ∈ U, HasDerivAt (r n) (r₁ n s) s) (hd₁ : ∀ n, ∀ s ∈ U, HasDerivAt (r₁ n) (r₂ n s) s)
    (hode : ∀ n, ∀ s ∈ U, (1 - s ^ 2) * r₂ n s - 2 * s * r₁ n s - c ^ 2 * s ^ 2 * r n s + χ n * r n s = 0)
    (a : ι → ℝ) (h0 : ∀ s ∈ U, ∑ n, a n * r n s = 0) : ∀ s ∈ U, ∑ n, a n * χ n * r n s = 0 := by
  have hz : ∀ (F F' : ℝ → ℝ), (∀ s ∈ U, HasDerivAt F (F' s) s) → (∀ s ∈ U, F s = 0) → ∀ s ∈ U, F' s = 0 := by
    intro F F' hF h0 s hs
    have hev : F =ᶠ[nhds s] fun _ => 0 := Filter.eventually_of_mem (hU.mem_nhds hs) h0
    exact ((hF s hs).congr_of_eventuallyEq hev.symm).unique (hasDerivAt_const s 0)
  have hD : ∀ s ∈ U, HasDerivAt (fun u => ∑ n, a n * r n u) (∑ n, a n * r₁ n s) s := fun s hs =>
    HasDerivAt.fun_sum fun n _ => (hd n s hs).const_mul (a n)
  have hD₁ : ∀ s ∈ U, HasDerivAt (fun u => ∑ n, a n * r₁ n u) (∑ n, a n * r₂ n s) s := fun s hs =>
    HasDerivAt.fun_sum fun n _ => (hd₁ n s hs).const_mul (a n)
  have h1 := hz _ _ hD h0
  have h2 := hz _ _ hD₁ h1
  intro s hs
  have hsum : ∑ n, a n * ((1 - s ^ 2) * r₂ n s - 2 * s * r₁ n s - c ^ 2 * s ^ 2 * r n s + χ n * r n s) = 0 :=
    Finset.sum_eq_zero fun n _ => by rw [hode n s hs, mul_zero]
  have e : ∑ n, a n * ((1 - s ^ 2) * r₂ n s - 2 * s * r₁ n s - c ^ 2 * s ^ 2 * r n s + χ n * r n s)
      = (1 - s ^ 2) * ∑ n, a n * r₂ n s - 2 * s * ∑ n, a n * r₁ n s - c ^ 2 * s ^ 2 * ∑ n, a n * r n s
        + ∑ n, a n * χ n * r n s := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  rw [e, h2 s hs, h1 s hs, h0 s hs] at hsum
  linarith

/-- Iterating: `Σ_n a_n χ_n^m r_n = 0` on `U` for every `m`. -/
theorem sum_mul_chi_pow_eq_zero {U : Set ℝ} (hU : IsOpen U) {c : ℝ} {r r₁ r₂ : ι → ℝ → ℝ} {χ : ι → ℝ}
    (hd : ∀ n, ∀ s ∈ U, HasDerivAt (r n) (r₁ n s) s) (hd₁ : ∀ n, ∀ s ∈ U, HasDerivAt (r₁ n) (r₂ n s) s)
    (hode : ∀ n, ∀ s ∈ U, (1 - s ^ 2) * r₂ n s - 2 * s * r₁ n s - c ^ 2 * s ^ 2 * r n s + χ n * r n s = 0)
    (a : ι → ℝ) (h0 : ∀ s ∈ U, ∑ n, a n * r n s = 0) (m : ℕ) : ∀ s ∈ U, ∑ n, a n * χ n ^ m * r n s = 0 := by
  induction m with
  | zero => simpa using h0
  | succ m ih =>
    have := sum_mul_chi_eq_zero hU hd hd₁ hode (fun n => a n * χ n ^ m) ih
    intro s hs
    simpa [pow_succ, mul_assoc] using this s hs

end Vanish

/-- The levels `χ_n = lev c (2n)` of the rungs `n < x` exist at `80 ≤ 2πx`. -/
theorem exists_level {x : ℕ} (hx : 80 ≤ 2 * π * x) (n : Fin x) :
    ∃ χ, IsLevelIdx (2 * π * x) (2 * (n : ℕ)) χ :=
  Cvs.Prolate.RungFamilyRangePartners.exists_main hx ⟨n, Finset.mem_range.2 n.2⟩

/-- The rung levels are strictly increasing in `n`. -/
theorem lev_strictMono {x : ℕ} (hx : 80 ≤ 2 * π * x) :
    StrictMono fun n : Fin x => lev (2 * π * x) (2 * (n : ℕ)) := fun n m hnm =>
  Cvs.Prolate.EvenRungsByIndex.lev_lt (exists_level hx m) (by have : (n : ℕ) < m := hnm; omega)

/-- **The rungs are independent on `(1/2, 1)`**: `Σ_n a_n h_{4n} = 0` there forces `a = 0`. -/
theorem eq_zero_of_sum_rung {x : ℕ} (hx : 80 ≤ 2 * π * x) (a : Fin x → ℝ)
    (h0 : ∀ s ∈ Ioo (1 / 2 : ℝ) 1, ∑ n, a n * rung (2 * π * x) (2 * (n : ℕ)) s = 0) : a = 0 := by
  set c := 2 * π * (x : ℝ)
  have hU : Ioo (1 / 2 : ℝ) 1 ⊆ uIcc (-1) 1 := by
    rw [Set.uIcc_of_le (by norm_num)]; exact fun s hs => ⟨by linarith [hs.1], hs.2.le⟩
  have hspec := fun n : Fin x => Cvs.Prolate.EvenRungsByIndex.rung_spec (exists_level hx n)
  have hpow := sum_mul_chi_pow_eq_zero isOpen_Ioo (c := c) (χ := fun n : Fin x => lev c (2 * (n : ℕ)))
    (fun n s hs => (hspec n).1 s (hU hs)) (fun n s hs => (hspec n).2.1 s (hU hs))
    (fun n s hs => (hspec n).2.2.2.1 s (hU hs)) a h0
  have hdet : (vandermonde fun n : Fin x => lev c (2 * (n : ℕ))).det ≠ 0 :=
    det_vandermonde_ne_zero_iff.2 (lev_strictMono hx).injective
  have hpt : ∀ s ∈ Ioo (1 / 2 : ℝ) 1, ∀ n, a n * rung c (2 * (n : ℕ)) s = 0 := by
    intro s hs
    have hv : (fun n => a n * rung c (2 * (n : ℕ)) s) ᵥ* vandermonde (fun n : Fin x => lev c (2 * (n : ℕ)))
        = 0 := by
      ext m
      simp only [vecMul, dotProduct, vandermonde_apply, Pi.zero_apply]
      rw [← hpow m s hs]
      refine Finset.sum_congr rfl fun n _ => ?_
      ring
    exact congrFun (eq_zero_of_vecMul_eq_zero hdet hv)
  ext n
  have hcont : ContinuousOn (fun s => a n * rung c (2 * (n : ℕ)) s) (Icc (1 / 2) 1) :=
    ((continuousOn_rung c _).mono fun s (hs : s ∈ Icc (1 / 2 : ℝ) 1) => ⟨by linarith [hs.1], hs.2⟩).const_smul (a n)
  have heq : EqOn (fun s => a n * rung c (2 * (n : ℕ)) s) (fun _ => 0) (Icc (1 / 2) 1) :=
    Set.EqOn.of_subset_closure (fun s hs => hpt s hs n) hcont continuousOn_const Ioo_subset_Icc_self
      (by rw [closure_Ioo (by norm_num)])
  have h1 := heq (right_mem_Icc.2 (by norm_num))
  simp only at h1
  rcases mul_eq_zero.1 h1 with h | h
  · exact h
  · exact absurd h (Cvs.Prolate.EvenRungsByIndex.rung_one_ne_zero (exists_level hx n))

/-- **`C ≻ 0`** at `80 ≤ 2πx`. -/
theorem cellGram_posDef {x : ℕ} (hx : 80 ≤ 2 * π * x) : (cellGram x).PosDef := by
  rw [cellGram, Matrix.posDef_gram_iff_linearIndependent, Fintype.linearIndependent_iff]
  intro a ha
  have hae : ∀ᵐ u ∂(volume.restrict (Ioc (1 / 2 : ℝ) 1)), ∑ n, a n * cellFun x n u = 0 := by
    filter_upwards [Cvs.L2a.PlaneBridgePlateau.coeFn_sum_smul_toLp _ (memLp_cellFun x) a, ha ▸ Lp.coeFn_zero ..] with u h1 h2
    rw [← h1]
    exact h2
  have hae' : (fun u => ∑ n, a n * cellFun x n u) =ᵐ[volume.restrict (Ioo (1 / 2 : ℝ) 1)] fun _ => 0 :=
    ae_restrict_of_ae_restrict_of_subset Ioo_subset_Ioc_self hae
  have hc : ContinuousOn (fun u => ∑ n, a n * cellFun x n u) (Ioo (1 / 2 : ℝ) 1) :=
    continuousOn_finsetSum _ fun n _ => (((continuousOn_rung _ _).const_smul (√2)).mono
      fun s (hs : s ∈ Ioo (1 / 2 : ℝ) 1) => ⟨by linarith [hs.1], hs.2.le⟩).const_smul (a n)
  have heq := Measure.eqOn_open_of_ae_eq hae' isOpen_Ioo hc continuousOn_const
  have h0 := eq_zero_of_sum_rung hx (fun n => √2 * a n) fun s hs => by
    have := heq hs
    simp only [cellFun] at this
    rw [← this]
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  intro n
  have := congrFun h0 n
  simp only [Pi.zero_apply, mul_eq_zero, Real.sqrt_eq_zero'] at this
  rcases this with h | h
  · norm_num at h
  · exact h

/-! ### The edge displacement at `t = 1/2` -/

/-- The edge trace `p_n = √(3/2)·h_{4n}(1/2)`. -/
def edgeP (x : ℕ) (n : Fin x) : ℝ := √(3 / 2) * rung (2 * π * x) (2 * (n : ℕ)) (1 / 2)

/-- The edge derivative `q_n = √(3/2)·h_{4n}′(1/2)`. -/
def edgeQ (x : ℕ) (n : Fin x) : ℝ := √(3 / 2) * rung₁ (2 * π * x) (2 * (n : ℕ)) (1 / 2)

/-- The cell Gram is symmetric. -/
theorem cellGram_comm (x : ℕ) (n m : Fin x) : cellGram x n m = cellGram x m n := by
  rw [cellGram, gram_apply, gram_apply, real_inner_comm]

/-- **The Green identity at `t = 1/2`** (Cvs.Prolate.LadderWronskian): `(χ_m − χ_n) C_nm = q_m p_n − p_m q_n`. -/
theorem cellGram_green {x : ℕ} (hx : 80 ≤ 2 * π * x) (n m : Fin x) :
    (lev (2 * π * x) (2 * (m : ℕ)) - lev (2 * π * x) (2 * (n : ℕ))) * cellGram x n m
      = edgeQ x m * edgeP x n - edgeP x m * edgeQ x n := by
  obtain ⟨ha, ha₁, -, hang, -, -⟩ := Cvs.Prolate.EvenRungsByIndex.rung_spec (exists_level hx n)
  obtain ⟨hb, hb₁, -, hangb, -, -⟩ := Cvs.Prolate.EvenRungsByIndex.rung_spec (exists_level hx m)
  have hw := Cvs.Prolate.LadderWronskian.wronskian_eq ha ha₁ hang hb hb₁ hangb (s := 1 / 2) ⟨by norm_num, by norm_num⟩
  rw [intervalIntegral.integral_of_le (by norm_num)] at hw
  have h32 : √(3 / 2) * √(3 / 2) = 3 / 2 := Real.mul_self_sqrt (by norm_num)
  rw [cellGram_apply, edgeP, edgeP, edgeQ, edgeQ]
  linear_combination -2 * hw - (rung₁ (2 * π * x) (2 * (m : ℕ)) (1 / 2) * rung (2 * π * x) (2 * (n : ℕ)) (1 / 2)
    - rung (2 * π * x) (2 * (m : ℕ)) (1 / 2) * rung₁ (2 * π * x) (2 * (n : ℕ)) (1 / 2)) * h32

/-- The edge generator `G = [q p]`. -/
def edgeGen (x : ℕ) : Matrix (Fin x) (Fin 2) ℝ := Matrix.of fun n i => ![edgeQ x n, edgeP x n] i

/-- The symplectic form `J = [[0, 1], [−1, 0]]`. -/
def symp : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -1, 0]

/-- **Prop 5.2 for the cell Gram**: `diag χ·C − C·diag χ = GJGᵀ = qpᵀ − pqᵀ`. -/
theorem cellGram_displacement {x : ℕ} (hx : 80 ≤ 2 * π * x) :
    diagonal (fun n : Fin x => lev (2 * π * x) (2 * (n : ℕ))) * cellGram x
      - cellGram x * diagonal (fun n : Fin x => lev (2 * π * x) (2 * (n : ℕ)))
      = edgeGen x * symp * (edgeGen x)ᵀ := by
  ext n m
  have h := cellGram_green hx m n
  rw [cellGram_comm x m n] at h
  rw [Matrix.sub_apply, diagonal_mul, mul_diagonal]
  simp [Matrix.mul_apply, Fin.sum_univ_two, edgeGen, symp, Function.swap]
  linear_combination h

/-- **Prop 5.2 on every layer**: `Λ_A S_A − S_A Λ_A = S_A X J Xᵀ S_A`, `X = (C⁻¹G)_A`, for `A = {j ≥ k}`. -/
theorem cellLayer_displacement {x : ℕ} (hx : 80 ≤ 2 * π * x) (k : Fin x) :
    diagonal (fun j : {j // k ≤ j} => lev (2 * π * x) (2 * ((j : Fin x) : ℕ))) * Cvs.Upstream.PencilLayerBound.layer (cellGram x) k
      - Cvs.Upstream.PencilLayerBound.layer (cellGram x) k * diagonal (fun j : {j // k ≤ j} => lev (2 * π * x) (2 * ((j : Fin x) : ℕ)))
      = Cvs.Upstream.PencilLayerBound.layer (cellGram x) k
          * ((cellGram x)⁻¹ * edgeGen x).submatrix (Subtype.val : {j // k ≤ j} → Fin x) (id : Fin 2 → Fin 2) * symp
          * (((cellGram x)⁻¹ * edgeGen x).submatrix (Subtype.val : {j // k ≤ j} → Fin x) (id : Fin 2 → Fin 2))ᵀ
          * Cvs.Upstream.PencilLayerBound.layer (cellGram x) k :=
  Cvs.Upstream.SchurLayerFloors.layer_displacement_lowRank (cellGram_posDef hx) _ _ _ (cellGram_displacement hx) k

/-! ### The weights `μ_j` -/

/-- `x ≥ 2` at `80 ≤ 2πx`. -/
theorem two_le_of_scale {x : ℕ} (hx : 80 ≤ 2 * π * x) : 2 ≤ x := by
  by_contra h
  have : (x : ℝ) ≤ 1 := by exact_mod_cast (by omega : x ≤ 1)
  nlinarith [Real.pi_lt_four, Real.pi_pos]

/-- The concentration eigenvalue `λ_n = λ_{4n}` of rung `n` at `c = 2πx`. -/
def lam (x n : ℕ) : ℝ := lamR (2 * π * x) (2 * n)

/-- The top eigenvalue `λ_t`, `t = x − 1`. -/
def lamTop (x : ℕ) : ℝ := lam x (x - 1)

/-- **The weights** `μ_n = 2(1 − λ_n)/((1 − λ_t)(1 + √λ_n)²)`. -/
def mu (x n : ℕ) : ℝ := 2 * (1 - lam x n) / ((1 - lamTop x) * (1 + √(lam x n)) ^ 2)

/-- The increments `δ_n = μ_n − μ_{n−1}` (with `μ_{−1} = 0`). -/
def muInc (x n : ℕ) : ℝ := mu x n - if n = 0 then 0 else mu x (n - 1)

/-- Telescoping on the naturals: `Σ_{i ≤ J} (f i − f (i − 1)) = f J` with `f (−1) = 0`. -/
theorem sum_range_inc (f : ℕ → ℝ) (J : ℕ) :
    ∑ i ∈ Finset.range (J + 1), (f i - if i = 0 then 0 else f (i - 1)) = f J := by
  induction J with
  | zero => simp
  | succ J ih => rw [Finset.sum_range_succ, ih]; simp

/-- `μ_j = Σ_{k ≤ j} δ_k` on `Fin x`. -/
theorem mu_eq_sum (x : ℕ) (j : Fin x) :
    mu x j = ∑ k ∈ univ.filter (· ≤ j), muInc x k := by
  have h1 : ∑ k ∈ univ.filter (· ≤ j), muInc x k
      = ∑ k : Fin x, (fun i : ℕ => if i ≤ (j : ℕ) then muInc x i else 0) k := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun k _ => ?_
    show (if k ≤ j then muInc x k else 0) = if (k : ℕ) ≤ j then muInc x k else 0
    by_cases h : (k : ℕ) ≤ j
    · rw [ite_eq_left h, ite_eq_left (Fin.le_iff_val_le_val.mpr h)]
    · rw [ite_eq_right h, ite_eq_right fun h' => h (Fin.le_iff_val_le_val.mp h')]
  rw [h1, Fin.sum_univ_eq_sum_range (fun i : ℕ => if i ≤ (j : ℕ) then muInc x i else 0) x,
    ← Finset.sum_filter (fun i : ℕ => i ≤ (j : ℕ)) (fun i => muInc x i)]
  have h2 : (Finset.range x).filter (· ≤ (j : ℕ)) = Finset.range (j + 1) := by
    ext i; simp only [Finset.mem_filter, Finset.mem_range]; omega
  rw [h2]
  exact (sum_range_inc (mu x) j).symm

/-- `λ_n ≥ 0`. -/
theorem lam_nonneg (x n : ℕ) : 0 ≤ lam x n := sq_nonneg _

/-- `λ` is antitone along the rungs `n ≤ m < x`. -/
theorem lam_anti {x : ℕ} (hx : 80 ≤ 2 * π * x) {n m : ℕ} (hm : m < x) (hnm : n ≤ m) : lam x m ≤ lam x n :=
  Cvs.Prolate.EvenRungsByIndex.lamR_anti (by linarith) (exists_level hx ⟨m, hm⟩) (by omega)

/-- `λ_n ≤ 1`. -/
theorem lam_le_one {x : ℕ} (hx : 80 ≤ 2 * π * x) {n : ℕ} (hn : n < x) : lam x n ≤ 1 :=
  (lam_anti hx hn (Nat.zero_le n)).trans (by unfold lam; simpa using Cvs.Prolate.EvenRungsByIndex.lamR_zero_le_one (by linarith))

/-- `λ_t < 1`. -/
theorem lamTop_lt_one {x : ℕ} (hx : 80 ≤ 2 * π * x) : lamTop x < 1 := by
  have h2 := two_le_of_scale hx
  exact Cvs.Prolate.EvenRungsByIndex.lamR_lt_one (by linarith) (exists_level hx ⟨x - 1, by omega⟩) (by omega)

/-- `λ_t ≥ ½` (Cvs.L2a.WindowChainInputsProlate). -/
theorem half_le_lamTop {x : ℕ} (hx : 80 ≤ 2 * π * x) : 1 / 2 ≤ lamTop x := by
  have h2 := two_le_of_scale hx
  exact Cvs.L2a.WindowChainInputsProlate.half_le_lamR hx (by omega)

/-- `(1 − λ)/(1 + √λ)² = (1 − √λ)/(1 + √λ)` for `λ ≥ 0`. -/
theorem one_sub_div_sq {l : ℝ} (hl : 0 ≤ l) : (1 - l) / (1 + √l) ^ 2 = (1 - √l) / (1 + √l) := by
  have hs : 0 < 1 + √l := by positivity
  have hl' : l = √l ^ 2 := (sq_sqrt hl).symm
  rw [div_eq_div_iff (by positivity) hs.ne']
  nth_rewrite 1 [hl']
  ring

/-- `μ_n ≥ 0`. -/
theorem mu_nonneg {x : ℕ} (hx : 80 ≤ 2 * π * x) {n : ℕ} (hn : n < x) : 0 ≤ mu x n := by
  have := lam_le_one hx hn
  have := lamTop_lt_one hx
  unfold mu
  apply div_nonneg <;> nlinarith [sq_nonneg (1 + √(lam x n))]

/-- **`μ` is nondecreasing**: `δ_k ≥ 0` for every rung `k < x`. -/
theorem muInc_nonneg {x : ℕ} (hx : 80 ≤ 2 * π * x) {k : ℕ} (hk : k < x) : 0 ≤ muInc x k := by
  unfold muInc
  split_ifs with h0
  · simpa using mu_nonneg hx hk
  · have hanti := lam_anti hx hk (Nat.sub_le k 1)
    have ht := lamTop_lt_one hx
    have hsq : √(lam x k) ≤ √(lam x (k - 1)) := Real.sqrt_le_sqrt hanti
    have hf : (1 - √(lam x (k - 1))) / (1 + √(lam x (k - 1))) ≤ (1 - √(lam x k)) / (1 + √(lam x k)) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [Real.sqrt_nonneg (lam x k)]
    have e : ∀ n, mu x n = 2 / (1 - lamTop x) * ((1 - √(lam x n)) / (1 + √(lam x n))) := by
      intro n
      rw [mu, ← one_sub_div_sq (lam_nonneg x n)]
      field_simp
    rw [sub_nonneg, e, e]
    exact mul_le_mul_of_nonneg_left hf (div_nonneg (by norm_num) (by linarith))

/-- **`μ_t ≤ μ* = 12 − 8√2`** from `λ_t ≥ ½`. -/
theorem mu_top_le {x : ℕ} (hx : 80 ≤ 2 * π * x) : mu x (x - 1) ≤ 12 - 8 * √2 := by
  have ht := lamTop_lt_one hx
  have hh := half_le_lamTop hx
  have hs : √(1 / 2) ≤ √(lamTop x) := Real.sqrt_le_sqrt hh
  have h12 : √(1 / 2 : ℝ) = √2 / 2 := by
    have : (√2 / 2) ^ 2 = 1 / 2 := by rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num
    rw [← this, Real.sqrt_sq (by positivity)]
  rw [h12] at hs
  have h2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h2l : √2 < 3 / 2 := by nlinarith [Real.sqrt_nonneg 2]
  have hm : mu x (x - 1) = 2 / (1 + √(lamTop x)) ^ 2 := by
    rw [mu, lamTop]
    field_simp
    have : 1 - lam x (x - 1) ≠ 0 := by rw [← lamTop]; linarith
    field_simp
  rw [hm, div_le_iff₀ (by positivity)]
  nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg (lamTop x)]

/-! ### The levels in units of `c²` -/

/-- `T_n = χ_n/c²` at `c = 2πx`. -/
def levT (x : ℕ) (n : Fin x) : ℝ := lev (2 * π * x) (2 * (n : ℕ)) / (2 * π * x) ^ 2

/-- `T` is strictly increasing in `n`. -/
theorem levT_strictMono {x : ℕ} (hx : 80 ≤ 2 * π * x) : StrictMono (levT x) := fun n m hnm =>
  div_lt_div_of_pos_right (lev_strictMono hx hnm) (by positivity)

/-! ### The main cell profile in the cell Gram -/

/-- The prolate coefficients `b̃` of a spine class: `b̃_0 = −Σ_j b_j α_j`, `b̃_n = b_n` for `n ≥ 1`. -/
def coefH (x : ℕ) (b : Cvs.Approximant.SpineSubspace.SF x → ℝ) (n : Fin x) : ℝ :=
  if h : (n : ℕ) ∈ Cvs.Approximant.SpineSubspace.SF x then b ⟨n, h⟩ else -∑ j, b j * Cvs.Approximant.DeepIndexSpineSpan.alpha (2 * π * x) j

/-- The weighted coefficients `w_n = (1 + √λ_n) b̃_n`. -/
def coefW (x : ℕ) (b : Cvs.Approximant.SpineSubspace.SF x → ℝ) (n : Fin x) : ℝ := (1 + √(lam x n)) * coefH x b n

/-- **The main cell profile in prolate coordinates**: `cellMain = Σ_n w_n h_{4n}`. -/
theorem cellMain_eq_sum {x : ℕ} (hx : 1 ≤ x) (b : Cvs.Approximant.SpineSubspace.SF x → ℝ) (s : ℝ) :
    Cvs.Route.Visibility.EvenFirstCellPoisson.cellMain x b s = ∑ n, coefW x b n * rung (2 * π * x) (2 * (n : ℕ)) s := by
  set c := 2 * π * (x : ℝ)
  set f : ℕ → ℝ := fun i => (1 + √(lam x i))
    * (if h : i ∈ Cvs.Approximant.SpineSubspace.SF x then b ⟨i, h⟩ else -∑ j, b j * Cvs.Approximant.DeepIndexSpineSpan.alpha c j) * rung c (2 * i) s
  have h1 : ∑ n : Fin x, coefW x b n * rung c (2 * (n : ℕ)) s = ∑ i ∈ Finset.range x, f i :=
    Fin.sum_univ_eq_sum_range f x
  rw [h1, ← Finset.sum_filter_add_sum_filter_not (Finset.range x) (1 ≤ ·)]
  have h0 : (Finset.range x).filter (fun i => ¬ 1 ≤ i) = {0} := by
    ext i; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]; omega
  rw [h0, Finset.sum_singleton]
  have hSF : ∑ i ∈ (Finset.range x).filter (1 ≤ ·), f i
      = ∑ j : Cvs.Approximant.SpineSubspace.SF x, (1 + √(lam x j)) * b j * rung c (2 * (j : ℕ)) s := by
    rw [← Finset.sum_coe_sort]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hj : (j : ℕ) ∈ Cvs.Approximant.SpineSubspace.SF x := j.2
    simp only [f, dite_eq_left hj]
  have h0f : f 0 = (1 + √(lamR c 0)) * (-∑ j, b j * Cvs.Approximant.DeepIndexSpineSpan.alpha c j) * rung c 0 s := by
    have : (0 : ℕ) ∉ Cvs.Approximant.SpineSubspace.SF x := by simp [Cvs.Approximant.SpineSubspace.SF]
    simp only [f, dite_eq_right this, lam, mul_zero]
    rfl
  rw [hSF, h0f, Cvs.Route.Visibility.EvenFirstCellPoisson.cellMain]
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [sub_eq_add_neg]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    simp only [lam]
    ring
  · rw [mul_neg, neg_mul, Finset.mul_sum, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    ring

/-- **The main cell energy is the cell Gram form**: `∫_{(1/2,1]} cellMain² = ½ wᵀCw`. -/
theorem integral_cellMain_sq {x : ℕ} (hx : 1 ≤ x) (b : Cvs.Approximant.SpineSubspace.SF x → ℝ) :
    ∫ u in Ioc (1 / 2 : ℝ) 1, Cvs.Route.Visibility.EvenFirstCellPoisson.cellMain x b u ^ 2 = coefW x b ⬝ᵥ (cellGram x *ᵥ coefW x b) / 2 := by
  rw [quad_cellGram]
  simp only [cellMain_eq_sum hx]
  ring

/-- The prolate energy `E(b) = Σ_n (1 − λ_n) b̃_n²`. -/
def energyE (x : ℕ) (b : Cvs.Approximant.SpineSubspace.SF x → ℝ) : ℝ := ∑ n : Fin x, (1 - lam x n) * coefH x b n ^ 2

/-- `E(b) ≥ 0`. -/
theorem energyE_nonneg {x : ℕ} (hx : 80 ≤ 2 * π * x) (b : Cvs.Approximant.SpineSubspace.SF x → ℝ) : 0 ≤ energyE x b :=
  Finset.sum_nonneg fun n _ => mul_nonneg (by linarith [lam_le_one hx n.2]) (sq_nonneg _)

/-- **I1**: `E(b) ≤ (1 − λ_t)·λ_max(diag μ, C)·∫_{(1/2,1]} cellMain²`. -/
theorem energyE_le {x : ℕ} (hx : 80 ≤ 2 * π * x) (b : Cvs.Approximant.SpineSubspace.SF x → ℝ) :
    energyE x b ≤ (1 - lamTop x) * Cvs.Upstream.PencilLayerBound.pencilTop (fun n : Fin x => mu x n) (cellGram x) Set.univ
      * ∫ u in Ioc (1 / 2 : ℝ) 1, Cvs.Route.Visibility.EvenFirstCellPoisson.cellMain x b u ^ 2 := by
  have hx1 : 1 ≤ x := by have := two_le_of_scale hx; omega
  have ht := lamTop_lt_one hx
  have hP := Cvs.Upstream.PencilLayerBound.sum_le_pencilTop (cellGram_posDef hx) (fun n : Fin x => mu_nonneg hx n.2)
    (Set.mem_univ (coefW x b))
  rw [integral_cellMain_sq hx1]
  have e : ∑ n : Fin x, mu x n * coefW x b n ^ 2 = 2 / (1 - lamTop x) * energyE x b := by
    rw [energyE, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    have h1 : (0 : ℝ) < 1 + √(lam x n) := by positivity
    rw [mu, coefW]
    field_simp
  rw [e] at hP
  have h1 : 0 < 1 - lamTop x := by linarith
  have := mul_le_mul_of_nonneg_left hP (by linarith : (0 : ℝ) ≤ (1 - lamTop x) / 2)
  calc energyE x b = (1 - lamTop x) / 2 * (2 / (1 - lamTop x) * energyE x b) := by field_simp
    _ ≤ _ := this
    _ = _ := by ring

end Cvs.Prolate.Gram.ProlateCellGramHalfUnit
