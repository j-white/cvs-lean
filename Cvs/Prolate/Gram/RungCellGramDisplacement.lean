import Mathlib
import Cvs.Finite.ParityDisplacementEigenspaces
import Cvs.Prolate.EvenRungParseval
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.RungFamilyRangePartners
import Cvs.Prolate.SlepianEvenOrdering

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The rung cell Gram: `0 ≺ C ≤ 1`, and its displacement identity under Schur complements

`[diag ω, G] = euᵀ − ueᵀ` for symmetric invertible `G` gives `[diag ω, G⁻¹] = (G⁻¹u)(G⁻¹e)ᵀ − (G⁻¹e)(G⁻¹u)ᵀ`, so the
Schur complement of `M ≻ 0` onto `T` has generators `e_T − M_TF M_FF⁻¹ e_F`. The rung cell Gram
`C_ab = 2∫_{1/2}^1 h_a h_b` has `[diag χ, C] = (3/2)(pqᵀ − qpᵀ)`, `p = h′(1/2)`, `q = h(1/2)`; angular solutions at
distinct levels are independent on any open set, so `C ≻ 0`, and evenness with orthonormality gives `C ≤ 1`.
-/

noncomputable section

open Matrix

namespace Cvs.Prolate.Gram.RungCellGramDisplacement
open Cvs.ZeroCounting

open Cvs.Finite.ParityDisplacementEigenspaces (Displacement)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The displacement identity in matrix form, under inversion and restriction -/

/-- `Displacement ω G e u` is the commutator identity `diag ω · G − G · diag ω = euᵀ − ueᵀ`. -/
theorem displacement_iff {om : ι → ℝ} {G : Matrix ι ι ℝ} {e u : ι → ℝ} :
    Displacement om G e u ↔ diagonal om * G - G * diagonal om = vecMulVec e u - vecMulVec u e := by
  constructor
  · intro h
    ext i j
    simp only [Matrix.sub_apply, diagonal_mul, mul_diagonal, vecMulVec_apply]
    linarith [h i j]
  · intro h i j
    have := congrFun (congrFun h i) j
    simp only [Matrix.sub_apply, diagonal_mul, mul_diagonal, vecMulVec_apply] at this
    linarith

/-- **Inversion**: `[diag ω, G] = euᵀ − ueᵀ` for symmetric invertible `G` gives
`[diag ω, G⁻¹] = (G⁻¹u)(G⁻¹e)ᵀ − (G⁻¹e)(G⁻¹u)ᵀ`. -/
theorem displacement_inv {om : ι → ℝ} {G : Matrix ι ι ℝ} {e u : ι → ℝ} (hs : Gᵀ = G) (hu : IsUnit G.det)
    (hd : Displacement om G e u) : Displacement om G⁻¹ (G⁻¹ *ᵥ u) (G⁻¹ *ᵥ e) := by
  rw [displacement_iff] at hd ⊢
  set D := diagonal om
  have e1 : G⁻¹ * (G * D) * G⁻¹ = D * G⁻¹ := by
    rw [← Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.one_mul]
  have e2 : G⁻¹ * (D * G) * G⁻¹ = G⁻¹ * D := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv _ hu, Matrix.mul_one]
  have key : D * G⁻¹ - G⁻¹ * D = G⁻¹ * (G * D - D * G) * G⁻¹ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, e1, e2]
  have hGD : G * D - D * G = vecMulVec u e - vecMulVec e u := by
    rw [← neg_sub, hd, neg_sub]
  have hsi : G⁻¹ᵀ = G⁻¹ := by rw [transpose_nonsing_inv, hs]
  have hv : ∀ x : ι → ℝ, x ᵥ* G⁻¹ = G⁻¹ *ᵥ x := fun x => by
    rw [← vecMul_transpose, hsi]
  rw [key, hGD, Matrix.mul_sub, Matrix.sub_mul, mul_vecMulVec, mul_vecMulVec, vecMulVec_mul,
    vecMulVec_mul, hv, hv]

omit [Fintype ι] [DecidableEq ι] in
/-- **Restriction**: the identity passes to every principal block. -/
theorem displacement_toBlock {om : ι → ℝ} {G : Matrix ι ι ℝ} {e u : ι → ℝ} (hd : Displacement om G e u)
    (p : ι → Prop) :
    Displacement (fun j : {j // p j} => om j) (G.toBlock p p) (fun j => e j) (fun j => u j) :=
  fun i j => hd i j

variable {p : ι → Prop} [DecidablePred p]

/-! ### The cell Gram of the rungs -/

open Cvs.Prolate.EvenRungsByIndex (rung rung₁ lev IsLevelIdx rung_spec)

/-- The cell Gram of the rungs `h_a = rung c (n a)` on `(1/2, 1)`: `C_ab = 2∫_{1/2}^1 h_a h_b`. -/
def cellGram (c : ℝ) (n : ι → ℕ) : Matrix ι ι ℝ :=
  Matrix.of fun a b => 2 * ∫ s in (1 / 2 : ℝ)..1, rung c (n a) s * rung c (n b) s

/-! ### Independence on an open set, positivity and the bound `C ≤ 1` -/

section Indep

variable {κ : Type*} [DecidableEq κ]

omit [DecidableEq κ] in
/-- If `Σ_{j ∈ s} a_j h_j` vanishes on an open `U` where `h_j′ = h₁_j`, then `Σ_{j ∈ s} a_j h₁_j` vanishes on `U`. -/
theorem sum_deriv_eq_zero_of_isOpen {s : Finset κ} {h h₁ : κ → ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hd : ∀ j, ∀ t ∈ U, HasDerivAt (h j) (h₁ j t) t) (a : κ → ℝ)
    (hz : ∀ t ∈ U, ∑ j ∈ s, a j * h j t = 0) : ∀ t ∈ U, ∑ j ∈ s, a j * h₁ j t = 0 := by
  intro t ht
  have h1 : HasDerivAt (fun y => ∑ j ∈ s, a j * h j y) (∑ j ∈ s, a j * h₁ j t) t :=
    HasDerivAt.fun_sum fun j _ => (hd j t ht).const_mul (a j)
  have h2 : HasDerivAt (fun y => ∑ j ∈ s, a j * h j y) 0 t :=
    (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq (Filter.eventually_of_mem (hU.mem_nhds ht) hz)
  exact h1.unique h2

/-- **Angular solutions at distinct levels are independent on an open set**: if `Σ_{j ∈ s} a_j h_j = 0` on `U`,
each `h_j` solving the angular equation at level `χ_j` there with `χ` injective on `s`, then each `a_j h_j = 0`. -/
theorem mul_eq_zero_of_sum_eq_zero {c : ℝ} {h h₁ h₂ : κ → ℝ → ℝ} {χ : κ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hd : ∀ j, ∀ t ∈ U, HasDerivAt (h j) (h₁ j t) t) (hd₁ : ∀ j, ∀ t ∈ U, HasDerivAt (h₁ j) (h₂ j t) t)
    (hode : ∀ j, ∀ t ∈ U, (1 - t ^ 2) * h₂ j t - 2 * t * h₁ j t - c ^ 2 * t ^ 2 * h j t + χ j * h j t = 0)
    (s : Finset κ) (hχ : Set.InjOn χ s) (a : κ → ℝ) (hz : ∀ t ∈ U, ∑ j ∈ s, a j * h j t = 0) :
    ∀ j ∈ s, ∀ t ∈ U, a j * h j t = 0 := by
  induction s using Finset.induction_on generalizing a with
  | empty => simp
  | @insert m s hm ih =>
    have hz1 := sum_deriv_eq_zero_of_isOpen hU hd a hz
    have hz2 := sum_deriv_eq_zero_of_isOpen hU hd₁ a hz1
    have hχz : ∀ t ∈ U, ∑ j ∈ insert m s, a j * χ j * h j t = 0 := by
      intro t ht
      have e : ∑ j ∈ insert m s, a j * χ j * h j t = -((1 - t ^ 2) * ∑ j ∈ insert m s, a j * h₂ j t
          - 2 * t * ∑ j ∈ insert m s, a j * h₁ j t - c ^ 2 * t ^ 2 * ∑ j ∈ insert m s, a j * h j t) := by
        simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun j _ => by linear_combination (a j) * hode j t ht
      rw [e, hz t ht, hz1 t ht, hz2 t ht]; ring
    have hs : ∀ t ∈ U, ∑ j ∈ s, a j * (χ j - χ m) * h j t = 0 := by
      intro t ht
      have h1 := hχz t ht
      have h2 := hz t ht
      rw [Finset.sum_insert hm] at h1 h2
      have e : ∑ j ∈ s, a j * (χ j - χ m) * h j t =
          ∑ j ∈ s, a j * χ j * h j t - χ m * ∑ j ∈ s, a j * h j t := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [e]
      linear_combination h1 - χ m * h2
    have hrest := ih (hχ.mono (Finset.coe_subset.mpr (Finset.subset_insert m s))) _ hs
    have hs' : ∀ j ∈ s, ∀ t ∈ U, a j * h j t = 0 := by
      intro j hj t ht
      have hne : χ j - χ m ≠ 0 := sub_ne_zero.mpr fun he => by
        have := hχ (Finset.mem_coe.mpr (Finset.mem_insert_of_mem hj))
          (Finset.mem_coe.mpr (Finset.mem_insert_self m s)) he
        exact hm (this ▸ hj)
      have h3 : (a j * h j t) * (χ j - χ m) = 0 := by linear_combination hrest j hj t ht
      exact (mul_eq_zero.mp h3).resolve_right hne
    intro j hj t ht
    rcases Finset.mem_insert.mp hj with rfl | hj
    · have h2 := hz t ht
      rw [Finset.sum_insert hm, Finset.sum_eq_zero fun i hi => hs' i hi t ht, add_zero] at h2
      exact h2
    · exact hs' j hj t ht

end Indep

omit [DecidableEq ι] in
/-- The integral of a squared combination: `∫(Σ_j a_j f_j)² = Σ_{ij} a_ia_j ∫ f_if_j` for continuous `f_j`. -/
theorem integral_sq_sum {f : ι → ℝ → ℝ} {α β : ℝ} (hf : ∀ j, ContinuousOn (f j) (Set.uIcc α β)) (a : ι → ℝ) :
    ∫ s in α..β, (∑ j, a j * f j s) ^ 2 = ∑ i, ∑ j, a i * a j * ∫ s in α..β, f i s * f j s := by
  simp_rw [sq, Finset.sum_mul_sum]
  rw [intervalIntegral.integral_finsetSum fun i _ => ?_]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [intervalIntegral.integral_finsetSum fun j _ => ?_]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_congr fun s _ => by ring
    · exact ((continuousOn_const.mul (hf i)).mul (continuousOn_const.mul (hf j))).intervalIntegrable
  · exact (continuousOn_finsetSum _ fun j _ =>
      (continuousOn_const.mul (hf i)).mul (continuousOn_const.mul (hf j))).intervalIntegrable

omit [Fintype ι] [DecidableEq ι] in
theorem continuousOn_rung_cell {c : ℝ} {k : ℕ} (h : ∃ χ, IsLevelIdx c k χ) {α β : ℝ}
    (hα : -1 ≤ α) (hβ : β ≤ 1) (hαβ : α ≤ β) : ContinuousOn (rung c k) (Set.uIcc α β) :=
  (Cvs.Prolate.EvenRungsByIndex.continuousOn_rung h).mono (by rw [Set.uIcc_of_le hαβ]; exact Set.Icc_subset_Icc hα hβ)

omit [DecidableEq ι] in
/-- **The cell energy**: `aᵀCa = 2∫_{1/2}^1 (Σ_j a_j h_j)²`. -/
theorem quad_cellGram {c : ℝ} {n : ι → ℕ} (h : ∀ a, ∃ χ, IsLevelIdx c (n a) χ) (a : ι → ℝ) :
    a ⬝ᵥ (cellGram c n *ᵥ a) = 2 * ∫ s in (1 / 2 : ℝ)..1, (∑ j, a j * rung c (n j) s) ^ 2 := by
  rw [integral_sq_sum (fun j => continuousOn_rung_cell (h j) (by norm_num) le_rfl (by norm_num)) a]
  simp only [dotProduct, mulVec, cellGram, of_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

omit [Fintype ι] [DecidableEq ι] in
/-- A rung is nonzero somewhere in `(1/2, 1)`. -/
theorem exists_rung_ne_zero {c : ℝ} {k : ℕ} (h : ∃ χ, IsLevelIdx c k χ) :
    ∃ t ∈ Set.Ioo (1 / 2 : ℝ) 1, rung c k t ≠ 0 := by
  have h1 := Cvs.Prolate.EvenRungsByIndex.rung_one_ne_zero h
  have hc := (Cvs.Prolate.EvenRungsByIndex.continuousOn_rung h) 1 ⟨by norm_num, le_rfl⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousWithinAt_iff.mp hc |rung c k 1| (abs_pos.mpr h1)
  set t := 1 - min (δ / 2) (1 / 4)
  have hm : 0 < min (δ / 2) (1 / 4) := lt_min (by linarith) (by norm_num)
  have hm' : min (δ / 2) (1 / 4) ≤ 1 / 4 := min_le_right _ _
  have hmδ : min (δ / 2) (1 / 4) < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  refine ⟨t, ⟨by linarith, by linarith⟩, fun h0 => ?_⟩
  have := hball (x := t) ⟨by linarith, by linarith⟩ (by
    rw [Real.dist_eq, show t - 1 = -min (δ / 2) (1 / 4) by ring, abs_neg, abs_of_pos hm]; exact hmδ)
  rw [Real.dist_eq, h0, zero_sub, abs_neg] at this
  exact lt_irrefl _ this

omit [Fintype ι] [DecidableEq ι] in
/-- Distinct level indices have distinct levels. -/
theorem lev_ne {c : ℝ} {k j : ℕ} (hk : ∃ χ, IsLevelIdx c k χ) (hj : ∃ χ, IsLevelIdx c j χ) (hkj : k ≠ j) :
    lev c k ≠ lev c j := by
  rcases lt_or_gt_of_ne hkj with h | h
  · exact (Cvs.Prolate.EvenRungsByIndex.lev_lt hj h).ne
  · exact (Cvs.Prolate.EvenRungsByIndex.lev_lt hk h).ne'

/-- **wf-schur Lemma 0, positivity**: the cell Gram of rungs with distinct indices is positive definite. -/
theorem cellGram_posDef {c : ℝ} {n : ι → ℕ} (hn : Function.Injective n) (h : ∀ a, ∃ χ, IsLevelIdx c (n a) χ) :
    (cellGram c n).PosDef := by
  have hH : (cellGram c n).IsHermitian := by
    ext a b
    simp only [conjTranspose_apply, star_trivial, cellGram, of_apply]
    exact congrArg (2 * ·) (intervalIntegral.integral_congr fun s _ => by ring)
  refine .of_dotProduct_mulVec_pos hH fun a ha => ?_
  rw [star_trivial, quad_cellGram h]
  set g : ℝ → ℝ := fun s => ∑ j, a j * rung c (n j) s
  have hgc : ContinuousOn g (Set.uIcc (1 / 2 : ℝ) 1) :=
    continuousOn_finsetSum _ fun j _ =>
      continuousOn_const.mul (continuousOn_rung_cell (h j) (by norm_num) le_rfl (by norm_num))
  have hint : IntervalIntegrable (fun s => g s ^ 2) MeasureTheory.volume (1 / 2 : ℝ) 1 := (hgc.pow 2).intervalIntegrable
  have hnn : 0 ≤ ∫ s in (1 / 2 : ℝ)..1, g s ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) fun s _ => sq_nonneg _
  rcases hnn.lt_or_eq with hlt | heq
  · linarith
  exfalso
  have hae := (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae (by norm_num)
    (Filter.Eventually.of_forall fun s => sq_nonneg (g s)) hint).mp heq.symm
  have hae' : (fun s => g s ^ 2) =ᵐ[MeasureTheory.volume.restrict (Set.Ioo (1 / 2 : ℝ) 1)] 0 :=
    MeasureTheory.ae_restrict_of_ae_restrict_of_subset Set.Ioo_subset_Ioc_self hae
  have hIoo : Set.Ioo (1 / 2 : ℝ) 1 ⊆ Set.uIcc (1 / 2 : ℝ) 1 := by
    rw [Set.uIcc_of_le (by norm_num)]; exact Set.Ioo_subset_Icc_self
  have heqOn := MeasureTheory.Measure.eqOn_open_of_ae_eq hae' isOpen_Ioo ((hgc.pow 2).mono hIoo)
    continuousOn_const
  have hz : ∀ t ∈ Set.Ioo (1 / 2 : ℝ) 1, ∑ j ∈ Finset.univ, a j * rung c (n j) t = 0 := fun t ht =>
    pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (heqOn ht)
  have hsub : Set.Ioo (1 / 2 : ℝ) 1 ⊆ Set.uIcc (-1 : ℝ) 1 := by
    rw [Set.uIcc_of_le (by norm_num)]; exact fun t ht => ⟨by linarith [ht.1], ht.2.le⟩
  have hall := mul_eq_zero_of_sum_eq_zero (c := c) (h := fun j => rung c (n j))
    (h₁ := fun j => rung₁ c (n j)) (h₂ := fun j => Cvs.Prolate.EvenRungsByIndex.rung₂ c (n j))
    (χ := fun j => lev c (n j)) isOpen_Ioo
    (fun j t ht => (rung_spec (h j)).1 t (hsub ht)) (fun j t ht => (rung_spec (h j)).2.1 t (hsub ht))
    (fun j t ht => (rung_spec (h j)).2.2.2.1 t (hsub ht)) Finset.univ
    (fun i _ j _ hij => by_contra fun hne => lev_ne (h i) (h j) (hn.ne hne) hij) a hz
  apply ha
  ext j
  obtain ⟨t, ht, hne⟩ := exists_rung_ne_zero (h j)
  exact (mul_eq_zero.mp (hall j (Finset.mem_univ j) t ht)).resolve_right hne

omit [DecidableEq ι] in
/-- **wf-schur Lemma 0, `C ≤ 1`**: for distinct indices, `aᵀCa ≤ |a|²`. -/
theorem quad_cellGram_le {c : ℝ} {n : ι → ℕ} (hn : Function.Injective n) (h : ∀ a, ∃ χ, IsLevelIdx c (n a) χ)
    (a : ι → ℝ) : a ⬝ᵥ (cellGram c n *ᵥ a) ≤ a ⬝ᵥ a := by
  classical
  rw [quad_cellGram h]
  set g : ℝ → ℝ := fun s => ∑ j, a j * rung c (n j) s
  have hgc : ContinuousOn g (Set.Icc (-1 : ℝ) 1) :=
    continuousOn_finsetSum _ fun j _ =>
      continuousOn_const.mul (Cvs.Prolate.EvenRungsByIndex.continuousOn_rung (h j))
  have hint : ∀ α β : ℝ, -1 ≤ α → β ≤ 1 → α ≤ β →
      IntervalIntegrable (fun s => g s ^ 2) MeasureTheory.volume α β := fun α β hα hβ hαβ =>
    ((hgc.pow 2).mono (by rw [Set.uIcc_of_le hαβ]; exact Set.Icc_subset_Icc hα hβ)).intervalIntegrable
  have hsplit : ∫ s in (0 : ℝ)..1, g s ^ 2 =
      (∫ s in (0 : ℝ)..(1 / 2), g s ^ 2) + ∫ s in (1 / 2 : ℝ)..1, g s ^ 2 :=
    (intervalIntegral.integral_add_adjacent_intervals (hint 0 (1 / 2) (by norm_num) (by norm_num) (by norm_num))
      (hint (1 / 2) 1 (by norm_num) le_rfl (by norm_num))).symm
  have hleft : 0 ≤ ∫ s in (0 : ℝ)..(1 / 2), g s ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) fun s _ => sq_nonneg _
  have heven : ∫ s in (-1 : ℝ)..1, g s ^ 2 = 2 * ∫ s in (0 : ℝ)..1, g s ^ 2 :=
    Cvs.Prolate.SlepianEvenOrdering.integral_even_fold (hgc.pow 2) fun s hs => by
      simp only [g]
      congr 1
      exact Finset.sum_congr rfl fun j _ => by
        rw [(rung_spec (h j)).2.2.2.2.1 s ⟨by linarith [hs.1], hs.2⟩]
  have hfull : ∫ s in (-1 : ℝ)..1, g s ^ 2 = a ⬝ᵥ a := by
    rw [integral_sq_sum (fun j => continuousOn_rung_cell (h j) le_rfl le_rfl (by norm_num)) a, dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i]
    · have := (rung_spec (h i)).2.2.2.2.2
      rw [show (∫ s in (-1 : ℝ)..1, rung c (n i) s * rung c (n i) s) = ∫ s in (-1 : ℝ)..1, rung c (n i) s ^ 2 from
        intervalIntegral.integral_congr fun s _ => by ring, this, mul_one]
    · intro j _ hji
      have := Cvs.Prolate.EvenRungParseval.integral_rung_mul_rung (c := c) (k := ⟨n i, h i⟩) (j := ⟨n j, h j⟩)
        (fun he => hji (hn (congrArg Subtype.val he).symm))
      rw [this, mul_zero]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  linarith

/-- The rung index map `j ↦ 2j` of the even rungs `h_{4j}`, `j < x`. -/
def rungIdx (x : ℕ) (j : Fin x) : ℕ := 2 * (j : ℕ)

/-- The cell Gram of the rungs `h_{4j}`, `j < x`, at `c = 2πx`. -/
def rungCellGram (x : ℕ) : Matrix (Fin x) (Fin x) ℝ := cellGram (2 * Real.pi * x) (rungIdx x)

/-- Every rung index `2j`, `j < x`, has a level once `2πx ≥ 80`. -/
theorem rungIdx_level {x : ℕ} (hx : 80 ≤ 2 * Real.pi * x) (j : Fin x) :
    ∃ χ, IsLevelIdx (2 * Real.pi * x) (rungIdx x j) χ :=
  Cvs.Prolate.RungFamilyRangePartners.exists_main hx ⟨j, Finset.mem_range.mpr j.2⟩

/-- **wf-schur Lemma 0 on the window rungs**: `rungCellGram x` is positive definite once `2πx ≥ 80`. -/
theorem rungCellGram_posDef {x : ℕ} (hx : 80 ≤ 2 * Real.pi * x) : (rungCellGram x).PosDef :=
  cellGram_posDef (fun i j h => Fin.ext (by simpa [rungIdx] using h)) (rungIdx_level hx)

/-- **wf-schur Lemma 0 on the window rungs**: `aᵀCa ≤ |a|²` for `C = rungCellGram x`. -/
theorem quad_rungCellGram_le {x : ℕ} (hx : 80 ≤ 2 * Real.pi * x) (a : Fin x → ℝ) :
    a ⬝ᵥ (rungCellGram x *ᵥ a) ≤ a ⬝ᵥ a :=
  quad_cellGram_le (fun i j h => Fin.ext (by simpa [rungIdx] using h)) (rungIdx_level hx) a

end Cvs.Prolate.Gram.RungCellGramDisplacement
