import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.Gram.CentralSquareInverseForm
import Cvs.Prolate.Gram.FullTwistOuterCell
import Cvs.Prolate.Gram.ProlateCellGramHalfUnit
import Cvs.Prolate.SlepianCommutingRelation

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The inverse form is convex in the rung vector, so it splits over a cut

For continuous `z`, `v ↦ invForm x v z` is convex: its `v`-part is a positive quadratic plus a linear term.
Jensen and Cauchy–Schwarz then bound it on a sum of single rungs by `(Σ_j |a_j|√g_j)²` from per-rung bounds
`invForm x (α e_j) z ≤ α² g_j`, and the inverse bound on `{j ≥ k}` follows from a bound `θ` on the part above a
cut `k₁` and per-rung bounds below it whenever `θ + Σ_{j<k₁} W_j g_j ≤ 1`.
-/

noncomputable section

open Real Filter Finset Set MeasureTheory
open Cvs.ZeroCounting
open Cvs.Prolate.Gram.ProlateCellGramHalfUnit (lam levT)
open Cvs.Prolate.Gram.FullTwistOuterCell (rungSum)
open Cvs.L2a.AngularProlateTailPositive (psi)
open Cvs.Prolate.Gram.CentralSquareInverseForm (cut centralT invForm InverseBound)

namespace Cvs.Prolate.Gram.InverseFormConvexSplit
open Cvs.ZeroCounting

/-! ### Continuity and linearity of the pieces -/

/-- The cosine transform of an interval-integrable profile is continuous. -/
theorem continuous_psi_of_intervalIntegrable {c : ℝ} {g : ℝ → ℝ} (hg : IntervalIntegrable g volume (-1) 1) :
    Continuous (psi c g) := by
  unfold psi Cvs.Prolate.SlepianCommutingRelation.kint
  refine intervalIntegral.continuous_of_dominated_interval (bound := fun s => |g s|) (fun ξ => ?_)
    (fun ξ => Filter.Eventually.of_forall fun s _ => ?_) hg.abs (Filter.Eventually.of_forall fun s _ => ?_)
  · exact (hg.mul_continuousOn (by fun_prop : Continuous fun s => Real.cos (c * ξ * s)).continuousOn).def'.1
  · rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
  · fun_prop

/-- A rung combination is continuous on `[−1, 1]`. -/
theorem continuousOn_rungSum (x : ℕ) (v : Fin x → ℝ) : ContinuousOn (rungSum x v) (Icc (-1) 1) := by
  have h := continuousOn_finsetSum (univ : Finset (Fin x))
    fun n _ => (continuousOn_const (c := v n)).mul (Cvs.Prolate.Gram.ProlateCellGramHalfUnit.continuousOn_rung (2 * π * x) (2 * (n : ℕ)))
  exact h.congr fun u _ => by simp [rungSum]

/-- A function continuous on `[−1, 1]` is continuous on `[−½, ½]`. -/
theorem continuousOn_half {f : ℝ → ℝ} (hf : ContinuousOn f (Icc (-1) 1)) :
    ContinuousOn f (uIcc (-(1 / 2 : ℝ)) (1 / 2)) :=
  hf.mono fun u hu => by
    rw [Set.uIcc_of_le (by norm_num)] at hu
    exact ⟨by linarith [hu.1], by linarith [hu.2]⟩

/-- The central cut of a function interval-integrable on `[−1, 1]` is interval-integrable there. -/
theorem intervalIntegrable_cut {f : ℝ → ℝ} (hf : IntervalIntegrable f volume (-1) 1) :
    IntervalIntegrable (cut f) volume (-1) 1 := by
  exact ⟨hf.1.indicator measurableSet_Icc, hf.2.indicator measurableSet_Icc⟩

/-- The profile `f_v + 1_{[−½, ½]} f_v` of the cross term. -/
def prof (x : ℕ) (v : Fin x → ℝ) (s : ℝ) : ℝ := rungSum x v s + cut (rungSum x v) s

/-- The profile is interval-integrable on `[−1, 1]`. -/
theorem intervalIntegrable_prof (x : ℕ) (v : Fin x → ℝ) : IntervalIntegrable (prof x v) volume (-1) 1 := by
  have h := (continuousOn_rungSum x v).intervalIntegrable_of_Icc (μ := volume) (by norm_num : (-1 : ℝ) ≤ 1)
  exact h.add (intervalIntegrable_cut h)

/-- The cross-term vector `b_v = √x·ψ_c(f_v + 1_{[−½, ½]} f_v)`. -/
def bv (x : ℕ) (v : Fin x → ℝ) (t : ℝ) : ℝ := √x * psi (2 * π * x) (prof x v) t

/-- `b_v` is continuous. -/
theorem continuous_bv (x : ℕ) (v : Fin x → ℝ) : Continuous (bv x v) :=
  continuous_const.mul (continuous_psi_of_intervalIntegrable (intervalIntegrable_prof x v))

/-- The rung combination is linear. -/
theorem rungSum_comb (x : ℕ) (a b : Fin x → ℝ) (t s u : ℝ) :
    rungSum x (t • a + s • b) u = t * rungSum x a u + s * rungSum x b u := by
  simp only [rungSum, Finset.mul_sum, ← Finset.sum_add_distrib, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun n _ => by ring

/-- The profile is linear. -/
theorem prof_comb (x : ℕ) (a b : Fin x → ℝ) (t s u : ℝ) :
    prof x (t • a + s • b) u = t * prof x a u + s * prof x b u := by
  simp only [prof, cut, Set.indicator_apply, rungSum_comb]
  split_ifs <;> ring

/-- The cosine transform is linear on interval-integrable profiles. -/
theorem psi_comb {c : ℝ} {g h : ℝ → ℝ} (hg : IntervalIntegrable g volume (-1) 1)
    (hh : IntervalIntegrable h volume (-1) 1) (t s ξ : ℝ) :
    psi c (fun u => t * g u + s * h u) ξ = t * psi c g ξ + s * psi c h ξ := by
  unfold psi Cvs.Prolate.SlepianCommutingRelation.kint
  have hc : Continuous fun u : ℝ => Real.cos (c * ξ * u) := by fun_prop
  have e : (fun u => (t * g u + s * h u) * Real.cos (c * ξ * u))
      = fun u => t * (g u * Real.cos (c * ξ * u)) + s * (h u * Real.cos (c * ξ * u)) := by
    funext u; ring
  simp only [e]
  rw [intervalIntegral.integral_add ((hg.mul_continuousOn hc.continuousOn).const_mul t)
    ((hh.mul_continuousOn hc.continuousOn).const_mul s), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]

/-- `b_v` is linear. -/
theorem bv_comb (x : ℕ) (a b : Fin x → ℝ) (t s ξ : ℝ) :
    bv x (t • a + s • b) ξ = t * bv x a ξ + s * bv x b ξ := by
  have e : prof x (t • a + s • b) = fun u => t * prof x a u + s * prof x b u := funext (prof_comb x a b t s)
  rw [bv, e, psi_comb (intervalIntegrable_prof x a) (intervalIntegrable_prof x b), bv, bv]
  ring

/-- `invForm` in terms of `b_v`. -/
theorem invForm_eq (x : ℕ) (v : Fin x → ℝ) (z : ℝ → ℝ) :
    invForm x v z = (v ⬝ᵥ v + (∫ t in (-(1 / 2 : ℝ))..(1 / 2), rungSum x v t ^ 2)
      + 2 * (∫ t in (-(1 / 2 : ℝ))..(1 / 2), bv x v t * z t)
      - (∫ t in (-(1 / 2 : ℝ))..(1 / 2), z t ^ 2) + ∫ t in (-(1 / 2 : ℝ))..(1 / 2), centralT x z t ^ 2) / 2 := rfl

/-! ### Convexity -/

/-- `(tA + sB)² ≤ tA² + sB²` for `t, s ≥ 0`, `t + s = 1`. -/
theorem sq_comb_le {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) (hts : t + s = 1) (A B : ℝ) :
    (t * A + s * B) ^ 2 ≤ t * A ^ 2 + s * B ^ 2 := by
  have e : t * A ^ 2 + s * B ^ 2 - (t * A + s * B) ^ 2 = t * s * (A - B) ^ 2 := by
    obtain rfl : s = 1 - t := by linarith
    ring
  nlinarith [mul_nonneg (mul_nonneg ht hs) (sq_nonneg (A - B))]

/-- **The inverse form is convex in the rung vector** for continuous `z`. -/
theorem convexOn_invForm (x : ℕ) {z : ℝ → ℝ} (hz : Continuous z) :
    ConvexOn ℝ univ fun v : Fin x → ℝ => invForm x v z := by
  refine ⟨convex_univ, fun a _ b _ t s ht hs hts => ?_⟩
  simp only [smul_eq_mul]
  have hI : ∀ v : Fin x → ℝ, IntervalIntegrable (fun u => rungSum x v u ^ 2) volume (-(1 / 2)) (1 / 2) :=
    fun v => ((continuousOn_half (continuousOn_rungSum x v)).pow 2).intervalIntegrable
  have hB : ∀ v : Fin x → ℝ, IntervalIntegrable (fun u => bv x v u * z u) volume (-(1 / 2)) (1 / 2) :=
    fun v => ((continuous_bv x v).mul hz).intervalIntegrable _ _
  have h1 : (t • a + s • b) ⬝ᵥ (t • a + s • b) ≤ t * (a ⬝ᵥ a) + s * (b ⬝ᵥ b) := by
    simp only [dotProduct, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    have := sq_comb_le ht hs hts (a i) (b i)
    nlinarith
  have h2 : (∫ u in (-(1 / 2 : ℝ))..(1 / 2), rungSum x (t • a + s • b) u ^ 2)
      ≤ t * (∫ u in (-(1 / 2 : ℝ))..(1 / 2), rungSum x a u ^ 2)
        + s * ∫ u in (-(1 / 2 : ℝ))..(1 / 2), rungSum x b u ^ 2 := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add ((hI a).const_mul t) ((hI b).const_mul s)]
    refine intervalIntegral.integral_mono_on (by norm_num) (hI _) (((hI a).const_mul t).add ((hI b).const_mul s))
      fun u _ => ?_
    rw [rungSum_comb]
    exact sq_comb_le ht hs hts _ _
  have h3 : (∫ u in (-(1 / 2 : ℝ))..(1 / 2), bv x (t • a + s • b) u * z u)
      = t * (∫ u in (-(1 / 2 : ℝ))..(1 / 2), bv x a u * z u)
        + s * ∫ u in (-(1 / 2 : ℝ))..(1 / 2), bv x b u * z u := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add ((hB a).const_mul t) ((hB b).const_mul s)]
    refine intervalIntegral.integral_congr fun u _ => ?_
    simp only [bv_comb]
    ring
  rw [invForm_eq, invForm_eq, invForm_eq, h3]
  obtain rfl : s = 1 - t := by linarith
  nlinarith [h1, h2]

/-! ### Jensen over single rungs -/

/-- **The inverse form on a sum of single rungs**: from `invForm x (α e_j) z ≤ α² g_j` with `g_j > 0` on `S` and
`invForm x 0 z ≤ 0`, `invForm x (Σ_{j∈S} a_j e_j) z ≤ (Σ_{j∈S} |a_j|√g_j)²`. -/
theorem invForm_sum_single_le {x : ℕ} {z : ℝ → ℝ} (hz : Continuous z) (S : Finset (Fin x)) (a g : Fin x → ℝ)
    (hg : ∀ j ∈ S, 0 < g j) (hR : ∀ j ∈ S, ∀ α : ℝ, invForm x (Pi.single j α) z ≤ α ^ 2 * g j)
    (h0 : invForm x 0 z ≤ 0) :
    invForm x (∑ j ∈ S, Pi.single j (a j)) z ≤ (∑ j ∈ S, |a j| * √(g j)) ^ 2 := by
  set S0 := ∑ j ∈ S, |a j| * √(g j) with hS0
  have hterm : ∀ j ∈ S, 0 ≤ |a j| * √(g j) := fun j _ => mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
  rcases (Finset.sum_nonneg hterm).eq_or_lt with h | hpos
  · have ha : ∀ j ∈ S, a j = 0 := fun j hj => by
      have h' := (Finset.sum_eq_zero_iff_of_nonneg hterm).1 h.symm j hj
      rcases mul_eq_zero.1 h' with h'' | h''
      · exact abs_eq_zero.1 h''
      · exact absurd h'' (Real.sqrt_pos.2 (hg j hj)).ne'
    have hsum : ∑ j ∈ S, Pi.single j (a j) = (0 : Fin x → ℝ) :=
      Finset.sum_eq_zero fun j hj => by rw [ha j hj, Pi.single_zero]
    have hz0 : S0 = 0 := by rw [hS0, ← h]
    rw [hsum, hz0]
    simpa using h0
  set w : Fin x → ℝ := fun j => |a j| * √(g j) / S0
  have hw0 : ∀ j ∈ S, 0 ≤ w j := fun j hj => div_nonneg (hterm j hj) hpos.le
  have hw1 : ∑ j ∈ S, w j = 1 := by
    simp only [w, ← Finset.sum_div]
    exact div_self hpos.ne'
  set p : Fin x → Fin x → ℝ := fun j => Pi.single j (a j / w j)
  have hp : ∀ j ∈ S, w j • p j = Pi.single j (a j) := fun j hj => by
    by_cases ha : a j = 0
    · simp [p, ha]
    · have hwj : w j ≠ 0 := by
        have : 0 < |a j| * √(g j) := mul_pos (abs_pos.2 ha) (Real.sqrt_pos.2 (hg j hj))
        exact (div_pos this hpos).ne'
      simp only [p]
      rw [← Pi.single_smul, smul_eq_mul, mul_div_cancel₀ _ hwj]
  have hJ := (convexOn_invForm x hz).map_sum_le hw0 hw1 (fun j _ => Set.mem_univ (p j))
  rw [Finset.sum_congr rfl hp] at hJ
  refine hJ.trans ?_
  have hbound : ∀ j ∈ S, w j • invForm x (p j) z ≤ |a j| * √(g j) * S0 := fun j hj => by
    rw [smul_eq_mul]
    by_cases ha : a j = 0
    · have : w j = 0 := by simp [w, ha]
      rw [this, ha]
      simp
    · have hgj := hg j hj
      have hsg : 0 < √(g j) := Real.sqrt_pos.2 hgj
      have hwj : 0 < w j := div_pos (mul_pos (abs_pos.2 ha) hsg) hpos
      calc w j * invForm x (p j) z ≤ w j * ((a j / w j) ^ 2 * g j) :=
            mul_le_mul_of_nonneg_left (hR j hj _) hwj.le
        _ = a j ^ 2 * g j / w j := by field_simp
        _ = |a j| * √(g j) * S0 := by
            simp only [w]
            have hsq : √(g j) ^ 2 = g j := Real.sq_sqrt hgj.le
            rw [div_div_eq_mul_div, ← sq_abs (a j)]
            field_simp
            rw [hsq]
            ring
  calc ∑ j ∈ S, w j • invForm x (p j) z ≤ ∑ j ∈ S, |a j| * √(g j) * S0 := Finset.sum_le_sum hbound
    _ = S0 ^ 2 := by rw [← Finset.sum_mul, sq]

/-- **Cauchy–Schwarz for weighted rungs**: `(Σ |W_j y_j|√g_j)² ≤ (Σ W_j g_j)(Σ W_j y_j²)` for `W, g ≥ 0`. -/
theorem sum_abs_mul_sqrt_sq_le {ι : Type*} (S : Finset ι) (W y g : ι → ℝ) (hW : ∀ j ∈ S, 0 ≤ W j)
    (hg : ∀ j ∈ S, 0 ≤ g j) :
    (∑ j ∈ S, |W j * y j| * √(g j)) ^ 2 ≤ (∑ j ∈ S, W j * g j) * ∑ j ∈ S, W j * y j ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq S (fun j => √(W j * g j)) fun j => √(W j) * |y j|
  have e1 : ∀ j ∈ S, √(W j * g j) * (√(W j) * |y j|) = |W j * y j| * √(g j) := fun j hj => by
    rw [Real.sqrt_mul (hW j hj), abs_mul, abs_of_nonneg (hW j hj)]
    have := Real.mul_self_sqrt (hW j hj)
    calc √(W j) * √(g j) * (√(W j) * |y j|) = (√(W j) * √(W j)) * |y j| * √(g j) := by ring
      _ = W j * |y j| * √(g j) := by rw [this]
  have e2 : ∀ j ∈ S, √(W j * g j) ^ 2 = W j * g j := fun j hj => Real.sq_sqrt (mul_nonneg (hW j hj) (hg j hj))
  have e3 : ∀ j ∈ S, (√(W j) * |y j|) ^ 2 = W j * y j ^ 2 := fun j hj => by
    rw [mul_pow, Real.sq_sqrt (hW j hj), sq_abs]
  rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, Finset.sum_congr rfl e3] at h
  exact h

/-! ### The split at a cut -/

/-- **The bound above a cut** `k₁`: `invForm x (W·y on {j ≥ k₁}) z ≤ θ Σ_{j ≥ k₁} W_j y_j²` for all `y` and
continuous `z`, with the weights `W` of the layer `{j ≥ k}`. -/
def UpperInverseBound (x : ℕ) (k k₁ : Fin x) (ε θ : ℝ) : Prop :=
  ∀ (y : Fin x → ℝ) (z : ℝ → ℝ), Continuous z →
    invForm x (fun j => if k₁ ≤ j then Cvs.Prolate.Gram.CentralSquareInverseForm.weight x k ε j * y j else 0) z
      ≤ θ * ∑ j ∈ univ.filter (k₁ ≤ ·), Cvs.Prolate.Gram.CentralSquareInverseForm.weight x k ε j * y j ^ 2

/-- **A per-rung inverse bound** `invForm x (α e_j) z ≤ α² g` for every `α` and continuous `z`. -/
def RungInverseBound (x : ℕ) (j : Fin x) (g : ℝ) : Prop :=
  ∀ (α : ℝ) (z : ℝ → ℝ), Continuous z → invForm x (Pi.single j α) z ≤ α ^ 2 * g

/-- The weights are nonnegative for `ε ≤ 1` at `80 ≤ 2πx`. -/
theorem weight_nonneg {x : ℕ} (hx : 80 ≤ 2 * π * x) (k : Fin x) {ε : ℝ} (hε : ε ≤ 1) (j : Fin x) :
    0 ≤ Cvs.Prolate.Gram.CentralSquareInverseForm.weight x k ε j := by
  have := Cvs.Prolate.Gram.ProlateCellGramHalfUnit.lam_le_one hx j.2
  unfold Cvs.Prolate.Gram.CentralSquareInverseForm.weight
  split_ifs <;> linarith

/-- The weighted vector splits at `k₁` into its part above and a sum of single rungs below. -/
theorem weight_vec_split (x : ℕ) (k k₁ : Fin x) (ε : ℝ) (y : Fin x → ℝ) :
    (fun j => Cvs.Prolate.Gram.CentralSquareInverseForm.weight x k ε j * y j)
      = (fun j => if k₁ ≤ j then Cvs.Prolate.Gram.CentralSquareInverseForm.weight x k ε j * y j else 0)
        + ∑ j ∈ univ.filter (· < k₁), Pi.single j (Cvs.Prolate.Gram.CentralSquareInverseForm.weight x k ε j * y j) := by
  funext i
  simp only [Pi.add_apply, Finset.sum_apply, Pi.single_apply]
  rw [Finset.sum_ite_eq (univ.filter (· < k₁)) i]
  by_cases h : k₁ ≤ i
  · have : ¬ i < k₁ := not_lt.2 h
    simp [h, this]
  · have : i < k₁ := not_le.1 h
    simp [h, this]

/-- **The inverse bound from a bound above a cut and per-rung bounds below it**: at `80 ≤ 2πx` with `ε ≤ 1`,
`UpperInverseBound x k k₁ ε θ`, `RungInverseBound x j (g j)` with `g j > 0` for `j < k₁`, `invForm x 0 z ≤ 0`, and
`θ + τ ≤ 1` for some `τ > 0` above `Σ_{j<k₁} W_j g_j`, give `InverseBound x k ε`. -/
theorem inverseBound_of_split {x : ℕ} (hx : 80 ≤ 2 * π * x) {k k₁ : Fin x} {ε θ τ : ℝ} (hε : ε ≤ 1)
    (hθ : 0 < θ) (hτ : 0 < τ) (hθτ : θ + τ ≤ 1) (hU : UpperInverseBound x k k₁ ε θ) (g : Fin x → ℝ)
    (hg : ∀ j < k₁, 0 < g j) (hR : ∀ j < k₁, RungInverseBound x j (g j))
    (h0 : ∀ z : ℝ → ℝ, Continuous z → invForm x 0 z ≤ 0)
    (hsum : ∑ j ∈ univ.filter (· < k₁), Cvs.Prolate.Gram.CentralSquareInverseForm.weight x k ε j * g j ≤ τ) : InverseBound x k ε := by
  intro y z hz
  set W := Cvs.Prolate.Gram.CentralSquareInverseForm.weight x k ε
  have hW := weight_nonneg hx k hε
  set t := θ / (θ + τ) with ht_def
  have hθτ0 : 0 < θ + τ := by linarith
  have ht0 : 0 < t := div_pos hθ hθτ0
  have ht1 : 1 - t = τ / (θ + τ) := by rw [ht_def]; field_simp; ring
  have hs0 : 0 < 1 - t := by rw [ht1]; exact div_pos hτ hθτ0
  set SA := ∑ j ∈ univ.filter (k₁ ≤ ·), W j * y j ^ 2
  set SB := ∑ j ∈ univ.filter (· < k₁), W j * y j ^ 2
  have hSA : 0 ≤ SA := Finset.sum_nonneg fun j _ => mul_nonneg (hW j) (sq_nonneg _)
  have hSB : 0 ≤ SB := Finset.sum_nonneg fun j _ => mul_nonneg (hW j) (sq_nonneg _)
  set u : Fin x → ℝ := fun j => if k₁ ≤ j then W j * y j else 0
  set w : Fin x → ℝ := ∑ j ∈ univ.filter (· < k₁), Pi.single j (W j * y j)
  have hsplit : (fun j => W j * y j) = t • (t⁻¹ • u) + (1 - t) • ((1 - t)⁻¹ • w) := by
    rw [smul_smul, smul_smul, mul_inv_cancel₀ ht0.ne', mul_inv_cancel₀ hs0.ne', one_smul, one_smul]
    exact weight_vec_split x k k₁ ε y
  have hconv := (convexOn_invForm x hz).2 (Set.mem_univ (t⁻¹ • u)) (Set.mem_univ ((1 - t)⁻¹ • w)) ht0.le
    hs0.le (by ring)
  rw [← hsplit] at hconv
  -- the part above the cut
  have hAu : t⁻¹ • u = fun j => if k₁ ≤ j then W j * (t⁻¹ * y j) else 0 := by
    funext j; simp only [u, Pi.smul_apply, smul_eq_mul]; split_ifs <;> ring
  have hA : invForm x (t⁻¹ • u) z ≤ θ * (SA / t ^ 2) := by
    rw [hAu]
    refine (hU (fun j => t⁻¹ * y j) z hz).trans_eq ?_
    congr 1
    show _ = (∑ j ∈ univ.filter (k₁ ≤ ·), W j * y j ^ 2) / t ^ 2
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    field_simp
    exact mul_comm _ _
  -- the part below the cut
  have hBw : (1 - t)⁻¹ • w = ∑ j ∈ univ.filter (· < k₁), Pi.single j (W j * ((1 - t)⁻¹ * y j)) := by
    simp only [w, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Pi.single_smul, smul_eq_mul]
    ring_nf
  have hB : invForm x ((1 - t)⁻¹ • w) z ≤ τ * (SB / (1 - t) ^ 2) := by
    rw [hBw]
    have hj := invForm_sum_single_le hz (univ.filter (· < k₁)) (fun j => W j * ((1 - t)⁻¹ * y j)) g
      (fun j hj => hg j (Finset.mem_filter.1 hj).2) (fun j hj α => hR j (Finset.mem_filter.1 hj).2 α z hz)
      (h0 z hz)
    refine hj.trans ?_
    have hcs := sum_abs_mul_sqrt_sq_le (univ.filter (· < k₁)) W (fun j => (1 - t)⁻¹ * y j) g
      (fun j _ => hW j) (fun j hj => (hg j (Finset.mem_filter.1 hj).2).le)
    refine hcs.trans ?_
    have e : ∑ j ∈ univ.filter (· < k₁), W j * ((1 - t)⁻¹ * y j) ^ 2 = SB / (1 - t) ^ 2 := by
      simp only [SB, Finset.sum_div]
      refine Finset.sum_congr rfl fun j _ => ?_
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_right hsum (div_nonneg hSB (sq_nonneg _))
  have htot : ∑ j, W j * y j ^ 2 = SA + SB := by
    rw [← Finset.sum_filter_add_sum_filter_not univ (k₁ ≤ ·)]
    congr 1
    refine Finset.sum_congr (by ext j; simp) fun _ _ => rfl
  rw [htot]
  have e1 : t * (θ * (SA / t ^ 2)) = (θ + τ) * SA := by
    rw [ht_def]; field_simp
  have e2 : (1 - t) * (τ * (SB / (1 - t) ^ 2)) = (θ + τ) * SB := by
    rw [ht1]; field_simp
  calc invForm x (fun j => W j * y j) z
      ≤ t • invForm x (t⁻¹ • u) z + (1 - t) • invForm x ((1 - t)⁻¹ • w) z := hconv
    _ ≤ t * (θ * (SA / t ^ 2)) + (1 - t) * (τ * (SB / (1 - t) ^ 2)) := by
        simp only [smul_eq_mul]
        exact add_le_add (mul_le_mul_of_nonneg_left hA ht0.le) (mul_le_mul_of_nonneg_left hB hs0.le)
    _ = (θ + τ) * (SA + SB) := by rw [e1, e2]; ring
    _ ≤ SA + SB := by nlinarith

end Cvs.Prolate.Gram.InverseFormConvexSplit

end
