import Mathlib
import Cvs.Prolate.EvenRungParseval
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.Gram.CentralResolventTrace
import Cvs.Prolate.Hardy.CosineSynthesisPlancherel
import Cvs.Prolate.Hardy.HighpassExtensionRung
import Cvs.Prolate.SincTopIsRung

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Even continuous data on `[−1, 1]` expands in the central rungs in `L²(I)`

For even continuous `y` the restrictions to `I = [−½, ½]` satisfy `Q y = Σ_k ⟨y, h_k⟩ Q h_k` in `L²(I)`, with
`‖Q Σ_{k∈s} a_k h_k‖² ≤ Σ_{k∈s} a_k²` by orthonormality of the rungs on `[−1, 1]` and Parseval over them.
-/

noncomputable section

open Real Set MeasureTheory Filter Topology intervalIntegral

namespace Cvs.Prolate.Hardy.CentralRungExpansion
open Cvs.ZeroCounting

open Cvs.Prolate.EvenRungsByIndex (rung IsLevelIdx rung_spec continuousOn_rung)
open Cvs.Prolate.SincTopIsRung (clampExt clampExt_of_mem continuous_clampExt clampExt_neg)
open Cvs.Prolate.Gram.CentralResolventTrace (L2I)

/-! ### Restriction to `I` -/

/-- The class in `L²(I)` of a continuous function. -/
def qI {y : ℝ → ℝ} (hy : Continuous y) : L2I := (Cvs.Prolate.Hardy.HighpassExtensionRung.memLp_restrict_of_continuous hy).toLp y

theorem coeFn_qI {y : ℝ → ℝ} (hy : Continuous y) : (qI hy : ℝ → ℝ) =ᵐ[volume.restrict Cvs.Prolate.Hardy.CosineSynthesisPlancherel.cI] y :=
  MemLp.coeFn_toLp _

theorem qI_sub {y z : ℝ → ℝ} (hy : Continuous y) (hz : Continuous z) :
    qI (hy.sub hz) = qI hy - qI hz :=
  MemLp.toLp_sub _ _

theorem qI_smul (r : ℝ) {y : ℝ → ℝ} (hy : Continuous y) :
    qI (y := fun t => r * y t) (continuous_const.mul hy) = r • qI hy :=
  MemLp.toLp_const_smul r _

theorem qI_sum {ι : Type*} (s : Finset ι) (a : ι → ℝ) {g : ι → ℝ → ℝ} (hg : ∀ k, Continuous (g k)) :
    qI (continuous_finsetSum s fun k _ => continuous_const.mul (hg k) : Continuous fun t => ∑ k ∈ s, a k * g k t) =
      ∑ k ∈ s, a k • qI (hg k) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact MemLp.toLp_zero _
  | insert k s hk ih =>
    rw [Finset.sum_insert hk, ← ih, ← qI_smul]
    simp only [Finset.sum_insert hk]
    exact MemLp.toLp_add _ _

/-- `‖Q y‖² = ∫_I y²`. -/
theorem norm_qI_sq {y : ℝ → ℝ} (hy : Continuous y) : ‖qI hy‖ ^ 2 = ∫ t in Cvs.Prolate.Hardy.CosineSynthesisPlancherel.cI, y t ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae ((coeFn_qI hy).mono fun t ht => ?_)
  simp only [ht, RCLike.inner_apply, conj_trivial, sq]

/-- `‖Q y‖² ≤ ∫_{−1}^{1} y²`. -/
theorem norm_qI_sq_le {y : ℝ → ℝ} (hy : Continuous y) : ‖qI hy‖ ^ 2 ≤ ∫ t in (-1 : ℝ)..1, y t ^ 2 := by
  rw [norm_qI_sq, intervalIntegral.integral_of_le (by norm_num), ← integral_Icc_eq_integral_Ioc]
  refine setIntegral_mono_set ((hy.pow 2).continuousOn.integrableOn_compact isCompact_Icc)
    (Filter.Eventually.of_forall fun t => sq_nonneg _) (Filter.Eventually.of_forall ?_)
  exact Icc_subset_Icc (by norm_num) (by norm_num)

/-! ### The rungs as global continuous functions -/

open Classical in
/-- The rung `h_k`, clamped to a continuous function on `ℝ` (zero at missing levels). -/
def hk (c : ℝ) (k : ℕ) : ℝ → ℝ := if ∃ χ, IsLevelIdx c k χ then clampExt (rung c k) else 0

theorem continuous_hk (c : ℝ) (k : ℕ) : Continuous (hk c k) := by
  unfold hk; split_ifs with h
  · exact continuous_clampExt (continuousOn_rung h)
  · exact continuous_const

theorem hk_eq {c : ℝ} {k : ℕ} (h : ∃ χ, IsLevelIdx c k χ) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    hk c k t = rung c k t := by
  unfold hk; rw [if_pos h, clampExt_of_mem ht]

/-- **Orthonormality on `[−1, 1]`**: `∫ h_k h_j = δ_kj` at existing levels. -/
theorem integral_hk_mul_hk {c : ℝ} {k j : ℕ} (hk' : ∃ χ, IsLevelIdx c k χ) (hj : ∃ χ, IsLevelIdx c j χ) :
    ∫ t in (-1 : ℝ)..1, hk c k t * hk c j t = if k = j then 1 else 0 := by
  have e : ∫ t in (-1 : ℝ)..1, hk c k t * hk c j t = ∫ t in (-1 : ℝ)..1, rung c k t * rung c j t := by
    refine integral_congr fun t ht => ?_
    rw [uIcc_of_le (by norm_num)] at ht
    simp only [hk_eq hk' ht, hk_eq hj ht]
  rw [e]
  split_ifs with hkj
  · subst hkj
    have h1 := (rung_spec hk').2.2.2.2.2
    rw [show (fun t => rung c k t * rung c k t) = fun t => rung c k t ^ 2 by ext t; ring]
    exact h1
  · exact Cvs.Prolate.EvenRungParseval.integral_rung_mul_rung (k := ⟨k, hk'⟩) (j := ⟨j, hj⟩) fun h => hkj (congrArg Subtype.val h)

open Classical in
/-- The rung coefficient `⟨y, h_k⟩_{[−1, 1]}` (zero at missing levels). -/
def coef (c : ℝ) (y : ℝ → ℝ) (k : ℕ) : ℝ :=
  if ∃ χ, IsLevelIdx c k χ then ∫ t in (-1 : ℝ)..1, y t * hk c k t else 0

theorem hk_of_not {c : ℝ} {k : ℕ} (h : ¬ ∃ χ, IsLevelIdx c k χ) : hk c k = 0 := by
  unfold hk; rw [if_neg h]

/-- **Parseval** over the rungs for even continuous `y`, indexed by `ℕ`. -/
theorem hasSum_coef_sq {c : ℝ} (hc : c ≠ 0) {y : ℝ → ℝ} (hy : Continuous y)
    (he : ∀ t ∈ Icc (-1 : ℝ) 1, y (-t) = y t) :
    HasSum (fun k => coef c y k ^ 2) (∫ t in (-1 : ℝ)..1, y t ^ 2) := by
  classical
  have h0 := Cvs.Prolate.EvenRungParseval.hasSum_sq_integral_mul_rung hc hy.continuousOn he
  have h : HasSum ((fun k : ℕ => (∫ s in (-1 : ℝ)..1, y s * rung c k s) ^ 2) ∘
      ((↑) : {k : ℕ | ∃ χ, IsLevelIdx c k χ} → ℕ)) (∫ s in (-1 : ℝ)..1, y s ^ 2) := h0
  rw [hasSum_subtype_iff_indicator] at h
  refine h.congr_fun fun k => ?_
  by_cases hk' : ∃ χ, IsLevelIdx c k χ
  · rw [indicator_of_mem (show k ∈ {k | ∃ χ, IsLevelIdx c k χ} from hk'), coef, if_pos hk']
    congr 1
    refine integral_congr fun t ht => ?_
    rw [uIcc_of_le (by norm_num)] at ht
    simp only [hk_eq hk' ht]
  · rw [indicator_of_notMem (show k ∉ {k | ∃ χ, IsLevelIdx c k χ} from hk'), coef, if_neg hk']
    simp

/-- `∫_{−1}^{1} (Σ_{k∈s} a_k h_k)(Σ_{j∈s} b_j h_j) = Σ_{k∈s} a_k b_k` for coefficients carried by levels. -/
theorem integral_sum_mul_sum {c : ℝ} (s : Finset ℕ) {a b : ℕ → ℝ}
    (ha : ∀ k, ¬ (∃ χ, IsLevelIdx c k χ) → a k = 0) :
    ∫ t in (-1 : ℝ)..1, (∑ k ∈ s, a k * hk c k t) * (∑ j ∈ s, b j * hk c j t) = ∑ k ∈ s, a k * b k := by
  have hint : ∀ k j, IntervalIntegrable (fun t => a k * hk c k t * (b j * hk c j t)) volume (-1) 1 :=
    fun k j => ((continuous_const.mul (continuous_hk c k)).mul
      (continuous_const.mul (continuous_hk c j))).intervalIntegrable _ _
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  have hint2 : ∀ k ∈ s, IntervalIntegrable (fun t => ∑ j ∈ s, a k * hk c k t * (b j * hk c j t)) volume (-1) 1 :=
    fun k _ => ((continuous_finsetSum s fun j _ => ((continuous_const.mul (continuous_hk c k)).mul
      (continuous_const.mul (continuous_hk c j)))) :
        Continuous fun t => ∑ j ∈ s, a k * hk c k t * (b j * hk c j t)).intervalIntegrable _ _
  rw [intervalIntegral.integral_finsetSum hint2]
  refine Finset.sum_congr rfl fun k hks => ?_
  rw [intervalIntegral.integral_finsetSum fun j _ => hint k j]
  rw [Finset.sum_eq_single k]
  · by_cases hk' : ∃ χ, IsLevelIdx c k χ
    · have := integral_hk_mul_hk hk' hk'
      rw [if_pos rfl] at this
      rw [show (fun t => a k * hk c k t * (b k * hk c k t)) = fun t => a k * b k * (hk c k t * hk c k t) by
        ext t; ring, intervalIntegral.integral_const_mul, this, mul_one]
    · rw [ha k hk']; simp
  · intro j _ hjk
    by_cases hk' : ∃ χ, IsLevelIdx c k χ
    · by_cases hj : ∃ χ, IsLevelIdx c j χ
      · have := integral_hk_mul_hk hk' hj
        rw [if_neg (Ne.symm hjk)] at this
        rw [show (fun t => a k * hk c k t * (b j * hk c j t)) = fun t => a k * b j * (hk c k t * hk c j t) by
          ext t; ring, intervalIntegral.integral_const_mul, this, mul_zero]
      · rw [hk_of_not hj]; simp
    · rw [ha k hk']; simp
  · intro h; exact absurd hks h

theorem coef_of_not {c : ℝ} {y : ℝ → ℝ} {k : ℕ} (h : ¬ ∃ χ, IsLevelIdx c k χ) : coef c y k = 0 := by
  unfold coef; rw [if_neg h]

/-- `‖Q Σ_{k∈s} a_k h_k‖² ≤ Σ_{k∈s} a_k²` for coefficients carried by levels. -/
theorem norm_sum_sq_le {c : ℝ} (s : Finset ℕ) {a : ℕ → ℝ} (ha : ∀ k, ¬ (∃ χ, IsLevelIdx c k χ) → a k = 0) :
    ‖∑ k ∈ s, a k • qI (continuous_hk c k)‖ ^ 2 ≤ ∑ k ∈ s, a k ^ 2 := by
  rw [← qI_sum s a (continuous_hk c)]
  refine (norm_qI_sq_le _).trans (le_of_eq ?_)
  rw [show (fun t => (∑ k ∈ s, a k * hk c k t) ^ 2) = fun t => (∑ k ∈ s, a k * hk c k t) * (∑ j ∈ s, a j * hk c j t)
    by ext t; ring, integral_sum_mul_sum s ha]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- `∫_{−1}^{1} (Σ_{k∈s} a_k h_k − y)² = ∫ y² − Σ_{k∈s} a_k²` for `a_k = ⟨y, h_k⟩`. -/
theorem integral_sub_sq {c : ℝ} (s : Finset ℕ) {y : ℝ → ℝ} (hy : Continuous y) :
    ∫ t in (-1 : ℝ)..1, ((∑ k ∈ s, coef c y k * hk c k t) - y t) ^ 2 =
      (∫ t in (-1 : ℝ)..1, y t ^ 2) - ∑ k ∈ s, coef c y k ^ 2 := by
  have hH : Continuous fun t => ∑ k ∈ s, coef c y k * hk c k t :=
    continuous_finsetSum s fun k _ => continuous_const.mul (continuous_hk c k)
  have h1 : IntervalIntegrable (fun t => (∑ k ∈ s, coef c y k * hk c k t) * (∑ j ∈ s, coef c y j * hk c j t))
    volume (-1) 1 := (hH.mul hH).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun t => 2 * ((∑ k ∈ s, coef c y k * hk c k t) * y t)) volume (-1) 1 :=
    ((hH.mul hy).const_mul 2).intervalIntegrable _ _
  have h3 : IntervalIntegrable (fun t => y t ^ 2) volume (-1) 1 := (hy.pow 2).intervalIntegrable _ _
  have h12 : IntervalIntegrable (fun t => (∑ k ∈ s, coef c y k * hk c k t) * (∑ j ∈ s, coef c y j * hk c j t) -
    2 * ((∑ k ∈ s, coef c y k * hk c k t) * y t)) volume (-1) 1 := h1.sub h2
  have hHy : ∫ t in (-1 : ℝ)..1, (∑ k ∈ s, coef c y k * hk c k t) * y t = ∑ k ∈ s, coef c y k ^ 2 := by
    simp_rw [Finset.sum_mul]
    have hi : ∀ k ∈ s, IntervalIntegrable (fun t => coef c y k * hk c k t * y t) volume (-1) 1 :=
      fun k _ => ((continuous_const.mul (continuous_hk c k)).mul hy).intervalIntegrable _ _
    rw [intervalIntegral.integral_finsetSum hi]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show (fun t => coef c y k * hk c k t * y t) = fun t => coef c y k * (y t * hk c k t) by ext t; ring,
      intervalIntegral.integral_const_mul]
    by_cases hk' : ∃ χ, IsLevelIdx c k χ
    · rw [sq]; congr 1; unfold coef; rw [if_pos hk']
    · rw [coef_of_not hk']; ring
  rw [show (fun t => ((∑ k ∈ s, coef c y k * hk c k t) - y t) ^ 2) = fun t =>
    (∑ k ∈ s, coef c y k * hk c k t) * (∑ j ∈ s, coef c y j * hk c j t) -
      2 * ((∑ k ∈ s, coef c y k * hk c k t) * y t) + y t ^ 2 by ext t; ring,
    intervalIntegral.integral_add h12 h3, intervalIntegral.integral_sub h1 h2,
    integral_sum_mul_sum s (fun k hk' => coef_of_not hk'), intervalIntegral.integral_const_mul, hHy]
  simp_rw [← sq]
  ring

/-- **The rung expansion in `L²(I)`**: `Q y = Σ_k ⟨y, h_k⟩ Q h_k` for even continuous `y`. -/
theorem hasSum_qI {c : ℝ} (hc : c ≠ 0) {y : ℝ → ℝ} (hy : Continuous y) (he : ∀ t ∈ Icc (-1 : ℝ) 1, y (-t) = y t) :
    HasSum (fun k => coef c y k • qI (continuous_hk c k)) (qI hy) := by
  have hP := hasSum_coef_sq hc hy he
  unfold HasSum
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hle : ∀ s : Finset ℕ, ‖∑ k ∈ s, coef c y k • qI (continuous_hk c k) - qI hy‖ ≤
      √((∫ t in (-1 : ℝ)..1, y t ^ 2) - ∑ k ∈ s, coef c y k ^ 2) := by
    intro s
    rw [← qI_sum s (coef c y) (continuous_hk c), ← qI_sub, ← integral_sub_sq s hy]
    exact Real.le_sqrt_of_sq_le (norm_qI_sq_le _)
  refine squeeze_zero (fun s => norm_nonneg _) hle ?_
  have ht : Tendsto (fun s : Finset ℕ => (∫ t in (-1 : ℝ)..1, y t ^ 2) - ∑ k ∈ s, coef c y k ^ 2) atTop (𝓝 0) := by
    have := (tendsto_const_nhds (x := ∫ t in (-1 : ℝ)..1, y t ^ 2)).sub hP
    rwa [sub_self] at this
  have := (Real.continuous_sqrt.tendsto 0).comp ht
  rw [Real.sqrt_zero] at this
  exact this

end Cvs.Prolate.Hardy.CentralRungExpansion

end
