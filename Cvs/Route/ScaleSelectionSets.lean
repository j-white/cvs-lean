import Mathlib
import Cvs.WeilForm.MaskedShift.CoherenceDeficit

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Selection sets of scales: window averages and simultaneous phase returns

Two infinite sets of scales. For finite nonempty windows `W k ⊆ [k, ∞)`, the scales where `Φ` is at least its
`W k`-mean meet every window. In a compact normed group every `q • ξ` returns within `δ` of `0` for arbitrarily
large `q`; on the torus `ι → ℝ/ℤ` this puts `γᵢ log x / 2π` within `δ` of `ℤ` for all `i` at infinitely many `x`,
where `sin²(γᵢ log x / 2) ≤ (πδ)²`.
-/

noncomputable section

open Real Filter Set Topology

namespace Cvs.Route.ScaleSelectionSets

/-! ### 1. Scales where a functional is at least its window mean -/

/-- The scales `x ∈ W k` at which `Φ x` is at least the mean of `Φ` over `W k`, for some `k`. -/
def aboveMeanSet (W : ℕ → Finset ℕ) (Φ : ℕ → ℝ) : Set ℕ :=
  {x | ∃ k, x ∈ W k ∧ ∑ y ∈ W k, Φ y ≤ (W k).card * Φ x}

/-- **Every nonempty window meets `aboveMeanSet`.** -/
theorem exists_mem_aboveMeanSet (W : ℕ → Finset ℕ) (Φ : ℕ → ℝ) {k : ℕ} (hk : (W k).Nonempty) :
    ∃ x ∈ W k, x ∈ aboveMeanSet W Φ := by
  have hsum : ∑ _y ∈ W k, ∑ z ∈ W k, Φ z ≤ ∑ y ∈ W k, (W k).card * Φ y := by
    rw [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
  obtain ⟨x, hx, hle⟩ := Finset.exists_le_of_sum_le hk hsum
  exact ⟨x, hx, k, hx, hle⟩

/-- **`aboveMeanSet` is infinite** for nonempty windows `W k ⊆ [k, ∞)`. -/
theorem aboveMeanSet_infinite {W : ℕ → Finset ℕ} (hne : ∀ k, (W k).Nonempty)
    (hge : ∀ k, ∀ x ∈ W k, k ≤ x) (Φ : ℕ → ℝ) : (aboveMeanSet W Φ).Infinite := by
  refine Set.infinite_of_forall_exists_gt fun a => ?_
  obtain ⟨x, hxW, hxS⟩ := exists_mem_aboveMeanSet W Φ (hne (a + 1))
  exact ⟨x, hxS, Nat.lt_of_succ_le (hge (a + 1) x hxW)⟩

/-- On `aboveMeanSet`, `Φ x` is at least the mean of `Φ` over a window containing `x`. -/
theorem mean_le_of_mem_aboveMeanSet {W : ℕ → Finset ℕ} (hne : ∀ k, (W k).Nonempty) {Φ : ℕ → ℝ} {x : ℕ}
    (hx : x ∈ aboveMeanSet W Φ) :
    ∃ k, x ∈ W k ∧ (∑ y ∈ W k, Φ y) / (W k).card ≤ Φ x := by
  obtain ⟨k, hxk, hle⟩ := hx
  have hc : (0 : ℝ) < (W k).card := by exact_mod_cast (hne k).card_pos
  exact ⟨k, hxk, (div_le_iff₀ hc).mpr (by linarith)⟩

/-- The dyadic windows `[2^k, 2^{k+1})`, of length `log 2` in `L = log x`. -/
def dyadic (k : ℕ) : Finset ℕ := Finset.Ico (2 ^ k) (2 ^ (k + 1))

/-- The dyadic windows are nonempty. -/
theorem dyadic_nonempty (k : ℕ) : (dyadic k).Nonempty :=
  ⟨2 ^ k, Finset.mem_Ico.mpr ⟨le_rfl, Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self k)⟩⟩

/-- The dyadic window `k` lies in `[k, ∞)`. -/
theorem le_of_mem_dyadic {k x : ℕ} (hx : x ∈ dyadic k) : k ≤ x :=
  (Nat.lt_two_pow_self).le.trans (Finset.mem_Ico.mp hx).1

/-- The dyadic `aboveMeanSet` is infinite. -/
theorem aboveMeanSet_dyadic_infinite (Φ : ℕ → ℝ) : (aboveMeanSet dyadic Φ).Infinite :=
  aboveMeanSet_infinite dyadic_nonempty (fun _ _ hx => le_of_mem_dyadic hx) Φ

/-! ### 2. Returns in a compact group -/

/-- **Recurrence in a compact normed group**: `‖q • ξ‖ < δ` for some `q ≥ M`, for every `δ > 0` and `M`. -/
theorem exists_ge_norm_nsmul_lt {G : Type*} [SeminormedAddCommGroup G] [CompactSpace G] (ξ : G) {δ : ℝ}
    (hδ : 0 < δ) (M : ℕ) : ∃ q : ℕ, M ≤ q ∧ ‖q • ξ‖ < δ := by
  obtain ⟨a, -, φ, hφ, hlim⟩ :=
    isCompact_univ.tendsto_subseq (x := fun n : ℕ => n • ξ) (fun n => mem_univ _)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hlim (δ / 2) (by positivity)
  set k := φ N + M + N
  have hk : φ N + M ≤ φ k := (Nat.le_add_right _ N).trans (hφ.id_le k)
  refine ⟨φ k - φ N, by omega, ?_⟩
  rw [sub_nsmul ξ (show φ N ≤ φ k by omega), ← sub_eq_add_neg, ← dist_eq_norm]
  have h1 := hN k (by omega)
  have h2 := hN N le_rfl
  simp only [Function.comp_apply] at h1 h2
  calc dist (φ k • ξ) (φ N • ξ) ≤ dist (φ k • ξ) a + dist a (φ N • ξ) := dist_triangle _ _ _
    _ < δ / 2 + δ / 2 := add_lt_add h1 (by rw [dist_comm]; exact h2)
    _ = δ := by ring

/-- **Simultaneous returns on `ℝ/ℤ`**: for finitely many `αᵢ`, `‖q αᵢ‖_{ℝ/ℤ} < δ` for all `i` at some `q ≥ M`. -/
theorem exists_ge_forall_norm_mul_lt {ι : Type*} [Fintype ι] (α : ι → ℝ) {δ : ℝ} (hδ : 0 < δ) (M : ℕ) :
    ∃ q : ℕ, M ≤ q ∧ ∀ i, ‖(((q : ℝ) * α i : ℝ) : UnitAddCircle)‖ < δ := by
  obtain ⟨q, hq, hn⟩ :=
    exists_ge_norm_nsmul_lt (G := ι → UnitAddCircle) (fun i => (α i : UnitAddCircle)) hδ M
  refine ⟨q, hq, fun i => lt_of_le_of_lt ?_ hn⟩
  have h := norm_le_pi_norm (q • fun i => (α i : UnitAddCircle)) i
  have he : (q • fun i => (α i : UnitAddCircle)) i = (((q : ℝ) * α i : ℝ) : UnitAddCircle) := by
    rw [Pi.smul_apply, ← AddCircle.coe_nsmul, nsmul_eq_mul]
  rwa [he] at h

/-! ### 3. Scales with all phases `γᵢ log x / 2π` near `ℤ` -/

/-- The scales `x` with `‖γᵢ log x / 2π‖_{ℝ/ℤ} ≤ δ` for every `i`. -/
def phaseSet {ι : Type*} (γ : ι → ℝ) (δ : ℝ) : Set ℕ :=
  {x | ∀ i, ‖((γ i * Real.log x / (2 * π) : ℝ) : UnitAddCircle)‖ ≤ δ}

/-- `‖(y : ℝ/ℤ)‖ ≤ |y|`. -/
theorem norm_coe_le_abs (y : ℝ) : ‖(y : UnitAddCircle)‖ ≤ |y| := by
  rw [UnitAddCircle.norm_eq]
  simpa using round_le y 0

/-- `0 ≤ q − log ⌊e^q⌋₊ < 1/⌊e^q⌋₊` for `q ≥ 0`. -/
theorem sub_log_floor_exp {q : ℝ} (hq : 0 ≤ q) :
    0 < (⌊Real.exp q⌋₊ : ℝ) ∧ q < ⌊Real.exp q⌋₊ ∧ 0 ≤ q - Real.log ⌊Real.exp q⌋₊ ∧
      q - Real.log ⌊Real.exp q⌋₊ < 1 / ⌊Real.exp q⌋₊ := by
  set x : ℕ := ⌊Real.exp q⌋₊
  have hlt : Real.exp q < x + 1 := Nat.lt_floor_add_one _
  have hle : (x : ℝ) ≤ Real.exp q := Nat.floor_le (Real.exp_pos q).le
  have hq1 : q + 1 ≤ Real.exp q := Real.add_one_le_exp q
  have hqx : q < x := by linarith
  have hx0 : (0 : ℝ) < x := lt_of_le_of_lt hq hqx
  refine ⟨hx0, hqx, ?_, ?_⟩
  · have := Real.log_le_log hx0 hle
    rw [Real.log_exp] at this
    linarith
  · have h1 := Real.log_le_sub_one_of_pos (div_pos (Real.exp_pos q) hx0)
    rw [Real.log_div (Real.exp_pos q).ne' hx0.ne', Real.log_exp] at h1
    have h2 : Real.exp q / x - 1 < 1 / x := by
      rw [div_sub_one hx0.ne', div_lt_div_iff_of_pos_right hx0]
      linarith
    linarith

/-- **`phaseSet γ δ` is infinite** for finitely many ordinates `γᵢ` and every `δ > 0`. -/
theorem phaseSet_infinite {ι : Type*} [Fintype ι] (γ : ι → ℝ) {δ : ℝ} (hδ : 0 < δ) :
    (phaseSet γ δ).Infinite := by
  refine Set.infinite_of_forall_exists_gt fun a => ?_
  set B : ℝ := ∑ i, |γ i|
  have hB : ∀ i, |γ i| ≤ B := fun i =>
    Finset.single_le_sum (f := fun i => |γ i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)
  obtain ⟨q, hqM, hq⟩ :=
    exists_ge_forall_norm_mul_lt (fun i => γ i / (2 * π)) (half_pos hδ) (a + ⌈B / δ⌉₊)
  obtain ⟨hx0, hqx, hd0, hd1⟩ := sub_log_floor_exp (Nat.cast_nonneg q)
  set x : ℕ := ⌊Real.exp q⌋₊
  have hqM' : ((a + ⌈B / δ⌉₊ : ℕ) : ℝ) ≤ q := by exact_mod_cast hqM
  have hBx : B ≤ δ * x := by
    have h1 : B / δ ≤ (⌈B / δ⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : B / δ ≤ x := by push_cast at hqM'; linarith [(Nat.cast_nonneg a : (0 : ℝ) ≤ a)]
    rwa [div_le_iff₀ hδ, mul_comm] at h2
  refine ⟨x, fun i => ?_, ?_⟩
  · set d := q - Real.log x
    have hsplit : γ i * Real.log x / (2 * π) = (q : ℝ) * (γ i / (2 * π)) - γ i * d / (2 * π) := by
      simp only [d]; ring
    have hpi : (0 : ℝ) < 2 * π := by positivity
    have herr : |γ i * d / (2 * π)| ≤ δ / 2 := by
      rw [abs_div, abs_mul, abs_of_nonneg hd0, abs_of_pos hpi, div_le_iff₀ hpi]
      have h1 : |γ i| * d ≤ |γ i| * (1 / x) := mul_le_mul_of_nonneg_left hd1.le (abs_nonneg _)
      have h2 : |γ i| * (1 / x) ≤ δ := by
        rw [mul_one_div, div_le_iff₀ hx0]
        exact (hB i).trans hBx
      nlinarith [Real.pi_gt_three]
    rw [hsplit, AddCircle.coe_sub]
    calc ‖(((q : ℝ) * (γ i / (2 * π)) : ℝ) : UnitAddCircle) - ((γ i * d / (2 * π) : ℝ) : UnitAddCircle)‖
        ≤ ‖(((q : ℝ) * (γ i / (2 * π)) : ℝ) : UnitAddCircle)‖
          + ‖((γ i * d / (2 * π) : ℝ) : UnitAddCircle)‖ := norm_sub_le _ _
      _ ≤ δ / 2 + δ / 2 := add_le_add (hq i).le ((norm_coe_le_abs _).trans herr)
      _ = δ := by ring
  · have : (a : ℝ) < x := by push_cast at hqM'; linarith [(Nat.cast_nonneg ⌈B / δ⌉₊ : (0 : ℝ) ≤ _)]
    exact_mod_cast this

/-- **The phase factor on `phaseSet`**: `sin²(γᵢ log x / 2) ≤ (πδ)²` for every `i`. -/
theorem sin_sq_le_of_mem_phaseSet {ι : Type*} {γ : ι → ℝ} {δ : ℝ} {x : ℕ} (hx : x ∈ phaseSet γ δ) (i : ι) :
    Real.sin (γ i * Real.log x / 2) ^ 2 ≤ (π * δ) ^ 2 := by
  have h := Cvs.WeilForm.MaskedShift.CoherenceDeficit.abs_sin_pi_le (γ i * Real.log x / (2 * π))
  have harg : π * (γ i * Real.log x / (2 * π)) = γ i * Real.log x / 2 := by field_simp
  rw [harg] at h
  have h2 : |Real.sin (γ i * Real.log x / 2)| ≤ π * δ :=
    h.trans (mul_le_mul_of_nonneg_left (hx i) Real.pi_pos.le)
  rw [← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) h2 2

/-- **Weighted phase sum on `phaseSet`**: `∑ cᵢ sin²(γᵢ log x / 2) ≤ (πδ)² ∑ cᵢ` for `cᵢ ≥ 0`. -/
theorem sum_mul_sin_sq_le_of_mem_phaseSet {ι : Type*} [Fintype ι] {γ c : ι → ℝ} (hc : ∀ i, 0 ≤ c i)
    {δ : ℝ} {x : ℕ} (hx : x ∈ phaseSet γ δ) :
    ∑ i, c i * Real.sin (γ i * Real.log x / 2) ^ 2 ≤ (π * δ) ^ 2 * ∑ i, c i := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [mul_comm ((π * δ) ^ 2)]
  exact mul_le_mul_of_nonneg_left (sin_sq_le_of_mem_phaseSet hx i) (hc i)

end Cvs.Route.ScaleSelectionSets
