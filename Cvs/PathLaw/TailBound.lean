/-
From rapid coefficients to super-algebraic projection tails
(rapid-decay campaign, stage 4).

Two abstract facts finish the analytic chain:

* `RapidFourierDecay.superAlgebraicDecay_coeffTail` — the ℓ¹ tails
  `∑_{|k|>N} ‖c_k‖` of a rapidly decaying sequence decay
  super-algebraically (dominate the tail termwise by
  `C/N^{q+1} · 1/k²` and sum the `p`-series).
* `norm_sub_starProjection_basisWindow_le` — in any Hilbert space with
  a `ℤ`-indexed Hilbert basis, the projection tail onto the window span
  `span{e_k : |k| ≤ N}` is at most the ℓ¹ coefficient tail: the
  projection minimizes distance, and the truncated basis expansion is a
  competitor whose error is the tail sum.

Together (`superAlgebraicDecay_basisWindow_tail`): a vector with
rapidly decaying basis coefficients has super-algebraically decaying
window-projection tails — the exact hypothesis shape of
`superalgebraic_sections`.
-/
import Cvs.PathLaw.CoeffFormula
import Mathlib.Analysis.PSeries

open Filter Submodule Real

namespace Cvs.PathLaw

/-- The ℓ¹ coefficient tail past the window `N`. -/
noncomputable def coeffTail (c : ℤ → ℂ) (N : ℕ) : ℝ :=
  ∑' k : ℤ, if (N : ℤ) < |k| then ‖c k‖ else 0

lemma coeffTail_term_nonneg (c : ℤ → ℂ) (N : ℕ) (k : ℤ) :
    0 ≤ (if (N : ℤ) < |k| then ‖c k‖ else 0) := by
  split
  · exact norm_nonneg _
  · exact le_refl 0

/-- A rapidly decaying sequence is absolutely summable. -/
theorem RapidFourierDecay.summable_norm {c : ℤ → ℂ}
    (hc : RapidFourierDecay c) : Summable fun k : ℤ => ‖c k‖ := by
  obtain ⟨C, hC⟩ := hc 2
  have hC0 : ∀ k : ℤ, k ≠ 0 → ‖c k‖ ≤ (max C 0) / (k : ℝ) ^ 2 := by
    intro k hk
    have hkpos : (0 : ℝ) < |(k : ℝ)| ^ 2 := by
      have : ((k : ℝ)) ≠ 0 := by exact_mod_cast hk
      positivity
    calc ‖c k‖ ≤ C / |(k : ℝ)| ^ 2 := hC k hk
      _ ≤ (max C 0) / |(k : ℝ)| ^ 2 := by gcongr; exact le_max_left C 0
      _ = (max C 0) / (k : ℝ) ^ 2 := by rw [sq_abs]
  have hs2 : Summable fun k : ℤ => (max C 0) * (1 / (k : ℝ) ^ 2) :=
    (summable_one_div_int_pow.mpr one_lt_two).mul_left _
  have hg : Summable fun k : ℤ => if k = 0 then 0 else ‖c k‖ := by
    refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) hs2
    · split
      · exact le_refl 0
      · exact norm_nonneg _
    · by_cases hk : k = 0
      · simp [hk]
      · rw [if_neg hk]
        calc ‖c k‖ ≤ (max C 0) / (k : ℝ) ^ 2 := hC0 k hk
          _ = (max C 0) * (1 / (k : ℝ) ^ 2) := by ring
  have hsingle : Summable fun k : ℤ => if k = 0 then ‖c 0‖ else 0 :=
    summable_of_ne_finset_zero (s := {0}) fun k hk =>
      if_neg (by simpa using hk)
  have := hg.add hsingle
  refine this.congr fun k => ?_
  by_cases hk : k = 0 <;> simp [hk]

/-- **The ℓ¹ tails of a rapidly decaying sequence decay
super-algebraically**: each tail term past `N` is dominated by
`C/N^{q+1} · 1/k²`, and the `p`-series sums. -/
theorem RapidFourierDecay.superAlgebraicDecay_coeffTail {c : ℤ → ℂ}
    (hc : RapidFourierDecay c) : SuperAlgebraicDecay (coeffTail c) := by
  intro q
  obtain ⟨C, hC⟩ := hc (q + 3)
  set C' : ℝ := max C 0 with hC'def
  have hC'0 : 0 ≤ C' := le_max_right C 0
  set S : ℝ := ∑' k : ℤ, 1 / (k : ℝ) ^ 2 with hSdef
  have hS0 : 0 ≤ S :=
    tsum_nonneg fun k => by positivity
  have hs2 : Summable fun k : ℤ => 1 / (k : ℝ) ^ 2 :=
    summable_one_div_int_pow.mpr one_lt_two
  -- the tail bound for N ≥ 1
  have hbound : ∀ N : ℕ, 1 ≤ N →
      coeffTail c N ≤ C' * S / (N : ℝ) ^ (q + 1) := by
    intro N hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hterm : ∀ k : ℤ, (if (N : ℤ) < |k| then ‖c k‖ else 0)
        ≤ (C' / (N : ℝ) ^ (q + 1)) * (1 / (k : ℝ) ^ 2) := by
      intro k
      by_cases hk : (N : ℤ) < |k|
      · rw [if_pos hk]
        have hk0 : k ≠ 0 := by
          intro h0
          rw [h0] at hk
          simp at hk
          omega
        have hkR : (N : ℝ) < |(k : ℝ)| := by
          have : ((N : ℤ) : ℝ) < (|k| : ℝ) := by exact_mod_cast hk
          simpa [Int.cast_abs] using this
        have hkR1 : (1 : ℝ) ≤ |(k : ℝ)| := le_trans (by exact_mod_cast hN)
          hkR.le
        have habs : (0 : ℝ) < |(k : ℝ)| := lt_of_lt_of_le zero_lt_one hkR1
        calc ‖c k‖ ≤ C / |(k : ℝ)| ^ (q + 3) := hC k hk0
          _ ≤ C' / |(k : ℝ)| ^ (q + 3) := by
              gcongr
              exact le_max_left C 0
          _ = (C' / |(k : ℝ)| ^ (q + 1)) * (1 / |(k : ℝ)| ^ 2) := by
              rw [div_mul_div_comm, mul_one, ← pow_add]
          _ ≤ (C' / (N : ℝ) ^ (q + 1)) * (1 / |(k : ℝ)| ^ 2) := by
              gcongr
          _ = (C' / (N : ℝ) ^ (q + 1)) * (1 / (k : ℝ) ^ 2) := by
              rw [sq_abs]
      · rw [if_neg hk]
        positivity
    have hsum_rhs : Summable fun k : ℤ =>
        (C' / (N : ℝ) ^ (q + 1)) * (1 / (k : ℝ) ^ 2) := hs2.mul_left _
    have hsum_lhs : Summable fun k : ℤ =>
        (if (N : ℤ) < |k| then ‖c k‖ else 0) :=
      Summable.of_nonneg_of_le (coeffTail_term_nonneg c N) hterm hsum_rhs
    calc coeffTail c N ≤ ∑' k : ℤ,
          (C' / (N : ℝ) ^ (q + 1)) * (1 / (k : ℝ) ^ 2) :=
        hsum_lhs.tsum_le_tsum hterm hsum_rhs
      _ = (C' / (N : ℝ) ^ (q + 1)) * S := tsum_mul_left
      _ = C' * S / (N : ℝ) ^ (q + 1) := by ring
  -- squeeze
  have htends : Tendsto (fun N : ℕ => C' * S / (N : ℝ)) atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    htends ?_ ?_
  · filter_upwards with N
    exact mul_nonneg (by positivity)
      (tsum_nonneg (coeffTail_term_nonneg c N))
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    calc (N : ℝ) ^ q * coeffTail c N
        ≤ (N : ℝ) ^ q * (C' * S / (N : ℝ) ^ (q + 1)) := by
          exact mul_le_mul_of_nonneg_left (hbound N hN) (by positivity)
      _ = C' * S / (N : ℝ) := by
          rw [pow_succ]
          field_simp

/-! ### Window spans of a `ℤ`-indexed Hilbert basis -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The window span `span{e_k : |k| ≤ N}` of a Hilbert basis. -/
noncomputable def basisWindow (e : HilbertBasis ℤ ℂ H) (N : ℕ) :
    Submodule ℂ H :=
  span ℂ (⇑e '' {k : ℤ | |k| ≤ (N : ℤ)})

instance basisWindow_finiteDimensional (e : HilbertBasis ℤ ℂ H) (N : ℕ) :
    FiniteDimensional ℂ (basisWindow e N) := by
  apply FiniteDimensional.span_of_finite
  apply Set.Finite.image
  have hsub : {k : ℤ | |k| ≤ (N : ℤ)} ⊆ Set.Icc (-(N : ℤ)) N := fun k hk =>
    Set.mem_Icc.mpr (abs_le.mp hk)
  exact (Set.finite_Icc _ _).subset hsub

/-- **Projection tails are controlled by coefficient tails**: the
truncated basis expansion is a competitor for the minimizing
projection, and its error is the ℓ¹ tail. -/
theorem norm_sub_starProjection_basisWindow_le
    (e : HilbertBasis ℤ ℂ H) (f : H) (N : ℕ)
    (hsum : Summable fun k : ℤ => ‖e.repr f k‖) :
    ‖f - (basisWindow e N).starProjection f‖
      ≤ coeffTail (fun k => e.repr f k) N := by
  classical
  set S : Finset ℤ := Finset.Icc (-(N : ℤ)) N with hSdef
  set g : H := ∑ k ∈ S, e.repr f k • e k with hgdef
  have hgmem : g ∈ basisWindow e N := by
    apply Submodule.sum_mem
    intro k hk
    apply Submodule.smul_mem
    apply subset_span
    refine ⟨k, ?_, rfl⟩
    have := Finset.mem_Icc.mp hk
    show |k| ≤ (N : ℤ)
    rw [abs_le]
    exact this
  have hmin : ‖f - (basisWindow e N).starProjection f‖ ≤ ‖f - g‖ := by
    rw [Submodule.starProjection_minimal]
    exact ciInf_le ⟨0, by rintro x ⟨u, rfl⟩; exact norm_nonneg _⟩
      (⟨g, hgmem⟩ : basisWindow e N)
  have hfin : HasSum (fun k : ℤ =>
      if k ∈ S then e.repr f k • e k else 0) g := by
    have h : HasSum (fun k : ℤ => if k ∈ S then e.repr f k • e k else 0)
        (∑ k ∈ S, if k ∈ S then e.repr f k • e k else 0) :=
      hasSum_sum_of_ne_finset_zero (fun k hk => if_neg hk)
    have heq : (∑ k ∈ S, if k ∈ S then e.repr f k • e k else 0) = g := by
      rw [hgdef]
      exact Finset.sum_congr rfl fun k hk => if_pos hk
    rwa [heq] at h
  have htail : HasSum (fun k : ℤ =>
      if k ∈ S then 0 else e.repr f k • e k) (f - g) := by
    have h := (e.hasSum_repr f).sub hfin
    convert h using 1
    funext k
    by_cases hk : k ∈ S <;> simp [hk]
  have hnorm_le : ∀ k : ℤ, ‖if k ∈ S then 0 else e.repr f k • e k‖
      ≤ (if (N : ℤ) < |k| then ‖e.repr f k‖ else 0) := by
    intro k
    by_cases hk : k ∈ S
    · rw [if_pos hk, norm_zero]
      exact coeffTail_term_nonneg (fun k => e.repr f k) N k
    · rw [if_neg hk]
      have hk' : ¬(-(N : ℤ) ≤ k ∧ k ≤ N) := by
        simpa [hSdef, Finset.mem_Icc] using hk
      have habs : (N : ℤ) < |k| := by
        rcases le_or_gt k 0 with hk0 | hk0
        · rw [abs_of_nonpos hk0]
          omega
        · rw [abs_of_pos hk0]
          omega
      rw [if_pos habs, norm_smul]
      have h1 : ‖e k‖ = 1 := e.orthonormal.1 k
      rw [h1, mul_one]
  have hsum_rhs : Summable fun k : ℤ =>
      (if (N : ℤ) < |k| then ‖e.repr f k‖ else 0) := by
    refine Summable.of_nonneg_of_le
      (coeffTail_term_nonneg (fun k => e.repr f k) N) (fun k => ?_) hsum
    split
    · exact le_refl _
    · exact norm_nonneg _
  have hsum_lhs : Summable fun k : ℤ =>
      ‖if k ∈ S then 0 else e.repr f k • e k‖ :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _) hnorm_le hsum_rhs
  calc ‖f - (basisWindow e N).starProjection f‖
      ≤ ‖f - g‖ := hmin
    _ = ‖∑' k : ℤ, if k ∈ S then 0 else e.repr f k • e k‖ := by
        rw [htail.tsum_eq]
    _ ≤ ∑' k : ℤ, ‖if k ∈ S then 0 else e.repr f k • e k‖ :=
        norm_tsum_le_tsum_norm hsum_lhs
    _ ≤ coeffTail (fun k => e.repr f k) N :=
        hsum_lhs.tsum_le_tsum hnorm_le hsum_rhs

/-- **Rapid coefficients give super-algebraic window-projection tails**
— the exact hypothesis shape of `superalgebraic_sections`. -/
theorem superAlgebraicDecay_basisWindow_tail (e : HilbertBasis ℤ ℂ H)
    (f : H) (hc : RapidFourierDecay fun k => e.repr f k) :
    SuperAlgebraicDecay fun N =>
      ‖f - (basisWindow e N).starProjection f‖ :=
  SuperAlgebraicDecay.of_le (C := 1)
    hc.superAlgebraicDecay_coeffTail
    (fun N => norm_nonneg _)
    (fun N => by
      rw [one_mul]
      exact norm_sub_starProjection_basisWindow_le e f N hc.summable_norm)

end Cvs.PathLaw
