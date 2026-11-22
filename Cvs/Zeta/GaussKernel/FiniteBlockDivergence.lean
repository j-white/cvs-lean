import Mathlib
import Cvs.Zeta.GaussKernel.OffsetKernel

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Driving a finite block to `-∞`

A summable real family whose finite block is below `-B` and whose tail is at most `B` has
negative total.
-/

open Complex Real

namespace Cvs.Zeta.GaussKernel.AdmissibleKernel

/-!
## The assembly

Two pieces remain, and neither mentions `zeta`.
-/

/-- The split, for an arbitrary summable real family. -/
theorem tsum_neg_of_finset {ι : Type*} {f : ι → ℝ} (hf : Summable f) (S : Finset ι)
    {B : ℝ} (hS : ∑ i ∈ S, f i < -B)
    (htail : ∑' i : ((S : Set ι)ᶜ : Set ι), f i ≤ B) :
    ∑' i, f i < 0 := by
  rw [← hf.sum_add_tsum_compl (s := S)]
  linarith

/-!
## The finite block

The tail is handled.
-/

/-- A growing exponential beats any constant multiple of a slower one. -/
theorem tendsto_exp_sub_const_mul_exp {A K c₀ c₁ : ℝ} (hA : 0 < A) (h0 : 0 < c₀)
    (h1 : c₁ < c₀) :
    Filter.Tendsto (fun lam : ℝ => A * Real.exp (lam * c₀) - K * Real.exp (lam * c₁))
      Filter.atTop Filter.atTop := by
  have hz : Filter.Tendsto (fun lam : ℝ => 2 * K * Real.exp (lam * (c₁ - c₀)))
      Filter.atTop (nhds 0) := by
    simpa using (tendsto_exp_mul_nhds_zero (by linarith : c₁ - c₀ < 0)).const_mul (2 * K)
  have hev := hz.eventually_lt_const hA
  have hgrow : Filter.Tendsto (fun lam : ℝ => A / 2 * Real.exp (lam * c₀))
      Filter.atTop Filter.atTop := by
    refine Filter.Tendsto.const_mul_atTop (by linarith : (0 : ℝ) < A / 2) ?_
    exact Real.tendsto_exp_atTop.comp
      (Filter.Tendsto.atTop_mul_const h0 (Filter.tendsto_id (α := ℝ)))
  refine Filter.tendsto_atTop_mono' Filter.atTop ?_ hgrow
  filter_upwards [hev] with lam hlam
  have hexp0 : (0 : ℝ) < Real.exp (lam * c₀) := Real.exp_pos _
  have heq : Real.exp (lam * c₁) = Real.exp (lam * c₀) * Real.exp (lam * (c₁ - c₀)) := by
    rw [← Real.exp_add]; ring_nf
  rw [heq]
  nlinarith [mul_pos hexp0
    (by linarith : (0 : ℝ) < A / 2 - K * Real.exp (lam * (c₁ - c₀)))]

/-- The pointwise core: at a single `lam`, the block is below the difference of the two
exponentials. -/
theorem finset_sum_le_bound {ι : Type*} [DecidableEq ι] {S T : Finset ι}
    (hTS : T ⊆ S) (hT : T.Nonempty) {f : ι → ℝ → ℝ} {c₀ c₁ A B lam : ℝ}
    (hA : 0 < A) (hB : 0 ≤ B)
    (hdom : ∀ i ∈ T, f i lam ≤ -(A * Real.exp (lam * c₀)))
    (hbd : ∀ i ∈ S, i ∉ T → f i lam ≤ B * Real.exp (lam * c₁)) :
    ∑ i ∈ S, f i lam
      ≤ -(A * Real.exp (lam * c₀) - ((S.card : ℝ) * B) * Real.exp (lam * c₁)) := by
  rw [← Finset.sum_sdiff hTS]
  have hE0 : (0 : ℝ) < Real.exp (lam * c₀) := Real.exp_pos _
  have hE1 : (0 : ℝ) ≤ Real.exp (lam * c₁) := (Real.exp_pos _).le
  have hT1 : (1 : ℝ) ≤ (T.card : ℝ) := by
    have : 1 ≤ T.card := hT.card_pos
    exact_mod_cast this
  have hTsum : ∑ i ∈ T, f i lam ≤ -(A * Real.exp (lam * c₀)) := by
    calc ∑ i ∈ T, f i lam ≤ ∑ _i ∈ T, -(A * Real.exp (lam * c₀)) :=
          Finset.sum_le_sum fun i hi => hdom i hi
      _ = -((T.card : ℝ) * (A * Real.exp (lam * c₀))) := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ -(A * Real.exp (lam * c₀)) := by
          nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (T.card : ℝ) - 1)
            (mul_pos hA hE0).le]
  have hRsum : ∑ i ∈ S \ T, f i lam
      ≤ ((S.card : ℝ) * B) * Real.exp (lam * c₁) := by
    calc ∑ i ∈ S \ T, f i lam ≤ ∑ _i ∈ S \ T, B * Real.exp (lam * c₁) :=
          Finset.sum_le_sum fun i hi =>
            hbd i (Finset.mem_sdiff.mp hi).1 (Finset.mem_sdiff.mp hi).2
      _ = (((S \ T).card : ℝ)) * (B * Real.exp (lam * c₁)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((S.card : ℝ) * B) * Real.exp (lam * c₁) := by
          have hc : (((S \ T).card : ℝ)) ≤ (S.card : ℝ) := by
            exact_mod_cast Finset.card_le_card Finset.sdiff_subset
          have hBE : (0 : ℝ) ≤ B * Real.exp (lam * c₁) := by positivity
          nlinarith [mul_le_mul_of_nonneg_right hc hBE]
  linarith

/-- **The block, when the target only dips at special `lam`.** This is the form the kernel needs:
`re_gaussKernel_le_neg_half` holds where the cosine is `-1`, which is an arithmetic
progression, not a ray. -/
theorem frequently_finset_sum_lt {ι : Type*} [DecidableEq ι] {S T : Finset ι}
    (hTS : T ⊆ S) (hT : T.Nonempty)
    {f : ι → ℝ → ℝ} {c₀ c₁ A B : ℝ} (hA : 0 < A) (hB : 0 ≤ B) (h0 : 0 < c₀)
    (h1 : c₁ < c₀) {P : ℝ → Prop} (hP : ∃ᶠ lam : ℝ in Filter.atTop, P lam)
    (hdom : ∀ i ∈ T, ∀ lam : ℝ, 0 ≤ lam → P lam →
      f i lam ≤ -(A * Real.exp (lam * c₀)))
    (hbd : ∀ i ∈ S, i ∉ T → ∀ lam : ℝ, 0 ≤ lam → f i lam ≤ B * Real.exp (lam * c₁))
    (C : ℝ) :
    ∃ᶠ lam : ℝ in Filter.atTop, ∑ i ∈ S, f i lam < -C := by
  have hlim : Filter.Tendsto
      (fun lam : ℝ => -(A * Real.exp (lam * c₀)
        - ((S.card : ℝ) * B) * Real.exp (lam * c₁)))
      Filter.atTop Filter.atBot :=
    Filter.tendsto_neg_atBot_iff.mpr
      (tendsto_exp_sub_const_mul_exp (K := (S.card : ℝ) * B) hA h0 h1)
  have hev := (Filter.eventually_ge_atTop (0 : ℝ)).and
    (hlim.eventually (Filter.eventually_lt_atBot (-C)))
  refine (hP.and_eventually hev).mono fun lam h => ?_
  refine lt_of_le_of_lt ?_ h.2.2
  exact finset_sum_le_bound hTS hT hA hB
    (fun i hi => hdom i hi lam h.2.1 h.1)
    (fun i hiS hiT => hbd i hiS hiT lam h.2.1)

/-! ## Composing the two halves

The block is negative *frequently* — the cosine reaches `-1` only on an
arithmetic progression of `lam`, not on a ray — while the tail is small
*eventually*.  Mathlib's `Filter.Frequently.and_eventually` is exactly the
combinator for that mismatch, and with it the assembly is three lines. -/

/-- **The assembly.** A summable family whose finite block is frequently below `-1` and whose tail
is eventually at most `1` has negative total at arbitrarily large `lam`. -/
theorem frequently_tsum_neg {ι : Type*} {f : ℝ → ι → ℝ} (S : Finset ι)
    (hsum : ∀ᶠ lam : ℝ in Filter.atTop, Summable (f lam))
    (hblock : ∃ᶠ lam : ℝ in Filter.atTop, ∑ i ∈ S, f lam i < -1)
    (htail : ∀ᶠ lam : ℝ in Filter.atTop,
      ∑' i : ((S : Set ι)ᶜ : Set ι), f lam i ≤ 1) :
    ∃ᶠ lam : ℝ in Filter.atTop, ∑' i, f lam i < 0 :=
  (hblock.and_eventually (htail.and hsum)).mono fun _ h =>
    tsum_neg_of_finset h.2.2 S h.1 h.2.1

/-- The maximum the block lemma asks for. -/
theorem exists_max_lt {ι : Type*} [DecidableEq ι] (R : Finset ι) (c : ι → ℝ) {c₀ : ℝ}
    (h : ∀ i ∈ R, c i < c₀) : ∃ c₁, c₁ < c₀ ∧ ∀ i ∈ R, c i ≤ c₁ := by
  rcases R.eq_empty_or_nonempty with rfl | hne
  · exact ⟨c₀ - 1, by linarith, by simp⟩
  · refine ⟨(R.image c).max' (hne.image c), ?_, fun i hi => ?_⟩
    · obtain ⟨j, hj, hje⟩ := Finset.mem_image.mp ((R.image c).max'_mem (hne.image c))
      rw [← hje]; exact h j hj
    · exact Finset.le_max' _ _ (Finset.mem_image_of_mem c hi)

/-!
## Choosing the offset

Write the offset as `a = γ₀ - ε` with `ε > 0` small, where `γ₀` is the target's ordinate.
-/

/-- The dual of `exists_max_lt`: a positive quantity on a finite set is uniformly bounded below by
a positive number. -/
theorem exists_pos_lt_all {ι : Type*} [DecidableEq ι] (R : Finset ι) (d : ι → ℝ)
    (h : ∀ i ∈ R, 0 < d i) : ∃ ε, 0 < ε ∧ ∀ i ∈ R, ε < d i := by
  rcases R.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, by simp⟩
  · have hmem := (R.image d).min'_mem (hne.image d)
    obtain ⟨j, hj, hje⟩ := Finset.mem_image.mp hmem
    have hpos : 0 < (R.image d).min' (hne.image d) := by
      rw [← hje]; exact h j hj
    refine ⟨(R.image d).min' (hne.image d) / 2, by linarith, fun i hi => ?_⟩
    have hmin := Finset.min'_le (R.image d) (d i) (Finset.mem_image_of_mem d hi)
    linarith

/-! ## The kernel's bounds in the block's shape

Two statements, matching the two hypotheses of `tendsto_finset_sum_atBot`.
Both are the closed form of `re_gaussKernel` plus `|cos| ≤ 1`. -/

/-!
## The second bump

`re_gaussKernel_le_two_exp` bounds a competitor by the larger of its two rates, and
`rate_lt_of_offset` covers only the first.
-/

/-- The second bump's rate is below the target's as soon as the offset does not
sit within `ε` of `-γ`. -/
theorem rate_snd_lt {δ₀ δ γ a ε : ℝ} (hε : 0 < ε) (hδ : δ ^ 2 ≤ δ₀ ^ 2)
    (h : ε < |γ + a|) : δ ^ 2 - (γ + a) ^ 2 < δ₀ ^ 2 - ε ^ 2 := by
  have h1 : ε ^ 2 < (γ + a) ^ 2 := by
    nlinarith [sq_abs (γ + a), abs_nonneg (γ + a)]
  linarith

/-!
## When the target's bound applies

`re_gaussKernel_le_neg_half` needs two things at once: the cosine at `-1`, and the second bump
dominated.
-/

/-!
## The quadruple

An off-line zero comes with three partners: `1-ρ`, `conj ρ`, `1-conj ρ`, which in the `(γ, δ)`
coordinates are the sign changes `γ ↦ -γ` and `δ ↦ -δ`.
-/

/-! ## The block, instantiated at the kernel

Every hypothesis of `frequently_finset_sum_lt` now has a matching lemma.  This
is the wiring: `re_gaussKernel_le_neg_half_of` for the distinguished set,
`re_gaussKernel_le_two_exp` for the rest, and `exists_max_lt` to turn the
pointwise rate comparison into the uniform one. -/

/-!
## Discharging the dominating series

`frequently_kernel_tsum_neg` still carries `hb`, summability of the two envelopes at one fixed
`lam₀`.
-/

end Cvs.Zeta.GaussKernel.AdmissibleKernel
