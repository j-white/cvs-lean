import Mathlib
import Cvs.StepA.StepACriterion
import Cvs.Zeta.GaussKernel.DivisorWeightCoordinates
import Cvs.Zeta.GaussKernel.WeightedRateLemma
import Cvs.Zeta.GaussKernel.ZetaZeroStatement
import Cvs.Zeta.RiemannVonMangoldt
import Cvs.Zeta.RiemannXi
import Cvs.Zeta.XiZeroStripBridge
import Cvs.Zeta.ZeroCounting.FinitelyManyBelowOrdinate
import Cvs.Zeta.ZeroIndexSummability

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The distinct positive zero ordinates in increasing order

`posOrd` is the set of values `|Im ρ|` over the nontrivial zeros, and `ordSeq k` is its `k`-th element
in increasing order (`γ_{k+1}` in the paper's numbering). It is strictly increasing, starts above
`6.24`, every zero with `|Im ρ| < ordSeq k` has `|Im ρ| = ordSeq j` for some `j < k`, and
`∑ 1/ordSeq k²` converges.
-/

noncomputable section

open Filter Topology

namespace Cvs.Finite.OddDisplacementPencil
open Cvs.ZeroCounting
open Cvs.Zeta.GaussKernel.AdmissibleKernel (nonTrivialZeroSet)

/-- The positive zero ordinates `{|Im ρ|}`. -/
def posOrd : Set ℝ := {t | 0 < t ∧ ∃ ρ : nonTrivialZeroSet, |(ρ : ℂ).im| = t}

/-- The `k`-th positive zero ordinate in increasing order, distinct values counted once. -/
def ordSeq : ℕ → ℝ
  | 0 => sInf posOrd
  | k + 1 => sInf (posOrd ∩ Set.Ioi (ordSeq k))

/-- Every zero of `ξ` is a nontrivial zero of `ζ`. -/
private theorem mem_nonTrivialZeroSet_of_riemannXi {u : ℂ} (h : Cvs.Zeta.riemannXi u = 0) :
    u ∈ nonTrivialZeroSet := by
  obtain ⟨h0, h1⟩ := Cvs.Zeta.XiZeroStripBridge.riemannXi_mem_strip h
  have hu1 : u ≠ 1 := fun hu => by rw [hu, Complex.one_re] at h1; exact lt_irrefl 1 h1
  exact ⟨(Cvs.Zeta.riemannXi_eq_zero_iff_riemannZeta h0 hu1).mp h, h0, h1⟩

/-- `log (2 + x) ^ n / x → 0`. -/
private theorem tendsto_log_two_add_pow_div (n : ℕ) :
    Tendsto (fun x : ℝ => Real.log (2 + x) ^ n / x) atTop (𝓝 0) := by
  refine ((Real.tendsto_pow_log_div_mul_add_atTop 1 (-2) n one_ne_zero).comp
    (tendsto_atTop_add_const_left atTop 2 tendsto_id)).congr fun x => ?_
  simp only [Function.comp_apply, id]
  ring_nf

/-- `x log (x/2π) − x + 2π − C (1 + log (2 + x))² → ∞`: the Riemann–von Mangoldt main term
outgrows its error term. -/
private theorem tendsto_mainTerm_sub_err (C : ℝ) :
    Tendsto (fun x : ℝ => x * Real.log (x / (2 * Real.pi)) - x + 2 * Real.pi
      - C * (1 + Real.log (2 + x)) ^ 2) atTop atTop := by
  have hq : Tendsto (fun x : ℝ => 1 / x + 2 * (Real.log (2 + x) ^ 1 / x)
      + Real.log (2 + x) ^ 2 / x) atTop (𝓝 (0 + 2 * 0 + 0)) :=
    ((tendsto_const_nhds.div_atTop tendsto_id).add
      ((tendsto_log_two_add_pow_div 1).const_mul 2)).add (tendsto_log_two_add_pow_div 2)
  have hl : Tendsto (fun x : ℝ => Real.log (x / (2 * Real.pi))) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_id.atTop_div_const (by positivity))
  have hf : Tendsto (fun x : ℝ => Real.log (x / (2 * Real.pi)) + (-1 - C *
      (1 / x + 2 * (Real.log (2 + x) ^ 1 / x) + Real.log (2 + x) ^ 2 / x))) atTop atTop :=
    hl.atTop_add ((tendsto_const_nhds.sub (hq.const_mul C)))
  refine tendsto_atTop_add_const_right _ (2 * Real.pi) (tendsto_id.atTop_mul_atTop₀ hf)
    |>.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  simp only [id]
  field_simp
  ring

/-- Above every height there is a nontrivial zero. -/
private theorem exists_lt_abs_im (t : ℝ) : ∃ ρ : nonTrivialZeroSet, t < |(ρ : ℂ).im| := by
  by_contra hcon
  push Not at hcon
  have hxi : ∀ u : ℂ, Cvs.Zeta.riemannXi u = 0 → |u.im| ≤ t := fun u hu =>
    hcon ⟨u, mem_nonTrivialZeroSet_of_riemannXi hu⟩
  obtain ⟨C, -, hC⟩ := Cvs.ZeroCounting.exists_zero_count_asymptotic
  set T₀ : ℝ := max 20 (t + 1)
  obtain ⟨T₁, S₁, m₁, hT₁, -, hS₁, hm₁, -⟩ := hC T₀ (le_max_left _ _)
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((tendsto_mainTerm_sub_err C).eventually_gt_atTop
    (Real.pi * ∑ ρ ∈ S₁, (m₁ ρ : ℝ)))
  obtain ⟨T', S, m, hT', -, hS, hm, herr⟩ := hC (max T₀ N) (le_trans (le_max_left _ _)
    (le_max_left _ _))
  have hSS : S = S₁ := by
    ext u
    rw [hS, hS₁]
    refine and_congr_right fun hu => ?_
    have h1 : |u.im| < T₀ := lt_of_le_of_lt (hxi u hu) (lt_of_lt_of_le (lt_add_one t)
      (le_max_right _ _))
    exact ⟨fun _ => lt_of_lt_of_le h1 hT₁,
      fun _ => lt_of_lt_of_le h1 (le_trans (le_max_left _ _) hT')⟩
  have hmm : m = m₁ := funext fun u => by exact_mod_cast (hm u).trans (hm₁ u).symm
  have hlt := hN T' (le_trans (le_max_right _ _) hT')
  rw [hSS, hmm] at herr
  have := (abs_le.mp herr).1
  linarith

-- H_fix Theorem (the `γ_i` are the distinct positive ordinates; finitely many below each height)
/-- **Above every height the next positive ordinate is attained**: `posOrd ∩ (t, ∞)` has a least
element. -/
theorem isLeast_posOrd_Ioi (t : ℝ) : IsLeast (posOrd ∩ Set.Ioi t) (sInf (posOrd ∩ Set.Ioi t)) := by
  obtain ⟨ρ, hρ⟩ := exists_lt_abs_im (max t 0)
  set a := |(ρ : ℂ).im|
  have ha : a ∈ posOrd ∩ Set.Ioi t :=
    ⟨⟨lt_of_le_of_lt (le_max_right _ _) hρ, ρ, rfl⟩, lt_of_le_of_lt (le_max_left _ _) hρ⟩
  have hfin : (posOrd ∩ Set.Ioi t ∩ Set.Iic a).Finite := by
    refine ((Cvs.Zeta.ZeroCounting.FinitelyManyBelowOrdinate.finite_ordinate_below (a + 1)).image
      fun σ : nonTrivialZeroSet => |(σ : ℂ).im|).subset ?_
    rintro s ⟨⟨⟨-, σ, rfl⟩, -⟩, hs⟩
    exact ⟨σ, lt_of_le_of_lt hs (lt_add_one a), rfl⟩
  obtain ⟨m, hm, hmin⟩ := Set.exists_min_image _ id hfin ⟨a, ha, Set.mem_Iic.mpr le_rfl⟩
  have hleast : IsLeast (posOrd ∩ Set.Ioi t) m := by
    refine ⟨hm.1, fun b hb => ?_⟩
    rcases le_or_gt b a with hba | hab
    · exact hmin b ⟨hb, hba⟩
    · exact le_trans hm.2 hab.le
  rw [hleast.csInf_eq]
  exact hleast

/-- Each `ordSeq k` is a positive ordinate. -/
private theorem ordSeq_mem_posOrd (k : ℕ) : ordSeq k ∈ posOrd := by
  cases k with
  | zero =>
    have h := (isLeast_posOrd_Ioi 0).1.1
    have he : posOrd ∩ Set.Ioi 0 = posOrd := Set.inter_eq_left.mpr fun t ht => ht.1
    rw [he] at h
    exact h
  | succ k => exact (isLeast_posOrd_Ioi (ordSeq k)).1.1

/-- `ordSeq` is strictly increasing. -/
private theorem strictMono_ordSeq_aux : StrictMono ordSeq :=
  strictMono_nat_of_lt_succ fun k => (isLeast_posOrd_Ioi (ordSeq k)).1.2

/-- `1/|γ|²` is summable over the nontrivial zeros. -/
private theorem summable_inv_abs_im_sq :
    Summable fun σ : nonTrivialZeroSet => 1 / |(σ : ℂ).im| ^ 2 := by
  refine Cvs.Zeta.ZeroIndexSummability.summable_of_inv_sq_bound (C := 4) (by norm_num) fun σ => ?_
  have h1 : (1 : ℝ) ≤ |(σ : ℂ).im| :=
    le_trans (by norm_num) (Cvs.StepA.StepACriterion.lt_abs_im σ).le
  have hw : (1 : ℝ) ≤ (Cvs.Criterion.divisorWeight σ : ℝ) := by
    exact_mod_cast Cvs.Criterion.one_le_divisorWeight σ
  set u := |(σ : ℂ).im|
  have hu : 0 < u := by linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc 1 / u ^ 2 ≤ 4 / (1 + u) ^ 2 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
    _ ≤ 4 * ((Cvs.Criterion.divisorWeight σ : ℝ) / (1 + u) ^ 2) := by
        rw [mul_div_assoc', div_le_div_iff_of_pos_right (by positivity)]
        linarith

-- H_fix Step 6 (`Ψ` from summability of `1/|ρ|²`)
/-- **The squared reciprocal ordinates are summable**: `∑_k 1/ordSeq k² < ∞`. -/
theorem summable_inv_ordSeq_sq : Summable fun k => 1 / ordSeq k ^ 2 := by
  choose ρ hρ using fun k => (ordSeq_mem_posOrd k).2
  have hinj : Function.Injective ρ := fun i j hij =>
    strictMono_ordSeq_aux.injective (by rw [← hρ i, ← hρ j, hij])
  exact (summable_inv_abs_im_sq.comp_injective hinj).congr fun k => by
    simp only [Function.comp_apply, hρ k]

theorem isLeast_ordSeq_zero : IsLeast posOrd (ordSeq 0) := by
  have h := isLeast_posOrd_Ioi 0
  have he : posOrd ∩ Set.Ioi 0 = posOrd := Set.inter_eq_left.mpr fun t ht => ht.1
  rw [he] at h
  exact h

theorem isLeast_ordSeq_succ (k : ℕ) : IsLeast (posOrd ∩ Set.Ioi (ordSeq k)) (ordSeq (k + 1)) :=
  isLeast_posOrd_Ioi (ordSeq k)

theorem ordSeq_mem (k : ℕ) : ordSeq k ∈ posOrd := by
  cases k with
  | zero => exact isLeast_ordSeq_zero.1
  | succ k => exact (isLeast_ordSeq_succ k).1.1

theorem ordSeq_pos (k : ℕ) : 0 < ordSeq k := (ordSeq_mem k).1

theorem ordSeq_strictMono : StrictMono ordSeq :=
  strictMono_nat_of_lt_succ fun k => (isLeast_ordSeq_succ k).1.2

theorem ordSeq_sq_mono : Monotone fun k => ordSeq k ^ 2 := fun _ _ hij =>
  pow_le_pow_left₀ (ordSeq_pos _).le (ordSeq_strictMono.monotone hij) 2

/-- Every zero below `ordSeq k` sits at an earlier ordinate. -/
theorem exists_eq_ordSeq_of_lt (k : ℕ) (ρ : nonTrivialZeroSet) (h : |(ρ : ℂ).im| < ordSeq k) :
    ∃ j < k, |(ρ : ℂ).im| = ordSeq j := by
  have hmem : |(ρ : ℂ).im| ∈ posOrd :=
    ⟨lt_trans (by norm_num) (Cvs.StepA.StepACriterion.lt_abs_im ρ), ρ, rfl⟩
  induction k with
  | zero => exact absurd (isLeast_ordSeq_zero.2 hmem) (not_le.mpr h)
  | succ k ih =>
    rcases lt_trichotomy |(ρ : ℂ).im| (ordSeq k) with hlt | heq | hgt
    · obtain ⟨j, hj, hj'⟩ := ih hlt
      exact ⟨j, Nat.lt_succ_of_lt hj, hj'⟩
    · exact ⟨k, Nat.lt_succ_self k, heq⟩
    · exact absurd ((isLeast_ordSeq_succ k).2 ⟨hmem, hgt⟩) (not_le.mpr h)

/-- No zero lies below the first ordinate. -/
theorem ordSeq_zero_le_abs_im (ρ : nonTrivialZeroSet) : ordSeq 0 ≤ |(ρ : ℂ).im| := by
  by_contra h
  obtain ⟨j, hj, -⟩ := exists_eq_ordSeq_of_lt 0 ρ (not_le.mp h)
  exact Nat.not_lt_zero j hj

/-- The squared ordinates tend to infinity. -/
theorem tendsto_ordSeq_sq : Tendsto (fun k => ordSeq k ^ 2) atTop atTop := by
  have h0 : Tendsto (fun k => 1 / ordSeq k ^ 2) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨summable_inv_ordSeq_sq.tendsto_atTop_zero,
      Eventually.of_forall fun k => Set.mem_Ioi.mpr (by have := ordSeq_pos k; positivity)⟩
  refine (tendsto_inv_nhdsGT_zero.comp h0).congr fun k => ?_
  simp [one_div, inv_inv]

end Cvs.Finite.OddDisplacementPencil
