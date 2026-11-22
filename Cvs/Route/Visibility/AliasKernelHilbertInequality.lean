import Mathlib
import Cvs.Route.Visibility.AliasPairThetaKernel
import Cvs.Upstream.HilbertInequalityUniformGap

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Hilbert's inequality for the leading alias kernel `k/(Λ_k − Λ_l)`

With `λ_k = √Λ_k` (`1/3`-separated), `k/(Λ_k − Λ_l) = (k/(2λ_k))(1/(λ_k − λ_l) + 1/(λ_k + λ_l))`; Cvs.Upstream.HilbertInequalityUniformGap bounds the
difference kernel and, on `ι ⊕ ι` with frequencies `±λ`, the Hankel kernel, so
`|Σ_{k≠l} a_kkU_kH_l/(Λ_k − Λ_l)| ≤ 3π(s²(ω²/4)ΣU² + ΣH²/s²) + (ω/12)Σ|U||H|` for `|a_k| ≤ ω`.
-/

noncomputable section

namespace Cvs.Route.Visibility.AliasKernelHilbertInequality
open Cvs.ZeroCounting

open Real Finset
open Cvs.Route.Visibility.AliasPairThetaKernel (bet Lam lamF lamF_mem lamF_gap div_Lam_sub_eq)

section Hankel

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **Hilbert's inequality for a Hankel kernel**: `|Σ x_rz_t/(λ_r + λ_t)| ≤ (π/2)(s²Σx² + Σz²/s²)/D` when the
`λ` are `D`-separated and `λ_r + λ_t ≥ D`. -/
theorem hankel_real {freq : ι → ℝ} {D : ℝ} (hD : 0 < D) (hgap : ∀ r t, r ≠ t → D ≤ |freq r - freq t|)
    (hpos : ∀ r t, D ≤ freq r + freq t) (x z : ι → ℝ) {s : ℝ} (hs : 0 < s) :
    |∑ r, ∑ t, x r * z t / (freq r + freq t)| ≤ π / 2 * (s ^ 2 * ∑ r, x r ^ 2 + (∑ r, z r ^ 2) / s ^ 2) / D := by
  let f : ι ⊕ ι → ℝ := Sum.elim freq (fun i => -freq i)
  let X : ι ⊕ ι → ℝ := Sum.elim x (fun _ => 0)
  let Z : ι ⊕ ι → ℝ := Sum.elim (fun _ => 0) z
  have hg : ∀ r t : ι ⊕ ι, r ≠ t → D ≤ |f r - f t| := by
    intro r t hrt
    cases r with
    | inl i =>
      cases t with
      | inl j => exact hgap i j fun h => hrt (congrArg Sum.inl h)
      | inr j =>
        simp only [f, Sum.elim_inl, Sum.elim_inr, sub_neg_eq_add]
        exact (hpos i j).trans (le_abs_self _)
    | inr i =>
      cases t with
      | inl j =>
        simp only [f, Sum.elim_inl, Sum.elim_inr]
        rw [show -freq i - freq j = -(freq j + freq i) by ring, abs_neg]
        exact (hpos j i).trans (le_abs_self _)
      | inr j =>
        simp only [f, Sum.elim_inr]
        rw [show -freq i - -freq j = -(freq i - freq j) by ring, abs_neg]
        exact hgap i j fun h => hrt (congrArg Sum.inr h)
  have h := Cvs.Upstream.HilbertInequalityUniformGap.hilbert_real_bilinear (freq := f) (D := D) hD hg X Z hs
  simpa [f, X, Z, Fintype.sum_sum_type, sub_neg_eq_add] using h

end Hankel

/-- **Hilbert's inequality for the alias kernel**: with `λ_k = √Λ_k`,
`|Σ_{k≠l} a_kkU_kH_l/(Λ_k − Λ_l)| ≤ 3π(s²(ω²/4)ΣU_k² + ΣH_k²/s²) + (ω/12)Σ|U_k||H_k|` for `|a_k| ≤ ω`. -/
theorem hilbert_alias_le (K : ℕ) {θ : ℝ} (hθ : 12 / 25 ≤ θ) {ω : ℝ} (a U H : ℕ → ℝ) (hω : 0 ≤ ω)
    (ha : ∀ k ∈ Icc 3 K, |a k| ≤ ω) {s : ℝ} (hs : 0 < s) :
    |∑ k ∈ Icc 3 K, ∑ l ∈ Icc 3 K, (if k = l then 0 else a k * k * U k * H l / (Lam k θ - Lam l θ))|
      ≤ 3 * π * (s ^ 2 * (ω ^ 2 / 4 * ∑ k ∈ Icc 3 K, U k ^ 2) + (∑ k ∈ Icc 3 K, H k ^ 2) / s ^ 2)
        + ω / 12 * ∑ k ∈ Icc 3 K, |U k| * |H k| := by
  set S := Icc 3 K
  set x : ℕ → ℝ := fun k => a k * U k * (k / (2 * lamF k θ)) with hx
  have hmem : ∀ k ∈ S, 3 ≤ k := fun k hk => (Finset.mem_Icc.mp hk).1
  have hlam : ∀ k ∈ S, (k : ℝ) ≤ lamF k θ ∧ lamF k θ ≤ k + 1 := fun k hk => lamF_mem (hmem k hk) hθ
  have hlam3 : ∀ k ∈ S, 3 ≤ lamF k θ := fun k hk => by
    have := (hlam k hk).1; have : (3 : ℝ) ≤ k := by exact_mod_cast hmem k hk
    linarith
  -- the partial fractions
  have hterm : ∀ k ∈ S, ∀ l ∈ S, (if k = l then 0 else a k * k * U k * H l / (Lam k θ - Lam l θ))
      = (if k = l then 0 else x k * H l / (lamF k θ - lamF l θ)) + (x k * H l / (lamF k θ + lamF l θ))
        - (if k = l then x k * H k / (2 * lamF k θ) else 0) := by
    intro k hk l hl
    by_cases hkl : k = l
    · subst hkl; rw [if_pos rfl, if_pos rfl, if_pos rfl, ← two_mul]; ring
    · simp only [if_neg hkl]
      rw [mul_assoc (a k * k), mul_div_assoc, div_eq_mul_one_div (U k * H l),
        show a k * k * (U k * H l * (1 / (Lam k θ - Lam l θ))) = a k * U k * H l * ((k : ℝ) / (Lam k θ - Lam l θ))
          by ring, div_Lam_sub_eq (hmem k hk) (hmem l hl) hkl hθ]
      simp only [hx]; ring
  rw [Finset.sum_congr rfl fun k hk => Finset.sum_congr rfl fun l hl => hterm k hk l hl]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  -- move to the subtype
  have hsub : ∀ f : ℕ → ℕ → ℝ, ∑ k ∈ S, ∑ l ∈ S, f k l = ∑ k : S, ∑ l : S, f k l := by
    intro f; rw [← Finset.sum_coe_sort]; exact Finset.sum_congr rfl fun k _ => (Finset.sum_coe_sort _ _).symm
  have hgap : ∀ r t : S, r ≠ t → (1 / 3 : ℝ) ≤ |lamF r θ - lamF t θ| := by
    intro r t hrt
    have hne : (r : ℕ) ≠ t := fun h => hrt (Subtype.ext h)
    rcases lt_or_gt_of_ne hne with h | h
    · have := lamF_gap (hmem r r.2) h hθ
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]; linarith
    · have := lamF_gap (hmem t t.2) h hθ
      rw [abs_of_nonneg (by linarith)]; linarith
  have hpos : ∀ r t : S, (1 / 3 : ℝ) ≤ lamF r θ + lamF t θ := fun r t => by
    have := hlam3 r r.2; have := hlam3 t t.2; linarith
  have h1 := Cvs.Upstream.HilbertInequalityUniformGap.hilbert_real_bilinear (ι := S) (freq := fun k => lamF k θ) (D := 1 / 3) (by norm_num) hgap
    (fun k => x k) (fun k => H k) hs
  have h2 := hankel_real (ι := S) (freq := fun k => lamF k θ) (D := 1 / 3) (by norm_num) hgap hpos
    (fun k => x k) (fun k => H k) hs
  have hx2 : ∑ k : S, x k ^ 2 ≤ ω ^ 2 / 4 * ∑ k ∈ S, U k ^ 2 := by
    rw [Finset.sum_coe_sort S (fun k => x k ^ 2), Finset.mul_sum]
    refine Finset.sum_le_sum fun k hk => ?_
    have hl := hlam k hk
    have hk0 : (0 : ℝ) < k := by have : (3 : ℝ) ≤ k := by exact_mod_cast hmem k hk
                                 linarith
    have hr : |(k : ℝ) / (2 * lamF k θ)| ≤ 1 / 2 := by
      rw [abs_of_nonneg (div_nonneg (Nat.cast_nonneg k) (by linarith)), div_le_div_iff₀ (by linarith) (by norm_num)]
      linarith
    simp only [hx]
    rw [show (a k * U k * (k / (2 * lamF k θ))) ^ 2 = (a k * (k / (2 * lamF k θ))) ^ 2 * U k ^ 2 by ring]
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    rw [← sq_abs, abs_mul]
    have : |a k| * |(k : ℝ) / (2 * lamF k θ)| ≤ ω * (1 / 2) := mul_le_mul (ha k hk) hr (abs_nonneg _) hω
    calc (|a k| * |(k : ℝ) / (2 * lamF k θ)|) ^ 2 ≤ (ω * (1 / 2)) ^ 2 := pow_le_pow_left₀ (by positivity) this 2
      _ = ω ^ 2 / 4 := by ring
  have hH : ∑ k : S, H k ^ 2 = ∑ k ∈ S, H k ^ 2 := Finset.sum_coe_sort S (fun k => H k ^ 2)
  have hdiag : |∑ k ∈ S, ∑ l ∈ S, (if k = l then x k * H k / (2 * lamF k θ) else 0)|
      ≤ ω / 12 * ∑ k ∈ S, |U k| * |H k| := by
    have e : ∑ k ∈ S, ∑ l ∈ S, (if k = l then x k * H k / (2 * lamF k θ) else 0)
        = ∑ k ∈ S, x k * H k / (2 * lamF k θ) :=
      Finset.sum_congr rfl fun k hk => by rw [Finset.sum_ite_eq]; exact if_pos hk
    rw [e, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k hk => ?_)
    have hl := hlam k hk
    have h3 := hlam3 k hk
    have hk0 : (0 : ℝ) < k := by have : (3 : ℝ) ≤ k := by exact_mod_cast hmem k hk
                                 linarith
    simp only [hx]
    rw [abs_div, abs_mul, abs_mul, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < 2 * lamF k θ),
      abs_div, abs_of_pos hk0, abs_of_pos (by linarith : (0 : ℝ) < 2 * lamF k θ)]
    have hr : (k : ℝ) / (2 * lamF k θ) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
    have hr' : 1 / (2 * lamF k θ) ≤ 1 / 6 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
    calc |a k| * |U k| * ((k : ℝ) / (2 * lamF k θ)) * |H k| / (2 * lamF k θ)
        = |a k| * ((k : ℝ) / (2 * lamF k θ)) * (1 / (2 * lamF k θ)) * (|U k| * |H k|) := by ring
      _ ≤ ω * (1 / 2) * (1 / 6) * (|U k| * |H k|) := by
          have h1 : |a k| * ((k : ℝ) / (2 * lamF k θ)) ≤ ω * (1 / 2) :=
            mul_le_mul (ha k hk) hr (div_nonneg (Nat.cast_nonneg k) (by linarith)) hω
          have h2 : |a k| * ((k : ℝ) / (2 * lamF k θ)) * (1 / (2 * lamF k θ)) ≤ ω * (1 / 2) * (1 / 6) :=
            mul_le_mul h1 hr' (div_nonneg zero_le_one (by linarith)) (by positivity)
          exact mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = ω / 12 * (|U k| * |H k|) := by ring
  have eH : ∑ k ∈ S, ∑ l ∈ S, (if k = l then 0 else x k * H l / (lamF k θ - lamF l θ))
      = ∑ r : S, ∑ t : S, (if r = t then 0 else x r * H t / (lamF r θ - lamF t θ)) := by
    rw [hsub]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun t _ => ?_
    by_cases h : r = t
    · rw [if_pos h, if_pos (congrArg Subtype.val h)]
    · rw [if_neg h, if_neg fun h' => h (Subtype.ext h')]
  have eK : ∑ k ∈ S, ∑ l ∈ S, x k * H l / (lamF k θ + lamF l θ)
      = ∑ r : S, ∑ t : S, x r * H t / (lamF r θ + lamF t θ) := hsub _
  rw [eH, eK]
  set A1 := ∑ r : S, ∑ t : S, (if r = t then 0 else x r * H t / (lamF r θ - lamF t θ))
  set A2 := ∑ r : S, ∑ t : S, x r * H t / (lamF r θ + lamF t θ)
  set A3 := ∑ k ∈ S, ∑ l ∈ S, (if k = l then x k * H k / (2 * lamF k θ) else 0)
  have hsum0 : 0 ≤ s ^ 2 * ∑ k : S, x k ^ 2 + (∑ k : S, H k ^ 2) / s ^ 2 := by positivity
  have hb : π / 2 * (s ^ 2 * ∑ k : S, x k ^ 2 + (∑ k : S, H k ^ 2) / s ^ 2) / (1 / 3)
      ≤ 3 / 2 * π * (s ^ 2 * (ω ^ 2 / 4 * ∑ k ∈ S, U k ^ 2) + (∑ k ∈ S, H k ^ 2) / s ^ 2) := by
    rw [← hH]
    have : s ^ 2 * ∑ k : S, x k ^ 2 ≤ s ^ 2 * (ω ^ 2 / 4 * ∑ k ∈ S, U k ^ 2) :=
      mul_le_mul_of_nonneg_left hx2 (by positivity)
    have hπ := Real.pi_pos
    rw [div_div_eq_mul_div, div_one]
    nlinarith
  calc |A1 + A2 - A3| ≤ |A1| + |A2| + |A3| := by
        refine (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ 3 / 2 * π * (s ^ 2 * (ω ^ 2 / 4 * ∑ k ∈ S, U k ^ 2) + (∑ k ∈ S, H k ^ 2) / s ^ 2)
        + 3 / 2 * π * (s ^ 2 * (ω ^ 2 / 4 * ∑ k ∈ S, U k ^ 2) + (∑ k ∈ S, H k ^ 2) / s ^ 2)
        + ω / 12 * ∑ k ∈ S, |U k| * |H k| := add_le_add (add_le_add (h1.trans hb) (h2.trans hb)) hdiag
    _ = _ := by ring

end Cvs.Route.Visibility.AliasKernelHilbertInequality
