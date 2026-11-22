import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.FullTailConvergence
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.SlepianCommutingRelation
import Cvs.Prolate.SlepianSignRule
import Cvs.Upstream.PoissonSummationDini
import Cvs.Xi.EImageWindowPoisson

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The inversion law of a rung's window class

Poisson summation for the cosine transform at every `θ > 0` off the lattice `(2π/c)ℕ`, so inside the window too. For
an even angular eigenfunction with `ψ = μG` on `[−1, 1]` and `a = 2π/c`, the modes `mθ ≤ 1` sum to `(μ/θ)E_G(a/θ)`, so
`E_G(θ) + aG(0)/(2θ) − ½∫G = τ (√a/θ) E_G(a/θ) + Σ_{mθ>1} ψ(mθ)` with `τ = μ√(c/2π)`, and `τ_k = (−1)^k √λ_k`.
-/

noncomputable section

open Real Set Filter Topology MeasureTheory Cvs.L2a.AngularProlateTailPositive Cvs.L2a.FullTailConvergence

namespace Cvs.Prolate.RungWindowInversionLaw

variable {g g₁ g₂ : ℝ → ℝ} {c : ℝ}

theorem tendsto_partial_poissonPiece (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hc : 0 < c) {θ : ℝ} (hθ0 : 0 < θ) {k : ℕ} (hk : (k : ℝ) < c * θ / (2 * π))
    (hk' : c * θ / (2 * π) < k + 1) :
    Tendsto (fun M : ℕ => ∑ m ∈ Finset.Icc 1 M, psi c g (m * θ)) atTop (𝓝 (poissonPiece c g k θ)) := by
  have hcθ : 0 < c * θ := by positivity
  set θ' := c * θ / (2 * π) with hθ'
  have hθ'0 : 0 < θ' := by have := pi_pos; positivity
  have hI : uIcc (-1 : ℝ) 1 = Icc (-1) 1 := uIcc_of_le (by norm_num)
  have hgc : ContinuousOn g (Icc (-1) 1) := fun s hs =>
    (hg s (by rw [hI]; exact hs)).continuousAt.continuousWithinAt
  have hg₁c : ContinuousOn g₁ (Icc (-1) 1) := fun s hs =>
    (hg₁ s (by rw [hI]; exact hs)).continuousAt.continuousWithinAt
  set gt := (Icc (-1 : ℝ) 1).indicator g with hgt
  have hgti : Integrable gt := (integrable_indicator_iff measurableSet_Icc).2 hgc.integrableOn_Icc
  have hgtm : Measurable gt := by
    classical
    have := hgc.measurable_piecewise (g := 0) continuous_zero.continuousOn measurableSet_Icc
    rwa [piecewise_eq_indicator] at this
  have hsupp : ∀ s, 1 < |s| → gt s = 0 := fun s hs => indicator_of_notMem (fun h => by
    have := abs_le.mpr ⟨h.1, h.2⟩; linarith) _
  have hout : ∀ z, θ' < |z| → gt (z / θ') = 0 := fun z hz =>
    hsupp _ (by rw [abs_div, abs_of_pos hθ'0, one_lt_div hθ'0]; exact hz)
  have hin : ∀ z, |z| ≤ θ' → z / θ' ∈ Icc (-1 : ℝ) 1 := fun z hz => by
    have h := abs_le.mp hz
    refine ⟨?_, ?_⟩
    · rw [le_div_iff₀ hθ'0]; linarith
    · rw [div_le_iff₀ hθ'0]; linarith
  obtain ⟨Mg, hMg⟩ := isCompact_Icc.exists_bound_of_continuousOn hgc
  obtain ⟨Mg1, hMg1⟩ := isCompact_Icc.exists_bound_of_continuousOn hg₁c
  have hMg0 : 0 ≤ Mg := (norm_nonneg _).trans (hMg 0 ⟨by norm_num, by norm_num⟩)
  have hMg10 : 0 ≤ Mg1 := (norm_nonneg _).trans (hMg1 0 ⟨by norm_num, by norm_num⟩)
  have hgtb : ∀ s, |gt s| ≤ Mg := fun s => by
    by_cases h : s ∈ Icc (-1 : ℝ) 1
    · rw [hgt, indicator_of_mem h]; exact hMg s h
    · rw [hgt, indicator_of_notMem h, abs_zero]; exact hMg0
  have hlipg : ∀ u ∈ Icc (-1 : ℝ) 1, ∀ v ∈ Icc (-1 : ℝ) 1, |g u - g v| ≤ Mg1 * |u - v| :=
    fun u hu v hv => (convex_Icc (-1 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le (f := g) (f' := g₁)
      (fun x hx => (hg x (by rw [hI]; exact hx)).hasDerivWithinAt) (fun x hx => hMg1 x hx) hv hu
  have hN : θ' ≤ ((k + 1 : ℕ) : ℝ) := by push_cast; linarith
  have hB : ∀ y, |Cvs.Upstream.PoissonSummationDini.per gt θ' (k + 1) y| ≤ ((2 * (k + 1) + 1 : ℕ) : ℝ) * Mg := by
    intro y
    unfold Cvs.Upstream.PoissonSummationDini.per
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun j _ => hgtb _).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  set δ := min (1 / 2 : ℝ) (min ((θ' - k) / 2) ((k + 1 - θ') / 2)) with hδd
  have hδ : 0 < δ := lt_min (by norm_num) (lt_min (by linarith) (by linarith))
  have hδ2 : δ ≤ 1 / 2 := min_le_left _ _
  have hδa : δ ≤ (θ' - k) / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hδb : δ ≤ (k + 1 - θ') / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hterm : ∀ j ∈ Finset.range (2 * (k + 1) + 1), ∀ y, |y| ≤ δ →
      |gt (((j : ℝ) - ((k + 1 : ℕ) : ℝ) + y) / θ') - gt (((j : ℝ) - ((k + 1 : ℕ) : ℝ) + 0) / θ')|
        ≤ Mg1 / θ' * |y| := by
    intro j hj y hy
    have hj' : j < 2 * (k + 1) + 1 := Finset.mem_range.mp hj
    have hya := abs_le.mp hy
    have hrhs : 0 ≤ Mg1 / θ' * |y| := by positivity
    push_cast
    rcases (show j = 0 ∨ j = 2 * k + 2 ∨ (1 ≤ j ∧ j ≤ 2 * k + 1) by omega) with h | h | h
    · subst h
      rw [hout _ (lt_abs.mpr (Or.inr (by push_cast; linarith))),
        hout _ (lt_abs.mpr (Or.inr (by push_cast; linarith))), sub_zero, abs_zero]
      exact hrhs
    · subst h
      rw [hout _ (lt_abs.mpr (Or.inl (by push_cast; linarith))),
        hout _ (lt_abs.mpr (Or.inl (by push_cast; linarith))), sub_zero, abs_zero]
      exact hrhs
    · have h1 : (1 : ℝ) ≤ j := by exact_mod_cast h.1
      have h2 : (j : ℝ) ≤ 2 * k + 1 := by exact_mod_cast h.2
      have m1 := hin ((j : ℝ) - (k + 1) + y) (abs_le.mpr ⟨by linarith, by linarith⟩)
      have m0 := hin ((j : ℝ) - (k + 1) + 0) (abs_le.mpr ⟨by linarith, by linarith⟩)
      rw [hgt, indicator_of_mem m1, indicator_of_mem m0]
      refine (hlipg _ m1 _ m0).trans (le_of_eq ?_)
      rw [show ((j : ℝ) - (k + 1) + y) / θ' - ((j : ℝ) - (k + 1) + 0) / θ' = y / θ' by ring, abs_div,
        abs_of_pos hθ'0]
      ring
  have hlip : ∀ y, |y| ≤ δ → |Cvs.Upstream.PoissonSummationDini.per gt θ' (k + 1) y - Cvs.Upstream.PoissonSummationDini.per gt θ' (k + 1) 0|
      ≤ ((2 * (k + 1) + 1 : ℕ) : ℝ) * (Mg1 / θ') * |y| := by
    intro y hy
    unfold Cvs.Upstream.PoissonSummationDini.per
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun j hj => hterm j hj y hy).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    exact le_of_eq (by ring)
  have hP := Cvs.Upstream.PoissonSummationDini.poisson hgti hgtm hsupp hθ'0 hN hB hδ hδ2 hlip
  have hG : ∀ m : ℕ, Cvs.Upstream.PoissonSummationDini.G gt (m * θ') = psi c g (m * θ) := by
    intro m
    rw [hgt, G_indicator]
    unfold psi Cvs.Prolate.SlepianCommutingRelation.kint
    refine intervalIntegral.integral_congr fun s _ => ?_
    have hπ : (π : ℝ) ≠ 0 := pi_ne_zero
    have hθ0' : θ ≠ 0 := hθ0.ne'
    have hc0 : c ≠ 0 := hc.ne'
    have : 2 * π * ((m : ℝ) * θ') * s = c * ((m : ℝ) * θ) * s := by
      rw [hθ']; field_simp
    simp only [this]
  have hG0 : Cvs.Upstream.PoissonSummationDini.G gt 0 = ∫ s in (-1 : ℝ)..1, g s := by
    rw [hgt, G_indicator]; simp
  set P := ∑ j ∈ Finset.range (2 * (k + 1) + 1), gt (((j : ℝ) - ((k + 1 : ℕ) : ℝ)) / θ') with hPd
  have hlim : Tendsto (fun M : ℕ => ∑ m ∈ Finset.Icc 1 M, psi c g (m * θ)) atTop
      (𝓝 ((P - θ' * Cvs.Upstream.PoissonSummationDini.G gt 0) / (2 * θ'))) := by
    have := (hP.sub_const (θ' * Cvs.Upstream.PoissonSummationDini.G gt 0)).div_const (2 * θ')
    refine this.congr fun M => ?_
    simp only [hG]
    set S := ∑ m ∈ Finset.Icc 1 M, psi c g (m * θ)
    rw [show θ' * (Cvs.Upstream.PoissonSummationDini.G gt 0 + 2 * S) - θ' * Cvs.Upstream.PoissonSummationDini.G gt 0
      = (2 * θ') * S by ring]
    exact mul_div_cancel_left₀ S (by positivity)
  have hPeq : P = ∑ n ∈ Finset.Icc (-(k : ℤ)) k, g (2 * π * n / (c * θ)) := by
    rw [hPd, show 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ']
    rw [hout _ (lt_abs.mpr (Or.inr (by push_cast; linarith))),
      hout _ (lt_abs.mpr (Or.inl (by push_cast; linarith))), add_zero, add_zero]
    refine Finset.sum_nbij' (fun j => (j : ℤ) - k) (fun n => (n + k).toNat) ?_ ?_ ?_ ?_ ?_
    · intro j hj; simp only [Finset.mem_range] at hj; simp only [Finset.mem_Icc]; omega
    · intro n hn; simp only [Finset.mem_Icc] at hn; simp only [Finset.mem_range]; omega
    · intro j _; simp
    · intro n hn; simp only [Finset.mem_Icc] at hn; omega
    · intro j hj
      have hj' : (j : ℝ) ≤ 2 * k := by exact_mod_cast (show j ≤ 2 * k by simp at hj; omega)
      have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      have m := hin (((j + 1 : ℕ) : ℝ) - ((k + 1 : ℕ) : ℝ)) (abs_le.mpr ⟨by push_cast; linarith,
        by push_cast; linarith⟩)
      rw [hgt, indicator_of_mem m]
      congr 1
      push_cast
      rw [hθ']
      field_simp
      ring
  have hval : poissonPiece c g k θ = (P - θ' * Cvs.Upstream.PoissonSummationDini.G gt 0) / (2 * θ') := by
    rw [hPeq, hG0, poissonPiece, hθ']
    field_simp
  rw [hval]
  exact hlim

/-- `E_G(a/θ) = θ Σ_{1 ≤ n ≤ 1/θ} G(nθ)`. -/
theorem eimage_inv {a θ : ℝ} (ha : 0 < a) (hθ : 0 < θ) (G : ℝ → ℝ) :
    Cvs.Xi.EImageWindowPoisson.eimage a G (a / θ) = θ * ∑ n ∈ Finset.Icc 1 ⌊1 / θ⌋₊, G (n * θ) := by
  unfold Cvs.Xi.EImageWindowPoisson.eimage
  have h1 : a / (a / θ) = θ := by field_simp
  have h2 : a / θ / a = 1 / θ := by field_simp
  rw [h1, h2]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  congr 1; field_simp

/-- **The inversion law**: for an even `C²` profile with `ψ = psi c G = μG` on `[−1, 1]`, `a = 2π/c`, and `θ > 0` off
the lattice `aℕ`, the tail sums `Σ_{m ≤ M, mθ > 1} ψ(mθ)` tend to `E_G(θ) + aG(0)/(2θ) − ½∫G − (μ/θ)E_G(a/θ)`. -/
theorem tendsto_tail_inversion {G G₁ G₂ : ℝ → ℝ} {c θ μ : ℝ} (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G (G₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G₁ (G₂ s) s) (heven : ∀ s ∈ Icc (-1 : ℝ) 1, G (-s) = G s)
    (hc : 0 < c) (hθ : 0 < θ) (hlat : ∀ k : ℕ, θ ≠ k * (2 * π / c))
    (hμ : ∀ s ∈ Icc (-1 : ℝ) 1, psi c G s = μ * G s) :
    Tendsto (fun M : ℕ => ∑ m ∈ (Finset.Icc 1 M).filter (fun m : ℕ => 1 < m * θ), psi c G (m * θ)) atTop
      (𝓝 (Cvs.Xi.EImageWindowPoisson.eimage (2 * π / c) G θ + 2 * π / c * G 0 / (2 * θ)
        - 1 / 2 * (∫ s in (-1 : ℝ)..1, G s) - μ / θ * Cvs.Xi.EImageWindowPoisson.eimage (2 * π / c) G (2 * π / c / θ))) := by
  have hpi := pi_pos
  have ha : 0 < 2 * π / c := by positivity
  set k := ⌊c * θ / (2 * π)⌋₊ with hkd
  have hx : 0 ≤ c * θ / (2 * π) := by positivity
  have hk1 : (k : ℝ) ≤ c * θ / (2 * π) := Nat.floor_le hx
  have hk2 : c * θ / (2 * π) < k + 1 := Nat.lt_floor_add_one _
  have hk : (k : ℝ) < c * θ / (2 * π) := by
    refine lt_of_le_of_ne hk1 fun h => hlat k ?_
    field_simp at h ⊢
    linarith
  have hP := tendsto_partial_poissonPiece hg hg₁ hc hθ hk hk2
  rw [Cvs.Xi.EImageWindowPoisson.poissonPiece_eq_eimage heven hc hθ hk hk2] at hP
  set K := ⌊1 / θ⌋₊ with hKd
  have hhead : ∑ m ∈ Finset.Icc 1 K, psi c G (m * θ)
      = μ / θ * Cvs.Xi.EImageWindowPoisson.eimage (2 * π / c) G (2 * π / c / θ) := by
    rw [eimage_inv ha hθ, ← mul_assoc, div_mul_cancel₀ μ hθ.ne', Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.1 hm).1
    have hmK : (m : ℝ) ≤ 1 / θ := (Nat.cast_le.2 (Finset.mem_Icc.1 hm).2).trans (Nat.floor_le (by positivity))
    have hmθ : (m : ℝ) * θ ≤ 1 := by rwa [le_div_iff₀ hθ] at hmK
    exact hμ _ ⟨by nlinarith, hmθ⟩
  have hsplit : ∀ M : ℕ, K ≤ M → ∑ m ∈ (Finset.Icc 1 M).filter (fun m : ℕ => 1 < m * θ), psi c G (m * θ)
      = ∑ m ∈ Finset.Icc 1 M, psi c G (m * θ) - ∑ m ∈ Finset.Icc 1 K, psi c G (m * θ) := by
    intro M hM
    have hf : (Finset.Icc 1 M).filter (fun m : ℕ => ¬ 1 < m * θ) = Finset.Icc 1 K := by
      ext m
      simp only [Finset.mem_filter, Finset.mem_Icc, not_lt]
      constructor
      · rintro ⟨⟨h1, -⟩, h2⟩
        refine ⟨h1, Nat.le_floor ?_⟩
        rwa [le_div_iff₀ hθ]
      · rintro ⟨h1, h2⟩
        have hmK : (m : ℝ) ≤ 1 / θ := (Nat.cast_le.2 h2).trans (Nat.floor_le (by positivity))
        exact ⟨⟨h1, h2.trans hM⟩, by rwa [le_div_iff₀ hθ] at hmK⟩
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 M) (fun m : ℕ => 1 < m * θ), hf]
    ring
  rw [← hhead]
  have hEv : (fun M : ℕ => ∑ m ∈ Finset.Icc 1 M, psi c G (m * θ) - ∑ m ∈ Finset.Icc 1 K, psi c G (m * θ))
      =ᶠ[atTop] fun M : ℕ => ∑ m ∈ (Finset.Icc 1 M).filter (fun m : ℕ => 1 < m * θ), psi c G (m * θ) := by
    filter_upwards [eventually_ge_atTop K] with M hM
    rw [hsplit M hM]
  exact (hP.sub_const (∑ m ∈ Finset.Icc 1 K, psi c G (m * θ))).congr' hEv

/-- `muR c k = (−1)^k √λ_k √(2π/c)`: the eigenvalue is its concentration root with Slepian's sign. -/
theorem muR_eq_sign_sqrt {c : ℝ} {k : ℕ} (hc : 0 < c) (h : ∃ χ, Cvs.Prolate.EvenRungsByIndex.IsLevelIdx c k χ) :
    Cvs.Prolate.EvenRungsByIndex.muR c k
      = (-1 : ℝ) ^ k * √(Cvs.Prolate.EvenRungsByIndex.lamR c k) * √(2 * π / c) := by
  have hpos := Cvs.Prolate.SlepianSignRule.neg_one_pow_mul_muR_pos hc h
  set μ := Cvs.Prolate.EvenRungsByIndex.muR c k
  have hq : 0 < c / (2 * π) := by have := pi_pos; positivity
  have hl : √(Cvs.Prolate.EvenRungsByIndex.lamR c k) = |μ| * √(c / (2 * π)) := by
    unfold Cvs.Prolate.EvenRungsByIndex.lamR
    rw [Real.sqrt_sq_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hone : √(c / (2 * π)) * √(2 * π / c) = 1 := by
    rw [← Real.sqrt_mul hq.le, show c / (2 * π) * (2 * π / c) = 1 by field_simp, Real.sqrt_one]
  rw [hl, mul_assoc, mul_assoc, hone, mul_one]
  rcases Nat.even_or_odd k with he | ho
  · rw [he.neg_one_pow, one_mul] at hpos ⊢; rw [abs_of_pos hpos]
  · rw [ho.neg_one_pow, neg_one_mul, neg_pos] at hpos; rw [ho.neg_one_pow, abs_of_neg hpos]; ring

/-- **The inversion law of the rung of index `k`** (prolate `h_{2k}`): with `a = 2π/c` and `θ > 0` off `aℕ`, the
tail sums `Σ_{m ≤ M, mθ > 1} ψ(mθ)` tend to `E(θ) + aG(0)/(2θ) − ½∫G − (−1)^k √λ_k (√a/θ) E(a/θ)`, `G = rung c k`. -/
theorem tendsto_tail_inversion_rung {c θ : ℝ} {k : ℕ} (hc : 0 < c)
    (h : ∃ χ, Cvs.Prolate.EvenRungsByIndex.IsLevelIdx c k χ) (hθ : 0 < θ) (hlat : ∀ j : ℕ, θ ≠ j * (2 * π / c)) :
    Tendsto (fun M : ℕ => ∑ m ∈ (Finset.Icc 1 M).filter (fun m : ℕ => 1 < m * θ),
        psi c (Cvs.Prolate.EvenRungsByIndex.rung c k) (m * θ)) atTop
      (𝓝 (Cvs.Xi.EImageWindowPoisson.eimage (2 * π / c) (Cvs.Prolate.EvenRungsByIndex.rung c k) θ
        + 2 * π / c * Cvs.Prolate.EvenRungsByIndex.rung c k 0 / (2 * θ)
        - 1 / 2 * (∫ s in (-1 : ℝ)..1, Cvs.Prolate.EvenRungsByIndex.rung c k s)
        - (-1 : ℝ) ^ k * √(Cvs.Prolate.EvenRungsByIndex.lamR c k)
          * (√(2 * π / c) / θ * Cvs.Xi.EImageWindowPoisson.eimage (2 * π / c) (Cvs.Prolate.EvenRungsByIndex.rung c k)
            (2 * π / c / θ)))) := by
  obtain ⟨hg, hg₁, -, -, heven, -⟩ := Cvs.Prolate.EvenRungsByIndex.rung_spec h
  have := tendsto_tail_inversion hg hg₁ heven hc hθ hlat (Cvs.Prolate.EvenRungsByIndex.psi_rung h)
  rw [muR_eq_sign_sqrt hc h] at this
  convert this using 3
  ring

end Cvs.Prolate.RungWindowInversionLaw
