import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.MirrorSplitDefect
import Cvs.Prolate.RungExactOrthogonality
import Cvs.Prolate.RungMirrorIdentity

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The exact AM–GM charge of a subfamily's `e₁` defect

With `q(τ) = (1 − τ)/(2(1 + τ))`, `(1 − τ)² = 2q(1 − τ²)`, so for `Kψᵢ = −τᵢψᵢ`, `K` a contraction, and any finite `S`:
`|re⟨Σ_S aᵢ(1 − τᵢ)ψᵢ, G⟩| ≤ √Q_S √B_S`, `Q_S = Σ_S q a²M = ½P_S − Σ_S τ/(1 + τ) a²M`, `B_S = 2Σ_S (1 − τ²)⟨ψ, G⟩²/M`.
On the rung span `1 − τᵢ² = Mᵢ/Nᵢ` (Cvs.Prolate.RungMirrorIdentity, `N = ∫₀^∞ ψ²`), so `B_S = 2Σ_S ⟨ψ, G⟩²/N ≤ 2∫_{Ioi 1} G²`.
-/

noncomputable section

open MeasureTheory Set Real Cvs.L2a.AngularProlateTailPositive Cvs.L2a.MirrorSplitDefect

namespace Cvs.L2a.SubfamilyDefectCharge

/-! ### The per-rung weight -/

/-- The per-rung weight `q(τ) = (1 − τ)/(2(1 + τ))`. -/
def qOf (τ : ℝ) : ℝ := (1 - τ) / (2 * (1 + τ))

/-- `q(τ) = 1/(1 + τ) − ½`. -/
theorem qOf_eq_inv {τ : ℝ} (h : τ ≠ -1) : qOf τ = 1 / (1 + τ) - 1 / 2 := by
  have h1 : 1 + τ ≠ 0 := fun h' => h (by linarith)
  unfold qOf
  field_simp
  ring

/-- `q(τ) ≥ 0` on `(−1, 1]`. -/
theorem qOf_nonneg {τ : ℝ} (h1 : -1 < τ) (h2 : τ ≤ 1) : 0 ≤ qOf τ :=
  div_nonneg (by linarith) (by linarith)

/-- **Per rung**: `(1 − τ)² = 2q(τ)(1 − τ²)`. -/
theorem one_sub_sq_eq {τ : ℝ} (h : τ ≠ -1) : (1 - τ) ^ 2 = 2 * qOf τ * (1 - τ ^ 2) := by
  have h1 : 1 + τ ≠ 0 := fun h' => h (by linarith)
  unfold qOf
  field_simp
  ring

/-- **The Landau weight**: `τ ≥ 0` and `τ² ≥ ½` give `q(τ) ≤ (3 − 2√2)/2`. -/
theorem qOf_le_landau {τ : ℝ} (h0 : 0 ≤ τ) (hl : 1 / 2 ≤ τ ^ 2) : qOf τ ≤ (3 - 2 * √2) / 2 := by
  have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hs0 := Real.sqrt_nonneg 2
  have hτ : √2 / 2 ≤ τ := by nlinarith
  have hs2 : √2 < 2 := by nlinarith
  rw [qOf_eq_inv (by linarith)]
  have h1 : 1 / (1 + τ) ≤ 2 - √2 := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  linarith

/-! ### The scalar lemma -/

section Scalar

variable {ι : Type*}

/-- **Cauchy–Schwarz through a factorisation**: `fᵢ = xᵢyᵢ` on `S` gives `|Σ_S f| ≤ √(Σ_S x²) √(Σ_S y²)`. -/
theorem abs_sum_le_of_eq_mul (S : Finset ι) {f x y : ι → ℝ} (h : ∀ i ∈ S, f i = x i * y i) :
    |∑ i ∈ S, f i| ≤ √(∑ i ∈ S, x i ^ 2) * √(∑ i ∈ S, y i ^ 2) := by
  rw [Finset.sum_congr rfl h, ← Real.sqrt_mul (Finset.sum_nonneg fun i _ => sq_nonneg (x i))]
  exact Real.abs_le_sqrt (Finset.sum_mul_sq_le_sq_mul_sq S x y)

/-- `√(2q(τ)(1 − τ²)) = 1 − τ` on `(−1, 1]`. -/
theorem sqrt_two_q_mul {τ : ℝ} (h1 : -1 < τ) (h2 : τ ≤ 1) :
    √2 * √(qOf τ) * √(1 - τ ^ 2) = 1 - τ := by
  have hq := qOf_nonneg h1 h2
  rw [← Real.sqrt_mul (by norm_num), ← Real.sqrt_mul (by positivity), ← one_sub_sq_eq (by linarith),
    Real.sqrt_sq (by linarith)]

/-- **L1, mass form**: for `τᵢ ∈ (−1, 1]` and `Mᵢ > 0` on `S`,
`|Σ_S aᵢ(1 − τᵢ)gᵢ| ≤ √(Σ_S q(τᵢ)aᵢ²Mᵢ) √(2Σ_S (1 − τᵢ²)gᵢ²/Mᵢ)`. -/
theorem abs_sum_eone_le (S : Finset ι) (a τ g M : ι → ℝ) (hM : ∀ i ∈ S, 0 < M i)
    (hτ : ∀ i ∈ S, -1 < τ i ∧ τ i ≤ 1) :
    |∑ i ∈ S, a i * (1 - τ i) * g i|
      ≤ √(∑ i ∈ S, qOf (τ i) * a i ^ 2 * M i) * √(2 * ∑ i ∈ S, (1 - τ i ^ 2) * g i ^ 2 / M i) := by
  have h := abs_sum_le_of_eq_mul S (f := fun i => a i * (1 - τ i) * g i)
    (x := fun i => a i * √(qOf (τ i)) * √(M i))
    (y := fun i => √2 * √(1 - τ i ^ 2) * g i / √(M i)) fun i hi => by
      have hm := Real.sqrt_pos.2 (hM i hi)
      have e := sqrt_two_q_mul (hτ i hi).1 (hτ i hi).2
      field_simp
      rw [← e]
      ring
  have ex : ∀ i ∈ S, (a i * √(qOf (τ i)) * √(M i)) ^ 2 = qOf (τ i) * a i ^ 2 * M i := fun i hi => by
    rw [mul_pow, mul_pow, Real.sq_sqrt (qOf_nonneg (hτ i hi).1 (hτ i hi).2), Real.sq_sqrt (hM i hi).le]
    ring
  have ey : ∀ i ∈ S, (√2 * √(1 - τ i ^ 2) * g i / √(M i)) ^ 2 = 2 * ((1 - τ i ^ 2) * g i ^ 2 / M i) :=
    fun i hi => by
      have h1 : 0 ≤ 1 - τ i ^ 2 := by nlinarith [(hτ i hi).1, (hτ i hi).2]
      rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt h1,
        Real.sq_sqrt (hM i hi).le]
      ring
  rw [Finset.sum_congr rfl ex, Finset.sum_congr rfl ey, ← Finset.mul_sum] at h
  exact h

/-- **The coupling reduction**: with `q(τᵢ) ≤ q'` and `gᵢ² ≤ κᵢMᵢP` on `S`,
`|Σ_S aᵢ(1 − τᵢ)gᵢ| ≤ √(2q'Σ_S (1 − τᵢ²)κᵢ) √(Σ_S aᵢ²Mᵢ) √P`. -/
theorem abs_sum_eone_le_coupling (S : Finset ι) (a τ g M κ : ι → ℝ) {P q' : ℝ} (hP : 0 ≤ P) (hq' : 0 ≤ q')
    (hM : ∀ i ∈ S, 0 < M i) (hτ : ∀ i ∈ S, -1 < τ i ∧ τ i ≤ 1) (hq : ∀ i ∈ S, qOf (τ i) ≤ q')
    (hκ : ∀ i ∈ S, g i ^ 2 ≤ κ i * M i * P) :
    |∑ i ∈ S, a i * (1 - τ i) * g i|
      ≤ √(2 * q' * ∑ i ∈ S, (1 - τ i ^ 2) * κ i) * √(∑ i ∈ S, a i ^ 2 * M i) * √P := by
  have h := abs_sum_eone_le S a τ g M hM hτ
  set A := ∑ i ∈ S, a i ^ 2 * M i
  set B := ∑ i ∈ S, (1 - τ i ^ 2) * κ i
  have hA : 0 ≤ A := Finset.sum_nonneg fun i hi => mul_nonneg (sq_nonneg _) (hM i hi).le
  have hQ : ∑ i ∈ S, qOf (τ i) * a i ^ 2 * M i ≤ q' * A := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    have h0 : 0 ≤ a i ^ 2 * M i := mul_nonneg (sq_nonneg _) (hM i hi).le
    nlinarith [hq i hi]
  have hBle : ∑ i ∈ S, (1 - τ i ^ 2) * g i ^ 2 / M i ≤ B * P := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i hi => ?_
    have h1 : 0 ≤ 1 - τ i ^ 2 := by nlinarith [(hτ i hi).1, (hτ i hi).2]
    rw [div_le_iff₀ (hM i hi)]
    have := mul_le_mul_of_nonneg_left (hκ i hi) h1
    linarith
  have h1 : √(∑ i ∈ S, qOf (τ i) * a i ^ 2 * M i) ≤ √(q' * A) := Real.sqrt_le_sqrt hQ
  have h2 : √(2 * ∑ i ∈ S, (1 - τ i ^ 2) * g i ^ 2 / M i) ≤ √(2 * (B * P)) :=
    Real.sqrt_le_sqrt (by linarith)
  have h3 := (h.trans (mul_le_mul h1 h2 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))
  refine h3.trans (le_of_eq ?_)
  rcases le_or_gt 0 B with hB | hB
  · rw [Real.sqrt_mul hq', Real.sqrt_mul (by norm_num), Real.sqrt_mul hB, Real.sqrt_mul (by positivity),
      Real.sqrt_mul (by norm_num)]
    ring
  · have hBP : 2 * (B * P) ≤ 0 := by nlinarith
    have hBq : 2 * q' * B ≤ 0 := by nlinarith
    rw [Real.sqrt_eq_zero'.2 hBP, Real.sqrt_eq_zero'.2 hBq]
    ring

end Scalar

/-! ### L1 for a contraction -/

section Abstract

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {ι : Type*}

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

end Abstract

/-! ### The span instance -/

section Span

local notation "μ₁" => (volume.restrict (Ioi (1 : ℝ)))

variable {ι : Type*} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ μ : ι → ℝ}

/-- **The `e₁` charge as rung pairings**: for `G ∈ L²(1, ∞)`,
`∫_{Ioi 1} re e₁ · G = Σ aᵢ(1 − τᵢ) ∫_{Ioi 1} ψᵢG`, with `e₁ = eOne c Φ` and `τᵢ = μᵢ√(c/2π)`. -/
theorem integral_eOne_re_mul (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 0 < c) (heven : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, g i (-s) = g i s)
    (hμ : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, psi c (g i) s = μ i * g i s) {G : ℝ → ℝ} (hG : MemLp G 2 μ₁) :
    ∫ x in Ioi 1, (eOne c (fun ξ => ∑ i, a i * psi c (g i) ξ) x).re * G x
      = ∑ i, a i * (1 - μ i * √(c / (2 * π))) * ∫ x in Ioi 1, psi c (g i) x * G x := by
  have hgc : ∀ i, ContinuousOn (g i) (Icc (-1 : ℝ) 1) := fun i s hs =>
    (hg i s (by rwa [uIcc_of_le (by norm_num)])).continuousAt.continuousWithinAt
  have hI : ∀ i, Integrable (fun x => psi c (g i) x * G x) μ₁ := fun i =>
    (Cvs.Prolate.RungExactOrthogonality.memLp_psi (hg i) (hg₁ i) (hg₂c i) (hang i) hc).integrable_mul hG
  calc ∫ x in Ioi 1, (eOne c (fun ξ => ∑ i, a i * psi c (g i) ξ) x).re * G x
      = ∫ x in Ioi 1, ∑ i, a i * (1 - μ i * √(c / (2 * π))) * (psi c (g i) x * G x) := by
        refine integral_congr_ae ?_
        filter_upwards [eOne_high a hc hgc heven hμ] with x hx
        rw [hx, Complex.ofReal_re, Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ = ∑ i, a i * (1 - μ i * √(c / (2 * π))) * ∫ x in Ioi 1, psi c (g i) x * G x := by
        rw [integral_finsetSum _ fun i _ => (hI i).const_mul _]
        exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _

omit [Fintype ι] in
/-- **The coupling reduction on the span with Landau's weight**: for `τᵢ ≥ 0`, `λᵢ = τᵢ² ≥ ½`, `Mᵢ > 0` and
`(∫_{Ioi 1} ψᵢG)² ≤ κᵢMᵢP` on `S`, the band charge is at most `√(2q'Σ_S (1 − λᵢ)κᵢ) √(Σ_S aᵢ²Mᵢ) √P`,
`q' = (3 − 2√2)/2`. -/
theorem eone_coupling_landau_span (a : ι → ℝ) (S : Finset ι)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hc : 0 < c) (heven : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, g i (-s) = g i s)
    (hμ : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, psi c (g i) s = μ i * g i s)
    (hg0 : ∀ i ∈ S, ∃ s ∈ Icc (-1 : ℝ) 1, g i s ≠ 0) (hM : ∀ i ∈ S, 0 < ∫ ξ in Ioi 1, psi c (g i) ξ ^ 2)
    (hτ0 : ∀ i ∈ S, 0 ≤ μ i * √(c / (2 * π))) (hland : ∀ i ∈ S, 1 / 2 ≤ (μ i * √(c / (2 * π))) ^ 2)
    (G : ℝ → ℝ) (κ : ι → ℝ) {P : ℝ} (hP : 0 ≤ P)
    (hκ : ∀ i ∈ S, (∫ x in Ioi 1, psi c (g i) x * G x) ^ 2 ≤ κ i * (∫ ξ in Ioi 1, psi c (g i) ξ ^ 2) * P) :
    |∑ i ∈ S, a i * (1 - μ i * √(c / (2 * π))) * ∫ x in Ioi 1, psi c (g i) x * G x|
      ≤ √(2 * ((3 - 2 * √2) / 2) * ∑ i ∈ S, (1 - (μ i * √(c / (2 * π))) ^ 2) * κ i)
        * √(∑ i ∈ S, a i ^ 2 * ∫ ξ in Ioi 1, psi c (g i) ξ ^ 2) * √P := by
  have hgc : ∀ i, ContinuousOn (g i) (Icc (-1 : ℝ) 1) := fun i s hs =>
    (hg i s (by rwa [uIcc_of_le (by norm_num)])).continuousAt.continuousWithinAt
  have hq' : 0 ≤ (3 - 2 * √2) / 2 := by
    have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    nlinarith [Real.sqrt_nonneg 2]
  exact abs_sum_eone_le_coupling S a (fun i => μ i * √(c / (2 * π)))
    (fun i => ∫ x in Ioi 1, psi c (g i) x * G x) (fun i => ∫ ξ in Ioi 1, psi c (g i) ξ ^ 2) κ hP hq' hM
    (fun i hi => ⟨by linarith [hτ0 i hi], (abs_le.1 (Cvs.Prolate.RungMirrorIdentity.abs_tau_le_one hc (hgc i)
      (heven i) (hμ i) (hg0 i hi))).2⟩)
    (fun i hi => qOf_le_landau (hτ0 i hi) (hland i hi)) hκ

end Span

end Cvs.L2a.SubfamilyDefectCharge
