import Mathlib
import Cvs.L2a.FarMassPlateau
import Cvs.L2a.FrameConstantFirstModeAngle
import Cvs.L2a.PlateauAssemblyTrivialGain
import Cvs.L2a.ResonantConstantClosedForm
import Cvs.L2a.RungSpanFromPlateau
import Cvs.L2a.TailEdgeFarSplit
import Cvs.L2a.TailOfModes
import Cvs.L2a.TrivialGainsCrossConstants

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The plateau from the edge–far angle, and the prime constant in closed form

An edge–far angle `|⟨F_e, F_f⟩| ≤ δ‖F_e‖‖F_f‖` gives `|⟨F_e, F_f⟩| ≤ δ/(2(1 − δ))·∫F²`, so the plateau's `r` is
`δ/(1 − 2δ)`. With low gains `1 − δ_n ≥ 1 − δ` and plateau gains `≥ gH_n`, L2a's prime constant over any set of prime
powers is at most `2R + 2√(log 2·(1 + ρ₁)R) + ρ`, `R` the closed resonant form of Cvs.L2a.ResonantConstantClosedForm.
-/

namespace Cvs.L2a.EdgeFarAnglePlateau

open Real Finset MeasureTheory ArithmeticFunction Cvs.L2a.TailOfModes Cvs.L2a.FarMassPlateau Cvs.L2a.TailEdgeFarSplit Cvs.L2a.RungSpanFromPlateau Cvs.L2a.PlateauAssemblyTrivialGain Cvs.L2a.ResonantConstantClosedForm Cvs.L2a.TrivialGainsCrossConstants Cvs.L2a.FrameConstantFirstModeAngle

/-- The resonant constant in closed form. -/
noncomputable def resConst (δ g ε₃ : ℝ) (M k₀ : ℕ) : ℝ :=
  (1 / (1 - δ)) * ∑ n ∈ (Icc 1 M).filter (· < k₀), Real.log n / n
    + (1 / g) * ∑ n ∈ (Icc 1 M).filter (k₀ ≤ ·), 1 / (n : ℝ)
    + ε₃ * ∑ n ∈ Icc 1 M, Real.log n / n

/-- The prime constant in closed form. -/
noncomputable def primeConst (δ g ε₃ ρ₁ ρ : ℝ) (M k₀ : ℕ) : ℝ :=
  2 * resConst δ g ε₃ M k₀ + 2 * √(Real.log 2 * (1 + ρ₁) * resConst δ g ε₃ M k₀) + ρ

/-- The plateau gain from an edge–far angle `δ` and a far defect `ε`. -/
noncomputable def plateauGain (δ ε : ℝ) : ℝ := (1 - δ / (1 - 2 * δ)) * (1 - ε)

/-- **An angle bounds the pairing by the whole norm**: `|X| ≤ δ/(2(1 − δ))·(P + Q + 2X)`. -/
theorem corr_le_of_angle {P Q X δ N : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hδ0 : 0 ≤ δ) (hδ : δ < 1)
    (hX : |X| ≤ δ * √(P * Q)) (hN : N = P + Q + 2 * X) : |X| ≤ δ / (2 * (1 - δ)) * N := by
  have hsum := sum_le_of_angle hP hQ hδ0 hδ hX
  have hsq : √(P * Q) ≤ (P + Q) / 2 := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [sq_nonneg (P - Q)]
  have h1 : 0 < 1 - δ := by linarith
  calc |X| ≤ δ * ((P + Q) / 2) := le_trans hX (mul_le_mul_of_nonneg_left hsq hδ0)
    _ ≤ δ * (N / (1 - δ) / 2) := by
        rw [hN]; gcongr
    _ = δ / (2 * (1 - δ)) * N := by field_simp

/-- **The edge–far pairing against the tail norm** from the edge–far angle. -/
theorem edge_far_le_of_angle (Φ : ℝ → ℝ) (M : ℕ) {b δ : ℝ} (k : ℕ) (hb : 1 ≤ b)
    (hcont : ContinuousOn Φ (Set.Icc 1 (M * b))) (hδ0 : 0 ≤ δ) (hδ : δ < 1)
    (hang : |∫ θ in Set.Ioi 1, edgeF Φ M b k θ * farF Φ M b k θ|
      ≤ δ * √((∫ θ in Set.Ioi 1, edgeF Φ M b k θ ^ 2) * ∫ θ in Set.Ioi 1, farF Φ M b k θ ^ 2)) :
    |∫ θ in Set.Ioi 1, edgeF Φ M b k θ * farF Φ M b k θ|
      ≤ δ / (2 * (1 - δ)) * ∫ θ in Set.Ioi 1, tailF Φ M b θ ^ 2 := by
  have hFe := integrableOn_edgeF_sq Φ M k hb hcont
  have hFf := integrableOn_farF_sq Φ M k hb hcont
  have hFef := integrableOn_edgeF_mul_farF Φ M k hb hcont
  refine corr_le_of_angle (setIntegral_nonneg measurableSet_Ioi fun θ _ => sq_nonneg _)
    (setIntegral_nonneg measurableSet_Ioi fun θ _ => sq_nonneg _) hδ0 hδ hang ?_
  have e : (fun θ => tailF Φ M b θ ^ 2)
      = fun θ => edgeF Φ M b k θ ^ 2 + farF Φ M b k θ ^ 2 + 2 * (edgeF Φ M b k θ * farF Φ M b k θ) := by
    funext θ; rw [tailF_eq_edge_add_far Φ M b k θ]; ring
  have h12 : ∫ θ in Set.Ioi 1, (edgeF Φ M b k θ ^ 2 + farF Φ M b k θ ^ 2)
      = (∫ θ in Set.Ioi 1, edgeF Φ M b k θ ^ 2) + ∫ θ in Set.Ioi 1, farF Φ M b k θ ^ 2 := integral_add hFe hFf
  have h123 : ∫ θ in Set.Ioi 1, (edgeF Φ M b k θ ^ 2 + farF Φ M b k θ ^ 2
        + 2 * (edgeF Φ M b k θ * farF Φ M b k θ))
      = (∫ θ in Set.Ioi 1, (edgeF Φ M b k θ ^ 2 + farF Φ M b k θ ^ 2))
        + ∫ θ in Set.Ioi 1, 2 * (edgeF Φ M b k θ * farF Φ M b k θ) :=
    integral_add (hFe.add hFf) (hFef.const_mul 2)
  rw [e, h123, h12, integral_const_mul]

/-- The plateau constant of an edge–far angle `δ < 1/3` is below `1/4`. -/
theorem cef_lt {δ : ℝ} (hδ : δ < 1 / 3) : δ / (2 * (1 - δ)) < 1 / 4 := by
  rw [div_lt_iff₀ (by linarith)]; linarith

/-- The plateau constant's `r` is `δ/(1 − 2δ)`. -/
theorem cef_r {δ : ℝ} (hδ : δ < 1 / 3) :
    2 * (δ / (2 * (1 - δ))) / (1 - 2 * (δ / (2 * (1 - δ)))) = δ / (1 - 2 * δ) := by
  have h1 : 1 - δ ≠ 0 := by intro h; linarith
  have h2 : 1 - 2 * δ ≠ 0 := by intro h; linarith
  have h3 : 1 - 2 * (δ / (2 * (1 - δ))) ≠ 0 := by
    rw [show 1 - 2 * (δ / (2 * (1 - δ))) = (1 - 2 * δ) / (1 - δ) by field_simp; ring]
    exact div_ne_zero h2 h1
  rw [div_eq_div_iff h3 h2]
  field_simp
  ring

/-- **The low gains**: `δ_1 ≤ σ/(1 + σ)` from `S₁ ≤ σT₁`, and `δ_j ≤ C̄/(1 + C̄)` from `C_j ≤ C̄`. -/
theorem deltaSeq_le {S₁ T₁ σ Cb : ℝ} (C : ℕ → ℝ) {k₀ : ℕ} (hS0 : 0 ≤ S₁) (hT : 0 < T₁) (hσ : 0 ≤ σ)
    (hS : S₁ ≤ σ * T₁) (hC0 : ∀ j, 0 ≤ C j) (hCb : ∀ j, 2 ≤ j → j < k₀ → C j ≤ Cb) :
    ∀ n, 1 ≤ n → n < k₀ → deltaSeq S₁ T₁ C n ≤ max (σ / (1 + σ)) (Cb / (1 + Cb)) := by
  intro n hn hnk
  unfold deltaSeq
  split_ifs with h1
  · refine le_max_of_le_left ?_
    have e : 1 - T₁ / (S₁ + T₁) = S₁ / (S₁ + T₁) := by field_simp; ring
    rw [e, div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  · refine le_max_of_le_right ?_
    have hC := hCb n (by omega) hnk
    have := hC0 n
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith

/-- `τ_k ≥ 0` for positive gains. -/
theorem tauG_nonneg {γ : ℕ → ℝ} {ε₃ : ℝ} {M k : ℕ} (hk : 1 ≤ k) (hγ : ∀ n ∈ Icc 1 M, 0 < γ n) (hε₃ : 0 ≤ ε₃) :
    0 ≤ tauG γ ε₃ M k := by
  unfold tauG
  refine Finset.sum_nonneg fun m' hm' => ?_
  rw [mem_filter, mem_Icc] at hm'
  have hn : k * m' ∈ Icc 1 M := mem_Icc.mpr ⟨by nlinarith [hm'.1.1], hm'.2⟩
  have hm'0 : (0 : ℝ) ≤ 1 / (m' : ℝ) := by positivity
  exact mul_nonneg hm'0 (add_nonneg (one_div_pos.mpr (hγ _ hn)).le hε₃)

/-- **Any set of indices is dominated by `[1, M]`**: the resonant terms vanish outside it. -/
theorem sum_le_Icc (S : Finset ℕ) {γ : ℕ → ℝ} {ε₃ : ℝ} {M : ℕ} (hγ : ∀ n ∈ Icc 1 M, 0 < γ n) (hε₃ : 0 ≤ ε₃) :
    ∑ k ∈ S, Λ k * tauG γ ε₃ M k / k ≤ ∑ k ∈ Icc 1 M, Λ k * tauG γ ε₃ M k / k := by
  have hz : ∀ k ∈ S, Λ k * tauG γ ε₃ M k / k ≠ 0 → k ∈ Icc 1 M := by
    intro k _ hk
    by_contra hn
    apply hk
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · subst h0; simp
    · have hkM : M < k := by rw [mem_Icc] at hn; omega
      have : tauG γ ε₃ M k = 0 := by
        unfold tauG
        refine Finset.sum_eq_zero fun m' hm' => ?_
        rw [mem_filter, mem_Icc] at hm'
        exfalso
        nlinarith [hm'.1.1, hm'.2]
      rw [this]; simp
  rw [← Finset.sum_filter_of_ne hz]
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun k hk => (mem_filter.mp hk).2) fun k hk _ => ?_
  have hk1 := (mem_Icc.mp hk).1
  have := tauG_nonneg hk1 hγ hε₃
  have := vonMangoldt_nonneg (n := k)
  positivity

/-- **L2a's prime constant in closed form**, over any set `S` of indices. -/
theorem prime_le_primeConst (S : Finset ℕ) {γ : ℕ → ℝ} {δ g ε₃ ρ₁ ρ : ℝ} {M k₀ : ℕ} (hδ : δ < 1) (hg : 0 < g)
    (hε₃ : 0 ≤ ε₃) (hρ₁ : 0 ≤ ρ₁)
    (hlow : ∀ n ∈ Icc 1 M, n < k₀ → 1 - δ ≤ γ n) (hhigh : ∀ n ∈ Icc 1 M, k₀ ≤ n → g * harm n ≤ γ n) :
    ∑ k ∈ S, 2 * Λ k * tauG γ ε₃ M k / k + (2 * Λ 2 * √((1 + ρ₁) * tauG γ ε₃ M 2 / 2) + ρ)
      ≤ primeConst δ g ε₃ ρ₁ ρ M k₀ := by
  have hγ : ∀ n ∈ Icc 1 M, 0 < γ n := fun n hn => by
    by_cases h : n < k₀
    · linarith [hlow n hn h]
    · have := harm_pos (mem_Icc.mp hn).1
      have := hhigh n hn (not_lt.mp h)
      nlinarith
  have hR : ∑ k ∈ Icc 1 M, Λ k * tauG γ ε₃ M k / k ≤ resConst δ g ε₃ M k₀ := resonant_le hδ hg hlow hhigh
  have hS := sum_le_Icc S hγ hε₃
  have h2 := sum_le_Icc {2} hγ hε₃
  rw [Finset.sum_singleton] at h2
  have hS2 : ∑ k ∈ S, 2 * Λ k * tauG γ ε₃ M k / k = 2 * ∑ k ∈ S, Λ k * tauG γ ε₃ M k / k := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
  have hL : Λ 2 = Real.log 2 := by rw [vonMangoldt_apply_prime Nat.prime_two]; norm_num
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hsq : Λ 2 * √((1 + ρ₁) * tauG γ ε₃ M 2 / 2)
      ≤ √(Real.log 2 * (1 + ρ₁) * resConst δ g ε₃ M k₀) := by
    have e : Λ 2 * √((1 + ρ₁) * tauG γ ε₃ M 2 / 2)
        = √(Real.log 2 * (1 + ρ₁) * (Λ 2 * tauG γ ε₃ M 2 / (2 : ℕ))) := by
      rw [hL, show Real.log 2 * (1 + ρ₁) * (Real.log 2 * tauG γ ε₃ M 2 / ((2 : ℕ) : ℝ))
          = Real.log 2 ^ 2 * ((1 + ρ₁) * tauG γ ε₃ M 2 / 2) by push_cast; ring,
        Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hlog2]
    rw [e]
    exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (h2.trans hR) (by positivity))
  unfold primeConst
  rw [hS2]
  nlinarith

/-- **The low gains of L2a** from `δ_n ≤ δ`. -/
theorem gainP_low {k₀ M : ℕ} {rs ws εs δs : ℕ → ℝ} {δ : ℝ} (hδs : ∀ n, 1 ≤ n → n < k₀ → δs n ≤ δ) :
    ∀ n ∈ Icc 1 M, n < k₀ → 1 - δ ≤ gainP k₀ rs ws εs δs n := fun n hn h => by
  unfold gainP; rw [if_neg (not_le.mpr h)]; linarith [hδs n (mem_Icc.mp hn).1 h]

/-- **The plateau gains of L2a** from `r_j w_j ≤ r` and `ε_j ≤ ε`. -/
theorem gainP_high {k₀ M : ℕ} {rs ws εs δs : ℕ → ℝ} {r ε : ℝ} (hr : r ≤ 1) (hε : ε ≤ 1)
    (hrs : ∀ n, rs n * ws n ≤ r) (hεs : ∀ n, εs n ≤ ε) :
    ∀ n ∈ Icc 1 M, k₀ ≤ n → (1 - r) * (1 - ε) * harm n ≤ gainP k₀ rs ws εs δs n := fun n hn h => by
  unfold gainP; rw [if_pos h]
  have hH := (harm_pos (mem_Icc.mp hn).1).le
  have h1 : (1 - r) * (1 - ε) ≤ (1 - rs n * ws n) * (1 - εs n) :=
    mul_le_mul (by linarith [hrs n]) (by linarith [hεs n]) (by linarith) (by linarith [hrs n])
  exact mul_le_mul_of_nonneg_right h1 hH

/-- **The coefficient of L2a above the floor's threshold**:
`F − (F − a₀)η′ − Π′ − q ≥ c₂` once `η′ ≤ η < 1`, `Π′ ≤ Π`, and `F ≥ max((Π + q + c₂ − a₀η)/(1 − η), a₀)`. -/
theorem coeff_ge {F a₀ η' η Pc Pb q c₂ : ℝ} (hη' : η' ≤ η) (hη : η < 1) (hFa : a₀ ≤ F) (hP : Pc ≤ Pb)
    (hF : (Pb + q + c₂ - a₀ * η) / (1 - η) ≤ F) : c₂ ≤ F - (F - a₀) * η' - Pc - q := by
  rw [div_le_iff₀ (by linarith)] at hF
  nlinarith [mul_le_mul_of_nonneg_left hη' (sub_nonneg.mpr hFa)]

end Cvs.L2a.EdgeFarAnglePlateau
