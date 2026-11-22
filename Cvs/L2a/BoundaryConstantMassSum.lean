import Mathlib
import Cvs.L2a.TreeBoundFirstPairBoundary

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The boundary constant at `b` against the mass sum

With `|ψ_i(ξ)| ≤ K_i/ξ` and `|u_i(ξ)| ≤ K_i'ξ` on `ξ ≥ 1` (Cvs.Prolate.RungDecayBeyondEdge), `P_ψ(ξ) ≤ (Σ|a_i|K_i)/ξ`, `P_u(ξ) ≤ (Σ|a_i|K_i')ξ`,
so the boundary constant of Cvs.L2a.TreeBoundFirstPairBoundary obeys `B_c ≤ (Σ|a_i|K_i)(Σ|a_i|K_i')(κ₁ᴿ m₂² + κ₂ᴿ/m₂)` with `R` cancelled, and by
Cauchy–Schwarz `Σ|a_i|K_i ≤ √(N₀ Σ K_i²/M_i)`: `B_c ≤ N₀ √(Q_ψ Q_u)(κ₁ᴿ m₂² + κ₂ᴿ/m₂)` with `Q_f = Σ K_i²/M_i`.
-/

namespace Cvs.L2a.BoundaryConstantMassSum

open Real Set Finset Cvs.L2a.TreeBoundFirstPairBoundary

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **Cauchy–Schwarz against the masses**: `(Σ|a_i|K_i)² ≤ (Σ a_i²M_i)(Σ K_i²/M_i)` for `M_i > 0`. -/
theorem sum_abs_mul_sq_le {a K Mm : ι → ℝ} (hM : ∀ i, 0 < Mm i) :
    (∑ i, |a i| * K i) ^ 2 ≤ (∑ i, a i ^ 2 * Mm i) * ∑ i, K i ^ 2 / Mm i := by
  have e : ∀ i, |a i| * K i = (|a i| * √(Mm i)) * (K i / √(Mm i)) := fun i => by
    have := (hM i).ne'
    have hs : √(Mm i) ≠ 0 := (Real.sqrt_pos.mpr (hM i)).ne'
    field_simp
  have e2 : ∀ i, (|a i| * √(Mm i)) ^ 2 = a i ^ 2 * Mm i := fun i => by
    rw [mul_pow, sq_abs, Real.sq_sqrt (hM i).le]
  have e3 : ∀ i, (K i / √(Mm i)) ^ 2 = K i ^ 2 / Mm i := fun i => by
    rw [div_pow, Real.sq_sqrt (hM i).le]
  simp_rw [e]
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => |a i| * √(Mm i)) (fun i => K i / √(Mm i))
  simp_rw [e2, e3] at h
  exact h

theorem Pabs_le_div {a : ι → ℝ} {f : ι → ℝ → ℝ} {K : ι → ℝ} {ξ : ℝ}
    (hf : ∀ i, |f i ξ| ≤ K i / ξ) : Pabs a f ξ ≤ (∑ i, |a i| * K i) / ξ := by
  unfold Pabs
  rw [Finset.sum_div]
  apply Finset.sum_le_sum; intro i _
  rw [mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (hf i) (abs_nonneg _)

theorem Pabs_le_mul {a : ι → ℝ} {f : ι → ℝ → ℝ} {K : ι → ℝ} {ξ : ℝ}
    (hf : ∀ i, |f i ξ| ≤ K i * ξ) : Pabs a f ξ ≤ (∑ i, |a i| * K i) * ξ := by
  unfold Pabs
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum; intro i _
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (hf i) (abs_nonneg _)

/-- **The boundary constant with `R` cancelled**. -/
theorem Bc_le {a : ι → ℝ} {ψ u : ι → ℝ → ℝ} {Kψ Ku : ι → ℝ} {m₂ R κ₁R κ₂R : ℝ} (hm : 1 ≤ m₂) (hR : 1 ≤ R)
    (hκ₁ : 0 ≤ κ₁R) (hκ₂ : 0 ≤ κ₂R)
    (hψ : ∀ i, ∀ ξ, 1 ≤ ξ → |ψ i ξ| ≤ Kψ i / ξ) (hu : ∀ i, ∀ ξ, 1 ≤ ξ → |u i ξ| ≤ Ku i * ξ) :
    Bc a ψ u m₂ R κ₁R κ₂R ≤ (∑ i, |a i| * Kψ i) * (∑ i, |a i| * Ku i) * (κ₁R * m₂ ^ 2 + κ₂R / m₂) := by
  unfold Bc
  have hR0 : 0 < R := by linarith
  have hm0 : 0 < m₂ := by linarith
  have hmR : 1 ≤ m₂ * R := by nlinarith
  have hmR0 : 0 < m₂ * R := by linarith
  have h1 := Pabs_le_div (a := a) (fun i => hψ i R hR)
  have h2 := Pabs_le_mul (a := a) (fun i => hu i (m₂ * R) hmR)
  have h3 := Pabs_le_mul (a := a) (fun i => hu i R hR)
  have h4 := Pabs_le_div (a := a) (fun i => hψ i (m₂ * R) hmR)
  have hP1 := Pabs_nonneg a ψ R; have hP2 := Pabs_nonneg a u (m₂ * R)
  have hP3 := Pabs_nonneg a u R; have hP4 := Pabs_nonneg a ψ (m₂ * R)
  set Sψ := ∑ i, |a i| * Kψ i with hSψ
  set Su := ∑ i, |a i| * Ku i with hSu
  have hSψ0 : 0 ≤ Sψ := Finset.sum_nonneg fun i _ => by
    have := (abs_nonneg (ψ i R)).trans (hψ i R hR)
    rw [le_div_iff₀ hR0, zero_mul] at this
    exact mul_nonneg (abs_nonneg _) this
  have hSu0 : 0 ≤ Su := Finset.sum_nonneg fun i _ => by
    have := (abs_nonneg (u i R)).trans (hu i R hR)
    exact mul_nonneg (abs_nonneg _) ((mul_nonneg_iff_of_pos_right hR0).mp this)
  calc κ₁R * Pabs a ψ R * (m₂ * Pabs a u (m₂ * R)) + κ₂R * Pabs a u R * Pabs a ψ (m₂ * R)
      ≤ κ₁R * (Sψ / R) * (m₂ * (Su * (m₂ * R))) + κ₂R * (Su * R) * (Sψ / (m₂ * R)) := by gcongr
    _ = Sψ * Su * (κ₁R * m₂ ^ 2 + κ₂R / m₂) := by field_simp

/-- **The boundary constant against the mass sum**: `B_c ≤ N₀ √(Q_ψ Q_u)(κ₁ᴿm₂² + κ₂ᴿ/m₂)`, `Q_f = Σ K_i²/M_i`. -/
theorem Bc_le_N0 {a : ι → ℝ} {ψ u : ι → ℝ → ℝ} {Kψ Ku Mm : ι → ℝ} {m₂ R κ₁R κ₂R : ℝ} (hm : 1 ≤ m₂) (hR : 1 ≤ R)
    (hκ₁ : 0 ≤ κ₁R) (hκ₂ : 0 ≤ κ₂R) (hM : ∀ i, 0 < Mm i)
    (hψ : ∀ i, ∀ ξ, 1 ≤ ξ → |ψ i ξ| ≤ Kψ i / ξ) (hu : ∀ i, ∀ ξ, 1 ≤ ξ → |u i ξ| ≤ Ku i * ξ) :
    Bc a ψ u m₂ R κ₁R κ₂R
      ≤ (∑ i, a i ^ 2 * Mm i) * √((∑ i, Kψ i ^ 2 / Mm i) * ∑ i, Ku i ^ 2 / Mm i) * (κ₁R * m₂ ^ 2 + κ₂R / m₂) := by
  have h := Bc_le (a := a) hm hR hκ₁ hκ₂ hψ hu
  have hN0 : 0 ≤ ∑ i, a i ^ 2 * Mm i := Finset.sum_nonneg fun i _ => by nlinarith [sq_nonneg (a i), (hM i).le]
  have hQψ : 0 ≤ ∑ i, Kψ i ^ 2 / Mm i := Finset.sum_nonneg fun i _ => div_nonneg (sq_nonneg _) (hM i).le
  have hQu : 0 ≤ ∑ i, Ku i ^ 2 / Mm i := Finset.sum_nonneg fun i _ => div_nonneg (sq_nonneg _) (hM i).le
  have c1 := sum_abs_mul_sq_le (a := a) (K := Kψ) hM
  have c2 := sum_abs_mul_sq_le (a := a) (K := Ku) hM
  have hSψ0 : 0 ≤ ∑ i, |a i| * Kψ i := Finset.sum_nonneg fun i _ => by
    have := (abs_nonneg (ψ i 1)).trans (hψ i 1 le_rfl)
    exact mul_nonneg (abs_nonneg _) (by simpa using this)
  have hSu0 : 0 ≤ ∑ i, |a i| * Ku i := Finset.sum_nonneg fun i _ => by
    have := (abs_nonneg (u i 1)).trans (hu i 1 le_rfl)
    exact mul_nonneg (abs_nonneg _) (by simpa using this)
  have hprod : (∑ i, |a i| * Kψ i) * (∑ i, |a i| * Ku i)
      ≤ (∑ i, a i ^ 2 * Mm i) * √((∑ i, Kψ i ^ 2 / Mm i) * ∑ i, Ku i ^ 2 / Mm i) := by
    have hsq : ((∑ i, |a i| * Kψ i) * (∑ i, |a i| * Ku i)) ^ 2
        ≤ ((∑ i, a i ^ 2 * Mm i) * √((∑ i, Kψ i ^ 2 / Mm i) * ∑ i, Ku i ^ 2 / Mm i)) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (mul_nonneg hQψ hQu)]
      calc (∑ i, |a i| * Kψ i) ^ 2 * (∑ i, |a i| * Ku i) ^ 2
          ≤ ((∑ i, a i ^ 2 * Mm i) * ∑ i, Kψ i ^ 2 / Mm i) * ((∑ i, a i ^ 2 * Mm i) * ∑ i, Ku i ^ 2 / Mm i) :=
            mul_le_mul c1 c2 (sq_nonneg _) (by positivity)
        _ = _ := by ring
    exact (pow_le_pow_iff_left₀ (mul_nonneg hSψ0 hSu0) (by positivity) two_ne_zero).mp hsq
  calc _ ≤ _ := h
    _ ≤ _ := mul_le_mul_of_nonneg_right hprod (by positivity)

end Cvs.L2a.BoundaryConstantMassSum
