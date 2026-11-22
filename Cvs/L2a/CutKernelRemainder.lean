import Mathlib
import Cvs.L2a.FarFarBound
import Cvs.L2a.FarIntegrationByParts
import Cvs.L2a.QIdentityComplexWeight
import Cvs.L2a.QIdentityIterated
import Cvs.L2a.SigmaSquareMultiplier
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The remainder bound: CK (iii)

`|Γ_bot| + |R_top| + |𝒞_a| ≤ γ(c; δ₀, s₀, J)·P` with `γ = BN3 + BN2 + BF + TN3 + TN2 + D + 2E₁ + E_V + T2`, a sum of
closed forms in `c, δ₀, s₀, J` free of `M`, and `γ → 0` as `c → ∞` at `J = c/4 + 1`.
-/

noncomputable section

namespace Cvs.L2a.CutKernelRemainder

open Real Set Filter Topology MeasureTheory
open Cvs.L2a.AngularProlateTailPositive Cvs.L2a.FarIntegrationByParts

variable {ι : Type} [Fintype ι]

/-! ### The zeta values -/

/-- The real zeta series `ζ(s) = Σ_{n ≥ 1} n^{−s}`. -/
def zR (s : ℝ) : ℝ := ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ s

/-- `ζ(s) ≤ s/(s − 1)` by the integral test, for the values not in closed form. -/
theorem zR_le {s : ℝ} (hs : 1 < s) : zR s ≤ s / (s - 1) := by
  have hs0 : 0 < s := by linarith
  have hpos : ∀ n : ℕ, 0 ≤ 1 / ((n : ℝ) + 1) ^ s := fun n => by positivity
  refine Real.tsum_le_of_sum_range_le hpos fun n => ?_
  rcases n with _ | n
  · simp only [Finset.range_zero, Finset.sum_empty]
    exact div_nonneg hs0.le (by linarith)
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero, zero_add, Real.one_rpow, div_one]
  set f : ℝ → ℝ := fun x => (x ^ s)⁻¹ with hf
  have hanti : AntitoneOn f (Icc 1 (1 + n)) := by
    intro x hx y hy hxy
    simp only [hf]
    exact inv_anti₀ (Real.rpow_pos_of_pos (by linarith [hx.1]) s)
      (Real.rpow_le_rpow (by linarith [hx.1]) hxy hs0.le)
  have hsum := hanti.sum_le_integral
  have hint : ∫ x in (1 : ℝ)..1 + n, f x = (1 - (1 + (n : ℝ)) ^ (-s + 1)) / (s - 1) := by
    have : ∀ x ∈ uIcc (1 : ℝ) (1 + n), f x = x ^ (-s) := fun x hx => by
      have hx1 : 1 ≤ x := by
        rcases le_total 1 (1 + (n : ℝ)) with h | h
        · rw [uIcc_of_le h] at hx; exact hx.1
        · rw [uIcc_of_ge h] at hx; linarith [hx.1, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      simp only [hf]; rw [Real.rpow_neg (by linarith)]
    rw [intervalIntegral.integral_congr this, integral_rpow (Or.inr ⟨by linarith, ?_⟩)]
    · rw [Real.one_rpow]
      have h1 : -s + 1 ≠ 0 := by linarith
      have h2 : s - 1 ≠ 0 := by linarith
      rw [div_eq_div_iff h1 h2]
      ring
    · rw [uIcc_of_le (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])]
      intro h; linarith [h.1]
  rw [hint] at hsum
  have hle : ∑ i ∈ Finset.range n, 1 / ((((i + 1 : ℕ) : ℝ)) + 1) ^ s ≤ 1 / (s - 1) := by
    have e : ∑ i ∈ Finset.range n, 1 / ((((i + 1 : ℕ) : ℝ)) + 1) ^ s
        = ∑ i ∈ Finset.range n, f (1 + ((i + 1 : ℕ) : ℝ)) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hf, one_div]; ring_nf
    rw [e]
    refine hsum.trans ?_
    have : 0 ≤ (1 + (n : ℝ)) ^ (-s + 1) := Real.rpow_nonneg (by positivity) _
    rw [div_le_div_iff_of_pos_right (by linarith)]
    linarith
  have : s / (s - 1) = 1 + 1 / (s - 1) := by
    have h2 : s - 1 ≠ 0 := by linarith
    field_simp
    ring
  rw [this]
  push_cast at hle ⊢
  linarith

/-! ### The four series over `m ≥ 3` -/

/-! ### Atom majorants -/

/-- **Far side** (`χ₀ = c²`, `x ≥ 1`, `y ≥ 1`): the three atom profiles over `|Q_{c²}| ≥ c²(x² − 1)(y² − 1)`. -/
theorem pr_le_far {w w₁ w₂ : ℝ → ℂ} {c y x : ℝ} (hc : 0 < c) (hx : 1 < x) (hy : 1 < y) :
    Cvs.L2a.SigmaSquareMultiplier.pr₁ w₁ w₂ c (c ^ 2) y x
        ≤ ((2 * x + 2 * (c * y) * (x ^ 2 - 1)) * ‖w₁ x‖ + (x ^ 2 - 1) * ‖w₂ x‖) / (c ^ 2 * ((x ^ 2 - 1) * (y ^ 2 - 1)))
      ∧ Cvs.L2a.SigmaSquareMultiplier.pr₂ w w₁ c (c ^ 2) y x
        ≤ (((2 * x + 2 * (c * y) * (x ^ 2 - 1)) * (2 * c ^ 2 * x * (y ^ 2 - 1) + 2 * c * y)
              + (x ^ 2 - 1) * (2 * c ^ 2 * (y ^ 2 - 1))) * ‖w x‖
            + 2 * (x ^ 2 - 1) * (2 * c ^ 2 * x * (y ^ 2 - 1) + 2 * c * y) * ‖w₁ x‖)
          / (c ^ 2 * ((x ^ 2 - 1) * (y ^ 2 - 1))) ^ 2
      ∧ Cvs.L2a.SigmaSquareMultiplier.pr₃ w c (c ^ 2) y x
        ≤ 2 * (x ^ 2 - 1) * (2 * c ^ 2 * x * (y ^ 2 - 1) + 2 * c * y) ^ 2 * ‖w x‖
          / (c ^ 2 * ((x ^ 2 - 1) * (y ^ 2 - 1))) ^ 3 := by
  have hp : 0 < x ^ 2 - 1 := by nlinarith
  have hq : 0 < y ^ 2 - 1 := by nlinarith
  have hD : 0 < c ^ 2 * ((x ^ 2 - 1) * (y ^ 2 - 1)) := by positivity
  have hQ : c ^ 2 * ((x ^ 2 - 1) * (y ^ 2 - 1)) ≤ ‖qQ c (c ^ 2) y x‖ := by
    have := Cvs.L2a.QIdentityComplexWeight.norm_qQ_ge_re c (c ^ 2) y x
    rw [sub_self, sub_zero, abs_of_pos (by positivity)] at this
    linarith [show c ^ 2 * (x ^ 2 - 1) * (y ^ 2 - 1) = c ^ 2 * ((x ^ 2 - 1) * (y ^ 2 - 1)) by ring]
  have hQ1 : ‖qQ₁ c y x‖ ≤ 2 * c ^ 2 * x * (y ^ 2 - 1) + 2 * c * y :=
    Cvs.L2a.QIdentityIterated.norm_qQ₁_le_far (by linarith) hy.le hc.le
  have hQ2 : ‖qQ₂ c y‖ = 2 * c ^ 2 * (y ^ 2 - 1) := Cvs.L2a.QIdentityComplexWeight.norm_qQ₂_eq hy.le
  have hA1 := Cvs.L2a.QIdentityComplexWeight.norm_aC₁_le (w₁ := w₁) (w₂ := w₂) hc.le (by linarith : (0 : ℝ) ≤ y) hx.le
  have hA2 := Cvs.L2a.QIdentityComplexWeight.norm_aC₂_le (w := w) (w₁ := w₁) hc.le (by linarith : (0 : ℝ) ≤ y) hx.le
  have hA3 := Cvs.L2a.QIdentityComplexWeight.norm_aC₃_eq (w := w) (c := c) (y := y) hx.le
  unfold Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval.pP at hA1 hA2 hA3
  have hk : 0 ≤ 2 * x + 2 * (c * y) * (x ^ 2 - 1) := by
    have : 0 ≤ c * y := by nlinarith
    positivity
  refine ⟨?_, ?_, ?_⟩
  · unfold Cvs.L2a.SigmaSquareMultiplier.pr₁
    exact div_le_div₀ (by positivity) hA1 hD hQ
  · unfold Cvs.L2a.SigmaSquareMultiplier.pr₂
    refine div_le_div₀ (by positivity) (hA2.trans ?_) (by positivity) (pow_le_pow_left₀ hD.le hQ 2)
    rw [hQ2]
    gcongr
  · unfold Cvs.L2a.SigmaSquareMultiplier.pr₃
    refine div_le_div₀ (by positivity) (hA3.le.trans ?_) (by positivity) (pow_le_pow_left₀ hD.le hQ 3)
    gcongr

/-! ### The nine closed forms -/

/-- The quintic window norms `n₀ = √(181/462)`, `n₁ = √(10/7)`, `n₂ = √(120/7)`. -/
def n₀ : ℝ := √(181 / 462)

def n₁ : ℝ := √(10 / 7)

def n₂ : ℝ := √(120 / 7)

/-- `κ = √(2c/π)`. -/
def kap (c : ℝ) : ℝ := √(2 * c / π)

/-- BN3, the bottom corners `m ≥ 3` on `t ∈ (1, 2)`: expansion about `χ = 0`, ratio `9/49`, `ℓ²` over `W_m`. -/
def γBN3 (c δ : ℝ) : ℝ :=
  2 * (49 / 40 * (√3 / 2 * (n₁ / √δ * (4 * kap c * (1 + 21 / (16 * c)) / c) * √((π ^ 2 / 3 - 355 / 144) / 16)
        + n₂ / (δ * √δ) * (kap c / c ^ 2) * √(π ^ 2 / 12 - 55 / 576)))
    + (49 / 40) ^ 2 * (√3 / 2 * (n₀ * √δ * (8 * kap c * (1 + 21 / (16 * c)) * (1 + 2 / (5 * c)) / c
          + 2 * kap c / c ^ 2) * √(81 / 64 * (81 / 25) * (zR 6 - 1 - 1 / 64))
        + n₁ / √δ * (4 * kap c * (1 + 2 / (5 * c)) / c ^ 2) * √(81 / 64 * (81 / 25) * (zR 4 - 1 - 1 / 16))))
    + (49 / 40) ^ 3 * (√3 / 2 * n₀ * √δ * (8 * kap c * (1 + 2 / (5 * c)) ^ 2 / c ^ 2)
        * √((9 / 8) ^ 4 * (81 / 25) * (zR 6 - 1 - 1 / 64))))

def G21 (β : ℝ) : ℝ := 5 / 2 * 5 ^ (-(1 / 10) : ℝ) * 24 ^ (2 / 5 : ℝ) / β ^ 2

/-- The top-kernel majorants `A₀, B₀` at `ϖ`. -/
def A0 (c ϖ e : ℝ) : ℝ := 1 / (c * ϖ) + 3 / 8 / (c ^ 2 * ϖ ^ 2) + e / (c ^ 3 * ϖ ^ 2)

def B0 (c ϖ e : ℝ) : ℝ := 20 / (c * ϖ) + 54 / (c ^ 2 * ϖ ^ 2) + e / (c ^ 3 * ϖ ^ 2)

/-- D, the double boundary of `𝒞_a`: the count envelope at `M` twice. -/
def γD (c J : ℝ) : ℝ :=
  6 * J * kap c * A0 c (9 / 10) (1 / 4) ^ 2 * zR 2 + 3 * (1 + Real.log 3) * J * kap c / (16 * c ^ 2)
    + 60 * J * kap c * B0 c (9 / 10) 24 * zR 3 / (9 * (9 / 10) * c ^ 2)

/-- E₁, the `t`-bulk of `𝒞_a` on `(M, ∞)`: ratio `1/10`. -/
def γE1 (c J : ℝ) : ℝ :=
  2 * kap c * (3 * √(6 * J) / √8)
    * (10 / 9 * (8 * (1 + 3 / (8 * c)) * B0 c (9 / 10) 24 / (√3 * (9 / 10) * c)) * zR (5 / 2)
      + 10 / 9 * (16 * B0 c (9 / 10) 24 / (√5 * (9 / 10) ^ 2 * c ^ 2)) * zR (7 / 2)
      + (10 / 9) ^ 2 * (9 * (1 + 3 / (8 * c)) * (1 + 1 / (2 * c)) / (2 * c))
        * (A0 c (9 / 10) (1 / 4) * zR (3 / 2) / 3 + 1 / (4 * c) / √2 * ((1 + Real.log 3) / 3))
      + (10 / 9) ^ 2 * (9 / (8 * c ^ 2))
        * (A0 c (9 / 10) (1 / 4) * zR (3 / 2) / 6 + 1 / (4 * c) / √3 / (2 * √2) * ((1 + Real.log 3) / 3))
      + (10 / 9) ^ 2 * (9 * (1 + 1 / (2 * c)) * B0 c (9 / 10) 24 / (√3 * (9 / 10) * c ^ 2)) * zR (5 / 2) / 3
      + (10 / 9) ^ 3 * (81 * (1 + 1 / (2 * c)) ^ 2 / (16 * c ^ 2))
        * (A0 c (9 / 10) (1 / 4) * zR (3 / 2) / 6 + 1 / (4 * c) / √3 / (2 * √2) * ((1 + Real.log 3) / 3)))

/-! ### Tools for the pieces -/

/-- Finite Minkowski: `√Σ(a + b)² ≤ √Σa² + √Σb²`. -/
theorem sqrt_sum_add_sq_le (s : Finset ℕ) (a b : ℕ → ℝ) :
    √(∑ m ∈ s, (a m + b m) ^ 2) ≤ √(∑ m ∈ s, a m ^ 2) + √(∑ m ∈ s, b m ^ 2) := by
  rw [Real.sqrt_le_left (by positivity)]
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt s a b
  have ha := Real.sq_sqrt (Finset.sum_nonneg (s := s) fun m _ => sq_nonneg (a m))
  have hb := Real.sq_sqrt (Finset.sum_nonneg (s := s) fun m _ => sq_nonneg (b m))
  have e : ∑ m ∈ s, (a m + b m) ^ 2 = ∑ m ∈ s, a m ^ 2 + 2 * ∑ m ∈ s, a m * b m + ∑ m ∈ s, b m ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun m _ => by ring
  rw [e]
  nlinarith

/-- **The window `L²` bound**: `|h_m| ≤ α_m f_m + β_m g_m` on `W_m` with `‖f_m‖² ≤ A`, `‖g_m‖² ≤ B` gives
`(Σ_m ‖h_m‖²)^{1/2} ≤ √A(Σα_m²)^{1/2} + √B(Σβ_m²)^{1/2}`. -/
theorem sqrt_sum_window_le {s : Finset ℕ} {W : ℕ → Set ℝ} {h f g : ℕ → ℝ → ℝ} {α β : ℕ → ℝ} {A B : ℝ}
    (hα : ∀ m ∈ s, 0 ≤ α m) (hβ : ∀ m ∈ s, 0 ≤ β m) (hW : ∀ m ∈ s, MeasurableSet (W m))
    (hf0 : ∀ m ∈ s, ∀ x, 0 ≤ f m x) (hg0 : ∀ m ∈ s, ∀ x, 0 ≤ g m x)
    (hf : ∀ m ∈ s, MemLp (f m) 2 (volume.restrict (W m))) (hg : ∀ m ∈ s, MemLp (g m) 2 (volume.restrict (W m)))
    (hA : ∀ m ∈ s, ∫ x in W m, f m x ^ 2 ≤ A) (hB : ∀ m ∈ s, ∫ x in W m, g m x ^ 2 ≤ B)
    (hh0 : ∀ m ∈ s, ∀ x ∈ W m, 0 ≤ h m x) (hh : ∀ m ∈ s, ∀ x ∈ W m, h m x ≤ α m * f m x + β m * g m x) :
    √(∑ m ∈ s, ∫ x in W m, h m x ^ 2) ≤ √A * √(∑ m ∈ s, α m ^ 2) + √B * √(∑ m ∈ s, β m ^ 2) := by
  have hwin : ∀ m ∈ s, ∫ x in W m, h m x ^ 2 ≤ (α m * √A + β m * √B) ^ 2 := by
    intro m hm
    have hf2 := (memLp_two_iff_integrable_sq (hf m hm).aestronglyMeasurable).1 (hf m hm)
    have hg2 := (memLp_two_iff_integrable_sq (hg m hm).aestronglyMeasurable).1 (hg m hm)
    have hfg : Integrable (fun x => f m x * g m x) (volume.restrict (W m)) := (hf m hm).integrable_mul (hg m hm)
    have hI : Integrable (fun x => α m ^ 2 * f m x ^ 2 + 2 * (α m * β m) * (f m x * g m x) + β m ^ 2 * g m x ^ 2)
        (volume.restrict (W m)) :=
      ((hf2.const_mul _).add (hfg.const_mul _)).add (hg2.const_mul _)
    have h1 : ∫ x in W m, h m x ^ 2
        ≤ ∫ x in W m, (α m ^ 2 * f m x ^ 2 + 2 * (α m * β m) * (f m x * g m x) + β m ^ 2 * g m x ^ 2) := by
      refine integral_mono_of_nonneg (Eventually.of_forall fun x => sq_nonneg _) hI ?_
      refine (ae_restrict_iff' (hW m hm)).2 (Eventually.of_forall fun x hx => ?_)
      have h1 := hh m hm x hx
      have h0 := hh0 m hm x hx
      have e : α m ^ 2 * f m x ^ 2 + 2 * (α m * β m) * (f m x * g m x) + β m ^ 2 * g m x ^ 2
          = (α m * f m x + β m * g m x) ^ 2 := by ring
      show h m x ^ 2 ≤ α m ^ 2 * f m x ^ 2 + 2 * (α m * β m) * (f m x * g m x) + β m ^ 2 * g m x ^ 2
      rw [e]
      exact pow_le_pow_left₀ h0 h1 2
    have i1 : Integrable (fun x => α m ^ 2 * f m x ^ 2 + 2 * (α m * β m) * (f m x * g m x))
        (volume.restrict (W m)) := (hf2.const_mul _).add (hfg.const_mul _)
    rw [integral_add (f := fun x => α m ^ 2 * f m x ^ 2 + 2 * (α m * β m) * (f m x * g m x))
      (g := fun x => β m ^ 2 * g m x ^ 2) i1 (hg2.const_mul _),
      integral_add (f := fun x => α m ^ 2 * f m x ^ 2) (g := fun x => 2 * (α m * β m) * (f m x * g m x))
        (hf2.const_mul _) (hfg.const_mul _), integral_const_mul, integral_const_mul,
      integral_const_mul] at h1
    have hcs := Cvs.L2a.FarFarBound.integral_mul_abs_le (hf0 m hm) (hf m hm) (hg m hm)
    have hcs' : ∫ x in W m, f m x * g m x ≤ √A * √B := by
      have e : ∫ x in W m, f m x * |g m x| = ∫ x in W m, f m x * g m x :=
        integral_congr_ae (Eventually.of_forall fun x => by simp [abs_of_nonneg (hg0 m hm x)])
      rw [e] at hcs
      refine hcs.trans (mul_le_mul (Real.sqrt_le_sqrt (hA m hm)) (Real.sqrt_le_sqrt (hB m hm))
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    have hA0 : 0 ≤ A := (integral_nonneg fun x => sq_nonneg (f m x)).trans (hA m hm)
    have hB0 : 0 ≤ B := (integral_nonneg fun x => sq_nonneg (g m x)).trans (hB m hm)
    have hsA := Real.sq_sqrt hA0
    have hsB := Real.sq_sqrt hB0
    have hαβ : 0 ≤ α m * β m := mul_nonneg (hα m hm) (hβ m hm)
    have t1 : α m ^ 2 * ∫ x in W m, f m x ^ 2 ≤ α m ^ 2 * A := mul_le_mul_of_nonneg_left (hA m hm) (sq_nonneg _)
    have t2 : β m ^ 2 * ∫ x in W m, g m x ^ 2 ≤ β m ^ 2 * B := mul_le_mul_of_nonneg_left (hB m hm) (sq_nonneg _)
    have t3 : 2 * (α m * β m) * ∫ x in W m, f m x * g m x ≤ 2 * (α m * β m) * (√A * √B) :=
      mul_le_mul_of_nonneg_left hcs' (by positivity)
    calc ∫ x in W m, h m x ^ 2 ≤ _ := h1
      _ ≤ α m ^ 2 * A + 2 * (α m * β m) * (√A * √B) + β m ^ 2 * B := by linarith
      _ = (α m * √A + β m * √B) ^ 2 := by
          rw [show (α m * √A + β m * √B) ^ 2
              = α m ^ 2 * √A ^ 2 + 2 * (α m * β m) * (√A * √B) + β m ^ 2 * √B ^ 2 by ring, hsA, hsB]
  calc √(∑ m ∈ s, ∫ x in W m, h m x ^ 2) ≤ √(∑ m ∈ s, (α m * √A + β m * √B) ^ 2) :=
        Real.sqrt_le_sqrt (Finset.sum_le_sum hwin)
    _ ≤ √(∑ m ∈ s, (α m * √A) ^ 2) + √(∑ m ∈ s, (β m * √B) ^ 2) := sqrt_sum_add_sq_le s _ _
    _ = √A * √(∑ m ∈ s, α m ^ 2) + √B * √(∑ m ∈ s, β m ^ 2) := by
        simp only [mul_pow, ← Finset.sum_mul]
        rw [Real.sqrt_mul (Finset.sum_nonneg fun m _ => sq_nonneg _), Real.sqrt_mul
          (Finset.sum_nonneg fun m _ => sq_nonneg _), Real.sqrt_sq (Real.sqrt_nonneg _),
          Real.sqrt_sq (Real.sqrt_nonneg _)]
        ring

/-- The one-window form of `sqrt_sum_window_le`. -/
theorem sqrt_window_le {W : Set ℝ} {h f g : ℝ → ℝ} {α β A B : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hW : MeasurableSet W) (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) (hf : MemLp f 2 (volume.restrict W))
    (hg : MemLp g 2 (volume.restrict W)) (hA : ∫ x in W, f x ^ 2 ≤ A) (hB : ∫ x in W, g x ^ 2 ≤ B)
    (hh0 : ∀ x ∈ W, 0 ≤ h x) (hh : ∀ x ∈ W, h x ≤ α * f x + β * g x) :
    √(∫ x in W, h x ^ 2) ≤ √A * α + √B * β := by
  have := sqrt_sum_window_le (s := {0}) (W := fun _ => W) (h := fun _ => h) (f := fun _ => f) (g := fun _ => g)
    (α := fun _ => α) (β := fun _ => β) (A := A) (B := B) (fun _ _ => hα) (fun _ _ => hβ) (fun _ _ => hW)
    (fun _ _ => hf0) (fun _ _ => hg0) (fun _ _ => hf) (fun _ _ => hg) (fun _ _ => hA) (fun _ _ => hB)
    (fun _ _ => hh0) (fun _ _ => hh)
  simpa [Real.sqrt_sq hα, Real.sqrt_sq hβ] using this

theorem one_lt_log_three : 1 < Real.log 3 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have := Real.exp_one_lt_d9
  linarith

/-! ### `γ → 0` -/

/-- Limits of sums, products, powers, roots and maxima of convergent atoms. -/
local syntax "tend" : tactic
macro_rules
  | `(tactic| tend) => `(tactic| first
      | with_reducible exact tendsto_const_nhds
      | with_reducible assumption
      | (with_reducible apply Filter.Tendsto.add <;> tend)
      | (with_reducible apply Filter.Tendsto.sub <;> tend)
      | (with_reducible apply Filter.Tendsto.mul <;> tend)
      | (with_reducible apply Filter.Tendsto.div_const <;> tend)
      | (with_reducible apply Filter.Tendsto.pow <;> tend)
      | (with_reducible apply Filter.Tendsto.sqrt <;> tend)
      | (with_reducible apply Filter.Tendsto.max <;> tend))

theorem sqrt_mul_sq_div (a b : ℝ) {t : ℝ} (ht : 0 ≤ t) : √(a * t ^ 2 / b) = t * √(a / b) := by
  rw [show a * t ^ 2 / b = a / b * t ^ 2 by ring, Real.sqrt_mul' _ (sq_nonneg t), Real.sqrt_sq ht]; ring

theorem kap_sq {s : ℝ} (hs : 0 ≤ s) : kap (s ^ 2) = s * √(2 / π) := by
  unfold kap; exact sqrt_mul_sq_div 2 π hs

/-! ### The far bottom corners -/

section pieces

variable {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ)

end pieces

end Cvs.L2a.CutKernelRemainder
