import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.Prolate.DilatedModeGreenIdentity
import Cvs.Prolate.ExteriorSpanBernstein
import Cvs.Prolate.Gram.RungGramFloorAtInfinity
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Route.Visibility.AliasPairGreenIntegrand
import Cvs.Route.Visibility.AliasPairThetaKernel

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The pointwise bound on the Green integrand of an alias pair

For the span `h = Σ b_iψ_i` with levels in `[0, c²]`, on `12/25 ≤ θ ≤ 11/10` with `q_{kl} ≤ 3/4`, `|w| ≤ 1` and
`|w′| ≤ 70`, the mode-summed Green integrand of `(k, l)` differs from its leading term `N₀` by at most
`Γ₀/(c(k − l)²)·Σ_{N<M}(N + 1)²(3/4)^N Z_N(kθ)Z_N(lθ) + (k + l)(8ω₀ + 192L₀)c⁻²(2M + 1)(3/4)^M R`.
-/

noncomputable section

namespace Cvs.Route.Visibility.AliasPairPointwiseBound
open Cvs.ZeroCounting

open Real Set Finset
open Cvs.L2a.AngularProlateTailPositive (psi)
open Cvs.Prolate.Gram.RungGramFloorAtInfinity (rungU)
open Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval (pP)
open Cvs.Prolate.ExteriorSpanBernstein (spanH spanU)
open Cvs.Route.Visibility.AliasPairThetaKernel (bet Lam qK bet_mem abs_Lam_sub_ge one_lt_of)
open Cvs.Prolate.DilatedModeGreenIdentity (Pk Vk Ak AkD gI Ak_eq pP_mul_eq)
open Cvs.Route.Visibility.AliasPairGreenIntegrand (B1s B2s green_split pair_dev_le coeff_le)

variable {ι : Type*} [Fintype ι]

/-- The centred levels `e_i = c²/2 − χ_i`. -/
def eK (c : ℝ) (χ : ι → ℝ) (i : ι) : ℝ := c ^ 2 / 2 - χ i

/-- The normalised `a`-th level moment of the span at `t`: `Σ b_ie_i^aψ_i(t)/(c²/2)^a`. -/
def Hn (c : ℝ) (g : ι → ℝ → ℝ) (χ : ι → ℝ) (b : ι → ℝ) (a : ℕ) (t : ℝ) : ℝ :=
  spanH c g (fun i => b i * eK c χ i ^ a) t / (c ^ 2 / 2) ^ a

/-- The normalised `a`-th level moment of the slope at `t`: `Σ b_ie_i^aψ_i′(t)/(c(c²/2)^a)`. -/
def Dn (c : ℝ) (g : ι → ℝ → ℝ) (χ : ι → ℝ) (b : ι → ℝ) (a : ℕ) (t : ℝ) : ℝ :=
  spanU c g (fun i => b i * eK c χ i ^ a) t / pP t / (c * (c ^ 2 / 2) ^ a)

/-- The moment majorant `Z_N(t) = Σ_{a ≤ N+1}(|H_a(t)| + |D_a(t)|)`. -/
def Zf (c : ℝ) (g : ι → ℝ → ℝ) (χ : ι → ℝ) (b : ι → ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  ∑ a ∈ range (N + 2), (|Hn c g χ b a t| + |Dn c g χ b a t|)

/-- The leading (Hilbert) term of the pair `(k, l)`. -/
def N0 (c : ℝ) (g : ι → ℝ → ℝ) (b : ι → ℝ) (w w' : ℝ → ℝ) (k l : ℕ) (θ : ℝ) : ℝ :=
  ((w' θ - 2 * w θ * θ * bet k θ) * k * (spanU c g b (k * θ) / pP (k * θ) * spanH c g b (l * θ))
    - (w' θ - 2 * w θ * θ * bet l θ) * l * (spanH c g b (k * θ) * (spanU c g b (l * θ) / pP (l * θ))))
    / (c ^ 2 * (Lam k θ - Lam l θ))

/-- The remainder mass `Σ_i(|b_iψ_i′(kθ)| + |b_iψ_i(kθ)|)·Σ_j(|b_jψ_j′(lθ)| + |b_jψ_j(lθ)|)`. -/
def Rf (c : ℝ) (g : ι → ℝ → ℝ) (b : ι → ℝ) (k l : ℕ) (θ : ℝ) : ℝ :=
  (∑ i, (|b i * Vk c (g i) k θ| + |b i * Pk c (g i) k θ|)) * (∑ j, (|b j * Vk c (g j) l θ| + |b j * Pk c (g j) l θ|))

/-- `β̄ = 5625/671`. -/
def βb : ℝ := 5625 / 671

/-- `ω₀ = 70 + (11/5)β̄`. -/
def ω₀ : ℝ := 70 + 11 / 5 * βb

/-- `L₀ = (11/10)β̄²`. -/
def L₀ : ℝ := 11 / 10 * βb ^ 2

/-- `Γ₀ = 16ω₀β̄/21 + 12L₀/7`. -/
def Γ₀ : ℝ := 16 * ω₀ * βb / 21 + 12 * L₀ / 7

/-- The level moments of the values `b_iψ_i(t)` are `H_a(t)`. -/
theorem mom_P (c : ℝ) (g : ι → ℝ → ℝ) (χ b : ι → ℝ) (a : ℕ) (t : ℝ) :
    (∑ i, b i * psi c (g i) t * eK c χ i ^ a) / (c ^ 2 / 2) ^ a = Hn c g χ b a t := by
  unfold Hn spanH; congr 1; exact Finset.sum_congr rfl fun i _ => by ring

/-- The level moments of the slopes `b_iψ_i′(t)` are `cD_a(t)`. -/
theorem mom_V {c : ℝ} (hc : 0 < c) (g : ι → ℝ → ℝ) (χ b : ι → ℝ) (a : ℕ) (t : ℝ) :
    (∑ i, b i * (rungU c (g i) t / pP t) * eK c χ i ^ a) / (c ^ 2 / 2) ^ a = c * Dn c g χ b a t := by
  unfold Dn spanU
  have hr : (c ^ 2 / 2) ^ a ≠ 0 := pow_ne_zero _ (by positivity)
  have e : ∑ i, b i * (rungU c (g i) t / pP t) * eK c χ i ^ a = (∑ i, b i * eK c χ i ^ a * rungU c (g i) t) / pP t := by
    rw [Finset.sum_div]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [e]
  field_simp

/-- **The pointwise pair bound**: on `12/25 ≤ θ ≤ 11/10` with `q_{kl} ≤ 3/4`, `|w| ≤ 1`, `|w′| ≤ 70`, the mode-summed
Green integrand minus its leading term is at most `Γ₀/(c(k − l)²)·Σ_N(N + 1)²(3/4)^N Z_N(kθ)Z_N(lθ)` plus remainder. -/
theorem pair_pointwise {c : ℝ} (hc : 0 < c) (g : ι → ℝ → ℝ) {χ : ι → ℝ} (hχ : ∀ i, 0 ≤ χ i ∧ χ i ≤ c ^ 2)
    (b : ι → ℝ) {k l : ℕ} (hk : 3 ≤ k) (hl : 3 ≤ l) (hkl : k ≠ l) {θ : ℝ} (hθ : 12 / 25 ≤ θ) (hθ1 : θ ≤ 11 / 10)
    (hq : qK k l θ ≤ 3 / 4) {w w' : ℝ → ℝ} (hw : |w θ| ≤ 1) (hw' : |w' θ| ≤ 70) {M : ℕ} (hM : 1 ≤ M) :
    |∑ i, ∑ j, b i * b j * gI c (g i) (g j) (χ i) (χ j) w w' k l θ - N0 c g b w w' k l θ|
      ≤ Γ₀ / (c * ((k : ℝ) - l) ^ 2)
          * ∑ N ∈ range M, ((N : ℝ) + 1) ^ 2 * (3 / 4) ^ N * (Zf c g χ b N (k * θ) * Zf c g χ b N (l * θ))
        + (k + l) * (8 * ω₀ + 192 * L₀) / c ^ 2 * (((2 * M + 1) * (3 / 4) ^ M) * Rf c g b k l θ) := by
  set r : ℝ := c ^ 2 / 2 with hr
  set A : ℝ := c ^ 2 * (Lam k θ - Lam l θ) with hAdef
  set β₁ := bet k θ
  set β₂ := bet l θ
  set e : ι → ℝ := eK c χ
  set Ad : ℝ := -θ * c ^ 2 * (β₁ ^ 2 - β₂ ^ 2)
  set γ₁ : ℝ := -2 * θ * β₁ ^ 2
  set γ₂ : ℝ := -2 * θ * β₂ ^ 2
  set XV : ι → ℝ := fun i => b i * Vk c (g i) k θ
  set XP : ι → ℝ := fun i => b i * Pk c (g i) k θ
  set YV : ι → ℝ := fun i => b i * Vk c (g i) l θ
  set YP : ι → ℝ := fun i => b i * Pk c (g i) l θ
  have hk2 : (k : ℝ) ^ 2 * θ ^ 2 - 1 ≠ 0 := by have := one_lt_of hk hθ; intro h; linarith
  have hl2 : (l : ℝ) ^ 2 * θ ^ 2 - 1 ≠ 0 := by have := one_lt_of hl hθ; intro h; linarith
  have hbk := bet_mem hk hθ
  have hbl := bet_mem hl hθ
  have hr0 : 0 < r := by positivity
  have hgap := abs_Lam_sub_ge hk hl hθ
  have hd : 0 < |(k : ℝ) ^ 2 - (l : ℝ) ^ 2| := by
    refine abs_pos.mpr fun h => hkl ?_
    have : (k : ℝ) ^ 2 = (l : ℝ) ^ 2 := by linarith
    exact_mod_cast (sq_eq_sq₀ (Nat.cast_nonneg k) (Nat.cast_nonneg l)).mp this
  have hAabs : c ^ 2 * |(k : ℝ) ^ 2 - (l : ℝ) ^ 2| / 2 ≤ |A| := by
    rw [hAdef, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < c ^ 2)]
    nlinarith [sq_nonneg c]
  have hA0 : A ≠ 0 := abs_pos.mp (lt_of_lt_of_le (by positivity) hAabs)
  -- the Green integrand in decoupled form
  have hsum : ∑ i, ∑ j, b i * b j * gI c (g i) (g j) (χ i) (χ j) w w' k l θ
      = ∑ i, ∑ j, ((w' θ / (A + β₁ * e i - β₂ * e j) - w θ * (Ad + γ₁ * e i - γ₂ * e j) / (A + β₁ * e i - β₂ * e j) ^ 2)
        * (k * XV i * YP j - XP i * (l * YV j))
        - 2 * (w θ / (A + β₁ * e i - β₂ * e j)) * θ * (β₁ * (k * XV i) * YP j - β₂ * XP i * (l * YV j))) := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have hD : Ak c (χ i) k θ - Ak c (χ j) l θ = A + β₁ * e i - β₂ * e j := by
      rw [Ak_eq _ hk2, Ak_eq _ hl2]; simp only [hAdef, e, eK, β₁, β₂]; ring
    have hD' : AkD c (χ i) k θ - AkD c (χ j) l θ = Ad + γ₁ * e i - γ₂ * e j := by
      simp only [AkD, Ad, γ₁, γ₂, e, eK, β₁, β₂]; ring
    simp only [gI, hD, hD', XV, XP, YV, YP]
    ring
  rw [hsum, green_split]
  have hN0 : N0 c g b w w' k l θ = ((w' θ - 2 * w θ * θ * β₁) * k * ((∑ n, XV n) * (∑ m, YP m))
        - (w' θ - 2 * w θ * θ * β₂) * l * ((∑ n, XP n) * (∑ m, YV m))) / A := by
    have h1 : ∑ n, XV n = spanU c g b (k * θ) / pP (k * θ) := by
      simp only [XV, Vk, spanU, Finset.sum_div]; exact Finset.sum_congr rfl fun i _ => by ring
    have h2 : ∑ n, YV n = spanU c g b (l * θ) / pP (l * θ) := by
      simp only [YV, Vk, spanU, Finset.sum_div]; exact Finset.sum_congr rfl fun i _ => by ring
    have h3 : ∑ n, XP n = spanH c g b (k * θ) := by simp only [XP, Pk, spanH]
    have h4 : ∑ n, YP n = spanH c g b (l * θ) := by simp only [YP, Pk, spanH]
    rw [h1, h2, h3, h4]; rfl
  rw [hN0]
  -- the moment bounds
  have hZ : ∀ (t : ℝ) N a, a ≤ N + 1 → |Hn c g χ b a t| ≤ Zf c g χ b N t ∧ |Dn c g χ b a t| ≤ Zf c g χ b N t := by
    intro t N a ha
    have hmem : a ∈ range (N + 2) := Finset.mem_range.mpr (by omega)
    have hsingle := Finset.single_le_sum (f := fun a => |Hn c g χ b a t| + |Dn c g χ b a t|)
      (fun a _ => by positivity) hmem
    exact ⟨le_trans (le_add_of_nonneg_right (abs_nonneg _)) hsingle,
      le_trans (le_add_of_nonneg_left (abs_nonneg _)) hsingle⟩
  have hmVk : ∀ a, (∑ n, XV n * e n ^ a) / r ^ a = c * Dn c g χ b a (k * θ) := fun a => by
    rw [← mom_V hc g χ b a (k * θ)]; rfl
  have hmPk : ∀ a, (∑ n, XP n * e n ^ a) / r ^ a = Hn c g χ b a (k * θ) := fun a => by
    rw [← mom_P c g χ b a (k * θ)]; rfl
  have hmVl : ∀ a, (∑ n, YV n * e n ^ a) / r ^ a = c * Dn c g χ b a (l * θ) := fun a => by
    rw [← mom_V hc g χ b a (l * θ)]; rfl
  have hmPl : ∀ a, (∑ n, YP n * e n ^ a) / r ^ a = Hn c g χ b a (l * θ) := fun a => by
    rw [← mom_P c g χ b a (l * θ)]; rfl
  have hZK : ∀ N a, a ≤ N + 1 → |(∑ n, XV n * e n ^ a) / r ^ a| ≤ c * Zf c g χ b N (k * θ)
      ∧ |(∑ n, XP n * e n ^ a) / r ^ a| ≤ Zf c g χ b N (k * θ) := by
    intro N a ha
    rw [hmVk, hmPk, abs_mul, abs_of_pos hc]
    exact ⟨mul_le_mul_of_nonneg_left (hZ _ N a ha).2 hc.le, (hZ _ N a ha).1⟩
  have hZL : ∀ N a, a ≤ N + 1 → |(∑ n, YV n * e n ^ a) / r ^ a| ≤ c * Zf c g χ b N (l * θ)
      ∧ |(∑ n, YP n * e n ^ a) / r ^ a| ≤ Zf c g χ b N (l * θ) := by
    intro N a ha
    rw [hmVl, hmPl, abs_mul, abs_of_pos hc]
    exact ⟨mul_le_mul_of_nonneg_left (hZ _ N a ha).2 hc.le, (hZ _ N a ha).1⟩
  have he : ∀ n, |e n| ≤ r := fun n => by
    simp only [e, eK, hr]; rw [abs_le]; constructor <;> linarith [(hχ n).1, (hχ n).2]
  have hqA : r * (β₁ + β₂) / |A| ≤ 3 / 4 := by
    have : r * (β₁ + β₂) / |A| = qK k l θ := by
      simp only [qK, hAdef, hr, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < c ^ 2)]
      field_simp
      rfl
    rw [this]; exact hq
  have hωb : ∀ β, 0 ≤ β → β ≤ 5625 / 671 → |w' θ - 2 * w θ * θ * β| ≤ ω₀ := by
    intro β h0 h1
    have hθ0 : 0 ≤ θ := by linarith
    calc |w' θ - 2 * w θ * θ * β| ≤ |w' θ| + |2 * w θ * θ * β| := abs_sub _ _
      _ = |w' θ| + 2 * |w θ| * θ * β := by
          rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_nonneg hθ0,
            abs_of_nonneg h0]
      _ ≤ 70 + 2 * 1 * (11 / 10) * (5625 / 671) := by gcongr
      _ = ω₀ := by simp only [ω₀, βb]; norm_num
  have hdev := pair_dev_le XV XP YV YP e (Ad := Ad) (γ₁ := γ₁) (γ₂ := γ₂) (w := w θ) hc hr0 he hbk.1.le hbl.1.le hA0
    hqA (hωb _ hbk.1.le hbk.2) (hωb _ hbl.1.le hbl.2) (Nat.cast_nonneg k) (Nat.cast_nonneg l)
    (fun N => Zf c g χ b N (k * θ)) (fun N => Zf c g χ b N (l * θ)) hZK hZL hM
  have hcoef := coeff_le (A := A) (β₁ := β₁) (β₂ := β₂) (Ad := Ad) (γ₁ := γ₁) (γ₂ := γ₂) (w := w θ) (ω := ω₀)
    (L := L₀) (βb := βb) hc hr hk hl hkl hAabs (by simp only [βb]; linarith [hbk.2, hbl.2]) hbk.1.le hbl.1.le hw
    (by simp only [ω₀, βb]; norm_num) ?_ ?_ ?_ (by simp only [βb]; norm_num) (by simp only [L₀]; positivity)
  · have hS0 : 0 ≤ ∑ N ∈ range M, ((N : ℝ) + 1) ^ 2 * (3 / 4) ^ N
        * (Zf c g χ b N (k * θ) * Zf c g χ b N (l * θ)) := by
      refine Finset.sum_nonneg fun N _ => mul_nonneg (by positivity) (mul_nonneg ?_ ?_) <;>
        exact Finset.sum_nonneg fun a _ => by positivity
    have hR0 : 0 ≤ ((2 * M + 1 : ℝ) * (3 / 4) ^ M) * Rf c g b k l θ := by
      unfold Rf; positivity
    refine hdev.trans ?_
    rw [mul_assoc _ ((2 * (M : ℝ) + 1) * (3 / 4) ^ M)]
    refine add_le_add (mul_le_mul_of_nonneg_right ?_ hS0) (mul_le_mul_of_nonneg_right hcoef.2 hR0)
    refine hcoef.1.trans (le_of_eq ?_)
    simp only [Γ₀]
  · have h1 : β₁ ^ 2 ≤ βb ^ 2 := pow_le_pow_left₀ hbk.1.le hbk.2 2
    have h2 : β₂ ^ 2 ≤ βb ^ 2 := pow_le_pow_left₀ hbl.1.le hbl.2 2
    have h3 : |β₁ ^ 2 - β₂ ^ 2| ≤ βb ^ 2 := by
      rw [abs_le]; constructor <;> nlinarith [sq_nonneg β₁, sq_nonneg β₂]
    have hθ0 : 0 ≤ θ := by linarith
    simp only [Ad, L₀]
    rw [show -θ * c ^ 2 * (β₁ ^ 2 - β₂ ^ 2) = -(θ * c ^ 2) * (β₁ ^ 2 - β₂ ^ 2) by ring, abs_mul, abs_neg,
      abs_of_nonneg (by positivity : 0 ≤ θ * c ^ 2)]
    calc θ * c ^ 2 * |β₁ ^ 2 - β₂ ^ 2| ≤ 11 / 10 * c ^ 2 * βb ^ 2 := by gcongr
      _ = 11 / 10 * βb ^ 2 * c ^ 2 := by ring
  · have hθ0 : 0 ≤ θ := by linarith
    have h1 : β₁ ^ 2 ≤ βb ^ 2 := pow_le_pow_left₀ hbk.1.le hbk.2 2
    simp only [γ₁, L₀]
    rw [show -2 * θ * β₁ ^ 2 = -(2 * θ * β₁ ^ 2) by ring, abs_neg,
      abs_of_nonneg (mul_nonneg (mul_nonneg (by norm_num) hθ0) (sq_nonneg _))]
    have := mul_le_mul hθ1 h1 (sq_nonneg _) (by norm_num)
    linarith
  · have hθ0 : 0 ≤ θ := by linarith
    have h1 : β₂ ^ 2 ≤ βb ^ 2 := pow_le_pow_left₀ hbl.1.le hbl.2 2
    simp only [γ₂, L₀]
    rw [show -2 * θ * β₂ ^ 2 = -(2 * θ * β₂ ^ 2) by ring, abs_neg,
      abs_of_nonneg (mul_nonneg (mul_nonneg (by norm_num) hθ0) (sq_nonneg _))]
    have := mul_le_mul hθ1 h1 (sq_nonneg _) (by norm_num)
    linarith

end Cvs.Route.Visibility.AliasPairPointwiseBound
