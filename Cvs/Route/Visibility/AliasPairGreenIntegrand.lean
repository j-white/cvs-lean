import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Cvs.Upstream.PairSumPowerDecoupling

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The decoupled Green integrand of an alias pair and its pointwise majorant

Writing `D_{ij} = A + β₁e_i − β₂e_j` and `D′_{ij} = A_d + γ₁e_i − γ₂e_j`, the mode-summed Green integrand is a
combination of the pair sums over `1/D` and `1/D²`; with Cvs.Upstream.PairSumPowerDecoupling and `q ≤ 3/4`, its deviation from the leading term
`(w′ − 2wθβ₁)k(ΣX_V)(ΣY_P)/A − (w′ − 2wθβ₂)l(ΣX_P)(ΣY_V)/A` is at most `Γ/(c(k − l)²)·Σ_N (N + 1)²(3/4)^N Z_K Z_L`.
-/

noncomputable section

namespace Cvs.Route.Visibility.AliasPairGreenIntegrand

open Finset Cvs.Upstream.PairSumPowerDecoupling

variable {ι : Type*} [Fintype ι]

/-- The first-order pair sum `Σ_{nm} F_nG_m/(A + β₁e_n − β₂e_m)`. -/
def B1s (F G e : ι → ℝ) (A β₁ β₂ : ℝ) : ℝ := ∑ n, ∑ m, F n * G m / (A + β₁ * e n - β₂ * e m)

/-- The second-order pair sum `Σ_{nm} F_nG_m/(A + β₁e_n − β₂e_m)²`. -/
def B2s (F G e : ι → ℝ) (A β₁ β₂ : ℝ) : ℝ := ∑ n, ∑ m, F n * G m / (A + β₁ * e n - β₂ * e m) ^ 2

/-- **The Green integrand in decoupled form.** -/
theorem green_split (XV XP YV YP e : ι → ℝ) (A β₁ β₂ Ad γ₁ γ₂ w w' θ k l : ℝ) :
    ∑ i, ∑ j, ((w' / (A + β₁ * e i - β₂ * e j) - w * (Ad + γ₁ * e i - γ₂ * e j) / (A + β₁ * e i - β₂ * e j) ^ 2)
        * (k * XV i * YP j - XP i * (l * YV j))
        - 2 * (w / (A + β₁ * e i - β₂ * e j)) * θ * (β₁ * (k * XV i) * YP j - β₂ * XP i * (l * YV j)))
      = (w' - 2 * w * θ * β₁) * k * B1s XV YP e A β₁ β₂ - (w' - 2 * w * θ * β₂) * l * B1s XP YV e A β₁ β₂
        - w * k * (Ad * B2s XV YP e A β₁ β₂ + γ₁ * B2s (fun i => e i * XV i) YP e A β₁ β₂
            - γ₂ * B2s XV (fun j => e j * YP j) e A β₁ β₂)
        + w * l * (Ad * B2s XP YV e A β₁ β₂ + γ₁ * B2s (fun i => e i * XP i) YV e A β₁ β₂
            - γ₂ * B2s XP (fun j => e j * YV j) e A β₁ β₂) := by
  simp only [B1s, B2s, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- `Σ_{a ≤ N}|P_a||Q_{N−a}| ≤ (N + 1)XY` when every `|P_a| ≤ X` and `|Q_b| ≤ Y`. -/
theorem sum_mom_le {P Q : ℕ → ℝ} {X Y : ℝ} (N : ℕ) (hP : ∀ a ≤ N, |P a| ≤ X) (hQ : ∀ b ≤ N, |Q b| ≤ Y) :
    ∑ a ∈ range (N + 1), |P a| * |Q (N - a)| ≤ ((N : ℝ) + 1) * (X * Y) := by
  have hY : 0 ≤ Y := (abs_nonneg _).trans (hQ 0 (Nat.zero_le _))
  calc ∑ a ∈ range (N + 1), |P a| * |Q (N - a)| ≤ ∑ _a ∈ range (N + 1), X * Y := by
        refine Finset.sum_le_sum fun a ha => ?_
        have ha' : a ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
        exact mul_le_mul (hP a ha') (hQ _ (Nat.sub_le _ _)) (abs_nonneg _) ((abs_nonneg _).trans (hP a ha'))
    _ = ((N : ℝ) + 1) * (X * Y) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring

/-- **The first-order piece**: the deviation of the `1/D` pair sum from its leading term, with moment bounds. -/
theorem B1s_dev_le (F G e : ι → ℝ) {A β₁ β₂ r : ℝ} (hA : A ≠ 0) (hr : 0 < r) (hβ₁ : 0 ≤ β₁) (hβ₂ : 0 ≤ β₂)
    (he : ∀ n, |e n| ≤ r) (hq : r * (β₁ + β₂) / |A| ≤ 3 / 4) (X Y : ℕ → ℝ)
    (hX : ∀ N a, a ≤ N → |(∑ n, F n * e n ^ a) / r ^ a| ≤ X N)
    (hY : ∀ N b, b ≤ N → |(∑ m, G m * e m ^ b) / r ^ b| ≤ Y N) {M : ℕ} (hM : 1 ≤ M) :
    |B1s F G e A β₁ β₂ - (∑ n, F n) * (∑ m, G m) / A|
      ≤ (∑ N ∈ range M, ((N : ℝ) + 1) * (3 / 4) ^ N * (X N * Y N)) * (4 / 3 * (r * (β₁ + β₂) / |A|)) / |A|
        + 4 * (3 / 4) ^ M * ((∑ n, |F n|) * (∑ m, |G m|)) / |A| := by
  have h := bilin1 F G e hA hr hβ₁ hβ₂ he hq (by norm_num : (3 / 4 : ℝ) < 1) hM
  set q₀ := r * (β₁ + β₂) / |A| with hq₀
  have hq0 : 0 ≤ q₀ := by positivity
  have hA' : 0 < |A| := abs_pos.mpr hA
  refine h.trans ?_
  rw [add_div]
  refine add_le_add ?_ (le_of_eq ?_)
  · refine div_le_div_of_nonneg_right ?_ hA'.le
    rw [Finset.sum_mul]
    have hg0 : ∀ N : ℕ, 0 ≤ ((N : ℝ) + 1) * (3 / 4) ^ N * (X N * Y N) * (4 / 3 * q₀) := by
      intro N
      have h1 := (abs_nonneg _).trans (hX N 0 (Nat.zero_le _))
      have h2 := (abs_nonneg _).trans (hY N 0 (Nat.zero_le _))
      have h3 := pow_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4) N
      exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) h3) (mul_nonneg h1 h2))
        (mul_nonneg (by norm_num) hq0)
    refine (Finset.sum_le_sum fun N hN => ?_).trans
      (Finset.sum_le_sum_of_subset_of_nonneg (t := range M) (fun N hN => by
        rw [Finset.mem_range]; exact (Finset.mem_Ico.mp hN).2) fun N _ _ => hg0 N)
    have hN1 : 1 ≤ N := (Finset.mem_Ico.mp hN).1
    have hmom := sum_mom_le (P := fun a => (∑ n, F n * e n ^ a) / r ^ a)
      (Q := fun b => (∑ m, G m * e m ^ b) / r ^ b) N (hX N) (hY N)
    have hpow : q₀ ^ N ≤ 4 / 3 * q₀ * (3 / 4) ^ N := by
      obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
      rw [pow_succ, pow_succ]
      have : q₀ ^ N' ≤ (3 / 4) ^ N' := pow_le_pow_left₀ hq0 hq N'
      nlinarith [pow_nonneg hq0 N', pow_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4) N']
    have hs0 : 0 ≤ ∑ a ∈ range (N + 1), |(∑ n, F n * e n ^ a) / r ^ a| * |(∑ m, G m * e m ^ (N - a)) / r ^ (N - a)| :=
      Finset.sum_nonneg fun a _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
    calc q₀ ^ N * ∑ a ∈ range (N + 1), |(∑ n, F n * e n ^ a) / r ^ a| * |(∑ m, G m * e m ^ (N - a)) / r ^ (N - a)|
        ≤ (4 / 3 * q₀ * (3 / 4) ^ N) * (((N : ℝ) + 1) * (X N * Y N)) :=
          mul_le_mul hpow hmom hs0 (mul_nonneg (mul_nonneg (by norm_num) hq0) (pow_nonneg (by norm_num) _))
      _ = ((N : ℝ) + 1) * (3 / 4) ^ N * (X N * Y N) * (4 / 3 * q₀) := by ring
  · rw [Finset.sum_mul_sum]
    field_simp
    ring

/-- **The second-order piece**: the `1/D²` pair sum with moment bounds. -/
theorem B2s_le (F G e : ι → ℝ) {A β₁ β₂ r : ℝ} (hA : A ≠ 0) (hr : 0 < r) (hβ₁ : 0 ≤ β₁) (hβ₂ : 0 ≤ β₂)
    (he : ∀ n, |e n| ≤ r) (hq : r * (β₁ + β₂) / |A| ≤ 3 / 4) (X Y : ℕ → ℝ)
    (hX : ∀ N a, a ≤ N → |(∑ n, F n * e n ^ a) / r ^ a| ≤ X N)
    (hY : ∀ N b, b ≤ N → |(∑ m, G m * e m ^ b) / r ^ b| ≤ Y N) (M : ℕ) :
    |B2s F G e A β₁ β₂|
      ≤ (∑ N ∈ range M, ((N : ℝ) + 1) ^ 2 * (3 / 4) ^ N * (X N * Y N)) / A ^ 2
        + 16 * (2 * M + 1) * (3 / 4) ^ M * ((∑ n, |F n|) * (∑ m, |G m|)) / A ^ 2 := by
  have h := bilin2 F G e hA hr hβ₁ hβ₂ he hq (by norm_num : (3 / 4 : ℝ) < 1) M
  set q₀ := r * (β₁ + β₂) / |A| with hq₀
  have hq0 : 0 ≤ q₀ := by positivity
  have hA2 : 0 < A ^ 2 := by positivity
  refine h.trans ?_
  rw [add_div]
  refine add_le_add ?_ (le_of_eq ?_)
  · refine div_le_div_of_nonneg_right (Finset.sum_le_sum fun N _ => ?_) hA2.le
    have hmom := sum_mom_le (P := fun a => (∑ n, F n * e n ^ a) / r ^ a)
      (Q := fun b => (∑ m, G m * e m ^ b) / r ^ b) N (hX N) (hY N)
    have hpow : q₀ ^ N ≤ (3 / 4) ^ N := pow_le_pow_left₀ hq0 hq N
    have hs0 : 0 ≤ ∑ a ∈ range (N + 1), |(∑ n, F n * e n ^ a) / r ^ a| * |(∑ m, G m * e m ^ (N - a)) / r ^ (N - a)| :=
      Finset.sum_nonneg fun a _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
    calc ((N : ℝ) + 1) * (q₀ ^ N * ∑ a ∈ range (N + 1),
          |(∑ n, F n * e n ^ a) / r ^ a| * |(∑ m, G m * e m ^ (N - a)) / r ^ (N - a)|)
        ≤ ((N : ℝ) + 1) * ((3 / 4) ^ N * (((N : ℝ) + 1) * (X N * Y N))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hpow hmom hs0 (pow_nonneg (by norm_num) _)) (by positivity)
      _ = ((N : ℝ) + 1) ^ 2 * (3 / 4) ^ N * (X N * Y N) := by ring
  · rw [Finset.sum_mul_sum]
    field_simp
    ring

/-- Moments of an `e`-weighted vector are shifted moments: `Σ(e_nF_n)e_n^a/r^a = r·Σ F_ne_n^{a+1}/r^{a+1}`. -/
theorem mom_shift (F e : ι → ℝ) {r : ℝ} (hr : 0 < r) (a : ℕ) :
    (∑ n, e n * F n * e n ^ a) / r ^ a = r * ((∑ n, F n * e n ^ (a + 1)) / r ^ (a + 1)) := by
  have hr' : r ^ a ≠ 0 := pow_ne_zero _ hr.ne'
  rw [pow_succ, mul_div_assoc', div_eq_div_iff hr' (mul_ne_zero hr' hr.ne')]
  rw [Finset.sum_mul, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun n _ => by ring

/-- `Σ|e_nF_n| ≤ rΣ|F_n|`. -/
theorem sum_abs_mul_le (F e : ι → ℝ) {r : ℝ} (he : ∀ n, |e n| ≤ r) :
    ∑ n, |e n * F n| ≤ r * ∑ n, |F n| := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun n _ => by rw [abs_mul]; exact mul_le_mul_of_nonneg_right (he n) (abs_nonneg _)

/-- **The pointwise pair deviation**: the decoupled Green integrand minus its leading term, bounded by the moment
majorants `ZK`, `ZL` and a remainder `O(M(3/4)^M)`. -/
theorem pair_dev_le (XV XP YV YP e : ι → ℝ) {c r A β₁ β₂ Ad γ₁ γ₂ w w' θ ω k l : ℝ}
    (hc : 0 < c) (hr : 0 < r) (he : ∀ n, |e n| ≤ r) (hβ₁ : 0 ≤ β₁) (hβ₂ : 0 ≤ β₂) (hA : A ≠ 0)
    (hq : r * (β₁ + β₂) / |A| ≤ 3 / 4) (hω₁ : |w' - 2 * w * θ * β₁| ≤ ω) (hω₂ : |w' - 2 * w * θ * β₂| ≤ ω)
    (hk : 0 ≤ k) (hl : 0 ≤ l) (ZK ZL : ℕ → ℝ)
    (hZK : ∀ N a, a ≤ N + 1 → |(∑ n, XV n * e n ^ a) / r ^ a| ≤ c * ZK N ∧ |(∑ n, XP n * e n ^ a) / r ^ a| ≤ ZK N)
    (hZL : ∀ N b, b ≤ N + 1 → |(∑ n, YV n * e n ^ b) / r ^ b| ≤ c * ZL N ∧ |(∑ n, YP n * e n ^ b) / r ^ b| ≤ ZL N)
    {M : ℕ} (hM : 1 ≤ M) :
    |((w' - 2 * w * θ * β₁) * k * B1s XV YP e A β₁ β₂ - (w' - 2 * w * θ * β₂) * l * B1s XP YV e A β₁ β₂
        - w * k * (Ad * B2s XV YP e A β₁ β₂ + γ₁ * B2s (fun i => e i * XV i) YP e A β₁ β₂
            - γ₂ * B2s XV (fun j => e j * YP j) e A β₁ β₂)
        + w * l * (Ad * B2s XP YV e A β₁ β₂ + γ₁ * B2s (fun i => e i * XP i) YV e A β₁ β₂
            - γ₂ * B2s XP (fun j => e j * YV j) e A β₁ β₂))
      - ((w' - 2 * w * θ * β₁) * k * ((∑ n, XV n) * (∑ m, YP m))
        - (w' - 2 * w * θ * β₂) * l * ((∑ n, XP n) * (∑ m, YV m))) / A|
      ≤ ((ω * k + ω * l) * c * (4 / 3 * (r * (β₁ + β₂) / |A|)) / |A|
          + |w| * (k + l) * (|Ad| * c + |γ₁| * (r * c) + |γ₂| * (r * c)) / A ^ 2)
          * ∑ N ∈ range M, ((N : ℝ) + 1) ^ 2 * (3 / 4) ^ N * (ZK N * ZL N)
        + (4 * (ω * k + ω * l) / |A| + 16 * |w| * (k + l) * (|Ad| + |γ₁| * r + |γ₂| * r) / A ^ 2)
          * ((2 * M + 1) * (3 / 4) ^ M) * ((∑ n, (|XV n| + |XP n|)) * (∑ m, (|YV m| + |YP m|))) := by
  set S := ∑ N ∈ range M, ((N : ℝ) + 1) ^ 2 * (3 / 4) ^ N * (ZK N * ZL N) with hS
  set SK := ∑ n, (|XV n| + |XP n|) with hSK
  set SL := ∑ m, (|YV m| + |YP m|) with hSL
  set T := ((2 * M + 1 : ℝ) * (3 / 4) ^ M) with hT
  set q₀ := r * (β₁ + β₂) / |A| with hq₀
  have hA' : 0 < |A| := abs_pos.mpr hA
  have hA2 : 0 < A ^ 2 := by positivity
  have hZK0 : ∀ N, 0 ≤ ZK N := fun N => (abs_nonneg _).trans (hZK N 0 (Nat.zero_le _)).2
  have hZL0 : ∀ N, 0 ≤ ZL N := fun N => (abs_nonneg _).trans (hZL N 0 (Nat.zero_le _)).2
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun N _ => mul_nonneg (by positivity) (mul_nonneg (hZK0 N) (hZL0 N))
  have hSK0 : 0 ≤ SK := Finset.sum_nonneg fun n _ => by positivity
  have hSL0 : 0 ≤ SL := Finset.sum_nonneg fun n _ => by positivity
  have hq0 : 0 ≤ q₀ := by positivity
  have hT0 : (3 / 4 : ℝ) ^ M ≤ T := by
    rw [hT]; have : (1 : ℝ) ≤ 2 * M + 1 := by have := (Nat.cast_nonneg M : (0 : ℝ) ≤ M); linarith
    nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4) M]
  -- sums of absolute values
  have hXV : ∑ n, |XV n| ≤ SK := (Finset.sum_le_sum fun n _ => le_add_of_nonneg_right (abs_nonneg _)).trans_eq hSK.symm
  have hXP : ∑ n, |XP n| ≤ SK := (Finset.sum_le_sum fun n _ => le_add_of_nonneg_left (abs_nonneg _)).trans_eq hSK.symm
  have hYV : ∑ n, |YV n| ≤ SL := (Finset.sum_le_sum fun n _ => le_add_of_nonneg_right (abs_nonneg _)).trans_eq hSL.symm
  have hYP : ∑ n, |YP n| ≤ SL := (Finset.sum_le_sum fun n _ => le_add_of_nonneg_left (abs_nonneg _)).trans_eq hSL.symm
  have hpair : ∀ {a b : ℝ}, 0 ≤ a → 0 ≤ b → a ≤ SK → b ≤ SL → a * b ≤ SK * SL := fun ha hb h1 h2 =>
    mul_le_mul h1 h2 hb hSK0
  -- the first-order sums
  have hS1 : ∀ (X Y : ℕ → ℝ), (∀ N, X N * Y N ≤ c * (ZK N * ZL N)) →
      ∑ N ∈ range M, ((N : ℝ) + 1) * (3 / 4) ^ N * (X N * Y N) ≤ c * S := by
    intro X Y hXY
    rw [hS, Finset.mul_sum]
    refine Finset.sum_le_sum fun N _ => ?_
    have h1 : ((N : ℝ) + 1) ≤ ((N : ℝ) + 1) ^ 2 := by nlinarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
    have h2 : 0 ≤ (3 / 4 : ℝ) ^ N := pow_nonneg (by norm_num) N
    have h3 : 0 ≤ ZK N * ZL N := mul_nonneg (hZK0 N) (hZL0 N)
    calc ((N : ℝ) + 1) * (3 / 4) ^ N * (X N * Y N) ≤ ((N : ℝ) + 1) * (3 / 4) ^ N * (c * (ZK N * ZL N)) :=
          mul_le_mul_of_nonneg_left (hXY N) (by positivity)
      _ = ((N : ℝ) + 1) * (c * (3 / 4) ^ N * (ZK N * ZL N)) := by ring
      _ ≤ ((N : ℝ) + 1) ^ 2 * (c * (3 / 4) ^ N * (ZK N * ZL N)) :=
          mul_le_mul_of_nonneg_right h1 (mul_nonneg (mul_nonneg hc.le h2) h3)
      _ = c * (((N : ℝ) + 1) ^ 2 * (3 / 4) ^ N * (ZK N * ZL N)) := by ring
  have hS2 : ∀ (X Y : ℕ → ℝ) (κ : ℝ), (∀ N, X N * Y N ≤ κ * (ZK N * ZL N)) →
      ∑ N ∈ range M, ((N : ℝ) + 1) ^ 2 * (3 / 4) ^ N * (X N * Y N) ≤ κ * S := by
    intro X Y κ hXY
    rw [hS, Finset.mul_sum]
    refine Finset.sum_le_sum fun N _ => ?_
    calc ((N : ℝ) + 1) ^ 2 * (3 / 4) ^ N * (X N * Y N) ≤ ((N : ℝ) + 1) ^ 2 * (3 / 4) ^ N * (κ * (ZK N * ZL N)) :=
          mul_le_mul_of_nonneg_left (hXY N) (by positivity)
      _ = κ * (((N : ℝ) + 1) ^ 2 * (3 / 4) ^ N * (ZK N * ZL N)) := by ring
  -- piece 1
  have h1 := B1s_dev_le XV YP e hA hr hβ₁ hβ₂ he hq (fun N => c * ZK N) ZL
    (fun N a ha => (hZK N a (by omega)).1) (fun N b hb => (hZL N b (by omega)).2) hM
  have h1' : |B1s XV YP e A β₁ β₂ - (∑ n, XV n) * (∑ m, YP m) / A|
      ≤ c * S * (4 / 3 * q₀) / |A| + 4 * (3 / 4) ^ M * (SK * SL) / |A| := by
    refine h1.trans (add_le_add ?_ ?_)
    · refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (by positivity)) hA'.le
      exact hS1 _ _ fun N => by ring_nf; exact le_rfl
    · refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (by positivity)) hA'.le
      exact hpair (Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.sum_nonneg fun _ _ => abs_nonneg _) hXV hYP
  have h2 := B1s_dev_le XP YV e hA hr hβ₁ hβ₂ he hq ZK (fun N => c * ZL N)
    (fun N a ha => (hZK N a (by omega)).2) (fun N b hb => (hZL N b (by omega)).1) hM
  have h2' : |B1s XP YV e A β₁ β₂ - (∑ n, XP n) * (∑ m, YV m) / A|
      ≤ c * S * (4 / 3 * q₀) / |A| + 4 * (3 / 4) ^ M * (SK * SL) / |A| := by
    refine h2.trans (add_le_add ?_ ?_)
    · refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (by positivity)) hA'.le
      exact hS1 _ _ fun N => by ring_nf; exact le_rfl
    · refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (by positivity)) hA'.le
      exact hpair (Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.sum_nonneg fun _ _ => abs_nonneg _) hXP hYV
  -- the second-order pieces
  have hsumeV : ∑ n, |(fun i => e i * XV i) n| ≤ r * SK :=
    (sum_abs_mul_le XV e he).trans (mul_le_mul_of_nonneg_left hXV hr.le)
  have hsumeP : ∑ n, |(fun i => e i * XP i) n| ≤ r * SK :=
    (sum_abs_mul_le XP e he).trans (mul_le_mul_of_nonneg_left hXP hr.le)
  have hsumeYV : ∑ n, |(fun i => e i * YV i) n| ≤ r * SL :=
    (sum_abs_mul_le YV e he).trans (mul_le_mul_of_nonneg_left hYV hr.le)
  have hsumeYP : ∑ n, |(fun i => e i * YP i) n| ≤ r * SL :=
    (sum_abs_mul_le YP e he).trans (mul_le_mul_of_nonneg_left hYP hr.le)
  have hB2 : ∀ (F G : ι → ℝ) (X Y : ℕ → ℝ) (κ ρF ρG : ℝ), 0 ≤ ρF → 0 ≤ ρG →
      (∀ N a, a ≤ N → |(∑ n, F n * e n ^ a) / r ^ a| ≤ X N) →
      (∀ N b, b ≤ N → |(∑ m, G m * e m ^ b) / r ^ b| ≤ Y N) →
      (∀ N, X N * Y N ≤ κ * (ZK N * ZL N)) → ∑ n, |F n| ≤ ρF * SK → ∑ m, |G m| ≤ ρG * SL →
      |B2s F G e A β₁ β₂| ≤ (κ * S + 16 * T * (ρF * ρG) * (SK * SL)) / A ^ 2 := by
    intro F G X Y κ ρF ρG hρF hρG hX hY hXY hF hG
    have h := B2s_le F G e hA hr hβ₁ hβ₂ he hq X Y hX hY M
    refine h.trans ?_
    rw [← add_div]
    refine div_le_div_of_nonneg_right (add_le_add (hS2 X Y κ hXY) ?_) hA2.le
    have : (∑ n, |F n|) * (∑ m, |G m|) ≤ (ρF * SK) * (ρG * SL) :=
      mul_le_mul hF hG (Finset.sum_nonneg fun _ _ => abs_nonneg _) (by positivity)
    rw [hT]
    nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4) M, (Nat.cast_nonneg M : (0 : ℝ) ≤ M)]
  have hmV : ∀ N a, a ≤ N → |(∑ n, (fun i => e i * XV i) n * e n ^ a) / r ^ a| ≤ r * c * ZK N := by
    intro N a ha
    rw [show (∑ n, (fun i => e i * XV i) n * e n ^ a) = ∑ n, e n * XV n * e n ^ a from rfl, mom_shift XV e hr,
      abs_mul, abs_of_pos hr, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hZK N (a + 1) (by omega)).1 hr.le
  have hmP : ∀ N a, a ≤ N → |(∑ n, (fun i => e i * XP i) n * e n ^ a) / r ^ a| ≤ r * ZK N := by
    intro N a ha
    rw [show (∑ n, (fun i => e i * XP i) n * e n ^ a) = ∑ n, e n * XP n * e n ^ a from rfl, mom_shift XP e hr,
      abs_mul, abs_of_pos hr]
    exact mul_le_mul_of_nonneg_left (hZK N (a + 1) (by omega)).2 hr.le
  have hmYV : ∀ N a, a ≤ N → |(∑ n, (fun i => e i * YV i) n * e n ^ a) / r ^ a| ≤ r * c * ZL N := by
    intro N a ha
    rw [show (∑ n, (fun i => e i * YV i) n * e n ^ a) = ∑ n, e n * YV n * e n ^ a from rfl, mom_shift YV e hr,
      abs_mul, abs_of_pos hr, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hZL N (a + 1) (by omega)).1 hr.le
  have hmYP : ∀ N a, a ≤ N → |(∑ n, (fun i => e i * YP i) n * e n ^ a) / r ^ a| ≤ r * ZL N := by
    intro N a ha
    rw [show (∑ n, (fun i => e i * YP i) n * e n ^ a) = ∑ n, e n * YP n * e n ^ a from rfl, mom_shift YP e hr,
      abs_mul, abs_of_pos hr]
    exact mul_le_mul_of_nonneg_left (hZL N (a + 1) (by omega)).2 hr.le
  have hZZ : ∀ N, 0 ≤ ZK N * ZL N := fun N => mul_nonneg (hZK0 N) (hZL0 N)
  have b1 := hB2 XV YP (fun N => c * ZK N) ZL c 1 1 zero_le_one zero_le_one
    (fun N a ha => (hZK N a (by omega)).1) (fun N b hb => (hZL N b (by omega)).2)
    (fun N => le_of_eq (by ring)) (by rw [one_mul]; exact hXV) (by rw [one_mul]; exact hYP)
  have b2 := hB2 (fun i => e i * XV i) YP (fun N => r * c * ZK N) ZL (r * c) r 1 hr.le zero_le_one hmV
    (fun N b hb => (hZL N b (by omega)).2) (fun N => le_of_eq (by ring)) hsumeV (by rw [one_mul]; exact hYP)
  have b3 := hB2 XV (fun j => e j * YP j) (fun N => c * ZK N) (fun N => r * ZL N) (r * c) 1 r zero_le_one hr.le
    (fun N a ha => (hZK N a (by omega)).1) hmYP (fun N => le_of_eq (by ring)) (by rw [one_mul]; exact hXV) hsumeYP
  have b4 := hB2 XP YV ZK (fun N => c * ZL N) c 1 1 zero_le_one zero_le_one
    (fun N a ha => (hZK N a (by omega)).2) (fun N b hb => (hZL N b (by omega)).1)
    (fun N => le_of_eq (by ring)) (by rw [one_mul]; exact hXP) (by rw [one_mul]; exact hYV)
  have b5 := hB2 (fun i => e i * XP i) YV (fun N => r * ZK N) (fun N => c * ZL N) (r * c) r 1 hr.le zero_le_one hmP
    (fun N b hb => (hZL N b (by omega)).1) (fun N => le_of_eq (by ring)) hsumeP (by rw [one_mul]; exact hYV)
  have b6 := hB2 XP (fun j => e j * YV j) ZK (fun N => r * c * ZL N) (r * c) 1 r zero_le_one hr.le
    (fun N a ha => (hZK N a (by omega)).2) hmYV (fun N => le_of_eq (by ring)) (by rw [one_mul]; exact hXP) hsumeYV
  -- assemble
  have key : ((w' - 2 * w * θ * β₁) * k * B1s XV YP e A β₁ β₂ - (w' - 2 * w * θ * β₂) * l * B1s XP YV e A β₁ β₂
        - w * k * (Ad * B2s XV YP e A β₁ β₂ + γ₁ * B2s (fun i => e i * XV i) YP e A β₁ β₂
            - γ₂ * B2s XV (fun j => e j * YP j) e A β₁ β₂)
        + w * l * (Ad * B2s XP YV e A β₁ β₂ + γ₁ * B2s (fun i => e i * XP i) YV e A β₁ β₂
            - γ₂ * B2s XP (fun j => e j * YV j) e A β₁ β₂))
      - ((w' - 2 * w * θ * β₁) * k * ((∑ n, XV n) * (∑ m, YP m))
        - (w' - 2 * w * θ * β₂) * l * ((∑ n, XP n) * (∑ m, YV m))) / A
      = (w' - 2 * w * θ * β₁) * k * (B1s XV YP e A β₁ β₂ - (∑ n, XV n) * (∑ m, YP m) / A)
        - (w' - 2 * w * θ * β₂) * l * (B1s XP YV e A β₁ β₂ - (∑ n, XP n) * (∑ m, YV m) / A)
        - w * k * (Ad * B2s XV YP e A β₁ β₂ + γ₁ * B2s (fun i => e i * XV i) YP e A β₁ β₂
            - γ₂ * B2s XV (fun j => e j * YP j) e A β₁ β₂)
        + w * l * (Ad * B2s XP YV e A β₁ β₂ + γ₁ * B2s (fun i => e i * XP i) YV e A β₁ β₂
            - γ₂ * B2s XP (fun j => e j * YV j) e A β₁ β₂) := by
    field_simp
    ring
  rw [key]
  have hω0 : 0 ≤ ω := (abs_nonneg _).trans hω₁
  have e1 : |(w' - 2 * w * θ * β₁) * k * (B1s XV YP e A β₁ β₂ - (∑ n, XV n) * (∑ m, YP m) / A)|
      ≤ ω * k * (c * S * (4 / 3 * q₀) / |A| + 4 * (3 / 4) ^ M * (SK * SL) / |A|) := by
    rw [abs_mul, abs_mul, abs_of_nonneg hk]
    exact mul_le_mul (mul_le_mul_of_nonneg_right hω₁ hk) h1' (abs_nonneg _) (mul_nonneg hω0 hk)
  have e2 : |(w' - 2 * w * θ * β₂) * l * (B1s XP YV e A β₁ β₂ - (∑ n, XP n) * (∑ m, YV m) / A)|
      ≤ ω * l * (c * S * (4 / 3 * q₀) / |A| + 4 * (3 / 4) ^ M * (SK * SL) / |A|) := by
    rw [abs_mul, abs_mul, abs_of_nonneg hl]
    exact mul_le_mul (mul_le_mul_of_nonneg_right hω₂ hl) h2' (abs_nonneg _) (mul_nonneg hω0 hl)
  have e3 : |w * k * (Ad * B2s XV YP e A β₁ β₂ + γ₁ * B2s (fun i => e i * XV i) YP e A β₁ β₂
            - γ₂ * B2s XV (fun j => e j * YP j) e A β₁ β₂)|
      ≤ |w| * k * (|Ad| * ((c * S + 16 * T * (1 * 1) * (SK * SL)) / A ^ 2)
        + |γ₁| * (((r * c) * S + 16 * T * (r * 1) * (SK * SL)) / A ^ 2)
        + |γ₂| * (((r * c) * S + 16 * T * (1 * r) * (SK * SL)) / A ^ 2)) := by
    rw [abs_mul, abs_mul, abs_of_nonneg hk]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine (abs_sub _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
    · rw [abs_mul]; exact mul_le_mul_of_nonneg_left b1 (abs_nonneg _)
    · rw [abs_mul]; exact mul_le_mul_of_nonneg_left b2 (abs_nonneg _)
    · rw [abs_mul]; exact mul_le_mul_of_nonneg_left b3 (abs_nonneg _)
  have e4 : |w * l * (Ad * B2s XP YV e A β₁ β₂ + γ₁ * B2s (fun i => e i * XP i) YV e A β₁ β₂
            - γ₂ * B2s XP (fun j => e j * YV j) e A β₁ β₂)|
      ≤ |w| * l * (|Ad| * ((c * S + 16 * T * (1 * 1) * (SK * SL)) / A ^ 2)
        + |γ₁| * (((r * c) * S + 16 * T * (r * 1) * (SK * SL)) / A ^ 2)
        + |γ₂| * (((r * c) * S + 16 * T * (1 * r) * (SK * SL)) / A ^ 2)) := by
    rw [abs_mul, abs_mul, abs_of_nonneg hl]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine (abs_sub _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
    · rw [abs_mul]; exact mul_le_mul_of_nonneg_left b4 (abs_nonneg _)
    · rw [abs_mul]; exact mul_le_mul_of_nonneg_left b5 (abs_nonneg _)
    · rw [abs_mul]; exact mul_le_mul_of_nonneg_left b6 (abs_nonneg _)
  have hgap : 0 ≤ 4 * (ω * k + ω * l) / |A| * ((T - (3 / 4) ^ M) * (SK * SL)) := by
    have := mul_nonneg (sub_nonneg.mpr hT0) (mul_nonneg hSK0 hSL0)
    positivity
  calc _ ≤ |(w' - 2 * w * θ * β₁) * k * (B1s XV YP e A β₁ β₂ - (∑ n, XV n) * (∑ m, YP m) / A)|
        + |(w' - 2 * w * θ * β₂) * l * (B1s XP YV e A β₁ β₂ - (∑ n, XP n) * (∑ m, YV m) / A)|
        + |w * k * (Ad * B2s XV YP e A β₁ β₂ + γ₁ * B2s (fun i => e i * XV i) YP e A β₁ β₂
            - γ₂ * B2s XV (fun j => e j * YP j) e A β₁ β₂)|
        + |w * l * (Ad * B2s XP YV e A β₁ β₂ + γ₁ * B2s (fun i => e i * XP i) YV e A β₁ β₂
            - γ₂ * B2s XP (fun j => e j * YV j) e A β₁ β₂)| := by
        refine (abs_add_le _ _).trans (add_le_add ((abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)) le_rfl)
    _ ≤ _ := add_le_add (add_le_add (add_le_add e1 e2) e3) e4
    _ = ((ω * k + ω * l) * c * (4 / 3 * q₀) / |A|
          + |w| * (k + l) * (|Ad| * c + |γ₁| * (r * c) + |γ₂| * (r * c)) / A ^ 2) * S
        + (4 * (ω * k + ω * l) / |A| + 16 * |w| * (k + l) * (|Ad| + |γ₁| * r + |γ₂| * r) / A ^ 2)
          * T * (SK * SL) - 4 * (ω * k + ω * l) / |A| * ((T - (3 / 4) ^ M) * (SK * SL)) := by
        field_simp
        ring
    _ ≤ _ := by linarith

/-- `(k + l)/|k² − l²|² ≤ 1/(7(k − l)²)` for distinct `k, l ≥ 3`. -/
theorem add_div_sq_le {k l : ℕ} (hk : 3 ≤ k) (hl : 3 ≤ l) (hkl : k ≠ l) :
    ((k : ℝ) + l) / |(k : ℝ) ^ 2 - (l : ℝ) ^ 2| ^ 2 ≤ 1 / (7 * ((k : ℝ) - l) ^ 2) := by
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hl' : (3 : ℝ) ≤ l := by exact_mod_cast hl
  have hd : ((k : ℝ) - l) ^ 2 ≠ 0 := by
    have : (k : ℝ) ≠ l := by exact_mod_cast hkl
    exact pow_ne_zero 2 (sub_ne_zero.mpr this)
  have hd0 : 0 < ((k : ℝ) - l) ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hd)
  rw [sq_abs, show (k : ℝ) ^ 2 - (l : ℝ) ^ 2 = ((k : ℝ) - l) * (k + l) by ring, mul_pow,
    div_le_div_iff₀ (by positivity) (by positivity)]
  have h7 : (7 : ℝ) ≤ k + l := by
    have : 7 ≤ k + l := by omega
    exact_mod_cast this
  have hp : 0 ≤ ((k : ℝ) - l) ^ 2 * (k + l) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h7 hp]

/-- **The pair coefficients**: the majorant coefficient decays like `1/(c(k − l)²)` and the remainder coefficient
is `O((k + l)/c²)`. -/
theorem coeff_le {c r A β₁ β₂ Ad γ₁ γ₂ w ω L βb : ℝ} {k l : ℕ} (hc : 0 < c) (hr : r = c ^ 2 / 2)
    (hk : 3 ≤ k) (hl : 3 ≤ l) (hkl : k ≠ l) (hA : c ^ 2 * |(k : ℝ) ^ 2 - (l : ℝ) ^ 2| / 2 ≤ |A|)
    (hβ : β₁ + β₂ ≤ 2 * βb) (_hβ₁ : 0 ≤ β₁) (_hβ₂ : 0 ≤ β₂) (hw : |w| ≤ 1) (hω : 0 ≤ ω)
    (hAd : |Ad| ≤ L * c ^ 2) (hγ₁ : |γ₁| ≤ 2 * L) (hγ₂ : |γ₂| ≤ 2 * L) (hβb : 0 ≤ βb) (hL : 0 ≤ L) :
    ((ω * k + ω * l) * c * (4 / 3 * (r * (β₁ + β₂) / |A|)) / |A|
          + |w| * (k + l) * (|Ad| * c + |γ₁| * (r * c) + |γ₂| * (r * c)) / A ^ 2)
        ≤ (16 * ω * βb / 21 + 12 * L / 7) / (c * ((k : ℝ) - l) ^ 2)
      ∧ (4 * (ω * k + ω * l) / |A| + 16 * |w| * (k + l) * (|Ad| + |γ₁| * r + |γ₂| * r) / A ^ 2)
        ≤ (k + l) * (8 * ω + 192 * L) / c ^ 2 := by
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hl' : (3 : ℝ) ≤ l := by exact_mod_cast hl
  set d := |(k : ℝ) ^ 2 - (l : ℝ) ^ 2| with hd
  have hd1 : 1 ≤ d := by
    rw [hd]
    rcases lt_or_gt_of_ne hkl with h | h
    · have : (k : ℝ) + 1 ≤ l := by exact_mod_cast h
      rw [abs_of_nonpos (by nlinarith)]; nlinarith
    · have : (l : ℝ) + 1 ≤ k := by exact_mod_cast h
      rw [abs_of_nonneg (by nlinarith)]; nlinarith
  have hd0 : 0 < d := by linarith
  have hc2 : 0 < c ^ 2 := by positivity
  have hA0 : 0 < |A| := lt_of_lt_of_le (by positivity) hA
  have hA2 : A ^ 2 = |A| ^ 2 := (sq_abs A).symm
  have hkl0 : (0 : ℝ) ≤ k + l := by linarith
  have hw0 : 0 ≤ |w| := abs_nonneg w
  -- `1/|A| ≤ 2/(c²d)` and `1/A² ≤ 4/(c⁴d²)`
  have hiA : 1 / |A| ≤ 2 / (c ^ 2 * d) := by
    rw [div_le_div_iff₀ hA0 (by positivity)]; linarith
  have hiA2 : 1 / A ^ 2 ≤ 4 / (c ^ 2 * d) ^ 2 := by
    rw [hA2, div_le_div_iff₀ (by positivity) (by positivity)]
    have : (c ^ 2 * d / 2) ^ 2 ≤ |A| ^ 2 := pow_le_pow_left₀ (by positivity) hA 2
    nlinarith
  constructor
  · have hfirst : (ω * k + ω * l) * c * (4 / 3 * (r * (β₁ + β₂) / |A|)) / |A|
        ≤ (k + l) * c ^ 3 * (4 / 3 * ω * βb) * (1 / A ^ 2) := by
      rw [hA2, hr]
      have : (c ^ 2 / 2) * (β₁ + β₂) ≤ c ^ 2 * βb := by nlinarith
      rw [show (ω * k + ω * l) * c * (4 / 3 * (c ^ 2 / 2 * (β₁ + β₂) / |A|)) / |A|
          = (k + l) * c * (4 / 3 * ω) * ((c ^ 2 / 2) * (β₁ + β₂)) * (1 / |A| ^ 2) by field_simp]
      rw [show (k + l) * c ^ 3 * (4 / 3 * ω * βb) * (1 / |A| ^ 2)
          = (k + l) * c * (4 / 3 * ω) * (c ^ 2 * βb) * (1 / |A| ^ 2) by ring]
      gcongr
    have hsecond : |w| * (k + l) * (|Ad| * c + |γ₁| * (r * c) + |γ₂| * (r * c)) / A ^ 2
        ≤ (k + l) * c ^ 3 * (3 * L) * (1 / A ^ 2) := by
      rw [hr]
      have h1 : |Ad| * c + |γ₁| * (c ^ 2 / 2 * c) + |γ₂| * (c ^ 2 / 2 * c) ≤ c ^ 3 * (3 * L) := by
        have := mul_le_mul_of_nonneg_right hAd hc.le
        have := mul_le_mul_of_nonneg_right hγ₁ (by positivity : (0 : ℝ) ≤ c ^ 2 / 2 * c)
        have := mul_le_mul_of_nonneg_right hγ₂ (by positivity : (0 : ℝ) ≤ c ^ 2 / 2 * c)
        nlinarith
      calc |w| * (k + l) * (|Ad| * c + |γ₁| * (c ^ 2 / 2 * c) + |γ₂| * (c ^ 2 / 2 * c)) / A ^ 2
          = |w| * (k + l) * (|Ad| * c + |γ₁| * (c ^ 2 / 2 * c) + |γ₂| * (c ^ 2 / 2 * c)) * (1 / A ^ 2) := by ring
        _ ≤ 1 * (k + l) * (c ^ 3 * (3 * L)) * (1 / A ^ 2) := by gcongr
        _ = (k + l) * c ^ 3 * (3 * L) * (1 / A ^ 2) := by ring
    have hsum : (k + l) * c ^ 3 * (4 / 3 * ω * βb) * (1 / A ^ 2) + (k + l) * c ^ 3 * (3 * L) * (1 / A ^ 2)
        ≤ (k + l) * c ^ 3 * (4 / 3 * ω * βb + 3 * L) * (4 / (c ^ 2 * d) ^ 2) := by
      rw [← add_mul, ← mul_add]
      gcongr
    have hfin : (k + l) * c ^ 3 * (4 / 3 * ω * βb + 3 * L) * (4 / (c ^ 2 * d) ^ 2)
        ≤ (16 * ω * βb / 21 + 12 * L / 7) / (c * ((k : ℝ) - l) ^ 2) := by
      have hkey := add_div_sq_le hk hl hkl
      rw [← hd] at hkey
      have hX : 0 ≤ 4 / 3 * ω * βb + 3 * L := by positivity
      have e : (k + l) * c ^ 3 * (4 / 3 * ω * βb + 3 * L) * (4 / (c ^ 2 * d) ^ 2)
          = (4 * (4 / 3 * ω * βb + 3 * L) / c) * ((k + l) / d ^ 2) := by
        field_simp
      rw [e]
      calc (4 * (4 / 3 * ω * βb + 3 * L) / c) * ((k + l) / d ^ 2)
          ≤ (4 * (4 / 3 * ω * βb + 3 * L) / c) * (1 / (7 * ((k : ℝ) - l) ^ 2)) :=
            mul_le_mul_of_nonneg_left hkey (by positivity)
        _ = (16 * ω * βb / 21 + 12 * L / 7) / (c * ((k : ℝ) - l) ^ 2) := by field_simp; ring
    linarith
  · have hfirst : 4 * (ω * k + ω * l) / |A| ≤ (k + l) * (8 * ω) / c ^ 2 := by
      rw [div_eq_mul_one_div]
      calc 4 * (ω * k + ω * l) * (1 / |A|) ≤ 4 * (ω * k + ω * l) * (2 / (c ^ 2 * d)) :=
            mul_le_mul_of_nonneg_left hiA (by positivity)
        _ ≤ 4 * (ω * k + ω * l) * (2 / (c ^ 2 * 1)) := by
            gcongr
        _ = (k + l) * (8 * ω) / c ^ 2 := by field_simp; ring
    have hsecond : 16 * |w| * (k + l) * (|Ad| + |γ₁| * r + |γ₂| * r) / A ^ 2 ≤ (k + l) * (192 * L) / c ^ 2 := by
      rw [hr]
      have h1 : |Ad| + |γ₁| * (c ^ 2 / 2) + |γ₂| * (c ^ 2 / 2) ≤ 3 * L * c ^ 2 := by
        have := mul_le_mul_of_nonneg_right hγ₁ (by positivity : (0 : ℝ) ≤ c ^ 2 / 2)
        have := mul_le_mul_of_nonneg_right hγ₂ (by positivity : (0 : ℝ) ≤ c ^ 2 / 2)
        nlinarith
      rw [div_eq_mul_one_div]
      calc 16 * |w| * (k + l) * (|Ad| + |γ₁| * (c ^ 2 / 2) + |γ₂| * (c ^ 2 / 2)) * (1 / A ^ 2)
          ≤ 16 * 1 * (k + l) * (3 * L * c ^ 2) * (4 / (c ^ 2 * d) ^ 2) := by
            gcongr
        _ ≤ 16 * 1 * (k + l) * (3 * L * c ^ 2) * (4 / (c ^ 2 * 1) ^ 2) := by
            gcongr
        _ = (k + l) * (192 * L) / c ^ 2 := by field_simp; ring
    have : (k + l) * (8 * ω) / c ^ 2 + (k + l) * (192 * L) / c ^ 2 = (k + l) * (8 * ω + 192 * L) / c ^ 2 := by
      ring
    linarith

end Cvs.Route.Visibility.AliasPairGreenIntegrand
