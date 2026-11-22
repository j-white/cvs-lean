import Mathlib
import Cvs.L2a.PositionTailEdgeRow
import Cvs.L2a.PositionTailPairsLowerEnd
import Cvs.L2a.PositionTailSquareIntegral
import Cvs.L2a.PositionTruncatedTail
import Cvs.Upstream.OffDiagonalHarmonicSum

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The truncation gap of the position-truncated tail

Under the hypotheses of Cvs.L2a.PositionTailSquareIntegral and `∫_b^{b'} ψ² ≤ T/b` for `1 ≤ b ≤ b'`: for `1 ≤ k ≤ X`, with `n = ⌊k⌋`,
`∫_{θ>1} (posTail ψ X − posTail ψ k)² ≤ (T + (4π²/3)rowC + (H_n + 2 + (16/9)(π²/6)²)B² + 14(H_n² + 2H_n + 2)BD/c²)/k`,
hence `≤ 18(T + rowC + B² + BD/c²)(2 + log k)²/k`.
-/

noncomputable section

open Real Set MeasureTheory

namespace Cvs.L2a.PositionTailTruncationGap

open Cvs.L2a.PositionTruncatedTail (posTail)
open Cvs.Upstream.OffDiagonalHarmonicSum (harm w harm_succ harm_nonneg sum_Icc_inv sum_w_top w_comm)

/-- Harmonic numbers are monotone. -/
lemma harm_mono {m n : ℕ} (h : m ≤ n) : harm m ≤ harm n :=
  monotone_nat_of_le_succ (fun n => by rw [harm_succ]; have : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) := by positivity
                                       linarith) h

/-- `harm n ≤ 1 + log n`. -/
lemma harm_le_log (n : ℕ) : harm n ≤ 1 + Real.log n := by
  have h := harmonic_le_one_add_log n
  rw [← sum_Icc_inv, harmonic_eq_sum_Icc] at *
  have e : ((∑ i ∈ Finset.Icc 1 n, (↑i : ℚ)⁻¹ : ℚ) : ℝ) = ∑ a ∈ Finset.Icc 1 n, 1 / (a : ℝ) := by
    push_cast; simp [one_div]
  rw [← e]; exact h

/-- `∑_{m=a+1}^{a+t} w(a,m) = (H_a + H_t − H_{a+t})/a²` for `a ≥ 1`. -/
lemma sum_w_above_eq (a t : ℕ) (ha : 1 ≤ a) :
    ∑ m ∈ Finset.Icc (a + 1) (a + t), w a m = (harm a + harm t - harm (a + t)) / (a : ℝ) ^ 2 := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  induction t with
  | zero => simp [harm]
  | succ t ih =>
    rw [← add_assoc, Finset.sum_Icc_succ_top (by omega), ih, harm_succ, harm_succ]
    unfold w
    push_cast
    rw [show (a : ℝ) - (a + t + 1) = -((t : ℝ) + 1) by ring, abs_neg, abs_of_pos (by positivity)]
    field_simp
    ring

/-- `∑_{a < m ≤ N} w(a,m) ≤ H_a/a²`. -/
lemma sum_w_above_le (a N : ℕ) (ha : 1 ≤ a) :
    ∑ m ∈ Finset.Icc (a + 1) N, w a m ≤ harm a / (a : ℝ) ^ 2 := by
  have h0 : ∀ m, 0 ≤ w a m := fun m => by unfold w; positivity
  calc _ ≤ ∑ m ∈ Finset.Icc (a + 1) (a + N), w a m :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc le_rfl (by omega)) fun _ _ _ => h0 _
    _ = _ := sum_w_above_eq a N ha
    _ ≤ _ := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        linarith [harm_mono (show N ≤ a + N by omega)]

/-- `∑_{m ≤ N, m ≠ a} w(a,m) ≤ 3H_a/a²` for `a ≥ 1`. -/
lemma sum_w_ne_le (a N : ℕ) (ha : 1 ≤ a) :
    ∑ m ∈ (Finset.Icc 1 N).filter (· ≠ a), w a m ≤ 3 * harm a / (a : ℝ) ^ 2 := by
  have h0 : ∀ m, 0 ≤ w a m := fun m => by unfold w; positivity
  obtain ⟨M, rfl⟩ : ∃ M, a = M + 1 := ⟨a - 1, by omega⟩
  have hsub : (Finset.Icc 1 N).filter (· ≠ M + 1) ⊆ Finset.Icc 1 M ∪ Finset.Icc (M + 1 + 1) N := by
    intro m hm; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_union] at hm ⊢; omega
  have hdis : Disjoint (Finset.Icc 1 M) (Finset.Icc (M + 1 + 1) N) := by
    rw [Finset.disjoint_left]; intro x h1 h2; simp only [Finset.mem_Icc] at h1 h2; omega
  have hlow : ∑ m ∈ Finset.Icc 1 M, w (M + 1) m = 2 * harm M / ((M : ℝ) + 1) ^ 2 := by
    rw [← sum_w_top]; exact Finset.sum_congr rfl fun m _ => w_comm _ _
  calc _ ≤ ∑ m ∈ Finset.Icc 1 M ∪ Finset.Icc (M + 1 + 1) N, w (M + 1) m :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => h0 _
    _ = _ := Finset.sum_union hdis
    _ ≤ 2 * harm (M + 1) / ((M + 1 : ℕ) : ℝ) ^ 2 + harm (M + 1) / ((M + 1 : ℕ) : ℝ) ^ 2 := by
        rw [hlow]
        refine add_le_add ?_ (sum_w_above_le _ _ (by omega))
        push_cast
        apply div_le_div_of_nonneg_right _ (by positivity)
        linarith [harm_mono (show M ≤ M + 1 by omega)]
    _ = _ := by ring

/-- `∑_{n < a ≤ N} 1/a² ≤ 1/n − 1/N` for `1 ≤ n ≤ N`. -/
lemma sum_inv_sq_tail (n N : ℕ) (hn : 1 ≤ n) (hN : n ≤ N) :
    ∑ a ∈ Finset.Icc (n + 1) N, 1 / (a : ℝ) ^ 2 ≤ 1 / (n : ℝ) - 1 / N := by
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ N hN ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hN0 : (1 : ℝ) ≤ N := by exact_mod_cast (le_trans hn hN)
    have key : 1 / ((N + 1 : ℕ) : ℝ) ^ 2 ≤ 1 / (N : ℝ) - 1 / ((N + 1 : ℕ) : ℝ) := by
      push_cast
      rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith

/-- `∑_{n < a ≤ N} H_a/a² ≤ (H_n + 1)/n − (H_N + 1)/N` for `1 ≤ n ≤ N`. -/
lemma sum_harm_sq_tail (n N : ℕ) (hn : 1 ≤ n) (hN : n ≤ N) :
    ∑ a ∈ Finset.Icc (n + 1) N, harm a / (a : ℝ) ^ 2 ≤ (harm n + 1) / n - (harm N + 1) / N := by
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ N hN ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hN0 : (1 : ℝ) ≤ N := by exact_mod_cast (le_trans hn hN)
    have hh := harm_nonneg N
    have key : harm (N + 1) / ((N + 1 : ℕ) : ℝ) ^ 2
        ≤ (harm N + 1) / N - (harm (N + 1) + 1) / ((N + 1 : ℕ) : ℝ) := by
      rw [harm_succ]
      push_cast
      have e : (harm N + 1) / (N : ℝ) - (harm N + 1 / ((N : ℝ) + 1) + 1) / ((N : ℝ) + 1)
          - (harm N + 1 / ((N : ℝ) + 1)) / ((N : ℝ) + 1) ^ 2
          = (harm N * ((N : ℝ) + 1) + 1) / ((N : ℝ) * ((N : ℝ) + 1) ^ 3) := by
        field_simp; ring
      have : 0 ≤ (harm N * ((N : ℝ) + 1) + 1) / ((N : ℝ) * ((N : ℝ) + 1) ^ 3) := by positivity
      linarith
    linarith

/-- The lower end `max(1, k/j)` of the `j`-th mode of the truncation gap. -/
def lowEnd (k : ℝ) (j : ℕ) : ℝ := max 1 (k / j)

/-- The gain `1/max(1, k/j)` of a pair whose smaller index is `j`. -/
def phi (k : ℝ) (j : ℕ) : ℝ := 1 / lowEnd k j

/-- Every lower end is at least `1`. -/
lemma one_le_lowEnd (k : ℝ) (j : ℕ) : 1 ≤ lowEnd k j := le_max_left _ _

/-- The gain is nonnegative. -/
lemma phi_nonneg (k : ℝ) (j : ℕ) : 0 ≤ phi k j := by
  unfold phi; have := one_le_lowEnd k j; positivity

/-- The gain is at most `1`. -/
lemma phi_le_one (k : ℝ) (j : ℕ) : phi k j ≤ 1 := by
  unfold phi; rw [div_le_one (by linarith [one_le_lowEnd k j])]; exact one_le_lowEnd k j

/-- The gain is at most `j/k`. -/
lemma phi_le_div {k : ℝ} (hk : 0 < k) {j : ℕ} (hj : 1 ≤ j) : phi k j ≤ j / k := by
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  unfold phi lowEnd
  calc 1 / max 1 (k / j) ≤ 1 / (k / j) := one_div_le_one_div_of_le (by positivity) (le_max_right _ _)
    _ = j / k := by rw [one_div_div]

/-- Splitting a `phi`-weighted sum at `n = ⌊k⌋`. -/
lemma sum_phi_le {k : ℝ} (hk : 1 ≤ k) {N : ℕ} (hN : ⌊k⌋₊ ≤ N) (g : ℕ → ℝ) (hg : ∀ a, 0 ≤ g a) :
    ∑ a ∈ Finset.Icc 1 N, phi k a * g a
      ≤ (1 / k) * ∑ a ∈ Finset.Icc 1 ⌊k⌋₊, (a : ℝ) * g a + ∑ a ∈ Finset.Icc (⌊k⌋₊ + 1) N, g a := by
  set n := ⌊k⌋₊
  have hk0 : 0 < k := by linarith
  have hsplit : Finset.Icc 1 N = Finset.Icc 1 n ∪ Finset.Icc (n + 1) N := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_union]; omega
  have hdis : Disjoint (Finset.Icc 1 n) (Finset.Icc (n + 1) N) := by
    rw [Finset.disjoint_left]; intro x h1 h2; simp only [Finset.mem_Icc] at h1 h2; omega
  rw [hsplit, Finset.sum_union hdis, Finset.mul_sum]
  refine add_le_add (Finset.sum_le_sum fun a ha => ?_) (Finset.sum_le_sum fun a _ => ?_)
  · have ha1 := (Finset.mem_Icc.mp ha).1
    calc phi k a * g a ≤ (a / k) * g a := mul_le_mul_of_nonneg_right (phi_le_div hk0 ha1) (hg a)
      _ = 1 / k * (a * g a) := by ring
  · calc phi k a * g a ≤ 1 * g a := mul_le_mul_of_nonneg_right (phi_le_one k a) (hg a)
      _ = g a := one_mul _

/-- `1/⌊k⌋ ≤ 2/k` for `k ≥ 1`. -/
lemma inv_floor_le {k : ℝ} (hk : 1 ≤ k) : 1 / (⌊k⌋₊ : ℝ) ≤ 2 / k := by
  have hn : (1 : ℝ) ≤ ⌊k⌋₊ := by exact_mod_cast Nat.le_floor (by exact_mod_cast hk)
  have hlt := Nat.lt_floor_add_one k
  rw [div_le_div_iff₀ (by linarith) (by linarith)]; linarith

/-- The diagonal weights: `∑_{a ≤ N} phi(a)/a² ≤ (H_n + 2)/k`, `n = ⌊k⌋`. -/
lemma sum_phi_diag_le {k : ℝ} (hk : 1 ≤ k) {N : ℕ} (hN : ⌊k⌋₊ ≤ N) :
    ∑ a ∈ Finset.Icc 1 N, phi k a * (1 / (a : ℝ) ^ 2) ≤ (harm ⌊k⌋₊ + 2) / k := by
  have hn : 1 ≤ ⌊k⌋₊ := Nat.le_floor (by exact_mod_cast hk)
  refine (sum_phi_le hk hN _ fun a => by positivity).trans ?_
  have e : ∑ a ∈ Finset.Icc 1 ⌊k⌋₊, (a : ℝ) * (1 / (a : ℝ) ^ 2) = harm ⌊k⌋₊ := by
    rw [← sum_Icc_inv]
    refine Finset.sum_congr rfl fun a ha => ?_
    have : (a : ℝ) ≠ 0 := by have := (Finset.mem_Icc.mp ha).1; positivity
    field_simp
  rw [e]
  have h1 := sum_inv_sq_tail _ _ hn hN
  have h2 := inv_floor_le hk
  have h3 : 0 ≤ 1 / (N : ℝ) := by positivity
  have h4 : (harm ⌊k⌋₊ + 2) / k = 1 / k * harm ⌊k⌋₊ + 2 / k := by ring
  rw [h4]; linarith

/-- The off-diagonal weights: `∑_{a ≤ N} phi(a)·3H_a/a² ≤ 3(H_n² + 2H_n + 2)/k`, `n = ⌊k⌋`. -/
lemma sum_phi_off_le {k : ℝ} (hk : 1 ≤ k) {N : ℕ} (hN : ⌊k⌋₊ ≤ N) :
    ∑ a ∈ Finset.Icc 1 N, phi k a * (3 * harm a / (a : ℝ) ^ 2)
      ≤ 3 * (harm ⌊k⌋₊ ^ 2 + 2 * harm ⌊k⌋₊ + 2) / k := by
  have hn : 1 ≤ ⌊k⌋₊ := Nat.le_floor (by exact_mod_cast hk)
  have hk0 : 0 < k := by linarith
  refine (sum_phi_le hk hN _ fun a => by have := harm_nonneg a; positivity).trans ?_
  have e1 : ∑ a ∈ Finset.Icc 1 ⌊k⌋₊, (a : ℝ) * (3 * harm a / (a : ℝ) ^ 2)
      ≤ 3 * harm ⌊k⌋₊ * harm ⌊k⌋₊ := by
    calc _ ≤ ∑ a ∈ Finset.Icc 1 ⌊k⌋₊, 3 * harm ⌊k⌋₊ * (1 / (a : ℝ)) := by
          refine Finset.sum_le_sum fun a ha => ?_
          have ha1 := Finset.mem_Icc.mp ha
          have : (0 : ℝ) < a := by exact_mod_cast ha1.1
          have hm := harm_mono ha1.2
          rw [show (a : ℝ) * (3 * harm a / (a : ℝ) ^ 2) = 3 * harm a * (1 / a) by field_simp]
          exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = _ := by rw [← Finset.mul_sum, sum_Icc_inv]
  have e2 : ∑ a ∈ Finset.Icc (⌊k⌋₊ + 1) N, 3 * harm a / (a : ℝ) ^ 2
      ≤ 3 * ((harm ⌊k⌋₊ + 1) / ⌊k⌋₊) := by
    have h := sum_harm_sq_tail _ _ hn hN
    have h0 : 0 ≤ (harm N + 1) / N := by have := harm_nonneg N; positivity
    rw [show ∑ a ∈ Finset.Icc (⌊k⌋₊ + 1) N, 3 * harm a / (a : ℝ) ^ 2
        = 3 * ∑ a ∈ Finset.Icc (⌊k⌋₊ + 1) N, harm a / (a : ℝ) ^ 2 by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring]
    linarith
  have h2 := inv_floor_le hk
  have hH := harm_nonneg ⌊k⌋₊
  have e3 : (harm ⌊k⌋₊ + 1) / ⌊k⌋₊ ≤ (harm ⌊k⌋₊ + 1) * (2 / k) := by
    rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left h2 (by linarith)
  have e4 : 3 * (harm ⌊k⌋₊ ^ 2 + 2 * harm ⌊k⌋₊ + 2) / k
      = 1 / k * (3 * harm ⌊k⌋₊ * harm ⌊k⌋₊) + 3 * ((harm ⌊k⌋₊ + 1) * (2 / k)) := by ring
  rw [e4]
  have := mul_le_mul_of_nonneg_left e1 (show 0 ≤ 1 / k by positivity)
  linarith

/-- The edge row from a lower end `b1 ≥ 1`: `|∫_{b1}^{b2} ψ(θ)ψ(mθ)| ≤ 4·rowC/(m² b1)` for `m ≥ 2`. -/
theorem abs_integral_row_gap_le {ψ v v' : ℝ → ℝ} {c χ m b1 b2 A A₁ B D κ : ℝ}
    (hψ : ∀ ξ, HasDerivAt ψ (v ξ) ξ) (hv : ∀ ξ, HasDerivAt v (v' ξ) ξ) (hvc : Continuous v')
    (hode : ∀ ξ, (ξ ^ 2 - 1) * v' ξ + 2 * ξ * v ξ + (c ^ 2 * ξ ^ 2 - χ) * ψ ξ = 0)
    (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχ : χ ≤ c ^ 2) (hm : 2 ≤ m) (hb1 : 1 ≤ b1) (hb12 : b1 ≤ b2)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hq : ∀ ξ, 2 ≤ ξ → κ * c ^ 2 * ξ ^ 2 ≤ c ^ 2 * ξ ^ 2 - χ)
    (hA : ∀ θ ∈ Icc (1 : ℝ) 2, |ψ θ| ≤ A) (hA₁ : ∫ θ in (1 : ℝ)..2, |v θ| ≤ A₁) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hψB : ∀ ξ, 2 ≤ ξ → |ψ ξ| ≤ B / ξ) (hvD : ∀ ξ, 2 ≤ ξ → |v ξ| ≤ D / ξ) :
    |∫ θ in b1..b2, ψ θ * ψ (m * θ)| ≤ 4 * Cvs.L2a.PositionTailEdgeRow.rowC c A A₁ B D κ / m ^ 2 / b1 := by
  set R := Cvs.L2a.PositionTailEdgeRow.rowC c A A₁ B D κ with hR
  have hm0 : 0 < m := by linarith
  have hb10 : 0 < b1 := by linarith
  have hψc : Continuous ψ := continuous_iff_continuousAt.2 fun ξ => (hψ ξ).continuousAt
  have hcont : Continuous fun θ => ψ θ * ψ (m * θ) := hψc.mul (hψc.comp (continuous_const.mul continuous_id))
  have hc2 : 0 < c ^ 2 := by positivity
  rcases lt_or_ge b1 2 with h2 | h2
  · have hrow := fun b (hb : 1 ≤ b) => Cvs.L2a.PositionTailEdgeRow.abs_integral_row_le (b := b) hψ hv hvc hode hc
      hχ0 hχ hm hb hκ hκ1 hq hA hA₁ hB hD hψB hvD
    have e := intervalIntegral.integral_interval_sub_left (a := (1 : ℝ)) (b := b2) (c := b1)
      (hcont.intervalIntegrable (μ := volume) _ _) (hcont.intervalIntegrable (μ := volume) _ _)
    rw [← e]
    have h1 := hrow b2 (by linarith)
    have h3 := hrow b1 hb1
    have hR0 : 0 ≤ R / m ^ 2 := le_trans (abs_nonneg _) h1
    calc _ ≤ |∫ θ in (1 : ℝ)..b2, ψ θ * ψ (m * θ)| + |∫ θ in (1 : ℝ)..b1, ψ θ * ψ (m * θ)| := abs_sub _ _
      _ ≤ 2 * (R / m ^ 2) := by linarith
      _ ≤ 4 * R / m ^ 2 / b1 := by
          rw [show 4 * R / m ^ 2 / b1 = (R / m ^ 2) * (4 / b1) by ring]
          rw [mul_comm 2 (R / m ^ 2)]
          refine mul_le_mul_of_nonneg_left ?_ hR0
          rw [le_div_iff₀ hb10]; linarith
  · have hscale : ∫ θ in b1..b2, ψ θ * ψ (m * θ)
        = 2 * ∫ u in b1 / 2..b2 / 2, ψ (2 * u) * ψ ((2 * m) * u) := by
      have h := intervalIntegral.integral_comp_mul_left (a := b1 / 2) (b := b2 / 2)
        (fun θ => ψ θ * ψ (m * θ)) (c := 2) (by norm_num)
      rw [show 2 * (b1 / 2) = b1 by ring, show 2 * (b2 / 2) = b2 by ring] at h
      have e : ∫ u in b1 / 2..b2 / 2, ψ (2 * u) * ψ ((2 * m) * u)
          = ∫ u in b1 / 2..b2 / 2, ψ (2 * u) * ψ (m * (2 * u)) := by
        congr 1; funext u; ring_nf
      rw [e, h, smul_eq_mul]; ring
    have hfar := Cvs.L2a.PositionTailPairsLowerEnd.abs_integral_far_le (a := 2) (m := 2 * m) (b1 := b1 / 2) (b2 := b2 / 2)
      hψ hv hvc hode hc hχ0 hχ le_rfl (by linarith) (by linarith) (by linarith) (by linarith) hB hD hψB hvD
    have hd : |(2 : ℝ) - 2 * m| = 2 * m - 2 := by rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    rw [hd] at hfar
    have hf1 : 14 / 3 * (B * D) / (c ^ 2 * (2 * (2 * m) * (2 * m - 2))) ≤ 7 / 6 * (B * D) / c ^ 2 / m ^ 2 := by
      have hden : c ^ 2 * (4 * m ^ 2) ≤ c ^ 2 * (2 * (2 * m) * (2 * m - 2)) :=
        mul_le_mul_of_nonneg_left (by nlinarith) hc2.le
      calc 14 / 3 * (B * D) / (c ^ 2 * (2 * (2 * m) * (2 * m - 2)))
          ≤ 14 / 3 * (B * D) / (c ^ 2 * (4 * m ^ 2)) :=
            div_le_div_of_nonneg_left (by positivity) (by positivity) hden
        _ = 7 / 6 * (B * D) / c ^ 2 / m ^ 2 := by field_simp; ring
    have hf2 : 16 / 9 * (B ^ 2 / ((2 : ℝ) ^ 3 * (2 * m) ^ 3)) ≤ B ^ 2 / 36 / m ^ 2 := by
      rw [div_div, show (16 : ℝ) / 9 * (B ^ 2 / ((2 : ℝ) ^ 3 * (2 * m) ^ 3)) = B ^ 2 / (36 * m ^ 3)
        by field_simp; ring]
      exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by nlinarith)
    have hsum : 7 / 6 * (B * D) / c ^ 2 / m ^ 2 + B ^ 2 / 36 / m ^ 2 ≤ R / 2 / m ^ 2 := by
      rw [← add_div]
      apply div_le_div_of_nonneg_right _ (by positivity)
      rw [hR]; unfold Cvs.L2a.PositionTailEdgeRow.rowC
      have : 0 ≤ D * (6 * A / κ + 2 * A₁ / κ + 2 * A / κ ^ 2) / c ^ 2 := by
        have hA0 : 0 ≤ A := le_trans (abs_nonneg _) (hA 1 ⟨le_rfl, by norm_num⟩)
        have hA₁0 : 0 ≤ A₁ :=
          le_trans (intervalIntegral.integral_nonneg (by norm_num) fun _ _ => abs_nonneg _) hA₁
        positivity
      have : 0 ≤ (B * D) / c ^ 2 := by positivity
      have e : 7 / 6 * (B * D) / c ^ 2 = 7 / 6 * ((B * D) / c ^ 2) := by ring
      have e2 : 7 / 3 * (B * D) / c ^ 2 = 7 / 3 * ((B * D) / c ^ 2) := by ring
      rw [e, e2]; nlinarith [sq_nonneg B]
    have hg := hfar.trans (div_le_div_of_nonneg_right (add_le_add hf1 hf2) (by linarith : (0 : ℝ) ≤ b1 / 2))
    have hg2 := hg.trans (div_le_div_of_nonneg_right hsum (by linarith : (0 : ℝ) ≤ b1 / 2))
    rw [hscale, abs_mul, abs_two]
    calc 2 * |∫ u in b1 / 2..b2 / 2, ψ (2 * u) * ψ ((2 * m) * u)| ≤ 2 * (R / 2 / m ^ 2 / (b1 / 2)) := by linarith
      _ = 2 * R / m ^ 2 / b1 := by field_simp
      _ ≤ 4 * R / m ^ 2 / b1 := by
          have hR0 : 0 ≤ R / 2 / m ^ 2 / (b1 / 2) := le_trans (abs_nonneg _) hg2
          have hR0' : 0 ≤ R := by
            have : 0 < m ^ 2 * b1 := by positivity
            have e : R / 2 / m ^ 2 / (b1 / 2) = R / (m ^ 2 * b1) := by field_simp
            rw [e] at hR0; exact (div_nonneg_iff.mp hR0).elim (fun h => h.1) fun h => absurd h.2 (not_le.2 this)
          gcongr; norm_num

/-- The `m`-th mode of the truncation gap: `ψ(mθ)` on `(max(1, k/m), X/m]`. -/
def gapMode (ψ : ℝ → ℝ) (k X : ℝ) (m : ℕ) (θ : ℝ) : ℝ :=
  Set.indicator (Ioc (lowEnd k m) (X / m)) (fun θ => ψ (m * θ)) θ

/-- The pair integral of the truncation gap: `∫ ψ(aθ)ψ(mθ)` over the intersection of the two mode supports. -/
def gapPair (ψ : ℝ → ℝ) (k X : ℝ) (a m : ℕ) : ℝ :=
  ∫ θ in Ioc (max (lowEnd k a) (lowEnd k m)) (min (X / a) (X / m)), ψ (a * θ) * ψ (m * θ)

/-- **The truncation gap is the sum of its modes**: `posTail ψ X − posTail ψ k = Σ_{m ≤ ⌊X⌋} gapMode m`. -/
theorem posTail_sub_eq_sum (ψ : ℝ → ℝ) {k X : ℝ} (hk : 1 ≤ k) (hkX : k ≤ X) (θ : ℝ) :
    posTail ψ X θ - posTail ψ k θ = ∑ m ∈ Finset.Icc 1 ⌊X⌋₊, gapMode ψ k X m θ := by
  rw [Cvs.L2a.PositionTruncatedTail.posTail_eq_sum, Cvs.L2a.PositionTruncatedTail.posTail_eq_sum]
  have hext : ∑ m ∈ Finset.Icc 1 ⌊k⌋₊, Set.indicator (Ioc 1 (k / m)) (fun θ => ψ (m * θ)) θ
      = ∑ m ∈ Finset.Icc 1 ⌊X⌋₊, Set.indicator (Ioc 1 (k / m)) (fun θ => ψ (m * θ)) θ := by
    refine Finset.sum_subset (Finset.Icc_subset_Icc le_rfl (Nat.floor_le_floor hkX)) fun m hm hn => ?_
    have hm1 := (Finset.mem_Icc.mp hm).1
    have hlt : ⌊k⌋₊ < m := by simp only [Finset.mem_Icc, not_and, not_le] at hn; exact hn hm1
    have hkm : k < m := Nat.lt_of_floor_lt hlt
    have hm0 : (0 : ℝ) < m := by linarith
    have : Ioc (1 : ℝ) (k / m) = ∅ := Ioc_eq_empty (not_lt.2 (by rw [div_le_one hm0]; linarith))
    rw [this, indicator_empty]
  rw [hext, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
  have hkXm : k / m ≤ X / m := div_le_div_of_nonneg_right hkX hm0.le
  unfold gapMode lowEnd
  simp only [Set.indicator, Set.mem_Ioc, max_lt_iff]
  rcases le_or_gt θ 1 with ha | ha
  · simp [not_lt.2 ha]
  rcases le_or_gt θ (k / m) with hb | hb
  · have hc : θ ≤ X / m := hb.trans hkXm
    simp [ha, hb, hc, not_lt.2 hb]
  · rcases le_or_gt θ (X / m) with hc | hc
    · simp [ha, hb, hc, not_le.2 hb]
    · simp [ha, hb, not_le.2 hb, not_le.2 hc]

/-- A set integral over `(b1, b2]` is at most `β ≥ 0` when the interval integral is, for `b1 ≤ b2`. -/
lemma setIntegral_Ioc_le {f : ℝ → ℝ} {b1 b2 β : ℝ} (hβ : 0 ≤ β)
    (h : b1 ≤ b2 → ∫ θ in b1..b2, f θ ≤ β) : ∫ θ in Ioc b1 b2, f θ ≤ β := by
  by_cases h12 : b1 ≤ b2
  · rw [← intervalIntegral.integral_of_le h12]; exact h h12
  · rw [Ioc_eq_empty (fun h' => h12 h'.le)]; simpa using hβ

/-- The first mode starts at `k`. -/
lemma lowEnd_one {k : ℝ} (hk : 1 ≤ k) : lowEnd k 1 = k := by
  unfold lowEnd; rw [Nat.cast_one, div_one, max_eq_right hk]

/-- The gain of a pair is at most the gain of either index. -/
lemma one_div_max_le_phi (k : ℝ) (a m : ℕ) : 1 / max (lowEnd k a) (lowEnd k m) ≤ phi k a :=
  one_div_le_one_div_of_le (by linarith [one_le_lowEnd k a]) (le_max_left _ _)

/-- **The truncation gap of the position-truncated tail**: for `1 ≤ k ≤ X`,
`∫_{θ>1} (posTail ψ X − posTail ψ k)² ≤ (T + (4π²/3)·rowC + (H_n + 2 + (16/9)(π²/6)²)B² + 14(H_n² + 2H_n + 2)BD/c²)/k`,
`n = ⌊k⌋`. -/
theorem integral_posTail_gap_le {ψ v v' : ℝ → ℝ} {c χ A A₁ B D κ T k X : ℝ}
    (hψ : ∀ ξ, HasDerivAt ψ (v ξ) ξ) (hv : ∀ ξ, HasDerivAt v (v' ξ) ξ) (hvc : Continuous v')
    (hode : ∀ ξ, (ξ ^ 2 - 1) * v' ξ + 2 * ξ * v ξ + (c ^ 2 * ξ ^ 2 - χ) * ψ ξ = 0)
    (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχ : χ ≤ c ^ 2) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hq : ∀ ξ, 2 ≤ ξ → κ * c ^ 2 * ξ ^ 2 ≤ c ^ 2 * ξ ^ 2 - χ)
    (hA : ∀ θ ∈ Icc (1 : ℝ) 2, |ψ θ| ≤ A) (hA₁ : ∫ θ in (1 : ℝ)..2, |v θ| ≤ A₁) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hψB : ∀ ξ, 2 ≤ ξ → |ψ ξ| ≤ B / ξ) (hvD : ∀ ξ, 2 ≤ ξ → |v ξ| ≤ D / ξ)
    (hT : ∀ b b', 1 ≤ b → b ≤ b' → ∫ θ in b..b', ψ θ ^ 2 ≤ T / b) (hk : 1 ≤ k) (hkX : k ≤ X) :
    ∫ θ in Ioi 1, (posTail ψ X θ - posTail ψ k θ) ^ 2
      ≤ (T + 4 * π ^ 2 / 3 * Cvs.L2a.PositionTailEdgeRow.rowC c A A₁ B D κ
          + (harm ⌊k⌋₊ + 2 + 16 / 9 * (π ^ 2 / 6) ^ 2) * B ^ 2
          + 14 * (harm ⌊k⌋₊ ^ 2 + 2 * harm ⌊k⌋₊ + 2) * (B * D) / c ^ 2) / k := by
  have hψc : Continuous ψ := continuous_iff_continuousAt.2 fun ξ => (hψ ξ).continuousAt
  set N := ⌊X⌋₊ with hN
  set n := ⌊k⌋₊ with hn
  set R := Cvs.L2a.PositionTailEdgeRow.rowC c A A₁ B D κ with hR
  set K := 14 / 3 * (B * D) / c ^ 2 with hK
  set P : ℕ → ℕ → ℝ := fun a m => gapPair ψ k X a m with hP
  have hk0 : 0 < k := by linarith
  have hnN : n ≤ N := Nat.floor_le_floor hkX
  have hn1 : 1 ≤ n := Nat.le_floor (by exact_mod_cast hk)
  have hN1 : 1 ≤ N := le_trans hn1 hnN
  have hA0 : 0 ≤ A := le_trans (abs_nonneg _) (hA 1 ⟨le_rfl, by norm_num⟩)
  have hA₁0 : 0 ≤ A₁ :=
    le_trans (intervalIntegral.integral_nonneg (by norm_num) fun _ _ => abs_nonneg _) hA₁
  have hR0 : 0 ≤ R := by rw [hR]; unfold Cvs.L2a.PositionTailEdgeRow.rowC; positivity
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hT0 : 0 ≤ T := by have := hT 1 1 le_rfl le_rfl; simpa using this
  -- the pairing formula
  have hpt : ∀ θ, (posTail ψ X θ - posTail ψ k θ) ^ 2 = ∑ a ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N,
      Set.indicator (Ioc (max (lowEnd k a) (lowEnd k m)) (min (X / a) (X / m)))
        (fun θ => ψ (a * θ) * ψ (m * θ)) θ := by
    intro θ
    rw [posTail_sub_eq_sum ψ hk hkX, sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun m _ => ?_
    unfold gapMode
    rw [← inter_indicator_mul, Set.Ioc_inter_Ioc]
  have hterm : ∀ a m : ℕ, Integrable (Set.indicator (Ioc (max (lowEnd k a) (lowEnd k m)) (min (X / a) (X / m)))
      (fun θ => ψ (a * θ) * ψ (m * θ))) := by
    intro a m
    have hc' : Continuous fun θ : ℝ => ψ (a * θ) * ψ (m * θ) :=
      (hψc.comp (continuous_const.mul continuous_id)).mul (hψc.comp (continuous_const.mul continuous_id))
    exact (integrable_indicator_iff measurableSet_Ioc).2
      ((hc'.continuousOn.integrableOn_Icc).mono_set Ioc_subset_Icc_self)
  have hsum_int : Integrable (fun θ => ∑ a ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N,
      Set.indicator (Ioc (max (lowEnd k a) (lowEnd k m)) (min (X / a) (X / m)))
        (fun θ => ψ (a * θ) * ψ (m * θ)) θ) :=
    integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun m _ => hterm a m
  have hkey : ∫ θ in Ioi 1, (posTail ψ X θ - posTail ψ k θ) ^ 2
      ≤ ∑ a ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N, P a m := by
    simp_rw [hpt]
    refine (setIntegral_le_integral hsum_int (Filter.Eventually.of_forall fun θ => ?_)).trans (le_of_eq ?_)
    · have := sq_nonneg (posTail ψ X θ - posTail ψ k θ)
      rw [hpt θ] at this; simpa using this
    · rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun m _ => hterm a m]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [integral_finsetSum _ fun m _ => hterm a m]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [integral_indicator measurableSet_Ioc]; rfl
  -- lower ends
  have hb1 : ∀ a m : ℕ, 1 ≤ max (lowEnd k a) (lowEnd k m) := fun a m =>
    le_trans (one_le_lowEnd k a) (le_max_left _ _)
  have hbk1 : ∀ m : ℕ, k ≤ max (lowEnd k 1) (lowEnd k m) := fun m =>
    (lowEnd_one hk).ge.trans (le_max_left _ _)
  have hbk2 : ∀ a : ℕ, k ≤ max (lowEnd k a) (lowEnd k 1) := fun a =>
    (lowEnd_one hk).ge.trans (le_max_right _ _)
  -- the (1,1) pair
  have h11 : P 1 1 ≤ T / k := by
    simp only [hP, gapPair, Nat.cast_one, one_mul]
    refine setIntegral_Ioc_le (by positivity) fun h12 => ?_
    have h := hT _ _ (hb1 1 1) h12
    simp only [← sq]
    refine h.trans (div_le_div_of_nonneg_left hT0 hk0 ?_)
    simpa using hbk1 1
  -- the edge rows
  have hrow : ∀ m ∈ Finset.Icc 2 N, P 1 m ≤ 4 * R * (1 / (m : ℝ) ^ 2) * (1 / k) := by
    intro m hm
    have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
    simp only [hP, gapPair, Nat.cast_one, one_mul]
    refine setIntegral_Ioc_le (by positivity) fun h12 => ?_
    have h := abs_integral_row_gap_le hψ hv hvc hode hc hχ0 hχ hm2 (hb1 1 m) h12 hκ hκ1 hq hA hA₁ hB hD hψB hvD
    refine (le_abs_self _).trans (h.trans ?_)
    rw [show 4 * R * (1 / (m : ℝ) ^ 2) * (1 / k) = 4 * R / m ^ 2 / k by ring]
    exact div_le_div_of_nonneg_left (by positivity) hk0 (by simpa using hbk1 m)
  have hcol : ∀ a ∈ Finset.Icc 2 N, P a 1 ≤ 4 * R * (1 / (a : ℝ) ^ 2) * (1 / k) := by
    intro a ha
    have ha2 : (2 : ℝ) ≤ a := by exact_mod_cast (Finset.mem_Icc.mp ha).1
    simp only [hP, gapPair, Nat.cast_one, one_mul]
    refine setIntegral_Ioc_le (by positivity) fun h12 => ?_
    have h := abs_integral_row_gap_le hψ hv hvc hode hc hχ0 hχ ha2 (hb1 a 1) h12 hκ hκ1 hq hA hA₁ hB hD hψB hvD
    simp_rw [mul_comm (ψ (a * _)) (ψ _)]
    refine (le_abs_self _).trans (h.trans ?_)
    rw [show 4 * R * (1 / (a : ℝ) ^ 2) * (1 / k) = 4 * R / a ^ 2 / k by ring]
    exact div_le_div_of_nonneg_left (by positivity) hk0 (by simpa using hbk2 a)
  -- the diagonal
  have hdiag : ∀ a ∈ Finset.Icc 2 N, P a a ≤ B ^ 2 * (phi k a * (1 / (a : ℝ) ^ 2)) := by
    intro a ha
    have ha2 : (2 : ℝ) ≤ a := by exact_mod_cast (Finset.mem_Icc.mp ha).1
    simp only [hP, gapPair]
    refine setIntegral_Ioc_le (by have := phi_nonneg k a; positivity) fun h12 => ?_
    have h := Cvs.L2a.PositionTailPairsLowerEnd.integral_diag_le ha2 (hb1 a a) h12 hψc hψB
    simp only [← sq]
    refine h.trans ?_
    have hp := one_div_max_le_phi k a a
    have hb0 : 0 < max (lowEnd k a) (lowEnd k a) := by linarith [hb1 a a]
    rw [show B ^ 2 / ((a : ℝ) ^ 2 * max (lowEnd k a) (lowEnd k a))
        = B ^ 2 * (1 / (a : ℝ) ^ 2) * (1 / max (lowEnd k a) (lowEnd k a)) by field_simp]
    rw [show B ^ 2 * (phi k a * (1 / (a : ℝ) ^ 2)) = B ^ 2 * (1 / (a : ℝ) ^ 2) * phi k a by ring]
    exact mul_le_mul_of_nonneg_left hp (by positivity)
  -- the far off-diagonal pairs
  have hfar : ∀ a ∈ Finset.Icc 2 N, ∀ m ∈ (Finset.Icc 2 N).erase a,
      P a m ≤ K * (phi k a * w a m) + 16 / 9 * B ^ 2 * (1 / (a : ℝ) ^ 2 * (1 / (m : ℝ) ^ 2)) * (1 / k) := by
    intro a ha m hm
    have ha' := Finset.mem_Icc.mp ha
    have hmne := (Finset.mem_erase.mp hm).1
    have hm' := Finset.mem_Icc.mp (Finset.mem_erase.mp hm).2
    have ha2 : (2 : ℝ) ≤ a := by exact_mod_cast ha'.1
    have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm'.1
    have hw0 : 0 ≤ w a m := by unfold w; positivity
    have hφ0 := phi_nonneg k a
    simp only [hP, gapPair]
    refine setIntegral_Ioc_le (by positivity) fun h12 => ?_
    have h := Cvs.L2a.PositionTailPairsLowerEnd.abs_integral_far_le (a := (a : ℝ)) (m := (m : ℝ)) hψ hv hvc hode hc hχ0 hχ
      ha2 hm2 (by exact_mod_cast (Ne.symm hmne)) (hb1 a m) h12 hB hD hψB hvD
    have e1 : 14 / 3 * (B * D) / (c ^ 2 * ((a : ℝ) * m * |(a : ℝ) - m|)) = K * w a m := by
      unfold w; rw [hK, mul_one_div, div_div]
    rw [e1] at h
    refine (le_abs_self _).trans (h.trans ?_)
    set b := max (lowEnd k a) (lowEnd k m)
    have hb0 : 0 < b := by linarith [hb1 a m]
    have hp : 1 / b ≤ phi k a := one_div_max_le_phi k a m
    have hpk : phi k a ≤ a / k := phi_le_div hk0 (by omega)
    have hE0 : 0 ≤ 16 / 9 * (B ^ 2 / ((a : ℝ) ^ 3 * (m : ℝ) ^ 3)) := by positivity
    have ha0 : (0 : ℝ) < a := by linarith
    have hm0 : (0 : ℝ) < m := by linarith
    calc (K * w a m + 16 / 9 * (B ^ 2 / ((a : ℝ) ^ 3 * (m : ℝ) ^ 3))) / b
        = (K * w a m + 16 / 9 * (B ^ 2 / ((a : ℝ) ^ 3 * (m : ℝ) ^ 3))) * (1 / b) := by ring
      _ ≤ (K * w a m + 16 / 9 * (B ^ 2 / ((a : ℝ) ^ 3 * (m : ℝ) ^ 3))) * phi k a :=
          mul_le_mul_of_nonneg_left hp (by positivity)
      _ = K * (phi k a * w a m) + 16 / 9 * (B ^ 2 / ((a : ℝ) ^ 3 * (m : ℝ) ^ 3)) * phi k a := by ring
      _ ≤ K * (phi k a * w a m) + 16 / 9 * (B ^ 2 / ((a : ℝ) ^ 3 * (m : ℝ) ^ 3)) * (a / k) := by
          gcongr
      _ ≤ _ := by
          gcongr ?_ + ?_
          · exact le_rfl
          · rw [show 16 / 9 * (B ^ 2 / ((a : ℝ) ^ 3 * (m : ℝ) ^ 3)) * (a / k)
                = 16 / 9 * B ^ 2 * (1 / (a : ℝ) ^ 2 * (1 / (m : ℝ) ^ 3)) * (1 / k) by field_simp]
            gcongr
            · exact one_le_two.trans ha2 |> fun h => by linarith
            · norm_num
  -- summing each family
  have split : ∀ F : ℕ → ℝ, ∑ a ∈ Finset.Icc 1 N, F a = F 1 + ∑ a ∈ Finset.Icc 2 N, F a := by
    intro F
    have : Finset.Icc 1 N = insert 1 (Finset.Icc 2 N) := by ext x; simp; omega
    rw [this, Finset.sum_insert (by simp)]
  have Z := Cvs.L2a.PositionTailSquareIntegral.sum_inv_sq_le N
  have Z0 : 0 ≤ ∑ a ∈ Finset.Icc 2 N, 1 / (a : ℝ) ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  have hRk : 0 ≤ 4 * R * (1 / k) := by positivity
  have S1 : ∑ m ∈ Finset.Icc 2 N, P 1 m ≤ 4 * R * (π ^ 2 / 6) * (1 / k) := by
    calc _ ≤ ∑ m ∈ Finset.Icc 2 N, 4 * R * (1 / k) * (1 / (m : ℝ) ^ 2) :=
          Finset.sum_le_sum fun m hm => (hrow m hm).trans (le_of_eq (by ring))
      _ = 4 * R * (1 / k) * ∑ m ∈ Finset.Icc 2 N, 1 / (m : ℝ) ^ 2 := by rw [Finset.mul_sum]
      _ ≤ 4 * R * (1 / k) * (π ^ 2 / 6) := mul_le_mul_of_nonneg_left Z hRk
      _ = _ := by ring
  have S2 : ∑ a ∈ Finset.Icc 2 N, P a 1 ≤ 4 * R * (π ^ 2 / 6) * (1 / k) := by
    calc _ ≤ ∑ a ∈ Finset.Icc 2 N, 4 * R * (1 / k) * (1 / (a : ℝ) ^ 2) :=
          Finset.sum_le_sum fun a ha => (hcol a ha).trans (le_of_eq (by ring))
      _ = 4 * R * (1 / k) * ∑ a ∈ Finset.Icc 2 N, 1 / (a : ℝ) ^ 2 := by rw [Finset.mul_sum]
      _ ≤ 4 * R * (1 / k) * (π ^ 2 / 6) := mul_le_mul_of_nonneg_left Z hRk
      _ = _ := by ring
  have hsub2 : Finset.Icc 2 N ⊆ Finset.Icc 1 N := Finset.Icc_subset_Icc (by norm_num) le_rfl
  have S3 : ∑ a ∈ Finset.Icc 2 N, P a a ≤ B ^ 2 * ((harm n + 2) / k) := by
    calc _ ≤ ∑ a ∈ Finset.Icc 2 N, B ^ 2 * (phi k a * (1 / (a : ℝ) ^ 2)) := Finset.sum_le_sum hdiag
      _ = B ^ 2 * ∑ a ∈ Finset.Icc 2 N, phi k a * (1 / (a : ℝ) ^ 2) := by rw [Finset.mul_sum]
      _ ≤ B ^ 2 * ∑ a ∈ Finset.Icc 1 N, phi k a * (1 / (a : ℝ) ^ 2) := by
          gcongr
          intro a _ _; have := phi_nonneg k a; positivity
      _ ≤ _ := mul_le_mul_of_nonneg_left (sum_phi_diag_le hk hnN) (sq_nonneg B)
  have W : ∑ a ∈ Finset.Icc 2 N, ∑ m ∈ (Finset.Icc 2 N).erase a, phi k a * w a m
      ≤ 3 * (harm n ^ 2 + 2 * harm n + 2) / k := by
    calc _ = ∑ a ∈ Finset.Icc 2 N, phi k a * ∑ m ∈ (Finset.Icc 2 N).erase a, w a m := by
          simp only [Finset.mul_sum]
      _ ≤ ∑ a ∈ Finset.Icc 2 N, phi k a * (3 * harm a / (a : ℝ) ^ 2) := by
          refine Finset.sum_le_sum fun a ha => mul_le_mul_of_nonneg_left ?_ (phi_nonneg k a)
          refine le_trans ?_ (sum_w_ne_le a N (by have := (Finset.mem_Icc.mp ha).1; omega))
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun m _ _ => by unfold w; positivity
          intro m hm
          simp only [Finset.mem_erase, Finset.mem_Icc, Finset.mem_filter] at hm ⊢
          omega
      _ ≤ ∑ a ∈ Finset.Icc 1 N, phi k a * (3 * harm a / (a : ℝ) ^ 2) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub2 fun a _ _ => by
            have := phi_nonneg k a; have := harm_nonneg a; positivity
      _ ≤ _ := sum_phi_off_le hk hnN
  have V : ∑ a ∈ Finset.Icc 2 N, ∑ m ∈ (Finset.Icc 2 N).erase a, 1 / (a : ℝ) ^ 2 * (1 / (m : ℝ) ^ 2)
      ≤ (π ^ 2 / 6) ^ 2 := by
    calc _ ≤ ∑ a ∈ Finset.Icc 2 N, ∑ m ∈ Finset.Icc 2 N, 1 / (a : ℝ) ^ 2 * (1 / (m : ℝ) ^ 2) :=
          Finset.sum_le_sum fun a _ => Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
            fun _ _ _ => by positivity
      _ = (∑ a ∈ Finset.Icc 2 N, 1 / (a : ℝ) ^ 2) * ∑ m ∈ Finset.Icc 2 N, 1 / (m : ℝ) ^ 2 :=
          (Finset.sum_mul_sum _ _ _ _).symm
      _ ≤ _ := by rw [sq]; exact mul_le_mul Z Z Z0 (by positivity)
  have S4 : ∑ a ∈ Finset.Icc 2 N, ∑ m ∈ (Finset.Icc 2 N).erase a, P a m
      ≤ K * (3 * (harm n ^ 2 + 2 * harm n + 2) / k) + 16 / 9 * B ^ 2 * (π ^ 2 / 6) ^ 2 * (1 / k) := by
    calc _ ≤ ∑ a ∈ Finset.Icc 2 N, ∑ m ∈ (Finset.Icc 2 N).erase a,
          (K * (phi k a * w a m) + 16 / 9 * B ^ 2 * (1 / k) * (1 / (a : ℝ) ^ 2 * (1 / (m : ℝ) ^ 2))) :=
          Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun m hm => (hfar a ha m hm).trans (le_of_eq (by ring))
      _ = K * (∑ a ∈ Finset.Icc 2 N, ∑ m ∈ (Finset.Icc 2 N).erase a, phi k a * w a m)
          + 16 / 9 * B ^ 2 * (1 / k) * (∑ a ∈ Finset.Icc 2 N, ∑ m ∈ (Finset.Icc 2 N).erase a,
              1 / (a : ℝ) ^ 2 * (1 / (m : ℝ) ^ 2)) := by
          simp only [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ K * (3 * (harm n ^ 2 + 2 * harm n + 2) / k) + 16 / 9 * B ^ 2 * (1 / k) * (π ^ 2 / 6) ^ 2 :=
          add_le_add (mul_le_mul_of_nonneg_left W hK0) (mul_le_mul_of_nonneg_left V (by positivity))
      _ = _ := by ring
  -- assemble
  have hdec : ∑ a ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N, P a m
      = P 1 1 + ∑ m ∈ Finset.Icc 2 N, P 1 m + ∑ a ∈ Finset.Icc 2 N, P a 1
        + ∑ a ∈ Finset.Icc 2 N, P a a + ∑ a ∈ Finset.Icc 2 N, ∑ m ∈ (Finset.Icc 2 N).erase a, P a m := by
    rw [split, split (P 1)]
    have : ∀ a ∈ Finset.Icc 2 N, ∑ m ∈ Finset.Icc 1 N, P a m
        = P a 1 + (P a a + ∑ m ∈ (Finset.Icc 2 N).erase a, P a m) := fun a ha => by
      rw [split (P a), Finset.add_sum_erase _ _ ha]
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_add_distrib]
    ring
  have hfin : (T + 4 * π ^ 2 / 3 * R + (harm n + 2 + 16 / 9 * (π ^ 2 / 6) ^ 2) * B ^ 2
          + 14 * (harm n ^ 2 + 2 * harm n + 2) * (B * D) / c ^ 2) / k
      = T / k + 4 * R * (π ^ 2 / 6) * (1 / k) + 4 * R * (π ^ 2 / 6) * (1 / k) + B ^ 2 * ((harm n + 2) / k)
        + (K * (3 * (harm n ^ 2 + 2 * harm n + 2) / k) + 16 / 9 * B ^ 2 * (π ^ 2 / 6) ^ 2 * (1 / k)) := by
    rw [hK]; field_simp; ring
  refine hkey.trans ?_
  rw [hdec, hfin]
  linarith [h11, S1, S2, S3, S4]

/-- **The truncation gap in logarithmic form**: for `1 ≤ k ≤ X`,
`∫_{θ>1} (posTail ψ X − posTail ψ k)² ≤ 18·(T + rowC + B² + BD/c²)·(2 + log k)²/k`. -/
theorem integral_posTail_gap_le_log {ψ v v' : ℝ → ℝ} {c χ A A₁ B D κ T k X : ℝ}
    (hψ : ∀ ξ, HasDerivAt ψ (v ξ) ξ) (hv : ∀ ξ, HasDerivAt v (v' ξ) ξ) (hvc : Continuous v')
    (hode : ∀ ξ, (ξ ^ 2 - 1) * v' ξ + 2 * ξ * v ξ + (c ^ 2 * ξ ^ 2 - χ) * ψ ξ = 0)
    (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχ : χ ≤ c ^ 2) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hq : ∀ ξ, 2 ≤ ξ → κ * c ^ 2 * ξ ^ 2 ≤ c ^ 2 * ξ ^ 2 - χ)
    (hA : ∀ θ ∈ Icc (1 : ℝ) 2, |ψ θ| ≤ A) (hA₁ : ∫ θ in (1 : ℝ)..2, |v θ| ≤ A₁) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hψB : ∀ ξ, 2 ≤ ξ → |ψ ξ| ≤ B / ξ) (hvD : ∀ ξ, 2 ≤ ξ → |v ξ| ≤ D / ξ)
    (hT : ∀ b b', 1 ≤ b → b ≤ b' → ∫ θ in b..b', ψ θ ^ 2 ≤ T / b) (hk : 1 ≤ k) (hkX : k ≤ X) :
    ∫ θ in Ioi 1, (posTail ψ X θ - posTail ψ k θ) ^ 2
      ≤ 18 * (T + Cvs.L2a.PositionTailEdgeRow.rowC c A A₁ B D κ + B ^ 2 + B * D / c ^ 2)
          * (2 + Real.log k) ^ 2 / k := by
  have h := integral_posTail_gap_le hψ hv hvc hode hc hχ0 hχ hκ hκ1 hq hA hA₁ hB hD hψB hvD hT hk hkX
  refine h.trans (div_le_div_of_nonneg_right ?_ (by linarith))
  set R := Cvs.L2a.PositionTailEdgeRow.rowC c A A₁ B D κ with hR
  set H := harm ⌊k⌋₊ with hH
  set L := 2 + Real.log k with hL
  have hA0 : 0 ≤ A := le_trans (abs_nonneg _) (hA 1 ⟨le_rfl, by norm_num⟩)
  have hA₁0 : 0 ≤ A₁ :=
    le_trans (intervalIntegral.integral_nonneg (by norm_num) fun _ _ => abs_nonneg _) hA₁
  have hR0 : 0 ≤ R := by rw [hR]; unfold Cvs.L2a.PositionTailEdgeRow.rowC; positivity
  have hT0 : 0 ≤ T := by have := hT 1 1 le_rfl le_rfl; simpa using this
  have hE0 : 0 ≤ B * D / c ^ 2 := by positivity
  have hH0 : 0 ≤ H := harm_nonneg _
  have hn1 : (1 : ℝ) ≤ ⌊k⌋₊ := by exact_mod_cast Nat.le_floor (by exact_mod_cast hk)
  have hHL : H + 1 ≤ L := by
    have h1 := harm_le_log ⌊k⌋₊
    have h2 : Real.log ⌊k⌋₊ ≤ Real.log k := Real.log_le_log (by linarith) (Nat.floor_le (by linarith))
    rw [hL]; linarith
  have hL2 : 2 ≤ L := by rw [hL]; linarith [Real.log_nonneg hk]
  have hLL : 4 ≤ L ^ 2 := by nlinarith
  have hπ := Real.pi_lt_d2
  have hπ0 := Real.pi_pos
  have hπ2 : π ^ 2 < 9.93 := by nlinarith
  have c1 : T ≤ 18 * L ^ 2 * T := by nlinarith
  have c2 : 4 * π ^ 2 / 3 * R ≤ 18 * L ^ 2 * R := by
    apply mul_le_mul_of_nonneg_right _ hR0; nlinarith
  have c3 : (H + 2 + 16 / 9 * (π ^ 2 / 6) ^ 2) * B ^ 2 ≤ 18 * L ^ 2 * B ^ 2 := by
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg B)
    have : (π ^ 2 / 6) ^ 2 ≤ 3 := by
      have : π ^ 2 / 6 ≤ 1.66 := by linarith
      nlinarith
    nlinarith
  have c4 : 14 * (H ^ 2 + 2 * H + 2) * (B * D) / c ^ 2 ≤ 18 * L ^ 2 * (B * D / c ^ 2) := by
    rw [mul_div_assoc]
    apply mul_le_mul_of_nonneg_right _ hE0
    nlinarith
  have e : 18 * (T + R + B ^ 2 + B * D / c ^ 2) * L ^ 2
      = 18 * L ^ 2 * T + 18 * L ^ 2 * R + 18 * L ^ 2 * B ^ 2 + 18 * L ^ 2 * (B * D / c ^ 2) := by ring
  rw [e]
  linarith

end Cvs.L2a.PositionTailTruncationGap
