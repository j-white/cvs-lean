import Mathlib
import Cvs.L2a.FrameConstantFirstModeAngle
import Cvs.L2a.RungApproximationErrorCharge
import Cvs.L2a.TailOfModes

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The span's frame bound from rung-level data

For `Φ = Σᵢ aᵢψᵢ` with `Gᵢ = ∫₁ᵇψᵢ²`, the tail norm is `∫₁ᵇ(Φ + Δ)²`, `Δ = Σ_{m≥2}Φ(m·)`. If the span's mode-1 angle
is `|∫₁ᵇΦΔ| ≤ δ√(∫Φ²∫Δ²)`, the rungs' pairings on `[1, b]` are `|∫₁ᵇψᵢψⱼ| ≤ √(τᵢτⱼ)` with Schur rows
`Σ_{j≠i}√(τᵢτⱼ/(GᵢGⱼ)) ≤ e < 1`, and `S = Σᵢ ∫_b^{Mb}ψᵢ²/Gᵢ`, then `∫₁^{Mb}Φ² ≤ ((1 + S/(1 − e))/(1 − δ))·∫tailF²`:
the frame constant behind every charge to the tail norm, from one span angle and single-rung quantities.
-/

namespace Cvs.L2a.SpanFrameFromRungs

open Real Set Finset MeasureTheory intervalIntegral Cvs.L2a.TailOfModes Cvs.L2a.RungApproximationErrorCharge Cvs.L2a.FrameConstantFirstModeAngle

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The Schur floor of a Gram form**: `(1 − e)Σⱼ aⱼ²Gⱼⱼ ≤ Σⱼₖ aⱼaₖGⱼₖ`. -/
theorem schur_floor (a : ι → ℝ) (G E : ι → ι → ℝ) {e : ℝ} (hdiag : ∀ j, 0 ≤ G j j)
    (hoff : ∀ j k, j ≠ k → |G j k| ≤ E j k * √(G j j * G k k)) (hE0 : ∀ j k, 0 ≤ E j k)
    (hsym : ∀ j k, E j k = E k j) (hrow : ∀ j, ∑ k, E j k ≤ e) :
    (1 - e) * ∑ j, a j ^ 2 * G j j ≤ ∑ j, ∑ k, a j * a k * G j k := by
  set d : ι → ℝ := fun j => a j ^ 2 * G j j with hdd
  have hd : ∀ j, 0 ≤ d j := fun j => mul_nonneg (sq_nonneg _) (hdiag j)
  have hpt : ∀ j k, (if j = k then d j else 0) - E j k * ((d j + d k) / 2) ≤ a j * a k * G j k := fun j k => by
    by_cases h : j = k
    · subst h; rw [if_pos rfl]
      have : a j * a j * G j j = d j := by simp only [hdd]; ring
      nlinarith [hE0 j j, hd j]
    · rw [if_neg h]
      have hsq : √(d j * d k) ≤ (d j + d k) / 2 := by
        rw [Real.sqrt_le_left (by linarith [hd j, hd k])]
        nlinarith [sq_nonneg (d j - d k), hd j, hd k]
      have hX : |a j * a k * G j k| ≤ E j k * √(d j * d k) := by
        calc |a j * a k * G j k| = |a j * a k| * |G j k| := by rw [abs_mul]
          _ ≤ |a j * a k| * (E j k * √(G j j * G k k)) :=
              mul_le_mul_of_nonneg_left (hoff j k h) (abs_nonneg _)
          _ = E j k * √(d j * d k) := by
              simp only [hdd]
              rw [show a j ^ 2 * G j j * (a k ^ 2 * G k k) = (a j * a k) ^ 2 * (G j j * G k k) by ring,
                Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]
              ring
      have h2 : E j k * √(d j * d k) ≤ E j k * ((d j + d k) / 2) := mul_le_mul_of_nonneg_left hsq (hE0 j k)
      linarith [neg_abs_le (a j * a k * G j k)]
  have hsum : ∑ j, ∑ k, ((if j = k then d j else 0) - E j k * ((d j + d k) / 2)) ≤ ∑ j, ∑ k, a j * a k * G j k :=
    Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => hpt j k
  simp only [Finset.sum_sub_distrib] at hsum
  have hdiagsum : ∑ j, ∑ k, (if j = k then d j else 0) = ∑ j, d j := by
    apply Finset.sum_congr rfl; intro j _; rw [Finset.sum_ite_eq univ j (fun _ => d j), if_pos (Finset.mem_univ _)]
  rw [hdiagsum] at hsum
  have hA : ∑ j, ∑ k, E j k * ((d j + d k) / 2)
      = (1 / 2) * (∑ j, ∑ k, E j k * d j) + (1 / 2) * (∑ j, ∑ k, E j k * d k) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro j _
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro k _; ring
  have hB1 : ∑ j, ∑ k, E j k * d j ≤ e * ∑ j, d j := by
    rw [Finset.mul_sum]; apply Finset.sum_le_sum; intro j _
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hrow j) (hd j)
  have hB2 : ∑ j, ∑ k, E j k * d k ≤ e * ∑ j, d j := by
    rw [Finset.sum_comm, Finset.mul_sum]; apply Finset.sum_le_sum; intro k _
    rw [← Finset.sum_mul]
    have : ∑ j, E j k = ∑ j, E k j := Finset.sum_congr rfl fun j _ => hsym j k
    rw [this]
    exact mul_le_mul_of_nonneg_right (hrow k) (hd k)
  rw [hA] at hsum
  simp only [hdd] at hsum hB1 hB2 ⊢
  nlinarith

/-- **The tail norm as an interval integral**: `∫_{(1,∞)} tailF² = ∫₁ᵇ(Φ + Σ_{m≥2}Φ(m·))²`. -/
theorem tail_sq_eq (Φ : ℝ → ℝ) {M : ℕ} {b : ℝ} (hM : 1 ≤ M) (hb : 1 ≤ b) :
    ∫ θ in Ioi 1, tailF Φ M b θ ^ 2 = ∫ θ in (1 : ℝ)..b, (Φ θ + ∑ m ∈ Finset.Icc 2 M, Φ (m * θ)) ^ 2 := by
  have e1 : ∫ θ in Ioi 1, tailF Φ M b θ ^ 2 = ∫ θ in Ioc 1 b, (∑ m ∈ Finset.Icc 1 M, Φ (m * θ)) ^ 2 := by
    have hsub : Ioc (1 : ℝ) b ⊆ Ioi 1 := fun θ hθ => hθ.1
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi hsub
      (fun θ hθ => by unfold tailF; rw [indicator_of_notMem hθ.2]; ring)]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro θ hθ; simp only; unfold tailF; rw [indicator_of_mem hθ]
  rw [e1, ← intervalIntegral.integral_of_le hb]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  have hs : Finset.Icc 1 M = insert 1 (Finset.Icc 2 M) := by
    ext m; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  rw [hs, Finset.sum_insert (by simp)]
  simp

/-- **The span's mass as a Gram form**. -/
theorem sq_sum_integral (a : ι → ℝ) (ψ : ι → ℝ → ℝ) {p q : ℝ} (hpq : p ≤ q)
    (hc : ∀ i, ContinuousOn (ψ i) (Icc p q)) :
    ∫ θ in p..q, (∑ i, a i * ψ i θ) ^ 2 = ∑ i, ∑ j, a i * a j * ∫ θ in p..q, ψ i θ * ψ j θ := by
  have hII : ∀ i j, IntervalIntegrable (fun θ => a i * a j * (ψ i θ * ψ j θ)) volume p q := fun i j =>
    (continuousOn_const.mul ((hc i).mul (hc j))).intervalIntegrable_of_Icc hpq
  have e : (fun θ => (∑ i, a i * ψ i θ) ^ 2) = fun θ => ∑ i, ∑ j, a i * a j * (ψ i θ * ψ j θ) := by
    funext θ; rw [sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hsumII : ∀ i ∈ (univ : Finset ι),
      IntervalIntegrable (fun θ => ∑ j, a i * a j * (ψ i θ * ψ j θ)) volume p q := fun i _ =>
    (continuousOn_finsetSum _ fun j _ => continuousOn_const.mul ((hc i).mul (hc j))).intervalIntegrable_of_Icc hpq
  rw [e, intervalIntegral.integral_finsetSum hsumII]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [intervalIntegral.integral_finsetSum fun j _ => hII i j]
  exact Finset.sum_congr rfl fun j _ => intervalIntegral.integral_const_mul _ _

/-- **The span's frame bound from rung-level data**. -/
theorem frame_of_rungs (a : ι → ℝ) (ψ : ι → ℝ → ℝ) {M : ℕ} {b δ e S : ℝ} (G τ : ι → ℝ)
    (hM : 1 ≤ M) (hb : 1 ≤ b) (hcont : ∀ i, ContinuousOn (ψ i) (Icc 1 (M * b)))
    (hδ0 : 0 ≤ δ) (hδ : δ < 1)
    (hangle : |∫ θ in (1 : ℝ)..b, (∑ i, a i * ψ i θ) * ∑ m ∈ Finset.Icc 2 M, ∑ i, a i * ψ i (m * θ)|
      ≤ δ * √((∫ θ in (1 : ℝ)..b, (∑ i, a i * ψ i θ) ^ 2)
          * ∫ θ in (1 : ℝ)..b, (∑ m ∈ Finset.Icc 2 M, ∑ i, a i * ψ i (m * θ)) ^ 2))
    (hGdef : ∀ i, G i = ∫ θ in (1 : ℝ)..b, ψ i θ ^ 2) (hG : ∀ i, 0 < G i) (hτ0 : ∀ i, 0 ≤ τ i)
    (hpair : ∀ i j, i ≠ j → |∫ θ in (1 : ℝ)..b, ψ i θ * ψ j θ| ≤ √(τ i * τ j))
    (he0 : 0 ≤ e) (he : e < 1)
    (hrow : ∀ i, ∑ j ∈ univ.erase i, √(τ i * τ j) / √(G i * G j) ≤ e)
    (hS : ∑ i, (∫ ξ in b..(M * b), ψ i ξ ^ 2) / G i ≤ S) :
    ∫ ξ in (1 : ℝ)..(M * b), (∑ i, a i * ψ i ξ) ^ 2
      ≤ ((1 + S / (1 - e)) / (1 - δ)) * ∫ θ in Ioi 1, tailF (fun ξ => ∑ i, a i * ψ i ξ) M b θ ^ 2 := by
  set Φ : ℝ → ℝ := fun ξ => ∑ i, a i * ψ i ξ with hΦd
  set Δ : ℝ → ℝ := fun θ => ∑ m ∈ Finset.Icc 2 M, Φ (m * θ) with hΔd
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hbMb : b ≤ M * b := by nlinarith
  have h1Mb : (1 : ℝ) ≤ M * b := le_trans hb hbMb
  have hsub1 : Icc 1 b ⊆ Icc 1 (M * b) := Icc_subset_Icc le_rfl hbMb
  have hsub2 : Icc b (M * b) ⊆ Icc 1 (M * b) := Icc_subset_Icc hb le_rfl
  have cΦ : ContinuousOn Φ (Icc 1 (M * b)) := continuousOn_finsetSum _ fun i _ => continuousOn_const.mul (hcont i)
  -- each dilate `Φ(m·)`, `2 ≤ m ≤ M`, is continuous on `[1, b]`
  have cΦm : ∀ m ∈ Finset.Icc 2 M, ContinuousOn (fun θ => Φ (m * θ)) (Icc 1 b) := fun m hm => by
    have hm1 : (1 : ℝ) ≤ m := by have := (Finset.mem_Icc.mp hm).1; exact_mod_cast (by omega : 1 ≤ m)
    have hmM : (m : ℝ) ≤ M := by exact_mod_cast (Finset.mem_Icc.mp hm).2
    refine cΦ.comp (continuous_const.mul continuous_id).continuousOn fun θ hθ => ⟨?_, ?_⟩
    · nlinarith [hθ.1]
    · have := mul_le_mul hmM hθ.2 (by linarith [hθ.1]) (by linarith); simpa using this
  have cΔ : ContinuousOn Δ (Icc 1 b) := continuousOn_finsetSum _ cΦm
  have cΦb : ContinuousOn Φ (Icc 1 b) := cΦ.mono hsub1
  -- the tail norm `N = P + Q + 2C`
  set P := ∫ θ in (1 : ℝ)..b, Φ θ ^ 2 with hPd
  set Q := ∫ θ in (1 : ℝ)..b, Δ θ ^ 2 with hQd
  set C := ∫ θ in (1 : ℝ)..b, Φ θ * Δ θ with hCd
  set N := ∫ θ in Ioi 1, tailF Φ M b θ ^ 2 with hNd
  have hN : N = P + Q + 2 * C := by
    rw [hNd, tail_sq_eq Φ hM hb]
    have i1 : IntervalIntegrable (fun θ => Φ θ ^ 2) volume 1 b := (cΦb.pow 2).intervalIntegrable_of_Icc hb
    have i2 : IntervalIntegrable (fun θ => Δ θ ^ 2) volume 1 b := (cΔ.pow 2).intervalIntegrable_of_Icc hb
    have i3 : IntervalIntegrable (fun θ => 2 * (Φ θ * Δ θ)) volume 1 b :=
      (continuousOn_const.mul (cΦb.mul cΔ)).intervalIntegrable_of_Icc hb
    have e : (fun θ => (Φ θ + ∑ m ∈ Finset.Icc 2 M, Φ (m * θ)) ^ 2)
        = fun θ => Φ θ ^ 2 + Δ θ ^ 2 + 2 * (Φ θ * Δ θ) := by funext θ; simp only [hΔd]; ring
    rw [e, intervalIntegral.integral_add (i1.add i2) i3, intervalIntegral.integral_add i1 i2,
      intervalIntegral.integral_const_mul]
  have hP0 : 0 ≤ P := intervalIntegral.integral_nonneg hb fun θ _ => sq_nonneg _
  have hQ0 : 0 ≤ Q := intervalIntegral.integral_nonneg hb fun θ _ => sq_nonneg _
  have hPQ : P + Q ≤ N / (1 - δ) := by rw [hN]; exact sum_le_of_angle hP0 hQ0 hδ0 hδ hangle
  -- the Gram floor `(1 − e)Σ aᵢ²Gᵢ ≤ P`
  set Gm : ι → ι → ℝ := fun i j => ∫ θ in (1 : ℝ)..b, ψ i θ * ψ j θ with hGmd
  set E : ι → ι → ℝ := fun i j => if i = j then 0 else √(τ i * τ j) / √(G i * G j) with hEd
  have hGii : ∀ i, Gm i i = G i := fun i => by simp only [hGmd, hGdef i, sq]
  have hPgram : P = ∑ i, ∑ j, a i * a j * Gm i j := sq_sum_integral a ψ hb fun i => (hcont i).mono hsub1
  have hfloor : (1 - e) * ∑ i, a i ^ 2 * Gm i i ≤ P := by
    rw [hPgram]
    refine schur_floor a Gm E (fun i => by rw [hGii]; exact (hG i).le) (fun i j hij => ?_) (fun i j => ?_)
      (fun i j => ?_) (fun i => ?_)
    · simp only [hEd, if_neg hij, hGii]
      have hGG : 0 < √(G i * G j) := Real.sqrt_pos.mpr (mul_pos (hG i) (hG j))
      rw [div_mul_cancel₀ _ hGG.ne']
      exact hpair i j hij
    · simp only [hEd]; split_ifs <;> positivity
    · simp only [hEd]; split_ifs with h1 h2 h2
      · rfl
      · exact absurd h1.symm h2
      · exact absurd h2.symm h1
      · rw [mul_comm (τ i), mul_comm (G i)]
    · calc ∑ j, E i j = ∑ j ∈ univ.erase i, √(τ i * τ j) / √(G i * G j) := by
            rw [← Finset.add_sum_erase univ _ (Finset.mem_univ i)]
            simp only [hEd, if_pos rfl, zero_add]
            exact Finset.sum_congr rfl fun j hj => by rw [if_neg (Finset.ne_of_mem_erase hj).symm]
        _ ≤ e := hrow i
  have hdiagG : ∑ i, a i ^ 2 * Gm i i = ∑ i, a i ^ 2 * G i := Finset.sum_congr rfl fun i _ => by rw [hGii]
  rw [hdiagG] at hfloor
  -- the far mass `R ≤ (Σ aᵢ²Gᵢ)·S` by the rung triangle (Cvs.L2a.RungApproximationErrorCharge)
  set R := ∫ ξ in b..(M * b), Φ ξ ^ 2 with hRd
  have hR : R ≤ (∑ i, a i ^ 2 * G i) * S := by
    have h := layer_error_le a G ψ (fun i ξ => |ψ i ξ|) hbMb hG (fun i ξ _ => le_refl _)
      (fun i => (hcont i).mono hsub2) (fun i => ((hcont i).mono hsub2).abs)
    simp only [sq_abs] at h
    have hG0 : 0 ≤ ∑ i, a i ^ 2 * G i := Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (hG i).le
    exact h.trans (mul_le_mul_of_nonneg_left hS hG0)
  -- assemble
  have hsplit : ∫ ξ in (1 : ℝ)..(M * b), Φ ξ ^ 2 = P + R := by
    have i1 : IntervalIntegrable (fun ξ => Φ ξ ^ 2) volume 1 b := (cΦb.pow 2).intervalIntegrable_of_Icc hb
    have i2 : IntervalIntegrable (fun ξ => Φ ξ ^ 2) volume b (M * b) :=
      ((cΦ.mono hsub2).pow 2).intervalIntegrable_of_Icc hbMb
    exact (intervalIntegral.integral_add_adjacent_intervals i1 i2).symm
  have h1δ : 0 < 1 - δ := by linarith
  have h1e : 0 < 1 - e := by linarith
  have hN0 : 0 ≤ N := by
    rw [hNd]; exact setIntegral_nonneg measurableSet_Ioi fun θ _ => sq_nonneg _
  have hPN : P ≤ N / (1 - δ) := by linarith
  have hGN : ∑ i, a i ^ 2 * G i ≤ N / ((1 - e) * (1 - δ)) := by
    rw [le_div_iff₀ (mul_pos h1e h1δ)]
    have := (le_div_iff₀ h1δ).mp hPN
    nlinarith
  have hS0 : 0 ≤ S := le_trans (Finset.sum_nonneg fun i _ => div_nonneg
    (intervalIntegral.integral_nonneg hbMb fun ξ _ => sq_nonneg _) (hG i).le) hS
  rw [hsplit]
  calc P + R ≤ N / (1 - δ) + N / ((1 - e) * (1 - δ)) * S := by
        have := mul_le_mul_of_nonneg_right hGN hS0
        linarith
    _ = ((1 + S / (1 - e)) / (1 - δ)) * N := by field_simp

end Cvs.L2a.SpanFrameFromRungs
