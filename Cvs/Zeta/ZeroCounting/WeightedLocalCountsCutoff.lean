import Mathlib
import Cvs.StepA.Edge.DeepSetZeroSums
import Cvs.StepA.Edge.FiniteTopGap
import Cvs.StepA.Edge.GapRectangleBlaschke
import Cvs.StepA.RestEnvelopeSmall
import Cvs.Zeta.CompletedZeroIndex
import Cvs.Zeta.GaussKernel.DivisorWeightCoordinates
import Cvs.Zeta.GaussKernel.ZeroChain
import Cvs.Zeta.GaussKernel.ZetaZeroStatement
import Cvs.Zeta.LocalCountTransfer
import Cvs.Zeta.ZeroDensityTail
import Cvs.Zeta.ZeroTailInverseSquare
import Cvs.Zeta.ZetaSeamStatement
import Cvs.Zeta.ZetaZeroWindows

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Weighted local counts, and the zero sums above a gapped cutoff

`Cvs.Zeta.ZeroDensityTail`'s local count with multiplicity gives `Σ m_ρ ≤ 264 log(a + 4)` over `a ≤ |γ| < a + 1`, so for `g`
decreasing on `[1, ∞)`, `Σ m_ρ g(|γ_ρ| − s) ≤ Σ_{k=1}^K 264 log(s + k + 4)g(k)`. Above a gapped cutoff `H` this
bounds `R(H) = Σ_{deep, |γ| > H} m_ρ/(|γ_ρ| − H)²`, and both `R(H)` and `Φ(H) = Σ m_ρ φ_ρ` are summable.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology Finset
open Cvs.Zeta.GaussKernel.AdmissibleKernel (nonTrivialZeroSet)
open Cvs.StepA.Edge.FiniteTopGap (mult mult_nonneg)
open Cvs.StepA.Edge.DeepSetZeroSums (deepSet mem_deepSet)
open Cvs.StepA.Edge.GapRectangleBlaschke (phi Gap)

namespace Cvs.Zeta.ZeroCounting.WeightedLocalCountsCutoff
open Cvs.ZeroCounting

/-! ### Local mass with multiplicity -/

/-- **The local mass**: zeros with ordinates in `(t, t + 1]` carry total multiplicity at most `88 log(|t| + 3)`. -/
theorem sum_mult_le_of_window (F : Finset nonTrivialZeroSet) (t : ℝ)
    (hF : ∀ ρ ∈ F, t < (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ t + 1) :
    ∑ ρ ∈ F, mult ρ ≤ 88 * Real.log (|t| + 3) := by
  classical
  set F' := F.map Cvs.Criterion.zeroEquiv.symm.toEmbedding with hF'
  have h1 : ∑ ρ ∈ F, mult ρ = ((∑ ρ ∈ F', Cvs.Zeta.Explicit.Venue.completedZetaZeroMultiplicity ρ : ℕ) : ℝ) := by
    rw [hF', Finset.sum_map]; push_cast; rfl
  have h2 := Cvs.Zeta.LocalCountTransfer.sum_le_Ncount (a := t) (b := t + 1) F' (fun ρ hρ => by
    rw [hF', Finset.mem_map] at hρ
    obtain ⟨σ, hσ, rfl⟩ := hρ
    exact hF σ hσ)
  have h3 := Cvs.Zeta.ZeroDensityTail.localCount_le t
  rw [h1]
  exact (Nat.cast_le.2 h2).trans h3

/-- **The local mass in absolute ordinate**: zeros with `a ≤ |γ| < a + 1`, `a ≥ 0`, carry total multiplicity at
most `264 log(a + 4)`. -/
theorem sum_mult_le_of_abs_window (F : Finset nonTrivialZeroSet) {a : ℝ} (ha : 0 ≤ a)
    (hF : ∀ ρ ∈ F, a ≤ |(ρ : ℂ).im| ∧ |(ρ : ℂ).im| < a + 1) :
    ∑ ρ ∈ F, mult ρ ≤ 264 * Real.log (a + 4) := by
  classical
  set P1 : nonTrivialZeroSet → Prop := fun ρ => a - 1 < (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ a - 1 + 1
  set P2 : nonTrivialZeroSet → Prop := fun ρ => a < (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ a + 1
  set P3 : nonTrivialZeroSet → Prop := fun ρ => -a - 1 < (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ -a - 1 + 1
  have hpt : ∀ ρ ∈ F, mult ρ ≤ (if P1 ρ then mult ρ else 0) + (if P2 ρ then mult ρ else 0)
      + (if P3 ρ then mult ρ else 0) := by
    intro ρ hρ
    have hm := mult_nonneg ρ
    obtain ⟨h1, h2⟩ := hF ρ hρ
    rcases le_or_gt 0 (ρ : ℂ).im with hγ | hγ
    · rw [abs_of_nonneg hγ] at h1 h2
      rcases le_or_gt (ρ : ℂ).im a with h3 | h3
      · have : P1 ρ := ⟨by linarith, by linarith⟩
        rw [if_pos this]
        split_ifs <;> linarith
      · have : P2 ρ := ⟨h3, by linarith⟩
        rw [if_pos this]
        split_ifs <;> linarith
    · rw [abs_of_neg hγ] at h1 h2
      have : P3 ρ := ⟨by linarith, by linarith⟩
      rw [if_pos this]
      split_ifs <;> linarith
  have hsum := Finset.sum_le_sum hpt
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter,
    ← Finset.sum_filter] at hsum
  have e1 := sum_mult_le_of_window (F.filter P1) (a - 1) fun ρ hρ => (Finset.mem_filter.1 hρ).2
  have e2 := sum_mult_le_of_window (F.filter P2) a fun ρ hρ => (Finset.mem_filter.1 hρ).2
  have e3 := sum_mult_le_of_window (F.filter P3) (-a - 1) fun ρ hρ => (Finset.mem_filter.1 hρ).2
  have hab1 : |a - 1| ≤ a + 1 := abs_le.2 ⟨by linarith, by linarith⟩
  have l1 : Real.log (|a - 1| + 3) ≤ Real.log (a + 4) :=
    Real.log_le_log (by positivity) (by linarith)
  have l2 : Real.log (|a| + 3) ≤ Real.log (a + 4) :=
    Real.log_le_log (by positivity) (by rw [abs_of_nonneg ha]; linarith)
  have l3 : Real.log (|-a - 1| + 3) ≤ Real.log (a + 4) :=
    Real.log_le_log (by positivity) (by rw [abs_of_nonpos (by linarith)]; linarith)
  linarith

/-- **The window sum**: for `g ≥ 0` decreasing on `[1, ∞)` and zeros with `1 ≤ |γ| − s < K + 1`,
`Σ m_ρ g(|γ_ρ| − s) ≤ Σ_{k=1}^K 264 log(s + k + 4)g(k)`. -/
theorem sum_mult_mul_le (F : Finset nonTrivialZeroSet) {s : ℝ} (hs : 0 ≤ s) (K : ℕ) {g : ℝ → ℝ}
    (hg0 : ∀ y, 1 ≤ y → 0 ≤ g y) (hgm : ∀ y y', 1 ≤ y → y ≤ y' → g y' ≤ g y)
    (hF : ∀ ρ ∈ F, 1 ≤ |(ρ : ℂ).im| - s ∧ |(ρ : ℂ).im| - s < K + 1) :
    ∑ ρ ∈ F, mult ρ * g (|(ρ : ℂ).im| - s) ≤ ∑ k ∈ Finset.Icc 1 K, 264 * Real.log (s + k + 4) * g k := by
  classical
  set kf : nonTrivialZeroSet → ℕ := fun ρ => ⌊|(ρ : ℂ).im| - s⌋₊ with hkf
  have hk1 : ∀ ρ ∈ F, (kf ρ : ℝ) ≤ |(ρ : ℂ).im| - s := fun ρ hρ =>
    Nat.floor_le (by linarith [(hF ρ hρ).1])
  have hk2 : ∀ ρ : nonTrivialZeroSet, |(ρ : ℂ).im| - s < (kf ρ : ℝ) + 1 := fun ρ => Nat.lt_floor_add_one _
  have hmaps : ∀ ρ ∈ F, kf ρ ∈ Finset.Icc 1 K := by
    intro ρ hρ
    obtain ⟨h1, h2⟩ := hF ρ hρ
    rw [Finset.mem_Icc]
    constructor
    · exact Nat.le_floor (by push_cast; exact h1)
    · have : (kf ρ : ℝ) < K + 1 := (hk1 ρ hρ).trans_lt h2
      have : kf ρ < K + 1 := by exact_mod_cast this
      omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_le_sum fun k hk => ?_
  have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast (Finset.mem_Icc.1 hk).1
  calc ∑ ρ ∈ F.filter (fun ρ => kf ρ = k), mult ρ * g (|(ρ : ℂ).im| - s)
      ≤ ∑ ρ ∈ F.filter (fun ρ => kf ρ = k), mult ρ * g k := by
        refine Finset.sum_le_sum fun ρ hρ => ?_
        obtain ⟨hρF, hρk⟩ := Finset.mem_filter.1 hρ
        refine mul_le_mul_of_nonneg_left (hgm _ _ hk1' ?_) (mult_nonneg ρ)
        rw [← hρk]; exact hk1 ρ hρF
    _ = (∑ ρ ∈ F.filter (fun ρ => kf ρ = k), mult ρ) * g k := by rw [Finset.sum_mul]
    _ ≤ 264 * Real.log (s + k + 4) * g k := by
        refine mul_le_mul_of_nonneg_right ?_ (hg0 _ hk1')
        refine (sum_mult_le_of_abs_window _ (by positivity : (0 : ℝ) ≤ s + k) fun ρ hρ => ?_).trans_eq ?_
        · obtain ⟨hρF, hρk⟩ := Finset.mem_filter.1 hρ
          have a1 := hk1 ρ hρF
          have a2 := hk2 ρ
          rw [hρk] at a1 a2
          constructor <;> linarith
        · ring_nf

/-- `Σ_{k=1}^K 1/k² ≤ 2`. -/
theorem sum_Icc_inv_sq_le (K : ℕ) : ∑ k ∈ Finset.Icc 1 K, 1 / ((k : ℝ)) ^ 2 ≤ 2 := by
  have h := sum_Ioo_inv_sq_le (α := ℝ) 0 (K + 1)
  have e : Finset.Ioo 0 (K + 1) = Finset.Icc 1 K := by ext k; simp; omega
  rw [e] at h
  simpa [one_div] using h.trans (by norm_num)

/-- `Σ_{k=1}^K 1/k ≤ 1 + log K`. -/
theorem sum_Icc_inv_le (K : ℕ) : ∑ k ∈ Finset.Icc 1 K, 1 / (k : ℝ) ≤ 1 + Real.log K := by
  have h := harmonic_le_one_add_log K
  have e : (harmonic K : ℝ) = ∑ k ∈ Finset.Icc 1 K, 1 / (k : ℝ) := by
    induction K with
    | zero => simp
    | succ n ih =>
      rw [harmonic_succ, Finset.sum_Icc_succ_top (by omega), ← ih (harmonic_le_one_add_log n)]
      push_cast; ring
  linarith [e ▸ h]

/-! ### Above a gapped cutoff -/

/-- The deep zeros above `H`. -/
abbrev Above (δD H : ℝ) := {ρ : nonTrivialZeroSet // δD ≤ |Cvs.GaussKernel.del ρ| ∧ H < |(ρ : ℂ).im|}

theorem one_le_of_above {δD H : ℝ} (hg : Gap δD H) (ρ : Above δD H) : H + 1 ≤ |((ρ : nonTrivialZeroSet) : ℂ).im| := by
  have h := hg ρ.1 ρ.2.1
  have h2 := ρ.2.2
  rw [abs_of_nonneg (by linarith)] at h
  linarith

/-- `Σ m_ρ/γ²` over a finite set is at most `Z = Σ' m_ρ/γ²`. -/
theorem sum_mult_inv_sq_le (G : Finset nonTrivialZeroSet) :
    ∑ ρ ∈ G, mult ρ * (1 / ((ρ : ℂ).im) ^ 2) ≤ Cvs.StepA.Edge.DeepSetZeroSums.invSqSum :=
  Summable.sum_le_tsum _ (fun ρ _ => mul_nonneg (mult_nonneg ρ) (by positivity))
    Cvs.StepA.RestEnvelopeSmall.summable_divisorWeight_div_sq

/-- **The gap sum, finitely**: every finite set of deep zeros above a gapped `H ≥ 1` has
`Σ m_ρ/(|γ_ρ| − H)² ≤ 528 log(2H + 5) + 4Z`. -/
theorem sum_above_le {δD H : ℝ} (hH : 1 ≤ H) (hg : Gap δD H) (u : Finset (Above δD H)) :
    ∑ ρ ∈ u, mult ρ * (1 / (|((ρ : nonTrivialZeroSet) : ℂ).im| - H) ^ 2)
      ≤ 528 * Real.log (2 * H + 5) + 4 * Cvs.StepA.Edge.DeepSetZeroSums.invSqSum := by
  classical
  set G := u.map (Function.Embedding.subtype _) with hG
  have hGmem : ∀ ρ ∈ G, δD ≤ |Cvs.GaussKernel.del ρ| ∧ H + 1 ≤ |(ρ : ℂ).im| := by
    intro ρ hρ
    rw [hG, Finset.mem_map] at hρ
    obtain ⟨σ, _, rfl⟩ := hρ
    exact ⟨σ.2.1, one_le_of_above hg σ⟩
  have e : ∑ ρ ∈ u, mult ρ * (1 / (|((ρ : nonTrivialZeroSet) : ℂ).im| - H) ^ 2)
      = ∑ ρ ∈ G, mult ρ * (1 / (|(ρ : ℂ).im| - H) ^ 2) := by
    rw [hG, Finset.sum_map]; rfl
  rw [e, ← Finset.sum_filter_add_sum_filter_not G (fun ρ : nonTrivialZeroSet => |(ρ : ℂ).im| < 2 * H + 1)]
  set K := ⌈H⌉₊ with hK
  have hKr : (K : ℝ) ≤ H + 1 := (Nat.ceil_lt_add_one (by linarith)).le
  have hKr' : H ≤ K := Nat.le_ceil H
  have hnear : ∑ ρ ∈ G.filter (fun ρ : nonTrivialZeroSet => |(ρ : ℂ).im| < 2 * H + 1),
      mult ρ * (1 / (|(ρ : ℂ).im| - H) ^ 2)
      ≤ 528 * Real.log (2 * H + 5) := by
    refine (sum_mult_mul_le _ (by linarith) K (g := fun y => 1 / y ^ 2) (fun y hy => by positivity)
      (fun y y' hy hyy' => one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ (by linarith) hyy' 2))
      fun ρ hρ => ?_).trans ?_
    · obtain ⟨hρG, hρn⟩ := Finset.mem_filter.1 hρ
      have := (hGmem ρ hρG).2
      constructor <;> linarith
    · calc ∑ k ∈ Finset.Icc 1 K, 264 * Real.log (H + k + 4) * (1 / (k : ℝ) ^ 2)
          ≤ ∑ k ∈ Finset.Icc 1 K, 264 * Real.log (2 * H + 5) * (1 / (k : ℝ) ^ 2) := by
            refine Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_right ?_ (by positivity)
            have hk2 : (k : ℝ) ≤ K := by exact_mod_cast (Finset.mem_Icc.1 hk).2
            have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (Finset.mem_Icc.1 hk).1
            exact mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) (by linarith)) (by norm_num)
        _ = 264 * Real.log (2 * H + 5) * ∑ k ∈ Finset.Icc 1 K, 1 / (k : ℝ) ^ 2 := by rw [Finset.mul_sum]
        _ ≤ 264 * Real.log (2 * H + 5) * 2 :=
            mul_le_mul_of_nonneg_left (sum_Icc_inv_sq_le K)
              (mul_nonneg (by norm_num) (Real.log_nonneg (by linarith)))
        _ = 528 * Real.log (2 * H + 5) := by ring
  have hfar : ∑ ρ ∈ G.filter (fun ρ : nonTrivialZeroSet => ¬ |(ρ : ℂ).im| < 2 * H + 1),
      mult ρ * (1 / (|(ρ : ℂ).im| - H) ^ 2)
      ≤ 4 * Cvs.StepA.Edge.DeepSetZeroSums.invSqSum := by
    refine le_trans ?_ (mul_le_mul_of_nonneg_left (sum_mult_inv_sq_le (G.filter
      (fun ρ : nonTrivialZeroSet => ¬ |(ρ : ℂ).im| < 2 * H + 1))) (by norm_num))
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun ρ hρ => ?_
    have h1 := not_lt.1 (Finset.mem_filter.1 hρ).2
    have hm := mult_nonneg ρ
    have hγ0 : 0 < |(ρ : ℂ).im| := by linarith
    have hd : |(ρ : ℂ).im| / 2 ≤ |(ρ : ℂ).im| - H := by linarith
    have hb : 1 / (|(ρ : ℂ).im| - H) ^ 2 ≤ 4 * (1 / ((ρ : ℂ).im) ^ 2) := by
      rw [← sq_abs ((ρ : ℂ).im)]
      calc 1 / (|(ρ : ℂ).im| - H) ^ 2 ≤ 1 / (|(ρ : ℂ).im| / 2) ^ 2 :=
            one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ (by positivity) hd 2)
        _ = 4 * (1 / |(ρ : ℂ).im| ^ 2) := by field_simp; ring
    nlinarith [mul_le_mul_of_nonneg_left hb hm]
  linarith

/-- The near pair mass `Σ_{ρ deep, H < |γ_ρ| ≤ M} m_ρ φ_ρ`. -/
def phiNear (δD H M : ℝ) : ℝ :=
  ∑ ρ ∈ (deepSet δD M).filter (fun ρ : nonTrivialZeroSet => H < |(ρ : ℂ).im|), mult ρ * phi δD H ρ

theorem phi_nonneg (δD H : ℝ) (ρ : nonTrivialZeroSet) : 0 ≤ phi δD H ρ :=
  Finset.sum_nonneg fun _ _ => by positivity

/-- A far zero: `φ_ρ ≤ 4#D/γ_ρ²` once `|γ_ρ| ≥ 2H`. -/
theorem phi_le_far {δD H : ℝ} (hH : 0 ≤ H) {ρ : nonTrivialZeroSet} (hρ : 2 * H < |(ρ : ℂ).im|) :
    phi δD H ρ ≤ (deepSet δD H).card * (4 * (1 / ((ρ : ℂ).im) ^ 2)) := by
  unfold phi
  rw [← nsmul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun ρ' hρ' => ?_
  have h1 := (mem_deepSet.1 hρ').1
  have hd : |(ρ : ℂ).im| / 2 ≤ |(ρ : ℂ).im| - |(ρ' : ℂ).im| := by linarith
  have hγ0 : 0 < |(ρ : ℂ).im| := by linarith
  rw [← sq_abs ((ρ : ℂ).im)]
  calc 1 / (|(ρ : ℂ).im| - |(ρ' : ℂ).im|) ^ 2 ≤ 1 / (|(ρ : ℂ).im| / 2) ^ 2 :=
        one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ (by positivity) hd 2)
    _ = 4 * (1 / |(ρ : ℂ).im| ^ 2) := by field_simp; ring

/-- **The pair mass, finitely**: every finite set of deep zeros above a gapped `H ≥ 1` has
`Σ m_ρ φ_ρ ≤ phiNear δ_D H M + 4#D·tailBound(M)` for `M ≥ 2H`, `9 + e ≤ 2M`. -/
theorem sum_phi_above_le {δD H M : ℝ} (hH : 1 ≤ H) (hM : 2 * H ≤ M)
    (hM' : 9 + Real.exp 1 ≤ 2 * M) (u : Finset (Above δD H)) :
    ∑ ρ ∈ u, mult ρ * phi δD H ρ
      ≤ phiNear δD H M + 4 * (deepSet δD H).card * Cvs.Zeta.ZeroTailInverseSquare.tailBound M := by
  classical
  set G := u.map (Function.Embedding.subtype _) with hG
  have hGmem : ∀ ρ ∈ G, δD ≤ |Cvs.GaussKernel.del ρ| ∧ H < |(ρ : ℂ).im| := by
    intro ρ hρ
    rw [hG, Finset.mem_map] at hρ
    obtain ⟨σ, _, rfl⟩ := hρ
    exact σ.2
  have e : ∑ ρ ∈ u, mult ρ * phi δD H ρ = ∑ ρ ∈ G, mult ρ * phi δD H ρ := by
    rw [hG, Finset.sum_map]; rfl
  rw [e, ← Finset.sum_filter_add_sum_filter_not G (fun ρ : nonTrivialZeroSet => |(ρ : ℂ).im| ≤ M)]
  have hnear : ∑ ρ ∈ G.filter (fun ρ : nonTrivialZeroSet => |(ρ : ℂ).im| ≤ M), mult ρ * phi δD H ρ
      ≤ phiNear δD H M := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun ρ hρ => ?_)
      fun ρ _ _ => mul_nonneg (mult_nonneg ρ) (phi_nonneg δD H ρ)
    obtain ⟨hρG, hρM⟩ := Finset.mem_filter.1 hρ
    obtain ⟨h1, h2⟩ := hGmem ρ hρG
    exact Finset.mem_filter.2 ⟨mem_deepSet.2 ⟨hρM, h1⟩, h2⟩
  have hfar : ∑ ρ ∈ G.filter (fun ρ : nonTrivialZeroSet => ¬ |(ρ : ℂ).im| ≤ M), mult ρ * phi δD H ρ
      ≤ 4 * (deepSet δD H).card * Cvs.Zeta.ZeroTailInverseSquare.tailBound M := by
    set Gf := G.filter (fun ρ : nonTrivialZeroSet => ¬ |(ρ : ℂ).im| ≤ M)
    have hGf : ∀ ρ ∈ Gf, M < |(ρ : ℂ).im| := fun ρ hρ => not_le.1 (Finset.mem_filter.1 hρ).2
    have h1 : ∑ ρ ∈ Gf, mult ρ * phi δD H ρ
        ≤ ∑ ρ ∈ Gf, (deepSet δD H).card * 4 * (mult ρ * (1 / ((ρ : ℂ).im) ^ 2)) := by
      refine Finset.sum_le_sum fun ρ hρ => ?_
      have := phi_le_far (δD := δD) (by linarith) (show 2 * H < |(ρ : ℂ).im| by linarith [hGf ρ hρ])
      have hm := mult_nonneg ρ
      calc mult ρ * phi δD H ρ ≤ mult ρ * ((deepSet δD H).card * (4 * (1 / ((ρ : ℂ).im) ^ 2))) :=
            mul_le_mul_of_nonneg_left this hm
        _ = _ := by ring
    have hT := Cvs.Zeta.ZeroTailInverseSquare.tsum_le_tailBound hM'
    have h2 : ∑ ρ ∈ Gf, mult ρ * (1 / ((ρ : ℂ).im) ^ 2) ≤ Cvs.Zeta.ZeroTailInverseSquare.tailBound M := by
      have e2 : ∑ ρ ∈ Gf, mult ρ * (1 / ((ρ : ℂ).im) ^ 2)
          = ∑ ρ ∈ Gf.subtype (fun ρ : nonTrivialZeroSet => M < |(ρ : ℂ).im|),
            (Cvs.Criterion.divisorWeight (ρ : nonTrivialZeroSet) : ℝ) / (((ρ : nonTrivialZeroSet) : ℂ)).im ^ 2 := by
        rw [Finset.sum_subtype_of_mem (fun ρ : nonTrivialZeroSet =>
          (Cvs.Criterion.divisorWeight ρ : ℝ) / ((ρ : ℂ)).im ^ 2) hGf]
        refine Finset.sum_congr rfl fun ρ _ => ?_
        rw [mul_one_div]
      rw [e2]
      exact (Summable.sum_le_tsum _ (fun _ _ => by positivity) hT.1).trans hT.2
    rw [← Finset.mul_sum] at h1
    nlinarith [Nat.cast_nonneg (α := ℝ) (deepSet δD H).card]
  linarith

end Cvs.Zeta.ZeroCounting.WeightedLocalCountsCutoff

end
