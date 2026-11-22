import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.FullTailConvergence
import Cvs.L2a.PositionTailPrimeLevels
import Cvs.L2a.PositionTailSpanAdapters
import Cvs.L2a.PositionTruncatedTail
import Cvs.L2a.TailLogScaleTest
import Cvs.Zeta.PrimePowerSideTruncated
import Cvs.Zeta.WeilPositivityStatement

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The prime side of `F_X` converges to `Prime_∞`

`Prime_∞ = 2∫_{(1,∞)} ⟨F_∞, F_∞ − F_k⟩ dk/k − 2∫ log θ F_∞²` with `|⟨F_∞, F_∞ − F_k⟩| ≤ B_G √(K1b/√k)`, so the level
integral converges absolutely; dominated convergence in `k` and in `θ` carries `PositionTailPrimeLevels`'s level form to it.
-/

namespace Cvs.L2a.FullTailPrimeChannel

open Real Set Filter Topology MeasureTheory Cvs.L2a.AngularProlateTailPositive Cvs.L2a.PositionTruncatedTail Cvs.L2a.FullTailConvergence

/-- `Prime_∞ = 2∫_{(1,∞)} ⟨F_∞, F_∞ − F_k⟩ dk/k − 2∫_{(1,∞)} log θ F_∞²`. -/
noncomputable def primeInf (Φ : ℝ → ℝ) : ℝ :=
  2 * (∫ k in Ioi 1, (∫ θ in Ioi 1, fullTail Φ θ * (fullTail Φ θ - posTail Φ k θ)) / k)
    - 2 * ∫ θ in Ioi 1, Real.log θ * fullTail Φ θ ^ 2

variable {g g₁ g₂ : ℝ → ℝ} {c : ℝ}

/-! ### Measurability in the level -/

/-- For `N ≥ ⌊X⌋₊` the position-truncated tail is the mode sum over `m ≤ N` cut at `1 < θ`, `mθ ≤ X`. -/
theorem posTail_eq_sum_cut (Φ : ℝ → ℝ) {X : ℝ} {N : ℕ} (hN : ⌊X⌋₊ ≤ N) (θ : ℝ) :
    posTail Φ X θ = ∑ m ∈ Finset.Icc 1 N,
      ({p : ℝ × ℝ | 1 < p.2 ∧ (m : ℝ) * p.2 ≤ p.1}).indicator (fun p => Φ (m * p.2)) (X, θ) := by
  rw [posTail_eq_sum]
  have hterm : ∀ m ∈ Finset.Icc 1 N, ({p : ℝ × ℝ | 1 < p.2 ∧ (m : ℝ) * p.2 ≤ p.1}).indicator
      (fun p => Φ (m * p.2)) (X, θ) = (Ioc 1 (X / m)).indicator (fun θ => Φ (m * θ)) θ := by
    intro m hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
    have hiff : (X, θ) ∈ {p : ℝ × ℝ | 1 < p.2 ∧ (m : ℝ) * p.2 ≤ p.1} ↔ θ ∈ Ioc 1 (X / m) := by
      show (1 < θ ∧ (m : ℝ) * θ ≤ X) ↔ _
      rw [mem_Ioc, le_div_iff₀ hm0, mul_comm θ]
    by_cases h : θ ∈ Ioc 1 (X / m)
    · rw [indicator_of_mem h, indicator_of_mem (hiff.mpr h)]
    · rw [indicator_of_notMem h, indicator_of_notMem (fun h' => h (hiff.mp h'))]
  rw [Finset.sum_congr (rfl : Finset.Icc 1 N = Finset.Icc 1 N) hterm]
  refine Finset.sum_subset (Finset.Icc_subset_Icc le_rfl hN) ?_
  intro m hm hnot
  have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
  have hXm : X < m := by
    have h1 : ⌊X⌋₊ < m := by
      by_contra h
      exact hnot (Finset.mem_Icc.mpr ⟨hm1, not_lt.mp h⟩)
    have h2 := Nat.lt_floor_add_one X
    have h3 : ((⌊X⌋₊ : ℕ) : ℝ) + 1 ≤ m := by exact_mod_cast h1
    linarith
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  refine indicator_of_notMem (fun h => ?_) _
  have h1 : (1 : ℝ) < θ := h.1
  have h2 : (m : ℝ) < m * θ := by nlinarith
  have h3 := (le_div_iff₀ hm0).mp h.2
  linarith

/-- **Joint measurability**: `(X, θ) ↦ posTail Φ X θ` is measurable for continuous `Φ`. -/
theorem measurable_posTail_uncurry {Φ : ℝ → ℝ} (hΦ : Continuous Φ) :
    Measurable fun p : ℝ × ℝ => posTail Φ p.1 p.2 := by
  refine measurable_of_tendsto_metrizable (f := fun N p => ∑ m ∈ Finset.Icc 1 N,
    ({p : ℝ × ℝ | 1 < p.2 ∧ (m : ℝ) * p.2 ≤ p.1}).indicator (fun p => Φ (m * p.2)) p) (fun N => ?_) ?_
  · refine Finset.measurable_sum _ fun m _ => ?_
    refine (hΦ.measurable.comp (measurable_const.mul measurable_snd)).indicator ?_
    change MeasurableSet ({p : ℝ × ℝ | 1 < p.2} ∩ {p : ℝ × ℝ | (m : ℝ) * p.2 ≤ p.1})
    exact ((measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_le (measurable_const.mul measurable_snd) measurable_fst))
  · rw [tendsto_pi_nhds]
    intro p
    refine tendsto_atTop_of_eventually_const (i₀ := ⌊p.1⌋₊) fun N hN => ?_
    exact (posTail_eq_sum_cut Φ hN p.2).symm

/-- **The level is measurable**: `k ↦ ∫_{(1,∞)} a (a − F_k)` for measurable `a` and continuous `Φ`. -/
theorem measurable_level {Φ a : ℝ → ℝ} (hΦ : Continuous Φ) (ha : Measurable a) :
    Measurable fun k => ∫ θ in Ioi 1, a θ * (a θ - posTail Φ k θ) := by
  have hf : Measurable fun p : ℝ × ℝ => a p.2 * (a p.2 - posTail Φ p.1 p.2) :=
    (ha.comp measurable_snd).mul ((ha.comp measurable_snd).sub (measurable_posTail_uncurry hΦ))
  exact (hf.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioi (1 : ℝ)))).measurable

/-! ### Cauchy–Schwarz bounds on the level -/

/-- `|∫_{(1,∞)} f h| ≤ √D K'` when `∫ f² ≤ D` and `|h| ≤ K'/θ`, both measurable and `f` bounded by `K/θ`. -/
theorem abs_inner_le {f h : ℝ → ℝ} {K K' D : ℝ} (hf : Measurable f) (hh : Measurable h)
    (hfK : ∀ θ, 0 < θ → |f θ| ≤ K / θ) (hhK : ∀ θ, 0 < θ → |h θ| ≤ K' / θ) (hK' : 0 ≤ K')
    (hD : ∫ θ in Ioi 1, f θ ^ 2 ≤ D) : |∫ θ in Ioi 1, f θ * h θ| ≤ √D * K' := by
  refine (abs_setIntegral_mul_le (integrableOn_sq_of_le hf hfK) (integrableOn_sq_of_le hh hhK)
    (integrableOn_mul_of_le hf hh hfK hhK)).trans ?_
  have h2 : √(∫ θ in Ioi 1, h θ ^ 2) ≤ K' := by
    rw [← Real.sqrt_sq hK']; exact Real.sqrt_le_sqrt (integral_sq_le_of_le hh hhK)
  exact mul_le_mul (Real.sqrt_le_sqrt hD) h2 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

/-- `√(K/√k)/k = √K k^{−5/4}` for `k > 0`. -/
theorem sqrt_div_sqrt_div_eq (K : ℝ) {k : ℝ} (hk : 0 < k) : √(K / √k) / k = √K * k ^ (-(5 / 4 : ℝ)) := by
  rw [Real.sqrt_div' K (Real.sqrt_nonneg k), Real.sqrt_eq_rpow k, Real.sqrt_eq_rpow (k ^ (1 / 2 : ℝ)),
    ← rpow_mul hk.le, show -(5 / 4 : ℝ) = -(1 / 2 * (1 / 2)) + -1 by norm_num, rpow_add hk, rpow_neg hk.le,
    rpow_neg_one]
  have : 0 < k ^ (1 / 2 * (1 / 2) : ℝ) := rpow_pos_of_pos hk _
  field_simp

/-- **The level bound at `X`**: `|⟨F_X, F_X − F_k⟩| ≤ 2 B_G √(K1b/√k)` for `1 ≤ k ≤ X`. -/
theorem abs_level_le (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hc : 0 < c) {X k : ℝ} (hk : 1 ≤ k) (hkX : k ≤ X) :
    |∫ θ in Ioi 1, posTail (psi c g) X θ * (posTail (psi c g) X θ - posTail (psi c g) k θ)|
      ≤ 2 * BG c (g 1 + g (-1)) (|g₁ 1 - g₁ (-1)| + ∫ s in (-1 : ℝ)..1, |g₂ s|)
        * √(K1b c (g 1 + g (-1)) (|g₁ 1 - g₁ (-1)| + ∫ s in (-1 : ℝ)..1, |g₂ s|) / √k) := by
  set B := BG c (g 1 + g (-1)) (|g₁ 1 - g₁ (-1)| + ∫ s in (-1 : ℝ)..1, |g₂ s|)
  set Kb := K1b c (g 1 + g (-1)) (|g₁ 1 - g₁ (-1)| + ∫ s in (-1 : ℝ)..1, |g₂ s|)
  have hB : 0 ≤ B := BG_nonneg hc _ (C1_nonneg g₁ g₂)
  set a := posTail (psi c g) X
  set q := posTail (psi c g) k
  set b := fullTail (psi c g)
  have ham := measurable_posTail_psi hg c X
  have hqm := measurable_posTail_psi hg c k
  have hbm := measurable_fullTail hg hg₁ hg₂c hc
  have hab : ∀ θ, 0 < θ → |a θ| ≤ B / θ := fun θ hθ => abs_posTail_le hg hg₁ hg₂c hc X hθ
  have hda : ∀ θ, 0 < θ → |a θ - b θ| ≤ 2 * B / θ := fun θ hθ => abs_posTail_sub_le hg hg₁ hg₂c hc X hθ
  have hdq : ∀ θ, 0 < θ → |q θ - b θ| ≤ 2 * B / θ := fun θ hθ => abs_posTail_sub_le hg hg₁ hg₂c hc k hθ
  have i1 : IntegrableOn (fun θ => (a θ - b θ) * a θ) (Ioi 1) :=
    integrableOn_mul_of_le (f := fun θ => a θ - b θ) (ham.sub hbm) ham hda hab
  have i2 : IntegrableOn (fun θ => (q θ - b θ) * a θ) (Ioi 1) :=
    integrableOn_mul_of_le (f := fun θ => q θ - b θ) (hqm.sub hbm) ham hdq hab
  have hsplit : ∫ θ in Ioi 1, a θ * (a θ - q θ)
      = (∫ θ in Ioi 1, (a θ - b θ) * a θ) - ∫ θ in Ioi 1, (q θ - b θ) * a θ := by
    rw [← integral_sub i1 i2]; congr 1; funext θ; ring
  have hX : 1 ≤ X := hk.trans hkX
  have hKX := (integral_sub_sq_le hg hg₁ hg₂c hc hX).trans (K1_le hc _ _ hX)
  have hKk := (integral_sub_sq_le hg hg₁ hg₂c hc hk).trans (K1_le hc _ _ hk)
  have c1 := abs_inner_le (f := fun θ => a θ - b θ) (ham.sub hbm) ham hda hab hB hKX
  have c2 := abs_inner_le (f := fun θ => q θ - b θ) (hqm.sub hbm) ham hdq hab hB hKk
  have hKb : 0 ≤ Kb := by
    have h0 : 0 ≤ ∫ θ in Ioi 1, (q θ - b θ) ^ 2 :=
      setIntegral_nonneg_of_ae (Eventually.of_forall fun θ => sq_nonneg _)
    have := h0.trans hKk
    have hs : 0 < √k := Real.sqrt_pos.mpr (by linarith)
    exact (div_nonneg_iff.mp this).elim (fun h => h.1) fun h => absurd h.2 (not_le.mpr hs)
  have hmono : √(Kb / √X) ≤ √(Kb / √k) :=
    Real.sqrt_le_sqrt (div_le_div_of_nonneg_left hKb (Real.sqrt_pos.mpr (by linarith))
      (Real.sqrt_le_sqrt hkX))
  rw [hsplit]
  calc |(∫ θ in Ioi 1, (a θ - b θ) * a θ) - ∫ θ in Ioi 1, (q θ - b θ) * a θ|
      ≤ |∫ θ in Ioi 1, (a θ - b θ) * a θ| + |∫ θ in Ioi 1, (q θ - b θ) * a θ| := abs_sub _ _
    _ ≤ √(Kb / √X) * B + √(Kb / √k) * B := add_le_add c1 c2
    _ ≤ 2 * B * √(Kb / √k) := by nlinarith [mul_le_mul_of_nonneg_right hmono hB]

/-- **The level bound at `∞`**: `|⟨F_∞, F_∞ − F_k⟩| ≤ B_G √(K1b/√k)` for `k ≥ 1`. -/
theorem abs_level_inf_le (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hc : 0 < c) {k : ℝ} (hk : 1 ≤ k) :
    |∫ θ in Ioi 1, fullTail (psi c g) θ * (fullTail (psi c g) θ - posTail (psi c g) k θ)|
      ≤ BG c (g 1 + g (-1)) (|g₁ 1 - g₁ (-1)| + ∫ s in (-1 : ℝ)..1, |g₂ s|)
        * √(K1b c (g 1 + g (-1)) (|g₁ 1 - g₁ (-1)| + ∫ s in (-1 : ℝ)..1, |g₂ s|) / √k) := by
  set B := BG c (g 1 + g (-1)) (|g₁ 1 - g₁ (-1)| + ∫ s in (-1 : ℝ)..1, |g₂ s|)
  have hB : 0 ≤ B := BG_nonneg hc _ (C1_nonneg g₁ g₂)
  set q := posTail (psi c g) k
  set b := fullTail (psi c g)
  have hqm := measurable_posTail_psi hg c k
  have hbm := measurable_fullTail hg hg₁ hg₂c hc
  have hbb : ∀ θ, 0 < θ → |b θ| ≤ B / θ := fun θ hθ => abs_fullTail_le hg hg₁ hg₂c hc hθ
  have hdq : ∀ θ, 0 < θ → |q θ - b θ| ≤ 2 * B / θ := fun θ hθ => abs_posTail_sub_le hg hg₁ hg₂c hc k hθ
  have he : ∫ θ in Ioi 1, b θ * (b θ - q θ) = -∫ θ in Ioi 1, (q θ - b θ) * b θ := by
    rw [← integral_neg]; congr 1; funext θ; ring
  have hKk := (integral_sub_sq_le hg hg₁ hg₂c hc hk).trans (K1_le hc _ _ hk)
  rw [he, abs_neg, mul_comm B]
  exact abs_inner_le (f := fun θ => q θ - b θ) (hqm.sub hbm) hbm hdq hbb hB hKk

/-- **The level rate**: `|⟨F_X, F_X − F_k⟩ − ⟨F_∞, F_∞ − F_k⟩| ≤ 3 B_G √(K1b/√X)` for `X ≥ 1` and every `k`. -/
theorem abs_level_sub_le (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hc : 0 < c) {X : ℝ} (hX : 1 ≤ X) (k : ℝ) :
    |(∫ θ in Ioi 1, posTail (psi c g) X θ * (posTail (psi c g) X θ - posTail (psi c g) k θ))
        - ∫ θ in Ioi 1, fullTail (psi c g) θ * (fullTail (psi c g) θ - posTail (psi c g) k θ)|
      ≤ 3 * BG c (g 1 + g (-1)) (|g₁ 1 - g₁ (-1)| + ∫ s in (-1 : ℝ)..1, |g₂ s|)
        * √(K1b c (g 1 + g (-1)) (|g₁ 1 - g₁ (-1)| + ∫ s in (-1 : ℝ)..1, |g₂ s|) / √X) := by
  set B := BG c (g 1 + g (-1)) (|g₁ 1 - g₁ (-1)| + ∫ s in (-1 : ℝ)..1, |g₂ s|)
  have hB : 0 ≤ B := BG_nonneg hc _ (C1_nonneg g₁ g₂)
  set a := posTail (psi c g) X
  set q := posTail (psi c g) k
  set b := fullTail (psi c g)
  have ham := measurable_posTail_psi hg c X
  have hqm := measurable_posTail_psi hg c k
  have hbm := measurable_fullTail hg hg₁ hg₂c hc
  have hab : ∀ θ, 0 < θ → |a θ| ≤ B / θ := fun θ hθ => abs_posTail_le hg hg₁ hg₂c hc X hθ
  have hqb : ∀ θ, 0 < θ → |q θ| ≤ B / θ := fun θ hθ => abs_posTail_le hg hg₁ hg₂c hc k hθ
  have hbb : ∀ θ, 0 < θ → |b θ| ≤ B / θ := fun θ hθ => abs_fullTail_le hg hg₁ hg₂c hc hθ
  have hda : ∀ θ, 0 < θ → |a θ - b θ| ≤ 2 * B / θ := fun θ hθ => abs_posTail_sub_le hg hg₁ hg₂c hc X hθ
  have hw : ∀ θ, 0 < θ → |a θ - q θ + b θ| ≤ 3 * B / θ := fun θ hθ => by
    have h1 := hab θ hθ; have h2 := hqb θ hθ; have h3 := hbb θ hθ
    have := abs_add_three (a θ) (-q θ) (b θ)
    rw [abs_neg] at this
    calc |a θ - q θ + b θ| = |a θ + -q θ + b θ| := by ring_nf
      _ ≤ B / θ + B / θ + B / θ := by linarith
      _ = 3 * B / θ := by ring
  have hdiff : ∀ θ, 0 < θ → |a θ - q θ| ≤ 2 * B / θ := fun θ hθ => by
    have := abs_sub (a θ) (q θ); rw [mul_div_assoc]; linarith [hab θ hθ, hqb θ hθ]
  have i1 : IntegrableOn (fun θ => a θ * (a θ - q θ)) (Ioi 1) :=
    integrableOn_mul_of_le (h := fun θ => a θ - q θ) ham (ham.sub hqm) hab hdiff
  have hdiff' : ∀ θ, 0 < θ → |b θ - q θ| ≤ 2 * B / θ := fun θ hθ => by
    have := abs_sub (b θ) (q θ); rw [mul_div_assoc]; linarith [hbb θ hθ, hqb θ hθ]
  have i2 : IntegrableOn (fun θ => b θ * (b θ - q θ)) (Ioi 1) :=
    integrableOn_mul_of_le (h := fun θ => b θ - q θ) hbm (hbm.sub hqm) hbb hdiff'
  have he : (∫ θ in Ioi 1, a θ * (a θ - q θ)) - ∫ θ in Ioi 1, b θ * (b θ - q θ)
      = ∫ θ in Ioi 1, (a θ - b θ) * (a θ - q θ + b θ) := by
    rw [← integral_sub i1 i2]; congr 1; funext θ; ring
  have hKX := (integral_sub_sq_le hg hg₁ hg₂c hc hX).trans (K1_le hc _ _ hX)
  rw [he]
  refine (abs_inner_le (f := fun θ => a θ - b θ) (h := fun θ => a θ - q θ + b θ) (ham.sub hbm)
    ((ham.sub hqm).add hbm) hda hw (by positivity) hKX).trans (le_of_eq ?_)
  ring

/-! ### The level integral and the limit -/

/-- **The level integral converges absolutely**: `k ↦ ⟨F_∞, F_∞ − F_k⟩/k` is integrable on `(1, ∞)`. -/
theorem integrableOn_level (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hc : 0 < c) :
    IntegrableOn (fun k => (∫ θ in Ioi 1, fullTail (psi c g) θ * (fullTail (psi c g) θ - posTail (psi c g) k θ)) / k)
      (Ioi 1) := by
  set B := BG c (g 1 + g (-1)) (|g₁ 1 - g₁ (-1)| + ∫ s in (-1 : ℝ)..1, |g₂ s|)
  set Kb := K1b c (g 1 + g (-1)) (|g₁ 1 - g₁ (-1)| + ∫ s in (-1 : ℝ)..1, |g₂ s|)
  have hB : 0 ≤ B := BG_nonneg hc _ (C1_nonneg g₁ g₂)
  have hcont : Continuous (psi c g) :=
    (contDiff_psi (fun s hs => (hg s hs).continuousAt.continuousWithinAt) c).continuous
  have hmeas := (measurable_level hcont (measurable_fullTail hg hg₁ hg₂c hc)).div measurable_id
  refine Integrable.mono' (((integrableOn_Ioi_rpow_of_lt (show -(5 / 4 : ℝ) < -1 by norm_num)
    one_pos).const_mul (√Kb)).const_mul B) hmeas.aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun k (hk : 1 < k) => ?_))
  have hk0 : 0 < k := one_pos.trans hk
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hk0, ← sqrt_div_sqrt_div_eq Kb hk0, mul_div_assoc']
  exact div_le_div_of_nonneg_right (abs_level_inf_le hg hg₁ hg₂c hc hk.le) hk0.le

/-- **Pointwise convergence of the truncated tail**: `F_X(θ) → F_∞(θ)` for `θ > 1`. -/
theorem tendsto_posTail (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hc : 0 < c) {θ : ℝ} (hθ : 1 < θ) :
    Tendsto (fun X : ℝ => posTail (psi c g) X θ) atTop (𝓝 (fullTail (psi c g) θ)) := by
  have h := (tendsto_partial hg hg₁ hg₂c hc hθ).comp
    (tendsto_nat_floor_atTop.comp (tendsto_id.atTop_div_const (one_pos.trans hθ)))
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop θ] with X hX
  exact (posTail_eq_partial _ hθ hX).symm

/-- **The log term converges**: `∫_{(1,∞)} log θ F_X² → ∫_{(1,∞)} log θ F_∞²`, dominated by `4B_G² θ^{−7/4}`. -/
theorem tendsto_logTerm (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hc : 0 < c) :
    Tendsto (fun X : ℝ => ∫ θ in Ioi 1, Real.log θ * posTail (psi c g) X θ ^ 2) atTop
      (𝓝 (∫ θ in Ioi 1, Real.log θ * fullTail (psi c g) θ ^ 2)) := by
  set B := BG c (g 1 + g (-1)) (|g₁ 1 - g₁ (-1)| + ∫ s in (-1 : ℝ)..1, |g₂ s|)
  refine tendsto_integral_filter_of_dominated_convergence (fun θ => 4 * B ^ 2 * θ ^ (-(7 / 4 : ℝ)))
    (Eventually.of_forall fun X => (measurable_log.mul
      ((measurable_posTail_psi hg c X).pow_const 2)).aestronglyMeasurable)
    (Eventually.of_forall fun X => (ae_restrict_iff' measurableSet_Ioi).2
      (Eventually.of_forall fun θ (hθ : 1 < θ) => ?_))
    ((integrableOn_Ioi_rpow_of_lt (show -(7 / 4 : ℝ) < -1 by norm_num) one_pos).const_mul _)
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun θ (hθ : 1 < θ) =>
      ((tendsto_posTail hg hg₁ hg₂c hc hθ).pow 2).const_mul _))
  have hθ0 : 0 < θ := one_pos.trans hθ
  have hl0 : 0 ≤ Real.log θ := Real.log_nonneg hθ.le
  have hlog : Real.log θ ≤ θ ^ (1 / 4 : ℝ) / (1 / 4) := Real.log_le_rpow_div hθ0.le (by norm_num)
  have hsq : posTail (psi c g) X θ ^ 2 ≤ (B / θ) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (abs_posTail_le hg hg₁ hg₂c hc X hθ0) 2
  have hr : θ ^ (-(7 / 4 : ℝ)) = θ ^ (1 / 4 : ℝ) / θ ^ 2 := by
    rw [show -(7 / 4 : ℝ) = 1 / 4 - 2 by norm_num, rpow_sub hθ0, rpow_two]
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hl0 (sq_nonneg _)), hr]
  calc Real.log θ * posTail (psi c g) X θ ^ 2 ≤ θ ^ (1 / 4 : ℝ) / (1 / 4) * (B / θ) ^ 2 :=
        mul_le_mul hlog hsq (sq_nonneg _) (hl0.trans hlog)
    _ = 4 * B ^ 2 * (θ ^ (1 / 4 : ℝ) / θ ^ 2) := by field_simp

/-- **The prime side converges to `Prime_∞`** along `P = R = ⌊X⌋₊`, `X → ∞`. -/
theorem tendsto_primeSide (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hc : 0 < c) :
    Tendsto (fun X : ℝ => Cvs.Zeta.Explicit.Weil.primePowerSideTruncated ⌊X⌋₊ ⌊X⌋₊
        (Cvs.Zeta.Explicit.Weil.selfConvolution (Cvs.L2a.TailLogScaleTest.logScale (posTail (psi c g) X))))
      atTop (𝓝 (primeInf (psi c g))) := by
  set B := BG c (g 1 + g (-1)) (|g₁ 1 - g₁ (-1)| + ∫ s in (-1 : ℝ)..1, |g₂ s|)
  set Kb := K1b c (g 1 + g (-1)) (|g₁ 1 - g₁ (-1)| + ∫ s in (-1 : ℝ)..1, |g₂ s|)
  have hB : 0 ≤ B := BG_nonneg hc _ (C1_nonneg g₁ g₂)
  have hcont : Continuous (psi c g) :=
    (contDiff_psi (fun s hs => (hg s hs).continuousAt.continuousWithinAt) c).continuous
  set L : ℝ → ℝ → ℝ := fun X k =>
    (Ioc 1 X).indicator (fun k => (∫ θ in Ioi 1, posTail (psi c g) X θ
      * (posTail (psi c g) X θ - posTail (psi c g) k θ)) / k) k with hLd
  have heq : (fun X : ℝ => 2 * (∫ k in Ioi 1, L X k)
        - 2 * ∫ θ in Ioi 1, Real.log θ * posTail (psi c g) X θ ^ 2)
      =ᶠ[atTop] fun X : ℝ => Cvs.Zeta.Explicit.Weil.primePowerSideTruncated ⌊X⌋₊ ⌊X⌋₊
        (Cvs.Zeta.Explicit.Weil.selfConvolution (Cvs.L2a.TailLogScaleTest.logScale (posTail (psi c g) X))) := by
    filter_upwards [eventually_ge_atTop 1] with X hX
    rw [Cvs.L2a.PositionTailPrimeLevels.primeSide_posTail_levels (psi c g) hX hcont.continuousOn ⌊X⌋₊ ⌊X⌋₊
      (fun k hk hkX => Cvs.L2a.PositionTailSpanAdapters.mem_primePowIndex_floor hk hkX),
      intervalIntegral.integral_of_le hX]
    simp only [hLd]
    rw [setIntegral_indicator measurableSet_Ioc, Set.inter_eq_right.mpr Ioc_subset_Ioi_self]
  have hA : Tendsto (fun X : ℝ => ∫ k in Ioi 1, L X k) atTop
      (𝓝 (∫ k in Ioi 1, (∫ θ in Ioi 1, fullTail (psi c g) θ
        * (fullTail (psi c g) θ - posTail (psi c g) k θ)) / k)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun k => 2 * B * (√Kb * k ^ (-(5 / 4 : ℝ))))
      (Eventually.of_forall fun X => ?_) (Eventually.of_forall fun X => (ae_restrict_iff' measurableSet_Ioi).2
        (Eventually.of_forall fun k (hk : 1 < k) => ?_))
      (((integrableOn_Ioi_rpow_of_lt (show -(5 / 4 : ℝ) < -1 by norm_num) one_pos).const_mul (√Kb)).const_mul
        (2 * B))
      ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun k (hk : 1 < k) => ?_))
    · exact (((measurable_level hcont (measurable_posTail_psi hg c X)).div measurable_id).indicator
        measurableSet_Ioc).aestronglyMeasurable
    · have hk0 : 0 < k := one_pos.trans hk
      have hb0 : 0 ≤ 2 * B * (√Kb * k ^ (-(5 / 4 : ℝ))) := by positivity
      simp only [hLd]
      by_cases hkX : k ∈ Ioc 1 X
      · rw [indicator_of_mem hkX, Real.norm_eq_abs, abs_div, abs_of_pos hk0, ← sqrt_div_sqrt_div_eq Kb hk0,
          ← mul_div_assoc]
        exact div_le_div_of_nonneg_right (abs_level_le hg hg₁ hg₂c hc hk.le hkX.2) hk0.le
      · rw [indicator_of_notMem hkX, norm_zero]; exact hb0
    · have hk0 : 0 < k := one_pos.trans hk
      have hconv : Tendsto (fun X : ℝ => ∫ θ in Ioi 1, posTail (psi c g) X θ
          * (posTail (psi c g) X θ - posTail (psi c g) k θ)) atTop
          (𝓝 (∫ θ in Ioi 1, fullTail (psi c g) θ * (fullTail (psi c g) θ - posTail (psi c g) k θ))) := by
        rw [tendsto_iff_norm_sub_tendsto_zero]
        have hu := (tendsto_sqrt_div_sqrt Kb).const_mul (3 * B)
        rw [mul_zero] at hu
        refine squeeze_zero' (Eventually.of_forall fun X => norm_nonneg _) ?_ hu
        filter_upwards [eventually_ge_atTop 1] with X hX
        rw [Real.norm_eq_abs]
        exact abs_level_sub_le hg hg₁ hg₂c hc hX k
      refine (hconv.div_const k).congr' ?_
      filter_upwards [eventually_ge_atTop k] with X hX
      simp only [hLd]
      rw [indicator_of_mem (show k ∈ Ioc 1 X from ⟨hk, hX⟩)]
  have hlim := ((hA.const_mul 2).sub ((tendsto_logTerm hg hg₁ hg₂c hc).const_mul 2)).congr' heq
  exact hlim

end Cvs.L2a.FullTailPrimeChannel
