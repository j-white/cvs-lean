import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.PositionTruncatedTail
import Cvs.L2a.TailLogScaleTest
import Cvs.Prolate.CosineTransformSecondOrder
import Cvs.Prolate.SlepianCommutingRelation
import Cvs.Upstream.PoissonSummationDini
import Cvs.Upstream.SawtoothPartialSums

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The full tail `F_∞(θ) = Σ_{m≥1} ψ(mθ)` and the `L²` rate of `F_X → F_∞`

For `g ∈ C²[−1, 1]`, `ψ = psi c g`: `F_∞` is the Poisson piece `(π/(cθ)) Σ_{|n|≤k} g(2πn/(cθ)) − ½∫g` off
`(2π/c)ℤ`, `|F_X|, |F_∞| ≤ B_G/θ`, `‖F_X − F_∞‖² ≤ K1(X) ≤ K1b/√X`, and energies and Gram entries converge.
-/

namespace Cvs.L2a.FullTailConvergence

open Real Set Filter Topology MeasureTheory Cvs.L2a.AngularProlateTailPositive Cvs.L2a.PositionTruncatedTail

/-- The full tail `F_∞(θ) = Σ_{m≥1} Φ(mθ)` on `θ > 1`, as the limit of the partial sums; `0` for `θ ≤ 1`. -/
noncomputable def fullTail (Φ : ℝ → ℝ) (θ : ℝ) : ℝ :=
  if 1 < θ then limUnder atTop (fun M : ℕ => ∑ m ∈ Finset.Icc 1 M, Φ (m * θ)) else 0

/-- The pointwise constant `B_G = (1 + π)|A|/c + (π²/6) C₁/c²`. -/
noncomputable def BG (c A C1 : ℝ) : ℝ := (1 + π) * |A| / c + π ^ 2 / 6 * C1 / c ^ 2

/-- The `L²` rate `K1(X)` of `F_X → F_∞`. -/
noncomputable def K1 (c A C1 X : ℝ) : ℝ :=
  16 * (1 + π) * A ^ 2 * (Real.logb 2 X + 1 + 8 * π / c) / (c ^ 2 * X) + 8 * C1 ^ 2 / (c ^ 4 * X ^ 2)
    + BG c A C1 ^ 2 / X

/-- The constant `K1b` with `K1(X) ≤ K1b/√X`. -/
noncomputable def K1b (c A C1 : ℝ) : ℝ :=
  16 * (1 + π) * A ^ 2 * (3 + 8 * π / c) / c ^ 2 + 8 * C1 ^ 2 / c ^ 4 + BG c A C1 ^ 2

/-- The Poisson piece `(π/(cθ)) Σ_{|n|≤k} g(2πn/(cθ)) − ½∫_{−1}^{1} g`. -/
noncomputable def poissonPiece (c : ℝ) (g : ℝ → ℝ) (k : ℕ) (θ : ℝ) : ℝ :=
  π / (c * θ) * ∑ n ∈ Finset.Icc (-(k : ℤ)) k, g (2 * π * n / (c * θ)) - 1 / 2 * ∫ s in (-1 : ℝ)..1, g s

variable {g g₁ g₂ : ℝ → ℝ} {c : ℝ}

/-! ### Generic lemmas -/

/-- `1/θ²` is integrable on `(a, ∞)` for `a > 0`. -/
theorem integrableOn_one_div_sq {a : ℝ} (ha : 0 < a) : IntegrableOn (fun θ : ℝ => 1 / θ ^ 2) (Ioi a) := by
  refine (integrableOn_Ioi_rpow_of_lt (show (-2 : ℝ) < -1 by norm_num) ha).congr_fun (fun θ hθ => ?_)
    measurableSet_Ioi
  have hθ : 0 < θ := ha.trans hθ
  show θ ^ (-2 : ℝ) = 1 / θ ^ 2
  rw [rpow_neg hθ.le, rpow_two, one_div]

/-- `∫_{(a,∞)} 1/θ² = 1/a` for `a > 0`. -/
theorem integral_one_div_sq {a : ℝ} (ha : 0 < a) : ∫ θ in Ioi a, 1 / θ ^ 2 = 1 / a := by
  have h := integral_Ioi_rpow_of_lt (show (-2 : ℝ) < -1 by norm_num) ha
  have e : ∫ θ in Ioi a, 1 / θ ^ 2 = ∫ θ in Ioi a, θ ^ (-2 : ℝ) :=
    setIntegral_congr_fun measurableSet_Ioi fun θ hθ => by
      have hθ : 0 < θ := ha.trans hθ
      rw [rpow_neg hθ.le, rpow_two, one_div]
  rw [e, h]
  norm_num
  rw [rpow_neg_one]

/-- A product of two measurable functions bounded by `K/θ` and `K'/θ` is integrable on `(1, ∞)`. -/
theorem integrableOn_mul_of_le {f h : ℝ → ℝ} {K K' : ℝ} (hf : Measurable f) (hh : Measurable h)
    (hfK : ∀ θ, 0 < θ → |f θ| ≤ K / θ) (hhK : ∀ θ, 0 < θ → |h θ| ≤ K' / θ) :
    IntegrableOn (fun θ => f θ * h θ) (Ioi 1) := by
  refine Integrable.mono' ((integrableOn_one_div_sq one_pos).const_mul (K * K'))
    (hf.mul hh).aestronglyMeasurable ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall
      fun θ (hθ : 1 < θ) => ?_))
  have hθ0 : 0 < θ := one_pos.trans hθ
  rw [Real.norm_eq_abs, abs_mul]
  calc |f θ| * |h θ| ≤ K / θ * (K' / θ) :=
        mul_le_mul (hfK θ hθ0) (hhK θ hθ0) (abs_nonneg _) ((abs_nonneg _).trans (hfK θ hθ0))
    _ = K * K' * (1 / θ ^ 2) := by field_simp

/-- **Cauchy–Schwarz on a set**, by the discriminant. -/
theorem sq_setIntegral_mul_le {S : Set ℝ} {f w : ℝ → ℝ} (hf : IntegrableOn (fun s => f s ^ 2) S)
    (hw : IntegrableOn (fun s => w s ^ 2) S) (hfw : IntegrableOn (fun s => f s * w s) S) :
    (∫ s in S, f s * w s) ^ 2 ≤ (∫ s in S, f s ^ 2) * ∫ s in S, w s ^ 2 := by
  have key : ∀ t : ℝ, 0 ≤ (∫ s in S, w s ^ 2) * (t * t) + (-2 * ∫ s in S, f s * w s) * t
      + ∫ s in S, f s ^ 2 := by
    intro t
    have hsq : (0 : ℝ) ≤ ∫ s in S, (f s - t * w s) ^ 2 := setIntegral_nonneg_of_ae (by
      exact Eventually.of_forall fun s => sq_nonneg _) |>.trans_eq rfl
    have hexp : ∫ s in S, (f s - t * w s) ^ 2
        = (∫ s in S, f s ^ 2) - 2 * t * (∫ s in S, f s * w s) + t ^ 2 * ∫ s in S, w s ^ 2 := by
      have i1 : IntegrableOn (fun s => f s ^ 2 - 2 * t * (f s * w s)) S := hf.sub (hfw.const_mul _)
      have i2 : IntegrableOn (fun s => t ^ 2 * w s ^ 2) S := hw.const_mul _
      rw [← integral_const_mul, ← integral_const_mul, ← integral_sub hf (hfw.const_mul _),
        ← integral_add i1 i2]
      congr 1; funext s; ring
    rw [hexp] at hsq
    linarith
  have hd := discrim_le_zero key
  unfold discrim at hd
  nlinarith

/-- `|∫ f w| ≤ √(∫ f²) √(∫ w²)` on a set. -/
theorem abs_setIntegral_mul_le {S : Set ℝ} {f w : ℝ → ℝ} (hf : IntegrableOn (fun s => f s ^ 2) S)
    (hw : IntegrableOn (fun s => w s ^ 2) S) (hfw : IntegrableOn (fun s => f s * w s) S) :
    |∫ s in S, f s * w s| ≤ √(∫ s in S, f s ^ 2) * √(∫ s in S, w s ^ 2) := by
  rw [← Real.sqrt_mul (setIntegral_nonneg_of_ae (Eventually.of_forall fun s => sq_nonneg (f s)))]
  exact Real.abs_le_sqrt (sq_setIntegral_mul_le hf hw hfw)

/-- `Σ_{m ∈ (M, N]} 1/m² ≤ 1/M` for `M ≥ 1`. -/
theorem sum_Ioc_one_div_sq_le {M : ℕ} (hM : 1 ≤ M) (N : ℕ) :
    ∑ m ∈ Finset.Ioc M N, 1 / (m : ℝ) ^ 2 ≤ 1 / (M : ℝ) := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  rcases lt_or_ge N M with h | h
  · rw [Finset.Ioc_eq_empty (by omega)]; simp only [Finset.sum_empty]; positivity
  have key : ∀ N, M ≤ N → ∑ m ∈ Finset.Ioc M N, 1 / (m : ℝ) ^ 2 ≤ 1 / (M : ℝ) - 1 / (N : ℝ) := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base => simp
    | succ n hn ih =>
      rw [Finset.sum_Ioc_succ_top hn]
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have h1 : 1 / (((n + 1 : ℕ) : ℝ)) ^ 2 ≤ 1 / n - 1 / ((n + 1 : ℕ) : ℝ) := by
        push_cast
        rw [div_sub_div _ _ hn0.ne' (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      push_cast at h1 ⊢
      linarith
  have := key N h
  have hN0 : (0 : ℝ) ≤ 1 / N := by positivity
  linarith

/-! ### The cosine transform -/

/-- **The cosine transform is `C¹`** for `g` continuous on `[−1, 1]`. -/
theorem contDiff_psi (hgc : ContinuousOn g (uIcc (-1) 1)) (c : ℝ) : ContDiff ℝ 1 (psi c g) := by
  have h1 : ∀ ξ, HasDerivAt (psi c g) (Cvs.Prolate.SlepianCommutingRelation.kint g
      (fun ξ s => -(c * s * Real.sin (c * ξ * s))) ξ) ξ := fun ξ =>
    Cvs.Prolate.SlepianCommutingRelation.hasDerivAt_kint (C := |c|) hgc (fun s => by fun_prop) (fun ξ => by fun_prop)
      (fun ξ => by fun_prop)
      (fun ξ s => by
        have h := (((hasDerivAt_id ξ).const_mul c).mul_const s).cos
        exact h.congr_deriv (by simp only [id, mul_one]; ring))
      (fun ξ s hs => by
        rw [abs_neg, abs_mul, abs_mul]
        have := abs_sin_le_one (c * ξ * s)
        have h0 : 0 ≤ |c| * |s| := by positivity
        calc |c| * |s| * |Real.sin (c * ξ * s)| ≤ |c| * 1 * 1 :=
              mul_le_mul (mul_le_mul_of_nonneg_left hs (abs_nonneg _)) this (abs_nonneg _) (by positivity)
          _ = |c| := by ring) ξ
  have h2 : ∀ ξ, HasDerivAt (Cvs.Prolate.SlepianCommutingRelation.kint g (fun ξ s => -(c * s * Real.sin (c * ξ * s))))
      (Cvs.Prolate.SlepianCommutingRelation.kint g (fun ξ s => -(c * s * (c * s * Real.cos (c * ξ * s)))) ξ) ξ := fun ξ =>
    Cvs.Prolate.SlepianCommutingRelation.hasDerivAt_kint (C := c ^ 2) hgc (fun s => by fun_prop) (fun ξ => by fun_prop)
      (fun ξ => by fun_prop)
      (fun ξ s => by
        have h := (((hasDerivAt_id ξ).const_mul c).mul_const s).sin.const_mul (c * s)
        exact h.neg.congr_deriv (by simp only [id, mul_one]; ring))
      (fun ξ s hs => by
        rw [abs_neg, abs_mul, abs_mul, abs_mul, abs_mul]
        have := abs_cos_le_one (c * ξ * s)
        have hs2 : |s| * |s| ≤ 1 := by nlinarith [abs_nonneg s]
        calc |c| * |s| * (|c| * |s| * |Real.cos (c * ξ * s)|) ≤ |c| * |s| * (|c| * |s| * 1) := by gcongr
          _ = |c| ^ 2 * (|s| * |s|) := by ring
          _ ≤ |c| ^ 2 * 1 := by gcongr
          _ = c ^ 2 := by rw [sq_abs, mul_one]) ξ
  rw [contDiff_one_iff_deriv]
  refine ⟨fun ξ => (h1 ξ).differentiableAt, ?_⟩
  have e : deriv (psi c g) = Cvs.Prolate.SlepianCommutingRelation.kint g (fun ξ s => -(c * s * Real.sin (c * ξ * s))) :=
    funext fun ξ => (h1 ξ).deriv
  rw [e]
  exact continuous_iff_continuousAt.2 fun ξ => (h2 ξ).continuousAt

/-- **The cosine transform is linear** in the profile. -/
theorem psi_sum {ι : Type*} (s : Finset ι) (a : ι → ℝ) (G : ι → ℝ → ℝ)
    (hG : ∀ i ∈ s, IntervalIntegrable (G i) volume (-1) 1) (c ξ : ℝ) :
    psi c (fun t => ∑ i ∈ s, a i * G i t) ξ = ∑ i ∈ s, a i * psi c (G i) ξ := by
  unfold psi Cvs.Prolate.SlepianCommutingRelation.kint
  simp_rw [Finset.sum_mul]
  rw [intervalIntegral.integral_finsetSum fun i hi =>
    (((hG i hi).const_mul (a i)).mul_continuousOn (by fun_prop : Continuous fun t =>
      Real.cos (c * ξ * t)).continuousOn)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← intervalIntegral.integral_const_mul]
  congr 1; funext t; ring

/-! ### Partial sums and pointwise bounds -/

/-- The constant `C₁ = |g₁(1) − g₁(−1)| + ∫|g₂|` is nonnegative. -/
theorem C1_nonneg (g₁ g₂ : ℝ → ℝ) : 0 ≤ |g₁ 1 - g₁ (-1)| + ∫ s in (-1 : ℝ)..1, |g₂ s| :=
  add_nonneg (abs_nonneg _) (intervalIntegral.integral_nonneg (by norm_num) fun _ _ => abs_nonneg _)

/-- `B_G ≥ 0`. -/
theorem BG_nonneg (hc : 0 < c) (A : ℝ) {C1 : ℝ} (hC1 : 0 ≤ C1) : 0 ≤ BG c A C1 := by
  unfold BG; have := pi_pos; positivity

/-- A sum over `[1, M]` is the sum over `[0, M]` less the `0` term. -/
theorem sum_Icc_one_eq (f : ℕ → ℝ) (M : ℕ) :
    ∑ m ∈ Finset.Icc 1 M, f m = ∑ m ∈ Finset.range (M + 1), f m - f 0 := by
  induction M with
  | zero => simp
  | succ n ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ _ (n + 1)]; ring

/-- **Sawtooth plus remainder**: over modes `m ≥ 1`, `Σ ψ(mθ)` is `(A/(cθ)) Σ sin(mcθ)/m` to
`(C₁/(cθ)²) Σ 1/m²`. -/
theorem abs_sum_sub_le (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hc : 0 < c) {θ : ℝ} (hθ : 0 < θ) (t : Finset ℕ) (ht : ∀ m ∈ t, 1 ≤ m) :
    |∑ m ∈ t, psi c g (m * θ) - (g 1 + g (-1)) / (c * θ) * ∑ m ∈ t, Real.sin (m * (c * θ)) / m|
      ≤ (|g₁ 1 - g₁ (-1)| + ∫ s in (-1 : ℝ)..1, |g₂ s|) / (c * θ) ^ 2 * ∑ m ∈ t, 1 / (m : ℝ) ^ 2 := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m hm => ?_)
  have hm : (0 : ℝ) < m := by exact_mod_cast ht m hm
  have h := Cvs.Prolate.CosineTransformSecondOrder.psi_sub_le hg hg₁ hg₂c (c := c) (ξ := m * θ) (by positivity)
  have e : (g 1 + g (-1)) / (c * θ) * (Real.sin (m * (c * θ)) / m)
      = (g 1 + g (-1)) * Real.sin (c * (m * θ)) / (c * (m * θ)) := by
    rw [show (m : ℝ) * (c * θ) = c * (m * θ) by ring]; field_simp
  rw [e]
  refine h.trans (le_of_eq ?_)
  field_simp

/-- **The partial sums converge** for `θ > 1`, to the full tail. -/
theorem tendsto_partial (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hc : 0 < c) {θ : ℝ} (hθ : 1 < θ) :
    Tendsto (fun M : ℕ => ∑ m ∈ Finset.Icc 1 M, psi c g (m * θ)) atTop (𝓝 (fullTail (psi c g) θ)) := by
  rw [fullTail, ite_eq_left hθ]
  apply tendsto_nhds_limUnder
  have hθ0 : 0 < θ := by linarith
  set A := g 1 + g (-1) with hA
  set C1 := |g₁ 1 - g₁ (-1)| + ∫ s in (-1 : ℝ)..1, |g₂ s| with hC1
  set t : ℕ → ℝ := fun m => psi c g (m * θ) - A / (c * θ) * (Real.sin (m * (c * θ)) / m) with ht
  have hsum : Summable t := by
    refine Summable.of_norm_bounded_eventually_nat (hasSum_zeta_two.summable.mul_left (C1 / (c * θ) ^ 2)) ?_
    filter_upwards [eventually_ge_atTop 1] with m hm
    rw [Real.norm_eq_abs]
    have := abs_sum_sub_le hg hg₁ hg₂c hc hθ0 {m} (by simpa using hm)
    simpa only [Finset.sum_singleton] using this
  obtain ⟨T, hT⟩ := hsum
  obtain ⟨S, hS⟩ := cauchySeq_tendsto_of_complete (Cvs.Upstream.SawtoothPartialSums.cauchySeq_sum_sin_div (c * θ))
  refine ⟨A / (c * θ) * S + (T - t 0), ?_⟩
  have hR : Tendsto (fun M : ℕ => ∑ m ∈ Finset.Icc 1 M, t m) atTop (𝓝 (T - t 0)) := by
    have := (hT.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)).sub_const (t 0)
    refine this.congr fun M => ?_
    rw [sum_Icc_one_eq]; rfl
  refine ((hS.const_mul (A / (c * θ))).add hR).congr fun M => ?_
  simp only [ht, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

/-- **The partial sums are `O(1/θ)`** for `θ ≥ 1`: `|Σ_{m≤M} ψ(mθ)| ≤ B_G/θ`. -/
theorem abs_partial_le (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hc : 0 < c) {θ : ℝ} (hθ : 1 ≤ θ) (M : ℕ) :
    |∑ m ∈ Finset.Icc 1 M, psi c g (m * θ)|
      ≤ BG c (g 1 + g (-1)) (|g₁ 1 - g₁ (-1)| + ∫ s in (-1 : ℝ)..1, |g₂ s|) / θ := by
  have hθ0 : 0 < θ := by linarith
  have h := abs_sum_sub_le hg hg₁ hg₂c hc hθ0 (Finset.Icc 1 M) (fun m hm => (Finset.mem_Icc.mp hm).1)
  have hS := Cvs.Upstream.SawtoothPartialSums.abs_sum_sin_div_le M (c * θ)
  have hZ : ∑ m ∈ Finset.Icc 1 M, 1 / (m : ℝ) ^ 2 ≤ π ^ 2 / 6 :=
    sum_le_hasSum _ (fun i _ => by positivity) hasSum_zeta_two
  have hC1 := C1_nonneg g₁ g₂
  set A := g 1 + g (-1) with hA
  set C1 := |g₁ 1 - g₁ (-1)| + ∫ s in (-1 : ℝ)..1, |g₂ s| with hC1d
  set P := ∑ m ∈ Finset.Icc 1 M, psi c g (m * θ)
  set Sw := ∑ m ∈ Finset.Icc 1 M, Real.sin (m * (c * θ)) / m
  have hcθ : 0 < c * θ := by positivity
  have h1 : |A / (c * θ) * Sw| ≤ |A| / (c * θ) * (1 + π) := by
    rw [abs_mul, abs_div, abs_of_pos hcθ]
    exact mul_le_mul_of_nonneg_left hS (by positivity)
  have h2 : C1 / (c * θ) ^ 2 * ∑ m ∈ Finset.Icc 1 M, 1 / (m : ℝ) ^ 2 ≤ C1 / c ^ 2 / θ * (π ^ 2 / 6) := by
    have h3 : C1 / (c * θ) ^ 2 ≤ C1 / c ^ 2 / θ := by
      rw [mul_pow, ← div_div]
      exact div_le_div_of_nonneg_left (by positivity) hθ0 (by nlinarith)
    exact mul_le_mul h3 hZ (Finset.sum_nonneg fun _ _ => by positivity) (by positivity)
  have h4 := abs_sub_abs_le_abs_sub P (A / (c * θ) * Sw)
  have e : BG c A C1 / θ = |A| / (c * θ) * (1 + π) + C1 / c ^ 2 / θ * (π ^ 2 / 6) := by
    unfold BG; field_simp
  rw [e]
  linarith

/-- On `(1, X]` the position-truncated tail is the partial sum to `⌊X/θ⌋`. -/
theorem posTail_eq_partial (Φ : ℝ → ℝ) {X θ : ℝ} (hθ : 1 < θ) (hθX : θ ≤ X) :
    posTail Φ X θ = ∑ m ∈ Finset.Icc 1 ⌊X / θ⌋₊, Φ (m * θ) := by
  rw [posTail_eq_sum]
  have hθ0 : 0 < θ := by linarith
  have hX0 : 0 < X := by linarith
  have hsub : Finset.Icc 1 ⌊X / θ⌋₊ ⊆ Finset.Icc 1 ⌊X⌋₊ :=
    Finset.Icc_subset_Icc le_rfl (Nat.floor_le_floor (div_le_self hX0.le hθ.le))
  have hiff : ∀ m : ℕ, 1 ≤ m → (θ ≤ X / m ↔ m ≤ ⌊X / θ⌋₊) := by
    intro m hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
    rw [Nat.le_floor_iff (by positivity), le_div_iff₀ hm0, le_div_iff₀ hθ0, mul_comm]
  symm
  rw [show ∑ m ∈ Finset.Icc 1 ⌊X / θ⌋₊, Φ (m * θ)
      = ∑ m ∈ Finset.Icc 1 ⌊X / θ⌋₊, Set.indicator (Ioc 1 (X / m)) (fun θ => Φ (m * θ)) θ from
    Finset.sum_congr rfl fun m hm => by
      have hm' := Finset.mem_Icc.mp hm
      rw [indicator_of_mem (show θ ∈ Ioc 1 (X / m) from ⟨hθ, (hiff m hm'.1).2 hm'.2⟩)]]
  refine Finset.sum_subset hsub fun m hm hnot => indicator_of_notMem (fun h => hnot ?_) _
  have hm' := Finset.mem_Icc.mp hm
  exact Finset.mem_Icc.mpr ⟨hm'.1, (hiff m hm'.1).1 h.2⟩

/-- **The position-truncated tail is `O(1/θ)`**: `|F_X(θ)| ≤ B_G/θ`. -/
theorem abs_posTail_le (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hc : 0 < c) (X : ℝ) {θ : ℝ} (hθ : 0 < θ) :
    |posTail (psi c g) X θ|
      ≤ BG c (g 1 + g (-1)) (|g₁ 1 - g₁ (-1)| + ∫ s in (-1 : ℝ)..1, |g₂ s|) / θ := by
  have hB := div_nonneg (BG_nonneg hc (g 1 + g (-1)) (C1_nonneg g₁ g₂)) hθ.le
  rcases le_or_gt θ 1 with h1 | h1
  · rw [posTail_zero _ _ h1, abs_zero]; exact hB
  rcases lt_or_ge X θ with h2 | h2
  · rw [posTail_of_gt _ h2, abs_zero]; exact hB
  rw [posTail_eq_partial _ h1 h2]
  exact abs_partial_le hg hg₁ hg₂c hc h1.le _

/-- **The full tail is `O(1/θ)`**: `|F_∞(θ)| ≤ B_G/θ`. -/
theorem abs_fullTail_le (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hc : 0 < c) {θ : ℝ} (hθ : 0 < θ) :
    |fullTail (psi c g) θ|
      ≤ BG c (g 1 + g (-1)) (|g₁ 1 - g₁ (-1)| + ∫ s in (-1 : ℝ)..1, |g₂ s|) / θ := by
  have hB := div_nonneg (BG_nonneg hc (g 1 + g (-1)) (C1_nonneg g₁ g₂)) hθ.le
  rcases le_or_gt θ 1 with h1 | h1
  · rw [fullTail, ite_eq_right (not_lt.mpr h1), abs_zero]; exact hB
  exact le_of_tendsto (tendsto_partial hg hg₁ hg₂c hc h1).abs
    (Eventually.of_forall fun M => abs_partial_le hg hg₁ hg₂c hc h1.le M)

/-! ### Measurability and `L²` -/

/-- The position-truncated tail of a continuous profile is measurable. -/
theorem measurable_posTail {Φ : ℝ → ℝ} (hΦ : Continuous Φ) (X : ℝ) : Measurable (posTail Φ X) := by
  rw [show posTail Φ X = fun θ => ∑ m ∈ Finset.Icc 1 ⌊X⌋₊,
      Set.indicator (Ioc 1 (X / m)) (fun θ => Φ (m * θ)) θ from funext (posTail_eq_sum Φ X)]
  exact Finset.measurable_sum _ fun m _ =>
    (hΦ.measurable.comp (measurable_const.mul measurable_id)).indicator measurableSet_Ioc

/-- **The full tail is measurable.** -/
theorem measurable_fullTail (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hc : 0 < c) : Measurable (fullTail (psi c g)) := by
  have hcont : Continuous (psi c g) :=
    (contDiff_psi (fun s hs => (hg s hs).continuousAt.continuousWithinAt) c).continuous
  refine measurable_of_tendsto_metrizable (f := fun M θ => (Ioi (1 : ℝ)).indicator
    (fun θ => ∑ m ∈ Finset.Icc 1 M, psi c g (m * θ)) θ) (fun M => ?_) ?_
  · exact (Finset.measurable_sum _ fun m _ =>
      hcont.measurable.comp (measurable_const.mul measurable_id)).indicator measurableSet_Ioi
  · rw [tendsto_pi_nhds]
    intro θ
    by_cases h : 1 < θ
    · simp only [indicator_of_mem (show θ ∈ Ioi (1 : ℝ) from h)]
      exact tendsto_partial hg hg₁ hg₂c hc h
    · simp only [indicator_of_notMem (show θ ∉ Ioi (1 : ℝ) from h)]
      rw [fullTail, ite_eq_right h]
      exact tendsto_const_nhds

/-- **The log-scale full tail is in `L²` and `L¹`**: `|f_∞(s)| ≤ B_G e^{−s/2} 1_{s>0}`. -/
theorem memLp_logScale_fullTail (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hc : 0 < c) :
    MemLp (Cvs.L2a.TailLogScaleTest.logScale (fullTail (psi c g))) 2 volume
      ∧ Integrable (Cvs.L2a.TailLogScaleTest.logScale (fullTail (psi c g))) volume := by
  set B := BG c (g 1 + g (-1)) (|g₁ 1 - g₁ (-1)| + ∫ s in (-1 : ℝ)..1, |g₂ s|) with hBd
  have hB : 0 ≤ B := BG_nonneg hc _ (C1_nonneg g₁ g₂)
  set d : ℝ → ℝ := (Ioi (0 : ℝ)).indicator fun s => B * exp (-(1 / 2) * s) with hd
  have hdm : Measurable d := (measurable_const.mul (measurable_exp.comp
    (measurable_const.mul measurable_id))).indicator measurableSet_Ioi
  have hdi : Integrable d := (integrable_indicator_iff measurableSet_Ioi).2
    ((exp_neg_integrableOn_Ioi 0 (by norm_num : (0 : ℝ) < 1 / 2)).const_mul B)
  have hdL : MemLp d 2 volume := by
    rw [memLp_two_iff_integrable_sq hdm.aestronglyMeasurable]
    have e : (fun s => d s ^ 2) = (Ioi (0 : ℝ)).indicator fun s => B ^ 2 * exp (-1 * s) := by
      funext s
      by_cases h : s ∈ Ioi (0 : ℝ)
      · rw [hd, indicator_of_mem h, indicator_of_mem h, mul_pow, sq (exp _), ← exp_add]; ring_nf
      · rw [hd, indicator_of_notMem h, indicator_of_notMem h]; ring
    rw [e]
    exact (integrable_indicator_iff measurableSet_Ioi).2
      ((exp_neg_integrableOn_Ioi 0 (by norm_num : (0 : ℝ) < 1)).const_mul _)
  have hFm := measurable_fullTail hg hg₁ hg₂c hc
  have hfm : AEStronglyMeasurable (Cvs.L2a.TailLogScaleTest.logScale (fullTail (psi c g))) volume := by
    unfold Cvs.L2a.TailLogScaleTest.logScale
    exact ((hFm.comp measurable_exp).mul (measurable_exp.comp (measurable_id.div_const 2))).aestronglyMeasurable
  have hpt : ∀ s, |Cvs.L2a.TailLogScaleTest.logScale (fullTail (psi c g)) s| ≤ d s := by
    intro s
    unfold Cvs.L2a.TailLogScaleTest.logScale
    by_cases h : s ∈ Ioi (0 : ℝ)
    · rw [hd, indicator_of_mem h, abs_mul, abs_of_pos (exp_pos _)]
      have h1 := abs_fullTail_le hg hg₁ hg₂c hc (exp_pos s)
      calc |fullTail (psi c g) (exp s)| * exp (s / 2) ≤ B / exp s * exp (s / 2) :=
            mul_le_mul_of_nonneg_right h1 (exp_pos _).le
        _ = B * exp (-(1 / 2) * s) := by
            rw [div_mul_eq_mul_div, div_eq_iff (exp_pos _).ne', mul_assoc, ← exp_add]; ring_nf
    · have hs : s ≤ 0 := not_lt.mp h
      have h0 : fullTail (psi c g) (exp s) = 0 := by
        rw [fullTail, ite_eq_right (not_lt.mpr (exp_le_one_iff.mpr hs))]
      rw [hd, indicator_of_notMem h, h0, zero_mul, abs_zero]
  refine ⟨hdL.of_le hfm (Eventually.of_forall fun s => ?_), hdi.mono' hfm (Eventually.of_forall fun s => ?_)⟩
  · rw [Real.norm_eq_abs, Real.norm_eq_abs]; exact (hpt s).trans (le_abs_self _)
  · rw [Real.norm_eq_abs]; exact hpt s

/-! ### The Poisson piece -/

/-- The cosine transform of `g` cut to `[−1, 1]` is the interval integral. -/
theorem G_indicator (g : ℝ → ℝ) (η : ℝ) :
    Cvs.Upstream.PoissonSummationDini.G ((Icc (-1 : ℝ) 1).indicator g) η
      = ∫ s in (-1 : ℝ)..1, g s * Real.cos (2 * π * η * s) := by
  unfold Cvs.Upstream.PoissonSummationDini.G
  have e : (fun s => (Icc (-1 : ℝ) 1).indicator g s * Real.cos (2 * π * η * s))
      = (Icc (-1 : ℝ) 1).indicator (fun s => g s * Real.cos (2 * π * η * s)) := by
    funext s; rw [indicator_mul_left]
  rw [e, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num)]

/-- **The closed form of the full tail** off the lattice `(2π/c)ℤ`: for `k < cθ/(2π) < k + 1`,
`F_∞(θ) = (π/(cθ)) Σ_{|n|≤k} g(2πn/(cθ)) − ½∫g` (Poisson summation, Cvs.Upstream.PoissonSummationDini). -/
theorem fullTail_eq_poissonPiece (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hc : 0 < c) {θ : ℝ} (hθ : 1 < θ) {k : ℕ} (hk : (k : ℝ) < c * θ / (2 * π))
    (hk' : c * θ / (2 * π) < k + 1) :
    fullTail (psi c g) θ = poissonPiece c g k θ := by
  have hθ0 : 0 < θ := by linarith
  have hcθ : 0 < c * θ := by positivity
  set θ' := c * θ / (2 * π) with hθ'
  have hθ'0 : 0 < θ' := by have := pi_pos; positivity
  have hI : uIcc (-1 : ℝ) 1 = Icc (-1) 1 := uIcc_of_le (by norm_num)
  have hgc : ContinuousOn g (Icc (-1) 1) := fun s hs =>
    (hg s (by rw [hI]; exact hs)).continuousAt.continuousWithinAt
  have hg₁c : ContinuousOn g₁ (Icc (-1) 1) := fun s hs =>
    (hg₁ s (by rw [hI]; exact hs)).continuousAt.continuousWithinAt
  set gt := (Icc (-1 : ℝ) 1).indicator g with hgt
  have hgti : Integrable gt := (integrable_indicator_iff measurableSet_Icc).2 hgc.integrableOn_Icc
  have hgtm : Measurable gt := by
    classical
    have := hgc.measurable_piecewise (g := 0) continuous_zero.continuousOn measurableSet_Icc
    rwa [piecewise_eq_indicator] at this
  have hsupp : ∀ s, 1 < |s| → gt s = 0 := fun s hs => indicator_of_notMem (fun h => by
    have := abs_le.mpr ⟨h.1, h.2⟩; linarith) _
  have hout : ∀ z, θ' < |z| → gt (z / θ') = 0 := fun z hz =>
    hsupp _ (by rw [abs_div, abs_of_pos hθ'0, one_lt_div hθ'0]; exact hz)
  have hin : ∀ z, |z| ≤ θ' → z / θ' ∈ Icc (-1 : ℝ) 1 := fun z hz => by
    have h := abs_le.mp hz
    refine ⟨?_, ?_⟩
    · rw [le_div_iff₀ hθ'0]; linarith
    · rw [div_le_iff₀ hθ'0]; linarith
  obtain ⟨Mg, hMg⟩ := isCompact_Icc.exists_bound_of_continuousOn hgc
  obtain ⟨Mg1, hMg1⟩ := isCompact_Icc.exists_bound_of_continuousOn hg₁c
  have hMg0 : 0 ≤ Mg := (norm_nonneg _).trans (hMg 0 ⟨by norm_num, by norm_num⟩)
  have hMg10 : 0 ≤ Mg1 := (norm_nonneg _).trans (hMg1 0 ⟨by norm_num, by norm_num⟩)
  have hgtb : ∀ s, |gt s| ≤ Mg := fun s => by
    by_cases h : s ∈ Icc (-1 : ℝ) 1
    · rw [hgt, indicator_of_mem h]; exact hMg s h
    · rw [hgt, indicator_of_notMem h, abs_zero]; exact hMg0
  have hlipg : ∀ u ∈ Icc (-1 : ℝ) 1, ∀ v ∈ Icc (-1 : ℝ) 1, |g u - g v| ≤ Mg1 * |u - v| :=
    fun u hu v hv => (convex_Icc (-1 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le (f := g) (f' := g₁)
      (fun x hx => (hg x (by rw [hI]; exact hx)).hasDerivWithinAt) (fun x hx => hMg1 x hx) hv hu
  have hN : θ' ≤ ((k + 1 : ℕ) : ℝ) := by push_cast; linarith
  have hB : ∀ y, |Cvs.Upstream.PoissonSummationDini.per gt θ' (k + 1) y| ≤ ((2 * (k + 1) + 1 : ℕ) : ℝ) * Mg := by
    intro y
    unfold Cvs.Upstream.PoissonSummationDini.per
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun j _ => hgtb _).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  set δ := min (1 / 2 : ℝ) (min ((θ' - k) / 2) ((k + 1 - θ') / 2)) with hδd
  have hδ : 0 < δ := lt_min (by norm_num) (lt_min (by linarith) (by linarith))
  have hδ2 : δ ≤ 1 / 2 := min_le_left _ _
  have hδa : δ ≤ (θ' - k) / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hδb : δ ≤ (k + 1 - θ') / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hterm : ∀ j ∈ Finset.range (2 * (k + 1) + 1), ∀ y, |y| ≤ δ →
      |gt (((j : ℝ) - ((k + 1 : ℕ) : ℝ) + y) / θ') - gt (((j : ℝ) - ((k + 1 : ℕ) : ℝ) + 0) / θ')|
        ≤ Mg1 / θ' * |y| := by
    intro j hj y hy
    have hj' : j < 2 * (k + 1) + 1 := Finset.mem_range.mp hj
    have hya := abs_le.mp hy
    have hrhs : 0 ≤ Mg1 / θ' * |y| := by positivity
    push_cast
    rcases (show j = 0 ∨ j = 2 * k + 2 ∨ (1 ≤ j ∧ j ≤ 2 * k + 1) by omega) with h | h | h
    · subst h
      rw [hout _ (lt_abs.mpr (Or.inr (by push_cast; linarith))),
        hout _ (lt_abs.mpr (Or.inr (by push_cast; linarith))), sub_zero, abs_zero]
      exact hrhs
    · subst h
      rw [hout _ (lt_abs.mpr (Or.inl (by push_cast; linarith))),
        hout _ (lt_abs.mpr (Or.inl (by push_cast; linarith))), sub_zero, abs_zero]
      exact hrhs
    · have h1 : (1 : ℝ) ≤ j := by exact_mod_cast h.1
      have h2 : (j : ℝ) ≤ 2 * k + 1 := by exact_mod_cast h.2
      have m1 := hin ((j : ℝ) - (k + 1) + y) (abs_le.mpr ⟨by linarith, by linarith⟩)
      have m0 := hin ((j : ℝ) - (k + 1) + 0) (abs_le.mpr ⟨by linarith, by linarith⟩)
      rw [hgt, indicator_of_mem m1, indicator_of_mem m0]
      refine (hlipg _ m1 _ m0).trans (le_of_eq ?_)
      rw [show ((j : ℝ) - (k + 1) + y) / θ' - ((j : ℝ) - (k + 1) + 0) / θ' = y / θ' by ring, abs_div,
        abs_of_pos hθ'0]
      ring
  have hlip : ∀ y, |y| ≤ δ → |Cvs.Upstream.PoissonSummationDini.per gt θ' (k + 1) y - Cvs.Upstream.PoissonSummationDini.per gt θ' (k + 1) 0|
      ≤ ((2 * (k + 1) + 1 : ℕ) : ℝ) * (Mg1 / θ') * |y| := by
    intro y hy
    unfold Cvs.Upstream.PoissonSummationDini.per
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun j hj => hterm j hj y hy).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    exact le_of_eq (by ring)
  have hP := Cvs.Upstream.PoissonSummationDini.poisson hgti hgtm hsupp hθ'0 hN hB hδ hδ2 hlip
  have hG : ∀ m : ℕ, Cvs.Upstream.PoissonSummationDini.G gt (m * θ') = psi c g (m * θ) := by
    intro m
    rw [hgt, G_indicator]
    unfold psi Cvs.Prolate.SlepianCommutingRelation.kint
    refine intervalIntegral.integral_congr fun s _ => ?_
    have hpi : (2 * π) ≠ 0 := by positivity
    have e : 2 * π * ((m : ℝ) * θ') * s = c * ((m : ℝ) * θ) * s := by
      rw [hθ']; field_simp
    exact congrArg (g s * ·) (congrArg Real.cos e)
  have hG0 : Cvs.Upstream.PoissonSummationDini.G gt 0 = ∫ s in (-1 : ℝ)..1, g s := by
    rw [hgt, G_indicator]; simp
  set P := ∑ j ∈ Finset.range (2 * (k + 1) + 1), gt (((j : ℝ) - ((k + 1 : ℕ) : ℝ)) / θ') with hPd
  have hlim : Tendsto (fun M : ℕ => ∑ m ∈ Finset.Icc 1 M, psi c g (m * θ)) atTop
      (𝓝 ((P - θ' * Cvs.Upstream.PoissonSummationDini.G gt 0) / (2 * θ'))) := by
    have := (hP.sub_const (θ' * Cvs.Upstream.PoissonSummationDini.G gt 0)).div_const (2 * θ')
    refine this.congr fun M => ?_
    simp only [hG]
    set S := ∑ m ∈ Finset.Icc 1 M, psi c g (m * θ)
    rw [show θ' * (Cvs.Upstream.PoissonSummationDini.G gt 0 + 2 * S) - θ' * Cvs.Upstream.PoissonSummationDini.G gt 0
      = (2 * θ') * S by ring]
    exact mul_div_cancel_left₀ S (by positivity)
  rw [tendsto_nhds_unique (tendsto_partial hg hg₁ hg₂c hc hθ) hlim]
  have hPeq : P = ∑ n ∈ Finset.Icc (-(k : ℤ)) k, g (2 * π * n / (c * θ)) := by
    rw [hPd, show 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ']
    rw [hout _ (lt_abs.mpr (Or.inr (by push_cast; linarith))),
      hout _ (lt_abs.mpr (Or.inl (by push_cast; linarith))), add_zero, add_zero]
    refine Finset.sum_nbij' (fun j => (j : ℤ) - k) (fun n => (n + k).toNat) ?_ ?_ ?_ ?_ ?_
    · intro j hj; simp only [Finset.mem_range] at hj; simp only [Finset.mem_Icc]; omega
    · intro n hn; simp only [Finset.mem_Icc] at hn; simp only [Finset.mem_range]; omega
    · intro j _; simp
    · intro n hn; simp only [Finset.mem_Icc] at hn; omega
    · intro j hj
      have hj' : (j : ℝ) ≤ 2 * k := by exact_mod_cast (show j ≤ 2 * k by simp at hj; omega)
      have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      have m := hin (((j + 1 : ℕ) : ℝ) - ((k + 1 : ℕ) : ℝ)) (abs_le.mpr ⟨by push_cast; linarith,
        by push_cast; linarith⟩)
      rw [hgt, indicator_of_mem m]
      congr 1
      push_cast
      rw [hθ']
      field_simp
      ring
  rw [hPeq, hG0, poissonPiece, hθ']
  field_simp

/-! ### The `L²` rate of `F_X → F_∞` -/

/-- The square of a measurable function bounded by `K/θ` is integrable on `(1, ∞)`. -/
theorem integrableOn_sq_of_le {f : ℝ → ℝ} {K : ℝ} (hf : Measurable f) (hfK : ∀ θ, 0 < θ → |f θ| ≤ K / θ) :
    IntegrableOn (fun θ => f θ ^ 2) (Ioi 1) := by
  simpa only [sq] using integrableOn_mul_of_le hf hf hfK hfK

/-- `∫_{(1,∞)} f² ≤ K²` for `|f(θ)| ≤ K/θ`. -/
theorem integral_sq_le_of_le {f : ℝ → ℝ} {K : ℝ} (hf : Measurable f) (hfK : ∀ θ, 0 < θ → |f θ| ≤ K / θ) :
    ∫ θ in Ioi 1, f θ ^ 2 ≤ K ^ 2 := by
  calc ∫ θ in Ioi 1, f θ ^ 2 ≤ ∫ θ in Ioi 1, K ^ 2 * (1 / θ ^ 2) :=
        setIntegral_mono_on (integrableOn_sq_of_le hf hfK) ((integrableOn_one_div_sq one_pos).const_mul _)
          measurableSet_Ioi fun θ (hθ : 1 < θ) => by
            have h0 : 0 < θ := one_pos.trans hθ
            calc f θ ^ 2 = |f θ| ^ 2 := (sq_abs _).symm
              _ ≤ (K / θ) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hfK θ h0) 2
              _ = K ^ 2 * (1 / θ ^ 2) := by field_simp
    _ = K ^ 2 := by rw [integral_const_mul, integral_one_div_sq one_pos]; ring

/-- **The pointwise rate on `(1, X]`**: `(F_X − F_∞)² ≤ (2A²/c²) min(G₀²/θ², 1/(X² sin²(cθ/2))) + 8C₁²/(c⁴X²θ²)`,
`G₀ = 2(1 + π)`. -/
theorem sub_sq_le_of_le (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hc : 0 < c) {X θ : ℝ} (hθ : 1 < θ) (hθX : θ ≤ X) :
    (posTail (psi c g) X θ - fullTail (psi c g) θ) ^ 2
      ≤ 2 * (g 1 + g (-1)) ^ 2 / c ^ 2
          * min ((2 * (1 + π)) ^ 2 / θ ^ 2) (1 / (X ^ 2 * Real.sin (c * θ / 2) ^ 2))
        + 8 * (|g₁ 1 - g₁ (-1)| + ∫ s in (-1 : ℝ)..1, |g₂ s|) ^ 2 / (c ^ 4 * X ^ 2) * (1 / θ ^ 2) := by
  have hθ0 : 0 < θ := by linarith
  have hX0 : 0 < X := by linarith
  have hcθ : 0 < c * θ := by positivity
  have hC1 := C1_nonneg g₁ g₂
  set A := g 1 + g (-1) with hA
  set C1 := |g₁ 1 - g₁ (-1)| + ∫ s in (-1 : ℝ)..1, |g₂ s| with hC1d
  set M := ⌊X / θ⌋₊ with hMd
  have hM1 : 1 ≤ M := Nat.le_floor (by rw [Nat.cast_one, le_div_iff₀ hθ0]; linarith)
  have hM1r : (1 : ℝ) ≤ M := by exact_mod_cast hM1
  have hM1X : X / θ ≤ M + 1 := (Nat.lt_floor_add_one _).le
  have hMX : X / θ ≤ 2 * M := by linarith
  rw [posTail_eq_partial _ hθ hθX]
  have hlim := ((tendsto_const_nhds (x := ∑ m ∈ Finset.Icc 1 M, psi c g (m * θ))).sub
    (tendsto_partial hg hg₁ hg₂c hc hθ)).pow 2
  refine le_of_tendsto hlim ?_
  filter_upwards [eventually_ge_atTop M] with N hN
  have hIcc : ∀ n, Finset.Icc 1 n = Finset.Ioc 0 n := fun n => by
    ext m; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  have hsplit : ∑ m ∈ Finset.Icc 1 N, psi c g (m * θ) - ∑ m ∈ Finset.Icc 1 M, psi c g (m * θ)
      = ∑ m ∈ Finset.Ioc M N, psi c g (m * θ) := by
    rw [hIcc, hIcc, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le M) hN]; ring
  rw [show (∑ m ∈ Finset.Icc 1 M, psi c g (m * θ) - ∑ m ∈ Finset.Icc 1 N, psi c g (m * θ)) ^ 2
      = (∑ m ∈ Finset.Icc 1 N, psi c g (m * θ) - ∑ m ∈ Finset.Icc 1 M, psi c g (m * θ)) ^ 2 by ring,
    hsplit]
  set τ := ∑ m ∈ Finset.Ioc M N, Real.sin (m * (c * θ)) / m with hτd
  set Sd := ∑ m ∈ Finset.Ioc M N, psi c g (m * θ) with hSd
  have hrem := abs_sum_sub_le hg hg₁ hg₂c hc hθ0 (Finset.Ioc M N)
    (fun m hm => by simp only [Finset.mem_Ioc] at hm; omega)
  have hZ := sum_Ioc_one_div_sq_le hM1 N
  have hb : C1 / (c * θ) ^ 2 * ∑ m ∈ Finset.Ioc M N, 1 / (m : ℝ) ^ 2 ≤ 2 * C1 / (c ^ 2 * θ * X) := by
    have h1 : 1 / (M : ℝ) ≤ 2 * θ / X := by
      rw [div_le_div_iff₀ (by positivity) hX0]
      rw [div_le_iff₀ hθ0] at hMX
      linarith
    calc C1 / (c * θ) ^ 2 * ∑ m ∈ Finset.Ioc M N, 1 / (m : ℝ) ^ 2 ≤ C1 / (c * θ) ^ 2 * (1 / M) :=
          mul_le_mul_of_nonneg_left hZ (by positivity)
      _ ≤ C1 / (c * θ) ^ 2 * (2 * θ / X) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 2 * C1 / (c ^ 2 * θ * X) := by field_simp
  have hτG : |τ| ≤ 2 * (1 + π) := Cvs.Upstream.SawtoothPartialSums.abs_sum_sin_div_Ioc_le M N (c * θ)
  have hτs : τ ^ 2 / θ ^ 2 ≤ 1 / (X ^ 2 * Real.sin (c * θ / 2) ^ 2) := by
    by_cases hs : Real.sin (c * θ / 2) = 0
    · have h0 : τ = 0 := Finset.sum_eq_zero fun m _ => by
        rw [Cvs.Upstream.SawtoothPartialSums.sin_mul_eq_zero_of_sin_half hs m, zero_div]
      rw [h0, hs]; simp
    · have hsp : 0 < |Real.sin (c * θ / 2)| := abs_pos.mpr hs
      have h1 := Cvs.Upstream.SawtoothPartialSums.abs_sum_sin_div_Ioc_mul_le M N (c * θ)
      have h2 : |τ| * (X / θ * |Real.sin (c * θ / 2)|) ≤ 1 :=
        le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hM1X hsp.le) (abs_nonneg _)) h1
      have h3 : |τ| * X * |Real.sin (c * θ / 2)| ≤ θ := by
        have e : |τ| * (X / θ * |Real.sin (c * θ / 2)|) = (|τ| * X * |Real.sin (c * θ / 2)|) / θ := by
          field_simp
        rw [e, div_le_one hθ0] at h2
        exact h2
      have h0 : 0 ≤ |τ| * X * |Real.sin (c * θ / 2)| :=
        mul_nonneg (mul_nonneg (abs_nonneg _) hX0.le) (abs_nonneg _)
      have h4 : (|τ| * X * |Real.sin (c * θ / 2)|) ^ 2 ≤ θ ^ 2 := pow_le_pow_left₀ h0 h3 2
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      calc τ ^ 2 * (X ^ 2 * Real.sin (c * θ / 2) ^ 2) = (|τ| * X * |Real.sin (c * θ / 2)|) ^ 2 := by
            rw [mul_pow, mul_pow, sq_abs, sq_abs]; ring
        _ ≤ θ ^ 2 := h4
        _ = 1 * θ ^ 2 := (one_mul _).symm
  have hτmin : τ ^ 2 / θ ^ 2 ≤ min ((2 * (1 + π)) ^ 2 / θ ^ 2) (1 / (X ^ 2 * Real.sin (c * θ / 2) ^ 2)) := by
    refine le_min (div_le_div_of_nonneg_right ?_ (by positivity)) hτs
    rw [← sq_abs τ]
    exact pow_le_pow_left₀ (abs_nonneg _) hτG 2
  have hSb : |Sd| ≤ |A| / (c * θ) * |τ| + 2 * C1 / (c ^ 2 * θ * X) := by
    have h1 := abs_sub_abs_le_abs_sub Sd (A / (c * θ) * τ)
    rw [abs_mul (A / (c * θ)) τ, abs_div, abs_of_pos hcθ] at h1
    linarith
  have hq : 0 ≤ |A| / (c * θ) * |τ| := by positivity
  calc Sd ^ 2 = |Sd| ^ 2 := (sq_abs _).symm
    _ ≤ (|A| / (c * θ) * |τ| + 2 * C1 / (c ^ 2 * θ * X)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hSb 2
    _ ≤ 2 * (|A| / (c * θ) * |τ|) ^ 2 + 2 * (2 * C1 / (c ^ 2 * θ * X)) ^ 2 := by
        nlinarith [sq_nonneg (|A| / (c * θ) * |τ| - 2 * C1 / (c ^ 2 * θ * X))]
    _ = 2 * A ^ 2 / c ^ 2 * (τ ^ 2 / θ ^ 2) + 8 * C1 ^ 2 / (c ^ 4 * X ^ 2) * (1 / θ ^ 2) := by
        rw [mul_pow, div_pow, sq_abs, sq_abs]; field_simp; ring
    _ ≤ _ := by gcongr

/-- `|F_X − F_∞| ≤ 2B_G/θ`. -/
theorem abs_posTail_sub_le (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hc : 0 < c) (X : ℝ) {θ : ℝ} (hθ : 0 < θ) :
    |posTail (psi c g) X θ - fullTail (psi c g) θ|
      ≤ 2 * BG c (g 1 + g (-1)) (|g₁ 1 - g₁ (-1)| + ∫ s in (-1 : ℝ)..1, |g₂ s|) / θ := by
  have h1 := abs_posTail_le hg hg₁ hg₂c hc X hθ
  have h2 := abs_fullTail_le hg hg₁ hg₂c hc hθ
  have := abs_sub (posTail (psi c g) X θ) (fullTail (psi c g) θ)
  rw [mul_div_assoc]; linarith

/-- The position-truncated tail of `ψ` is measurable. -/
theorem measurable_posTail_psi (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (c X : ℝ) :
    Measurable (posTail (psi c g) X) :=
  measurable_posTail (contDiff_psi (fun s hs => (hg s hs).continuousAt.continuousWithinAt) c).continuous X

/-- **The `L²` rate** (Theorem L (1)): `∫_{(1,∞)} (F_X − F_∞)² ≤ K1(X)` for `X ≥ 1`. -/
theorem integral_sub_sq_le (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hc : 0 < c) {X : ℝ} (hX : 1 ≤ X) :
    ∫ θ in Ioi 1, (posTail (psi c g) X θ - fullTail (psi c g) θ) ^ 2
      ≤ K1 c (g 1 + g (-1)) (|g₁ 1 - g₁ (-1)| + ∫ s in (-1 : ℝ)..1, |g₂ s|) X := by
  have hX0 : 0 < X := by linarith
  have hC1 := C1_nonneg g₁ g₂
  set A := g 1 + g (-1) with hA
  set C1 := |g₁ 1 - g₁ (-1)| + ∫ s in (-1 : ℝ)..1, |g₂ s| with hC1d
  set B := BG c A C1 with hBd
  have hB : 0 ≤ B := BG_nonneg hc A hC1
  have hDi : IntegrableOn (fun θ => (posTail (psi c g) X θ - fullTail (psi c g) θ) ^ 2) (Ioi 1) :=
    integrableOn_sq_of_le ((measurable_posTail_psi hg c X).sub (measurable_fullTail hg hg₁ hg₂c hc))
      fun θ hθ => abs_posTail_sub_le hg hg₁ hg₂c hc X hθ
  rw [← Ioc_union_Ioi_eq_Ioi hX, setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
    (hDi.mono_set Ioc_subset_Ioi_self) (hDi.mono_set (Ioi_subset_Ioi hX))]
  set G0 : ℝ := 2 * (1 + π) with hG0
  have hG00 : 0 ≤ G0 := by have := pi_pos; positivity
  set m : ℝ → ℝ := fun θ => min (G0 ^ 2 / θ ^ 2) (1 / (X ^ 2 * Real.sin (c * θ / 2) ^ 2)) with hmd
  have hmm : Measurable m := by
    have h1 : Measurable fun θ : ℝ => G0 ^ 2 / θ ^ 2 := by fun_prop
    have h2 : Measurable fun θ : ℝ => 1 / (X ^ 2 * Real.sin (c * θ / 2) ^ 2) := by fun_prop
    exact h1.min h2
  have hq : IntegrableOn (fun θ : ℝ => 1 / θ ^ 2) (Ioi 1) := integrableOn_one_div_sq one_pos
  have hmi : IntegrableOn m (Ioi 1) :=
    Integrable.mono' (hq.const_mul (G0 ^ 2)) hmm.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun θ (hθ : 1 < θ) => by
        have h0 : 0 < θ := one_pos.trans hθ
        have hm0 : 0 ≤ m θ := by simp only [hmd]; positivity
        rw [Real.norm_eq_abs, abs_of_nonneg hm0]
        exact (min_le_left _ _).trans (le_of_eq (by ring))))
  have hQi : IntegrableOn (fun θ => 2 * A ^ 2 / c ^ 2 * m θ + 8 * C1 ^ 2 / (c ^ 4 * X ^ 2) * (1 / θ ^ 2))
      (Ioc 1 X) := IntegrableOn.mono_set ((hmi.const_mul _).add (hq.const_mul _)) Ioc_subset_Ioi_self
  have hnear : ∫ θ in Ioc 1 X, (posTail (psi c g) X θ - fullTail (psi c g) θ) ^ 2
      ≤ ∫ θ in Ioc 1 X, (2 * A ^ 2 / c ^ 2 * m θ + 8 * C1 ^ 2 / (c ^ 4 * X ^ 2) * (1 / θ ^ 2)) :=
    setIntegral_mono_on (hDi.mono_set Ioc_subset_Ioi_self) hQi measurableSet_Ioc
      fun θ hθ => sub_sq_le_of_le hg hg₁ hg₂c hc hθ.1 hθ.2
  rw [integral_add (IntegrableOn.mono_set (hmi.const_mul _) Ioc_subset_Ioi_self)
    (IntegrableOn.mono_set (hq.const_mul _) Ioc_subset_Ioi_self), integral_const_mul,
    integral_const_mul] at hnear
  have hm_le : ∫ θ in Ioc 1 X, m θ ≤ 4 * G0 * (Real.logb 2 X + 1 + 8 * π / c) / X := by
    rw [← intervalIntegral.integral_of_le hX]
    exact Cvs.Upstream.SawtoothPartialSums.integral_dyadic_le hc hG00 hX
  have hq_le : ∫ θ in Ioc 1 X, 1 / θ ^ 2 ≤ 1 := by
    calc ∫ θ in Ioc 1 X, 1 / θ ^ 2 ≤ ∫ θ in Ioi 1, 1 / θ ^ 2 :=
          setIntegral_mono_set hq ((ae_restrict_iff' measurableSet_Ioi).2
            (Eventually.of_forall fun θ _ => by positivity)) (Eventually.of_forall fun x (hx : x ∈ Ioc 1 X) => (Ioc_subset_Ioi_self hx : x ∈ Ioi 1))
      _ = 1 := by rw [integral_one_div_sq one_pos]; norm_num
  have hfar : ∫ θ in Ioi X, (posTail (psi c g) X θ - fullTail (psi c g) θ) ^ 2 ≤ B ^ 2 / X := by
    calc ∫ θ in Ioi X, (posTail (psi c g) X θ - fullTail (psi c g) θ) ^ 2
          ≤ ∫ θ in Ioi X, B ^ 2 * (1 / θ ^ 2) :=
          setIntegral_mono_on (hDi.mono_set (Ioi_subset_Ioi hX))
            ((integrableOn_one_div_sq hX0).const_mul _) measurableSet_Ioi fun θ (hθ : X < θ) => by
              have h0 : 0 < θ := hX0.trans hθ
              rw [posTail_of_gt _ hθ, zero_sub, neg_sq, ← sq_abs]
              calc |fullTail (psi c g) θ| ^ 2 ≤ (B / θ) ^ 2 :=
                    pow_le_pow_left₀ (abs_nonneg _) (abs_fullTail_le hg hg₁ hg₂c hc h0) 2
                _ = B ^ 2 * (1 / θ ^ 2) := by field_simp
      _ = B ^ 2 / X := by rw [integral_const_mul, integral_one_div_sq hX0]; ring
  have hA2 : 0 ≤ 2 * A ^ 2 / c ^ 2 := by positivity
  have hC2 : 0 ≤ 8 * C1 ^ 2 / (c ^ 4 * X ^ 2) := by positivity
  have hsum := add_le_add (hnear.trans (add_le_add (mul_le_mul_of_nonneg_left hm_le hA2)
    (mul_le_mul_of_nonneg_left hq_le hC2))) hfar
  refine hsum.trans (le_of_eq ?_)
  unfold K1
  rw [hG0]
  ring

/-- **`K1(X) ≤ K1b/√X`** for `X ≥ 1`: `log₂X + 1 ≤ 3√X` since `log y ≤ y − 1` and `log 2 > 2/3`. -/
theorem K1_le (hc : 0 < c) (A C1 : ℝ) {X : ℝ} (hX : 1 ≤ X) : K1 c A C1 X ≤ K1b c A C1 / √X := by
  have hX0 : 0 < X := by linarith
  have hs : 0 < √X := Real.sqrt_pos.mpr hX0
  have hs1 : 1 ≤ √X := Real.one_le_sqrt.mpr hX
  have hsX : √X * √X = X := Real.mul_self_sqrt hX0.le
  have hsle : √X ≤ X := by nlinarith
  have hL : Real.logb 2 X + 1 ≤ 3 * √X := by
    have h1 : Real.log X = 2 * Real.log √X := by rw [Real.log_sqrt hX0.le]; ring
    have h2 := Real.log_le_sub_one_of_pos hs
    have h3 := Real.log_two_gt_d9
    have hl0 : 0 ≤ Real.log X := Real.log_nonneg hX
    have h4 : Real.log X / Real.log 2 ≤ 3 / 2 * Real.log X := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    show Real.log X / Real.log 2 + 1 ≤ 3 * √X
    linarith
  have hπc : 0 ≤ 8 * π / c := by have := pi_pos; positivity
  have hL0 : 0 ≤ Real.logb 2 X := Real.logb_nonneg (by norm_num) hX
  unfold K1 K1b
  rw [add_div, add_div]
  set B := BG c A C1
  have t1 : 16 * (1 + π) * A ^ 2 * (Real.logb 2 X + 1 + 8 * π / c) / (c ^ 2 * X)
      ≤ 16 * (1 + π) * A ^ 2 * (3 + 8 * π / c) / c ^ 2 / √X := by
    have hP : 0 ≤ 16 * (1 + π) * A ^ 2 / c ^ 2 := by have := pi_pos; positivity
    have h : (Real.logb 2 X + 1 + 8 * π / c) / X ≤ (3 + 8 * π / c) / √X := by
      rw [div_le_div_iff₀ hX0 hs]
      nlinarith [mul_le_mul_of_nonneg_right hL hs.le,
        mul_le_mul_of_nonneg_left (show √X ≤ √X * √X by nlinarith) hπc]
    calc 16 * (1 + π) * A ^ 2 * (Real.logb 2 X + 1 + 8 * π / c) / (c ^ 2 * X)
        = 16 * (1 + π) * A ^ 2 / c ^ 2 * ((Real.logb 2 X + 1 + 8 * π / c) / X) := by ring
      _ ≤ 16 * (1 + π) * A ^ 2 / c ^ 2 * ((3 + 8 * π / c) / √X) := mul_le_mul_of_nonneg_left h hP
      _ = _ := by ring
  have t2 : 8 * C1 ^ 2 / (c ^ 4 * X ^ 2) ≤ 8 * C1 ^ 2 / c ^ 4 / √X := by
    rw [← div_div]
    exact div_le_div_of_nonneg_left (by positivity) hs (by nlinarith)
  have t3 : B ^ 2 / X ≤ B ^ 2 / √X := div_le_div_of_nonneg_left (by positivity) hs hsle
  linarith

/-! ### Energies and Gram entries in the limit -/

/-- **The energy rate** (Theorem L (2)): `|N_X − N_∞| ≤ 2√(N_∞ K1) + K1`, by Cauchy–Schwarz on `(1, ∞)`. -/
theorem abs_N_sub_le (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hc : 0 < c) {X : ℝ} (hX : 1 ≤ X) :
    |(∫ θ in Ioi 1, posTail (psi c g) X θ ^ 2) - ∫ θ in Ioi 1, fullTail (psi c g) θ ^ 2|
      ≤ 2 * √((∫ θ in Ioi 1, fullTail (psi c g) θ ^ 2)
          * K1 c (g 1 + g (-1)) (|g₁ 1 - g₁ (-1)| + ∫ s in (-1 : ℝ)..1, |g₂ s|) X)
        + K1 c (g 1 + g (-1)) (|g₁ 1 - g₁ (-1)| + ∫ s in (-1 : ℝ)..1, |g₂ s|) X := by
  set a := posTail (psi c g) X with had
  set b := fullTail (psi c g) with hbd
  have ham := measurable_posTail_psi hg c X
  have hbm := measurable_fullTail hg hg₁ hg₂c hc
  have hab : ∀ θ, 0 < θ → |a θ| ≤ _ / θ := fun θ hθ => abs_posTail_le hg hg₁ hg₂c hc X hθ
  have hbb : ∀ θ, 0 < θ → |b θ| ≤ _ / θ := fun θ hθ => abs_fullTail_le hg hg₁ hg₂c hc hθ
  have hdb : ∀ θ, 0 < θ → |a θ - b θ| ≤ _ / θ := fun θ hθ => abs_posTail_sub_le hg hg₁ hg₂c hc X hθ
  have ha2 : IntegrableOn (fun θ => a θ ^ 2) (Ioi 1) := integrableOn_sq_of_le ham hab
  have hb2 : IntegrableOn (fun θ => b θ ^ 2) (Ioi 1) := integrableOn_sq_of_le hbm hbb
  have hd2 : IntegrableOn (fun θ => (a θ - b θ) ^ 2) (Ioi 1) :=
    integrableOn_sq_of_le (f := fun θ => a θ - b θ) (ham.sub hbm) hdb
  have hdbi : IntegrableOn (fun θ => (a θ - b θ) * b θ) (Ioi 1) :=
    integrableOn_mul_of_le (f := fun θ => a θ - b θ) (ham.sub hbm) hbm hdb hbb
  have hsplit : (∫ θ in Ioi 1, a θ ^ 2) - ∫ θ in Ioi 1, b θ ^ 2
      = (∫ θ in Ioi 1, (a θ - b θ) ^ 2) + 2 * ∫ θ in Ioi 1, (a θ - b θ) * b θ := by
    have e : (∫ θ in Ioi 1, (a θ - b θ) ^ 2) + 2 * ∫ θ in Ioi 1, (a θ - b θ) * b θ
        = ∫ θ in Ioi 1, ((a θ - b θ) ^ 2 + 2 * ((a θ - b θ) * b θ)) := by
      rw [integral_add hd2 (hdbi.const_mul 2), integral_const_mul]
    rw [e, ← integral_sub ha2 hb2]
    congr 1; funext θ; ring
  have hcs := abs_setIntegral_mul_le (f := fun θ => a θ - b θ) (w := b) hd2 hb2 hdbi
  have hK := integral_sub_sq_le hg hg₁ hg₂c hc hX
  have hD0 : 0 ≤ ∫ θ in Ioi 1, (a θ - b θ) ^ 2 :=
    setIntegral_nonneg_of_ae (Eventually.of_forall fun θ => sq_nonneg _)
  have hN0 : 0 ≤ ∫ θ in Ioi 1, b θ ^ 2 := setIntegral_nonneg_of_ae (Eventually.of_forall fun θ => sq_nonneg _)
  set K := K1 c (g 1 + g (-1)) (|g₁ 1 - g₁ (-1)| + ∫ s in (-1 : ℝ)..1, |g₂ s|) X
  have hsq : √(∫ θ in Ioi 1, (a θ - b θ) ^ 2) * √(∫ θ in Ioi 1, b θ ^ 2) ≤ √((∫ θ in Ioi 1, b θ ^ 2) * K) := by
    rw [Real.sqrt_mul hN0, mul_comm]
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hK) (Real.sqrt_nonneg _)
  rw [hsplit]
  calc |(∫ θ in Ioi 1, (a θ - b θ) ^ 2) + 2 * ∫ θ in Ioi 1, (a θ - b θ) * b θ|
      ≤ |∫ θ in Ioi 1, (a θ - b θ) ^ 2| + |2 * ∫ θ in Ioi 1, (a θ - b θ) * b θ| := abs_add_le _ _
    _ = (∫ θ in Ioi 1, (a θ - b θ) ^ 2) + 2 * |∫ θ in Ioi 1, (a θ - b θ) * b θ| := by
        rw [abs_of_nonneg hD0, abs_mul, abs_two]
    _ ≤ 2 * √((∫ θ in Ioi 1, b θ ^ 2) * K) + K := by linarith

/-- `√(K/√X) → 0` as `X → ∞`. -/
theorem tendsto_sqrt_div_sqrt (K : ℝ) : Tendsto (fun X : ℝ => √(K / √X)) atTop (𝓝 0) := by
  have h := (Real.continuous_sqrt.tendsto 0).comp
    ((tendsto_const_nhds (x := K)).div_atTop tendsto_sqrt_atTop)
  rw [Real.sqrt_zero] at h
  exact h

/-- **The energies converge**: `N_X = ∫_{(1,∞)} F_X² → N_∞ = ∫_{(1,∞)} F_∞²`. -/
theorem tendsto_N (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hc : 0 < c) :
    Tendsto (fun X : ℝ => ∫ θ in Ioi 1, posTail (psi c g) X θ ^ 2) atTop
      (𝓝 (∫ θ in Ioi 1, fullTail (psi c g) θ ^ 2)) := by
  set N := ∫ θ in Ioi 1, fullTail (psi c g) θ ^ 2 with hNd
  have hN0 : 0 ≤ N := setIntegral_nonneg_of_ae (Eventually.of_forall fun θ => sq_nonneg _)
  set Kb := K1b c (g 1 + g (-1)) (|g₁ 1 - g₁ (-1)| + ∫ s in (-1 : ℝ)..1, |g₂ s|)
  have hKb : Tendsto (fun X : ℝ => Kb / √X) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_sqrt_atTop
  have hu : Tendsto (fun X : ℝ => 2 * √(N * (Kb / √X)) + Kb / √X) atTop (𝓝 0) := by
    have h1 : Tendsto (fun X : ℝ => √(N * (Kb / √X))) atTop (𝓝 0) := by
      have := (Real.continuous_sqrt.tendsto (N * 0)).comp (hKb.const_mul N)
      rw [mul_zero, Real.sqrt_zero] at this
      exact this
    have := (h1.const_mul 2).add hKb
    rw [mul_zero, add_zero] at this
    exact this
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun X => norm_nonneg _) ?_ hu
  filter_upwards [eventually_ge_atTop 1] with X hX
  rw [Real.norm_eq_abs]
  refine (abs_N_sub_le hg hg₁ hg₂c hc hX).trans ?_
  have hk := K1_le hc (g 1 + g (-1)) (|g₁ 1 - g₁ (-1)| + ∫ s in (-1 : ℝ)..1, |g₂ s|) hX
  exact add_le_add (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hk hN0))
    two_pos.le) hk

end Cvs.L2a.FullTailConvergence
