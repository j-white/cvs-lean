import Mathlib
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.Approximant.SpineSubspace
import Cvs.L2a.ProlateFamilySpine
import Cvs.Prolate.EvenRungParseval
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.EvenRungsComplete
import Cvs.Prolate.ScalingLaplacianCauchyLaw
import Cvs.Prolate.SincTopIsRung
import Cvs.WeilForm.WeilFormOnWindowL2

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The Cauchy endpoint leak of the scaling Laplacian on a span of rungs

For `c > 0` and `G = Σ_{i ∈ I} a_i rung c (n i)` the rung coefficients of `−(θ + ½)²G` off `n(I)` are the Cauchy leak
`2μ_k[q_k P_a(μ_k) − p_k Q_a(μ_k)]`, `P_a(z) = Σ_i a_i p_{n(i)}/(z − μ_{n(i)})`, `Q_a` likewise, and they expand
`−(θ + ½)²G` in `L²(0, 1]` (Cvs.Prolate.EvenRungParseval); on the spine profiles of Cvs.Approximant.DeepIndexSpineSpan, `∫_{−1}^{1} −(θ + ½)²G = −2G′(1)`.
-/

noncomputable section

open Real Set MeasureTheory

namespace Cvs.Prolate.ScalingLaplacianEndpointLeak
open Cvs.ZeroCounting

open Cvs.WeilForm.WeilFormOnWindowL2 (window)
open Cvs.Prolate.EvenRungsByIndex (rung rung₁ rung₂ lev muR IsLevelIdx rung_spec continuousOn_rung)
open Cvs.Approximant.DeepIndexSpineSpan (spineG alpha)
open Cvs.L2a.ProlateFamilySpine (kOf bOf)
open Cvs.Prolate.EvenRungParseval (LevelIdx evCls rungBasis)
open Cvs.Prolate.ScalingLaplacianCauchyLaw (hamC scalingLap integral_scalingLap_rung cauchy_scalingLap_rung muR_ne rung₁_neg rung₂_neg rungSpace_level)

/-! ### The Cauchy transform -/

/-- The Cauchy transform `Σ_{j ∈ I} w_j/(z − μ_j)`. -/
def cauchyT {κ : Type*} (I : Finset κ) (μ w : κ → ℝ) (z : ℝ) : ℝ := ∑ j ∈ I, w j / (z - μ j)

/-- **The leak identity**: if `(μ₀ − μ_j)w_j = 2μ₀(p_j q₀ − q_j p₀)` and `μ₀ ≠ μ_j` for `j ∈ I`, then
`Σ_{j ∈ I} w_j a_j = 2μ₀[q₀ P_a(μ₀) − p₀ Q_a(μ₀)]`. -/
theorem sum_mul_eq_leak {κ : Type*} {I : Finset κ} {μ p q a w : κ → ℝ} {μ₀ p₀ q₀ : ℝ}
    (hW : ∀ j ∈ I, (μ₀ - μ j) * w j = 2 * μ₀ * (p j * q₀ - q j * p₀)) (hne : ∀ j ∈ I, μ₀ ≠ μ j) :
    ∑ j ∈ I, w j * a j
      = 2 * μ₀ * (q₀ * cauchyT I μ (fun j => a j * p j) μ₀ - p₀ * cauchyT I μ (fun j => a j * q j) μ₀) := by
  unfold cauchyT
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hd : μ₀ - μ j ≠ 0 := sub_ne_zero.mpr (hne j hj)
  have hw : w j = 2 * μ₀ * (p j * q₀ - q j * p₀) / (μ₀ - μ j) := by
    rw [eq_div_iff hd, mul_comm]; exact hW j hj
  rw [hw]
  ring

/-- The Taylor generator `Σ_{j ∈ I} w_j(μ_j − μ̄)^m`. -/
def taylorGen {κ : Type*} (I : Finset κ) (μ w : κ → ℝ) (μbar : ℝ) (m : ℕ) : ℝ := ∑ j ∈ I, w j * (μ j - μbar) ^ m

/-- The exact Taylor remainder `Σ_{j ∈ I} w_j(μ_j − μ̄)^{M+1}/((z − μ̄)^{M+1}(z − μ_j))`. -/
def taylorRem {κ : Type*} (I : Finset κ) (μ w : κ → ℝ) (μbar : ℝ) (M : ℕ) (z : ℝ) : ℝ :=
  ∑ j ∈ I, w j * (μ j - μbar) ^ (M + 1) / ((z - μbar) ^ (M + 1) * (z - μ j))

/-- **The geometric expansion**:
`1/(z − μ) = Σ_{m ≤ M} (μ − μ̄)^m/(z − μ̄)^{m+1} + (μ − μ̄)^{M+1}/((z − μ̄)^{M+1}(z − μ))`. -/
theorem one_div_sub_taylor {z μ μbar : ℝ} (h1 : z ≠ μbar) (h2 : z ≠ μ) (M : ℕ) :
    1 / (z - μ) = ∑ m ∈ Finset.range (M + 1), (μ - μbar) ^ m / (z - μbar) ^ (m + 1)
      + (μ - μbar) ^ (M + 1) / ((z - μbar) ^ (M + 1) * (z - μ)) := by
  have hu : z - μbar ≠ 0 := sub_ne_zero.2 h1
  have hd : z - μ ≠ 0 := sub_ne_zero.2 h2
  induction M with
  | zero =>
    simp only [zero_add, Finset.range_one, Finset.sum_singleton, pow_zero, pow_one]
    field_simp
    ring
  | succ M ih =>
    rw [Finset.sum_range_succ, add_assoc]
    have key : (μ - μbar) ^ (M + 1) / (z - μbar) ^ (M + 1 + 1)
        + (μ - μbar) ^ (M + 1 + 1) / ((z - μbar) ^ (M + 1 + 1) * (z - μ))
        = (μ - μbar) ^ (M + 1) / ((z - μbar) ^ (M + 1) * (z - μ)) := by
      field_simp
      ring
    rw [key]
    exact ih

/-- **The Cauchy transform to finite order**: for `z ≠ μ̄` and `z ≠ μ_j` on `I`,
`Σ_{j ∈ I} w_j/(z − μ_j) = Σ_{m ≤ M} b^{(m)}/(z − μ̄)^{m+1} + R_M(z)` with `b^{(m)} = Σ_j w_j(μ_j − μ̄)^m`. -/
theorem cauchyT_taylor {κ : Type*} (I : Finset κ) (μ w : κ → ℝ) {μbar z : ℝ} (h1 : z ≠ μbar)
    (h2 : ∀ j ∈ I, z ≠ μ j) (M : ℕ) :
    cauchyT I μ w z = ∑ m ∈ Finset.range (M + 1), taylorGen I μ w μbar m / (z - μbar) ^ (m + 1)
      + taylorRem I μ w μbar M z := by
  have e : ∀ j ∈ I, w j / (z - μ j)
      = ∑ m ∈ Finset.range (M + 1), w j * (μ j - μbar) ^ m / (z - μbar) ^ (m + 1)
        + w j * (μ j - μbar) ^ (M + 1) / ((z - μbar) ^ (M + 1) * (z - μ j)) := by
    intro j hj
    rw [div_eq_mul_one_div, one_div_sub_taylor h1 (h2 j hj) M, mul_add, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun m _ => by ring
    · ring
  unfold cauchyT taylorGen taylorRem
  rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, Finset.sum_comm]
  congr 1
  exact Finset.sum_congr rfl fun m _ => by rw [Finset.sum_div]

/-! ### Spans of rungs -/

section rung

variable {κ : Type*} {c : ℝ} {I : Finset κ} {n : κ → ℕ} {a : κ → ℝ}

/-- `G = Σ_{i ∈ I} a_i h_{n(i)}`. -/
def comb (c : ℝ) (I : Finset κ) (n : κ → ℕ) (a : κ → ℝ) (v : ℝ) : ℝ := ∑ i ∈ I, a i * rung c (n i) v

/-- `G′ = Σ_{i ∈ I} a_i h_{n(i)}′`. -/
def comb₁ (c : ℝ) (I : Finset κ) (n : κ → ℕ) (a : κ → ℝ) (v : ℝ) : ℝ := ∑ i ∈ I, a i * rung₁ c (n i) v

/-- `G″ = Σ_{i ∈ I} a_i h_{n(i)}″`. -/
def comb₂ (c : ℝ) (I : Finset κ) (n : κ → ℕ) (a : κ → ℝ) (v : ℝ) : ℝ := ∑ i ∈ I, a i * rung₂ c (n i) v

/-- `−(θ + ½)²` is linear on spans of rungs. -/
theorem scalingLap_comb (v : ℝ) :
    scalingLap (comb c I n a) (comb₁ c I n a) (comb₂ c I n a) v
      = ∑ i ∈ I, a i * scalingLap (rung c (n i)) (rung₁ c (n i)) (rung₂ c (n i)) v := by
  simp only [scalingLap, comb, comb₁, comb₂, Finset.mul_sum, Finset.sum_div, ← Finset.sum_add_distrib,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- `−(θ + ½)²h_j` is continuous on `[−1, 1]`. -/
theorem continuousOn_scalingLap_rung {j : ℕ} (hj : ∃ χ, IsLevelIdx c j χ) :
    ContinuousOn (scalingLap (rung c j) (rung₁ c j) (rung₂ c j)) (uIcc (-1) 1) := by
  obtain ⟨hg, hg₁, hg₂c, -, -, -⟩ := rung_spec hj
  have hgc : ContinuousOn (rung c j) (uIcc (-1) 1) := fun s hs => (hg s hs).continuousAt.continuousWithinAt
  have hg₁c : ContinuousOn (rung₁ c j) (uIcc (-1) 1) := fun s hs => (hg₁ s hs).continuousAt.continuousWithinAt
  unfold scalingLap
  exact (((continuousOn_id.pow 2).mul hg₂c).add ((continuousOn_const.mul continuousOn_id).mul hg₁c)
    |>.add (hgc.div_const 4)).neg

/-- `−(θ + ½)²h_j` is even on `[−1, 1]`. -/
theorem scalingLap_rung_neg {j : ℕ} (hj : ∃ χ, IsLevelIdx c j χ) :
    ∀ v ∈ Icc (-1 : ℝ) 1, scalingLap (rung c j) (rung₁ c j) (rung₂ c j) (-v)
      = scalingLap (rung c j) (rung₁ c j) (rung₂ c j) v := by
  intro v hv
  obtain ⟨-, -, -, -, heven, -⟩ := rung_spec hj
  simp only [scalingLap]
  rw [rung₂_neg hj v hv, rung₁_neg hj v hv, heven v hv]
  ring

/-- `−(θ + ½)²G` is continuous on `[−1, 1]`. -/
theorem continuousOn_scalingLap_comb (hI : ∀ i ∈ I, ∃ χ, IsLevelIdx c (n i) χ) :
    ContinuousOn (scalingLap (comb c I n a) (comb₁ c I n a) (comb₂ c I n a)) (Icc (-1) 1) := by
  have hI' : uIcc (-1 : ℝ) 1 = Icc (-1) 1 := uIcc_of_le (by norm_num)
  have : ContinuousOn (fun v => ∑ i ∈ I, a i * scalingLap (rung c (n i)) (rung₁ c (n i)) (rung₂ c (n i)) v)
      (Icc (-1) 1) :=
    continuousOn_finsetSum _ fun i hi => continuousOn_const.mul (hI' ▸ continuousOn_scalingLap_rung (hI i hi))
  exact this.congr fun v _ => scalingLap_comb v

/-- `−(θ + ½)²G` is even on `[−1, 1]`. -/
theorem scalingLap_comb_neg (hI : ∀ i ∈ I, ∃ χ, IsLevelIdx c (n i) χ) :
    ∀ s ∈ Icc (-1 : ℝ) 1, scalingLap (comb c I n a) (comb₁ c I n a) (comb₂ c I n a) (-s)
      = scalingLap (comb c I n a) (comb₁ c I n a) (comb₂ c I n a) s := by
  intro s hs
  rw [scalingLap_comb, scalingLap_comb]
  exact Finset.sum_congr rfl fun i hi => by rw [scalingLap_rung_neg (hI i hi) s hs]

/-- **Coefficients of `−(θ + ½)²G`**:
`∫_{−1}^{1} (−(θ + ½)²G) f = Σ_{i ∈ I} a_i ∫_{−1}^{1} (−(θ + ½)²h_{n(i)}) f`. -/
theorem integral_scalingLap_comb_mul (hI : ∀ i ∈ I, ∃ χ, IsLevelIdx c (n i) χ) {f : ℝ → ℝ}
    (hf : ContinuousOn f (uIcc (-1) 1)) :
    ∫ v in (-1 : ℝ)..1, scalingLap (comb c I n a) (comb₁ c I n a) (comb₂ c I n a) v * f v
      = ∑ i ∈ I, a i * ∫ v in (-1 : ℝ)..1,
          scalingLap (rung c (n i)) (rung₁ c (n i)) (rung₂ c (n i)) v * f v := by
  simp only [scalingLap_comb, Finset.sum_mul]
  rw [intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun v _ => ?_
    ring
  · intro j hj
    exact (((continuousOn_scalingLap_rung (hI j hj)).const_smul (a j)).mul hf).intervalIntegrable

/-- **The Cauchy endpoint leak**: for `c > 0` and `k ∉ n(I)`,
`∫_{−1}^{1} (−(θ + ½)²G) h_k = 2μ_k[q_k P_a(μ_k) − p_k Q_a(μ_k)]`. -/
theorem integral_scalingLap_comb_rung_of_not_mem (hc : 0 < c) (hI : ∀ i ∈ I, ∃ χ, IsLevelIdx c (n i) χ)
    {k : ℕ} (hk : ∃ χ, IsLevelIdx c k χ) (hkI : ∀ i ∈ I, n i ≠ k) :
    ∫ v in (-1 : ℝ)..1, scalingLap (comb c I n a) (comb₁ c I n a) (comb₂ c I n a) v * rung c k v
      = 2 * muR c k * (rung₁ c k 1 * cauchyT I (fun i => muR c (n i)) (fun i => a i * rung c (n i) 1) (muR c k)
          - rung c k 1 * cauchyT I (fun i => muR c (n i)) (fun i => a i * rung₁ c (n i) 1) (muR c k)) := by
  have hkc : ContinuousOn (rung c k) (uIcc (-1) 1) := by
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]; exact continuousOn_rung hk
  rw [integral_scalingLap_comb_mul hI hkc]
  have := sum_mul_eq_leak (I := I) (μ := fun i => muR c (n i)) (p := fun i => rung c (n i) 1)
    (q := fun i => rung₁ c (n i) 1) (a := a)
    (w := fun i => ∫ v in (-1 : ℝ)..1, scalingLap (rung c (n i)) (rung₁ c (n i)) (rung₂ c (n i)) v * rung c k v)
    (fun i hi => cauchy_scalingLap_rung hk (hI i hi) (hkI i hi).symm)
    (fun i hi => muR_ne hc hk (hI i hi) (hkI i hi).symm)
  exact (Finset.sum_congr rfl fun j _ => mul_comm _ _).trans this

/-- **The diagonal part**: `∫_{−1}^{1} (−(θ + ½)²G) h_k = −(χ_k + ¼) Σ_{n(i) = k} a_i + Σ_{i ∈ I} a_i M_{k n(i)}`
with `M_kl = ∫_{−1}^{1} (H_c h_l) h_k`, for every rung `k`. -/
theorem integral_scalingLap_comb_rung_eq (hI : ∀ i ∈ I, ∃ χ, IsLevelIdx c (n i) χ) {k : ℕ}
    (hk : ∃ χ, IsLevelIdx c k χ) :
    ∫ v in (-1 : ℝ)..1, scalingLap (comb c I n a) (comb₁ c I n a) (comb₂ c I n a) v * rung c k v
      = -(lev c k + 1 / 4) * (∑ i ∈ I, if n i = k then a i else 0)
        + ∑ i ∈ I, a i * ∫ v in (-1 : ℝ)..1, hamC c (rung c (n i)) (rung₂ c (n i)) v * rung c k v := by
  have hkc : ContinuousOn (rung c k) (uIcc (-1) 1) := by
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]; exact continuousOn_rung hk
  rw [integral_scalingLap_comb_mul hI hkc, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [integral_scalingLap_rung hk (hI i hi)]
  by_cases hik : n i = k
  · rw [if_pos hik, if_pos hik, hik]; ring
  · rw [if_neg hik, if_neg hik]; ring

/-- The rung coefficients of `−(θ + ½)²G`: the diagonal part on `n(I)`, the Cauchy leak off `n(I)`. -/
def coef (c : ℝ) (I : Finset κ) (n : κ → ℕ) (a : κ → ℝ) (k : ℕ) : ℝ :=
  if k ∈ I.image n then
    -(lev c k + 1 / 4) * (∑ i ∈ I, if n i = k then a i else 0)
      + ∑ i ∈ I, a i * ∫ v in (-1 : ℝ)..1, hamC c (rung c (n i)) (rung₂ c (n i)) v * rung c k v
  else 2 * muR c k * (rung₁ c k 1 * cauchyT I (fun i => muR c (n i)) (fun i => a i * rung c (n i) 1) (muR c k)
      - rung c k 1 * cauchyT I (fun i => muR c (n i)) (fun i => a i * rung₁ c (n i) 1) (muR c k))

/-- `coef` is the rung coefficient `∫_{−1}^{1} (−(θ + ½)²G) h_k` for `c > 0`. -/
theorem integral_scalingLap_comb_rung (hc : 0 < c) (hI : ∀ i ∈ I, ∃ χ, IsLevelIdx c (n i) χ) {k : ℕ}
    (hk : ∃ χ, IsLevelIdx c k χ) :
    ∫ v in (-1 : ℝ)..1, scalingLap (comb c I n a) (comb₁ c I n a) (comb₂ c I n a) v * rung c k v
      = coef c I n a k := by
  unfold coef
  split_ifs with hkI
  · exact integral_scalingLap_comb_rung_eq hI hk
  · exact integral_scalingLap_comb_rung_of_not_mem hc hI hk fun i hi h => hkI (Finset.mem_image.2 ⟨i, hi, h⟩)

/-- **The rung expansion of `−(θ + ½)²G` in `L²(0, 1]`**: for `c > 0`, `−(θ + ½)²G = Σ_k coef_k h_k` over all even
rungs, in norm. -/
theorem hasSum_scalingLap_comb (hc : 0 < c) (hI : ∀ i ∈ I, ∃ χ, IsLevelIdx c (n i) χ) :
    HasSum (fun k : LevelIdx c => coef c I n a k • evCls (continuousOn_rung k.2))
      (evCls (continuousOn_scalingLap_comb (a := a) hI)) := by
  have hF := continuousOn_scalingLap_comb (a := a) hI
  have hFe := scalingLap_comb_neg (a := a) hI
  have h := (rungBasis hc.ne').hasSum_repr (evCls hF)
  suffices e : (fun k : LevelIdx c => coef c I n a k • evCls (continuousOn_rung k.2))
      = fun k => (rungBasis hc.ne').repr (evCls hF) k • (rungBasis hc.ne') k by
    rw [e]; exact h
  funext k
  have hwc : ∀ k : LevelIdx c, ContinuousOn (rung c k) (Icc (-1) 1) := fun k => continuousOn_rung k.2
  have hwe : ∀ k : LevelIdx c, ∀ s ∈ Icc (-1 : ℝ) 1, rung c k (-s) = rung c k s :=
    fun k => (rung_spec k.2).2.2.2.2.1
  have hb : (rungBasis hc.ne' k : window 1) = Cvs.Prolate.EvenRungParseval.basisVec hwc k := by
    exact congrFun (Cvs.Prolate.EvenRungParseval.coe_hilbertBasis (w := fun k : LevelIdx c => rung c k) hwc hwe _ _ _) k
  rw [HilbertBasis.repr_apply_apply, hb, Cvs.Prolate.EvenRungParseval.inner_basisVec_left hwc hwe hF hFe k,
    Cvs.Prolate.EvenRungParseval.basisVec, smul_smul]
  have e : ∫ s in (-1 : ℝ)..1, rung c k s * scalingLap (comb c I n a) (comb₁ c I n a) (comb₂ c I n a) s
      = coef c I n a k := by
    rw [← integral_scalingLap_comb_rung hc hI k.2]
    exact intervalIntegral.integral_congr fun s _ => mul_comm _ _
  rw [e]
  have h2 : √2 / 2 * coef c I n a k * √2 = coef c I n a k := by
    have : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
    linear_combination (coef c I n a k / 2) * this
  rw [h2]
  rfl

/-- **The leak is square-summable**: `Σ_k coef_k² = ∫_{−1}^{1} (−(θ + ½)²G)²` for `c > 0`. -/
theorem hasSum_sq_coef (hc : 0 < c) (hI : ∀ i ∈ I, ∃ χ, IsLevelIdx c (n i) χ) :
    HasSum (fun k : LevelIdx c => coef c I n a k ^ 2)
      (∫ s in (-1 : ℝ)..1, scalingLap (comb c I n a) (comb₁ c I n a) (comb₂ c I n a) s ^ 2) := by
  have h := Cvs.Prolate.EvenRungParseval.hasSum_sq_integral_mul_rung hc.ne' (continuousOn_scalingLap_comb (a := a) hI)
    (scalingLap_comb_neg (a := a) hI)
  convert h using 1
  funext k
  rw [integral_scalingLap_comb_rung hc hI k.2]

/-- Pairing with an even continuous `E` sees only the even part of `f`. -/
theorem integral_mul_evenPart {E f : ℝ → ℝ} (hE : ContinuousOn E (Icc (-1) 1))
    (hEe : ∀ s ∈ Icc (-1 : ℝ) 1, E (-s) = E s) (hf : ContinuousOn f (Icc (-1) 1)) :
    ∫ s in (-1 : ℝ)..1, E s * ((f s + f (-s)) / 2) = ∫ s in (-1 : ℝ)..1, E s * f s := by
  have hI : uIcc (-1 : ℝ) 1 = Icc (-1) 1 := uIcc_of_le (by norm_num)
  have hfn : ContinuousOn (fun s => f (-s)) (Icc (-1) 1) :=
    hf.comp continuousOn_neg fun s hs => ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have i1 : IntervalIntegrable (fun s => E s * f s) volume (-1) 1 := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)]
    exact (hE.mul hf).integrableOn_compact isCompact_Icc
  have i2 : IntervalIntegrable (fun s => E s * f (-s)) volume (-1) 1 := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)]
    exact (hE.mul hfn).integrableOn_compact isCompact_Icc
  have hrefl : ∫ s in (-1 : ℝ)..1, E s * f (-s) = ∫ s in (-1 : ℝ)..1, E s * f s := by
    have e1 : ∫ s in (-1 : ℝ)..1, E s * f (-s) = ∫ s in (-1 : ℝ)..1, (fun t => E t * f t) (-s) := by
      refine intervalIntegral.integral_congr fun s hs => ?_
      simp only
      rw [hEe s (hI ▸ hs)]
    rw [e1, intervalIntegral.integral_comp_neg (fun t => E t * f t)]
    norm_num
  have e2 : ∫ s in (-1 : ℝ)..1, E s * ((f s + f (-s)) / 2)
      = (1 / 2) * ((∫ s in (-1 : ℝ)..1, E s * f s) + ∫ s in (-1 : ℝ)..1, E s * f (-s)) := by
    rw [← intervalIntegral.integral_add i1 i2, ← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun s _ => by ring
  rw [e2, hrefl]
  ring

/-- **The rung expansion, paired**: for `c > 0` and every continuous `f`,
`∫_{−1}^{1} (−(θ + ½)²G) f = Σ_k coef_k ∫_{−1}^{1} h_k f`. -/
theorem hasSum_integral_scalingLap_comb_mul (hc : 0 < c) (hI : ∀ i ∈ I, ∃ χ, IsLevelIdx c (n i) χ) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (-1) 1)) :
    HasSum (fun k : LevelIdx c => coef c I n a k * ∫ s in (-1 : ℝ)..1, rung c k s * f s)
      (∫ s in (-1 : ℝ)..1, scalingLap (comb c I n a) (comb₁ c I n a) (comb₂ c I n a) s * f s) := by
  have hF := continuousOn_scalingLap_comb (a := a) hI
  have hFe := scalingLap_comb_neg (a := a) hI
  have hfn : ContinuousOn (fun s => f (-s)) (Icc (-1) 1) :=
    hf.comp continuousOn_neg fun s hs => ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have hfe : ContinuousOn (fun s => (f s + f (-s)) / 2) (Icc (-1) 1) := (hf.add hfn).div_const 2
  have hfee : ∀ s ∈ Icc (-1 : ℝ) 1, (f (-s) + f (- -s)) / 2 = (f s + f (-s)) / 2 := fun s _ => by
    rw [neg_neg, add_comm]
  have h := Cvs.Prolate.EvenRungParseval.hasSum_integral_mul_rung hc.ne' hF hFe hfe hfee
  rw [integral_mul_evenPart hF hFe hf] at h
  convert h using 1
  funext k
  rw [integral_scalingLap_comb_rung hc hI k.2,
    integral_mul_evenPart (continuousOn_rung k.2) (rung_spec k.2).2.2.2.2.1 hf]

/-! ### The integral of `−(θ + ½)²G` -/

/-- **The integral of the scaling Laplacian**: for `G ∈ C²[−1, 1]`,
`∫_{−1}^{1} −(θ + ½)²G = −(G′(1) − G′(−1)) − ¼∫_{−1}^{1} G`. -/
theorem integral_scalingLap {G G₁ G₂ : ℝ → ℝ} (hG : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G (G₁ s) s)
    (hG₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G₁ (G₂ s) s) (hG₂c : ContinuousOn G₂ (uIcc (-1) 1)) :
    ∫ v in (-1 : ℝ)..1, scalingLap G G₁ G₂ v = -(G₁ 1 - G₁ (-1)) - (1 / 4) * ∫ v in (-1 : ℝ)..1, G v := by
  have hGc : ContinuousOn G (uIcc (-1) 1) := fun s hs => (hG s hs).continuousAt.continuousWithinAt
  have hG₁c : ContinuousOn G₁ (uIcc (-1) 1) := fun s hs => (hG₁ s hs).continuousAt.continuousWithinAt
  have hW : ∀ v ∈ uIcc (-1 : ℝ) 1, HasDerivAt (fun v => v ^ 2 * G₁ v) (v ^ 2 * G₂ v + 2 * v * G₁ v) v := by
    intro v hv
    refine ((hasDerivAt_pow 2 v).mul (hG₁ v hv)).congr_deriv ?_
    norm_num
    ring
  have hint1 : IntervalIntegrable (fun v => v ^ 2 * G₂ v + 2 * v * G₁ v) volume (-1) 1 :=
    (((continuousOn_id.pow 2).mul hG₂c).add ((continuousOn_const.mul continuousOn_id).mul hG₁c)).intervalIntegrable
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hW hint1
  have e : ∫ v in (-1 : ℝ)..1, scalingLap G G₁ G₂ v
      = -(∫ v in (-1 : ℝ)..1, (v ^ 2 * G₂ v + 2 * v * G₁ v)) - (1 / 4) * ∫ v in (-1 : ℝ)..1, G v := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg, ← intervalIntegral.integral_sub]
    · refine intervalIntegral.integral_congr fun v _ => ?_
      simp only [scalingLap]
      ring
    · exact hint1.neg
    · exact (hGc.intervalIntegrable).const_mul _
  rw [e, hftc]
  norm_num

/-- `G = Σ_{i ∈ I} a_i h_{n(i)}` has derivative `G′` on `[−1, 1]`. -/
theorem hasDerivAt_comb (hI : ∀ i ∈ I, ∃ χ, IsLevelIdx c (n i) χ) :
    ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (comb c I n a) (comb₁ c I n a s) s := fun s hs =>
  HasDerivAt.fun_sum fun j hj => ((rung_spec (hI j hj)).1 s hs).const_mul (a j)

/-- `G′` has derivative `G″` on `[−1, 1]`. -/
theorem hasDerivAt_comb₁ (hI : ∀ i ∈ I, ∃ χ, IsLevelIdx c (n i) χ) :
    ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (comb₁ c I n a) (comb₂ c I n a s) s := fun s hs =>
  HasDerivAt.fun_sum fun j hj => ((rung_spec (hI j hj)).2.1 s hs).const_mul (a j)

/-- **`∫_{−1}^{1} −(θ + ½)²G = −2G′(1) − ¼∫_{−1}^{1} G`** on spans of rungs. -/
theorem integral_scalingLap_comb (hI : ∀ i ∈ I, ∃ χ, IsLevelIdx c (n i) χ) :
    ∫ v in (-1 : ℝ)..1, scalingLap (comb c I n a) (comb₁ c I n a) (comb₂ c I n a) v
      = -2 * comb₁ c I n a 1 - (1 / 4) * ∫ v in (-1 : ℝ)..1, comb c I n a v := by
  have hc₂ : ContinuousOn (comb₂ c I n a) (uIcc (-1) 1) :=
    continuousOn_finsetSum _ fun j hj => continuousOn_const.mul (rung_spec (hI j hj)).2.2.1
  rw [integral_scalingLap (hasDerivAt_comb hI) (hasDerivAt_comb₁ hI) hc₂]
  have h1 : comb₁ c I n a (-1) = -comb₁ c I n a 1 := by
    simp only [comb₁, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [rung₁_neg (hI j hj) 1 ⟨by norm_num, le_rfl⟩]; ring
  rw [h1]; ring

/-- **The mean of the expansion**: `Σ_k coef_k ∫_{−1}^{1} h_k = −2G′(1) − ¼∫_{−1}^{1} G` for `c > 0`. -/
theorem hasSum_coef_mul_integral (hc : 0 < c) (hI : ∀ i ∈ I, ∃ χ, IsLevelIdx c (n i) χ) :
    HasSum (fun k : LevelIdx c => coef c I n a k * ∫ s in (-1 : ℝ)..1, rung c k s)
      (-2 * comb₁ c I n a 1 - (1 / 4) * ∫ v in (-1 : ℝ)..1, comb c I n a v) := by
  have h := hasSum_integral_scalingLap_comb_mul (a := a) hc hI (f := fun _ => (1 : ℝ)) continuousOn_const
  simp only [mul_one] at h
  rwa [integral_scalingLap_comb hI] at h

/-! ### Taylor generators of the leak -/

/-- **The leak to finite order about `μ̄`**: for `c > 0`, `k ∉ n(I)` and `μ_k ≠ μ̄`, the leak is
`2μ_k[q_k(Σ_{m ≤ M} b_P^{(m)}/(μ_k − μ̄)^{m+1} + R_P) − p_k(Σ_{m ≤ M} b_Q^{(m)}/(μ_k − μ̄)^{m+1} + R_Q)]`. -/
theorem integral_scalingLap_comb_rung_taylor (hc : 0 < c) (hI : ∀ i ∈ I, ∃ χ, IsLevelIdx c (n i) χ) {k : ℕ}
    (hk : ∃ χ, IsLevelIdx c k χ) (hkI : ∀ i ∈ I, n i ≠ k) {μbar : ℝ} (hμ : muR c k ≠ μbar) (M : ℕ) :
    ∫ v in (-1 : ℝ)..1, scalingLap (comb c I n a) (comb₁ c I n a) (comb₂ c I n a) v * rung c k v
      = 2 * muR c k * (rung₁ c k 1 *
            (∑ m ∈ Finset.range (M + 1), taylorGen I (fun i => muR c (n i)) (fun i => a i * rung c (n i) 1) μbar m
              / (muR c k - μbar) ^ (m + 1)
            + taylorRem I (fun i => muR c (n i)) (fun i => a i * rung c (n i) 1) μbar M (muR c k))
          - rung c k 1 *
            (∑ m ∈ Finset.range (M + 1), taylorGen I (fun i => muR c (n i)) (fun i => a i * rung₁ c (n i) 1) μbar m
              / (muR c k - μbar) ^ (m + 1)
            + taylorRem I (fun i => muR c (n i)) (fun i => a i * rung₁ c (n i) 1) μbar M (muR c k))) := by
  have h2 : ∀ i ∈ I, muR c k ≠ muR c (n i) := fun i hi => muR_ne hc hk (hI i hi) (hkI i hi).symm
  rw [integral_scalingLap_comb_rung_of_not_mem hc hI hk hkI, cauchyT_taylor _ _ _ hμ h2 M,
    cauchyT_taylor _ _ _ hμ h2 M]

end rung

/-! ### The spine profiles -/

section spine

variable {c : ℝ} {S : Finset ℕ}

/-- The spine profile is the span `Σ_{i : Option S} b_i h_{kOf i}`. -/
theorem spineG_eq_comb (c : ℝ) (a : S → ℝ) : spineG c a = comb c Finset.univ kOf (bOf c a) := by
  rw [← Cvs.L2a.ProlateFamilySpine.sum_option_eq_spineG]
  rfl

/-- The derivative of the spine profile, `Σ_{i : Option S} b_i h_{kOf i}′`. -/
def spineG₁ (c : ℝ) (a : S → ℝ) : ℝ → ℝ := comb₁ c Finset.univ kOf (bOf c a)

/-- The second derivative of the spine profile, `Σ_{i : Option S} b_i h_{kOf i}″`. -/
def spineG₂ (c : ℝ) (a : S → ℝ) : ℝ → ℝ := comb₂ c Finset.univ kOf (bOf c a)

/-- `spineG₁` is the derivative of the spine profile on `[−1, 1]`. -/
theorem hasDerivAt_spineG (hS : ∀ i : Option S, ∃ χ, IsLevelIdx c (kOf i) χ) (a : S → ℝ) :
    ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (spineG c a) (spineG₁ c a s) s := by
  rw [spineG_eq_comb]
  exact hasDerivAt_comb fun i _ => hS i

/-- **The Cauchy leak of a spine profile**: for `c > 0` and every rung `k` off `kOf(Option S)`,
`∫_{−1}^{1} (−(θ + ½)²G) h_k = 2μ_k[q_k P_b(μ_k) − p_k Q_b(μ_k)]` with `b = bOf`. -/
theorem integral_scalingLap_spineG_rung (hc : 0 < c) (hS : ∀ i : Option S, ∃ χ, IsLevelIdx c (kOf i) χ)
    (a : S → ℝ) {k : ℕ} (hk : ∃ χ, IsLevelIdx c k χ) (hkS : ∀ i : Option S, kOf i ≠ k) :
    ∫ v in (-1 : ℝ)..1, scalingLap (spineG c a) (spineG₁ c a) (spineG₂ c a) v * rung c k v
      = 2 * muR c k * (rung₁ c k 1 * cauchyT Finset.univ (fun i => muR c (kOf i))
            (fun i => bOf c a i * rung c (kOf i) 1) (muR c k)
          - rung c k 1 * cauchyT Finset.univ (fun i => muR c (kOf i))
            (fun i => bOf c a i * rung₁ c (kOf i) 1) (muR c k)) := by
  rw [spineG_eq_comb]
  exact integral_scalingLap_comb_rung_of_not_mem hc (fun i _ => hS i) hk fun i _ => hkS i

/-- **`∫_{−1}^{1} −(θ + ½)²G = −2G′(1)`** for a spine profile `G` and `c > 0`. -/
theorem integral_scalingLap_spineG (hc : 0 < c) (hS : ∀ i : Option S, ∃ χ, IsLevelIdx c (kOf i) χ)
    (a : S → ℝ) :
    ∫ v in (-1 : ℝ)..1, scalingLap (spineG c a) (spineG₁ c a) (spineG₂ c a) v = -2 * spineG₁ c a 1 := by
  have h0 := Cvs.Approximant.DeepIndexSpineSpan.integral_spineG hc a
  rw [spineG_eq_comb] at h0 ⊢
  unfold spineG₁ spineG₂
  rw [integral_scalingLap_comb fun i _ => hS i, h0]
  ring

/-- **The `h_0` split**: for `0 ∉ S`, `Σ_{k ∈ {0} ∪ 2S} b_k h_k = G + δh_0` with the spine profile
`G = spineG (b ∘ 2·)` and `δ = b_0 + Σ_{j ∈ S} b_{2j}α_j`. -/
theorem sum_rung_eq_spineG_add (h0 : 0 ∉ S) (b : ℕ → ℝ) (v : ℝ) :
    ∑ k ∈ insert 0 (S.image (2 * ·)), b k * rung c k v
      = spineG c (fun j : S => b (2 * j)) v + (b 0 + ∑ j : S, b (2 * j) * alpha c j) * rung c 0 v := by
  have h0' : 0 ∉ S.image (2 * ·) := by
    simp only [Finset.mem_image, not_exists, not_and]
    intro j hj h
    have : j = 0 := by omega
    exact h0 (this ▸ hj)
  rw [Finset.sum_insert h0', Finset.sum_image fun i _ j _ h => by simpa using h]
  have e1 : ∑ j ∈ S, b (2 * j) * rung c (2 * j) v = ∑ j : S, b (2 * (j : ℕ)) * rung c (2 * (j : ℕ)) v :=
    (Finset.sum_coe_sort S fun j => b (2 * j) * rung c (2 * j) v).symm
  have e2 : spineG c (fun j : S => b (2 * j)) v
      = ∑ j : S, b (2 * (j : ℕ)) * rung c (2 * (j : ℕ)) v
        - (∑ j : S, b (2 * (j : ℕ)) * alpha c j) * rung c 0 v := by
    simp only [spineG, mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [e1, e2]
  ring

end spine

/-! ### On the rung space at `c = 2πx` -/

/-- **The Cauchy leak on the rung space**: for `x ≥ 1`, `G = Σ_{m < x} a_m rung (2πx) (2m)` and every rung `k` not
of the form `2m`, `m < x`, `∫_{−1}^{1} (−(θ + ½)²G) h_k` is the Cauchy leak. -/
theorem rungSpace_leak {x : ℕ} (hx : 1 ≤ x) (a : ℕ → ℝ) {k : ℕ} (hk : ∃ χ, IsLevelIdx (2 * π * x) k χ)
    (hkI : ∀ m < x, 2 * m ≠ k) :
    ∫ v in (-1 : ℝ)..1, scalingLap (comb (2 * π * x) (Finset.range x) (2 * ·) a)
        (comb₁ (2 * π * x) (Finset.range x) (2 * ·) a) (comb₂ (2 * π * x) (Finset.range x) (2 * ·) a) v
        * rung (2 * π * x) k v
      = 2 * muR (2 * π * x) k * (rung₁ (2 * π * x) k 1
            * cauchyT (Finset.range x) (fun m => muR (2 * π * x) (2 * m))
              (fun m => a m * rung (2 * π * x) (2 * m) 1) (muR (2 * π * x) k)
          - rung (2 * π * x) k 1 * cauchyT (Finset.range x) (fun m => muR (2 * π * x) (2 * m))
              (fun m => a m * rung₁ (2 * π * x) (2 * m) 1) (muR (2 * π * x) k)) := by
  have hc : 0 < 2 * π * x := by
    have : (1 : ℝ) ≤ x := by exact_mod_cast hx
    positivity
  exact integral_scalingLap_comb_rung_of_not_mem hc (fun m hm => rungSpace_level (Finset.mem_range.1 hm)) hk
    fun m hm => hkI m (Finset.mem_range.1 hm)

/-- **The leak to finite order about `μ_0` on the rung space**: for `x ≥ 1` and `k` not of the form `2m`, `m < x`,
the leak is its `M`-th order Taylor sum about `μ̄ = muR (2πx) 0` plus the exact remainder. -/
theorem rungSpace_leak_taylor {x : ℕ} (hx : 1 ≤ x) (a : ℕ → ℝ) {k : ℕ} (hk : ∃ χ, IsLevelIdx (2 * π * x) k χ)
    (hkI : ∀ m < x, 2 * m ≠ k) (M : ℕ) :
    ∫ v in (-1 : ℝ)..1, scalingLap (comb (2 * π * x) (Finset.range x) (2 * ·) a)
        (comb₁ (2 * π * x) (Finset.range x) (2 * ·) a) (comb₂ (2 * π * x) (Finset.range x) (2 * ·) a) v
        * rung (2 * π * x) k v
      = 2 * muR (2 * π * x) k * (rung₁ (2 * π * x) k 1 *
            (∑ m ∈ Finset.range (M + 1), taylorGen (Finset.range x) (fun i => muR (2 * π * x) (2 * i))
                (fun i => a i * rung (2 * π * x) (2 * i) 1) (muR (2 * π * x) 0) m
              / (muR (2 * π * x) k - muR (2 * π * x) 0) ^ (m + 1)
            + taylorRem (Finset.range x) (fun i => muR (2 * π * x) (2 * i))
                (fun i => a i * rung (2 * π * x) (2 * i) 1) (muR (2 * π * x) 0) M (muR (2 * π * x) k))
          - rung (2 * π * x) k 1 *
            (∑ m ∈ Finset.range (M + 1), taylorGen (Finset.range x) (fun i => muR (2 * π * x) (2 * i))
                (fun i => a i * rung₁ (2 * π * x) (2 * i) 1) (muR (2 * π * x) 0) m
              / (muR (2 * π * x) k - muR (2 * π * x) 0) ^ (m + 1)
            + taylorRem (Finset.range x) (fun i => muR (2 * π * x) (2 * i))
                (fun i => a i * rung₁ (2 * π * x) (2 * i) 1) (muR (2 * π * x) 0) M (muR (2 * π * x) k))) := by
  have hc : 0 < 2 * π * x := by
    have : (1 : ℝ) ≤ x := by exact_mod_cast hx
    positivity
  have hk0 : k ≠ 0 := fun h => hkI 0 (by omega) (by omega)
  have hμ : muR (2 * π * x) k ≠ muR (2 * π * x) 0 :=
    muR_ne hc hk (rungSpace_level (j := 0) (by omega)) hk0
  exact integral_scalingLap_comb_rung_taylor hc (fun m hm => rungSpace_level (Finset.mem_range.1 hm)) hk
    (fun m hm => hkI m (Finset.mem_range.1 hm)) hμ M

/-- At `c = 2πx` with `x ≥ 1`, every spine index `kOf i` over `R_F`'s index set `SF x` has a level. -/
theorem SF_levels {x : ℕ} (hx : 1 ≤ x) :
    ∀ i : Option (Cvs.Approximant.SpineSubspace.SF x), ∃ χ, IsLevelIdx (2 * π * x) (kOf i) χ := by
  rintro (_ | j)
  · exact rungSpace_level (j := 0) (by omega)
  · exact rungSpace_level (Cvs.Approximant.SpineSubspace.SF_lt x j j.2)

/-- **The Cauchy leak of the `R_F` profiles**: for `x ≥ 1`, `a : SF x → ℝ` and every rung `k` not of the form `2m`,
`m < x`, `∫_{−1}^{1} (−(θ + ½)² spineG) h_k` is the Cauchy leak over `Option (SF x)`. -/
theorem SF_leak {x : ℕ} (hx : 1 ≤ x) (a : Cvs.Approximant.SpineSubspace.SF x → ℝ) {k : ℕ}
    (hk : ∃ χ, IsLevelIdx (2 * π * x) k χ) (hkI : ∀ m < x, 2 * m ≠ k) :
    ∫ v in (-1 : ℝ)..1, scalingLap (spineG (2 * π * x) a) (spineG₁ (2 * π * x) a) (spineG₂ (2 * π * x) a) v
        * rung (2 * π * x) k v
      = 2 * muR (2 * π * x) k * (rung₁ (2 * π * x) k 1 * cauchyT Finset.univ (fun i => muR (2 * π * x) (kOf i))
            (fun i => bOf (2 * π * x) a i * rung (2 * π * x) (kOf i) 1) (muR (2 * π * x) k)
          - rung (2 * π * x) k 1 * cauchyT Finset.univ (fun i => muR (2 * π * x) (kOf i))
            (fun i => bOf (2 * π * x) a i * rung₁ (2 * π * x) (kOf i) 1) (muR (2 * π * x) k)) := by
  have hc : 0 < 2 * π * x := by
    have : (1 : ℝ) ≤ x := by exact_mod_cast hx
    positivity
  refine integral_scalingLap_spineG_rung hc (SF_levels hx) a hk ?_
  rintro (_ | j)
  · exact hkI 0 (by omega)
  · exact hkI j (Cvs.Approximant.SpineSubspace.SF_lt x j j.2)

/-- **The integral of `−(θ + ½)²` on the `R_F` profiles**: `∫_{−1}^{1} −(θ + ½)²G = −2G′(1)` for `x ≥ 1`. -/
theorem SF_integral {x : ℕ} (hx : 1 ≤ x) (a : Cvs.Approximant.SpineSubspace.SF x → ℝ) :
    ∫ v in (-1 : ℝ)..1, scalingLap (spineG (2 * π * x) a) (spineG₁ (2 * π * x) a) (spineG₂ (2 * π * x) a) v
      = -2 * spineG₁ (2 * π * x) a 1 := by
  have hc : 0 < 2 * π * x := by
    have : (1 : ℝ) ≤ x := by exact_mod_cast hx
    positivity
  exact integral_scalingLap_spineG hc (SF_levels hx) a

/-- **The `h_0` split on the rung space**: for `x ≥ 1`, `Σ_{m < x} b_{2m} rung (2πx) (2m) = G + δh_0` with the
`R_F` profile `G = spineG (b ∘ 2·)` on `SF x` and `δ = b_0 + Σ_{j ∈ SF x} b_{2j}α_j`. -/
theorem SF_split {x : ℕ} (hx : 1 ≤ x) (b : ℕ → ℝ) (v : ℝ) :
    ∑ k ∈ (Finset.range x).image (2 * ·), b k * rung (2 * π * x) k v
      = spineG (2 * π * x) (fun j : Cvs.Approximant.SpineSubspace.SF x => b (2 * j)) v
        + (b 0 + ∑ j : Cvs.Approximant.SpineSubspace.SF x, b (2 * j) * alpha (2 * π * x) j) * rung (2 * π * x) 0 v := by
  have hI : (Finset.range x).image (2 * ·) = insert 0 ((Cvs.Approximant.SpineSubspace.SF x).image (2 * ·)) := by
    ext k
    simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨j, hj, rfl⟩
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · exact Or.inl rfl
      · exact Or.inr ⟨j, ⟨hj, hj0⟩, rfl⟩
    · rintro (rfl | ⟨j, ⟨hj, -⟩, rfl⟩)
      · exact ⟨0, hx, rfl⟩
      · exact ⟨j, hj, rfl⟩
  rw [hI]
  exact sum_rung_eq_spineG_add (by simp) b v

/-- **The integral-zero split of a span**: with `m_k = ∫_{−1}^{1} h_k` and `δ = (Σ_{k ∈ I} b_k m_k)/m_0`, the
coefficients `b_k − δ[k = 0]` give an integral-zero combination, for `c > 0` and `0 ∈ I`. -/
theorem integral_sharp_eq_zero {c : ℝ} {I : Finset ℕ} (hc : 0 < c) (hI : ∀ j ∈ I, ∃ χ, IsLevelIdx c j χ)
    (h0 : 0 ∈ I) (b : ℕ → ℝ) :
    ∫ v in (-1 : ℝ)..1, ∑ k ∈ I, (b k - if k = 0 then
        (∑ j ∈ I, b j * ∫ s in (-1 : ℝ)..1, rung c j s) / ∫ s in (-1 : ℝ)..1, rung c 0 s else 0) * rung c k v
      = 0 := by
  have hm0 := Cvs.Prolate.EvenRungsByIndex.integral_rung_zero_ne hc
  set δ := (∑ j ∈ I, b j * ∫ s in (-1 : ℝ)..1, rung c j s) / ∫ s in (-1 : ℝ)..1, rung c 0 s with hδ
  have hint : ∀ k ∈ I, IntervalIntegrable (fun v => (b k - if k = 0 then δ else 0) * rung c k v) volume (-1) 1 := by
    intro k hk
    have := continuousOn_rung (hI k hk)
    rw [← uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at this
    exact (continuousOn_const.mul this).intervalIntegrable
  rw [intervalIntegral.integral_finsetSum hint]
  have e : ∀ k ∈ I, ∫ v in (-1 : ℝ)..1, (b k - if k = 0 then δ else 0) * rung c k v
      = b k * (∫ s in (-1 : ℝ)..1, rung c k s) - if k = 0 then δ * ∫ s in (-1 : ℝ)..1, rung c 0 s else 0 := by
    intro k _
    rw [intervalIntegral.integral_const_mul]
    split_ifs with hk0
    · rw [hk0]; ring
    · ring
  rw [Finset.sum_congr rfl e, Finset.sum_sub_distrib, Finset.sum_ite_eq' I 0, if_pos h0, hδ,
    div_mul_cancel₀ _ hm0, sub_self]

end Cvs.Prolate.ScalingLaplacianEndpointLeak
