import Mathlib
import Cvs.Finite.EvenCosineLatticeSampling
import Cvs.L2a.AngularProlateTailPositive
import Cvs.Prolate.PlungeMassTrace
import Cvs.Prolate.SlepianCommutingRelation

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The difference of two rank-one projections: spectrum and floor, and the sinc lattice

For `T w = ⟪σ, w⟫σ − ⟪e, w⟫e` with `a = ‖e‖²`, `p = ‖σ‖²`, `c = ⟪e, σ⟫`: `T³ = (p − a)T² + (ap − c²)T`, the nonzero
eigenvalues are roots of `μ² − (p − a)μ − (ap − c²)`, and `⟪w, Tw⟫ ≥ μ₋‖w‖²`, attained when `e`, `σ` are
independent. On `ℓ²(ℤ)` the sinc row `σ_t = (sinc(π(n − t)))_n` is a unit vector (Cvs.Finite.EvenCosineLatticeSampling), so with `e` the `k`-th
coordinate vector the floor of `L(I − eeᵀ + σ_tσ_tᵀ)` is `L(1 − √(1 − sinc²(π(k − t))))`.
-/

noncomputable section

open Real

namespace Cvs.Upstream.RankOneProjectionDifference

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

/-- The difference of two rank-one maps, `T w = ⟪σ, w⟫σ − ⟪e, w⟫e`. -/
def T (e σ : E) : Module.End ℝ E where
  toFun w := ⟪σ, w⟫ • σ - ⟪e, w⟫ • e
  map_add' x y := by simp only [inner_add_right, add_smul]; abel
  map_smul' r x := by simp only [inner_smul_right, smul_sub, smul_smul, RingHom.id_apply]

/-- `T w = ⟪σ, w⟫σ − ⟪e, w⟫e`. -/
theorem T_apply (e σ w : E) : T e σ w = ⟪σ, w⟫ • σ - ⟪e, w⟫ • e := rfl

/-- `T` vanishes on the orthogonal complement of `{e, σ}`. -/
theorem T_eq_zero (e σ : E) {w : E} (he : ⟪e, w⟫ = 0) (hσ : ⟪σ, w⟫ = 0) : T e σ w = 0 := by
  simp [T_apply, he, hσ]

/-- `T` on the span of `σ` and `e`, in coordinates. -/
theorem T_comb (e σ : E) (x y : ℝ) :
    T e σ (x • σ + y • e)
      = (x * ⟪σ, σ⟫ + y * ⟪e, σ⟫) • σ + (-(x * ⟪e, σ⟫ + y * ⟪e, e⟫)) • e := by
  rw [T_apply]
  simp only [inner_add_right, real_inner_smul_right, real_inner_comm e σ]
  rw [neg_smul, sub_eq_add_neg]

/-- `T w` as a combination of `σ` and `e`. -/
theorem T_eq_comb (e σ w : E) : T e σ w = ⟪σ, w⟫ • σ + (-⟪e, w⟫) • e := by
  rw [T_apply, neg_smul, sub_eq_add_neg]

/-- **The cubic law**: `T³ = (p − a)T² + (ap − c²)T`, with `a = ‖e‖²`, `p = ‖σ‖²`, `c = ⟪e, σ⟫`. -/
theorem T_cube (e σ w : E) :
    T e σ (T e σ (T e σ w))
      = (⟪σ, σ⟫ - ⟪e, e⟫) • T e σ (T e σ w) + (⟪e, e⟫ * ⟪σ, σ⟫ - ⟪e, σ⟫ ^ 2) • T e σ w := by
  rw [T_eq_comb e σ w, T_comb, T_comb]
  module

/-- **The eigenvector at a root**: if `μ² − (p − a)μ − (ap − c²) = 0` then `T((μ − p)e + cσ) = μ((μ − p)e + cσ)`. -/
theorem T_eigvec (e σ : E) {μ : ℝ}
    (hμ : μ ^ 2 - (⟪σ, σ⟫ - ⟪e, e⟫) * μ - (⟪e, e⟫ * ⟪σ, σ⟫ - ⟪e, σ⟫ ^ 2) = 0) :
    T e σ ((μ - ⟪σ, σ⟫) • e + ⟪e, σ⟫ • σ) = μ • ((μ - ⟪σ, σ⟫) • e + ⟪e, σ⟫ • σ) := by
  have h := T_comb e σ ⟪e, σ⟫ (μ - ⟪σ, σ⟫)
  rw [add_comm ((μ - ⟪σ, σ⟫) • e) (⟪e, σ⟫ • σ), h]
  have h1 : ⟪e, σ⟫ * ⟪σ, σ⟫ + (μ - ⟪σ, σ⟫) * ⟪e, σ⟫ = μ * ⟪e, σ⟫ := by ring
  have h2 : -(⟪e, σ⟫ * ⟪e, σ⟫ + (μ - ⟪σ, σ⟫) * ⟪e, e⟫) = μ * (μ - ⟪σ, σ⟫) := by
    linear_combination (-1 : ℝ) * hμ
  rw [h1, h2, smul_add, smul_smul, smul_smul]

/-- The second eigenvector at a root, `ce − (μ + a)σ`. -/
theorem T_eigvec' (e σ : E) {μ : ℝ}
    (hμ : μ ^ 2 - (⟪σ, σ⟫ - ⟪e, e⟫) * μ - (⟪e, e⟫ * ⟪σ, σ⟫ - ⟪e, σ⟫ ^ 2) = 0) :
    T e σ (⟪e, σ⟫ • e + (-(μ + ⟪e, e⟫)) • σ) = μ • (⟪e, σ⟫ • e + (-(μ + ⟪e, e⟫)) • σ) := by
  have h := T_comb e σ (-(μ + ⟪e, e⟫)) ⟪e, σ⟫
  rw [add_comm (⟪e, σ⟫ • e) ((-(μ + ⟪e, e⟫)) • σ), h]
  have h1 : -(μ + ⟪e, e⟫) * ⟪σ, σ⟫ + ⟪e, σ⟫ * ⟪e, σ⟫ = μ * (-(μ + ⟪e, e⟫)) := by
    linear_combination hμ
  have h2 : -(-(μ + ⟪e, e⟫) * ⟪e, σ⟫ + ⟪e, σ⟫ * ⟪e, e⟫) = μ * ⟪e, σ⟫ := by ring
  rw [h1, h2, smul_add, smul_smul, smul_smul]

/-- **Each root is an eigenvalue** when `e` and `σ` are linearly independent. -/
theorem hasEigenvalue_T {e σ : E} (hind : LinearIndependent ℝ ![e, σ]) {μ : ℝ}
    (hμ : μ ^ 2 - (⟪σ, σ⟫ - ⟪e, e⟫) * μ - (⟪e, e⟫ * ⟪σ, σ⟫ - ⟪e, σ⟫ ^ 2) = 0) :
    Module.End.HasEigenvalue (T e σ) μ := by
  have hpair := LinearIndependent.pair_iff.mp hind
  by_cases h : μ - ⟪σ, σ⟫ = 0 ∧ ⟪e, σ⟫ = 0
  · obtain ⟨h1, h2⟩ := h
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := ⟪e, σ⟫ • e + (-(μ + ⟪e, e⟫)) • σ)
      ⟨Module.End.mem_eigenspace_iff.mpr (T_eigvec' e σ hμ), ?_⟩
    intro h0
    have := (hpair _ _ h0).2
    have hσ : σ ≠ 0 := hind.ne_zero 1
    have hp : 0 < ⟪σ, σ⟫ := real_inner_self_pos.mpr hσ
    have ha : 0 ≤ ⟪e, e⟫ := real_inner_self_nonneg
    have hμp : μ = ⟪σ, σ⟫ := by linarith
    rw [hμp] at this
    linarith
  · refine Module.End.hasEigenvalue_of_hasEigenvector (x := (μ - ⟪σ, σ⟫) • e + ⟪e, σ⟫ • σ)
      ⟨Module.End.mem_eigenspace_iff.mpr (T_eigvec e σ hμ), ?_⟩
    intro h0
    exact h (hpair _ _ h0)

/-- **Every eigenvalue is `0` or a root**: `Tw = λw`, `w ≠ 0` give `λ(λ² − (p − a)λ − (ap − c²)) = 0`. -/
theorem eigenvalue_root (e σ : E) {w : E} (hw : w ≠ 0) {l : ℝ} (hT : T e σ w = l • w) :
    l * (l ^ 2 - (⟪σ, σ⟫ - ⟪e, e⟫) * l - (⟪e, e⟫ * ⟪σ, σ⟫ - ⟪e, σ⟫ ^ 2)) = 0 := by
  have h := T_cube e σ w
  simp only [hT, map_smul, smul_smul] at h
  have h' : (l * (l * l) - ((⟪σ, σ⟫ - ⟪e, e⟫) * (l * l) + (⟪e, e⟫ * ⟪σ, σ⟫ - ⟪e, σ⟫ ^ 2) * l)) • w = 0 := by
    linear_combination (norm := module) h
  rcases smul_eq_zero.mp h' with h0 | h0
  · linear_combination h0
  · exact absurd h0 hw

/-! ### The smaller root and the floor -/

/-- The smaller root `μ₋ = ((p − a) − √((p − a)² + 4(ap − c²)))/2`. -/
def muLo (e σ : E) : ℝ :=
  ((⟪σ, σ⟫ - ⟪e, e⟫) - √((⟪σ, σ⟫ - ⟪e, e⟫) ^ 2 + 4 * (⟪e, e⟫ * ⟪σ, σ⟫ - ⟪e, σ⟫ ^ 2))) / 2

/-- The Gram determinant `ap − c²` is nonnegative. -/
theorem gram_nonneg (e σ : E) : 0 ≤ ⟪e, e⟫ * ⟪σ, σ⟫ - ⟪e, σ⟫ ^ 2 := by
  have := real_inner_mul_inner_self_le e σ
  nlinarith

/-- `μ₋` is a root of `μ² − (p − a)μ − (ap − c²)`. -/
theorem muLo_root (e σ : E) :
    muLo e σ ^ 2 - (⟪σ, σ⟫ - ⟪e, e⟫) * muLo e σ - (⟪e, e⟫ * ⟪σ, σ⟫ - ⟪e, σ⟫ ^ 2) = 0 := by
  have hD := gram_nonneg e σ
  have hX : 0 ≤ (⟪σ, σ⟫ - ⟪e, e⟫) ^ 2 + 4 * (⟪e, e⟫ * ⟪σ, σ⟫ - ⟪e, σ⟫ ^ 2) := by positivity
  have hs := Real.sq_sqrt hX
  unfold muLo
  linear_combination hs / 4

/-- `μ₋ ≤ 0`. -/
theorem muLo_le_zero (e σ : E) : muLo e σ ≤ 0 := by
  have hD := gram_nonneg e σ
  have h : |⟪σ, σ⟫ - ⟪e, e⟫| ≤ √((⟪σ, σ⟫ - ⟪e, e⟫) ^ 2 + 4 * (⟪e, e⟫ * ⟪σ, σ⟫ - ⟪e, σ⟫ ^ 2)) := by
    rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by linarith)
  unfold muLo
  have := le_abs_self (⟪σ, σ⟫ - ⟪e, e⟫)
  linarith

/-- `μ₋ ≤ p − a`. -/
theorem muLo_le_sub (e σ : E) : muLo e σ ≤ ⟪σ, σ⟫ - ⟪e, e⟫ := by
  have hD := gram_nonneg e σ
  have h : |⟪σ, σ⟫ - ⟪e, e⟫| ≤ √((⟪σ, σ⟫ - ⟪e, e⟫) ^ 2 + 4 * (⟪e, e⟫ * ⟪σ, σ⟫ - ⟪e, σ⟫ ^ 2)) := by
    rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by linarith)
  unfold muLo
  have := neg_abs_le (⟪σ, σ⟫ - ⟪e, e⟫)
  linarith

/-- The Gram determinant of `(σ, e, w)` times `ap − c²` is a squared norm. -/
theorem gram3_mul_nonneg (e σ w : E) :
    0 ≤ (⟪e, e⟫ * ⟪σ, σ⟫ - ⟪e, σ⟫ ^ 2)
      * ((⟪e, e⟫ * ⟪σ, σ⟫ - ⟪e, σ⟫ ^ 2) * ⟪w, w⟫
        - (⟪e, e⟫ * ⟪σ, w⟫ ^ 2 - 2 * ⟪e, σ⟫ * ⟪σ, w⟫ * ⟪e, w⟫ + ⟪σ, σ⟫ * ⟪e, w⟫ ^ 2)) := by
  set D := ⟪e, e⟫ * ⟪σ, σ⟫ - ⟪e, σ⟫ ^ 2
  set α := ⟪e, e⟫ * ⟪σ, w⟫ - ⟪e, σ⟫ * ⟪e, w⟫
  set β := ⟪σ, σ⟫ * ⟪e, w⟫ - ⟪e, σ⟫ * ⟪σ, w⟫
  have h := real_inner_self_nonneg (x := D • w - α • σ - β • e)
  have hexp : ⟪D • w - α • σ - β • e, D • w - α • σ - β • e⟫
      = D * D * ⟪w, w⟫ - 2 * D * α * ⟪σ, w⟫ - 2 * D * β * ⟪e, w⟫
        + α * α * ⟪σ, σ⟫ + 2 * α * β * ⟪e, σ⟫ + β * β * ⟪e, e⟫ := by
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
      real_inner_comm e σ, real_inner_comm σ w, real_inner_comm e w]
    ring
  rw [hexp] at h
  have : D * D * ⟪w, w⟫ - 2 * D * α * ⟪σ, w⟫ - 2 * D * β * ⟪e, w⟫
        + α * α * ⟪σ, σ⟫ + 2 * α * β * ⟪e, σ⟫ + β * β * ⟪e, e⟫
      = D * (D * ⟪w, w⟫
        - (⟪e, e⟫ * ⟪σ, w⟫ ^ 2 - 2 * ⟪e, σ⟫ * ⟪σ, w⟫ * ⟪e, w⟫ + ⟪σ, σ⟫ * ⟪e, w⟫ ^ 2)) := by
    simp only [D, α, β]; ring
  linarith

/-- The squared norm of `ασ + βe`. -/
theorem inner_comb_self (e σ : E) (α β : ℝ) :
    ⟪α • σ + β • e, α • σ + β • e⟫ = α ^ 2 * ⟪σ, σ⟫ + 2 * α * β * ⟪e, σ⟫ + β ^ 2 * ⟪e, e⟫ := by
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    real_inner_comm e σ]
  ring

/-- When `ap = c²` the vector `(as − ct)σ + (pt − cs)e` vanishes, so `as² − 2cst + pt² = 0`. -/
theorem quad_eq_zero_of_gram_zero (e σ w : E) (hD : ⟪e, e⟫ * ⟪σ, σ⟫ - ⟪e, σ⟫ ^ 2 = 0) :
    ⟪e, e⟫ * ⟪σ, w⟫ ^ 2 - 2 * ⟪e, σ⟫ * ⟪σ, w⟫ * ⟪e, w⟫ + ⟪σ, σ⟫ * ⟪e, w⟫ ^ 2 = 0 := by
  set α := ⟪e, e⟫ * ⟪σ, w⟫ - ⟪e, σ⟫ * ⟪e, w⟫
  set β := ⟪σ, σ⟫ * ⟪e, w⟫ - ⟪e, σ⟫ * ⟪σ, w⟫
  have hz := inner_comb_self e σ α β
  have hz' : α ^ 2 * ⟪σ, σ⟫ + 2 * α * β * ⟪e, σ⟫ + β ^ 2 * ⟪e, e⟫
      = (⟪e, e⟫ * ⟪σ, σ⟫ - ⟪e, σ⟫ ^ 2)
        * (⟪e, e⟫ * ⟪σ, w⟫ ^ 2 - 2 * ⟪e, σ⟫ * ⟪σ, w⟫ * ⟪e, w⟫ + ⟪σ, σ⟫ * ⟪e, w⟫ ^ 2) := by
    simp only [α, β]; ring
  rw [hz', hD, zero_mul] at hz
  have hz0 : α • σ + β • e = 0 := inner_self_eq_zero.mp hz
  have hw0 : ⟪α • σ + β • e, w⟫ = 0 := by rw [hz0, inner_zero_left]
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left] at hw0
  simp only [α, β] at hw0
  linear_combination hw0

/-- The scalar core of the floor: the root, the Gram inequalities and `μ₋ ≤ 0, p − a` give `μ₋n ≤ s² − t²`. -/
theorem scalar_floor {a p c s t n μ : ℝ} (hroot : μ ^ 2 - (p - a) * μ - (a * p - c ^ 2) = 0)
    (hμ0 : μ ≤ 0) (hμpa : μ ≤ p - a) (hD : 0 ≤ a * p - c ^ 2)
    (hG : 0 ≤ (a * p - c ^ 2) * ((a * p - c ^ 2) * n - (a * s ^ 2 - 2 * c * s * t + p * t ^ 2)))
    (hQ0 : a * p - c ^ 2 = 0 → a * s ^ 2 - 2 * c * s * t + p * t ^ 2 = 0)
    (ha : 0 ≤ a) (hp : 0 ≤ p) (hn : 0 ≤ n) (hta : t ^ 2 ≤ a * n) :
    μ * n ≤ s ^ 2 - t ^ 2 := by
  rcases hD.lt_or_eq with hDpos | hD0
  · have hQ : a * s ^ 2 - 2 * c * s * t + p * t ^ 2 ≤ (a * p - c ^ 2) * n := by
      have := (mul_nonneg_iff_of_pos_left hDpos).mp hG; linarith
    have hμneg : μ < 0 := by
      rcases hμ0.lt_or_eq with h | h
      · exact h
      · exfalso; rw [h] at hroot; nlinarith
    have hk : 0 < μ * (μ - p) := mul_pos_of_neg_of_neg hμneg (by linarith)
    have hsos : μ * (μ - p) * ((a * p - c ^ 2) * (s ^ 2 - t ^ 2) - μ * (a * s ^ 2 - 2 * c * s * t + p * t ^ 2))
        = (μ * (μ - p) * s + μ * c * t) ^ 2 := by
      linear_combination (-(μ * (μ - p) * (s ^ 2 - t ^ 2)) - μ ^ 2 * t ^ 2) * hroot
    have hform : 0 ≤ (a * p - c ^ 2) * (s ^ 2 - t ^ 2) - μ * (a * s ^ 2 - 2 * c * s * t + p * t ^ 2) := by
      have h2 : 0 ≤ μ * (μ - p) * ((a * p - c ^ 2) * (s ^ 2 - t ^ 2)
          - μ * (a * s ^ 2 - 2 * c * s * t + p * t ^ 2)) := by rw [hsos]; positivity
      exact (mul_nonneg_iff_of_pos_left hk).mp h2
    have h3 : 0 ≤ (a * p - c ^ 2) * (s ^ 2 - t ^ 2 - μ * n) := by nlinarith
    have := (mul_nonneg_iff_of_pos_left hDpos).mp h3
    linarith
  · have hQ := hQ0 hD0.symm
    have hlin : (a * s - c * t) ^ 2 = 0 := by
      have : (a * s - c * t) ^ 2 = a * (a * s ^ 2 - 2 * c * s * t + p * t ^ 2) - (a * p - c ^ 2) * t ^ 2 := by
        ring
      rw [this, hQ, ← hD0]; ring
    have hlin' : a * s = c * t := by nlinarith
    have hμ2 : μ * (μ - (p - a)) = 0 := by linear_combination hroot - hD0
    rcases eq_or_lt_of_le ha with ha0 | hapos
    · have ht0 : t = 0 := by rw [← ha0] at hta; nlinarith
      rw [ht0]; nlinarith [sq_nonneg s]
    · have h5 : a * s ^ 2 = p * t ^ 2 := by
        have h4 : a * (a * s ^ 2) = a * (p * t ^ 2) := by
          have : (a * s) ^ 2 = (c * t) ^ 2 := by rw [hlin']
          linear_combination this + t ^ 2 * hD0
        exact mul_left_cancel₀ hapos.ne' h4
      have hst : a * (s ^ 2 - t ^ 2) = (p - a) * t ^ 2 := by linarith
      rcases mul_eq_zero.mp hμ2 with hμz | hμz
      · rw [hμz]
        rcases le_or_gt a p with hap | hap
        · have : 0 ≤ a * (s ^ 2 - t ^ 2) := by rw [hst]; exact mul_nonneg (by linarith) (sq_nonneg t)
          have := (mul_nonneg_iff_of_pos_left hapos).mp this
          linarith
        · linarith
      · have hμe : μ = p - a := by linarith
        rw [hμe]
        have h6 : (p - a) * t ^ 2 ≥ (p - a) * (a * n) := by
          have : p - a ≤ 0 := by linarith
          nlinarith
        have h7 : a * (s ^ 2 - t ^ 2 - (p - a) * n) ≥ 0 := by nlinarith
        have := (mul_nonneg_iff_of_pos_left hapos).mp h7
        linarith

/-- **The floor of `T`**: `⟪w, Tw⟫ = ⟪σ, w⟫² − ⟪e, w⟫² ≥ μ₋‖w‖²`. -/
theorem muLo_le_inner (e σ w : E) : muLo e σ * ⟪w, w⟫ ≤ ⟪w, T e σ w⟫ := by
  have hTw : ⟪w, T e σ w⟫ = ⟪σ, w⟫ ^ 2 - ⟪e, w⟫ ^ 2 := by
    rw [T_apply, inner_sub_right, real_inner_smul_right, real_inner_smul_right, real_inner_comm σ w,
      real_inner_comm e w]; ring
  rw [hTw]
  have hta : ⟪e, w⟫ ^ 2 ≤ ⟪e, e⟫ * ⟪w, w⟫ := by
    have := real_inner_mul_inner_self_le e w; nlinarith
  exact scalar_floor (muLo_root e σ) (muLo_le_zero e σ) (muLo_le_sub e σ) (gram_nonneg e σ)
    (gram3_mul_nonneg e σ w) (quad_eq_zero_of_gram_zero e σ w) real_inner_self_nonneg
    real_inner_self_nonneg real_inner_self_nonneg hta

/-- **Equality at the eigenvector** `(μ₋ − p)e + cσ`. -/
theorem inner_eigvec (e σ : E) :
    ⟪(muLo e σ - ⟪σ, σ⟫) • e + ⟪e, σ⟫ • σ, T e σ ((muLo e σ - ⟪σ, σ⟫) • e + ⟪e, σ⟫ • σ)⟫
      = muLo e σ * ⟪(muLo e σ - ⟪σ, σ⟫) • e + ⟪e, σ⟫ • σ, (muLo e σ - ⟪σ, σ⟫) • e + ⟪e, σ⟫ • σ⟫ := by
  rw [T_eigvec e σ (muLo_root e σ), real_inner_smul_right]

/-! ### The lattice model -/

/-- **The model floor**: for unit `e`, `L(1 + μ₋)‖w‖² ≤ L⟪w, w − ⟪e, w⟫e + ⟪σ, w⟫σ⟫`, with
`μ₋² − (p − 1)μ₋ − (p − c²) = 0`. -/
theorem model_floor {e : E} (he : ⟪e, e⟫ = 1) (σ w : E) {L : ℝ} (hL : 0 ≤ L) :
    L * (1 + muLo e σ) * ⟪w, w⟫ ≤ L * ⟪w, w - ⟪e, w⟫ • e + ⟪σ, w⟫ • σ⟫
      ∧ muLo e σ ^ 2 - (⟪σ, σ⟫ - 1) * muLo e σ - (⟪σ, σ⟫ - ⟪e, σ⟫ ^ 2) = 0 := by
  refine ⟨?_, ?_⟩
  · have h := muLo_le_inner e σ w
    have hw : w - ⟪e, w⟫ • e + ⟪σ, w⟫ • σ = w + T e σ w := by rw [T_apply]; abel
    rw [hw, inner_add_right]
    nlinarith
  · have h := muLo_root e σ
    rw [he] at h
    linear_combination h

/-- **Two unit vectors**: `T v = ±√(1 − c²) v` for `v = (±√(1 − c²) − 1)e + cσ`, and `μ₋ = −√(1 − c²)`. -/
theorem unit_pair {e σ : E} (he : ⟪e, e⟫ = 1) (hσ : ⟪σ, σ⟫ = 1) :
    T e σ ((√(1 - ⟪e, σ⟫ ^ 2) - 1) • e + ⟪e, σ⟫ • σ)
        = √(1 - ⟪e, σ⟫ ^ 2) • ((√(1 - ⟪e, σ⟫ ^ 2) - 1) • e + ⟪e, σ⟫ • σ)
      ∧ T e σ ((-√(1 - ⟪e, σ⟫ ^ 2) - 1) • e + ⟪e, σ⟫ • σ)
        = (-√(1 - ⟪e, σ⟫ ^ 2)) • ((-√(1 - ⟪e, σ⟫ ^ 2) - 1) • e + ⟪e, σ⟫ • σ)
      ∧ muLo e σ = -√(1 - ⟪e, σ⟫ ^ 2) := by
  have hD : 0 ≤ 1 - ⟪e, σ⟫ ^ 2 := by have := gram_nonneg e σ; rw [he, hσ] at this; linarith
  have hs := Real.sq_sqrt hD
  have r1 : √(1 - ⟪e, σ⟫ ^ 2) ^ 2 - (⟪σ, σ⟫ - ⟪e, e⟫) * √(1 - ⟪e, σ⟫ ^ 2)
      - (⟪e, e⟫ * ⟪σ, σ⟫ - ⟪e, σ⟫ ^ 2) = 0 := by rw [he, hσ]; linear_combination hs
  have r2 : (-√(1 - ⟪e, σ⟫ ^ 2)) ^ 2 - (⟪σ, σ⟫ - ⟪e, e⟫) * (-√(1 - ⟪e, σ⟫ ^ 2))
      - (⟪e, e⟫ * ⟪σ, σ⟫ - ⟪e, σ⟫ ^ 2) = 0 := by rw [he, hσ]; linear_combination hs
  refine ⟨?_, ?_, ?_⟩
  · have := T_eigvec e σ r1; rwa [hσ] at this
  · have := T_eigvec e σ r2; rwa [hσ] at this
  · unfold muLo
    rw [he, hσ]
    have : (1 - 1 : ℝ) ^ 2 + 4 * (1 * 1 - ⟪e, σ⟫ ^ 2) = 2 ^ 2 * (1 - ⟪e, σ⟫ ^ 2) := by ring
    rw [this, Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
    ring

/-- The hypotheses are met by two orthonormal coordinate vectors of `ℝ²`. -/
theorem witness :
    LinearIndependent ℝ ![(EuclideanSpace.single 0 1 : EuclideanSpace ℝ (Fin 2)),
      EuclideanSpace.single 1 1] := by
  rw [LinearIndependent.pair_iff]
  intro s t h
  have h0 := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 0) h
  have h1 := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 1) h
  simp at h0 h1
  exact ⟨h0, h1⟩

/-! ### Attainment under independence -/

/-- Under independence the bottom eigenvector `(μ₋ − p)e + cσ` is nonzero. -/
theorem eigvec_ne_zero {e σ : E} (hind : LinearIndependent ℝ ![e, σ]) :
    (muLo e σ - ⟪σ, σ⟫) • e + ⟪e, σ⟫ • σ ≠ 0 := by
  intro h0
  have h := LinearIndependent.pair_iff.mp hind _ _ h0
  have hσ : σ ≠ 0 := hind.ne_zero 1
  have hp : 0 < ⟪σ, σ⟫ := real_inner_self_pos.mpr hσ
  have := muLo_le_zero e σ
  linarith [h.1]

/-- **`μ₋` is the minimum of the Rayleigh quotient of `T`** when `e` and `σ` are linearly independent. -/
theorem muLo_isLeast {e σ : E} (hind : LinearIndependent ℝ ![e, σ]) :
    IsLeast {r | ∃ w : E, w ≠ 0 ∧ r = ⟪w, T e σ w⟫ / ⟪w, w⟫} (muLo e σ) := by
  refine ⟨⟨_, eigvec_ne_zero hind, ?_⟩, ?_⟩
  · have hn : ⟪(muLo e σ - ⟪σ, σ⟫) • e + ⟪e, σ⟫ • σ, (muLo e σ - ⟪σ, σ⟫) • e + ⟪e, σ⟫ • σ⟫ ≠ 0 :=
      (real_inner_self_pos.mpr (eigvec_ne_zero hind)).ne'
    rw [inner_eigvec, mul_div_assoc, div_self hn, mul_one]
  · rintro r ⟨w, hw, rfl⟩
    rw [le_div_iff₀ (real_inner_self_pos.mpr hw)]
    exact muLo_le_inner e σ w

/-- **The model floor is attained**: for `e` independent of `σ` and `L ≥ 0`, `L(1 + μ₋)` is the minimum of
the Rayleigh quotient of `L(I − eeᵀ + σσᵀ)`. -/
theorem model_floor_isLeast {e σ : E} (hind : LinearIndependent ℝ ![e, σ]) {L : ℝ}
    (hL : 0 ≤ L) :
    IsLeast {r | ∃ w : E, w ≠ 0 ∧ r = L * ⟪w, w - ⟪e, w⟫ • e + ⟪σ, w⟫ • σ⟫ / ⟪w, w⟫}
      (L * (1 + muLo e σ)) := by
  have key : ∀ w : E, ⟪w, w - ⟪e, w⟫ • e + ⟪σ, w⟫ • σ⟫ = ⟪w, w⟫ + ⟪w, T e σ w⟫ := by
    intro w
    rw [show w - ⟪e, w⟫ • e + ⟪σ, w⟫ • σ = w + T e σ w by rw [T_apply]; abel, inner_add_right]
  obtain ⟨⟨w0, hw0, hr0⟩, -⟩ := muLo_isLeast hind
  refine ⟨⟨w0, hw0, ?_⟩, ?_⟩
  · have hn : ⟪w0, w0⟫ ≠ 0 := (real_inner_self_pos.mpr hw0).ne'
    rw [key, hr0]
    field_simp
  · rintro r ⟨w, hw, rfl⟩
    have hpos : 0 < ⟪w, w⟫ := real_inner_self_pos.mpr hw
    rw [key, le_div_iff₀ hpos]
    have h1 := mul_le_mul_of_nonneg_left (muLo_le_inner e σ w) hL
    nlinarith

/-- Two unit vectors with `|⟪e, σ⟫| < 1` are linearly independent. -/
theorem linearIndependent_of_abs_inner_lt {e σ : E} (he : ⟪e, e⟫ = 1) (hσ : ⟪σ, σ⟫ = 1)
    (hc : |⟪e, σ⟫| < 1) : LinearIndependent ℝ ![e, σ] := by
  rw [LinearIndependent.pair_iff]
  intro s t h
  have h1 := congrArg (fun x => ⟪e, x⟫) h
  have h2 := congrArg (fun x => ⟪σ, x⟫) h
  simp only [inner_add_right, real_inner_smul_right, he, hσ, inner_zero_right,
    real_inner_comm e σ] at h1 h2
  have hc2 : ⟪e, σ⟫ ^ 2 < 1 := by
    have := abs_lt.mp hc; nlinarith
  have hs : s * (1 - ⟪e, σ⟫ ^ 2) = 0 := by linear_combination h1 - ⟪e, σ⟫ * h2
  have hs0 : s = 0 := by
    rcases mul_eq_zero.mp hs with h | h
    · exact h
    · exfalso; linarith
  refine ⟨hs0, ?_⟩
  rw [hs0] at h2
  linarith

/-- **Two unit vectors at angle**: for `|c| < 1`, `√(1 − c²)` and `−√(1 − c²)` are eigenvalues of `T`. -/
theorem unit_pair_hasEigenvalue {e σ : E} (he : ⟪e, e⟫ = 1) (hσ : ⟪σ, σ⟫ = 1) (hc : |⟪e, σ⟫| < 1) :
    Module.End.HasEigenvalue (T e σ) (√(1 - ⟪e, σ⟫ ^ 2))
      ∧ Module.End.HasEigenvalue (T e σ) (-√(1 - ⟪e, σ⟫ ^ 2)) := by
  have hind := linearIndependent_of_abs_inner_lt he hσ hc
  have hD : 0 ≤ 1 - ⟪e, σ⟫ ^ 2 := by have := gram_nonneg e σ; rw [he, hσ] at this; linarith
  have hs := Real.sq_sqrt hD
  refine ⟨hasEigenvalue_T hind ?_, hasEigenvalue_T hind ?_⟩
  · rw [he, hσ]; linear_combination hs
  · rw [he, hσ]; linear_combination hs

/-! ### The two-sided sinc lattice -/

/-- **The shifted sinc row is a unit vector**: `∑_{n ∈ ℤ} sinc²(π(n − t)) = 1`. -/
theorem hasSum_sinc_sq_shift (t : ℝ) : HasSum (fun n : ℤ => sinc (π * (n - t)) ^ 2) 1 := by
  have hpsi : ∀ ξ : ℝ, Cvs.L2a.AngularProlateTailPositive.psi π (fun _ => 1) ξ = 2 * sinc (π * ξ) := by
    intro ξ
    unfold Cvs.L2a.AngularProlateTailPositive.psi Cvs.Prolate.SlepianCommutingRelation.kint
    have : ∀ s : ℝ, (1 : ℝ) * cos (π * ξ * s) = cos ((π * ξ) * s) * cos (0 * s) := by
      intro s; simp
    simp_rw [this]
    rw [Cvs.Prolate.PlungeMassTrace.integral_cos_mul_cos]
    ring_nf
  have h := Cvs.Finite.EvenCosineLatticeSampling.hasSum_sq_psi (c := π) (D := 1) pi_pos one_pos (by rw [mul_one]) (-t)
    (g := fun _ => (1 : ℝ)) (fun _ => rfl) continuousOn_const
  simp only [hpsi, mul_one, one_pow, intervalIntegral.integral_const, smul_eq_mul] at h
  have h' := h.mul_left (1 / 4)
  have hv : (1 / 4 : ℝ) * (2 * π / π * (1 - -1)) = 1 := by field_simp; norm_num
  have hf : (fun i : ℤ => 1 / 4 * (2 * sinc (π * (↑i + -t))) ^ 2) = fun n : ℤ => sinc (π * (n - t)) ^ 2 := by
    funext n
    rw [show π * ((n : ℝ) + -t) = π * (n - t) by ring]
    ring
  rw [hv, hf] at h'
  exact h'

/-- The shifted sinc row `σ_t = (sinc(π(n − t)))_{n ∈ ℤ}` in `ℓ²(ℤ)`. -/
def sigmaT (t : ℝ) : lp (fun _ : ℤ => ℝ) 2 :=
  ⟨fun n => sinc (π * (n - t)), memℓp_gen ((hasSum_sinc_sq_shift t).summable.congr fun n => by
    simp [Real.norm_eq_abs, sq_abs])⟩

/-- `‖σ_t‖ = 1`. -/
theorem inner_sigmaT_self (t : ℝ) : ⟪sigmaT t, sigmaT t⟫ = 1 := by
  rw [lp.inner_eq_tsum, ← (hasSum_sinc_sq_shift t).tsum_eq]
  refine tsum_congr fun n => ?_
  rw [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
  rfl

/-- The `k`-th coordinate vector of `ℓ²(ℤ)` is a unit vector. -/
theorem inner_single_self (k : ℤ) :
    ⟪(lp.single 2 k (1 : ℝ) : lp (fun _ : ℤ => ℝ) 2), lp.single 2 k (1 : ℝ)⟫ = 1 := by
  rw [lp.inner_single_left, lp.single_apply_self]
  simp

/-- The overlap of the `k`-th coordinate vector with `σ_t` is `sinc(π(k − t))`. -/
theorem inner_single_sigmaT (k : ℤ) (t : ℝ) :
    ⟪(lp.single 2 k (1 : ℝ) : lp (fun _ : ℤ => ℝ) 2), sigmaT t⟫ = sinc (π * (k - t)) := by
  rw [lp.inner_single_left]
  simp
  rfl

/-- **The two-sided lattice floor**: with `e` the `k`-th coordinate vector of `ℓ²(ℤ)`, `μ₋(e, σ_t) =
−√(1 − sinc²(π(k − t)))`, and `L(1 − √(1 − sinc²(π(k − t))))‖w‖² ≤ L⟪w, (I − eeᵀ + σ_tσ_tᵀ)w⟫` for `L ≥ 0`. -/
theorem lattice_floor (k : ℤ) (t : ℝ) {L : ℝ} (hL : 0 ≤ L) (w : lp (fun _ : ℤ => ℝ) 2) :
    muLo (lp.single 2 k (1 : ℝ) : lp (fun _ : ℤ => ℝ) 2) (sigmaT t) = -√(1 - sinc (π * (k - t)) ^ 2)
      ∧ L * (1 - √(1 - sinc (π * (k - t)) ^ 2)) * ⟪w, w⟫
        ≤ L * ⟪w, w - ⟪(lp.single 2 k (1 : ℝ) : lp (fun _ : ℤ => ℝ) 2), w⟫ • lp.single 2 k (1 : ℝ)
            + ⟪sigmaT t, w⟫ • sigmaT t⟫ := by
  have hμ := (unit_pair (inner_single_self k) (inner_sigmaT_self t)).2.2
  rw [inner_single_sigmaT] at hμ
  refine ⟨hμ, ?_⟩
  have h := (model_floor (inner_single_self k) (sigmaT t) w hL).1
  rwa [hμ, ← sub_eq_add_neg] at h

/-- `|sinc x| < 1` for `x ≠ 0`. -/
theorem abs_sinc_lt_one {x : ℝ} (hx : x ≠ 0) : |sinc x| < 1 := by
  rw [sinc_of_ne_zero hx, abs_div, div_lt_one (abs_pos.mpr hx)]
  exact abs_sin_lt_abs hx

/-- **The two-sided lattice floor is attained** off the lattice point `t = k`: `L(1 − √(1 − sinc²(π(k − t))))` is
the minimum of the Rayleigh quotient of `L(I − eeᵀ + σ_tσ_tᵀ)` on `ℓ²(ℤ)`. -/
theorem lattice_floor_isLeast (k : ℤ) {t : ℝ} (ht : t ≠ k) {L : ℝ} (hL : 0 ≤ L) :
    IsLeast {r | ∃ w : lp (fun _ : ℤ => ℝ) 2, w ≠ 0 ∧ r = L * ⟪w, w
        - ⟪(lp.single 2 k (1 : ℝ) : lp (fun _ : ℤ => ℝ) 2), w⟫ • lp.single 2 k (1 : ℝ)
        + ⟪sigmaT t, w⟫ • sigmaT t⟫ / ⟪w, w⟫}
      (L * (1 - √(1 - sinc (π * (k - t)) ^ 2))) := by
  have hx : π * ((k : ℝ) - t) ≠ 0 := mul_ne_zero pi_ne_zero (sub_ne_zero.mpr (Ne.symm ht))
  have hc : |⟪(lp.single 2 k (1 : ℝ) : lp (fun _ : ℤ => ℝ) 2), sigmaT t⟫| < 1 := by
    rw [inner_single_sigmaT]; exact abs_sinc_lt_one hx
  have hind := linearIndependent_of_abs_inner_lt (inner_single_self k) (inner_sigmaT_self t) hc
  have h := model_floor_isLeast hind hL
  rwa [(lattice_floor k t hL 0).1, ← sub_eq_add_neg] at h

end Cvs.Upstream.RankOneProjectionDifference
