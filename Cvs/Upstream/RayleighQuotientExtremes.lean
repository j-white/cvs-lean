import Mathlib

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Extreme Rayleigh quotients of operators on a finite-dimensional real inner product space

`lamMax T` and `lamMin T` are the supremum and infimum of the Rayleigh quotient of `T`. They are
eigenvalues of a self-adjoint `T`, are monotone and `1`-Lipschitz in the quadratic form (Weyl),
are invariant under orthogonal conjugation, and obey a Schur-complement bound near an isolated
extreme eigenvalue and a penalty bound for a rank-one penalty.
-/

noncomputable section

open scoped RealInnerProductSpace

namespace Cvs.StepA.Edge.PlanarBoxLemma
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The supremum of the Rayleigh quotient `⟪T x, x⟫ / ‖x‖²` over `x ≠ 0`. -/
def lamMax (T : E →L[ℝ] E) : ℝ := ⨆ x : {x : E // x ≠ 0}, T.rayleighQuotient x

/-- The infimum of the Rayleigh quotient `⟪T x, x⟫ / ‖x‖²` over `x ≠ 0`. -/
def lamMin (T : E →L[ℝ] E) : ℝ := ⨅ x : {x : E // x ≠ 0}, T.rayleighQuotient x

/-! ### Basic bounds -/

omit [FiniteDimensional ℝ E] in
/-- The Rayleigh quotient of a real operator is `⟪T x, x⟫ / ‖x‖²`. -/
private theorem rq_def (T : E →L[ℝ] E) (x : E) :
    T.rayleighQuotient x = ⟪T x, x⟫ / ‖x‖ ^ 2 :=
  rfl

omit [FiniteDimensional ℝ E] in
/-- The Rayleigh quotient over nonzero vectors is bounded above (by `‖T‖`). -/
private theorem bddAbove_rq (T : E →L[ℝ] E) :
    BddAbove (Set.range fun x : {x : E // x ≠ 0} => T.rayleighQuotient x) :=
  ⟨‖T‖, by
    rintro _ ⟨x, rfl⟩
    exact (le_abs_self _).trans (T.rayleighQuotient_le_norm x)⟩

-- generic (finite dimension: the Rayleigh quotient is bounded)
/-- Every value of the quadratic form lies below `lamMax`: `⟪T x, x⟫ ≤ lamMax T ‖x‖²`. -/
theorem inner_le_lamMax (T : E →L[ℝ] E) (x : E) : ⟪T x, x⟫ ≤ lamMax T * ‖x‖ ^ 2 := by
  by_cases hx : x = 0
  · simp [hx]
  have hpos : 0 < ‖x‖ ^ 2 := pow_pos (norm_pos_iff.mpr hx) 2
  have h1 : T.rayleighQuotient x ≤ lamMax T := le_ciSup (bddAbove_rq T) ⟨x, hx⟩
  rw [rq_def, div_le_iff₀ hpos] at h1
  exact h1

-- generic
/-- A bound on the quadratic form bounds `lamMax`: `⟪T x, x⟫ ≤ c ‖x‖²` for all `x` gives
`lamMax T ≤ c`. -/
theorem lamMax_le [Nontrivial E] {T : E →L[ℝ] E} {c : ℝ} (h : ∀ x, ⟪T x, x⟫ ≤ c * ‖x‖ ^ 2) :
    lamMax T ≤ c := by
  obtain ⟨y, hy⟩ := exists_ne (0 : E)
  have : Nonempty {x : E // x ≠ 0} := ⟨⟨y, hy⟩⟩
  refine ciSup_le fun x => ?_
  have hpos : 0 < ‖(x : E)‖ ^ 2 := pow_pos (norm_pos_iff.mpr x.2) 2
  rw [rq_def, div_le_iff₀ hpos]
  exact h x

-- generic
/-- A test vector bounds `lamMax` from below: `x ≠ 0` and `c ‖x‖² ≤ ⟪T x, x⟫` give
`c ≤ lamMax T`. -/
theorem le_lamMax_of {T : E →L[ℝ] E} {x : E} (hx : x ≠ 0) {c : ℝ}
    (h : c * ‖x‖ ^ 2 ≤ ⟪T x, x⟫) : c ≤ lamMax T := by
  have hpos : 0 < ‖x‖ ^ 2 := pow_pos (norm_pos_iff.mpr hx) 2
  refine le_trans ?_ (le_ciSup (bddAbove_rq T) ⟨x, hx⟩)
  rw [rq_def, le_div_iff₀ hpos]
  exact h

-- generic
open scoped Pointwise in
/-- `lamMin T = −lamMax (−T)`. -/
theorem lamMin_eq_neg_lamMax_neg (T : E →L[ℝ] E) : lamMin T = -lamMax (-T) := by
  unfold lamMin lamMax
  simp only [ContinuousLinearMap.rayleighQuotient_neg_apply]
  rw [iSup, iInf]
  have hr : (Set.range fun x : {x : E // x ≠ 0} => -T.rayleighQuotient x) =
      -(Set.range fun x : {x : E // x ≠ 0} => T.rayleighQuotient x) := by
    ext a
    simp [neg_eq_iff_eq_neg]
  rw [hr, Real.sSup_neg, neg_neg]

/-- Every value of the quadratic form lies above `lamMin`: `lamMin T ‖x‖² ≤ ⟪T x, x⟫`. -/
theorem lamMin_le_inner (T : E →L[ℝ] E) (x : E) : lamMin T * ‖x‖ ^ 2 ≤ ⟪T x, x⟫ := by
  have h := inner_le_lamMax (-T) x
  rw [lamMin_eq_neg_lamMax_neg]
  simp only [neg_apply, inner_neg_left] at h
  linarith

/-- A lower bound on the quadratic form bounds `lamMin`: `c ‖x‖² ≤ ⟪T x, x⟫` for all `x` gives
`c ≤ lamMin T`. -/
theorem le_lamMin [Nontrivial E] {T : E →L[ℝ] E} {c : ℝ} (h : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪T x, x⟫) :
    c ≤ lamMin T := by
  rw [lamMin_eq_neg_lamMax_neg]
  have : lamMax (-T) ≤ -c := lamMax_le fun x => by
    simp only [neg_apply, inner_neg_left]
    linarith [h x]
  linarith

/-- A test vector bounds `lamMin` from above: `x ≠ 0` and `⟪T x, x⟫ ≤ c ‖x‖²` give
`lamMin T ≤ c`. -/
theorem lamMin_le_of {T : E →L[ℝ] E} {x : E} (hx : x ≠ 0) {c : ℝ}
    (h : ⟪T x, x⟫ ≤ c * ‖x‖ ^ 2) : lamMin T ≤ c := by
  rw [lamMin_eq_neg_lamMax_neg]
  have : -c ≤ lamMax (-T) := le_lamMax_of hx (by
    simp only [neg_apply, inner_neg_left]
    linarith)
  linarith

-- generic; Mathlib `LinearMap.IsSymmetric.hasEigenvalue_iSup_of_finiteDimensional`
/-- **`lamMax` is an eigenvalue** of a self-adjoint operator on a nontrivial space. -/
theorem exists_eigen_lamMax [Nontrivial E] {T : E →L[ℝ] E} (hT : IsSelfAdjoint T) :
    ∃ x : E, x ≠ 0 ∧ T x = lamMax T • x := by
  obtain ⟨v, hv⟩ := hT.isSymmetric.hasEigenvalue_iSup_of_finiteDimensional.exists_hasEigenvector
  refine ⟨v, hv.2, ?_⟩
  have h1 := Module.End.mem_eigenspace_iff.mp hv.1
  simpa [lamMax, rq_def] using h1

/-- **`lamMin` is an eigenvalue** of a self-adjoint operator on a nontrivial space. -/
theorem exists_eigen_lamMin [Nontrivial E] {T : E →L[ℝ] E} (hT : IsSelfAdjoint T) :
    ∃ x : E, x ≠ 0 ∧ T x = lamMin T • x := by
  obtain ⟨x, hx, hTx⟩ := exists_eigen_lamMax (T := -T) hT.neg
  refine ⟨x, hx, ?_⟩
  rw [lamMin_eq_neg_lamMax_neg]
  have := congrArg Neg.neg hTx
  simp only [neg_apply, neg_neg] at this
  rw [this, neg_smul]

/-! ### Weyl -/

/-! ### Scaling and orthogonal conjugation -/

-- generic
/-- `lamMax (c • T) = c · lamMax T` for `c ≥ 0`. -/
theorem lamMax_smul {c : ℝ} (hc : 0 ≤ c) (T : E →L[ℝ] E) : lamMax (c • T) = c * lamMax T := by
  unfold lamMax
  rw [Real.mul_iSup_of_nonneg hc]
  congr 1
  ext x
  simp only [rq_def, smul_apply, inner_smul_left]
  simp [mul_div_assoc]

/-- `lamMin (c • T) = c · lamMin T` for `c ≥ 0`. -/
theorem lamMin_smul {c : ℝ} (hc : 0 ≤ c) (T : E →L[ℝ] E) : lamMin (c • T) = c * lamMin T := by
  rw [lamMin_eq_neg_lamMax_neg, lamMin_eq_neg_lamMax_neg, ← smul_neg, lamMax_smul hc]
  ring

-- generic
/-- **Orthogonal conjugation** preserves `lamMax`: for `U` norm-preserving and surjective,
`lamMax (U* T U) = lamMax T`. -/
theorem lamMax_conj {U : E →L[ℝ] E} (hU : ∀ x, ‖U x‖ = ‖x‖) (hUs : Function.Surjective U)
    (T : E →L[ℝ] E) : lamMax (ContinuousLinearMap.adjoint U ∘L T ∘L U) = lamMax T := by
  have hinj : ∀ x, U x = 0 → x = 0 := fun x hx => by
    rw [← norm_eq_zero, ← hU x, hx, norm_zero]
  let f : {x : E // x ≠ 0} → {x : E // x ≠ 0} := fun x => ⟨U x, fun h => x.2 (hinj x h)⟩
  have hf : Function.Surjective f := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hUs y
    exact ⟨⟨x, fun h => hy (by rw [h, map_zero])⟩, rfl⟩
  unfold lamMax
  refine Eq.trans ?_ (hf.iSup_comp fun y : {x : E // x ≠ 0} => T.rayleighQuotient y)
  congr 1
  ext x
  simp only [f, rq_def, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left,
    hU]

/-- **Orthogonal conjugation** preserves `lamMin`. -/
theorem lamMin_conj {U : E →L[ℝ] E} (hU : ∀ x, ‖U x‖ = ‖x‖) (hUs : Function.Surjective U)
    (T : E →L[ℝ] E) : lamMin (ContinuousLinearMap.adjoint U ∘L T ∘L U) = lamMin T := by
  rw [lamMin_eq_neg_lamMax_neg, lamMin_eq_neg_lamMax_neg, ← lamMax_conj hU hUs (-T)]
  congr 2
  ext x
  simp

/-! ### Schur-complement bounds near an isolated extreme eigenvalue -/

omit [FiniteDimensional ℝ E] in
/-- Pythagoras with squares: `⟪x, y⟫ = 0` gives `‖x + y‖² = ‖x‖² + ‖y‖²`. -/
private theorem norm_add_sq_of_inner_eq_zero {x y : E} (h : ⟪x, y⟫ = 0) :
    ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
  have h1 := norm_add_sq_eq_norm_sq_add_norm_sq_real h
  rw [sq, sq, sq]
  exact h1

omit [FiniteDimensional ℝ E] in
/-- An operator with `‖T x‖ ≤ ε ‖x‖` has `|⟪T u, v⟫| ≤ ε ‖u‖ ‖v‖`. -/
private theorem abs_inner_le_of_bound {T : E →L[ℝ] E} {ε : ℝ} (hε : ∀ x, ‖T x‖ ≤ ε * ‖x‖)
    (u v : E) : |⟪T u, v⟫| ≤ ε * ‖u‖ * ‖v‖ :=
  (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hε u) (norm_nonneg v))

-- merged §2(c)
/-- **Schur lower bound**: if `A₀ = −σ` on `W`, `A₀ ≥ −σ + g` on `Wᗮ`, `‖Eₚ‖ ≤ ε ≤ g/4` and
`⟪Eₚ u, u⟫ ≥ m ‖u‖²` on `W` with `m ≤ ε`, then `A₀ + Eₚ ≥ −σ + m − 2ε²/g`. -/
theorem schur_lower {A₀ Ep : E →L[ℝ] E} (hA : IsSelfAdjoint A₀) {W : Submodule ℝ E}
    {σ g ε m : ℝ} (hW : ∀ u ∈ W, A₀ u = (-σ) • u)
    (hgap : ∀ v ∈ Wᗮ, (-σ + g) * ‖v‖ ^ 2 ≤ ⟪A₀ v, v⟫) (hg : 0 < g)
    (hε : ∀ x, ‖Ep x‖ ≤ ε * ‖x‖) (hεg : 4 * ε ≤ g)
    (hm : ∀ u ∈ W, m * ‖u‖ ^ 2 ≤ ⟪Ep u, u⟫) (hmε : m ≤ ε) (x : E) :
    (-σ + m - 2 * ε ^ 2 / g) * ‖x‖ ^ 2 ≤ ⟪(A₀ + Ep) x, x⟫ := by
  obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.exists_add_mem_mem_orthogonal (K := W) x
  have huv : ⟪u, v⟫ = 0 := Submodule.inner_right_of_mem_orthogonal hu hv
  have hnorm := norm_add_sq_of_inner_eq_zero huv
  have hAu : A₀ u = (-σ) • u := hW u hu
  have h1 : ⟪A₀ u, u⟫ = -σ * ‖u‖ ^ 2 := by
    rw [hAu, real_inner_smul_left, real_inner_self_eq_norm_sq]
  have h2 : ⟪A₀ u, v⟫ = 0 := by rw [hAu, real_inner_smul_left, huv, mul_zero]
  have h3 : ⟪A₀ v, u⟫ = 0 := by
    have hs := hA.isSymmetric v u
    simp only [ContinuousLinearMap.coe_coe] at hs
    rw [hs, real_inner_comm, h2]
  have h4 := hgap v hv
  have h5 := hm u hu
  have c1 := (abs_le.mp (abs_inner_le_of_bound hε u v)).1
  have c2 := (abs_le.mp (abs_inner_le_of_bound hε v u)).1
  have c3 := (abs_le.mp (abs_inner_le_of_bound hε v v)).1
  set k := 2 * ε ^ 2 / g with hkdef
  have hk : k * g = 2 * ε ^ 2 := by rw [hkdef]; exact div_mul_cancel₀ _ hg.ne'
  have key : 0 ≤ k * ‖u‖ ^ 2 + (g - ε - m + k) * ‖v‖ ^ 2 - 2 * ε * ‖u‖ * ‖v‖ := by
    have hid : g / 2 * (k * ‖u‖ ^ 2 + (g - ε - m + k) * ‖v‖ ^ 2 - 2 * ε * ‖u‖ * ‖v‖) =
        (ε * ‖u‖ - g * ‖v‖ / 2) ^ 2 + ‖v‖ ^ 2 / 4 * ((g - 2 * ε) ^ 2 + 2 * g * (ε - m)) := by
      linear_combination (‖u‖ ^ 2 / 2 + ‖v‖ ^ 2 / 2) * hk
    have hr : 0 ≤ (ε * ‖u‖ - g * ‖v‖ / 2) ^ 2 +
        ‖v‖ ^ 2 / 4 * ((g - 2 * ε) ^ 2 + 2 * g * (ε - m)) :=
      add_nonneg (sq_nonneg _) (mul_nonneg (by positivity)
        (add_nonneg (sq_nonneg _) (mul_nonneg (by positivity) (sub_nonneg.mpr hmε))))
    rw [← hid] at hr
    exact (mul_nonneg_iff_of_pos_left (by positivity)).mp hr
  rw [hnorm]
  simp only [add_apply, map_add, inner_add_left, inner_add_right]
  linarith

-- odd-chains Theorem A Step 6 (R2 l.265-267)
/-- **Schur upper bound at a top cluster**: if `A₀ = σ` on `W ≠ 0`, `A₀ ≤ σ − g` on `Wᗮ` and
`‖Eₚ‖ ≤ ε ≤ g/4`, some unit `w ∈ W` has `lamMax (A₀ + Eₚ) ≤ ⟪(A₀ + Eₚ) w, w⟫ + (2/g) ‖Eₚ w‖²`. -/
theorem schur_upper {A₀ Ep : E →L[ℝ] E} (hA : IsSelfAdjoint A₀) (hE : IsSelfAdjoint Ep)
    {W : Submodule ℝ E} (hW0 : W ≠ ⊥) {σ g ε : ℝ} (hW : ∀ u ∈ W, A₀ u = σ • u)
    (hgap : ∀ v ∈ Wᗮ, ⟪A₀ v, v⟫ ≤ (σ - g) * ‖v‖ ^ 2) (hg : 0 < g)
    (hε : ∀ x, ‖Ep x‖ ≤ ε * ‖x‖) (hεg : 4 * ε ≤ g) :
    ∃ w ∈ W, ‖w‖ = 1 ∧ lamMax (A₀ + Ep) ≤ ⟪(A₀ + Ep) w, w⟫ + 2 / g * ‖Ep w‖ ^ 2 := by
  obtain ⟨w₀, hw₀W, hw₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  have : Nontrivial E := ⟨⟨w₀, 0, hw₀⟩⟩
  have hw₀pos : 0 < ‖w₀‖ := norm_pos_iff.mpr hw₀
  have hε0 : 0 ≤ ε := by
    by_contra hneg
    push Not at hneg
    have := mul_neg_of_neg_of_pos hneg hw₀pos
    linarith [hε w₀, norm_nonneg (Ep w₀)]
  have hlow : σ - ε ≤ lamMax (A₀ + Ep) := by
    refine le_lamMax_of hw₀ ?_
    have h1 : ⟪A₀ w₀, w₀⟫ = σ * ‖w₀‖ ^ 2 := by
      rw [hW w₀ hw₀W, real_inner_smul_left, real_inner_self_eq_norm_sq]
    have h2 := (abs_le.mp (abs_inner_le_of_bound hε w₀ w₀)).1
    simp only [add_apply, inner_add_left]
    linarith
  obtain ⟨z, hz0, hAz⟩ := exists_eigen_lamMax (hA.add hE)
  set lam := lamMax (A₀ + Ep) with hlam
  obtain ⟨w, hw, v, hv, rfl⟩ := Submodule.exists_add_mem_mem_orthogonal (K := W) z
  have hwv : ⟪w, v⟫ = 0 := Submodule.inner_right_of_mem_orthogonal hw hv
  have hnorm := norm_add_sq_of_inner_eq_zero hwv
  have hAw : A₀ w = σ • w := hW w hw
  have h2 : ⟪A₀ w, v⟫ = 0 := by rw [hAw, real_inner_smul_left, hwv, mul_zero]
  have h3 : ⟪A₀ v, w⟫ = 0 := by
    have hs := hA.isSymmetric v w
    simp only [ContinuousLinearMap.coe_coe] at hs
    rw [hs, real_inner_comm, h2]
  have h4 : ⟪Ep v, w⟫ = ⟪Ep w, v⟫ := by
    have hs := hE.isSymmetric v w
    simp only [ContinuousLinearMap.coe_coe] at hs
    rw [hs, real_inner_comm]
  have h5 := hgap v hv
  have c1 : ⟪Ep w, v⟫ ≤ ‖Ep w‖ * ‖v‖ := real_inner_le_norm _ _
  have c2 := (abs_le.mp (abs_inner_le_of_bound hε v v)).2
  have e1 : ⟪(A₀ + Ep) (w + v), w + v⟫ = lam * (‖w‖ ^ 2 + ‖v‖ ^ 2) := by
    rw [hAz, real_inner_smul_left, real_inner_self_eq_norm_sq, hnorm]
  have e2 : ⟪(A₀ + Ep) (w + v), w + v⟫ = ⟪(A₀ + Ep) w, w⟫ + ⟪A₀ w, v⟫ + ⟪A₀ v, w⟫ +
      ⟪Ep w, v⟫ + ⟪Ep v, w⟫ + ⟪A₀ v, v⟫ + ⟪Ep v, v⟫ := by
    simp only [add_apply, map_add, inner_add_left, inner_add_right]
    ring
  have hpre : lam * (‖w‖ ^ 2 + ‖v‖ ^ 2) ≤
      ⟪(A₀ + Ep) w, w⟫ + 2 * ‖Ep w‖ * ‖v‖ + (σ - g + ε) * ‖v‖ ^ 2 := by
    linarith
  have hw0 : w ≠ 0 := by
    rintro rfl
    have hv0 : v ≠ 0 := by simpa using hz0
    have hvpos : 0 < ‖v‖ ^ 2 := pow_pos (norm_pos_iff.mpr hv0) 2
    simp only [map_zero, inner_zero_left, norm_zero, zero_add] at hpre
    have := mul_nonneg (sub_nonneg.mpr hlow) hvpos.le
    have := mul_pos (by linarith : (0 : ℝ) < g - 2 * ε) hvpos
    nlinarith
  set c := 2 / g with hcdef
  have hc : c * g = 2 := by rw [hcdef]; exact div_mul_cancel₀ _ hg.ne'
  have hgap2 : (σ - g + ε - lam) * ‖v‖ ^ 2 ≤ -(g / 2) * ‖v‖ ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
  have hsq : 2 * ‖Ep w‖ * ‖v‖ - g / 2 * ‖v‖ ^ 2 ≤ c * ‖Ep w‖ ^ 2 := by
    have hid : c * ‖Ep w‖ ^ 2 - (2 * ‖Ep w‖ * ‖v‖ - g / 2 * ‖v‖ ^ 2) =
        g / 2 * (‖v‖ - c * ‖Ep w‖) ^ 2 := by
      linear_combination (‖Ep w‖ * ‖v‖ - c * ‖Ep w‖ ^ 2 / 2) * hc
    have : 0 ≤ g / 2 * (‖v‖ - c * ‖Ep w‖) ^ 2 := by positivity
    linarith
  have hmain : lam * ‖w‖ ^ 2 ≤ ⟪(A₀ + Ep) w, w⟫ + c * ‖Ep w‖ ^ 2 := by
    nlinarith
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  refine ⟨‖w‖⁻¹ • w, W.smul_mem _ hw, ?_, ?_⟩
  · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hwpos.ne']
  · simp only [map_smul, real_inner_smul_left, real_inner_smul_right, norm_smul, norm_inv,
      norm_norm]
    calc lam = (lam * ‖w‖ ^ 2) * (‖w‖⁻¹) ^ 2 := by field_simp
      _ ≤ (⟪(A₀ + Ep) w, w⟫ + c * ‖Ep w‖ ^ 2) * (‖w‖⁻¹) ^ 2 :=
        mul_le_mul_of_nonneg_right hmain (sq_nonneg _)
      _ = _ := by ring

/-- **Schur lower bound at a bottom cluster**: if `A₀ = −σ` on `W ≠ 0`, `A₀ ≥ −σ + g` on `Wᗮ` and
`‖Eₚ‖ ≤ ε ≤ g/4`, some unit `v ∈ W` has `⟪(A₀ + Eₚ) v, v⟫ − (2/g) ‖Eₚ v‖² ≤ lamMin (A₀ + Eₚ)`. -/
theorem schur_lower_cluster {A₀ Ep : E →L[ℝ] E} (hA : IsSelfAdjoint A₀) (hE : IsSelfAdjoint Ep)
    {W : Submodule ℝ E} (hW0 : W ≠ ⊥) {σ g ε : ℝ} (hW : ∀ u ∈ W, A₀ u = (-σ) • u)
    (hgap : ∀ v ∈ Wᗮ, (-σ + g) * ‖v‖ ^ 2 ≤ ⟪A₀ v, v⟫) (hg : 0 < g)
    (hε : ∀ x, ‖Ep x‖ ≤ ε * ‖x‖) (hεg : 4 * ε ≤ g) :
    ∃ v ∈ W, ‖v‖ = 1 ∧ ⟪(A₀ + Ep) v, v⟫ - 2 / g * ‖Ep v‖ ^ 2 ≤ lamMin (A₀ + Ep) := by
  obtain ⟨v, hvW, hv1, hle⟩ := schur_upper (A₀ := -A₀) (Ep := -Ep) hA.neg hE.neg hW0 (σ := σ)
    (g := g) (ε := ε) (fun u hu => by simp [hW u hu])
    (fun v hv => by
      have := hgap v hv
      simp only [neg_apply, inner_neg_left]
      linarith) hg (fun x => by simpa using hε x) hεg
  refine ⟨v, hvW, hv1, ?_⟩
  rw [lamMin_eq_neg_lamMax_neg]
  have e1 : -(A₀ + Ep) = -A₀ + -Ep := by abel
  rw [e1]
  simp only [add_apply, neg_apply, inner_add_left,
    inner_neg_left, norm_neg] at hle ⊢
  linarith

/-! ### The penalty bound -/

-- merged §2(f)
/-- **Penalty bound**: for `p ∈ W`, `p ≠ 0`, `‖Q‖ ≤ q`, `⟪Q u, u⟫ ≥ μ ‖u‖²` on `W ∩ pᗮ` with
`μ ≤ q`, and `c ‖p‖² > 2q`, every `x ∈ W` has
`⟪Q x, x⟫ + c ⟪p, x⟫² ≥ (μ − q²/(c ‖p‖² − 2q)) ‖x‖²`. -/
theorem penalty_lower {Q : E →L[ℝ] E} {W : Submodule ℝ E} {p : E} (hp : p ∈ W) (hp0 : p ≠ 0)
    {q μ c : ℝ} (hq : ∀ x, ‖Q x‖ ≤ q * ‖x‖)
    (hμ : ∀ u ∈ W, ⟪p, u⟫ = 0 → μ * ‖u‖ ^ 2 ≤ ⟪Q u, u⟫) (hμq : μ ≤ q)
    (hc : 2 * q < c * ‖p‖ ^ 2) {x : E} (hx : x ∈ W) :
    (μ - q ^ 2 / (c * ‖p‖ ^ 2 - 2 * q)) * ‖x‖ ^ 2 ≤ ⟪Q x, x⟫ + c * ⟪p, x⟫ ^ 2 := by
  have hP : 0 < ‖p‖ ^ 2 := pow_pos (norm_pos_iff.mpr hp0) 2
  obtain ⟨s, k, hkW, hpk, rfl⟩ : ∃ s : ℝ, ∃ k ∈ W, ⟪p, k⟫ = 0 ∧ x = k + s • p := by
    refine ⟨⟪p, x⟫ / ‖p‖ ^ 2, x - (⟪p, x⟫ / ‖p‖ ^ 2) • p, W.sub_mem hx (W.smul_mem _ hp), ?_,
      (sub_add_cancel x _).symm⟩
    rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
      div_mul_cancel₀ _ hP.ne', sub_self]
  have hkp : ⟪k, s • p⟫ = 0 := by rw [real_inner_smul_right, real_inner_comm, hpk, mul_zero]
  have hnx : ‖k + s • p‖ ^ 2 = ‖k‖ ^ 2 + s ^ 2 * ‖p‖ ^ 2 := by
    rw [norm_add_sq_of_inner_eq_zero hkp, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have hpx : ⟪p, k + s • p⟫ = s * ‖p‖ ^ 2 := by
    rw [inner_add_right, hpk, real_inner_smul_right, real_inner_self_eq_norm_sq, zero_add]
  have hQx : ⟪Q (k + s • p), k + s • p⟫ =
      ⟪Q k, k⟫ + s * ⟪Q k, p⟫ + s * ⟪Q p, k⟫ + s ^ 2 * ⟪Q p, p⟫ := by
    simp only [map_add, map_smul, inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right]
    ring
  have hk1 := hμ k hkW hpk
  have b1 := abs_inner_le_of_bound hq k p
  have b2 := abs_inner_le_of_bound hq p k
  have b3 := (abs_le.mp (abs_inner_le_of_bound hq p p)).1
  have c1 : -(q * ‖k‖ * (|s| * ‖p‖)) ≤ s * ⟪Q k, p⟫ := by
    have h1 : |s * ⟪Q k, p⟫| ≤ q * ‖k‖ * (|s| * ‖p‖) := by
      rw [abs_mul]
      calc |s| * |⟪Q k, p⟫| ≤ |s| * (q * ‖k‖ * ‖p‖) :=
            mul_le_mul_of_nonneg_left b1 (abs_nonneg s)
        _ = q * ‖k‖ * (|s| * ‖p‖) := by ring
    linarith [neg_abs_le (s * ⟪Q k, p⟫)]
  have c2 : -(q * ‖k‖ * (|s| * ‖p‖)) ≤ s * ⟪Q p, k⟫ := by
    have h1 : |s * ⟪Q p, k⟫| ≤ q * ‖k‖ * (|s| * ‖p‖) := by
      rw [abs_mul]
      calc |s| * |⟪Q p, k⟫| ≤ |s| * (q * ‖p‖ * ‖k‖) :=
            mul_le_mul_of_nonneg_left b2 (abs_nonneg s)
        _ = q * ‖k‖ * (|s| * ‖p‖) := by ring
    linarith [neg_abs_le (s * ⟪Q p, k⟫)]
  have c3 : -(q * (s ^ 2 * ‖p‖ ^ 2)) ≤ s ^ 2 * ⟪Q p, p⟫ := by
    have h2 := mul_le_mul_of_nonneg_left b3 (sq_nonneg s)
    linarith
  have hT2 : (|s| * ‖p‖) ^ 2 = s ^ 2 * ‖p‖ ^ 2 := by rw [mul_pow, sq_abs]
  have hDpos : 0 < c * ‖p‖ ^ 2 - 2 * q := by linarith
  have hr0 : 0 ≤ q ^ 2 / (c * ‖p‖ ^ 2 - 2 * q) := div_nonneg (sq_nonneg q) hDpos.le
  have hrD : q ^ 2 / (c * ‖p‖ ^ 2 - 2 * q) * (c * ‖p‖ ^ 2 - 2 * q) = q ^ 2 :=
    div_mul_cancel₀ _ hDpos.ne'
  set D := c * ‖p‖ ^ 2 - 2 * q with hD
  set r := q ^ 2 / D with hr
  set T := |s| * ‖p‖ with hT
  have key : (μ - r) * (‖k‖ ^ 2 + T ^ 2) ≤
      μ * ‖k‖ ^ 2 - 2 * q * ‖k‖ * T + (c * ‖p‖ ^ 2 - q) * T ^ 2 := by
    have hid : D * (μ * ‖k‖ ^ 2 - 2 * q * ‖k‖ * T + (c * ‖p‖ ^ 2 - q) * T ^ 2 -
        (μ - r) * (‖k‖ ^ 2 + T ^ 2)) = (q * ‖k‖ - D * T) ^ 2 + D * (q - μ + r) * T ^ 2 := by
      linear_combination ‖k‖ ^ 2 * hrD - D * T ^ 2 * hD
    have h0 : 0 ≤ (q * ‖k‖ - D * T) ^ 2 + D * (q - μ + r) * T ^ 2 :=
      add_nonneg (sq_nonneg _)
        (mul_nonneg (mul_nonneg hDpos.le (by linarith)) (sq_nonneg _))
    rw [← hid] at h0
    have := (mul_nonneg_iff_of_pos_left hDpos).mp h0
    linarith
  rw [hT2] at key
  rw [hnx, hQx, hpx]
  linarith

/-! ### Compactness of a unit sphere -/

-- generic (IsCompact.exists_isMinOn on the unit sphere of a subspace)
/-- A function continuous and positive on the unit sphere of a subspace has a positive lower bound
there. -/
theorem exists_pos_le_on_sphere {W : Submodule ℝ E} {f : E → ℝ}
    (hf : ContinuousOn f {w | w ∈ W ∧ ‖w‖ = 1}) (hpos : ∀ w ∈ W, ‖w‖ = 1 → 0 < f w) :
    ∃ c > 0, ∀ w ∈ W, ‖w‖ = 1 → c ≤ f w := by
  have hK : IsCompact {w | w ∈ W ∧ ‖w‖ = 1} := by
    have h1 : {w | w ∈ W ∧ ‖w‖ = 1} = (W : Set E) ∩ Metric.sphere (0 : E) 1 := by
      ext w
      simp
    rw [h1]
    exact (isCompact_sphere (0 : E) 1).inter_left (Submodule.isClosed_of_finiteDimensional W)
  rcases Set.eq_empty_or_nonempty {w | w ∈ W ∧ ‖w‖ = 1} with he | hne
  · refine ⟨1, one_pos, fun w hw h1 => ?_⟩
    have : w ∈ {w | w ∈ W ∧ ‖w‖ = 1} := ⟨hw, h1⟩
    rw [he] at this
    exact this.elim
  obtain ⟨w₀, hw₀, hmin⟩ := hK.exists_isMinOn hne hf
  exact ⟨f w₀, hpos w₀ hw₀.1 hw₀.2, fun w hw h1 => hmin ⟨hw, h1⟩⟩

end Cvs.StepA.Edge.PlanarBoxLemma
