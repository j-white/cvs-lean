import Mathlib
import Cvs.Finite.TruncationQuadraticForm
import Cvs.WeilForm.CouplingSchurComplement

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The f_bulk Schur identity
For symmetric `B ≥ 0` on `D = ker ℓ` and `v_r ∈ R` with `ℓ v_r = c`, `B(v_r, ·) = 0` on `R ∩ D`: the rung
pivot is `min_{R, ℓ = c} B = B(v_r,v_r)` and the full pivot is `B(v_r,v_r) − B(d,d)`, `d` the
representer of `b̃ = B(v_r, ·)|_D`. For a frame of `D` with Gram `G ≻ 0`: `B(d,d) = b̃ᵀG⁻¹b̃`, the Schur
complement of `[[τ, b̃ᵀ], [b̃, G]]`. For `B(x,y) = ⟪Ax, Ay⟫`: `B(d,d) = ‖P A v_r‖² = ‖A v_r‖² cos²∠(A v_r, P A v_r)`.
-/

noncomputable section

open Matrix

namespace Cvs.WeilForm.BulkSchurIdentity

open Cvs.WeilForm.CouplingSchurComplement (apply_add_self)

/-! ### The pivot on a coset -/

section Form

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

/-- **The minimum of a form on a coset**: if `d ∈ D` represents `B(v, ·)` on `D` and `B ≥ 0` on `D`, then
`min_{y ∈ D} B(v + y, v + y) = B(v,v) − B(d,d)`, attained at `y = −d`. -/
theorem isLeast_coset {B : LinearMap.BilinForm ℝ E} (hB : B.IsSymm) {D : Submodule ℝ E} {v d : E}
    (hd : d ∈ D) (hrep : ∀ y ∈ D, B d y = B v y) (hpos : ∀ y ∈ D, 0 ≤ B y y) :
    IsLeast ((fun y => B (v + y) (v + y)) '' D) (B v v - B d d) := by
  have horth : ∀ y ∈ D, B (v - d) y = 0 := fun y hy => by
    rw [map_sub, LinearMap.sub_apply, hrep y hy, sub_self]
  have hval : B (v - d) (v - d) = B v v - B d d := by
    have h1 := hrep d hd
    have h2 := hB.eq d v
    simp only [map_sub, LinearMap.sub_apply]
    linarith
  refine ⟨⟨-d, D.neg_mem hd, by simp only [← sub_eq_add_neg, hval]⟩, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  have hsplit : v + y = (v - d) + (d + y) := by abel
  have hdy : d + y ∈ D := D.add_mem hd hy
  simp only
  rw [hsplit, apply_add_self hB, horth _ hdy, hval]
  linarith [hpos _ hdy]

/-- **The full pivot**: on `ℓ v = c`, with `d ∈ ker ℓ` representing `B(v₀, ·)` there and `B ≥ 0` on
`ker ℓ`, the minimum of `B(v,v)` is `B(v₀,v₀) − B(d,d)`. -/
theorem isLeast_feasible {B : LinearMap.BilinForm ℝ E} (hB : B.IsSymm) (ℓ : E →ₗ[ℝ] F) {c : F}
    {v₀ d : E} (hc : ℓ v₀ = c) (hd : ℓ d = 0) (hrep : ∀ y, ℓ y = 0 → B d y = B v₀ y)
    (hpos : ∀ y, ℓ y = 0 → 0 ≤ B y y) :
    IsLeast {t | ∃ v, ℓ v = c ∧ B v v = t} (B v₀ v₀ - B d d) := by
  have h := isLeast_coset hB (D := LinearMap.ker ℓ) (v := v₀) (LinearMap.mem_ker.mpr hd)
    (fun y hy => hrep y (LinearMap.mem_ker.mp hy)) (fun y hy => hpos y (LinearMap.mem_ker.mp hy))
  refine ⟨?_, fun t ⟨v, hv, ht⟩ => ?_⟩
  · obtain ⟨y, hy, hyt⟩ := h.1
    exact ⟨v₀ + y, by rw [map_add, hc, LinearMap.mem_ker.mp hy, add_zero], hyt⟩
  · have hy : v - v₀ ∈ LinearMap.ker ℓ := by
      rw [LinearMap.mem_ker, map_sub, hv, hc, sub_self]
    have := h.2 ⟨v - v₀, hy, rfl⟩
    simp only [add_sub_cancel] at this
    rw [← ht]; exact this

/-- **The f_bulk identity in form language.** For feasible `v_r ∈ R` with `B(v_r, ·) = 0` on `R ∩ ker ℓ`,
`d ∈ ker ℓ` representing `B(v_r, ·)` there and `B ≥ 0` on `ker ℓ`: the rung pivot is `B(v_r,v_r)`, the full
pivot is `B(v_r,v_r) − B(d,d)`, and `B(d, ·)` vanishes on `R ∩ ker ℓ`. -/
theorem pivot {B : LinearMap.BilinForm ℝ E} (hB : B.IsSymm) (ℓ : E →ₗ[ℝ] F) {c : F}
    {R : Submodule ℝ E} {vr d : E} (hvr : vr ∈ R) (hc : ℓ vr = c)
    (hrung : ∀ y ∈ R, ℓ y = 0 → B vr y = 0) (hd : ℓ d = 0)
    (hrep : ∀ y, ℓ y = 0 → B d y = B vr y) (hpos : ∀ y, ℓ y = 0 → 0 ≤ B y y) :
    IsLeast {t | ∃ v ∈ R, ℓ v = c ∧ B v v = t} (B vr vr)
      ∧ IsLeast {t | ∃ v, ℓ v = c ∧ B v v = t} (B vr vr - B d d)
      ∧ ∀ y ∈ R, ℓ y = 0 → B d y = 0 := by
  refine ⟨⟨⟨vr, hvr, hc, rfl⟩, ?_⟩, isLeast_feasible hB ℓ hc hd hrep hpos,
    fun y hy hy0 => (hrep y hy0).trans (hrung y hy hy0)⟩
  rintro t ⟨v, hvR, hv, rfl⟩
  have h := isLeast_coset hB (D := R ⊓ LinearMap.ker ℓ) (v := vr) (d := 0) (Submodule.zero_mem _)
    (fun y hy => by rw [map_zero, LinearMap.zero_apply, hrung y hy.1 (LinearMap.mem_ker.mp hy.2)])
    (fun y hy => hpos y (LinearMap.mem_ker.mp hy.2))
  have hy : v - vr ∈ R ⊓ LinearMap.ker ℓ :=
    ⟨R.sub_mem hvR hvr, LinearMap.mem_ker.mpr (by rw [map_sub, hv, hc, sub_self])⟩
  have := h.2 ⟨v - vr, hy, rfl⟩
  simp only [add_sub_cancel, map_zero, sub_zero] at this
  exact this

end Form

/-! ### The matrix form: `S22 = τ − b̃ᵀ Q_DD⁻¹ b̃` -/

section Frame

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Gram matrix `Q_DD` of a frame `e`. -/
def gram (B : LinearMap.BilinForm ℝ E) (e : ι → E) : Matrix ι ι ℝ :=
  Matrix.of fun i j => B (e i) (e j)

/-- The coupling vector `b̃ᵢ = B(v, eᵢ)`. -/
def coup (B : LinearMap.BilinForm ℝ E) (e : ι → E) (v : E) : ι → ℝ := fun i => B v (e i)

/-- The representer `d = ∑ᵢ (G⁻¹b̃)ᵢ eᵢ`. -/
def rep (B : LinearMap.BilinForm ℝ E) (e : ι → E) (v : E) : E :=
  ∑ i, ((gram B e)⁻¹ *ᵥ coup B e v) i • e i

omit [DecidableEq ι] in
theorem apply_sum_left (B : LinearMap.BilinForm ℝ E) (e : ι → E) (a : ι → ℝ) (y : E) :
    B (∑ i, a i • e i) y = ∑ i, a i * B (e i) y := by
  simp [map_sum, LinearMap.sum_apply, map_smul]

omit [DecidableEq ι] in
theorem apply_sum_right (B : LinearMap.BilinForm ℝ E) (e : ι → E) (a : ι → ℝ) (x : E) :
    B x (∑ i, a i • e i) = ∑ i, a i * B x (e i) := by
  simp [map_sum, map_smul]

omit [Fintype ι] [DecidableEq ι] in
theorem gram_isHermitian {B : LinearMap.BilinForm ℝ E} (hB : B.IsSymm) (e : ι → E) :
    (gram B e).IsHermitian := by
  ext i j
  simp [gram, hB.eq (e j) (e i)]

/-- `B(d, eⱼ) = b̃ⱼ` for `G` invertible. -/
theorem rep_apply_frame {B : LinearMap.BilinForm ℝ E} (hB : B.IsSymm) (e : ι → E) (v : E)
    (hG : IsUnit (gram B e).det) (j : ι) : B (rep B e v) (e j) = coup B e v j := by
  rw [rep, apply_sum_left]
  have hmul : gram B e *ᵥ ((gram B e)⁻¹ *ᵥ coup B e v) = coup B e v := by
    rw [mulVec_mulVec, mul_nonsing_inv _ hG, one_mulVec]
  have := congrFun hmul j
  rw [← this, mulVec, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [gram, of_apply, hB.eq (e i) (e j)]
  ring

/-- `B(d, y) = B(v, y)` on `span e`. -/
theorem rep_apply {B : LinearMap.BilinForm ℝ E} (hB : B.IsSymm) (e : ι → E) (v : E)
    (hG : IsUnit (gram B e).det) {y : E} (hy : y ∈ Submodule.span ℝ (Set.range e)) :
    B (rep B e v) y = B v y := by
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hy
  rw [apply_sum_right, apply_sum_right]
  exact Finset.sum_congr rfl fun i _ => by rw [rep_apply_frame hB e v hG]; rfl

theorem rep_mem (B : LinearMap.BilinForm ℝ E) (e : ι → E) (v : E) :
    rep B e v ∈ Submodule.span ℝ (Set.range e) :=
  Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- `B(d, d) = b̃ᵀ G⁻¹ b̃`. -/
theorem rep_apply_rep {B : LinearMap.BilinForm ℝ E} (hB : B.IsSymm) (e : ι → E) (v : E)
    (hG : IsUnit (gram B e).det) :
    B (rep B e v) (rep B e v) = coup B e v ⬝ᵥ ((gram B e)⁻¹ *ᵥ coup B e v) := by
  rw [rep_apply hB e v hG (rep_mem B e v), rep, apply_sum_right, dotProduct]
  exact Finset.sum_congr rfl fun i _ => by rw [mul_comm]; rfl

omit [DecidableEq ι] in
/-- `B(∑ aᵢeᵢ, ∑ aᵢeᵢ) = aᵀGa`. -/
theorem apply_sum_sum (B : LinearMap.BilinForm ℝ E) (e : ι → E) (a : ι → ℝ) :
    B (∑ i, a i • e i) (∑ i, a i • e i) = a ⬝ᵥ (gram B e *ᵥ a) := by
  rw [apply_sum_left, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [apply_sum_right, mulVec, dotProduct]
  simp only [gram, of_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

omit [DecidableEq ι] in
/-- `G ⪰ 0` gives `B ≥ 0` on `span e`. -/
theorem nonneg_of_posSemidef {B : LinearMap.BilinForm ℝ E} (e : ι → E)
    (hG : (gram B e).PosSemidef) {y : E} (hy : y ∈ Submodule.span ℝ (Set.range e)) : 0 ≤ B y y := by
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hy
  rw [apply_sum_sum]
  simpa using hG.dotProduct_mulVec_nonneg a

/-- **The f_bulk Schur identity.** `v_r ∈ R` feasible, `B(v_r, ·) = 0` on `R ∩ ker ℓ`, and `e` a frame of
`ker ℓ` with Gram `G = Q_DD ≻ 0`. With `τ = B(v_r,v_r)`, `b̃ = (B(v_r, eᵢ))ᵢ`: the rung pivot is `τ`, the full
pivot is `S = τ − b̃ᵀG⁻¹b̃`, `b̃` vanishes on frame vectors in `R`, and `1 − S/τ = b̃ᵀG⁻¹b̃/τ` for `τ ≠ 0`. -/
theorem pivot_schur {B : LinearMap.BilinForm ℝ E} (hB : B.IsSymm) (ℓ : E →ₗ[ℝ] F) {c : F}
    {R : Submodule ℝ E} {vr : E} (hvr : vr ∈ R) (hc : ℓ vr = c)
    (hrung : ∀ y ∈ R, ℓ y = 0 → B vr y = 0) (e : ι → E)
    (he : Submodule.span ℝ (Set.range e) = LinearMap.ker ℓ) (hG : (gram B e).PosDef) :
    IsLeast {t | ∃ v ∈ R, ℓ v = c ∧ B v v = t} (B vr vr)
      ∧ IsLeast {t | ∃ v, ℓ v = c ∧ B v v = t}
          (B vr vr - coup B e vr ⬝ᵥ ((gram B e)⁻¹ *ᵥ coup B e vr))
      ∧ (∀ i, e i ∈ R → coup B e vr i = 0)
      ∧ (B vr vr ≠ 0 → 1 - (B vr vr - coup B e vr ⬝ᵥ ((gram B e)⁻¹ *ᵥ coup B e vr)) / B vr vr
          = coup B e vr ⬝ᵥ ((gram B e)⁻¹ *ᵥ coup B e vr) / B vr vr) := by
  have hdet : IsUnit (gram B e).det := (Matrix.isUnit_iff_isUnit_det _).mp hG.isUnit
  have hker : ∀ y, ℓ y = 0 → y ∈ Submodule.span ℝ (Set.range e) := fun y hy => by
    rw [he]; exact LinearMap.mem_ker.mpr hy
  have hd : ℓ (rep B e vr) = 0 := by
    have := rep_mem B e vr
    rw [he] at this; exact LinearMap.mem_ker.mp this
  have heℓ : ∀ i, ℓ (e i) = 0 := fun i => by
    have : e i ∈ Submodule.span ℝ (Set.range e) := Submodule.subset_span ⟨i, rfl⟩
    rw [he] at this; exact LinearMap.mem_ker.mp this
  obtain ⟨h1, h2, -⟩ := pivot hB ℓ hvr hc hrung hd (fun y hy => rep_apply hB e vr hdet (hker y hy))
    (fun y hy => nonneg_of_posSemidef e hG.posSemidef (hker y hy))
  rw [rep_apply_rep hB e vr hdet] at h2
  refine ⟨h1, h2, fun i hi => hrung _ hi (heℓ i), fun hτ => ?_⟩
  field_simp
  ring

/-- **The pivot as a Schur complement**: `det [[τ, b̃ᵀ], [b̃, G]] = det G · (τ − b̃ᵀG⁻¹b̃)`. -/
theorem det_pivot {G : Matrix ι ι ℝ} (hdet : IsUnit G.det) (τ : ℝ) (b : ι → ℝ) :
    (fromBlocks (Matrix.of fun _ _ : Unit => τ) (Matrix.replicateRow Unit b)
        (Matrix.replicateCol Unit b) G).det = G.det * (τ - b ⬝ᵥ (G⁻¹ *ᵥ b)) := by
  let _ : Invertible G := invertibleOfIsUnitDet G hdet
  rw [det_fromBlocks₂₂, invOf_eq_nonsing_inv]
  congr 1
  rw [Matrix.det_unique]
  simp only [Matrix.sub_apply, of_apply, Matrix.mul_apply, replicateRow_apply, replicateCol_apply]
  rw [dotProduct_mulVec]
  simp [dotProduct, vecMul]

end Frame

/-! ### The sampling form: `1 − f_bulk = cos²∠(A v_r, A D)` -/

section Sampling

variable {E F V : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

open scoped InnerProductSpace
open InnerProductGeometry

/-- `⟪y, P y⟫ = ‖P y‖²`. -/
theorem inner_starProjection_self (K : Submodule ℝ V) [K.HasOrthogonalProjection] (y : V) :
    ⟪y, K.starProjection y⟫_ℝ = ‖K.starProjection y‖ ^ 2 := by
  have := K.starProjection_inner_eq_zero y (K.starProjection y) (K.starProjection_apply_mem y)
  rw [inner_sub_left, sub_eq_zero] at this
  rw [this, real_inner_self_eq_norm_sq]

/-- `‖P y‖ = ‖y‖ cos∠(y, P y)`. -/
theorem norm_starProjection_eq (K : Submodule ℝ V) [K.HasOrthogonalProjection] (y : V) :
    ‖K.starProjection y‖ = ‖y‖ * Real.cos (angle y (K.starProjection y)) := by
  rw [cos_angle, inner_starProjection_self]
  by_cases hy : ‖y‖ = 0
  · rw [norm_eq_zero.mp hy, map_zero, norm_zero, zero_mul]
  by_cases hp : ‖K.starProjection y‖ = 0
  · rw [hp]; simp
  field_simp

/-- **`P y` is the closest direction in `K`**: `cos²∠(y, z) ≤ cos²∠(y, P y)` for every `z ∈ K`. -/
theorem cos_sq_angle_le (K : Submodule ℝ V) [K.HasOrthogonalProjection] (y : V) {z : V}
    (hz : z ∈ K) : Real.cos (angle y z) ^ 2 ≤ Real.cos (angle y (K.starProjection y)) ^ 2 := by
  have hyz : ⟪y, z⟫_ℝ = ⟪K.starProjection y, z⟫_ℝ := by
    have := K.starProjection_inner_eq_zero y z hz
    rw [inner_sub_left, sub_eq_zero] at this; exact this
  by_cases hy : ‖y‖ = 0
  · rw [norm_eq_zero.mp hy]; simp
  have hy0 : 0 < ‖y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hy)
  have hP : Real.cos (angle y (K.starProjection y)) = ‖K.starProjection y‖ / ‖y‖ := by
    rw [norm_starProjection_eq K y]; field_simp
  rw [hP, cos_angle, hyz, div_pow, div_pow, mul_pow]
  by_cases hz0 : ‖z‖ = 0
  · rw [hz0]; simp; positivity
  have hcs := abs_real_inner_le_norm (K.starProjection y) z
  have hsq : ⟪K.starProjection y, z⟫_ℝ ^ 2 ≤ (‖K.starProjection y‖ * ‖z‖) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hcs 2
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [sq_nonneg ‖y‖, sq_nonneg ‖z‖]

/-- **The f_bulk identity in sampling form.** For a Gram form `B(x,y) = ⟪Ax, Ay⟫` and `P` the orthogonal
projection onto `A(ker ℓ)`, the pivot on `ℓ v = c` is `S = ‖A v₀‖² − ‖P A v₀‖²`, and
`1 − S/‖A v₀‖² = cos²∠(A v₀, P A v₀)` for `A v₀ ≠ 0`. -/
theorem pivot_gram {B : LinearMap.BilinForm ℝ E} (A : E →ₗ[ℝ] V) (hBA : ∀ x y, B x y = ⟪A x, A y⟫_ℝ)
    (ℓ : E →ₗ[ℝ] F) {c : F} {v₀ : E} (hc : ℓ v₀ = c)
    [((LinearMap.ker ℓ).map A).HasOrthogonalProjection] :
    IsLeast {t | ∃ v, ℓ v = c ∧ B v v = t}
        (‖A v₀‖ ^ 2 - ‖((LinearMap.ker ℓ).map A).starProjection (A v₀)‖ ^ 2)
      ∧ (A v₀ ≠ 0 → 1 - (‖A v₀‖ ^ 2 - ‖((LinearMap.ker ℓ).map A).starProjection (A v₀)‖ ^ 2)
          / ‖A v₀‖ ^ 2
          = Real.cos (angle (A v₀) (((LinearMap.ker ℓ).map A).starProjection (A v₀))) ^ 2) := by
  set K := (LinearMap.ker ℓ).map A with hK
  have hB : B.IsSymm := ⟨fun x y => by rw [hBA, hBA, real_inner_comm]⟩
  obtain ⟨d, hd, hdP⟩ := Submodule.mem_map.mp (K.starProjection_apply_mem (A v₀))
  have hrep : ∀ y, ℓ y = 0 → B d y = B v₀ y := fun y hy => by
    have hAy : A y ∈ K := Submodule.mem_map_of_mem (LinearMap.mem_ker.mpr hy)
    have := K.starProjection_inner_eq_zero (A v₀) (A y) hAy
    rw [inner_sub_left, sub_eq_zero] at this
    rw [hBA, hBA, hdP, this]
  have h := isLeast_feasible hB ℓ hc (LinearMap.mem_ker.mp hd) hrep
    (fun y _ => by rw [hBA]; exact real_inner_self_nonneg)
  rw [hBA, hBA, hdP, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  refine ⟨h, fun hy => ?_⟩
  have hy0 : ‖A v₀‖ ≠ 0 := norm_ne_zero_iff.mpr hy
  rw [norm_starProjection_eq K (A v₀)]
  field_simp
  ring

end Sampling

/-! ### On the CvS window matrix -/

section Window

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable {F : Type*} [AddCommGroup F] [Module ℝ F]

/-- The window form `B(x, y) = x ⬝ (M y)` with `M = Cvs.Finite.TruncationQuadraticForm.M`. -/
abbrev Bw (P R : ℕ) (L : ℝ) (mode : ι → ℤ) : LinearMap.BilinForm ℝ (ι → ℝ) :=
  Matrix.toBilin' (Cvs.Finite.TruncationQuadraticForm.M P R L mode)

theorem Bw_isSymm {L : ℝ} (hL : 0 < L) (P R : ℕ) {mode : ι → ℤ} (hinj : Function.Injective mode) :
    (Bw P R L mode).IsSymm := by
  refine ⟨fun x y => ?_⟩
  rw [Matrix.toBilin'_apply', Matrix.toBilin'_apply', dotProduct_mulVec, ← mulVec_transpose,
    dotProduct_comm]
  congr 2
  ext i j
  exact Cvs.Finite.TruncationQuadraticForm.M_symm hL P R hinj j i

/-- **The f_bulk Schur identity on the CvS window matrix** (no hypothesis on the zeros): for constraints
`ℓ`, a rung span `Rg`, the rung minimiser `v_r` and a frame `e` of `ker ℓ` with `Q_DD ≻ 0`, the pivot of
`ξ ⬝ (Mξ)` on `ℓ ξ = c` is `τ − b̃ᵀQ_DD⁻¹b̃`, and the rung pivot is `τ = v_r ⬝ (M v_r)`. -/
theorem pivot_schur_window {L : ℝ} (hL : 0 < L) (P R : ℕ) {mode : ι → ℤ}
    (hinj : Function.Injective mode) (ℓ : (ι → ℝ) →ₗ[ℝ] F) {c : F} {Rg : Submodule ℝ (ι → ℝ)}
    {vr : ι → ℝ} (hvr : vr ∈ Rg) (hc : ℓ vr = c)
    (hrung : ∀ y ∈ Rg, ℓ y = 0 → vr ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L mode *ᵥ y) = 0)
    (e : κ → ι → ℝ)
    (he : Submodule.span ℝ (Set.range e) = LinearMap.ker ℓ) (hG : (gram (Bw P R L mode) e).PosDef) :
    IsLeast {t | ∃ v ∈ Rg, ℓ v = c ∧ v ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L mode *ᵥ v) = t}
        (vr ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L mode *ᵥ vr))
      ∧ IsLeast {t | ∃ v, ℓ v = c ∧ v ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L mode *ᵥ v) = t}
          (vr ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L mode *ᵥ vr)
            - coup (Bw P R L mode) e vr ⬝ᵥ ((gram (Bw P R L mode) e)⁻¹ *ᵥ coup (Bw P R L mode) e vr)) := by
  have h := pivot_schur (Bw_isSymm hL P R hinj) ℓ hvr hc
    (fun y hy hy0 => by rw [Matrix.toBilin'_apply']; exact hrung y hy hy0) e he hG
  simp only [Matrix.toBilin'_apply'] at h
  exact ⟨h.1, h.2.1⟩

end Window

end Cvs.WeilForm.BulkSchurIdentity
