import Mathlib
import Cvs.Approximant.CosineColumnTailPairing
import Cvs.Approximant.SpineSubspace
import Cvs.Finite.EvenBulkModeMatrices
import Cvs.Finite.EvenCosineVectorEmbedding
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationQuadraticForm
import Cvs.Route.EvenHyperplaneFloorCompress
import Cvs.Route.EvenWindowBulkCoupling
import Cvs.Route.GroundRouteJointGap
import Cvs.Route.L1FloorFromBulkD0
import Cvs.Upstream.ConstrainedFormPivotChain
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.InfimumAttainedSphere
import Cvs.WeilForm.WeilFormOnWindowL2

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The floor sandwich for the even bulk floor at each truncation

At truncation `N` the even sector is `Cvs.Route.GroundRouteJointGap.evenSub N` (the cosine coordinates of `Cvs.Upstream.ConstrainedFormPivotChain.cosQ`), the form is
`Cvs.Route.GroundRouteJointGap.Meven` and `R₁(N)` is the span of the `N`-truncated rows of `Cvs.L2a.EvenSectorReflectionBound.R1`. `Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x b` forces
`b ≤ λ_r(N) ≤ λ_{#SF x}(N)`, antitone in `N`, and follows from `b ≤ λ_r − (λ_r − λ₀) sin²Θ_r(N)` for some `r ≤ N`
at all large `N`; that condition holds at every `r` once `λ₀(N) ≥ 0`, i.e. under even window positivity.
-/

noncomputable section

open Module Submodule Matrix
open scoped InnerProductSpace

namespace Cvs.Route.EvenBulkFloorSandwich
open Cvs.ZeroCounting

open Cvs.Finite.SymmetricModeSet (Idx mode negI negI_involutive)
open Cvs.Route.L1FloorFromBulkD0 (rung)
open Cvs.Route.GroundRouteJointGap (evenSub Meven isSymmetric_Meven inner_evenSub norm_sq_evenSub ofLp_Meven evenPart_dotProduct)
open Cvs.Upstream.ConstrainedFormPivotChain (ofCos toCos ofCos_even ofCos_toCos)
open Filter Topology

/-! ### The even sector in cosine coordinates -/

theorem ofCos_add (N : ℕ) (a b : Fin (N + 1) → ℝ) : ofCos N (a + b) = ofCos N a + ofCos N b := by
  funext i; rcases i with _ | ⟨k, s⟩ <;> rfl

theorem ofCos_smul (N : ℕ) (c : ℝ) (a : Fin (N + 1) → ℝ) : ofCos N (c • a) = c • ofCos N a := by
  funext i; rcases i with _ | ⟨k, s⟩ <;> rfl

theorem toCos_ofCos (N : ℕ) (a : Fin (N + 1) → ℝ) : toCos N (ofCos N a) = a := by
  funext m; refine Fin.cases rfl (fun k => rfl) m

/-- The even sector is the space of cosine coordinates: `a ↦ ofCos N a`. -/
def cosEquiv (N : ℕ) : (Fin (N + 1) → ℝ) ≃ₗ[ℝ] evenSub N where
  toFun a := ⟨WithLp.toLp 2 (ofCos N a), ofCos_even N a⟩
  map_add' a b := Subtype.ext (by simp [ofCos_add])
  map_smul' c a := Subtype.ext (by simp [ofCos_smul])
  invFun f := toCos N (WithLp.ofLp (f : EuclideanSpace ℝ (Idx N)))
  left_inv a := toCos_ofCos N a
  right_inv f := Subtype.ext (WithLp.ofLp_injective 2 (ofCos_toCos f.2))

/-! ### The rung span -/

/-- The even part of the mode coefficients of rung `j`, as an even vector. -/
def rungVec (x N : ℕ) (j : Cvs.Approximant.SpineSubspace.SF x) : evenSub N :=
  ⟨WithLp.toLp 2 (Cvs.Finite.TruncationQuadraticForm.evenPart (negI N)
      (Cvs.Route.EvenHyperplaneFloorCompress.normalCoeff (Real.log_natCast_nonneg x) (rung x j) (mode N))),
    Cvs.Finite.TruncationQuadraticForm.evenPart_even (negI_involutive N) _⟩

/-- The span of the even parts of the `N`-truncated rung rows, so `f ∈ R₁(N)ᗮ` iff `modeMap f ⊥ Cvs.L2a.EvenSectorReflectionBound.R1 x`
(`Cvs.Finite.EvenBulkModeMatrices.modeMap_mem_orthogonal_span_iff`). -/
def R1N (x N : ℕ) : Submodule ℝ (evenSub N) := span ℝ (Set.range (rungVec x N))

theorem inner_rungVec (x N : ℕ) (j : Cvs.Approximant.SpineSubspace.SF x) (f : evenSub N) :
    ⟪rungVec x N j, f⟫_ℝ = Cvs.Route.EvenHyperplaneFloorCompress.normalCoeff (Real.log_natCast_nonneg x) (rung x j) (mode N)
      ⬝ᵥ WithLp.ofLp (f : EuclideanSpace ℝ (Idx N)) := by
  rw [inner_evenSub]
  exact evenPart_dotProduct (negI_involutive N) _ f.2

/-- `f ∈ R₁(N)ᗮ` iff `f` is orthogonal to every rung row. -/
theorem mem_R1N_orthogonal {x N : ℕ} {f : evenSub N} :
    f ∈ (R1N x N)ᗮ ↔ ∀ j : Cvs.Approximant.SpineSubspace.SF x,
      Cvs.Route.EvenHyperplaneFloorCompress.normalCoeff (Real.log_natCast_nonneg x) (rung x j) (mode N)
        ⬝ᵥ WithLp.ofLp (f : EuclideanSpace ℝ (Idx N)) = 0 := by
  constructor
  · intro hf j
    rw [← inner_rungVec]
    exact inner_right_of_mem_orthogonal (K := R1N x N) (subset_span (Set.mem_range_self j)) hf
  · intro h
    refine (mem_orthogonal _ _).mpr fun u hu => ?_
    have hle : R1N x N ≤ (ℝ ∙ f)ᗮ := by
      refine span_le.mpr ?_
      rintro _ ⟨j, rfl⟩
      exact mem_orthogonal_singleton_iff_inner_right.mpr (by rw [real_inner_comm, inner_rungVec]; exact h j)
    rw [real_inner_comm]
    exact mem_orthogonal_singleton_iff_inner_right.mp (hle hu)

/-! ### The form at truncation `N` -/

section Form

variable {x : ℕ} (hx1 : (1 : ℝ) < x)

/-- The even window form at truncation `N` as a symmetric operator on the even sector. -/
abbrev formN (N : ℕ) : evenSub N →ₗ[ℝ] evenSub N := Meven x (Nat.clog 2 x) (Real.log_pos hx1) N

theorem isSymmetric_formN (N : ℕ) : (formN hx1 N).IsSymmetric := isSymmetric_Meven _ _ _ N

/-- **The even bulk floor is the floor of `T N` on `R₁(N)ᗮ` at every truncation.** -/
theorem evenBulkFloor_iff_trunc (b : ℝ) :
    Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x b ↔ ∀ N, ∀ f ∈ (R1N x N)ᗮ, b * ‖f‖ ^ 2 ≤ ⟪formN hx1 N f, f⟫_ℝ := by
  rw [Cvs.Finite.EvenBulkModeMatrices.evenBulkFloor_iff_matrix hx1]
  refine forall_congr' fun N => ⟨fun h f hf => ?_, fun h f hfe hc => ?_⟩
  · have := h _ f.2 (mem_R1N_orthogonal.mp hf)
    rw [norm_sq_evenSub, inner_evenSub, ofLp_Meven]
    exact this.trans_eq (dotProduct_comm _ _)
  · have := h ⟨WithLp.toLp 2 f, hfe⟩ (mem_R1N_orthogonal.mpr hc)
    rw [norm_sq_evenSub, inner_evenSub, ofLp_Meven] at this
    exact this.trans_eq (dotProduct_comm _ _)

/-! ### Window positivity is `λ₀(N) ≥ 0` -/

/-! ### Raising the truncation -/

theorem embed_add (N J : ℕ) (f g : Idx N → ℝ) :
    Cvs.Finite.EvenCosineVectorEmbedding.embed N J (f + g) = Cvs.Finite.EvenCosineVectorEmbedding.embed N J f + Cvs.Finite.EvenCosineVectorEmbedding.embed N J g := by
  funext i
  rcases i with _ | ⟨k, b⟩
  · simp [Cvs.Finite.EvenCosineVectorEmbedding.embed_none]
  · simp only [Cvs.Finite.EvenCosineVectorEmbedding.embed_some, Pi.add_apply, Cvs.Finite.EvenCosineVectorEmbedding.positiveCoef]
    split_ifs <;> simp

theorem embed_smul (N J : ℕ) (c : ℝ) (f : Idx N → ℝ) :
    Cvs.Finite.EvenCosineVectorEmbedding.embed N J (c • f) = c • Cvs.Finite.EvenCosineVectorEmbedding.embed N J f := by
  funext i
  rcases i with _ | ⟨k, b⟩
  · simp [Cvs.Finite.EvenCosineVectorEmbedding.embed_none]
  · simp only [Cvs.Finite.EvenCosineVectorEmbedding.embed_some, Pi.smul_apply, Cvs.Finite.EvenCosineVectorEmbedding.positiveCoef]
    split_ifs <;> simp

/-- The embedding of the even sector at order `N` into order `J` by retained cosine coefficients. -/
def embV (N J : ℕ) : evenSub N →ₗ[ℝ] evenSub J where
  toFun f := ⟨WithLp.toLp 2 (Cvs.Finite.EvenCosineVectorEmbedding.embed N J (WithLp.ofLp (f : EuclideanSpace ℝ (Idx N)))),
    Cvs.Finite.EvenCosineVectorEmbedding.embed_even N J _⟩
  map_add' f g := Subtype.ext (by simp [embed_add])
  map_smul' c f := Subtype.ext (by simp [embed_smul])

theorem ofLp_embV (N J : ℕ) (f : evenSub N) :
    WithLp.ofLp ((embV N J f : evenSub J) : EuclideanSpace ℝ (Idx J))
      = Cvs.Finite.EvenCosineVectorEmbedding.embed N J (WithLp.ofLp (f : EuclideanSpace ℝ (Idx N))) := rfl

theorem norm_embV {N J : ℕ} (hNJ : N ≤ J) (f : evenSub N) : ‖embV N J f‖ ^ 2 = ‖f‖ ^ 2 := by
  rw [norm_sq_evenSub, norm_sq_evenSub, ofLp_embV]
  simpa [dotProduct, sq] using Cvs.Finite.EvenCosineVectorEmbedding.sum_embed_sq hNJ _ f.2

theorem inner_formN_embV {N J : ℕ} (hNJ : N ≤ J) (f : evenSub N) :
    ⟪formN hx1 J (embV N J f), embV N J f⟫_ℝ = ⟪formN hx1 N f, f⟫_ℝ := by
  have hx0 : (0 : ℝ) < x := zero_lt_one.trans hx1
  rw [inner_evenSub, inner_evenSub, ofLp_Meven, ofLp_Meven, ofLp_embV, dotProduct_comm,
    dotProduct_comm (Cvs.Finite.TruncationQuadraticForm.M _ _ _ _ *ᵥ _)]
  have hJ := Cvs.Approximant.CosineColumnTailPairing.Q_modeMap hx0 hx1 x (Nat.clog 2 x) J
    (Cvs.Finite.EvenCosineVectorEmbedding.embed N J (WithLp.ofLp (f : EuclideanSpace ℝ (Idx N)))) (Cvs.Finite.EvenCosineVectorEmbedding.embed_even N J _)
  have hN := Cvs.Approximant.CosineColumnTailPairing.Q_modeMap hx0 hx1 x (Nat.clog 2 x) N (WithLp.ofLp (f : EuclideanSpace ℝ (Idx N))) f.2
  rw [Cvs.Finite.EvenCosineVectorEmbedding.modeMap_embed hx0 hNJ _ f.2, hN] at hJ
  exact (mul_left_cancel₀ (Real.log_pos hx1).ne' hJ).symm

include hx1 in
theorem embV_mem_R1N_orthogonal {N J : ℕ} (hNJ : N ≤ J) {f : evenSub N} (hf : f ∈ (R1N x N)ᗮ) :
    embV N J f ∈ (R1N x J)ᗮ := by
  have hx0 : (0 : ℝ) < x := zero_lt_one.trans hx1
  rw [mem_R1N_orthogonal] at hf ⊢
  rw [ofLp_embV]
  have h1 := (Cvs.Finite.EvenBulkModeMatrices.modeMap_mem_orthogonal_span_iff hx0 N _ (rung x)).mpr hf
  rw [← Cvs.Finite.EvenCosineVectorEmbedding.modeMap_embed hx0 hNJ _ f.2] at h1
  exact (Cvs.Finite.EvenBulkModeMatrices.modeMap_mem_orthogonal_span_iff hx0 J _ (rung x)).mp h1

/-- **The floor at order `J` restricts to every order `N ≤ J`.** -/
theorem floorN_anti {N J : ℕ} (hNJ : N ≤ J) {b : ℝ}
    (h : ∀ f ∈ (R1N x J)ᗮ, b * ‖f‖ ^ 2 ≤ ⟪formN hx1 J f, f⟫_ℝ) :
    ∀ f ∈ (R1N x N)ᗮ, b * ‖f‖ ^ 2 ≤ ⟪formN hx1 N f, f⟫_ℝ := fun f hf => by
  have := h _ (embV_mem_R1N_orthogonal hx1 hNJ hf)
  rwa [norm_embV hNJ, inner_formN_embV hx1 hNJ] at this

/-- **The even bulk floor is the floor of `formN N` on `R₁(N)ᗮ` at all large `N`.** -/
theorem evenBulkFloor_iff_eventually (b : ℝ) :
    Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x b ↔ ∀ᶠ N in atTop, ∀ f ∈ (R1N x N)ᗮ, b * ‖f‖ ^ 2 ≤ ⟪formN hx1 N f, f⟫_ℝ := by
  rw [evenBulkFloor_iff_trunc hx1]
  refine ⟨fun h => Eventually.of_forall h, fun h N => ?_⟩
  obtain ⟨J, hJ⟩ := eventually_atTop.1 h
  exact floorN_anti hx1 (le_max_left N J) (hJ _ (le_max_right N J))

/-! ### The eigenvalues in `N` -/

/-! ### The angle from the eigenvectors -/

end Form

end Cvs.Route.EvenBulkFloorSandwich
