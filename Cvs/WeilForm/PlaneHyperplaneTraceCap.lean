import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# A plane meets a hyperplane, and the trace caps the second value

    `M e ≥ a`,  `M u + M v ≤ T` on orthonormal pairs   ⟹   every plane carries `v` with
    `M v ≤ (T − a)‖v‖²`

which is the second-eigenvalue bound with no spectral theory in it.
-/

noncomputable section

namespace Cvs.WeilForm.PlaneHyperplaneTraceCap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **A plane meets a hyperplane.**  One linear condition cannot cut a two-dimensional space
to zero. -/
theorem exists_mem_orthogonal {V : Submodule ℝ E} (hV : Module.finrank ℝ V = 2) (e : E) :
    ∃ v : E, v ∈ V ∧ v ≠ 0 ∧ (inner ℝ e v : ℝ) = 0 := by
  classical
  haveI : FiniteDimensional ℝ (V : Submodule ℝ E) :=
    FiniteDimensional.of_finrank_pos (by rw [hV]; norm_num)
  let φ : V →ₗ[ℝ] ℝ :=
    { toFun := fun v => (inner ℝ e (v : E) : ℝ)
      map_add' := by intro x y; simp [inner_add_right]
      map_smul' := by intro c x; simp [real_inner_smul_right] }
  have hrange : Module.finrank ℝ (LinearMap.range φ) ≤ 1 := by
    have := Submodule.finrank_le (LinearMap.range φ)
    simpa using this
  have hrk := LinearMap.finrank_range_add_finrank_ker φ
  rw [hV] at hrk
  have hker : 1 ≤ Module.finrank ℝ (LinearMap.ker φ) := by omega
  have hne : LinearMap.ker φ ≠ ⊥ := by
    intro h
    rw [h] at hker
    simp at hker
  obtain ⟨w, hwmem, hwne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  refine ⟨(w : E), w.2, ?_, LinearMap.mem_ker.mp hwmem⟩
  intro h
  exact hwne (Subtype.ext h)

/-- **The trace caps the second value.**  With a unit vector already carrying `a`, every plane
carries a vector whose value is at most `T − a`. -/
theorem plane_bound_of_trace {M : E → ℝ} {T a : ℝ}
    (hpair : ∀ u v : E, ‖u‖ = 1 → ‖v‖ = 1 → (inner ℝ u v : ℝ) = 0 → M u + M v ≤ T)
    {e : E} (he1 : ‖e‖ = 1) (hea : a ≤ M e)
    (hsmul : ∀ (c : ℝ) (x : E), M (c • x) = c ^ 2 * M x)
    {V : Submodule ℝ E} (hV : Module.finrank ℝ V = 2) :
    ∃ v : E, v ∈ V ∧ v ≠ 0 ∧ M v ≤ (T - a) * ‖v‖ ^ 2 := by
  obtain ⟨v, hvV, hv0, horth⟩ := exists_mem_orthogonal hV e
  have hvn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv0
  have hunit : ‖(‖v‖)⁻¹ • v‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hvn]
  have horth' : (inner ℝ e ((‖v‖)⁻¹ • v) : ℝ) = 0 := by
    rw [real_inner_smul_right, horth, mul_zero]
  have hbound := hpair e ((‖v‖)⁻¹ • v) he1 hunit horth'
  rw [hsmul] at hbound
  refine ⟨v, hvV, hv0, ?_⟩
  have hpos : 0 < ‖v‖ ^ 2 := by positivity
  have hinv : ((‖v‖)⁻¹) ^ 2 * M v ≤ T - a := by linarith
  rw [inv_pow, inv_mul_le_iff₀ hpos] at hinv
  linarith

/-! ### The even sector's plane bound, assembled -/

/-- **The capping bound on a plane.**  `Q = A₀‖·‖² + D + pole` with the pole nonnegative, `D`
capped below by `λ*(‖·‖² − M)`, and `M` controlled by its trace: every plane then carries a
vector on which `Q` is at least `A₀ + λ*(1 − (T − a))` times the norm squared. -/
theorem even_plane_bound {Q D M pole : E → ℝ} {A0 lamstar T a : ℝ} {e : E}
    (hQ : ∀ v : E, Q v = A0 * ‖v‖ ^ 2 + D v + pole v)
    (hpole : ∀ v : E, 0 ≤ pole v)
    (hcap : ∀ v : E, lamstar * (‖v‖ ^ 2 - M v) ≤ D v)
    (hlam : 0 ≤ lamstar)
    (hpair : ∀ u v : E, ‖u‖ = 1 → ‖v‖ = 1 → (inner ℝ u v : ℝ) = 0 → M u + M v ≤ T)
    (he1 : ‖e‖ = 1) (hea : a ≤ M e)
    (hsmul : ∀ (c : ℝ) (x : E), M (c • x) = c ^ 2 * M x)
    {V : Submodule ℝ E} (hV : Module.finrank ℝ V = 2) :
    ∃ v : E, v ∈ V ∧ v ≠ 0 ∧
      (A0 + lamstar * (1 - (T - a))) * ‖v‖ ^ 2 ≤ Q v := by
  obtain ⟨v, hvV, hv0, hMv⟩ := plane_bound_of_trace hpair he1 hea hsmul hV
  refine ⟨v, hvV, hv0, ?_⟩
  have h1 : lamstar * (‖v‖ ^ 2 - (T - a) * ‖v‖ ^ 2) ≤ lamstar * (‖v‖ ^ 2 - M v) :=
    mul_le_mul_of_nonneg_left (by linarith) hlam
  have h2 := hcap v
  have h3 := hpole v
  rw [hQ v]
  nlinarith [h1, h2, h3]

end Cvs.WeilForm.PlaneHyperplaneTraceCap
