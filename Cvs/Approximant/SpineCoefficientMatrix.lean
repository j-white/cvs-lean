import Mathlib
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.Approximant.SpineFloorFormDomain
import Cvs.Approximant.SpineSubspace
import Cvs.L2a.SpineProfileWindowNormPos
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Route.L1FloorFromBulkD0
import Cvs.WeilForm.BulkSchurIdentity
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.InfimumAttainedSphere
import Cvs.WeilForm.SymmetricBilinearForm
import Cvs.WeilForm.ThetaSpaceParseval
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.Xi.EImageWindowPoisson
import Cvs.Xi.WindowImageMellinClosed

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The spine form as a coefficient matrix, and its zero side as a form in `u_s(a)`

The spine form `B(a, b) = Q(spineMap x a, spineMap x b)` on `SF x → ℝ` has Gram matrix `spineGram x`
with `aᵀ(spineGram x)a = Q(spineMap x a)`. With `u_s(a) = M[k_{G_a}](s) = Σ_j a_j u_s(e_j)` and
`u_{s̄}(a) = conj u_s(a)`: for `80 ≤ 2πx`, `Q(spineMap x a) = Σ_ρ m_ρ Re(u_{1−ρ}(a) u_ρ(a))`, summable;
`spineMap x` is injective, so negative definite subspaces of `Q` in `R_F` and of `spineGram x` correspond.
-/

noncomputable section

open MeasureTheory Real Set Complex Matrix Module ComplexConjugate

namespace Cvs.Approximant.SpineCoefficientMatrix

open Cvs.WeilForm.ThetaSpaceParseval (mellinR)
open Cvs.Xi.EImageWindowPoisson (window)

/-! ### Linearity of the window transform in the coefficients -/

/-- **The Mellin transform of a finite real combination**, each term convergent at `s`. -/
theorem mellinR_finsetSum {ι : Type*} (S : Finset ι) (b : ι → ℝ) (F : ι → ℝ → ℝ) {s : ℂ}
    (hF : ∀ i ∈ S, MellinConvergent (fun θ => (F i θ : ℂ)) s) :
    mellinR (fun θ => ∑ i ∈ S, b i * F i θ) s = ∑ i ∈ S, (b i : ℂ) * mellinR (F i) s := by
  unfold mellinR mellin
  have h : ∀ i ∈ S, (b i : ℂ) * ∫ θ in Ioi (0 : ℝ), (θ : ℂ) ^ (s - 1) • (F i θ : ℂ)
      = ∫ θ in Ioi (0 : ℝ), (b i : ℂ) * ((θ : ℂ) ^ (s - 1) • (F i θ : ℂ)) := fun i _ =>
    (integral_const_mul _ _).symm
  rw [Finset.sum_congr rfl h, ← integral_finsetSum S fun i hi => (hF i hi).const_mul _]
  refine setIntegral_congr_fun measurableSet_Ioi fun θ _ => ?_
  simp only [smul_eq_mul, ofReal_sum, ofReal_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The spine profile is the coefficient combination of the single-rung profiles. -/
theorem spineG_eq_sum (c : ℝ) (x : ℕ) (a : Cvs.Approximant.SpineSubspace.SF x → ℝ) :
    Cvs.Approximant.DeepIndexSpineSpan.spineG c a = fun s => ∑ j, a j * Cvs.Approximant.DeepIndexSpineSpan.spineG c (Pi.single j 1) s := by
  funext s
  unfold Cvs.Approximant.DeepIndexSpineSpan.spineG
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_eq_single j (fun k _ hk => by simp [hk]) (by simp)]
  simp

/-- The window transform of rung `j` at `s`: `u_s(e_j) = M[k_{G_{e_j}}](s)`. -/
def uVec (x : ℕ) (s : ℂ) (j : Cvs.Approximant.SpineSubspace.SF x) : ℂ :=
  mellinR (window (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) (Pi.single j 1))) s

/-- `u_s(a) = Σ_j a_j u_s(e_j)`. -/
def uA (x : ℕ) (s : ℂ) (a : Cvs.Approximant.SpineSubspace.SF x → ℝ) : ℂ := ∑ j, (a j : ℂ) * uVec x s j

/-- **The window transform of the spine profile is linear in the coefficients**: for `0 < x` and every
`s ∈ ℂ`, `M[k_{G_a}](s) = Σ_j a_j u_s(e_j)`. -/
theorem mellinR_window_spineG {x : ℕ} (hx : 0 < x) (a : Cvs.Approximant.SpineSubspace.SF x → ℝ) (s : ℂ) :
    mellinR (window (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a)) s = uA x s a := by
  have ha : (0 : ℝ) < 1 / x := by positivity
  have ha1 : (1 : ℝ) / x ≤ 1 := by
    rw [div_le_one (by positivity)]; exact_mod_cast hx
  rw [spineG_eq_sum, Cvs.Xi.EImageWindowPoisson.window_sum]
  refine mellinR_finsetSum _ _ _ fun j _ => Cvs.Xi.WindowImageMellinClosed.mellinConvergent_window ha ?_ s
  exact ((Cvs.L2a.SpineProfileWindowNormPos.continuousOn_spineG _ _).mono (Icc_subset_Icc (by linarith) le_rfl)).integrableOn_Icc

/-! ### The zero side in the coefficients -/

/-! ### The spine form and its Gram matrix -/

/-- The spine form `B(a, b) = QWbil(spineMap x a, spineMap x b)` on the coefficients. -/
def spineForm (x : ℕ) : LinearMap.BilinForm ℝ (Cvs.Approximant.SpineSubspace.SF x → ℝ) :=
  (Cvs.Route.L1FloorFromBulkD0.Bx x).compl₁₂ (Cvs.Approximant.SpineSubspace.spineMap x) (Cvs.Approximant.SpineSubspace.spineMap x)

theorem spineForm_self (x : ℕ) (a : Cvs.Approximant.SpineSubspace.SF x → ℝ) :
    spineForm x a a = Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) x (Nat.clog 2 x) (Cvs.Approximant.SpineSubspace.spineMap x a) :=
  Cvs.WeilForm.SymmetricBilinearForm.QWbil_self _ _ _ _

theorem spineForm_isSymm (x : ℕ) : (spineForm x).IsSymm :=
  ⟨fun _ _ => (Cvs.WeilForm.SymmetricBilinearForm.QWbil_isSymm (Real.log_natCast_nonneg x) x (Nat.clog 2 x)).eq _ _⟩

/-- The spine Gram matrix `(Q(spineMap x e_i, spineMap x e_j))_{ij}`. -/
def spineGram (x : ℕ) : Matrix (Cvs.Approximant.SpineSubspace.SF x) (Cvs.Approximant.SpineSubspace.SF x) ℝ :=
  Cvs.WeilForm.BulkSchurIdentity.gram (spineForm x) fun j => Pi.single j 1

theorem spineGram_isHermitian (x : ℕ) : (spineGram x).IsHermitian :=
  Cvs.WeilForm.BulkSchurIdentity.gram_isHermitian (spineForm_isSymm x) _

theorem sum_single (x : ℕ) (a : Cvs.Approximant.SpineSubspace.SF x → ℝ) : ∑ i, a i • (Pi.single i (1 : ℝ) : Cvs.Approximant.SpineSubspace.SF x → ℝ) = a := by
  ext k; simp [Pi.single_apply]

/-- `aᵀ(spineGram x)b = B(a, b)`. -/
theorem dot_spineGram (x : ℕ) (a b : Cvs.Approximant.SpineSubspace.SF x → ℝ) : a ⬝ᵥ (spineGram x *ᵥ b) = spineForm x a b := by
  conv_rhs => rw [← sum_single x a, ← sum_single x b]
  rw [Cvs.WeilForm.BulkSchurIdentity.apply_sum_left, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Cvs.WeilForm.BulkSchurIdentity.apply_sum_right, mulVec, dotProduct]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by rw [spineGram, Cvs.WeilForm.BulkSchurIdentity.gram, of_apply]; ring

/-- **The spine Gram matrix is the window form on the spine**: `aᵀ(spineGram x)a = Q(spineMap x a)`. -/
theorem quad_spineGram (x : ℕ) (a : Cvs.Approximant.SpineSubspace.SF x → ℝ) :
    a ⬝ᵥ (spineGram x *ᵥ a)
      = Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) x (Nat.clog 2 x) (Cvs.Approximant.SpineSubspace.spineMap x a) := by
  rw [dot_spineGram, spineForm_self]

/-! ### Spine vectors are nonzero -/

/-- **The spine map is injective** at `80 ≤ 2πx`: `a ≠ 0 → spineMap x a ≠ 0`. -/
theorem spineMap_injective {x : ℕ} (hx : 80 ≤ 2 * π * x) : Function.Injective (Cvs.Approximant.SpineSubspace.spineMap x) := by
  refine (injective_iff_map_eq_zero _).2 fun a ha => ?_
  by_contra hne
  have hpos := Cvs.L2a.SpineProfileWindowNormPos.window_norm_pos x hx (S := Cvs.Approximant.SpineSubspace.SF x)
    (fun j hj => ⟨(Finset.mem_filter.1 hj).2, Cvs.Approximant.SpineSubspace.SF_lt x j hj⟩) a hne
  rw [← Cvs.Approximant.SpineFloorFormDomain.norm_spineMap_sq x hx a, ha] at hpos
  simp at hpos

end Cvs.Approximant.SpineCoefficientMatrix
