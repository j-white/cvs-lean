import Mathlib
import Cvs.Upstream.ContractionTraceComparison
import Cvs.Upstream.FourierTransferDualOperator
import Cvs.Upstream.SchurLayerFloors

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The per-rung transfer bound `(C⁻¹)_jj ≤ 1 + 2B_jj/(1 − q)`

For eigenvectors `F e_b = σ_b e_b` of a symmetric contraction, inner solutions `s_b`, `B_bb = ⟨s_b, Qe_b⟩` and
`q = Σ_b (1 − σ_b)B_bb < 1`, every diagonal entry of the inverse of `C = Gram(e_b − Qe_b)` is `≤ 1 + 2B_jj/(1 − q)`.
-/

noncomputable section

open Matrix Finset

namespace Cvs.Upstream.ContractionInverseDiagonal
open Cvs.ZeroCounting

open Cvs.Upstream.FourierTransferDualOperator (IsSymmProj)
open Cvs.Upstream.ContractionTraceComparison (form)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Q F Ft : E →ₗ[ℝ] E}

/-- **The per-rung transfer**: with `F̃ = F + Σ_b (1 − σ_b)e_b e_bᵀ` a symmetric contraction, inner solutions `s_b`
and `q = Σ_b (1 − σ_b)⟨s_b, Qe_b⟩ < 1`, `C = Gram(e_b − Qe_b)` has `(C⁻¹)_jj ≤ 1 + 2⟨s_j, Qe_j⟩/(1 − q)`. -/
theorem inv_diag_le (hQ : IsSymmProj Q) (hF : ∀ x y, inner ℝ (F x) y = inner ℝ x (F y))
    (hFc : ∀ x, ‖F x‖ ≤ ‖x‖) (hFts : ∀ x y, inner ℝ (Ft x) y = inner ℝ x (Ft y)) (hFtc : ∀ x, ‖Ft x‖ ≤ ‖x‖)
    {e s : ι → E} {σ : ι → ℝ}
    (he : ∀ a b, inner ℝ (e a) (e b) = if a = b then 1 else 0) (hFe : ∀ b, F (e b) = σ b • e b)
    (hFt : ∀ z, Ft z = F z + ∑ b, ((1 - σ b) * inner ℝ (e b) z) • e b)
    (hs : ∀ b, Q (s b) = s b) (hse : ∀ b, s b = Q (e b) + Q (F (s b)))
    (hC : (gram ℝ fun b => e b - Q (e b)).PosDef) (hσ : ∀ b, σ b ≤ 1)
    (hq : ∑ b, (1 - σ b) * inner ℝ (s b) (Q (e b)) < 1) (j : ι) :
    (gram ℝ fun b => e b - Q (e b))⁻¹ j j
      ≤ 1 + 2 * inner ℝ (s j) (Q (e j)) / (1 - ∑ b, (1 - σ b) * inner ℝ (s b) (Q (e b))) := by
  set C := gram ℝ fun b => e b - Q (e b)
  have hBd : ∀ b, inner ℝ (s b) (Q (e b)) = form F (s b) (s b) := fun b =>
    Cvs.Upstream.ContractionTraceComparison.inner_eq_form hQ (hs b) (hse b)
  simp only [hBd] at hq ⊢
  set q := ∑ b, (1 - σ b) * form F (s b) (s b)
  have hδ : ∀ b, 0 ≤ 1 - σ b := fun b => sub_nonneg.mpr (hσ b)
  choose κ hκ using fun i => Cvs.Upstream.ContractionTraceComparison.exists_fix hF hFc hδ hq (s i)
  set r : ι → E := fun i => s i + ∑ c, κ i c • s c
  have htr := fun i => Cvs.Upstream.ContractionTraceComparison.transfer_eq (Ft := Ft) hQ hF hFt hs hse (hκ i)
  set Φ : ι → E := fun i => e i + Ft (r i)
  have hQΦ : ∀ i, Q (Φ i) = r i := fun i => by
    simp only [Φ, map_add]; exact ((htr i).2).symm
  have hΦ : ∀ i, Φ i = e i + Ft (Q (Φ i)) := fun i => by rw [hQΦ]
  have hFte := Cvs.Upstream.ContractionTraceComparison.fix_apply (Ft := Ft) he hFe hFt
  set w : ι → E := fun i => Φ i - Q (Φ i)
  have hdual : ∀ i b, inner ℝ (w i) (e b - Q (e b)) = if b = i then 1 else 0 := by
    intro i b
    have h0 : inner ℝ (w i) (Q (e b)) = 0 := by
      rw [← hQ.symm, Cvs.Upstream.FourierTransferDualOperator.inner_part_transfer hQ, inner_zero_left]
    rw [inner_sub_right, h0, sub_zero, Cvs.Upstream.FourierTransferDualOperator.inner_transfer hFts (hΦ i) (hFte b), he]
    by_cases h : i = b
    · simp [h]
    · simp [h, Ne.symm h]
  have hinv : C⁻¹ j j ≤ ‖w j‖ ^ 2 := by
    have h := Cvs.Upstream.SchurLayerFloors.quad_inv_le_norm_dual (g := id) hC w (fun a i => by rw [hdual a i]; rfl) (Pi.single j 1)
    simpa [Pi.single_apply, ite_smul, Finset.sum_ite_eq', Matrix.submatrix_id_id] using h
  have hnorm : ‖w j‖ ^ 2 ≤ 1 + 2 * form F (r j) (s j) := by
    have h := Cvs.Upstream.FourierTransferDualOperator.norm_sq_transfer_le hQ hFts hFtc (hΦ j) (hFte j)
    have h1 : ‖e j‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq, he]; simp
    rw [h1, hQΦ, Cvs.Upstream.ContractionTraceComparison.inner_eq_form hQ (htr j).1 (hse j)] at h
    show ‖Φ j - Q (Φ j)‖ ^ 2 ≤ _
    rw [hQΦ]; exact h
  have hwood : (1 - q) * form F (r j) (s j) ≤ form F (s j) (s j) := Cvs.Upstream.ContractionTraceComparison.form_le_of_fix hF hFc hδ hq (hκ j)
  have hq' : 0 < 1 - q := by linarith
  have h2 : form F (r j) (s j) ≤ form F (s j) (s j) / (1 - q) := by
    rw [le_div_iff₀ hq']; linarith
  calc C⁻¹ j j ≤ 1 + 2 * form F (r j) (s j) := hinv.trans hnorm
    _ ≤ 1 + 2 * (form F (s j) (s j) / (1 - q)) := by linarith
    _ = 1 + 2 * form F (s j) (s j) / (1 - q) := by ring

end Cvs.Upstream.ContractionInverseDiagonal

end
