import Mathlib
import Cvs.Upstream.FourierTransferDualOperator
import Cvs.Upstream.InverseExcessPencilTop
import Cvs.Upstream.SchurLayerFloors

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The finite transfer and trace comparison for a symmetric contraction

For eigenvectors `F e_b = σ_b e_b` of a symmetric contraction, a symmetric idempotent `Q` and inner solutions
`s_b = Qe_b + QFs_b`, `B_bc = ⟨s_b, Qe_c⟩`; if `q = Σ_b (1 − σ_b)B_bb < 1`, a finite Woodbury system gives
`(1 − q)⟨r_j, Qe_j⟩ ≤ B_jj`, and the transfer rows give `Σ_j μ_j((C⁻¹)_jj − 1) ≤ 2aT/(1 − mT)`.
-/

noncomputable section

open Matrix Finset

namespace Cvs.Upstream.ContractionTraceComparison
open Cvs.ZeroCounting

open Cvs.Upstream.FourierTransferDualOperator (IsSymmProj)
open Cvs.Upstream.InverseExcessPencilTop (excessTrace)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The resolvent form `ω(u, v) = ⟨u, v − Fv⟩`. -/
def form (F : E →ₗ[ℝ] E) (u v : E) : ℝ := inner ℝ u (v - F v)

section Form

variable {F : E →ₗ[ℝ] E}

/-- `ω` is symmetric when `F` is. -/
theorem form_symm (hF : ∀ x y, inner ℝ (F x) y = inner ℝ x (F y)) (u v : E) : form F u v = form F v u := by
  unfold form
  rw [inner_sub_right, inner_sub_right, real_inner_comm v u, ← hF u v, real_inner_comm v (F u)]

/-- `ω(u, u) ≥ 0` when `F` is a contraction. -/
theorem form_self_nonneg (hFc : ∀ x, ‖F x‖ ≤ ‖x‖) (u : E) : 0 ≤ form F u u := by
  unfold form
  rw [inner_sub_right, real_inner_self_eq_norm_sq]
  have h1 := real_inner_le_norm u (F u)
  have h2 := mul_le_mul_of_nonneg_left (hFc u) (norm_nonneg u)
  nlinarith

/-- `ω` is additive in the first slot. -/
theorem form_add_left (u u' v : E) : form F (u + u') v = form F u v + form F u' v := by
  unfold form; rw [inner_add_left]

/-- `ω` is linear over finite sums in the first slot. -/
theorem form_sum_left {ι : Type*} (s : Finset ι) (a : ι → ℝ) (u : ι → E) (v : E) :
    form F (∑ i ∈ s, a i • u i) v = ∑ i ∈ s, a i * form F (u i) v := by
  unfold form; simp only [sum_inner, inner_smul_left, conj_trivial]

/-- `ω` is linear over finite sums in the second slot. -/
theorem form_sum_right {ι : Type*} (s : Finset ι) (a : ι → ℝ) (u : E) (v : ι → E) :
    form F u (∑ i ∈ s, a i • v i) = ∑ i ∈ s, a i * form F u (v i) := by
  unfold form
  rw [map_sum, ← Finset.sum_sub_distrib, inner_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, ← smul_sub, inner_smul_right]

/-- **Cauchy–Schwarz for `ω`**: `ω(u, v)² ≤ ω(u, u)ω(v, v)`. -/
theorem form_sq_le (hF : ∀ x y, inner ℝ (F x) y = inner ℝ x (F y)) (hFc : ∀ x, ‖F x‖ ≤ ‖x‖) (u v : E) :
    form F u v ^ 2 ≤ form F u u * form F v v := by
  have h : ∀ t : ℝ, 0 ≤ form F v v * (t * t) + 2 * form F u v * t + form F u u := by
    intro t
    have h0 := form_self_nonneg hFc (u + t • v)
    have e1 : u + t • v - F (u + t • v) = (u - F u) + t • (v - F v) := by
      rw [map_add, map_smul]; module
    have e : form F (u + t • v) (u + t • v)
        = form F v v * (t * t) + 2 * form F u v * t + form F u u := by
      have hs := form_symm hF v u
      unfold form at hs ⊢
      rw [e1, inner_add_left, inner_add_right, inner_add_right, inner_smul_left, inner_smul_right,
        inner_smul_right, inner_smul_left, hs]
      simp only [conj_trivial]
      ring
    linarith
  have hd := discrim_le_zero h
  unfold discrim at hd
  nlinarith

end Form

section Solve

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {F : E →ₗ[ℝ] E}

/-- **The finite Woodbury system is solvable**: if `δ ≥ 0` and `Σ_b δ_b ω(s_b, s_b) < 1`, then for every `u₀`
some `κ` has `κ_b = δ_b ω(s_b, u₀ + Σ_c κ_c s_c)`. -/
theorem exists_fix (hF : ∀ x y, inner ℝ (F x) y = inner ℝ x (F y)) (hFc : ∀ x, ‖F x‖ ≤ ‖x‖) {s : ι → E}
    {δ : ι → ℝ} (hδ : ∀ b, 0 ≤ δ b) (hq : ∑ b, δ b * form F (s b) (s b) < 1) (u₀ : E) :
    ∃ κ : ι → ℝ, ∀ b, κ b = δ b * form F (s b) (u₀ + ∑ c, κ c • s c) := by
  set Bm : Matrix ι ι ℝ := Matrix.of fun b c => form F (s b) (s c)
  set L := Matrix.mulVecLin (1 - diagonal δ * Bm)
  have hL : ∀ κ, L κ = κ - fun b => δ b * form F (s b) (∑ c, κ c • s c) := by
    intro κ
    ext b
    simp only [L, Matrix.mulVecLin_apply, sub_mulVec, one_mulVec, Pi.sub_apply, ← mulVec_mulVec,
      mulVec_diagonal, form_sum_right]
    simp [Bm, mulVec, dotProduct, mul_comm]
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro κ hκ
    rw [hL, sub_eq_zero] at hκ
    set S := ∑ c, κ c • s c
    have hz : ∀ b, κ b = δ b * form F (s b) S := fun b => congrFun hκ b
    have hY : form F S S = ∑ b, δ b * form F (s b) S ^ 2 := by
      rw [form_sum_left]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [hz b]; ring
    have hY0 := form_self_nonneg hFc S
    have hle : ∑ b, δ b * form F (s b) S ^ 2 ≤ (∑ b, δ b * form F (s b) (s b)) * form F S S := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun b _ => ?_
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (form_sq_le hF hFc _ _) (hδ b)
    have hS0 : form F S S = 0 := by nlinarith
    ext b
    have hb := form_sq_le hF hFc (s b) S
    rw [hS0, mul_zero] at hb
    have : form F (s b) S = 0 := by nlinarith [sq_nonneg (form F (s b) S)]
    rw [hz b, this, mul_zero, Pi.zero_apply]
  obtain ⟨κ, hκ⟩ := (LinearMap.injective_iff_surjective.mp hinj) fun b => δ b * form F (s b) u₀
  refine ⟨κ, fun b => ?_⟩
  have h := congrFun hκ b
  rw [hL] at h
  simp only [Pi.sub_apply] at h
  have e : form F (s b) (u₀ + ∑ c, κ c • s c) = form F (s b) u₀ + form F (s b) (∑ c, κ c • s c) := by
    unfold form; rw [map_add, add_sub_add_comm, inner_add_right]
  rw [e]
  linarith

omit [DecidableEq ι] in
/-- **The Woodbury comparison**: for a solution `κ_b = δ_b ω(s_b, r)`, `r = s_j + Σ_c κ_c s_c`, of the finite system,
`(1 − q)ω(r, s_j) ≤ ω(s_j, s_j)` with `q = Σ_b δ_b ω(s_b, s_b) < 1`. -/
theorem form_le_of_fix (hF : ∀ x y, inner ℝ (F x) y = inner ℝ x (F y)) (hFc : ∀ x, ‖F x‖ ≤ ‖x‖) {s : ι → E}
    {δ : ι → ℝ} (hδ : ∀ b, 0 ≤ δ b) (hq : ∑ b, δ b * form F (s b) (s b) < 1) {j : ι} {κ : ι → ℝ}
    (hκ : ∀ b, κ b = δ b * form F (s b) (s j + ∑ c, κ c • s c)) :
    (1 - ∑ b, δ b * form F (s b) (s b)) * form F (s j + ∑ c, κ c • s c) (s j) ≤ form F (s j) (s j) := by
  set r := s j + ∑ c, κ c • s c
  set q := ∑ b, δ b * form F (s b) (s b)
  set Z := ∑ b, δ b * form F (s b) r ^ 2
  set Y := form F r r
  set zj := form F r (s j)
  have hq0 : 0 ≤ q := Finset.sum_nonneg fun b _ => mul_nonneg (hδ b) (form_self_nonneg hFc _)
  have hY : Y = zj + Z := by
    change form F (s j + ∑ c, κ c • s c) r = form F (s j + ∑ c, κ c • s c) (s j) + Z
    rw [form_add_left, form_sum_left, form_symm hF (s j) r]
    congr 1
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hκ b, form_symm hF (s b) r]; ring
  have hZ0 : 0 ≤ Z := Finset.sum_nonneg fun b _ => mul_nonneg (hδ b) (sq_nonneg _)
  have hZ : Z ≤ q * Y := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun b _ => ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left ((form_sq_le hF hFc _ _).trans (le_of_eq (by ring))) (hδ b)
  have hY0 : 0 ≤ Y := form_self_nonneg hFc r
  have hB0 : 0 ≤ form F (s j) (s j) := form_self_nonneg hFc _
  have hcs : zj ^ 2 ≤ form F (s j) (s j) * Y := by
    have := form_sq_le hF hFc (s j) r
    rw [form_symm hF (s j) r] at this
    linarith
  have hzj : (1 - q) * Y ≤ zj := by nlinarith
  rcases le_or_gt zj 0 with h | h
  · nlinarith
  · have h1 : (1 - q) * zj ^ 2 ≤ form F (s j) (s j) * zj := by nlinarith
    nlinarith

end Solve

section Transfer

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Q F Ft : E →ₗ[ℝ] E}

/-- `⟨r, Qy⟩ = ω(r, s)` for `Qr = r` and an inner solution `s = Qy + QFs`. -/
theorem inner_eq_form (hQ : IsSymmProj Q) {r s y : E} (hr : Q r = r) (hs : s = Q y + Q (F s)) :
    inner ℝ r (Q y) = form F r s := by
  have e : Q y = s - Q (F s) := by rw [eq_sub_iff_add_eq]; exact hs.symm
  rw [e, form, inner_sub_right, inner_sub_right, ← hQ.symm, hr]

omit [DecidableEq ι] in
/-- **The transfer solution**: a solution `κ` of the finite system gives `r = s_j + Σ_c κ_c s_c` with `Qr = r` and
`r = Qe_j + QF̃r`, for `F̃ = F + Σ_b (1 − σ_b)e_b e_bᵀ`. -/
theorem transfer_eq (hQ : IsSymmProj Q) (hF : ∀ x y, inner ℝ (F x) y = inner ℝ x (F y)) {e s : ι → E}
    {σ : ι → ℝ} (hFt : ∀ z, Ft z = F z + ∑ b, ((1 - σ b) * inner ℝ (e b) z) • e b)
    (hs : ∀ b, Q (s b) = s b) (hse : ∀ b, s b = Q (e b) + Q (F (s b))) {j : ι} {κ : ι → ℝ}
    (hκ : ∀ b, κ b = (1 - σ b) * form F (s b) (s j + ∑ c, κ c • s c)) :
    Q (s j + ∑ c, κ c • s c) = s j + ∑ c, κ c • s c
      ∧ s j + ∑ c, κ c • s c = Q (e j) + Q (Ft (s j + ∑ c, κ c • s c)) := by
  set r := s j + ∑ c, κ c • s c with hr
  have hQr : Q r = r := by
    simp only [r, map_add, map_sum, map_smul, hs]
  refine ⟨hQr, ?_⟩
  have hQF : ∀ b, Q (F (s b)) = s b - Q (e b) := fun b => by
    have := hse b; rw [eq_sub_iff_add_eq, add_comm]; exact this.symm
  have hcoef : ∀ b, (1 - σ b) * inner ℝ (e b) r = κ b := by
    intro b
    have h1 : inner ℝ (e b) r = inner ℝ r (Q (e b)) := by
      rw [← hQ.symm, hQr]; exact real_inner_comm _ _
    rw [h1, inner_eq_form hQ hQr (hse b), form_symm hF r (s b), hκ b]
  rw [hFt, map_add, map_sum]
  simp only [map_smul, hcoef]
  have hFr : Q (F r) = (s j - Q (e j)) + ∑ c, κ c • (s c - Q (e c)) := by
    simp only [r, map_add, map_sum, map_smul, hQF]
  rw [hFr]
  simp only [smul_sub, Finset.sum_sub_distrib, r]
  abel

/-- `F̃` fixes every `e_b` when `F e_b = σ_b e_b` and the `e_b` are orthonormal. -/
theorem fix_apply {e : ι → E} {σ : ι → ℝ} (he : ∀ a b, inner ℝ (e a) (e b) = if a = b then 1 else 0)
    (hFe : ∀ b, F (e b) = σ b • e b) (hFt : ∀ z, Ft z = F z + ∑ b, ((1 - σ b) * inner ℝ (e b) z) • e b)
    (j : ι) : Ft (e j) = e j := by
  rw [hFt, hFe]
  simp only [he, mul_ite, mul_one, mul_zero, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [← add_smul]; ring_nf; rw [one_smul]

/-- **The rung-fixed transform is a finite-rank shift**: for `P z = Σ_b ⟨e_b, z⟩e_b` over orthonormal eigenvectors
`T e_b = σ_b e_b` of a symmetric `T`, `P + (1 − P)T(1 − P) = T + Σ_b (1 − σ_b)e_b e_bᵀ`. -/
theorem fixT_eq {P T : E →ₗ[ℝ] E} {e : ι → E} {σ : ι → ℝ}
    (he : ∀ a b, inner ℝ (e a) (e b) = if a = b then 1 else 0) (hT : ∀ x y, inner ℝ (T x) y = inner ℝ x (T y))
    (hTe : ∀ b, T (e b) = σ b • e b) (hP : ∀ z, P z = ∑ b, inner ℝ (e b) z • e b) (z : E) :
    Cvs.Upstream.FourierTransferDualOperator.fixT P T z = T z + ∑ b, ((1 - σ b) * inner ℝ (e b) z) • e b := by
  have hy : ∀ b, inner ℝ (e b) (z - P z) = 0 := by
    intro b
    rw [inner_sub_right, hP, inner_sum]
    simp only [inner_smul_right, he, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true,
      sub_self]
  have hPT : P (T (z - P z)) = 0 := by
    rw [hP]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [← hT, hTe, inner_smul_left, hy, mul_zero, zero_smul]
  have hTP : T (P z) = ∑ b, (σ b * inner ℝ (e b) z) • e b := by
    rw [hP, map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_smul, hTe, smul_smul, mul_comm]
  rw [Cvs.Upstream.FourierTransferDualOperator.fixT_apply, hPT, sub_zero, map_sub, hTP, hP]
  simp only [sub_mul, one_mul, sub_smul, Finset.sum_sub_distrib]
  abel

/-- **The transfer and trace comparison**: with `F̃ = F + Σ_b (1 − σ_b)e_b e_bᵀ` a symmetric contraction, inner
solutions `s_b`, `μ_b ≤ aγ_b`, `1 − σ_b ≤ mγ_b` and `Σ_b γ_b⟨s_b, Qe_b⟩ ≤ T < 1/m`, the cell Gram
`C = Gram(e_b − Qe_b)` has `Σ_j μ_j((C⁻¹)_jj − 1) ≤ 2aT/(1 − mT)`. -/
theorem excessTrace_le (hQ : IsSymmProj Q) (hF : ∀ x y, inner ℝ (F x) y = inner ℝ x (F y))
    (hFc : ∀ x, ‖F x‖ ≤ ‖x‖) (hFts : ∀ x y, inner ℝ (Ft x) y = inner ℝ x (Ft y)) (hFtc : ∀ x, ‖Ft x‖ ≤ ‖x‖)
    {e s : ι → E} {σ μ γ : ι → ℝ} {a m T : ℝ}
    (he : ∀ a b, inner ℝ (e a) (e b) = if a = b then 1 else 0) (hFe : ∀ b, F (e b) = σ b • e b)
    (hFt : ∀ z, Ft z = F z + ∑ b, ((1 - σ b) * inner ℝ (e b) z) • e b)
    (hs : ∀ b, Q (s b) = s b) (hse : ∀ b, s b = Q (e b) + Q (F (s b)))
    (hC : (gram ℝ fun b => e b - Q (e b)).PosDef) (hσ : ∀ b, σ b ≤ 1) (hμ : ∀ b, 0 ≤ μ b)
    (hμa : ∀ b, μ b ≤ a * γ b) (hδm : ∀ b, 1 - σ b ≤ m * γ b) (ha : 0 ≤ a) (hm : 0 ≤ m)
    (hT : ∑ b, γ b * inner ℝ (s b) (Q (e b)) ≤ T) (hmT : m * T < 1) :
    excessTrace μ (gram ℝ fun b => e b - Q (e b)) ≤ 2 * a * T / (1 - m * T) := by
  set C := gram ℝ fun b => e b - Q (e b)
  set Bd : ι → ℝ := fun b => form F (s b) (s b)
  have hBd : ∀ b, inner ℝ (s b) (Q (e b)) = Bd b := fun b => inner_eq_form hQ (hs b) (hse b)
  have hBd0 : ∀ b, 0 ≤ Bd b := fun b => form_self_nonneg hFc _
  set S := ∑ b, γ b * Bd b
  have hST : S ≤ T := by simpa only [hBd] using hT
  have hδ : ∀ b, 0 ≤ 1 - σ b := fun b => sub_nonneg.mpr (hσ b)
  set q := ∑ b, (1 - σ b) * Bd b
  have hqS : q ≤ m * S := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun b _ => ?_
    rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (hδm b) (hBd0 b)
  have hqT : q ≤ m * T := hqS.trans (mul_le_mul_of_nonneg_left hST hm)
  have hq1 : q < 1 := hqT.trans_lt hmT
  have hpos : 0 < 1 - m * T := by linarith
  choose κ hκ using fun j => exists_fix hF hFc hδ hq1 (s j)
  set r : ι → E := fun j => s j + ∑ c, κ j c • s c
  have htr := fun j => transfer_eq (Ft := Ft) hQ hF hFt hs hse (hκ j)
  set Φ : ι → E := fun j => e j + Ft (r j)
  have hQΦ : ∀ j, Q (Φ j) = r j := fun j => by
    simp only [Φ, map_add]; exact ((htr j).2).symm
  have hΦ : ∀ j, Φ j = e j + Ft (Q (Φ j)) := fun j => by rw [hQΦ]
  have hFte := fix_apply (Ft := Ft) he hFe hFt
  set w : ι → E := fun j => Φ j - Q (Φ j)
  have hdual : ∀ j b, inner ℝ (w j) (e b - Q (e b)) = if b = j then 1 else 0 := by
    intro j b
    have h0 : inner ℝ (w j) (Q (e b)) = 0 := by
      rw [← hQ.symm, Cvs.Upstream.FourierTransferDualOperator.inner_part_transfer hQ, inner_zero_left]
    rw [inner_sub_right, h0, sub_zero, Cvs.Upstream.FourierTransferDualOperator.inner_transfer hFts (hΦ j) (hFte b), he]
    by_cases h : j = b
    · simp [h]
    · simp [h, Ne.symm h]
  have hinv : ∀ j, C⁻¹ j j ≤ ‖w j‖ ^ 2 := by
    intro j
    have h := Cvs.Upstream.SchurLayerFloors.quad_inv_le_norm_dual (g := id) hC w (fun a i => by rw [hdual a i]; rfl) (Pi.single j 1)
    simpa [Pi.single_apply, ite_smul, Finset.sum_ite_eq', Matrix.submatrix_id_id] using h
  have hnorm : ∀ j, ‖w j‖ ^ 2 ≤ 1 + 2 * form F (r j) (s j) := by
    intro j
    have h := Cvs.Upstream.FourierTransferDualOperator.norm_sq_transfer_le hQ hFts hFtc (hΦ j) (hFte j)
    have h1 : ‖e j‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq, he]; simp
    rw [h1, hQΦ, inner_eq_form hQ (htr j).1 (hse j)] at h
    show ‖Φ j - Q (Φ j)‖ ^ 2 ≤ _
    rw [hQΦ]; exact h
  have hwood : ∀ j, (1 - q) * form F (r j) (s j) ≤ Bd j := fun j => form_le_of_fix hF hFc hδ hq1 (hκ j)
  have hstep : ∀ j, μ j * (C⁻¹ j j - 1) ≤ 2 / (1 - q) * (μ j * Bd j) := by
    intro j
    have h1 : C⁻¹ j j - 1 ≤ 2 * form F (r j) (s j) := by linarith [hinv j, hnorm j]
    have hq' : 0 < 1 - q := by linarith
    have h2 : form F (r j) (s j) ≤ Bd j / (1 - q) := by
      rw [le_div_iff₀ hq']; linarith [hwood j]
    calc μ j * (C⁻¹ j j - 1) ≤ μ j * (2 * (Bd j / (1 - q))) :=
          mul_le_mul_of_nonneg_left (h1.trans (by linarith)) (hμ j)
      _ = 2 / (1 - q) * (μ j * Bd j) := by field_simp
  have hsum : ∑ j, μ j * Bd j ≤ a * T := by
    calc ∑ j, μ j * Bd j ≤ ∑ j, a * γ j * Bd j :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hμa j) (hBd0 j)
      _ = a * S := by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
      _ ≤ a * T := mul_le_mul_of_nonneg_left hST ha
  have hsum0 : 0 ≤ ∑ j, μ j * Bd j := Finset.sum_nonneg fun j _ => mul_nonneg (hμ j) (hBd0 j)
  calc excessTrace μ C ≤ ∑ j, 2 / (1 - q) * (μ j * Bd j) := Finset.sum_le_sum fun j _ => hstep j
    _ = 2 / (1 - q) * ∑ j, μ j * Bd j := by rw [Finset.mul_sum]
    _ ≤ 2 / (1 - m * T) * (a * T) := by
        apply mul_le_mul _ hsum hsum0 (by positivity)
        exact div_le_div_of_nonneg_left (by norm_num) hpos (by linarith)
    _ = 2 * a * T / (1 - m * T) := by ring

end Transfer

end Cvs.Upstream.ContractionTraceComparison

end
