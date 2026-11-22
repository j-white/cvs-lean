import Mathlib
import Cvs.Route.DilationLatticeCriterion
import Cvs.Route.OneCellCriterion
import Cvs.Route.OneCellLaplaceTransform
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.InfimumAttainedSphere
import Cvs.WeilForm.SymmetricBilinearForm
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowWeilCriterion

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# RH by induction on nested boxes
Boxes `f_n = 1_{(0, log n]}` have Gram kernel `K(x,y) = (G x + G y − G|x − y|)/2`. `Step N`: the form of the boxes
up to `N + 1` is nonnegative whenever the new box has coefficient one. `BoxPSD (N+1) ↔ BoxPSD N ∧ Step N`, and
`RH ↔ ∀ N ≥ 1, Step N`: the step is the one hypothesis of an exact induction.
-/

noncomputable section

open Real Finset Matrix

namespace Cvs.Route.NestedBoxInduction
open Cvs.ZeroCounting

open Cvs.Route.OneCellLaplaceTransform (G)

/-- The nested-box kernel. -/
def K (x y : ℝ) : ℝ := (G x + G y - G |x - y|) / 2

theorem K_self (x : ℝ) : K x x = G x := by
  unfold K; rw [sub_self, abs_zero, Cvs.Route.DilationLatticeCriterion.G_zero]; ring

theorem K_comm (x y : ℝ) : K x y = K y x := by
  unfold K; rw [abs_sub_comm]; ring

/-- The quadratic form of the boxes `f_2, …, f_M`. -/
def qf (M : ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ m ∈ Icc 2 M, ∑ n ∈ Icc 2 M, c m * c n * K (Real.log m) (Real.log n)

/-- The boxes up to `M` have a positive semidefinite Gram matrix. -/
def BoxPSD (M : ℕ) : Prop := ∀ c : ℕ → ℝ, 0 ≤ qf M c

/-- **The induction step at `N`**: nonnegative whenever the new box `f_{N+1}` has coefficient one. -/
def Step (N : ℕ) : Prop := ∀ c : ℕ → ℝ, c (N + 1) = 1 → 0 ≤ qf (N + 1) c

theorem qf_smul (M : ℕ) (t : ℝ) (c : ℕ → ℝ) : qf M (t • c) = t ^ 2 * qf M c := by
  unfold qf
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]; ring

theorem qf_of_zero {N : ℕ} {c : ℕ → ℝ} (hc : c (N + 1) = 0) : qf (N + 1) c = qf N c := by
  unfold qf
  have hsub : Icc 2 N ⊆ Icc 2 (N + 1) := Finset.Icc_subset_Icc le_rfl (Nat.le_succ N)
  have hnew : ∀ k ∈ Icc 2 (N + 1), k ∉ Icc 2 N → k = N + 1 := by
    intro k hk hk'; simp only [Finset.mem_Icc] at hk hk'; omega
  have inner : ∀ m : ℕ, ∑ n ∈ Icc 2 (N + 1), c m * c n * K (Real.log m) (Real.log n)
      = ∑ n ∈ Icc 2 N, c m * c n * K (Real.log m) (Real.log n) := fun m =>
    (Finset.sum_subset hsub (fun n hn hn' => by rw [hnew n hn hn', hc]; ring)).symm
  rw [Finset.sum_congr rfl (fun m _ => inner m)]
  exact (Finset.sum_subset hsub (fun m hm hm' => by
    rw [hnew m hm hm', hc]; simp)).symm

theorem boxPSD_one : BoxPSD 1 := by
  intro c; unfold qf; simp

theorem step_of_boxPSD {N : ℕ} (h : BoxPSD (N + 1)) : Step N := fun c _ => h c

theorem boxPSD_of_succ {N : ℕ} (h : BoxPSD (N + 1)) : BoxPSD N := by
  intro c
  let c' : ℕ → ℝ := Function.update c (N + 1) 0
  have hc' : c' (N + 1) = 0 := by simp [c']
  have hagree : qf N c' = qf N c := by
    unfold qf
    refine Finset.sum_congr rfl fun m hm => Finset.sum_congr rfl fun n hn => ?_
    simp only [Finset.mem_Icc] at hm hn
    simp only [c', Function.update_of_ne (show m ≠ N + 1 by omega), Function.update_of_ne (show n ≠ N + 1 by omega)]
  rw [← hagree, ← qf_of_zero hc']
  exact h c'

/-- **The induction step**: the boxes up to `N + 1` are positive iff those up to `N` are and the step holds. -/
theorem boxPSD_succ_iff (N : ℕ) : BoxPSD (N + 1) ↔ BoxPSD N ∧ Step N := by
  refine ⟨fun h => ⟨boxPSD_of_succ h, step_of_boxPSD h⟩, fun ⟨hN, hS⟩ c => ?_⟩
  by_cases ht : c (N + 1) = 0
  · rw [qf_of_zero ht]; exact hN c
  · have hc : c = c (N + 1) • ((c (N + 1))⁻¹ • c) := by
      rw [smul_smul, mul_inv_cancel₀ ht, one_smul]
    rw [hc, qf_smul]
    refine mul_nonneg (sq_nonneg _) (hS _ ?_)
    simp [Pi.smul_apply, inv_mul_cancel₀ ht]

theorem boxPSD_of_forall_step (h : ∀ N, 1 ≤ N → Step N) : ∀ M, 1 ≤ M → BoxPSD M := by
  intro M hM
  induction M, hM using Nat.le_induction with
  | base => exact boxPSD_one
  | succ N hN ih => exact (boxPSD_succ_iff N).2 ⟨ih, h N hN⟩

/-- Sum of a coefficient vector against a fixed row: two-point coefficients pick two values. -/
theorem sum_two (S : Finset ℕ) (n m : ℕ) (hn : n ∈ S) (F : ℕ → ℝ) :
    ∑ k ∈ S, ((if k = n then (1:ℝ) else 0) - (if k = m then 1 else 0)) * F k
      = F n - (if m ∈ S then F m else 0) := by
  simp only [sub_mul, ite_mul, one_mul, zero_mul, Finset.sum_sub_distrib, Finset.sum_ite_eq', hn, ite_true]

/-- On the difference of two boxes the form is `G` of the log ratio. -/
theorem qf_diff {m n : ℕ} (hm : 1 ≤ m) (hmn : m < n) :
    qf n (fun k => (if k = n then (1:ℝ) else 0) - (if k = m then 1 else 0)) = G (Real.log ((n : ℝ) / m)) := by
  set c : ℕ → ℝ := fun k => (if k = n then (1:ℝ) else 0) - (if k = m then 1 else 0) with hcdef
  have hnmem : n ∈ Icc 2 n := Finset.mem_Icc.2 ⟨by omega, le_rfl⟩
  have hrow : ∀ i : ℕ, ∑ j ∈ Icc 2 n, c i * c j * K (Real.log i) (Real.log j)
      = c i * (K (Real.log i) (Real.log n) - (if m ∈ Icc 2 n then K (Real.log i) (Real.log m) else 0)) := by
    intro i
    rw [← sum_two (Icc 2 n) n m hnmem (fun j => K (Real.log i) (Real.log j)), Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => by simp only [hcdef]; ring
  unfold qf
  rw [Finset.sum_congr rfl (fun i _ => hrow i)]
  have hout := sum_two (Icc 2 n) n m hnmem
    (fun i => K (Real.log i) (Real.log n) - (if m ∈ Icc 2 n then K (Real.log i) (Real.log m) else 0))
  simp only [hcdef] at hout ⊢
  rw [hout]
  have hlog : Real.log ((n : ℝ) / m) = Real.log n - Real.log m :=
    Real.log_div (Nat.cast_ne_zero.2 (by omega)) (Nat.cast_ne_zero.2 (by omega))
  have hlt : Real.log (m : ℝ) < Real.log n := Real.log_lt_log (by exact_mod_cast hm) (by exact_mod_cast hmn)
  by_cases hm2 : m ∈ Icc 2 n
  · simp only [hm2, ite_true, K_self, hlog]
    rw [K_comm (Real.log m) (Real.log n)]
    unfold K
    rw [abs_of_pos (by linarith : 0 < Real.log (n:ℝ) - Real.log m)]
    ring
  · have hm1 : m = 1 := by simp only [Finset.mem_Icc, not_and, not_le] at hm2; omega
    subst hm1
    simp [hm2, K_self]

/-- The step at every `N` gives `RH`. -/
theorem rh_of_forall_step (h : ∀ N, 1 ≤ N → Step N) : RiemannHypothesis := by
  have hpsd := boxPSD_of_forall_step h
  refine Cvs.Route.OneCellCriterion.riemannHypothesis_of_G_nonneg fun L hL => ?_
  refine Cvs.Route.DilationLatticeCriterion.G_nonneg_of_log_ratio (fun m n hm hmn => ?_) hL
  rw [← qf_diff hm hmn]
  exact hpsd n (by omega) _

/-! ### `RH` gives the step: the boxes are lattice classes -/

section forward

variable (M : ℕ) (hM : 2 ≤ M)

/-- The box `f_n` at level `M` as a class: `e_0 − e_{n−1}` for `n < M`, `e_0` for `n = M`
(`e_i = 1_{(log(i+1), log M]}`, Cvs.Route.DilationLatticeCriterion). -/
def fv (n : ℕ) : Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg M) :=
  if h : 1 ≤ n ∧ n < M then Cvs.Route.DilationLatticeCriterion.e M hM ⟨0, by omega⟩ - Cvs.Route.DilationLatticeCriterion.e M hM ⟨n - 1, by omega⟩
  else Cvs.Route.DilationLatticeCriterion.e M hM ⟨0, by omega⟩

local notation "QB" => Cvs.WeilForm.SymmetricBilinearForm.QWbil (Real.log_natCast_nonneg M) M (Nat.clog 2 M)

theorem a_zero : Cvs.Route.DilationLatticeCriterion.a M ⟨0, by omega⟩ = 0 := by simp [Cvs.Route.DilationLatticeCriterion.a]

theorem a_pred {n : ℕ} (h : 1 ≤ n ∧ n < M) : Cvs.Route.DilationLatticeCriterion.a M ⟨n - 1, by omega⟩ = Real.log n := by
  simp only [Cvs.Route.DilationLatticeCriterion.a]; congr 1; push_cast [Nat.cast_sub h.1]; ring

theorem QB_e (i j : Fin (M - 1)) :
    QB (Cvs.Route.DilationLatticeCriterion.e M hM i) (Cvs.Route.DilationLatticeCriterion.e M hM j)
      = (G (Real.log M - Cvs.Route.DilationLatticeCriterion.a M i) + G (Real.log M - Cvs.Route.DilationLatticeCriterion.a M j) - G |Cvs.Route.DilationLatticeCriterion.a M i - Cvs.Route.DilationLatticeCriterion.a M j|) / 2 :=
  Cvs.Route.DilationLatticeCriterion.latticeGram_eq M hM i j

theorem QB_fv {m n : ℕ} (hm : m ∈ Icc 2 M) (hn : n ∈ Icc 2 M) :
    QB (fv M hM m) (fv M hM n) = K (Real.log m) (Real.log n) := by
  simp only [Finset.mem_Icc] at hm hn
  have h0 := a_zero M hM
  have lm0 := Real.log_natCast_nonneg m
  have ln0 := Real.log_natCast_nonneg n
  have lM0 := Real.log_natCast_nonneg M
  have hs1 : ∀ x y z : Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg M),
      QB (x - y) z = QB x z - QB y z := fun x y z => LinearMap.map_sub₂ QB x y z
  have hs2 : ∀ x y z : Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg M),
      QB x (y - z) = QB x y - QB x z := fun x y z => (QB x).map_sub y z
  unfold fv K
  by_cases hm' : 1 ≤ m ∧ m < M <;> by_cases hn' : 1 ≤ n ∧ n < M
  · simp only [hm', hn', and_self, dite_eq_left, hs1, hs2, QB_e, h0, a_pred M hM hm',
      a_pred M hM hn', sub_zero, zero_sub, abs_neg, abs_zero, Cvs.Route.DilationLatticeCriterion.G_zero, abs_of_nonneg lm0, abs_of_nonneg ln0]
    ring
  · have hnM : n = M := by omega
    simp only [hm', hn', and_self, dite_eq_left, dite_eq_right, not_false_eq_true, hs1, hs2, QB_e, h0,
      a_pred M hM hm', sub_zero, zero_sub, abs_neg, abs_zero, Cvs.Route.DilationLatticeCriterion.G_zero, abs_of_nonneg lm0]
    rw [hnM, abs_sub_comm, abs_of_nonneg (by
      have : Real.log (m:ℝ) ≤ Real.log M := Real.log_le_log (by exact_mod_cast (by omega : 0 < m)) (by exact_mod_cast hm.2)
      linarith : (0:ℝ) ≤ Real.log M - Real.log m)]
    ring
  · have hmM : m = M := by omega
    simp only [hm', hn', and_self, dite_eq_left, dite_eq_right, not_false_eq_true, hs1, hs2, QB_e, h0,
      a_pred M hM hn', sub_zero, zero_sub, abs_neg, abs_zero, Cvs.Route.DilationLatticeCriterion.G_zero, abs_of_nonneg ln0]
    rw [hmM, abs_of_nonneg (by
      have : Real.log (n:ℝ) ≤ Real.log M := Real.log_le_log (by exact_mod_cast (by omega : 0 < n)) (by exact_mod_cast hn.2)
      linarith : (0:ℝ) ≤ Real.log M - Real.log n)]
    ring
  · have hmM : m = M := by omega
    have hnM : n = M := by omega
    simp only [hm', hn', dite_eq_right, not_false_eq_true, QB_e, h0, sub_zero, sub_self, abs_zero, Cvs.Route.DilationLatticeCriterion.G_zero]
    rw [hmM, hnM, sub_self, abs_zero, Cvs.Route.DilationLatticeCriterion.G_zero]
    ring

theorem qf_eq_Q (c : ℕ → ℝ) :
    qf M c = Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg M) M (Nat.clog 2 M) (∑ n ∈ Icc 2 M, c n • fv M hM n) := by
  rw [← Cvs.WeilForm.SymmetricBilinearForm.QWbil_self]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, qf]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [QB_fv M hM hm hn, K_comm]; ring

end forward

theorem boxPSD_of_rh (hRH : RiemannHypothesis) {M : ℕ} (hM : 2 ≤ M) : BoxPSD M := fun c => by
  rw [qf_eq_Q M hM c]
  exact (Cvs.WeilForm.WindowWeilCriterion.rh_iff_windowPos 2 le_rfl).1 hRH M hM _

/-- **RH by induction**: the Riemann hypothesis holds iff every induction step on the nested boxes holds. -/
theorem rh_iff_forall_step : RiemannHypothesis ↔ ∀ N, 1 ≤ N → Step N :=
  ⟨fun h N hN => step_of_boxPSD (boxPSD_of_rh h (by omega)), rh_of_forall_step⟩

end Cvs.Route.NestedBoxInduction
