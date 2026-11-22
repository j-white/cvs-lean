import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# Riemann's kernel `Φ`

`Φ(u) = ∑_{n ≥ 1} (2π²n⁴e^{9u/2} − 3πn²e^{5u/2}) e^{−πn²e^{2u}}` is the kernel of the cosine
representation of `Ξ`. Its defining series converges at every `u`, every term is positive for `0 ≤ u`,
and on `[0, ∞)` the sum is at most `e^{9u/2}e^{−πe^{2u}}` times a constant given as an explicit series.
-/

open Real

namespace Cvs.Xi.RiemannPhiKernel

/-- The `n`-th term of Riemann's kernel. -/
noncomputable def phiTerm (n : ℕ) (u : ℝ) : ℝ :=
  (2 * π ^ 2 * (n : ℝ) ^ 4 * exp (9 * u / 2) - 3 * π * (n : ℝ) ^ 2 * exp (5 * u / 2))
    * exp (-(π * (n : ℝ) ^ 2 * exp (2 * u)))

/-- The factored form, with the sign of the term carried by `2πn²e^{2u} − 3`. -/
theorem phiTerm_eq (n : ℕ) (u : ℝ) :
    phiTerm n u = π * (n : ℝ) ^ 2 * exp (5 * u / 2) * (2 * π * (n : ℝ) ^ 2 * exp (2 * u) - 3)
      * exp (-(π * (n : ℝ) ^ 2 * exp (2 * u))) := by
  have h : exp (9 * u / 2) = exp (5 * u / 2) * exp (2 * u) := by
    rw [← Real.exp_add]; ring_nf
  unfold phiTerm
  rw [h]; ring

theorem cast_le_sq (n : ℕ) : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
  rcases Nat.eq_zero_or_pos n with h | h
  · simp [h]
  · have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) n) (sub_nonneg.mpr h1)]

theorem cast_sq_le_pow_four (n : ℕ) : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 4 := by
  rcases Nat.eq_zero_or_pos n with h | h
  · simp [h]
  · have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
    have h2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
    nlinarith [mul_nonneg (sq_nonneg ((n : ℝ))) (sub_nonneg.mpr h2)]

/-- **Every term is positive on `[0, ∞)`.** -/
theorem phiTerm_pos {n : ℕ} (hn : 1 ≤ n) {u : ℝ} (hu : 0 ≤ u) : 0 < phiTerm n u := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have hX : (1 : ℝ) ≤ exp (2 * u) := Real.one_le_exp (by linarith)
  have hpi : (3 : ℝ) < π := Real.pi_gt_three
  have hprod : (1 : ℝ) ≤ (n : ℝ) ^ 2 * exp (2 * u) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hn2) (sub_nonneg.mpr hX)]
  have hfac : 0 < 2 * π * (n : ℝ) ^ 2 * exp (2 * u) - 3 := by
    nlinarith [mul_le_mul_of_nonneg_left hprod (by positivity : (0 : ℝ) ≤ 2 * π)]
  have h1 : 0 < π * (n : ℝ) ^ 2 * exp (5 * u / 2) := by positivity
  rw [phiTerm_eq]
  exact mul_pos (mul_pos h1 hfac) (Real.exp_pos _)

/-- The term is dominated by `n⁴e^{−πe^{2u}n}`, which is summable. -/
theorem abs_phiTerm_le (n : ℕ) (u : ℝ) :
    |phiTerm n u| ≤ (2 * π ^ 2 * exp (9 * u / 2) + 3 * π * exp (5 * u / 2))
      * ((n : ℝ) ^ 4 * exp (-(π * exp (2 * u)) * (n : ℝ))) := by
  have hpi := Real.pi_pos
  have he1 : (0 : ℝ) < exp (9 * u / 2) := Real.exp_pos _
  have he2 : (0 : ℝ) < exp (5 * u / 2) := Real.exp_pos _
  have he : (0 : ℝ) < exp (2 * u) := Real.exp_pos _
  have h4 : (0 : ℝ) ≤ (n : ℝ) ^ 4 := by positivity
  have hstep1 : |2 * π ^ 2 * (n : ℝ) ^ 4 * exp (9 * u / 2) - 3 * π * (n : ℝ) ^ 2 * exp (5 * u / 2)|
      ≤ (2 * π ^ 2 * exp (9 * u / 2) + 3 * π * exp (5 * u / 2)) * (n : ℝ) ^ 4 := by
    have h2 := cast_sq_le_pow_four n
    have hsq : (0 : ℝ) ≤ (n : ℝ) ^ 2 := by positivity
    have hB : (0 : ℝ) ≤ 3 * π * (n : ℝ) ^ 2 * exp (5 * u / 2) := by positivity
    have hgap : (0 : ℝ) ≤ 3 * π * exp (5 * u / 2) * ((n : ℝ) ^ 4 - (n : ℝ) ^ 2) :=
      mul_nonneg (by positivity) (sub_nonneg.mpr h2)
    have hA : (0 : ℝ) ≤ 2 * π ^ 2 * (n : ℝ) ^ 4 * exp (9 * u / 2) := by positivity
    rw [abs_le]
    constructor <;> nlinarith [hA, hgap, hB]
  have hstep2 : exp (-(π * (n : ℝ) ^ 2 * exp (2 * u))) ≤ exp (-(π * exp (2 * u)) * (n : ℝ)) := by
    apply Real.exp_le_exp.mpr
    have h := cast_le_sq n
    nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ π * exp (2 * u)) (sub_nonneg.mpr h)]
  calc |phiTerm n u|
      = |2 * π ^ 2 * (n : ℝ) ^ 4 * exp (9 * u / 2) - 3 * π * (n : ℝ) ^ 2 * exp (5 * u / 2)|
          * exp (-(π * (n : ℝ) ^ 2 * exp (2 * u))) := by
        unfold phiTerm
        rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    _ ≤ ((2 * π ^ 2 * exp (9 * u / 2) + 3 * π * exp (5 * u / 2)) * (n : ℝ) ^ 4)
          * exp (-(π * exp (2 * u)) * (n : ℝ)) :=
        mul_le_mul hstep1 hstep2 (Real.exp_pos _).le (by positivity)
    _ = (2 * π ^ 2 * exp (9 * u / 2) + 3 * π * exp (5 * u / 2))
          * ((n : ℝ) ^ 4 * exp (-(π * exp (2 * u)) * (n : ℝ))) := by ring

/-- **The defining series converges at every `u`.** -/
theorem summable_phiTerm (u : ℝ) : Summable (fun n : ℕ => phiTerm n u) := by
  have hX : 0 < π * exp (2 * u) := by positivity
  refine Summable.of_norm_bounded
    ((Real.summable_pow_mul_exp_neg_nat_mul 4 hX).mul_left
      (2 * π ^ 2 * exp (9 * u / 2) + 3 * π * exp (5 * u / 2))) (fun n => ?_)
  simpa [Real.norm_eq_abs] using abs_phiTerm_le n u

/-- **Riemann's kernel `Φ`.** -/
noncomputable def riemannPhi (u : ℝ) : ℝ := ∑' n : ℕ, phiTerm (n + 1) u

theorem summable_shifted (u : ℝ) : Summable (fun n : ℕ => phiTerm (n + 1) u) :=
  (summable_nat_add_iff 1).mpr (summable_phiTerm u)

/-- **`Φ` is positive on `[0, ∞)`.** -/
theorem riemannPhi_pos {u : ℝ} (hu : 0 ≤ u) : 0 < riemannPhi u := by
  have hfirst : phiTerm (0 + 1) u ≤ riemannPhi u := by
    have h := Summable.sum_le_tsum (f := fun n : ℕ => phiTerm (n + 1) u) {0}
      (fun i _ => (phiTerm_pos (Nat.le_add_left 1 i) hu).le) (summable_shifted u)
    simpa [riemannPhi] using h
  exact lt_of_lt_of_le (phiTerm_pos (Nat.le_add_left 1 0) hu) hfirst

/-- The shifted comparison series of the edge bound. -/
theorem summable_phiBoundTerm :
    Summable (fun n : ℕ => ((n : ℝ) + 1) ^ 4 * exp (-(π * ((n : ℝ) + 1) ^ 2))) := by
  have hbase : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ 4 * exp (-π * ((n : ℝ) + 1))) := by
    have h := (summable_nat_add_iff 1).mpr (Real.summable_pow_mul_exp_neg_nat_mul 4 Real.pi_pos)
    refine h.congr (fun n => ?_)
    push_cast
    ring_nf
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hbase
  have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have := Nat.cast_nonneg (α := ℝ) n; linarith
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
  have hpi := Real.pi_pos
  nlinarith [mul_nonneg hpi.le (mul_nonneg (by linarith : (0 : ℝ) ≤ (n : ℝ) + 1)
    (sub_nonneg.mpr h1))]

/-- The constant of the edge bound, as the series it is. -/
noncomputable def phiBoundConst : ℝ :=
  2 * π ^ 2 * exp π * ∑' n : ℕ, ((n : ℝ) + 1) ^ 4 * exp (-(π * ((n : ℝ) + 1) ^ 2))

/-- Splitting `e^{−πm²X}` into its value at the edge and a factor free of `X`. -/
theorem exp_sq_le {X m : ℝ} (hX : 1 ≤ X) (hm : 1 ≤ m) :
    exp (-(π * m ^ 2 * X)) ≤ exp π * exp (-(π * m ^ 2)) * exp (-(π * X)) := by
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hpi := Real.pi_pos
  have hm2 : (0 : ℝ) ≤ m ^ 2 - 1 := by nlinarith
  nlinarith [mul_nonneg hpi.le (mul_nonneg hm2 (sub_nonneg.mpr hX))]

/-- Each term is at most its edge value times a summable factor. -/
theorem phiTerm_le_bound {u : ℝ} (hu : 0 ≤ u) (n : ℕ) :
    phiTerm (n + 1) u
      ≤ (2 * π ^ 2 * exp π * exp (9 * u / 2) * exp (-(π * exp (2 * u))))
        * (((n : ℝ) + 1) ^ 4 * exp (-(π * ((n : ℝ) + 1) ^ 2))) := by
  have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  have hm : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hX : (1 : ℝ) ≤ exp (2 * u) := Real.one_le_exp (by linarith)
  have hpi := Real.pi_pos
  have hdrop : phiTerm (n + 1) u
      ≤ 2 * π ^ 2 * ((n : ℝ) + 1) ^ 4 * exp (9 * u / 2)
        * exp (-(π * ((n : ℝ) + 1) ^ 2 * exp (2 * u))) := by
    unfold phiTerm
    rw [hcast, sub_mul]
    have hsub : (0 : ℝ) ≤ 3 * π * ((n : ℝ) + 1) ^ 2 * exp (5 * u / 2)
        * exp (-(π * ((n : ℝ) + 1) ^ 2 * exp (2 * u))) := by positivity
    linarith
  refine hdrop.trans ?_
  have hsplit := exp_sq_le (X := exp (2 * u)) (m := (n : ℝ) + 1) hX hm
  have hcoef : (0 : ℝ) ≤ 2 * π ^ 2 * ((n : ℝ) + 1) ^ 4 * exp (9 * u / 2) := by positivity
  calc 2 * π ^ 2 * ((n : ℝ) + 1) ^ 4 * exp (9 * u / 2)
        * exp (-(π * ((n : ℝ) + 1) ^ 2 * exp (2 * u)))
      ≤ 2 * π ^ 2 * ((n : ℝ) + 1) ^ 4 * exp (9 * u / 2)
        * (exp π * exp (-(π * ((n : ℝ) + 1) ^ 2)) * exp (-(π * exp (2 * u)))) :=
        mul_le_mul_of_nonneg_left hsplit hcoef
    _ = (2 * π ^ 2 * exp π * exp (9 * u / 2) * exp (-(π * exp (2 * u))))
        * (((n : ℝ) + 1) ^ 4 * exp (-(π * ((n : ℝ) + 1) ^ 2))) := by ring

/-- **The edge bound.** On `[0, ∞)` the kernel is at most `e^{9u/2}e^{−πe^{2u}}` times a constant. -/
theorem riemannPhi_le {u : ℝ} (hu : 0 ≤ u) :
    riemannPhi u ≤ phiBoundConst * exp (9 * u / 2) * exp (-(π * exp (2 * u))) := by
  have h := (summable_shifted u).tsum_le_tsum (phiTerm_le_bound hu)
    (summable_phiBoundTerm.mul_left
      (2 * π ^ 2 * exp π * exp (9 * u / 2) * exp (-(π * exp (2 * u)))))
  rw [tsum_mul_left] at h
  refine h.trans_eq ?_
  unfold phiBoundConst
  ring

end Cvs.Xi.RiemannPhiKernel
