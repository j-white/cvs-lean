import Mathlib
import Cvs.L2a.TailLogScaleTest
import Cvs.L2a.TailModesPrimeSideBound
import Cvs.L2a.TailOfModes
import Cvs.WeilForm.PrimePowerIndexed
import Cvs.Zeta.PrimePowerSideTruncated
import Cvs.Zeta.WeilPositivityStatement

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The prime side of a combination of tails is bilinear

For `ψ = Σ_j a_j ψ_j` (finite, each `ψ_j` continuous on `[1, Mb]`), the tail of `ψ` is `Σ_j a_j` times the tails of
the `ψ_j`, each prime term expands as `∫F(θ)F(kθ) = Σ_{i,j} a_i a_j ∫F_i(θ)F_j(kθ)`, and the prime side is at most
`Σ_{i,j} |a_i||a_j| Σ_k 2Λ(k)|∫F_i(θ)F_j(kθ)|`.
-/

namespace Cvs.L2a.TailCombinationPrimeBilinear

open Real Set ArithmeticFunction Cvs.L2a.TailOfModes

variable {ι : Type*}

/-- **One prime term of a combination** expands bilinearly. -/
theorem integral_tailF_pair_sum (J : Finset ι) (a : ι → ℝ) (ψ : ι → ℝ → ℝ) (M : ℕ) {b k : ℝ}
    (hk : 1 ≤ k) (hkb : k ≤ b) (hcont : ∀ j ∈ J, ContinuousOn (ψ j) (Icc 1 (M * b))) :
    ∫ θ in Ioi 1, tailF (fun ξ => ∑ j ∈ J, a j * ψ j ξ) M b θ * tailF (fun ξ => ∑ j ∈ J, a j * ψ j ξ) M b (k * θ)
      = ∑ i ∈ J, ∑ j ∈ J, a i * a j * ∫ θ in Ioi 1, tailF (ψ i) M b θ * tailF (ψ j) M b (k * θ) := by
  have hk0 : 0 < k := by linarith
  have hbk : 1 ≤ b / k := by rw [le_div_iff₀ hk0]; linarith
  have hbk' : b / k ≤ b := div_le_self (by linarith) hk
  have hsum : ContinuousOn (fun ξ => ∑ j ∈ J, a j * ψ j ξ) (Icc 1 (M * b)) :=
    continuousOn_finsetSum _ fun j hj => continuousOn_const.mul (hcont j hj)
  -- each mode pair is integrable
  have hint : ∀ i ∈ J, ∀ j ∈ J, ∀ m ∈ Finset.Icc 1 M, ∀ m' ∈ Finset.Icc 1 M,
      IntervalIntegrable (fun θ => ψ i (m * θ) * ψ j (m' * (k * θ))) MeasureTheory.volume 1 (b / k) := by
    intro i hi j hj m hm m' hm'
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
    have hmM : (m : ℝ) ≤ M := by exact_mod_cast (Finset.mem_Icc.mp hm).2
    have hm1' : (1 : ℝ) ≤ m' := by exact_mod_cast (Finset.mem_Icc.mp hm').1
    have hmM' : (m' : ℝ) ≤ M := by exact_mod_cast (Finset.mem_Icc.mp hm').2
    apply ContinuousOn.intervalIntegrable_of_Icc hbk
    apply ContinuousOn.mul
    · exact (hcont i hi).comp (continuousOn_const.mul continuousOn_id) (fun θ hθ =>
        ⟨by nlinarith [hθ.1], by have := hθ.2.trans hbk'; nlinarith⟩)
    · exact (hcont j hj).comp (continuousOn_const.mul (continuousOn_const.mul continuousOn_id)) (fun θ hθ =>
        ⟨one_le_mul_of_one_le_of_one_le hm1' (one_le_mul_of_one_le_of_one_le hk hθ.1), by
          have : k * θ ≤ b := by rw [← le_div_iff₀' hk0]; exact hθ.2
          nlinarith⟩)
  rw [integral_tailF_pair _ _ M hk hkb hsum hsum]
  have e : ∀ m ∈ Finset.Icc 1 M, ∀ m' ∈ Finset.Icc 1 M,
      ∫ θ in (1 : ℝ)..b / k, (∑ j ∈ J, a j * ψ j (m * θ)) * ∑ j ∈ J, a j * ψ j (m' * (k * θ))
        = ∑ i ∈ J, ∑ j ∈ J, a i * a j * ∫ θ in (1 : ℝ)..b / k, ψ i (m * θ) * ψ j (m' * (k * θ)) := by
    intro m hm m' hm'
    have hpt : ∀ θ, (∑ j ∈ J, a j * ψ j (m * θ)) * ∑ j ∈ J, a j * ψ j (m' * (k * θ))
        = ∑ i ∈ J, ∑ j ∈ J, a i * a j * (ψ i (m * θ) * ψ j (m' * (k * θ))) := fun θ => by
      rw [Finset.sum_mul_sum]
      apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; ring
    simp_rw [hpt]
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl; intro i hi
      rw [intervalIntegral.integral_finsetSum]
      · apply Finset.sum_congr rfl; intro j hj
        rw [intervalIntegral.integral_const_mul]
      · intro j hj; exact (hint i hi j hj m hm m' hm').const_mul _
    · intro i hi
      have e3 : (fun θ => ∑ j ∈ J, a i * a j * (ψ i (m * θ) * ψ j (m' * (k * θ))))
          = ∑ j ∈ J, fun θ => a i * a j * (ψ i (m * θ) * ψ j (m' * (k * θ))) := by
        funext θ; simp [Finset.sum_apply]
      rw [e3]
      exact IntervalIntegrable.sum J fun j hj => (hint i hi j hj m hm m' hm').const_mul (a i * a j)
  rw [Finset.sum_congr rfl fun m hm => Finset.sum_congr rfl fun m' hm' => e m hm m' hm']
  have e2 : ∀ i ∈ J, ∀ j ∈ J, ∫ θ in Ioi 1, tailF (ψ i) M b θ * tailF (ψ j) M b (k * θ)
      = ∑ m ∈ Finset.Icc 1 M, ∑ m' ∈ Finset.Icc 1 M, ∫ θ in (1 : ℝ)..b / k, ψ i (m * θ) * ψ j (m' * (k * θ)) :=
    fun i hi j hj => integral_tailF_pair _ _ M hk hkb (hcont i hi) (hcont j hj)
  conv_rhs => rw [Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => by rw [e2 i hi j hj]]
  simp_rw [Finset.mul_sum]
  set f : ι → ι → ℕ → ℕ → ℝ := fun i j m m' => a i * a j * ∫ θ in (1 : ℝ)..b / k, ψ i (m * θ) * ψ j (m' * (k * θ))
  show ∑ m ∈ Finset.Icc 1 M, ∑ m' ∈ Finset.Icc 1 M, ∑ i ∈ J, ∑ j ∈ J, f i j m m'
    = ∑ i ∈ J, ∑ j ∈ J, ∑ m ∈ Finset.Icc 1 M, ∑ m' ∈ Finset.Icc 1 M, f i j m m'
  calc ∑ m ∈ Finset.Icc 1 M, ∑ m' ∈ Finset.Icc 1 M, ∑ i ∈ J, ∑ j ∈ J, f i j m m'
      = ∑ m ∈ Finset.Icc 1 M, ∑ i ∈ J, ∑ m' ∈ Finset.Icc 1 M, ∑ j ∈ J, f i j m m' :=
        Finset.sum_congr rfl fun m _ => Finset.sum_comm
    _ = ∑ i ∈ J, ∑ m ∈ Finset.Icc 1 M, ∑ m' ∈ Finset.Icc 1 M, ∑ j ∈ J, f i j m m' := Finset.sum_comm
    _ = ∑ i ∈ J, ∑ m ∈ Finset.Icc 1 M, ∑ j ∈ J, ∑ m' ∈ Finset.Icc 1 M, f i j m m' :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun m _ => Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun i _ => Finset.sum_comm

/-- **The prime side of a combination of tails**, bilinearly. -/
theorem primeSide_sum_le (J : Finset ι) (a : ι → ℝ) (ψ : ι → ℝ → ℝ) (P R N M : ℕ) {b : ℝ}
    (hidx : Cvs.WeilForm.PrimePowerIndexed.primePowIndex P R ⊆ Finset.Icc 2 N) (hNb : (N : ℝ) ≤ b)
    (hcont : ∀ j ∈ J, ContinuousOn (ψ j) (Icc 1 (M * b))) :
    Cvs.Zeta.Explicit.Weil.primePowerSideTruncated P R
        (Cvs.Zeta.Explicit.Weil.selfConvolution
          (Cvs.L2a.TailLogScaleTest.logScale (tailF (fun ξ => ∑ j ∈ J, a j * ψ j ξ) M b)))
      ≤ ∑ i ∈ J, ∑ j ∈ J, |a i| * |a j| * ∑ k ∈ Cvs.WeilForm.PrimePowerIndexed.primePowIndex P R,
          2 * Λ k * |∫ θ in Ioi 1, tailF (ψ i) M b θ * tailF (ψ j) M b (k * θ)| := by
  rw [Cvs.L2a.TailModesPrimeSideBound.primeSide_eq_image _ (tailF_zero _ M b)]
  have hterm : ∀ k ∈ Cvs.WeilForm.PrimePowerIndexed.primePowIndex P R,
      2 * Λ k * ∫ θ in Ioi 1, tailF (fun ξ => ∑ j ∈ J, a j * ψ j ξ) M b θ
          * tailF (fun ξ => ∑ j ∈ J, a j * ψ j ξ) M b (k * θ)
        ≤ ∑ i ∈ J, ∑ j ∈ J, |a i| * |a j|
          * (2 * Λ k * |∫ θ in Ioi 1, tailF (ψ i) M b θ * tailF (ψ j) M b (k * θ)|) := by
    intro k hk
    have hk2 := Finset.mem_Icc.mp (hidx hk)
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
    have hkN : (k : ℝ) ≤ N := by exact_mod_cast hk2.2
    have hΛ : 0 ≤ 2 * Λ k := by have := (vonMangoldt_nonneg : 0 ≤ Λ k); positivity
    rw [integral_tailF_pair_sum J a ψ M hk1 (hkN.trans hNb) hcont, Finset.mul_sum]
    apply Finset.sum_le_sum; intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro j _
    set I := ∫ θ in Ioi 1, tailF (ψ i) M b θ * tailF (ψ j) M b (k * θ)
    calc 2 * Λ k * (a i * a j * I) ≤ |2 * Λ k * (a i * a j * I)| := le_abs_self _
      _ = |a i| * |a j| * (2 * Λ k * |I|) := by
          rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_two, abs_of_nonneg (vonMangoldt_nonneg : 0 ≤ Λ k)]; ring
  calc _ ≤ ∑ k ∈ Cvs.WeilForm.PrimePowerIndexed.primePowIndex P R, ∑ i ∈ J, ∑ j ∈ J, |a i| * |a j|
          * (2 * Λ k * |∫ θ in Ioi 1, tailF (ψ i) M b θ * tailF (ψ j) M b (k * θ)|) := Finset.sum_le_sum hterm
    _ = _ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro i _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro j _
        rw [Finset.mul_sum]

end Cvs.L2a.TailCombinationPrimeBilinear
