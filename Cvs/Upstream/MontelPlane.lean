import Mathlib
import Cvs.Upstream.EntireFamilyRelativelyCompact

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Montel's theorem on the plane

Tychonoff over the balls of natural radius turns one compact closure per ball into a single
subsequence converging on every ball at once, and the limits are assembled by reading the value at
`z` off the ball whose radius is the ceiling of `‖z‖`, uniqueness of limits making the choice
harmless.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Set Metric Filter Bornology BoundedContinuousFunction

namespace Cvs.Upstream.MontelPlane

/-- **Montel's theorem**: a locally bounded family of entire functions has a subsequence
converging locally uniformly on the plane. -/
theorem exists_subseq_tendstoLocallyUniformlyOn {F : ℕ → ℂ → ℂ}
    (hd : ∀ n, Differentiable ℂ (F n))
    (hbd : ∀ R : ℝ, ∃ M : ℝ, ∀ (n : ℕ) (z : ℂ), ‖z‖ ≤ R → ‖F n z‖ ≤ M) :
    ∃ (φ : ℕ → ℕ) (f : ℂ → ℂ), StrictMono φ ∧
      TendstoLocallyUniformlyOn (fun k => F (φ k)) f atTop Set.univ := by
  classical
  choose M hM using hbd
  -- one compact closure per ball of natural radius
  set G : ∀ m : ℕ, ℕ → ↥(closedBall (0 : ℂ) (m : ℝ)) →ᵇ ℂ :=
    fun m => Cvs.Upstream.EntireFamilyRelativelyCompact.restrictBCF (m : ℝ) (fun i => (hd i).continuous) with hG
  have hcpt : ∀ m : ℕ, IsCompact (closure (Set.range (G m))) := by
    intro m
    exact Cvs.Upstream.EntireFamilyRelativelyCompact.isCompact_closure_range (r := (m : ℝ)) (δ := 1)
      (M := M ((m : ℝ) + 1)) hd one_pos (fun n z hz => hM ((m : ℝ) + 1) n z hz)
  -- Tychonoff on the product supplies the diagonal
  have hpi : IsCompact (Set.pi univ fun m : ℕ => closure (Set.range (G m))) :=
    isCompact_univ_pi hcpt
  have hmem : ∀ n : ℕ, (fun m : ℕ => G m n) ∈
      Set.pi univ fun m : ℕ => closure (Set.range (G m)) :=
    fun n m _ => subset_closure (Set.mem_range_self n)
  obtain ⟨g, -, φ, hφ, hlim⟩ := hpi.tendsto_subseq hmem
  have hcoord : ∀ m : ℕ, Tendsto (fun k => G m (φ k)) atTop (nhds (g m)) :=
    fun m => tendsto_pi_nhds.mp hlim m
  -- the limit on each ball, extended to the plane by zero
  set E : ℕ → ℂ → ℂ :=
    fun m z => if h : z ∈ closedBall (0 : ℂ) (m : ℝ) then g m ⟨z, h⟩ else 0 with hE
  have huniform : ∀ m : ℕ, TendstoUniformlyOn (fun k => F (φ k)) (E m) atTop
      (closedBall (0 : ℂ) (m : ℝ)) := by
    intro m
    rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
    have h := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp (hcoord m)
    have hf : (E m ∘ ((↑) : ↥(closedBall (0 : ℂ) (m : ℝ)) → ℂ)) = ⇑(g m) := by
      funext x
      simp only [hE, Function.comp_apply, dif_pos x.2, Subtype.coe_eta]
    rw [hf]
    exact h
  -- read the value at `z` off the ball whose radius is `⌈‖z‖⌉₊`
  refine ⟨φ, fun z => E ⌈‖z‖⌉₊ z, hφ, ?_⟩
  have hptw : ∀ z : ℂ, Tendsto (fun k => F (φ k) z) atTop (nhds (E ⌈‖z‖⌉₊ z)) := by
    intro z
    refine (huniform ⌈‖z‖⌉₊).tendsto_at ?_
    simpa [mem_closedBall_zero_iff] using Nat.le_ceil ‖z‖
  have hall : ∀ m : ℕ, TendstoUniformlyOn (fun k => F (φ k)) (fun z => E ⌈‖z‖⌉₊ z) atTop
      (closedBall (0 : ℂ) (m : ℝ)) := by
    intro m
    refine (huniform m).congr_right fun z hz => ?_
    exact tendsto_nhds_unique ((huniform m).tendsto_at hz) (hptw z)
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ]
  intro K _ hK
  obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  exact (hall ⌈r⌉₊).mono (hr.trans (closedBall_subset_closedBall (Nat.le_ceil r)))

end Cvs.Upstream.MontelPlane
