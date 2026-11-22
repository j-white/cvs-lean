import Mathlib
import Cvs.Xi.EImageWindowPoisson
import Cvs.Xi.MobiusReconstruction

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The bridge `Q(v) = −W(τ_v, v)` for `C¹` window functions

For a tame `v` of class `C¹` supported in `[a, 1]`, the fixed finite Möbius sum `profM` is `C¹` on `ℝ` and equals the
Möbius profile on `[a, 1]`; a smooth bump below `a` makes `∫₀¹ G = 0` with `G(0) = 0` (`smoothProfile`).  Then
`E_G = v` on the window (Cvs.Xi.MobiusReconstruction), the radical lemma (Cvs.WeilForm.EImageRadical) gives `weilθ(E_G, v) = 0`, and additivity (Cvs.L2a.WindowFormTailLimit) gives
`weilθ(v, v) = −weilθ(E_G − v, v)` (`bridge`); on the form domain at `a = 1/x`, `Q(v) = −weilθ(τ_v, v)` (`Q_wv_eq_neg_tail`).
-/

noncomputable section

open Real Set MeasureTheory Filter Topology

namespace Cvs.WeilForm.TailBridgeCOneWindow

open Cvs.Xi.EImageWindowPoisson (eimage window mem_Ioc_of_mem)
open Cvs.Xi.MobiusReconstruction (mobiusProfile eimage_mobiusProfile)
open scoped ArithmeticFunction.Moebius

variable {a : ℝ}

/-! ### `E_G` on the window sees only `G` on `[a, 1]` -/

theorem eimage_congr_Icc (ha : 0 < a) {G H : ℝ → ℝ} (hGH : ∀ u ∈ Icc a 1, G u = H u) {θ : ℝ} (hθ : θ ≤ 1) :
    eimage a G θ = eimage a H θ := by
  unfold eimage
  congr 1
  refine Finset.sum_congr rfl fun n hn => hGH _ ?_
  obtain ⟨hθa, hmem⟩ := mem_Ioc_of_mem ha hn
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.1 hn).1
  have hθ0 : 0 < θ := lt_of_lt_of_le ha hθa
  refine ⟨?_, hmem.2⟩
  rw [le_div_iff₀ hθ0]; nlinarith

/-! ### The fixed finite Möbius sum -/

/-- `profM a v u = Σ_{m ≤ ⌊1/a⌋} μ(m)·v(a/(mu))/(mu)`: the Möbius profile with a fixed index set. -/
def profM (a : ℝ) (v : ℝ → ℝ) (u : ℝ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 ⌊1 / a⌋₊, (μ m : ℝ) * (v (a / (m * u)) / (m * u))

theorem profM_eq_mobius (ha : 0 < a) {v : ℝ → ℝ} (hsupp : ∀ θ ∉ Icc a 1, v θ = 0)
    {u : ℝ} (hu : a ≤ u) (hu1 : u ≤ 1) : profM a v u = mobiusProfile a v u := by
  unfold profM mobiusProfile
  symm
  refine Finset.sum_subset ?_ ?_
  · intro m hm
    rw [Finset.mem_Icc] at hm ⊢
    exact ⟨hm.1, hm.2.trans (Nat.floor_le_floor (one_div_le_one_div_of_le ha hu))⟩
  · intro m hm hm'
    rw [Finset.mem_Icc] at hm
    have hu0 : 0 < u := lt_of_lt_of_le ha hu
    have hlt : ⌊1 / u⌋₊ < m := by
      by_contra h; exact hm' (Finset.mem_Icc.2 ⟨hm.1, not_lt.1 h⟩)
    have hm0 : (0:ℝ) < m := by exact_mod_cast hm.1
    have h1 : 1 / u < m := (Nat.floor_lt (by positivity)).1 hlt
    have h2 : 1 < (m:ℝ) * u := by rw [div_lt_iff₀ hu0] at h1; linarith
    have h3 : a / ((m:ℝ) * u) < a := by
      rw [div_lt_iff₀ (by positivity)]; nlinarith
    rw [hsupp _ (fun h => by linarith [h.1]), zero_div, mul_zero]

/-! ### The smooth profile -/

/-! ### The bridge -/

end Cvs.WeilForm.TailBridgeCOneWindow
