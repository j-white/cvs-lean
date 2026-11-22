import Mathlib
import Cvs.Approximant.SpineSubspace
import Cvs.L2a.WindowChainInputsProlate
import Cvs.Upstream.MergedBoundSchurForm
import Cvs.Upstream.MergedLowerBoundPositivity
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.InfimumAttainedSphere
import Cvs.WeilForm.PositivityOfRH
import Cvs.WeilForm.SymmetricBilinearForm
import Cvs.WeilForm.WeilFormOnWindowL2

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# CORE(x), the zero-margin Schur form of the window Weil form against `R_F`

`CoreAt` is `MergedBoundSchurForm`'s Schur form of `QWbil` on the whole form domain at `b = δ = 0`. Against a
finite-dimensional `R` with `Q > 0` on `R ∖ 0` it is `0 ≤ Q` everywhere, as it is against `⊥`; past
`c₀W ≤ 2πx` (Cvs.L2a.SpineProfileWindowNormPos: `Q > 0` on `R_F ∖ 0`) CORE(x) is CORE against `⊥` and `0 ≤ lam`, `BottomAttained`'s infimum
of `Q` on the unit sphere. RH gives CORE(x) for every `2 ≤ x`.
-/

noncomputable section

open MeasureTheory Real

namespace Cvs.Route.CoreSchurForm
open Cvs.ZeroCounting

/-! ### The Schur form at zero margins -/

/-- The zero-margin Schur form of `QWbil` on the whole form domain, against a subspace `RF`. -/
def CoreAt {L : ℝ} (hL : 0 ≤ L) (P R : ℕ) (RF : Submodule ℝ (Cvs.WeilForm.FormDomain.formDomain hL)) : Prop :=
  @Cvs.Upstream.MergedBoundSchurForm.Schur (Cvs.WeilForm.FormDomain.formDomain hL) (Submodule.normedAddCommGroup _)
    (Submodule.innerProductSpace _) (Cvs.WeilForm.SymmetricBilinearForm.QWbil hL P R) ⊤ RF 0 0

set_option synthInstance.maxHeartbeats 200000 in
/-- **`0 ≤ Q` on the whole form domain gives the zero-margin Schur form** against any subspace. -/
theorem coreAt_of_nonneg {L : ℝ} (hL : 0 ≤ L) (P R : ℕ) (RF : Submodule ℝ (Cvs.WeilForm.FormDomain.formDomain hL))
    (h : ∀ φ, 0 ≤ Cvs.WeilForm.InfimumAttainedSphere.Q hL P R φ) : CoreAt hL P R RF := by
  let instN : NormedAddCommGroup ↥(Cvs.WeilForm.FormDomain.formDomain hL) := Submodule.normedAddCommGroup _
  let instI : InnerProductSpace ℝ ↥(Cvs.WeilForm.FormDomain.formDomain hL) := Submodule.innerProductSpace _
  unfold CoreAt
  refine Cvs.Upstream.MergedBoundSchurForm.schur_of_merged (Cvs.WeilForm.SymmetricBilinearForm.QWbil_isSymm _ _ _) ?_ (by norm_num)
  intro r _ w _ _
  simp only [zero_mul, zero_add]
  rw [Cvs.WeilForm.SymmetricBilinearForm.QWbil_self]; exact h _

/-- The additive group structure on a subspace of the form domain, given explicitly: instance search
cannot unify the nested submodule instances through the `Lp` ambient space. -/
instance formDomainSub.addCommGroup {L : ℝ} {hL : 0 ≤ L}
    (RF : Submodule ℝ (Cvs.WeilForm.FormDomain.formDomain hL)) : AddCommGroup RF :=
  @Submodule.addCommGroup ℝ _ _ (Submodule.addCommGroup _) (Submodule.module _) RF

set_option synthInstance.maxHeartbeats 200000 in
/-- **The zero-margin Schur form is `0 ≤ Q` on the whole form domain** when `RF` is
finite-dimensional and `Q > 0` on its nonzero vectors. -/
theorem coreAt_iff_nonneg {L : ℝ} (hL : 0 ≤ L) (P R : ℕ)
    (RF : Submodule ℝ (Cvs.WeilForm.FormDomain.formDomain hL)) [FiniteDimensional ℝ RF]
    (hpos : ∀ r ∈ RF, r ≠ 0 → 0 < Cvs.WeilForm.InfimumAttainedSphere.Q hL P R r) :
    CoreAt hL P R RF ↔ ∀ φ, 0 ≤ Cvs.WeilForm.InfimumAttainedSphere.Q hL P R φ := by
  let instN : NormedAddCommGroup ↥(Cvs.WeilForm.FormDomain.formDomain hL) := Submodule.normedAddCommGroup _
  let instI : InnerProductSpace ℝ ↥(Cvs.WeilForm.FormDomain.formDomain hL) := Submodule.innerProductSpace _
  have hpos' : ∀ r ∈ RF, r ≠ 0 → 0 < Cvs.WeilForm.SymmetricBilinearForm.QWbil hL P R r r := fun r hr h0 => by
    rw [Cvs.WeilForm.SymmetricBilinearForm.QWbil_self]; exact hpos r hr h0
  refine ⟨fun hc φ => ?_, coreAt_of_nonneg hL P R RF⟩
  unfold CoreAt at hc
  have hm := (Cvs.Upstream.MergedBoundSchurForm.merged_iff_schur (Cvs.WeilForm.SymmetricBilinearForm.QWbil_isSymm hL P R) hpos'
    (by norm_num : (0:ℝ) < 1)).2 hc
  rw [← Cvs.WeilForm.SymmetricBilinearForm.QWbil_self]
  exact Cvs.Upstream.MergedLowerBoundPositivity.nonneg_of_merged (Q := fun x => Cvs.WeilForm.SymmetricBilinearForm.QWbil hL P R x x)
    (Cvs.Upstream.MergedBoundSchurForm.merged_iff_diag.mp hm) le_top le_rfl le_rfl (by norm_num) (Submodule.mem_top)

/-! ### CORE(x) at the spine scale -/

/-- **CORE(x)**: the zero-margin Schur form of `QWbil` at `L = log x`, `P = x`, `R = ⌈log₂ x⌉`,
on the whole form domain, against `R_F` (which is `⊥` below `80 ≤ 2πx`). -/
def Core (x : ℕ) : Prop :=
  CoreAt (Real.log_natCast_nonneg x) x (Nat.clog 2 x) (Cvs.Approximant.SpineSubspace.RF x)

/-- **CORE(x) is `0 ≤ Q` on the whole form domain**, past `c₀W ≤ 2πx`. -/
theorem core_iff_nonneg (x : ℕ) (hx : Cvs.L2a.WindowChainInputsProlate.c0W ≤ 2 * π * x) :
    Core x ↔ ∀ φ : Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x),
      0 ≤ Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) x (Nat.clog 2 x) φ :=
  coreAt_iff_nonneg _ _ _ (Cvs.Approximant.SpineSubspace.RF x) (Cvs.Approximant.SpineSubspace.RF_pos x hx)

/-- Under RH, `0 ≤ Q` on the whole form domain at `L = log x`, for `2 ≤ x`. -/
theorem nonneg_of_rh (hRH : RiemannHypothesis) (x : ℕ) (hx : 2 ≤ x) :
    ∀ φ : Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x),
      0 ≤ Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) x (Nat.clog 2 x) φ := by
  obtain ⟨hL, hP, hR⟩ := Cvs.Approximant.SpineSubspace.sizes x hx
  exact Cvs.WeilForm.PositivityOfRH.Q_nonneg_of_RH hRH hL hP hR

/-- **RH gives CORE(x)** for every `2 ≤ x`. -/
theorem core_of_rh (hRH : RiemannHypothesis) (x : ℕ) (hx : 2 ≤ x) : Core x :=
  coreAt_of_nonneg _ _ _ _ (nonneg_of_rh hRH x hx)

/-- The threshold `c₀W ≤ 2πx` forces `2 ≤ x`. -/
theorem two_le_of_c0W {x : ℕ} (hx : Cvs.L2a.WindowChainInputsProlate.c0W ≤ 2 * π * x) : 2 ≤ x := by
  have h80 := Cvs.Approximant.SpineSubspace.scale80_of_c0W hx
  have : (2 : ℝ) ≤ x := by nlinarith [Real.pi_lt_four]
  exact_mod_cast this

end Cvs.Route.CoreSchurForm
