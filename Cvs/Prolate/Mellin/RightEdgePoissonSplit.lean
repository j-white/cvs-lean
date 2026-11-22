import Mathlib
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.Approximant.SpineCouplingTailPairing
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.FullSpanIndexFloor
import Cvs.L2a.FullTailPolarisation
import Cvs.Prolate.Envelope.RungExteriorLaw
import Cvs.Prolate.EvenLevelIndexLemma
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.LiouvilleGreen.SoninFunction
import Cvs.Prolate.Mellin.RayTransformEdgeSum
import Cvs.Prolate.Mellin.RightEdgeIntegralPart
import Cvs.Prolate.Mellin.RungWindowLawRightEdge
import Cvs.Prolate.RungProfileEntireExtension
import Cvs.Prolate.RungWindowProfileCells
import Cvs.Prolate.SlepianCommutingRelation
import Cvs.Upstream.PeriodicAliasingIdentity

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The Poisson split of the right-edge sum, and the alias terms at the edge scale

Cvs.Upstream.PeriodicAliasingIdentity applied to `t ↦ G_j(tζ)` gives, for every `ζ ∈ ℂ`,
`H(ζ) = F(ζ) + (G_j(ζ) − G_j(0))/(2x) + Σ_{m ≥ 1} W_m(ζ)`, `W_m(ζ) = ∫_{−1}^{1} G_j(tζ) cos(2πxmt) dt`.
At `ζ = 1`, `W_m(1) = ψ_{G_j}(m)` is the cosine transform of the in-band profile at an integer outside the band,
and Sonin's function (Cvs.Prolate.LiouvilleGreen.SoninFunction) bounds it by the edge values: `|ψ_{G_j}(ξ)| ≤ |μ_{4j}h_{4j}(1)| + |α_jμ₀h₀(1)| ≤ E_j/√x`.
-/

noncomputable section

open Real Set MeasureTheory Filter Complex Topology
open Cvs.Prolate.RungProfileEntireExtension (GC psiC)
open Cvs.Prolate.RungWindowProfileCells (Gr)
open Cvs.Prolate.Mellin.RayTransformEdgeSum (edgeSum)
open Cvs.Prolate.Mellin.RightEdgeIntegralPart (intG)
open Cvs.Prolate.EvenRungsByIndex (rung muR lamR lev IsLevelIdx)
open Cvs.L2a.AngularProlateTailPositive (psi)

namespace Cvs.Prolate.Mellin.RightEdgePoissonSplit
open Cvs.ZeroCounting

/-- The `m`-th alias term `W_m(ζ) = ∫_{−1}^{1} G_j(tζ) cos(2πx(m + 1)t) dt`, `m ≥ 0`. -/
def aliasW (x j m : ℕ) (ζ : ℂ) : ℂ :=
  ∫ t in (-1 : ℝ)..1, GC x j (t * ζ) * Complex.cos (2 * π * x * (m + 1) * t)

/-- `ψ_g` is even. -/
theorem psiC_neg (c : ℝ) (g : ℝ → ℝ) (z : ℂ) : psiC c g (-z) = psiC c g z := by
  unfold psiC
  refine intervalIntegral.integral_congr fun u _ => ?_
  rw [show (c : ℂ) * -z * u = -(c * z * u) by ring, Complex.cos_neg]

/-- `G_j` is even. -/
theorem GC_neg (x j : ℕ) (z : ℂ) : GC x j (-z) = GC x j z := by
  unfold GC; rw [psiC_neg, psiC_neg]

/-- **The Poisson split of the right-edge sum**: for every `ζ`,
`Σ_{m ≥ 0} W_m(ζ) = H(ζ) − F(ζ) − (G_j(ζ) − G_j(0))/(2x)`. -/
theorem hasSum_aliasW {x j : ℕ} (hx : 80 ≤ 2 * π * x) (hj : j < x) (ζ : ℂ) :
    HasSum (fun m => aliasW x j m ζ)
      (edgeSum x j ζ - intG x j ζ - (GC x j ζ - GC x j 0) / (2 * x)) := by
  have hx0 : 0 < x := by exact_mod_cast Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx
  have hG := Cvs.Prolate.RungProfileEntireExtension.differentiable_GC hx hj
  have hG1 := hG.deriv
  have hG2 := hG1.deriv
  have hl : ∀ t : ℝ, HasDerivAt (fun y : ℝ => (y : ℂ) * ζ) ζ t := fun t => by
    simpa using ((hasDerivAt_id (t : ℂ)).mul_const ζ).comp_ofReal
  have hf : ∀ t ∈ uIcc (-1 : ℝ) 1, HasDerivAt (fun t : ℝ => GC x j (t * ζ)) (deriv (GC x j) (t * ζ) * ζ) t :=
    fun t _ => (hG _).hasDerivAt.comp t (hl t)
  have hf₁ : ∀ t ∈ uIcc (-1 : ℝ) 1, HasDerivAt (fun t : ℝ => deriv (GC x j) (t * ζ) * ζ)
      (deriv (deriv (GC x j)) (t * ζ) * ζ * ζ) t :=
    fun t _ => ((hG1 _).hasDerivAt.comp t (hl t)).mul_const ζ
  have hc2 := hG2.continuous
  have hf₂c : Continuous fun t : ℝ => deriv (deriv (GC x j)) (t * ζ) * ζ * ζ := by fun_prop
  have hf₂ : ContinuousOn (fun t : ℝ => deriv (deriv (GC x j)) (t * ζ) * ζ * ζ) (uIcc (-1) 1) :=
    hf₂c.continuousOn
  have hev : ∀ t ∈ Icc (-1 : ℝ) 1, GC x j (((-t : ℝ) : ℂ) * ζ) = GC x j (t * ζ) := fun t _ => by
    rw [show ((-t : ℝ) : ℂ) * ζ = -((t : ℂ) * ζ) by push_cast; ring, GC_neg]
  have h := Cvs.Upstream.PeriodicAliasingIdentity.hasSum_alias_even hf hf₁ hf₂ hev hx0
  unfold aliasW
  convert h using 1
  unfold edgeSum intG
  simp only [Complex.ofReal_one, one_mul, Complex.ofReal_zero, zero_mul, Complex.ofReal_div,
    Complex.ofReal_natCast]

/-- At the edge, the alias term is the cosine transform of the profile at the integer `m + 1`. -/
theorem aliasW_one {x j : ℕ} (hx : 80 ≤ 2 * π * x) (hj : j < x) (m : ℕ) :
    aliasW x j m 1 = ((psi (2 * π * x) (Gr x j) (m + 1) : ℝ) : ℂ) := by
  unfold aliasW psi Cvs.Prolate.SlepianCommutingRelation.kint
  rw [← intervalIntegral.integral_ofReal]
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [uIcc_of_le (by norm_num)] at ht
  simp only [mul_one]
  rw [Cvs.Prolate.RungProfileEntireExtension.GC_ofReal hx hj ht]
  push_cast
  unfold Gr
  push_cast
  ring_nf

/-- **The Poisson identity at the edge**: `Σ_{m ≥ 1} ψ_{G_j}(m) = (1/x)Σ_{n ≤ x} G_j(n/x) − (G_j(1) − G_j(0))/(2x)`. -/
theorem hasSum_psi_Gr {x j : ℕ} (hx : 80 ≤ 2 * π * x) (hj : j < x) :
    HasSum (fun m : ℕ => psi (2 * π * x) (Gr x j) (m + 1))
      (1 / x * ∑ n ∈ Finset.Icc 1 x, Gr x j (n / x) - (Gr x j 1 - Gr x j 0) / (2 * x)) := by
  have h := hasSum_aliasW hx hj 1
  simp_rw [aliasW_one hx hj] at h
  rw [Cvs.Prolate.Mellin.RayTransformEdgeSum.edgeSum_one hx hj, Cvs.Prolate.Mellin.RightEdgeIntegralPart.intG_one hx hj] at h
  have h1 : GC x j 1 = ((Gr x j 1 : ℝ) : ℂ) := by
    have := Cvs.Prolate.RungProfileEntireExtension.GC_ofReal hx hj (s := 1) ⟨by norm_num, le_rfl⟩
    simpa [Gr] using this
  have h0 : GC x j 0 = ((Gr x j 0 : ℝ) : ℂ) := by
    have := Cvs.Prolate.RungProfileEntireExtension.GC_ofReal hx hj (s := 0) ⟨by norm_num, by norm_num⟩
    simpa [Gr] using this
  rw [h1, h0] at h
  have e : ((1 / x * ∑ n ∈ Finset.Icc 1 x, Gr x j (n / x) : ℝ) : ℂ) - 0 - (((Gr x j 1 : ℝ) : ℂ)
      - ((Gr x j 0 : ℝ) : ℂ)) / (2 * x)
      = ((1 / x * ∑ n ∈ Finset.Icc 1 x, Gr x j (n / x) - (Gr x j 1 - Gr x j 0) / (2 * x) : ℝ) : ℂ) := by
    push_cast; ring
  rw [e] at h
  exact Complex.hasSum_ofReal.1 h

/-- **Sonin outside the band**: a rung's cosine transform never exceeds its edge value beyond `1`. -/
theorem abs_psi_rung_le {c : ℝ} {k : ℕ} (h : ∃ χ, IsLevelIdx c k χ) (hχ : lev c k < c ^ 2) {ξ : ℝ} (hξ : 1 ≤ ξ) :
    |psi c (rung c k) ξ| ≤ |muR c k| * |rung c k 1| := by
  obtain ⟨hg, hg₁, hg₂c, hang, -, -⟩ := Cvs.Prolate.EvenRungsByIndex.rung_spec h
  obtain ⟨hψ, hv, hode⟩ := Cvs.L2a.AngularProlateTailPositive.psi_system hg hg₁ hg₂c hang
  have hs := Cvs.Prolate.LiouvilleGreen.SoninFunction.prolate_sq_le_edge hχ ⟨hξ, le_rfl⟩ (fun r _ => hψ r) (fun r _ => hv r) (fun r _ => hode r)
  rw [Cvs.Prolate.EvenRungsByIndex.psi_rung h 1 ⟨by norm_num, le_rfl⟩] at hs
  rw [← abs_mul]
  exact sq_le_sq.1 hs

/-- `|μ_k| ≤ 1/√x` at `c = 2πx`. -/
theorem abs_muR_le {x k : ℕ} (hx : 80 ≤ 2 * π * x) (h : ∃ χ, IsLevelIdx (2 * π * x) k χ) :
    |muR (2 * π * x) k| ≤ 1 / √(x : ℝ) := by
  have hx0 : (0 : ℝ) < x := Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx
  have hc0 : 0 < 2 * π * (x : ℝ) := by positivity
  have hl := Cvs.Prolate.Envelope.RungExteriorLaw.lamR_le_one hc0 h
  rw [Cvs.Prolate.Envelope.RungExteriorLaw.lamR_eq hc0] at hl
  have hsq : muR (2 * π * x) k ^ 2 ≤ (1 / √(x : ℝ)) ^ 2 := by
    rw [div_pow, Real.sq_sqrt hx0.le, one_pow]
    have e : 2 * π * (x : ℝ) / (2 * π) = x := by field_simp
    rw [e] at hl
    rw [le_div_iff₀ hx0]; exact hl
  exact abs_le_of_sq_le_sq' hsq (by positivity) |>.2 |> fun h2 => by
    rw [abs_le]; exact ⟨(abs_le_of_sq_le_sq' hsq (by positivity)).1, h2⟩

/-- **Every alias term is at the edge scale**: for `ξ ≥ 1`, `|ψ_{G_j}(ξ)| ≤ E_j/√x`. -/
theorem abs_psi_Gr_le {x j : ℕ} (hx : 80 ≤ 2 * π * x) (hj : j < x) {ξ : ℝ} (hξ : 1 ≤ ξ) :
    |psi (2 * π * x) (Gr x j) ξ| ≤ Cvs.Prolate.Mellin.RungWindowLawRightEdge.edgeE x j / √(x : ℝ) := by
  set c := 2 * π * (x : ℝ) with hcdef
  have h1 := Cvs.L2a.FullSpanIndexFloor.full_index x hx hj
  have h0 := Cvs.Prolate.EvenRungsByIndex.exists_isLevelIdx_zero c
  have hsl := Cvs.L2a.FullSpanIndexFloor.sigmaLow_pos (by linarith : 1 < c)
  have hχ1 : lev c (2 * j) < c ^ 2 := by linarith [h1.2]
  have hχ0 : lev c 0 < c ^ 2 := lt_of_le_of_lt (Cvs.Prolate.EvenRungsByIndex.lev_le h1.1 (Nat.zero_le _)) hχ1
  have hlin : psi c (Gr x j) ξ = psi c (rung c (2 * j)) ξ - Cvs.Approximant.DeepIndexSpineSpan.alpha c j * psi c (rung c 0) ξ := by
    have := congrFun (Cvs.L2a.FullTailPolarisation.psi_add_smul (c := c) (Cvs.Prolate.EvenRungsByIndex.continuousOn_rung h1.1 |>.mono (by
      rw [uIcc_of_le (by norm_num)])) (Cvs.Prolate.EvenRungsByIndex.continuousOn_rung h0 |>.mono (by rw [uIcc_of_le (by norm_num)]))
      (-Cvs.Approximant.DeepIndexSpineSpan.alpha c j)) ξ
    unfold Gr
    rw [show (fun s => rung c (2 * j) s - Cvs.Approximant.DeepIndexSpineSpan.alpha c j * rung c 0 s)
      = fun s => rung c (2 * j) s + -Cvs.Approximant.DeepIndexSpineSpan.alpha c j * rung c 0 s by funext s; ring]
    rw [this]; ring
  have a1 := abs_psi_rung_le h1.1 hχ1 hξ
  have a0 := abs_psi_rung_le h0 hχ0 hξ
  have m1 := abs_muR_le hx h1.1
  have m0 := abs_muR_le (k := 0) hx h0
  rw [hlin]
  have hs : 0 < √(x : ℝ) := Real.sqrt_pos.2 (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx)
  unfold Cvs.Prolate.Mellin.RungWindowLawRightEdge.edgeE
  rw [← hcdef]
  calc |psi c (rung c (2 * j)) ξ - Cvs.Approximant.DeepIndexSpineSpan.alpha c j * psi c (rung c 0) ξ|
      ≤ |psi c (rung c (2 * j)) ξ| + |Cvs.Approximant.DeepIndexSpineSpan.alpha c j| * |psi c (rung c 0) ξ| := by
        refine (abs_sub _ _).trans (le_of_eq ?_); rw [abs_mul]
    _ ≤ |muR c (2 * j)| * |rung c (2 * j) 1| + |Cvs.Approximant.DeepIndexSpineSpan.alpha c j| * (|muR c 0| * |rung c 0 1|) := by gcongr
    _ ≤ 1 / √(x : ℝ) * |rung c (2 * j) 1| + |Cvs.Approximant.DeepIndexSpineSpan.alpha c j| * (1 / √(x : ℝ) * |rung c 0 1|) := by gcongr
    _ = (|rung c (2 * j) 1| + |Cvs.Approximant.DeepIndexSpineSpan.alpha c j| * |rung c 0 1|) / √(x : ℝ) := by ring

end Cvs.Prolate.Mellin.RightEdgePoissonSplit

end
