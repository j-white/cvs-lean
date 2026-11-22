import Mathlib
import Cvs.Approximant.ConnesVectorRealScale
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.Approximant.SpineCouplingTailPairing
import Cvs.Approximant.SpineFormOwnTailPairing
import Cvs.Approximant.SpineSubspace
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.FullTailConvergence
import Cvs.L2a.ProlateFamilySpine
import Cvs.Prolate.Envelope.RungExteriorLaw
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.Gram.ProlateCellGramHalfUnit
import Cvs.Prolate.PlungeMassTrace
import Cvs.Prolate.RungExactOrthogonality
import Cvs.Route.Visibility.EvenFirstCellPoisson
import Cvs.Route.Visibility.WindowChainCellFloors
import Cvs.Xi.EImageWindowPoisson
import Cvs.Xi.OddWindowPoissonLeakage

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The AL-R split: `√x·cellRem = Φ(2·) + T₃ + Z`, the exterior energy `E = 2x∫₁^∞ψ_G²` and `‖Φ(2·)‖² ≤ E/4`

On the first cell `(1/2, 1]` at `c = 2πx`, the scaled remainder `R = √x·cellRem` of the spine profile `G_b` is the
first alias `y₂(θ) = √x·ψ_G(2θ)`, the alias tail `T₃(θ) = √x·Σ_{k≥3}ψ_G(kθ)`, and the centre term
`Z(θ) = −√x·G_b(0)/(2xθ)`.  The exterior energy of `G_b` is `x∫_{(1,∞)}ψ_G² = E(b)/2`, which gives
`‖y₂‖² ≤ E(b)/4`, and `‖Z‖² = G_b(0)²/(4x)` exactly.
-/

noncomputable section

open Real Set MeasureTheory Filter Topology Finset

namespace Cvs.Route.Visibility.AliasRemainderSplit
open Cvs.ZeroCounting

open Cvs.L2a.AngularProlateTailPositive (psi)
open Cvs.Prolate.EvenRungsByIndex (rung rung₁ rung₂ lev lamR IsLevelIdx rung_spec)
open Cvs.Approximant.DeepIndexSpineSpan (spineG alpha)
open Cvs.Prolate.Gram.ProlateCellGramHalfUnit (coefH energyE lam lamTop)

/-! ### The spine profile in prolate coordinates and its exterior energy -/

/-- **The spine profile in prolate coordinates**: `G_b = Σ_n b̃_n h_{4n}`. -/
theorem spineG_eq_sum {x : ℕ} (hx : 1 ≤ x) (b : Cvs.Approximant.SpineSubspace.SF x → ℝ) (s : ℝ) :
    spineG (2 * π * x) b s = ∑ n : Fin x, coefH x b n * rung (2 * π * x) (2 * (n : ℕ)) s := by
  set c := 2 * π * (x : ℝ)
  set f : ℕ → ℝ := fun i =>
    (if h : i ∈ Cvs.Approximant.SpineSubspace.SF x then b ⟨i, h⟩ else -∑ j, b j * alpha c j) * rung c (2 * i) s
  have h1 : ∑ n : Fin x, coefH x b n * rung c (2 * (n : ℕ)) s = ∑ i ∈ Finset.range x, f i :=
    Fin.sum_univ_eq_sum_range f x
  rw [h1, ← Finset.sum_filter_add_sum_filter_not (Finset.range x) (1 ≤ ·)]
  have h0 : (Finset.range x).filter (fun i => ¬ 1 ≤ i) = {0} := by
    ext i; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]; omega
  rw [h0, Finset.sum_singleton]
  have hSF : ∑ i ∈ (Finset.range x).filter (1 ≤ ·), f i
      = ∑ j : Cvs.Approximant.SpineSubspace.SF x, b j * rung c (2 * (j : ℕ)) s := by
    rw [← Finset.sum_coe_sort]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hj : (j : ℕ) ∈ Cvs.Approximant.SpineSubspace.SF x := j.2
    simp only [f, dite_eq_left hj]
  have h0f : f 0 = (-∑ j, b j * alpha c j) * rung c 0 s := by
    have : (0 : ℕ) ∉ Cvs.Approximant.SpineSubspace.SF x := by simp [Cvs.Approximant.SpineSubspace.SF]
    simp only [f, dite_eq_right this, mul_zero]
  rw [hSF, h0f, spineG]
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [neg_mul, Finset.sum_mul, ← sub_eq_add_neg]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by ring

/-- The cosine transform of the spine profile in prolate coordinates: `ψ_G = Σ_n b̃_n ψ_{h_{4n}}`. -/
theorem psi_spineG_eq_sum {x : ℕ} (hx : 1 ≤ x) (b : Cvs.Approximant.SpineSubspace.SF x → ℝ) (ξ : ℝ) :
    psi (2 * π * x) (spineG (2 * π * x) b) ξ
      = ∑ n : Fin x, coefH x b n * psi (2 * π * x) (rung (2 * π * x) (2 * (n : ℕ))) ξ := by
  have e : spineG (2 * π * x) b = fun s => ∑ n ∈ Finset.univ, coefH x b n * rung (2 * π * x) (2 * (n : ℕ)) s :=
    funext (spineG_eq_sum hx b)
  rw [e, Cvs.L2a.FullTailConvergence.psi_sum _ _ _ (fun n _ => Cvs.Approximant.DeepIndexSpineSpan.intervalIntegrable_rung _ _)]

/-- **The exterior energy of the spine profile**: `x∫_{(1,∞)}ψ_G² = E(b)/2`. -/
theorem ext_energy {x : ℕ} (hx : 80 ≤ 2 * π * x) (b : Cvs.Approximant.SpineSubspace.SF x → ℝ) :
    (x : ℝ) * ∫ ξ in Ioi 1, psi (2 * π * x) (spineG (2 * π * x) b) ξ ^ 2 = energyE x b / 2 := by
  have hx1 : 1 ≤ x := by have := Cvs.Prolate.Gram.ProlateCellGramHalfUnit.two_le_of_scale hx; omega
  have hc : (0 : ℝ) < 2 * π * x := by linarith
  have hx0 : (0 : ℝ) < x := Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx
  have hspec := fun n : Fin x => rung_spec (Cvs.Prolate.Gram.ProlateCellGramHalfUnit.exists_level hx n)
  have hinj : Function.Injective fun n : Fin x => lev (2 * π * x) (2 * (n : ℕ)) :=
    (Cvs.Prolate.Gram.ProlateCellGramHalfUnit.lev_strictMono hx).injective
  simp only [psi_spineG_eq_sum hx1]
  rw [Cvs.Prolate.RungExactOrthogonality.integral_span_sq (coefH x b) (fun n => (hspec n).1) (fun n => (hspec n).2.1)
    (fun n => (hspec n).2.2.1) (fun n => (hspec n).2.2.2.1) hc hinj]
  simp only [fun n : Fin x => Cvs.Prolate.Envelope.RungExteriorLaw.mass_eq hc (Cvs.Prolate.Gram.ProlateCellGramHalfUnit.exists_level hx n)]
  rw [energyE, Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [lam]
  field_simp

/-- The squared transform of the spine profile is integrable on `(1, ∞)`. -/
theorem integrableOn_psi_spineG_sq {x : ℕ} (hx : 80 ≤ 2 * π * x) (b : Cvs.Approximant.SpineSubspace.SF x → ℝ) :
    IntegrableOn (fun ξ => psi (2 * π * x) (spineG (2 * π * x) b) ξ ^ 2) (Ioi 1) := by
  have hx1 : 1 ≤ x := by have := Cvs.Prolate.Gram.ProlateCellGramHalfUnit.two_le_of_scale hx; omega
  have hc : (0 : ℝ) < 2 * π * x := by linarith
  have hm : MemLp (fun ξ => ∑ n : Fin x, coefH x b n * psi (2 * π * x) (rung (2 * π * x) (2 * (n : ℕ))) ξ) 2
      (volume.restrict (Ioi 1)) := by
    refine memLp_finsetSum _ fun n _ => ?_
    obtain ⟨h1, h2, h3, h4, -⟩ := rung_spec (Cvs.Prolate.Gram.ProlateCellGramHalfUnit.exists_level hx n)
    exact (Cvs.Prolate.RungExactOrthogonality.memLp_psi h1 h2 h3 h4 hc).const_mul _
  have e : (fun ξ => psi (2 * π * x) (spineG (2 * π * x) b) ξ)
      = fun ξ => ∑ n : Fin x, coefH x b n * psi (2 * π * x) (rung (2 * π * x) (2 * (n : ℕ))) ξ :=
    funext (psi_spineG_eq_sum hx1 b)
  simp only [psi_spineG_eq_sum hx1 b]
  exact hm.integrable_sq

/-! ### The three pieces of the remainder -/

/-- The first alias `y₂(θ) = √x·ψ_G(2θ)`. -/
def alias2 (x : ℕ) (b : Cvs.Approximant.SpineSubspace.SF x → ℝ) (θ : ℝ) : ℝ :=
  √(x : ℝ) * psi (2 * π * x) (spineG (2 * π * x) b) (2 * θ)

/-- The alias tail `T₃(θ) = √x·Σ_{k≥3}ψ_G(kθ)`, written as `√x·(t_G(θ) − ψ_G(2θ))`. -/
def aliasTail (x : ℕ) (b : Cvs.Approximant.SpineSubspace.SF x → ℝ) (θ : ℝ) : ℝ :=
  √(x : ℝ) * (Cvs.Xi.OddWindowPoissonLeakage.leak (2 * π * x) (spineG (2 * π * x) b) θ - psi (2 * π * x) (spineG (2 * π * x) b) (2 * θ))

/-- The centre term `Z(θ) = −√x·G_b(0)/(2xθ)`. -/
def zTerm (x : ℕ) (b : Cvs.Approximant.SpineSubspace.SF x → ℝ) (θ : ℝ) : ℝ :=
  -(√(x : ℝ) * (1 / x * spineG (2 * π * x) b 0 / (2 * θ)))

/-- **The split** `√x·cellRem = y₂ + T₃ + Z`. -/
theorem sqrt_mul_cellRem_eq (x : ℕ) (b : Cvs.Approximant.SpineSubspace.SF x → ℝ) (θ : ℝ) :
    √(x : ℝ) * Cvs.Route.Visibility.EvenFirstCellPoisson.cellRem x b θ = alias2 x b θ + aliasTail x b θ + zTerm x b θ := by
  unfold Cvs.Route.Visibility.EvenFirstCellPoisson.cellRem alias2 aliasTail zTerm
  ring

/-- **The alias tail is the series `√x·Σ_{k≥3}ψ_G(kθ)`** at every `θ ∈ (1/2, 1]` off the lattice `x⁻¹ℕ`. -/
theorem tendsto_aliasTail {x : ℕ} (hx : 80 ≤ 2 * π * x) (b : Cvs.Approximant.SpineSubspace.SF x → ℝ) {θ : ℝ}
    (hθ : θ ∈ Ioc (1 / 2 : ℝ) 1) (hlat : ∀ k : ℕ, θ ≠ k * (1 / x)) :
    Tendsto (fun M : ℕ => √(x : ℝ) * ∑ m ∈ Finset.Icc 3 M, psi (2 * π * x) (spineG (2 * π * x) b) (m * θ))
      atTop (𝓝 (aliasTail x b θ)) := by
  have hc : (0 : ℝ) < 2 * π * x := by linarith
  have hθ0 : 0 < θ := by linarith [hθ.1]
  have hsc := Cvs.Approximant.SpineFormOwnTailPairing.scale_inv hx
  obtain ⟨G₁, G₂, hg, hg₁, hg₂c, heven, -⟩ := Cvs.Approximant.SpineCouplingTailPairing.spine_profile_data hx (Cvs.Approximant.SpineSubspace.SF_lt x) b
  have hT := Cvs.Xi.OddWindowPoissonLeakage.tendsto_sum_psi hg hg₁ hg₂c heven hc hθ0 (by rw [hsc]; exact hlat)
  have hL := Cvs.Xi.OddWindowPoissonLeakage.leak_eq_of_tendsto hθ0 hT
  rw [Cvs.Route.Visibility.EvenFirstCellPoisson.floor_inv_eq_one hθ, Finset.Icc_self, Finset.sum_singleton, Nat.cast_one, one_mul] at hL
  set ψ := psi (2 * π * x) (spineG (2 * π * x) b)
  have hlim := ((hT.sub_const (ψ θ)).sub_const (ψ (2 * θ))).const_mul (√(x : ℝ))
  have hev : (fun M : ℕ => √(x : ℝ) * (∑ m ∈ Finset.Icc 1 M, ψ (m * θ) - ψ θ - ψ (2 * θ)))
      =ᶠ[atTop] fun M : ℕ => √(x : ℝ) * ∑ m ∈ Finset.Icc 3 M, ψ (m * θ) := by
    filter_upwards [eventually_ge_atTop 2] with M hM
    congr 1
    have h1 : Finset.Icc 1 M = insert 1 (Finset.Icc 2 M) := by
      ext m; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have h2 : Finset.Icc 2 M = insert 2 (Finset.Icc 3 M) := by
      ext m; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [h1, Finset.sum_insert (by simp), h2, Finset.sum_insert (by simp)]
    push_cast
    ring_nf
  unfold aliasTail
  rw [hL]
  convert hlim.congr' hev using 2

/-! ### The first alias and the centre term -/

/-- **P1**: `‖y₂‖² = x∫_{(1/2,1]}ψ_G(2θ)² ≤ E(b)/4`. -/
theorem integral_alias2_sq_le {x : ℕ} (hx : 80 ≤ 2 * π * x) (b : Cvs.Approximant.SpineSubspace.SF x → ℝ) :
    ∫ θ in Ioc (1 / 2 : ℝ) 1, alias2 x b θ ^ 2 ≤ energyE x b / 4 := by
  set ψ := psi (2 * π * x) (spineG (2 * π * x) b)
  have hx0 : (0 : ℝ) < x := Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx
  have hint := integrableOn_psi_spineG_sq hx b
  have e1 : ∫ θ in Ioc (1 / 2 : ℝ) 1, alias2 x b θ ^ 2 = (x : ℝ) * ∫ θ in Ioc (1 / 2 : ℝ) 1, ψ (2 * θ) ^ 2 := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioc fun θ _ => ?_
    simp only [alias2, mul_pow, Real.sq_sqrt hx0.le, ψ]
  have e2 : ∫ θ in Ioc (1 / 2 : ℝ) 1, ψ (2 * θ) ^ 2 = 1 / 2 * ∫ ξ in Ioc (1 : ℝ) 2, ψ ξ ^ 2 := by
    rw [← intervalIntegral.integral_of_le (by norm_num), ← intervalIntegral.integral_of_le (by norm_num),
      intervalIntegral.integral_comp_mul_left (fun ξ => ψ ξ ^ 2) (by norm_num : (2 : ℝ) ≠ 0)]
    norm_num
  have h3 : ∫ ξ in Ioc (1 : ℝ) 2, ψ ξ ^ 2 ≤ ∫ ξ in Ioi 1, ψ ξ ^ 2 :=
    setIntegral_mono_set hint (Eventually.of_forall fun _ => sq_nonneg _) (Eventually.of_forall fun _ h => Ioc_subset_Ioi_self h)
  have hE := ext_energy hx b
  rw [e1, e2]
  calc (x : ℝ) * (1 / 2 * ∫ ξ in Ioc (1 : ℝ) 2, ψ ξ ^ 2) ≤ (x : ℝ) * (1 / 2 * ∫ ξ in Ioi 1, ψ ξ ^ 2) := by
        gcongr
    _ = energyE x b / 4 := by rw [← mul_assoc, mul_comm (x : ℝ), mul_assoc, hE]; ring

/-- `∫_{(1/2,1]} θ⁻² = 1`. -/
theorem integral_inv_sq_half_one : ∫ θ in Ioc (1 / 2 : ℝ) 1, (θ ^ 2)⁻¹ = 1 := by
  rw [← intervalIntegral.integral_of_le (by norm_num)]
  have hd : ∀ θ ∈ uIcc (1 / 2 : ℝ) 1, HasDerivAt (fun θ : ℝ => -θ⁻¹) ((θ ^ 2)⁻¹) θ := by
    intro θ hθ
    have h0 : θ ≠ 0 := by
      rw [Set.uIcc_of_le (by norm_num)] at hθ; linarith [hθ.1]
    have := (hasDerivAt_inv h0).neg
    rw [neg_neg] at this
    exact this
  have hc : ContinuousOn (fun θ : ℝ => (θ ^ 2)⁻¹) (uIcc (1 / 2) 1) := by
    refine ContinuousOn.inv₀ (continuousOn_pow 2) fun θ hθ => ?_
    rw [Set.uIcc_of_le (by norm_num)] at hθ; have : 0 < θ := by linarith [hθ.1]
    show θ ^ 2 ≠ 0
    positivity
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable)]
  norm_num

/-- **The centre term exactly**: `‖Z‖² = G_b(0)²/(4x)`. -/
theorem integral_zTerm_sq {x : ℕ} (hx : 1 ≤ x) (b : Cvs.Approximant.SpineSubspace.SF x → ℝ) :
    ∫ θ in Ioc (1 / 2 : ℝ) 1, zTerm x b θ ^ 2 = spineG (2 * π * x) b 0 ^ 2 / (4 * x) := by
  have hx0 : (0 : ℝ) < x := by exact_mod_cast hx
  have e : ∀ θ ∈ Ioc (1 / 2 : ℝ) 1, zTerm x b θ ^ 2 = spineG (2 * π * x) b 0 ^ 2 / (4 * x) * (θ ^ 2)⁻¹ := by
    intro θ hθ
    have : θ ≠ 0 := by linarith [hθ.1]
    simp only [zTerm, neg_sq, mul_pow, div_pow, Real.sq_sqrt hx0.le]
    field_simp
    ring
  rw [setIntegral_congr_fun measurableSet_Ioc e, integral_const_mul, integral_inv_sq_half_one, mul_one]

/-! ### Square integrability on the first cell -/

/-- A function continuous on `[1/2, 1]` is square integrable on `(1/2, 1]`. -/
theorem memLp_of_continuousOn {f : ℝ → ℝ} (hf : ContinuousOn f (Icc (1 / 2) 1)) :
    MemLp f 2 (volume.restrict (Ioc (1 / 2 : ℝ) 1)) := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  refine MemLp.of_bound ((hf.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc) M ?_
  rw [ae_restrict_iff' measurableSet_Ioc]
  exact Eventually.of_forall fun u hu => hM u (Ioc_subset_Icc_self hu)

/-- `y₂` is square integrable on `(1/2, 1]`. -/
theorem memLp_alias2 (x : ℕ) (b : Cvs.Approximant.SpineSubspace.SF x → ℝ) :
    MemLp (alias2 x b) 2 (volume.restrict (Ioc (1 / 2 : ℝ) 1)) := by
  have hψ : Continuous (psi (2 * π * x) (spineG (2 * π * x) b)) :=
    Cvs.Prolate.PlungeMassTrace.continuous_psi (Cvs.Approximant.ConnesVectorRealScale.continuousOn_spineG _ b)
  exact memLp_of_continuousOn
    ((continuous_const.mul (hψ.comp (continuous_const.mul continuous_id))).continuousOn)

/-- `Z` is square integrable on `(1/2, 1]`. -/
theorem memLp_zTerm (x : ℕ) (b : Cvs.Approximant.SpineSubspace.SF x → ℝ) :
    MemLp (zTerm x b) 2 (volume.restrict (Ioc (1 / 2 : ℝ) 1)) := by
  refine memLp_of_continuousOn ?_
  unfold zTerm
  refine (continuousOn_const.mul (continuousOn_const.div (continuousOn_const.mul continuousOn_id)
    fun θ hθ => ?_)).neg
  have : 0 < θ := by linarith [hθ.1]
  simp only [Pi.mul_apply, id]
  show (2 : ℝ) * θ ≠ 0
  positivity

/-- `T₃` is square integrable on `(1/2, 1]`. -/
theorem memLp_aliasTail {x : ℕ} (hx : 80 ≤ 2 * π * x) (b : Cvs.Approximant.SpineSubspace.SF x → ℝ) :
    MemLp (aliasTail x b) 2 (volume.restrict (Ioc (1 / 2 : ℝ) 1)) := by
  have e : aliasTail x b = fun θ => √(x : ℝ) * Cvs.Route.Visibility.EvenFirstCellPoisson.cellRem x b θ - alias2 x b θ - zTerm x b θ := by
    funext θ; rw [sqrt_mul_cellRem_eq]; ring
  rw [e]
  exact ((Cvs.Route.Visibility.WindowChainCellFloors.memLp_cellRem hx b).sub (memLp_alias2 x b)).sub (memLp_zTerm x b)

end Cvs.Route.Visibility.AliasRemainderSplit
