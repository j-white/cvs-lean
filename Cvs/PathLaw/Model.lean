/-
The Single-Atom Path Law — assembling the masked-rotation model.

With the DTFT matrix computation in hand (`Cvs.PathLaw.DTFT`) and the norm
identity over `ℂ` (`Cvs.PathLaw.Complexify`), the Loewner atom on `ℓ²(ℤ)` can be
matched with the masked rotation on `L²(𝕋)`.
-/
import Cvs.PathLaw.DTFT

open MeasureTheory Real

namespace Cvs.PathLaw

/-- `ℓ²(ℤ)` with complex scalars — the space the Loewner atom acts on, and
the one the paper's DTFT starts from. -/
abbrev AtomSpaceC : Type := lp (fun _ : ℤ => ℂ) 2

/-- Mathlib's Fourier basis, transported to the circle's volume measure
(which at period `1` *is* the normalised Haar measure). -/
noncomputable def fourierBasisV :
    HilbertBasis ℤ ℂ (Lp ℂ 2 (volume : Measure (AddCircle (1 : ℝ)))) :=
  volume_eq_haar ▸ (fourierBasis (T := (1 : ℝ)))

/-- **The DTFT**, as a linear isometry equivalence `ℓ²(ℤ) ≃ L²(𝕋)`. -/
noncomputable def dtft :
    AtomSpaceC ≃ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure (AddCircle (1 : ℝ))) :=
  fourierBasisV.repr.symm

theorem dtft_single (k : ℤ) :
    dtft (lp.single 2 k (1 : ℂ)) = fourierBasisV k :=
  fourierBasisV.repr_symm_single k

/-- Transporting the Fourier basis along a measure equality. Stated with the
measure as a *variable* so that `subst` applies. -/
theorem coeFn_fourierBasis_transport {μ : Measure (AddCircle (1 : ℝ))}
    (hμ : μ = AddCircle.haarAddCircle) (k : ℤ) :
    (((hμ ▸ (fourierBasis (T := (1 : ℝ))) : HilbertBasis ℤ ℂ (Lp ℂ 2 μ)) k :
        AddCircle (1 : ℝ) → ℂ)) =ᵐ[μ] fun z => fourier k z := by
  subst hμ
  show ((fourierBasis (T := (1 : ℝ)) k : AddCircle (1 : ℝ) → ℂ)) =ᵐ[_] _
  rw [coe_fourierBasis]
  exact coeFn_fourierLp 2 k

/-- The transported basis is the Fourier monomial, a.e. -/
theorem coeFn_fourierBasisV (k : ℤ) :
    ((fourierBasisV k : AddCircle (1 : ℝ) → ℂ))
      =ᵐ[volume] fun z => fourier k z :=
  coeFn_fourierBasis_transport volume_eq_haar k

/-! ### The masked-rotation model over `ℂ` -/

/-- A **masked-rotation model** for a complex atom: a linear isometry
equivalence onto `L²(𝕋)` intertwining `T` with the weighted masked rotation,
whose norm is the Chebyshev factor. -/
def MaskedRotationModelC (q c : ℕ) (T : AtomSpaceC →L[ℂ] AtomSpaceC) : Prop :=
  ∃ (e : AtomSpaceC ≃ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure (AddCircle (1 : ℝ))))
    (a : AddCircle (1 : ℝ)) (s₁ s₂ : Set (AddCircle (1 : ℝ)))
    (h₁ : MeasurableSet s₁) (h₂ : MeasurableSet s₂),
    (∀ x, (((weight q : ℝ) : ℂ) • maskedRotationC a s₁ s₂ h₁ h₂) (e x) = e (T x)) ∧
      ‖maskedRotationC a s₁ s₂ h₁ h₂‖
        = chebFactor (capacity (Real.log c) (Real.log q))

/-- **The Path Law from a complex masked-rotation model.** -/
theorem single_atom_path_law_of_modelC (q c : ℕ) (T : AtomSpaceC →L[ℂ] AtomSpaceC)
    (hmodel : MaskedRotationModelC q c T) : ‖T‖ = pathLawNorm q c := by
  obtain ⟨e, a, s₁, s₂, h₁, h₂, htransfer, hchain⟩ := hmodel
  have hnorm := opNorm_eq_of_intertwines e T
    (((weight q : ℝ) : ℂ) • maskedRotationC a s₁ s₂ h₁ h₂) htransfer
  rw [← hnorm, norm_smul, hchain, pathLawNorm, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (weight_nonneg q)]
  ring

/-! ### The matrix of the masked rotation in the Fourier basis -/

/-- The inner product `⟪e_l, W e_k⟫` is the integral computed in
`Cvs.PathLaw.DTFT`. -/
theorem inner_pathLawWC_fourierBasisV (β : ℝ) (l k : ℤ) :
    inner ℂ (fourierBasisV l) (pathLawWC β (fourierBasisV k))
      = ∫ z : AddCircle (1 : ℝ),
          ((maskFwd β).indicator
              (fun w => fourier k (w + ((β : ℝ) : AddCircle (1 : ℝ)))) z
            + (maskBwd β).indicator
              (fun w => fourier k (w + -((β : ℝ) : AddCircle (1 : ℝ)))) z)
          * (starRingEnd ℂ) (fourier l z) := by
  set bc := ((β : ℝ) : AddCircle (1 : ℝ)) with hbc
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [
    Lp.coeFn_add ((maskCLMC (maskFwd β) (measurableSet_maskFwd β)) (koopmanC bc (fourierBasisV k)))
      ((maskCLMC (maskBwd β) (measurableSet_maskBwd β)) (koopmanC (-bc) (fourierBasisV k))),
    coeFn_maskCLMC (maskFwd β) (measurableSet_maskFwd β) (koopmanC bc (fourierBasisV k)),
    coeFn_maskCLMC (maskBwd β) (measurableSet_maskBwd β) (koopmanC (-bc) (fourierBasisV k)),
    koopmanC_ae bc (fourierBasisV k), koopmanC_ae (-bc) (fourierBasisV k),
    ae_translate bc (coeFn_fourierBasisV k),
    ae_translate (-bc) (coeFn_fourierBasisV k),
    coeFn_fourierBasisV l] with z h1 h2 h3 h4 h5 h6 h7 h8
  rw [RCLike.inner_apply, h8]
  congr 1
  show (pathLawWC β (fourierBasisV k) : AddCircle (1 : ℝ) → ℂ) z = _
  rw [show (pathLawWC β (fourierBasisV k) : Lp ℂ 2 (volume : Measure (AddCircle (1 : ℝ))))
      = (maskCLMC (maskFwd β) (measurableSet_maskFwd β)) (koopmanC bc (fourierBasisV k))
        + (maskCLMC (maskBwd β) (measurableSet_maskBwd β)) (koopmanC (-bc) (fourierBasisV k)) from rfl,
    h1, Pi.add_apply, h2, h3]
  by_cases hx1 : z ∈ maskFwd β <;> by_cases hx2 : z ∈ maskBwd β <;>
    simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx1, hx2, h4, h5, h6, h7]

/-- **The weighted masked rotation has the Loewner matrix in the Fourier
basis.** -/
theorem inner_weighted_pathLawWC (q c : ℕ) (l k : ℤ)
    (hβ0 : 0 < Real.log q / Real.log c) (hβ1 : Real.log q / Real.log c < 1) :
    inner ℂ (fourierBasisV l)
        ((((weight q : ℝ) : ℂ) • pathLawWC (Real.log q / Real.log c))
          (fourierBasisV k))
      = ((atomEntry q c l k : ℝ) : ℂ) := by
  rw [smul_apply, inner_smul_right,
    inner_pathLawWC_fourierBasisV]
  exact matrix_element_atomEntry q c k l hβ0 hβ1

/-! ### The model exists -/

/-- The standard Hilbert basis of `ℓ²(ℤ, ℂ)`. -/
noncomputable def stdBasisC : HilbertBasis ℤ ℂ AtomSpaceC :=
  HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ AtomSpaceC)

@[simp] theorem stdBasisC_apply (k : ℤ) :
    stdBasisC k = lp.single 2 k (1 : ℂ) :=
  (stdBasisC.repr_symm_single k).symm

/-- **Every Loewner atom admits a masked-rotation model.**
The DTFT carries it to the masked rotation on `L²(𝕋)`. -/
theorem exists_maskedRotationModelC (q c : ℕ) (T : AtomSpaceC →L[ℂ] AtomSpaceC)
    (hβ0 : 0 < Real.log q / Real.log c) (hβ1 : Real.log q / Real.log c < 1)
    (hT : ∀ k l : ℤ, inner ℂ (lp.single 2 l (1 : ℂ)) (T (lp.single 2 k (1 : ℂ)))
            = ((atomEntry q c l k : ℝ) : ℂ)) :
    MaskedRotationModelC q c T := by
  set β := Real.log q / Real.log c with hβdef
  refine ⟨dtft, ((β : ℝ) : AddCircle (1 : ℝ)), maskFwd β, maskBwd β,
    measurableSet_maskFwd β, measurableSet_maskBwd β, ?_, ?_⟩
  · -- the intertwining
    have hEq : ((((weight q : ℝ) : ℂ) • pathLawWC β).comp
          (dtft.toLinearIsometry.toContinuousLinearMap))
        = (dtft.toLinearIsometry.toContinuousLinearMap).comp T := by
      refine eq_of_apply_basis' stdBasisC _ _ (fun k => ?_)
      show (((weight q : ℝ) : ℂ) • pathLawWC β) (dtft (stdBasisC k))
        = dtft (T (stdBasisC k))
      rw [stdBasisC_apply, dtft_single]
      refine eq_of_inner_basis_vec fourierBasisV (fun l => ?_)
      rw [inner_weighted_pathLawWC q c l k hβ0 hβ1,
        show (fourierBasisV l) = dtft (lp.single 2 l (1 : ℂ)) from
          (dtft_single l).symm,
        dtft.inner_map_map]
      exact (hT k l).symm
    intro x
    exact congrArg (fun A => A x) hEq
  · -- the chain norm
    show ‖pathLawWC β‖ = _
    rw [norm_pathLawWC β hβ0 (le_of_lt hβ1), hβdef, capacity_one_div]

/-! ### The Single-Atom Path Law -/

/-- For `2 ≤ q < c` the normalised step lies in `(0,1)`. -/
theorem beta_mem (q c : ℕ) (hq : 2 ≤ q) (hc : q < c) :
    0 < Real.log q / Real.log c ∧ Real.log q / Real.log c < 1 := by
  have h1q : (1 : ℕ) < q := by omega
  have hqc : (q : ℕ) < c := hc
  have hlq : 0 < Real.log q := Real.log_pos (by exact_mod_cast h1q)
  have hlc : Real.log q < Real.log c := by
    refine Real.log_lt_log (by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one (by omega)) ?_
    exact_mod_cast hqc
  have hlcpos : 0 < Real.log c := lt_trans hlq hlc
  refine ⟨div_pos hlq hlcpos, ?_⟩
  rw [div_lt_one hlcpos]
  exact hlc

/-- **THE SINGLE-ATOM PATH LAW.**

Any bounded operator on `ℓ²(ℤ)` whose matrix in the standard basis is the
unfolded Loewner divided-difference matrix of the prime power `q` at cutoff
`c` has operator norm exactly

    ‖T‖ = 2 cos(π / (⌈log c / log q⌉ + 1)) · Λ(q)/√q. -/
theorem single_atom_path_lawC (q c : ℕ) (hq : 2 ≤ q) (hc : q < c)
    (T : AtomSpaceC →L[ℂ] AtomSpaceC)
    (hT : ∀ k l : ℤ, inner ℂ (lp.single 2 l (1 : ℂ)) (T (lp.single 2 k (1 : ℂ)))
            = ((atomEntry q c l k : ℝ) : ℂ)) :
    ‖T‖ = pathLawNorm q c :=
  single_atom_path_law_of_modelC q c T
    (exists_maskedRotationModelC q c T (beta_mem q c hq hc).1 (beta_mem q c hq hc).2 hT)

/-- The canonical Loewner atom operator on `ℓ²(ℤ, ℂ)`, constructed via DTFT. -/
noncomputable def atomCLMC (q c : ℕ) : AtomSpaceC →L[ℂ] AtomSpaceC :=
  (dtft.symm.toLinearIsometry.toContinuousLinearMap).comp
    ((((weight q : ℝ) : ℂ) • pathLawWC (Real.log q / Real.log c)).comp
      (dtft.toLinearIsometry.toContinuousLinearMap))

/-- The canonical complex atom has the Loewner matrix elements. -/
theorem inner_atomCLMC (q c : ℕ) (hq : 2 ≤ q) (hc : q < c) (k l : ℤ) :
    inner ℂ (lp.single 2 l (1 : ℂ)) (atomCLMC q c (lp.single 2 k (1 : ℂ)))
      = ((atomEntry q c l k : ℝ) : ℂ) := by
  have hmem := beta_mem q c hq hc
  unfold atomCLMC
  simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometryEquiv.coe_toLinearIsometry]
  have h1 : dtft (lp.single 2 k (1 : ℂ)) = fourierBasisV k := dtft_single k
  rw [h1]
  have hinner : inner ℂ (lp.single 2 l (1 : ℂ))
      (dtft.symm ((((weight q : ℝ) : ℂ) • pathLawWC (Real.log q / Real.log c)) (fourierBasisV k)))
      = inner ℂ (dtft (lp.single 2 l (1 : ℂ)))
          ((((weight q : ℝ) : ℂ) • pathLawWC (Real.log q / Real.log c)) (fourierBasisV k)) := by
    rw [← dtft.inner_map_map, dtft.apply_symm_apply]
  rw [hinner, dtft_single l]
  exact inner_weighted_pathLawWC q c l k hmem.1 hmem.2

/-- **Unconditional Path Law for the canonical complex atom.** -/
theorem opNorm_atomCLMC (q c : ℕ) (hq : 2 ≤ q) (hc : q < c) :
    ‖atomCLMC q c‖ = pathLawNorm q c :=
  single_atom_path_lawC q c hq hc (atomCLMC q c) (inner_atomCLMC q c hq hc)

end Cvs.PathLaw

