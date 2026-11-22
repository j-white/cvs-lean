/-
Spectrum transport: the exact spectral set of the arithmetic block.

The spectral set of the masked rotation (`SpectralSet.lean`) is carried to
the Loewner atom on `ℓ²(ℤ, ℂ)`:

* spectra are invariant under intertwining by a linear isometry equivalence
  (`spectrum_eq_of_intertwines`), so the DTFT transports `spec` verbatim;
* the annihilating Chebyshev identity descends to the complex masked
  rotation componentwise through `reLp`/`imLp`, and the real eigenfunctions
  complexify through `ofRealLp`, giving
  `spec ℂ (pathLawWC β) = ℝ↪ℂ image of the Chebyshev families`;
* scaling by the arithmetic weight is `spectrum.smul_eq_smul`.

End result: for any operator on `ℓ²(ℤ, ℂ)` whose matrix is `atomEntry`,
the spectrum is exactly `Λ(q)/√q` times the union of the Chebyshev spectra
of `P_m` and `P_{m−1}` — the constants `1, √2, φ, √3, …` are spectral
values of the arithmetic blocks themselves.
-/
import Cvs.PathLaw.Model
import Cvs.PathLaw.SpectralSet

open MeasureTheory Polynomial

namespace Cvs.PathLaw

/-! ### Spectrum is invariant under isometric intertwining -/

section Intertwine

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- If `S ∘ e = e ∘ T` along a linear isometry equivalence, units transport:
`IsUnit (μ − S) → IsUnit (μ − T)`. -/
lemma isUnit_algebraMap_sub_of_intertwines (e : E ≃ₗᵢ[𝕜] F)
    (T : E →L[𝕜] E) (S : F →L[𝕜] F) (h : ∀ x, S (e x) = e (T x)) {μ : 𝕜}
    (hu : IsUnit (algebraMap 𝕜 (F →L[𝕜] F) μ - S)) :
    IsUnit (algebraMap 𝕜 (E →L[𝕜] E) μ - T) := by
  obtain ⟨u, hu⟩ := hu
  have hcomm : ∀ x : E,
      (algebraMap 𝕜 (F →L[𝕜] F) μ - S) (e x)
        = e ((algebraMap 𝕜 (E →L[𝕜] E) μ - T) x) := by
    intro x
    rw [sub_apply, sub_apply, Algebra.algebraMap_eq_smul_one,
      Algebra.algebraMap_eq_smul_one, smul_apply, smul_apply,
      one_apply_eq_self, one_apply_eq_self, h x, map_sub, map_smul]
  set v : E →L[𝕜] E :=
    (e.symm.toLinearIsometry.toContinuousLinearMap) ∘L
      ((↑u⁻¹ : F →L[𝕜] F) ∘L e.toLinearIsometry.toContinuousLinearMap)
    with hv
  rw [isUnit_iff_exists]
  refine ⟨v, ?_, ?_⟩
  · -- (μ − T) ∘ v = 1
    ext x
    have h1 : (↑u : F →L[𝕜] F) ((↑u⁻¹ : F →L[𝕜] F) (e x))
        = e x := by
      have hmu : (↑u : F →L[𝕜] F) * (↑u⁻¹ : F →L[𝕜] F) = 1 := u.mul_inv
      have happ := DFunLike.congr_fun hmu (e x)
      rw [one_apply_eq_self] at happ
      exact happ
    have h2 : (algebraMap 𝕜 (F →L[𝕜] F) μ - S)
        ((↑u⁻¹ : F →L[𝕜] F) (e x)) = e x := by
      rw [← hu]
      exact h1
    have h3 := hcomm (e.symm ((↑u⁻¹ : F →L[𝕜] F) (e x)))
    rw [e.apply_symm_apply] at h3
    have h4 : e ((algebraMap 𝕜 (E →L[𝕜] E) μ - T)
        (e.symm ((↑u⁻¹ : F →L[𝕜] F) (e x)))) = e x := by
      rw [← h3, h2]
    have h5 := congrArg e.symm h4
    simp only [e.symm_apply_apply] at h5
    show ((algebraMap 𝕜 (E →L[𝕜] E) μ - T) ∘L v) x = (1 : E →L[𝕜] E) x
    rw [ContinuousLinearMap.comp_apply, one_apply_eq_self]
    exact h5
  · -- v ∘ (μ − T) = 1
    ext x
    have h3 := hcomm x
    show (v ∘L (algebraMap 𝕜 (E →L[𝕜] E) μ - T)) x = (1 : E →L[𝕜] E) x
    rw [ContinuousLinearMap.comp_apply, one_apply_eq_self]
    show e.symm ((↑u⁻¹ : F →L[𝕜] F)
      (e ((algebraMap 𝕜 (E →L[𝕜] E) μ - T) x))) = x
    rw [← h3, ← hu]
    have h1 : (↑u⁻¹ : F →L[𝕜] F) ((↑u : F →L[𝕜] F) (e x)) = e x := by
      have hmu : (↑u⁻¹ : F →L[𝕜] F) * (↑u : F →L[𝕜] F) = 1 := u.inv_mul
      have happ := DFunLike.congr_fun hmu (e x)
      rw [one_apply_eq_self] at happ
      exact happ
    rw [h1, e.symm_apply_apply]

/-- **Spectrum is invariant under isometric intertwining.** -/
theorem spectrum_eq_of_intertwines (e : E ≃ₗᵢ[𝕜] F)
    (T : E →L[𝕜] E) (S : F →L[𝕜] F) (h : ∀ x, S (e x) = e (T x)) :
    spectrum 𝕜 T = spectrum 𝕜 S := by
  have h' : ∀ y, T (e.symm y) = e.symm (S y) := by
    intro y
    have h2 := h (e.symm y)
    rw [e.apply_symm_apply] at h2
    rw [h2, e.symm_apply_apply]
  ext μ
  rw [spectrum.mem_iff, spectrum.mem_iff]
  constructor
  · intro hT hS
    exact hT (isUnit_algebraMap_sub_of_intertwines e T S h hS)
  · intro hS hT
    exact hS (isUnit_algebraMap_sub_of_intertwines e.symm S T h' hT)

end Intertwine


/-! ### Componentwise polynomial calculus on complex `L²` -/

section ComplexComponents

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

lemma reLp_zero : reLp (0 : Lp ℂ 2 μ) = 0 := by
  have h := reLp_add (0 : Lp ℂ 2 μ) 0
  rw [add_zero] at h
  have h2 := congrArg (fun x => x - reLp (0 : Lp ℂ 2 μ)) h
  simpa using h2.symm

lemma imLp_zero : imLp (0 : Lp ℂ 2 μ) = 0 := by
  have h := imLp_add (0 : Lp ℂ 2 μ) 0
  rw [add_zero] at h
  have h2 := congrArg (fun x => x - imLp (0 : Lp ℂ 2 μ)) h
  simpa using h2.symm

lemma reLp_real_smul (r : ℝ) (f : Lp ℂ 2 μ) :
    reLp (((r : ℝ) : ℂ) • f) = r • reLp f := by
  apply Lp.ext
  filter_upwards [coeFn_reLp (((r : ℝ) : ℂ) • f), Lp.coeFn_smul ((r : ℝ) : ℂ) f,
    Lp.coeFn_smul r (reLp f), coeFn_reLp f] with x h1 h2 h3 h4
  rw [h1, h2, h3, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, h4]
  simp [Complex.mul_re]

lemma imLp_real_smul (r : ℝ) (f : Lp ℂ 2 μ) :
    imLp (((r : ℝ) : ℂ) • f) = r • imLp f := by
  apply Lp.ext
  filter_upwards [coeFn_imLp (((r : ℝ) : ℂ) • f), Lp.coeFn_smul ((r : ℝ) : ℂ) f,
    Lp.coeFn_smul r (imLp f), coeFn_imLp f] with x h1 h2 h3 h4
  rw [h1, h2, h3, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, h4]
  simp [Complex.mul_im]

lemma reLp_sum {ι : Type*} (s : Finset ι) (F : ι → Lp ℂ 2 μ) :
    reLp (∑ i ∈ s, F i) = ∑ i ∈ s, reLp (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [reLp_zero]
  | insert i s hi IH =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, reLp_add, IH]

lemma imLp_sum {ι : Type*} (s : Finset ι) (F : ι → Lp ℂ 2 μ) :
    imLp (∑ i ∈ s, F i) = ∑ i ∈ s, imLp (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [imLp_zero]
  | insert i s hi IH =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, imLp_add, IH]

lemma eq_zero_of_reLp_imLp {f : Lp ℂ 2 μ} (hre : reLp f = 0)
    (him : imLp f = 0) : f = 0 := by
  have h := norm_sq_eq_re_add_im f
  rw [hre, him, norm_zero] at h
  have h0 : ‖f‖ ^ 2 = 0 := by rw [h]; ring
  have : ‖f‖ = 0 := by
    have := sq_eq_zero_iff.mp h0
    exact this
  exact norm_eq_zero.mp this

lemma ofRealLp_smul (r : ℝ) (g : Lp ℝ 2 μ) :
    ofRealLp (r • g) = ((r : ℝ) : ℂ) • ofRealLp g := by
  apply Lp.ext
  filter_upwards [coeFn_ofRealLp (r • g), Lp.coeFn_smul r g,
    Lp.coeFn_smul ((r : ℝ) : ℂ) (ofRealLp g), coeFn_ofRealLp g]
    with x h1 h2 h3 h4
  rw [h1, h2, h3, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, h4]
  push_cast
  ring

lemma ofRealLp_ne_zero {g : Lp ℝ 2 μ} (hg : g ≠ 0) : ofRealLp g ≠ 0 := by
  intro hc
  apply hg
  have := norm_ofRealLp g
  rw [hc, norm_zero] at this
  exact norm_eq_zero.mp this.symm

end ComplexComponents

/-! ### The complex masked rotation: componentwise annihilation -/

section ComplexRotation

lemma reLp_pathLawWC (β : ℝ) (f : Lp ℂ 2 (volume : Measure (AddCircle (1 : ℝ)))) :
    reLp (pathLawWC β f) = pathLawW β (reLp f) :=
  reLp_maskedRotationC _ _ _ _ _ f

lemma imLp_pathLawWC (β : ℝ) (f : Lp ℂ 2 (volume : Measure (AddCircle (1 : ℝ)))) :
    imLp (pathLawWC β f) = pathLawW β (imLp f) :=
  imLp_maskedRotationC _ _ _ _ _ f

lemma reLp_pathLawWC_pow (β : ℝ) (n : ℕ)
    (f : Lp ℂ 2 (volume : Measure (AddCircle (1 : ℝ)))) :
    reLp ((pathLawWC β ^ n) f) = (pathLawW β ^ n) (reLp f) := by
  induction n generalizing f with
  | zero => simp [pow_zero, one_apply_eq_self]
  | succ n IH =>
    have h1 : (pathLawWC β ^ (n + 1)) f = pathLawWC β ((pathLawWC β ^ n) f) := by
      rw [pow_succ']
      rfl
    have h2 : (pathLawW β ^ (n + 1)) (reLp f)
        = pathLawW β ((pathLawW β ^ n) (reLp f)) := by
      rw [pow_succ']
      rfl
    rw [h1, h2, reLp_pathLawWC, IH]

lemma imLp_pathLawWC_pow (β : ℝ) (n : ℕ)
    (f : Lp ℂ 2 (volume : Measure (AddCircle (1 : ℝ)))) :
    imLp ((pathLawWC β ^ n) f) = (pathLawW β ^ n) (imLp f) := by
  induction n generalizing f with
  | zero => simp [pow_zero, one_apply_eq_self]
  | succ n IH =>
    have h1 : (pathLawWC β ^ (n + 1)) f = pathLawWC β ((pathLawWC β ^ n) f) := by
      rw [pow_succ']
      rfl
    have h2 : (pathLawW β ^ (n + 1)) (imLp f)
        = pathLawW β ((pathLawW β ^ n) (imLp f)) := by
      rw [pow_succ']
      rfl
    rw [h1, h2, imLp_pathLawWC, IH]

/-- **Real annihilation transports to `ℂ`** componentwise: any real
polynomial killing the real masked rotation kills its complex form. -/
theorem aeval_map_pathLawWC_of (β : ℝ) (q : Polynomial ℝ)
    (hq : Polynomial.aeval (pathLawW β) q = 0) :
    Polynomial.aeval (pathLawWC β) (q.map (algebraMap ℝ ℂ)) = 0 := by
  refine ContinuousLinearMap.ext fun f => ?_
  rw [zero_apply]
  set N := q.natDegree + 1 with hN
  have hdeg : (q.map (algebraMap ℝ ℂ)).natDegree < N :=
    lt_of_le_of_lt (Polynomial.natDegree_map_le) (Nat.lt_succ_self _)
  have hexp : (Polynomial.aeval (pathLawWC β) (q.map (algebraMap ℝ ℂ))) f
      = ∑ k ∈ Finset.range N,
          (((q.coeff k : ℝ) : ℂ)) • ((pathLawWC β ^ k) f) := by
    rw [Polynomial.aeval_eq_sum_range' hdeg, sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_apply, Polynomial.coeff_map, Complex.coe_algebraMap]
  have hreal : ∀ (u : Lp ℝ 2 (volume : Measure (AddCircle (1 : ℝ)))),
      ∑ k ∈ Finset.range N, q.coeff k • ((pathLawW β ^ k) u) = 0 := by
    intro u
    have happ := congrArg (fun (A : Lp ℝ 2 (volume : Measure (AddCircle (1 : ℝ)))
        →L[ℝ] Lp ℝ 2 (volume : Measure (AddCircle (1 : ℝ)))) => A u) hq
    simp only [zero_apply] at happ
    rw [← happ, Polynomial.aeval_eq_sum_range, sum_apply]
    exact Finset.sum_congr rfl fun k _ => by rw [smul_apply]
  rw [hexp]
  apply eq_zero_of_reLp_imLp
  · rw [reLp_sum]
    rw [Finset.sum_congr rfl (fun k _ => by
      rw [reLp_real_smul, reLp_pathLawWC_pow])]
    exact hreal (reLp f)
  · rw [imLp_sum]
    rw [Finset.sum_congr rfl (fun k _ => by
      rw [imLp_real_smul, imLp_pathLawWC_pow])]
    exact hreal (imLp f)

/-- The Chebyshev product annihilates the complex masked rotation. -/
theorem aeval_chainPolyC_pathLawWC (β : ℝ) (hβ : 0 < β) :
    Polynomial.aeval (pathLawWC β)
      ((chainPoly β).map (algebraMap ℝ ℂ)) = 0 :=
  aeval_map_pathLawWC_of β _ (aeval_chainPoly_pathLawW β hβ)

/-- Degenerate case: the single Chebyshev factor annihilates. -/
theorem aeval_pathCharPolyC_pathLawWC_deg (β : ℝ) (hβ : 0 < β)
    (hdeg : (capacity 1 β : ℝ) * β = 1) :
    Polynomial.aeval (pathLawWC β)
      ((pathCharPoly (capacity 1 β)).map (algebraMap ℝ ℂ)) = 0 :=
  aeval_map_pathLawWC_of β _ (aeval_pathCharPoly_pathLawW_deg β hβ hdeg)

/-! ### Roots over `ℂ` and complexified eigenvectors -/

lemma eval_map_pathCharPoly_eq_zero_iff (L : ℕ) (μ : ℂ) :
    ((pathCharPoly L).map (algebraMap ℝ ℂ)).eval μ = 0
      ↔ ∃ j : Fin L, μ = ((2 * Real.cos (pathAngle L j) : ℝ) : ℂ) := by
  rw [Polynomial.eval_map, pathCharPoly, Polynomial.eval₂_finsetProd,
    Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨j, -, hj⟩
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C,
      sub_eq_zero, Complex.coe_algebraMap] at hj
    exact ⟨j, hj⟩
  · rintro ⟨j, hj⟩
    refine ⟨j, Finset.mem_univ j, ?_⟩
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C,
      sub_eq_zero, Complex.coe_algebraMap]
    exact hj

/-- Real eigenvectors complexify: real eigenvalues of `W_ℝ` are complex
spectral values of `W_ℂ`. -/
lemma coe_mem_spectrum_pathLawWC {β : ℝ} {lam : ℝ}
    {g : Lp ℝ 2 (volume : Measure (AddCircle (1 : ℝ)))} (hg : g ≠ 0)
    (hWg : pathLawW β g = lam • g) :
    ((lam : ℝ) : ℂ) ∈ spectrum ℂ (pathLawWC β) := by
  refine mem_spectrum_of_eigenvector (x := ofRealLp g)
    (ofRealLp_ne_zero hg) ?_
  have h1 : pathLawWC β (ofRealLp g) = ofRealLp (pathLawW β g) :=
    (ofRealLp_maskedRotation _ _ _ _ _ g).symm
  rw [h1, hWg, ofRealLp_smul]

/-- **The complex spectral set of the masked rotation** (non-degenerate). -/
theorem spectrum_pathLawWC (β : ℝ) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hshort : 1 < (capacity 1 β : ℝ) * β) :
    spectrum ℂ (pathLawWC β)
      = (fun x : ℝ => (x : ℂ)) ''
          ((Set.range fun j : Fin (capacity 1 β) =>
              2 * Real.cos (pathAngle (capacity 1 β) j))
            ∪ (Set.range fun j : Fin (capacity 1 β - 1) =>
                2 * Real.cos (pathAngle (capacity 1 β - 1) j))) := by
  apply Set.eq_of_subset_of_subset
  · intro μ hμ
    have h := spectrum_subset_roots_of_aeval_eq_zero
      (aeval_chainPolyC_pathLawWC β hβ) hμ
    have h' : ((chainPoly β).map (algebraMap ℝ ℂ)).eval μ = 0 := h
    rw [chainPoly, Polynomial.map_mul, Polynomial.eval_mul,
      mul_eq_zero] at h'
    rcases h' with h' | h'
    · obtain ⟨j, hj⟩ := (eval_map_pathCharPoly_eq_zero_iff _ _).mp h'
      exact ⟨_, Or.inl ⟨j, rfl⟩, hj.symm⟩
    · obtain ⟨j, hj⟩ := (eval_map_pathCharPoly_eq_zero_iff _ _).mp h'
      exact ⟨_, Or.inr ⟨j, rfl⟩, hj.symm⟩
  · rintro μ ⟨x, hx, rfl⟩
    rcases hx with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · exact coe_mem_spectrum_pathLawWC
        (chainEigenFun_ne_zero β _ j (volume_chainSet_capacity_pos β hβ))
        (pathLawW_chainEigenFun β hβ _ j)
    · exact coe_mem_spectrum_pathLawWC
        (chainEigenFun_ne_zero β _ j
          (volume_chainSet_short_pos β hβ hβ1 hshort))
        (pathLawW_chainEigenFun β hβ _ j)

/-- **The complex spectral set, degenerate case.** -/
theorem spectrum_pathLawWC_deg (β : ℝ) (hβ : 0 < β)
    (hdeg : (capacity 1 β : ℝ) * β = 1) :
    spectrum ℂ (pathLawWC β)
      = (fun x : ℝ => (x : ℂ)) ''
          (Set.range fun j : Fin (capacity 1 β) =>
            2 * Real.cos (pathAngle (capacity 1 β) j)) := by
  apply Set.eq_of_subset_of_subset
  · intro μ hμ
    have h := spectrum_subset_roots_of_aeval_eq_zero
      (aeval_pathCharPolyC_pathLawWC_deg β hβ hdeg) hμ
    have h' : ((pathCharPoly (capacity 1 β)).map
        (algebraMap ℝ ℂ)).eval μ = 0 := h
    obtain ⟨j, hj⟩ := (eval_map_pathCharPoly_eq_zero_iff _ _).mp h'
    exact ⟨_, ⟨j, rfl⟩, hj.symm⟩
  · rintro μ ⟨x, ⟨j, rfl⟩, rfl⟩
    exact coe_mem_spectrum_pathLawWC
      (chainEigenFun_ne_zero β _ j (volume_chainSet_capacity_pos β hβ))
      (pathLawW_chainEigenFun β hβ _ j)

end ComplexRotation

/-! ### The spectrum of the arithmetic block -/

section Block

open scoped Pointwise

/-- Two operators with the same Loewner matrix coincide. -/
theorem eq_atomCLMC_of_matrix (q c : ℕ) (hq : 2 ≤ q) (hc : q < c)
    (T : AtomSpaceC →L[ℂ] AtomSpaceC)
    (hT : ∀ k l : ℤ, inner ℂ (lp.single 2 l (1 : ℂ)) (T (lp.single 2 k (1 : ℂ)))
        = ((atomEntry q c l k : ℝ) : ℂ)) :
    T = atomCLMC q c := by
  refine eq_of_inner_basis stdBasisC T (atomCLMC q c) fun i j => ?_
  have h1 : inner ℂ (stdBasisC j) (T (stdBasisC i))
      = ((atomEntry q c j i : ℝ) : ℂ) := by
    rw [stdBasisC_apply, stdBasisC_apply]
    exact hT i j
  have h2 : inner ℂ (stdBasisC j) (atomCLMC q c (stdBasisC i))
      = ((atomEntry q c j i : ℝ) : ℂ) := by
    rw [stdBasisC_apply, stdBasisC_apply]
    exact inner_atomCLMC q c hq hc i j
  have e1 : inner ℂ (T (stdBasisC i)) (stdBasisC j)
      = (starRingEnd ℂ) (inner ℂ (stdBasisC j) (T (stdBasisC i))) := by
    rw [inner_conj_symm]
  have e2 : inner ℂ (atomCLMC q c (stdBasisC i)) (stdBasisC j)
      = (starRingEnd ℂ)
          (inner ℂ (stdBasisC j) (atomCLMC q c (stdBasisC i))) := by
    rw [inner_conj_symm]
  rw [e1, e2, h1, h2]

/-- The DTFT intertwines the canonical atom with the weighted rotation. -/
lemma dtft_atomCLMC (q c : ℕ) (x : AtomSpaceC) :
    (((weight q : ℝ) : ℂ)
        • pathLawWC (Real.log q / Real.log c)) (dtft x)
      = dtft (atomCLMC q c x) := by
  have hx : atomCLMC q c x
      = dtft.symm ((((weight q : ℝ) : ℂ)
          • pathLawWC (Real.log q / Real.log c)) (dtft x)) := rfl
  rw [hx, dtft.apply_symm_apply]

/-- Scaling a coerced real set. -/
lemma smul_coe_image (w : ℝ) (S : Set ℝ) :
    ((w : ℂ)) • ((fun x : ℝ => (x : ℂ)) '' S)
      = (fun x : ℝ => ((w * x : ℝ) : ℂ)) '' S := by
  ext z
  simp only [Set.mem_smul_set, Set.mem_image]
  constructor
  · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨x, hx, ?_⟩
    rw [smul_eq_mul]
    push_cast
    ring
  · rintro ⟨x, hx, rfl⟩
    refine ⟨(x : ℂ), ⟨x, hx, rfl⟩, ?_⟩
    rw [smul_eq_mul]
    push_cast
    ring

/-- **The exact spectrum of the arithmetic block** (non-degenerate case).
Any operator on `ℓ²(ℤ, ℂ)` whose matrix is the Loewner atom `atomEntry` has
spectrum exactly `Λ(q)/√q` times the union of the Chebyshev spectra of
`P_m` and `P_{m−1}`, `m = ⌈log c / log q⌉`. In particular the algebraic
constants `1, √2, φ, √3, …` (times the weight) are spectral values of the
arithmetic blocks themselves. -/
theorem spectrum_single_atomC (q c : ℕ) (hq : 2 ≤ q) (hc : q < c)
    (T : AtomSpaceC →L[ℂ] AtomSpaceC)
    (hT : ∀ k l : ℤ, inner ℂ (lp.single 2 l (1 : ℂ)) (T (lp.single 2 k (1 : ℂ)))
        = ((atomEntry q c l k : ℝ) : ℂ))
    (hnd : 1 < (capacity (Real.log c) (Real.log q) : ℝ)
        * (Real.log q / Real.log c)) :
    spectrum ℂ T
      = (fun x : ℝ => ((weight q * x : ℝ) : ℂ)) ''
          ((Set.range fun j : Fin (capacity (Real.log c) (Real.log q)) =>
              2 * Real.cos (pathAngle (capacity (Real.log c) (Real.log q)) j))
            ∪ (Set.range fun j :
                  Fin (capacity (Real.log c) (Real.log q) - 1) =>
                2 * Real.cos
                  (pathAngle (capacity (Real.log c) (Real.log q) - 1) j))) := by
  have hβm := beta_mem q c hq hc
  have hcap : capacity 1 (Real.log q / Real.log c)
      = capacity (Real.log c) (Real.log q) := capacity_one_div _ _
  have hTeq : T = atomCLMC q c := eq_atomCLMC_of_matrix q c hq hc T hT
  have hspec : spectrum ℂ T
      = spectrum ℂ ((((weight q : ℝ) : ℂ))
          • pathLawWC (Real.log q / Real.log c)) := by
    rw [hTeq]
    exact spectrum_eq_of_intertwines dtft (atomCLMC q c) _
      (dtft_atomCLMC q c)
  rw [hspec]
  have hWspec := spectrum_pathLawWC (Real.log q / Real.log c) hβm.1 hβm.2.le
    (by rw [hcap]; exact hnd)
  rcases eq_or_ne (weight q) 0 with hw | hw
  · -- vanishing weight: both sides are `{0}`
    have hmc : 0 < capacity (Real.log c) (Real.log q) := by
      rw [← hcap]
      exact one_le_capacity _ hβm.1
    have hmc1 : 0 < capacity 1 (Real.log q / Real.log c) := by
      rw [hcap]
      exact hmc
    have hnt : Nontrivial
        (Lp ℂ 2 (volume : Measure (AddCircle (1 : ℝ)))) :=
      ⟨ofRealLp (chainEigenFun (Real.log q / Real.log c)
          (capacity 1 (Real.log q / Real.log c)) ⟨0, hmc1⟩), 0,
        ofRealLp_ne_zero (chainEigenFun_ne_zero _ _ _
          (volume_chainSet_capacity_pos _ hβm.1))⟩
    have : Nontrivial
        (Lp ℂ 2 (volume : Measure (AddCircle (1 : ℝ)))
          →L[ℂ] Lp ℂ 2 (volume : Measure (AddCircle (1 : ℝ)))) := by
      obtain ⟨x, y, hxy⟩ := hnt
      refine ⟨1, 0, fun hcon => hxy ?_⟩
      have hx := DFunLike.congr_fun hcon x
      rw [one_apply_eq_self, zero_apply] at hx
      have hy := DFunLike.congr_fun hcon y
      rw [one_apply_eq_self, zero_apply] at hy
      exact hx.trans hy.symm
    rw [hw]
    have hzero : (((0 : ℝ) : ℂ))
        • pathLawWC (Real.log q / Real.log c) = 0 := by
      rw [Complex.ofReal_zero]
      exact zero_smul ℂ (pathLawWC (Real.log q / Real.log c))
    rw [hzero, spectrum.zero_eq]
    apply Set.eq_of_subset_of_subset
    · intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      refine ⟨2 * Real.cos (pathAngle (capacity (Real.log c) (Real.log q))
        ⟨0, hmc⟩), Or.inl ⟨⟨0, hmc⟩, rfl⟩, ?_⟩
      push_cast
      ring
    · rintro z ⟨x, -, rfl⟩
      rw [Set.mem_singleton_iff]
      push_cast
      ring
  · have hwC : ((weight q : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hw
    have hsmul := spectrum.unit_smul_eq_smul
      (pathLawWC (Real.log q / Real.log c)) (Units.mk0 _ hwC)
    have hval : (Units.mk0 (((weight q : ℝ) : ℂ)) hwC)
        • pathLawWC (Real.log q / Real.log c)
        = (((weight q : ℝ) : ℂ)) • pathLawWC (Real.log q / Real.log c) := rfl
    have hval2 : (Units.mk0 (((weight q : ℝ) : ℂ)) hwC)
        • spectrum ℂ (pathLawWC (Real.log q / Real.log c))
        = (((weight q : ℝ) : ℂ))
            • spectrum ℂ (pathLawWC (Real.log q / Real.log c)) := rfl
    rw [← hval, hsmul, hval2, hWspec, hcap, smul_coe_image]

/-- **The canonical complex atom has exactly the Chebyshev spectrum.** -/
theorem spectrum_atomCLMC (q c : ℕ) (hq : 2 ≤ q) (hc : q < c)
    (hnd : 1 < (capacity (Real.log c) (Real.log q) : ℝ)
        * (Real.log q / Real.log c)) :
    spectrum ℂ (atomCLMC q c)
      = (fun x : ℝ => ((weight q * x : ℝ) : ℂ)) ''
          ((Set.range fun j : Fin (capacity (Real.log c) (Real.log q)) =>
              2 * Real.cos (pathAngle (capacity (Real.log c) (Real.log q)) j))
            ∪ (Set.range fun j :
                  Fin (capacity (Real.log c) (Real.log q) - 1) =>
                2 * Real.cos
                  (pathAngle (capacity (Real.log c) (Real.log q) - 1) j))) :=
  spectrum_single_atomC q c hq hc _ (inner_atomCLMC q c hq hc) hnd

end Block

end Cvs.PathLaw
