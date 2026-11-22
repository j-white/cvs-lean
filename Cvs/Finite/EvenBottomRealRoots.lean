import Mathlib
import Cvs.Finite.DisplacementIdentity
import Cvs.Finite.DividedDifferenceCommutator
import Cvs.Upstream.SymmetricMatrixBottom

/-!
# The even-sector bottom has real secular roots, with no condition on the odd sector
For a divided-difference matrix `M = ddMatrix a b ω` with `ω` injective and odd, `b` odd and `a` even under an
involution, the displacement identity closes on even vectors with `ω²` in place of `ω` (`qdisplacement`). If `ξ` is
even, `λ` is the bottom of `M` on even vectors, `Mξ = λξ` and the even eigenspace is the line through `ξ`, then
`∑ ξ_i/(ω_i² − w) ≠ 0` for every non-real `w` (`secular_ne_zero`). The even/odd ordering is not used.
-/

noncomputable section

open Matrix

namespace Cvs.Finite.EvenBottomRealRoots

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem sum_neg_even {neg : ι → ι} (hinv : Function.Involutive neg) (f : ι → ℝ) :
    ∑ i, f (neg i) = ∑ i, f i :=
  Equiv.sum_comp (Function.Involutive.toPerm neg hinv) f

/-- **The displacement identity in `ω²`, on even vectors.** -/
theorem qdisplacement {a b ω : ι → ℝ} (hωinj : Function.Injective ω) {neg : ι → ι}
    (hinv : Function.Involutive neg) (hω : ∀ i, ω (neg i) = -ω i) (hb : ∀ i, b (neg i) = -b i)
    {v : ι → ℝ} (hv : ∀ i, v (neg i) = v i) (i : ι) :
    ω i ^ 2 * (Cvs.Finite.DividedDifferenceCommutator.ddMatrix a b ω *ᵥ v) i
      - (Cvs.Finite.DividedDifferenceCommutator.ddMatrix a b ω *ᵥ (fun j => ω j ^ 2 * v j)) i
      = ω i * b i * ∑ j, v j - ∑ j, ω j * b j * v j := by
  have h1 := Cvs.Finite.DisplacementIdentity.displacement (a := a) (b := b) hωinj v i
  have h2 := Cvs.Finite.DisplacementIdentity.displacement (a := a) (b := b) hωinj (fun j => ω j * v j) i
  have hs1 : ∑ j, b j * v j = 0 :=
    Cvs.Finite.DisplacementIdentity.sum_eq_zero_of_odd hinv (fun j => by rw [hb, hv]; ring)
  have hs2 : ∑ j, ω j * v j = 0 :=
    Cvs.Finite.DisplacementIdentity.sum_eq_zero_of_odd hinv (fun j => by rw [hω, hv]; ring)
  have e : (fun j => ω j * (fun j => ω j * v j) j) = (fun j => ω j ^ 2 * v j) := funext fun j => by ring
  rw [e, hs2] at h2
  rw [hs1] at h1
  have hs3 : ∑ j, b j * (fun j => ω j * v j) j = ∑ j, ω j * b j * v j :=
    Finset.sum_congr rfl fun j _ => by ring
  rw [hs3] at h2
  linear_combination ω i * h1 + h2

omit [DecidableEq ι] in
/-- A matrix commuting with the involution sends even vectors to even vectors. -/
theorem mulVec_even {A : Matrix ι ι ℝ} {neg : ι → ι} (hinv : Function.Involutive neg)
    (hA : ∀ i j, A (neg i) (neg j) = A i j) {v : ι → ℝ} (hv : ∀ i, v (neg i) = v i) (i : ι) :
    (A *ᵥ v) (neg i) = (A *ᵥ v) i := by
  simp only [mulVec, dotProduct]
  rw [← sum_neg_even hinv (fun j => A (neg i) j * v j)]
  exact Finset.sum_congr rfl fun j _ => by rw [hA, hv]

omit [DecidableEq ι] in
/-- **Nonnegative on even vectors and zero at an even vector forces the image to vanish.** -/
theorem mulVec_eq_zero_of_even_psd {A : Matrix ι ι ℝ} (hsymm : ∀ i j, A i j = A j i) {neg : ι → ι}
    (hinv : Function.Involutive neg) (hA : ∀ i j, A (neg i) (neg j) = A i j)
    (hpsd : ∀ v : ι → ℝ, (∀ i, v (neg i) = v i) → 0 ≤ v ⬝ᵥ (A *ᵥ v))
    {v : ι → ℝ} (hv : ∀ i, v (neg i) = v i) (h0 : v ⬝ᵥ (A *ᵥ v) = 0) : A *ᵥ v = 0 := by
  set w := A *ᵥ v with hwdef
  have hw : ∀ i, w (neg i) = w i := mulVec_even hinv hA hv
  have hwAv : w ⬝ᵥ (A *ᵥ v) = w ⬝ᵥ w := rfl
  have hvAw : v ⬝ᵥ (A *ᵥ w) = w ⬝ᵥ w := by
    rw [Cvs.Upstream.SymmetricMatrixBottom.dotProduct_mulVec_comm hsymm]
  have hC := hpsd w hw
  have hexp : ∀ t : ℝ, (v + t • w) ⬝ᵥ (A *ᵥ (v + t • w))
      = v ⬝ᵥ (A *ᵥ v) + 2 * t * (w ⬝ᵥ w) + t ^ 2 * (w ⬝ᵥ (A *ᵥ w)) := by
    intro t
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct, add_dotProduct,
      dotProduct_smul, smul_dotProduct, smul_dotProduct, dotProduct_smul, hvAw, hwAv]
    simp only [smul_eq_mul]; ring
  by_contra hne
  have hpos : 0 < w ⬝ᵥ w := lt_of_le_of_ne (Cvs.Upstream.SymmetricMatrixBottom.dotProduct_self_nonneg' w)
    (fun h => hne (dotProduct_self_eq_zero.mp h.symm))
  set C := w ⬝ᵥ (A *ᵥ w)
  set s : ℝ := (w ⬝ᵥ w) / (C + 1) with hs
  have hC1 : 0 < C + 1 := by linarith
  have hs0 : 0 < s := div_pos hpos hC1
  have hsC : s * C ≤ w ⬝ᵥ w := by
    rw [hs, div_mul_eq_mul_div, div_le_iff₀ hC1]; nlinarith
  have hev : ∀ i, (v + (-s) • w) (neg i) = (v + (-s) • w) i := by
    intro i; simp [hv i, hw i]
  have h := hpsd _ hev
  rw [hexp, h0] at h
  nlinarith

/-- **The even-sector bottom has no non-real secular root.** -/
theorem secular_ne_zero {a b ω : ι → ℝ} (hωinj : Function.Injective ω) {neg : ι → ι}
    (hinv : Function.Involutive neg) (hω : ∀ i, ω (neg i) = -ω i) (hb : ∀ i, b (neg i) = -b i)
    (ha : ∀ i, a (neg i) = a i) {lam : ℝ} {xi : ι → ℝ} (hxieven : ∀ i, xi (neg i) = xi i) (hxi0 : xi ≠ 0)
    (hmin : ∀ v : ι → ℝ, (∀ i, v (neg i) = v i) →
      lam * (v ⬝ᵥ v) ≤ v ⬝ᵥ (Cvs.Finite.DividedDifferenceCommutator.ddMatrix a b ω *ᵥ v))
    (hxi : Cvs.Finite.DividedDifferenceCommutator.ddMatrix a b ω *ᵥ xi = lam • xi)
    (hker : ∀ v : ι → ℝ, (∀ i, v (neg i) = v i) →
      Cvs.Finite.DividedDifferenceCommutator.ddMatrix a b ω *ᵥ v = lam • v → ∃ c : ℝ, v = c • xi)
    {w : ℂ} (hw : w.im ≠ 0) :
    ∑ i, (xi i : ℂ) / (((ω i ^ 2 : ℝ) : ℂ) - w) ≠ 0 := by
  intro hS
  set M := Cvs.Finite.DividedDifferenceCommutator.ddMatrix a b ω with hM
  set α := w.re; set β := w.im
  set q : ι → ℝ := fun i => ω i ^ 2 with hq
  set d : ι → ℝ := fun i => (q i - α) ^ 2 + β ^ 2 with hd
  have hβ2 : 0 < β ^ 2 := by positivity
  have hdpos : ∀ i, 0 < d i := fun i => by simp only [hd]; positivity
  set U : ι → ℝ := fun i => xi i * (q i - α) / d i with hU
  set V : ι → ℝ := fun i => xi i * β / d i with hV
  -- the complex secular terms split into `U` and `V`
  have hterm : ∀ i, (xi i : ℂ) / (((ω i ^ 2 : ℝ) : ℂ) - w) = (U i : ℂ) + (V i : ℂ) * Complex.I := by
    intro i
    have hne : (((ω i ^ 2 : ℝ) : ℂ) - w) ≠ 0 := by
      intro h
      have h' := congrArg Complex.im h
      rw [Complex.sub_im, Complex.ofReal_im, Complex.zero_im] at h'
      exact hw (by linarith)
    have hdi : (ω i ^ 2 - w.re) ^ 2 + w.im ^ 2 ≠ 0 := by
      have := hdpos i; simp only [hd, hq] at this; exact this.ne'
    rw [div_eq_iff hne]
    have hxre : ((U i : ℂ) + (V i : ℂ) * Complex.I).re = U i := by simp
    have hxim : ((U i : ℂ) + (V i : ℂ) * Complex.I).im = V i := by simp
    have hyre : (((ω i ^ 2 : ℝ) : ℂ) - w).re = ω i ^ 2 - w.re := by
      rw [Complex.sub_re, Complex.ofReal_re]
    have hyim : (((ω i ^ 2 : ℝ) : ℂ) - w).im = -w.im := by
      rw [Complex.sub_im, Complex.ofReal_im, zero_sub]
    apply Complex.ext
    · rw [Complex.ofReal_re, Complex.mul_re, hxre, hxim, hyre, hyim]
      simp only [hU, hV, hd, hq]
      field_simp
      ring
    · rw [Complex.ofReal_im, Complex.mul_im, hxre, hxim, hyre, hyim]
      simp only [hU, hV, hd, hq]
      field_simp
      ring
  have hsumC : ((∑ i, U i : ℝ) : ℂ) + ((∑ i, V i : ℝ) : ℂ) * Complex.I = 0 := by
    rw [← hS, Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_add_distrib, ← Finset.sum_mul]
    push_cast; rfl
  have hU0 : ∑ i, U i = 0 := by
    have := congrArg Complex.re hsumC; simpa using this
  have hV0 : ∑ i, V i = 0 := by
    have := congrArg Complex.im hsumC; simpa using this
  -- parities
  have hqeven : ∀ i, q (neg i) = q i := fun i => by simp only [hq, hω]; ring
  have hUeven : ∀ i, U (neg i) = U i := fun i => by simp only [hU, hd, hqeven, hxieven]
  have hVeven : ∀ i, V (neg i) = V i := fun i => by simp only [hV, hd, hqeven, hxieven]
  -- the two relations
  have hdne : ∀ j, (ω j ^ 2 - w.re) ^ 2 + w.im ^ 2 ≠ 0 := by
    intro j; have := hdpos j; simp only [hd, hq] at this; exact this.ne'
  have hrel1 : (fun j => q j * U j) = xi + α • U - β • V := by
    funext j; have := hdne j
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hU, hV, hd, hq]
    field_simp; ring
  have hrel2 : (fun j => q j * V j) = α • V + β • U := by
    funext j; have := hdne j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hU, hV, hd, hq]
    field_simp
    try ring
  -- symmetry and involution invariance of `M`
  have hsymm : ∀ i j, M i j = M j i := by
    intro i j
    by_cases hij : i = j
    · rw [hij]
    · rw [hM, Cvs.Finite.DividedDifferenceCommutator.ddMatrix_off hij, Cvs.Finite.DividedDifferenceCommutator.ddMatrix_off (Ne.symm hij)]
      have : ω i - ω j ≠ 0 := sub_ne_zero.mpr (fun h => hij (hωinj h))
      have : ω j - ω i ≠ 0 := sub_ne_zero.mpr (fun h => hij (hωinj h.symm))
      field_simp; ring
  have hMneg : ∀ i j, M (neg i) (neg j) = M i j := by
    intro i j
    by_cases hij : i = j
    · rw [hij]; simp only [hM, Cvs.Finite.DividedDifferenceCommutator.ddMatrix, if_true, ha]
    · have hij' : neg i ≠ neg j := fun h => hij (hinv.injective h)
      rw [hM, Cvs.Finite.DividedDifferenceCommutator.ddMatrix_off hij, Cvs.Finite.DividedDifferenceCommutator.ddMatrix_off hij', hb, hb, hω, hω,
        show -b i - -b j = -(b i - b j) by ring, show -ω i - -ω j = -(ω i - ω j) by ring, neg_div_neg_eq]
  -- the displacement on `U` and `V`
  set cU := ∑ j, ω j * b j * U j
  have hE1 : ∀ i, (q i - α) * ((M *ᵥ U) i - lam * U i) + β * ((M *ᵥ V) i - lam * V i) = -cU := by
    intro i
    have h := qdisplacement (a := a) hωinj hinv hω hb hUeven i
    rw [hU0, mul_zero, zero_sub] at h
    change q i * (M *ᵥ U) i - (M *ᵥ (fun j => q j * U j)) i = -cU at h
    rw [hrel1, Matrix.mulVec_sub, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hxi] at h
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h
    have hr := congrFun hrel1 i
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hr
    linear_combination h - lam * hr
  -- the sum of the two forms vanishes
  have hsplit : ∀ i, U i * ((M *ᵥ U) i - lam * U i) + V i * ((M *ᵥ V) i - lam * V i)
      = (xi i / d i) * (-cU) := by
    intro i
    have := hdne i
    rw [← hE1 i]
    simp only [hU, hV, hd, hq]
    field_simp
    try ring
  have hxid : ∑ i, xi i / d i = 0 := by
    have hβ : β ≠ 0 := hw
    have : ∑ i, V i = β * ∑ i, xi i / d i := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by simp only [hV]; ring
    rw [hV0] at this
    rcases mul_eq_zero.mp this.symm with h | h
    · exact absurd h hβ
    · exact h
  have hsum0 : (U ⬝ᵥ (M *ᵥ U) - lam * (U ⬝ᵥ U)) + (V ⬝ᵥ (M *ᵥ V) - lam * (V ⬝ᵥ V)) = 0 := by
    have : ∑ i, (U i * ((M *ᵥ U) i - lam * U i) + V i * ((M *ᵥ V) i - lam * V i)) = 0 := by
      rw [Finset.sum_congr rfl fun i _ => hsplit i, ← Finset.sum_mul, hxid, zero_mul]
    simp only [dotProduct, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    rw [← this]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hUf := hmin U hUeven
  have hVf := hmin V hVeven
  have hUz : U ⬝ᵥ (M *ᵥ U) - lam * (U ⬝ᵥ U) = 0 := by linarith
  have hVz : V ⬝ᵥ (M *ᵥ V) - lam * (V ⬝ᵥ V) = 0 := by linarith
  -- `M − λ` is nonnegative on even vectors, so `U`, `V` are eigenvectors
  set A : Matrix ι ι ℝ := M - lam • (1 : Matrix ι ι ℝ) with hA
  have hAv : ∀ v : ι → ℝ, A *ᵥ v = M *ᵥ v - lam • v := by
    intro v; rw [hA, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hAq : ∀ v : ι → ℝ, v ⬝ᵥ (A *ᵥ v) = v ⬝ᵥ (M *ᵥ v) - lam * (v ⬝ᵥ v) := by
    intro v; rw [hAv, dotProduct_sub, dotProduct_smul, smul_eq_mul]
  have hAsymm : ∀ i j, A i j = A j i := by
    intro i j
    simp only [hA, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, hsymm i j]
    by_cases h : i = j
    · rw [h]
    · rw [if_neg h, if_neg (Ne.symm h)]
  have hAneg : ∀ i j, A (neg i) (neg j) = A i j := by
    intro i j
    simp only [hA, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, hMneg]
    by_cases h : i = j
    · rw [if_pos (by rw [h]), if_pos h]
    · rw [if_neg (fun h' => h (hinv.injective h')), if_neg h]
  have hApsd : ∀ v : ι → ℝ, (∀ i, v (neg i) = v i) → 0 ≤ v ⬝ᵥ (A *ᵥ v) := by
    intro v hv; rw [hAq]; linarith [hmin v hv]
  have hUk := mulVec_eq_zero_of_even_psd hAsymm hinv hAneg hApsd hUeven (by rw [hAq]; exact hUz)
  have hVk := mulVec_eq_zero_of_even_psd hAsymm hinv hAneg hApsd hVeven (by rw [hAq]; exact hVz)
  rw [hAv, sub_eq_zero] at hUk hVk
  obtain ⟨c1, hc1⟩ := hker U hUeven hUk
  obtain ⟨c2, hc2⟩ := hker V hVeven hVk
  -- `c₂ ≠ 0`, and `ξ` sums to zero
  obtain ⟨i0, hi0⟩ : ∃ i, xi i ≠ 0 := by
    by_contra h
    exact hxi0 (funext fun i => by by_contra hi; exact h ⟨i, hi⟩)
  have hc2ne : c2 ≠ 0 := by
    intro h
    have := congrFun hc2 i0
    simp only [h, zero_smul, Pi.zero_apply, hV] at this
    have hdi := hdpos i0
    rcases mul_eq_zero.mp (div_eq_zero_iff.mp this |>.resolve_right hdi.ne') with h' | h'
    · exact hi0 h'
    · exact hw h'
  have hxisum : ∑ i, xi i = 0 := by
    have : ∑ i, V i = c2 * ∑ i, xi i := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by rw [hc2]; rfl
    rw [hV0] at this
    rcases mul_eq_zero.mp this.symm with h | h
    · exact absurd h hc2ne
    · exact h
  -- on the support of `ξ`, `ω²` is constant
  have hconst : ∀ i, xi i ≠ 0 → q i = α + β * c1 / c2 := by
    intro i hi
    have h2 := congrFun hrel2 i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h2
    rw [hc1, hc2] at h2
    simp only [Pi.smul_apply, smul_eq_mul] at h2
    field_simp
    have : xi i * (c2 * q i - (α * c2 + β * c1)) = 0 := by linear_combination h2
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hi
    · linarith
  -- so the support is `{i₀, neg i₀}`, whose sum is not zero
  have hsupp : ∀ j, xi j ≠ 0 → j = i0 ∨ j = neg i0 := by
    intro j hj
    have hq' : ω j ^ 2 = ω i0 ^ 2 := by
      have := hconst j hj; have := hconst i0 hi0; simp only [hq] at *; linarith
    have hq'' : ω j * ω j = ω i0 * ω i0 := by rw [← sq, ← sq]; exact hq'
    rcases mul_self_eq_mul_self_iff.mp hq'' with h | h
    · exact Or.inl (hωinj h)
    · exact Or.inr (hωinj (by rw [h, hω]))
  have hsum2 : ∑ j, xi j = ∑ j ∈ ({i0, neg i0} : Finset ι), xi j := by
    refine (Finset.sum_subset (Finset.subset_univ _) fun j _ hj => ?_).symm
    by_contra hne
    rcases hsupp j hne with h | h
    · exact hj (by simp [h])
    · exact hj (by simp [h])
  rw [hsum2] at hxisum
  by_cases hfix : neg i0 = i0
  · simp only [hfix, Finset.mem_singleton, Finset.insert_eq_of_mem, Finset.sum_singleton] at hxisum
    exact hi0 hxisum
  · rw [Finset.sum_pair (Ne.symm hfix), hxieven] at hxisum
    exact hi0 (by linarith)

end Cvs.Finite.EvenBottomRealRoots
