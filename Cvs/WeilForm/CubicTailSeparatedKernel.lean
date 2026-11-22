import Mathlib
import Cvs.L2a.PlaneCorrelationL2
import Cvs.WeilForm.PoleTermDilationMean

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The cubic tail correction as a bounded separated kernel

The separated physical kernel is dominated by half the Carleman kernel.
Its weighted Schur bound controls the actual arch/pole correction.
-/

noncomputable section

open Real Set MeasureTheory Filter

namespace Cvs.WeilForm.CubicTailSeparatedKernel

/-- The positive Carleman row normalized by its square-root Schur weight. -/
def row (t s : ℝ) : ℝ := √t / (√s * (t + s))

theorem row_nonneg {t s : ℝ} (ht : 0 < t) (hs : 0 < s) : 0 ≤ row t s := by
  unfold row
  positivity

theorem row_one_comp_sq {u : ℝ} (hu : 0 < u) :
    (2 * u) * row 1 (u ^ 2) = 2 * (1 + u ^ 2)⁻¹ := by
  simp only [row, sqrt_one, Real.sqrt_sq_eq_abs, abs_of_pos hu]
  field_simp

/-- The normalized Carleman row is genuinely integrable at the origin and infinity. -/
theorem integrable_row_one : IntegrableOn (row 1) (Ioi 0) := by
  apply (integrableOn_Ioi_comp_rpow_iff (row 1) (by norm_num : (2 : ℝ) ≠ 0)).mp
  refine ((integrable_inv_one_add_sq.const_mul 2).restrict).congr
    (ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => ?_)
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 2), Real.rpow_two,
    show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, smul_eq_mul]
  exact (row_one_comp_sq hu).symm

/-- The exact square-root Schur mass is `π`. -/
theorem integral_row_one : (∫ s in Ioi (0 : ℝ), row 1 s) = π := by
  have h := integral_comp_rpow_Ioi (row 1) (by norm_num : (2 : ℝ) ≠ 0)
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 2), Real.rpow_two,
    show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, smul_eq_mul] at h
  rw [← h, setIntegral_congr_fun measurableSet_Ioi (fun u hu => row_one_comp_sq hu),
    integral_const_mul, integral_Ioi_inv_one_add_sq, Real.arctan_zero]
  ring

theorem row_scale {t s : ℝ} (ht : 0 < t) (hs : 0 < s) : row t (t * s) = row 1 s / t := by
  rw [row, row, sqrt_one, Real.sqrt_mul ht.le]
  have hts : 0 < √t := sqrt_pos.mpr ht
  have hss : 0 < √s := sqrt_pos.mpr hs
  field_simp

theorem integrable_row {t : ℝ} (ht : 0 < t) : IntegrableOn (row t) (Ioi 0) := by
  have h : IntegrableOn (fun s => row t (t * s)) (Ioi 0) :=
    (integrable_row_one.div_const t).congr
      (ae_restrict_of_forall_mem measurableSet_Ioi fun s hs => (row_scale ht hs).symm)
  simpa only [mul_zero] using (integrableOn_Ioi_comp_mul_left_iff (row t) 0 ht).mp h

theorem integral_row {t : ℝ} (ht : 0 < t) : (∫ s in Ioi (0 : ℝ), row t s) = π := by
  have h := integral_comp_mul_left_Ioi' (row t) 0 ht
  simp only [mul_zero, smul_eq_mul] at h
  rw [← h, setIntegral_congr_fun measurableSet_Ioi (fun s hs => row_scale ht hs),
    integral_div, integral_row_one]
  field_simp

/-- Lebesgue measure on the positive half-line. -/
abbrev positiveVolume : Measure ℝ := volume.restrict (Ioi 0)

/-- The weighted square majorant in the Carleman Schur argument. -/
def squareRow (f : ℝ → ℝ) (p : ℝ × ℝ) : ℝ := f p.1 ^ 2 * row p.1 p.2

private theorem measurable_row : Measurable (fun p : ℝ × ℝ => row p.1 p.2) := by
  unfold row
  fun_prop

theorem integral_squareRow_norm {t : ℝ} (ht : 0 < t) (f : ℝ → ℝ) :
    (∫ s, ‖squareRow f (t, s)‖ ∂positiveVolume) = π * f t ^ 2 := by
  have he : (fun s => ‖squareRow f (t, s)‖) =ᵐ[positiveVolume]
      fun s => f t ^ 2 * row t s :=
    ae_restrict_of_forall_mem measurableSet_Ioi fun s hs => by
      change ‖f t ^ 2 * row t s‖ = f t ^ 2 * row t s
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (row_nonneg ht hs))]
  rw [integral_congr_ae he, integral_const_mul, integral_row ht]
  ring

/-- The Schur square majorant is genuinely jointly integrable for each L² input. -/
theorem integrable_squareRow {f : ℝ → ℝ} (hf : MemLp f 2 positiveVolume) :
    Integrable (squareRow f) (positiveVolume.prod positiveVolume) := by
  have hm : AEStronglyMeasurable (squareRow f) (positiveVolume.prod positiveVolume) :=
    hf.integrable_sq.aestronglyMeasurable.comp_fst.mul measurable_row.aestronglyMeasurable
  apply (integrable_prod_iff hm).mpr
  constructor
  · exact ae_restrict_of_forall_mem measurableSet_Ioi fun t ht =>
      (integrable_row ht).const_mul (f t ^ 2)
  · refine (hf.integrable_sq.const_mul π).congr ?_
    exact ae_restrict_of_forall_mem measurableSet_Ioi fun t ht =>
      (integral_squareRow_norm ht f).symm

theorem integral_squareRow {f : ℝ → ℝ} (hf : MemLp f 2 positiveVolume) :
    (∫ p, squareRow f p ∂positiveVolume.prod positiveVolume)
      = π * ∫ t, f t ^ 2 ∂positiveVolume := by
  rw [integral_prod _ (integrable_squareRow hf)]
  have he : (fun t => ∫ s, squareRow f (t, s) ∂positiveVolume) =ᵐ[positiveVolume]
      fun t => π * f t ^ 2 := by
    apply ae_restrict_of_forall_mem measurableSet_Ioi
    intro t ht
    change (∫ s, f t ^ 2 * row t s ∂positiveVolume) = π * f t ^ 2
    rw [integral_const_mul, integral_row ht]
    ring
  rw [integral_congr_ae he, integral_const_mul]

/-- Weighted arithmetic-geometric mean gives the Carleman domination. -/
theorem carleman_abs_le_squareRows {t s : ℝ} (ht : 0 < t) (hs : 0 < s) (f g : ℝ) :
    |f * g / (t + s)| ≤ (f ^ 2 * row t s + g ^ 2 * row s t) / 2 := by
  have hts : 0 < √t := sqrt_pos.mpr ht
  have hss : 0 < √s := sqrt_pos.mpr hs
  have hadd : 0 < t + s := by positivity
  have hy := two_mul_le_add_sq (|f| * √t) (|g| * √s)
  simp only [mul_pow, sq_abs] at hy
  rw [abs_div, abs_mul, abs_of_pos hadd]
  unfold row
  rw [add_comm s t]
  field_simp
  nlinarith [hy]

/-- The Carleman pairing is absolutely jointly integrable on physical L². -/
theorem integrable_carleman {f g : ℝ → ℝ} (hf : MemLp f 2 positiveVolume)
    (hg : MemLp g 2 positiveVolume) :
    Integrable (fun p : ℝ × ℝ => f p.1 * g p.2 / (p.1 + p.2))
      (positiveVolume.prod positiveVolume) := by
  have hm : AEStronglyMeasurable (fun p : ℝ × ℝ => f p.1 * g p.2 / (p.1 + p.2))
      (positiveVolume.prod positiveVolume) := by
    convert
      (hf.aestronglyMeasurable.comp_fst.mul hg.aestronglyMeasurable.comp_snd).mul
        ((measurable_fst.add measurable_snd).inv.aestronglyMeasurable) using 1
    funext p
    simp [div_eq_mul_inv]
  refine (((integrable_squareRow hf).add (integrable_squareRow hg).swap).div_const 2).mono' hm ?_
  rw [Measure.prod_restrict]
  apply ae_restrict_of_forall_mem (measurableSet_Ioi.prod measurableSet_Ioi)
  rintro ⟨t, s⟩ ⟨ht, hs⟩
  change ‖f t * g s / (t + s)‖ ≤ (f t ^ 2 * row t s + g s ^ 2 * row s t) / 2
  rw [Real.norm_eq_abs]
  exact carleman_abs_le_squareRows ht hs _ _

/-- The square-root factors of the two Schur rows multiply to the Carleman kernel. -/
theorem sqrt_row_mul {t s : ℝ} (ht : 0 < t) (hs : 0 < s) :
    √(row t s) * √(row s t) = 1 / (t + s) := by
  have hts : 0 < √t := sqrt_pos.mpr ht
  have hss : 0 < √s := sqrt_pos.mpr hs
  have he : row t s * row s t = (1 / (t + s)) ^ 2 := by
    unfold row
    rw [add_comm s t]
    field_simp
  rw [← Real.sqrt_mul (row_nonneg ht hs), he, Real.sqrt_sq_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < 1 / (t + s))]

/-- A Schur square-root lift into the product L² space. -/
def lift (f : ℝ → ℝ) (p : ℝ × ℝ) : ℝ := f p.1 * √(row p.1 p.2)

theorem lift_sq_ae (f : ℝ → ℝ) :
    (fun p => lift f p ^ 2) =ᵐ[positiveVolume.prod positiveVolume] squareRow f := by
  rw [Measure.prod_restrict]
  apply ae_restrict_of_forall_mem (measurableSet_Ioi.prod measurableSet_Ioi)
  rintro ⟨t, s⟩ ⟨ht, hs⟩
  change (f t * √(row t s)) ^ 2 = f t ^ 2 * row t s
  rw [mul_pow, Real.sq_sqrt (row_nonneg ht hs)]

theorem memLp_lift {f : ℝ → ℝ} (hf : MemLp f 2 positiveVolume) :
    MemLp (lift f) 2 (positiveVolume.prod positiveVolume) := by
  have hm : AEStronglyMeasurable (lift f) (positiveVolume.prod positiveVolume) :=
    hf.aestronglyMeasurable.comp_fst.mul
      (Real.continuous_sqrt.measurable.comp measurable_row).aestronglyMeasurable
  exact (memLp_two_iff_integrable_sq hm).mpr
    ((integrable_squareRow hf).congr (lift_sq_ae f).symm)

theorem norm_lift_toLp {f : ℝ → ℝ} (hf : MemLp f 2 positiveVolume) :
    ‖(memLp_lift hf).toLp (lift f)‖ = √π * ‖hf.toLp f‖ := by
  have he : ‖(memLp_lift hf).toLp (lift f)‖ ^ 2 = π * ‖hf.toLp f‖ ^ 2 := by
    rw [Cvs.L2a.PlaneCorrelationL2.norm_sq_eq_integral, Cvs.L2a.PlaneCorrelationL2.norm_sq_eq_integral]
    calc
      ∫ p, ((memLp_lift hf).toLp (lift f)) p ^ 2 ∂positiveVolume.prod positiveVolume
        = ∫ p, lift f p ^ 2 ∂positiveVolume.prod positiveVolume :=
          integral_congr_ae (by filter_upwards [(memLp_lift hf).coeFn_toLp] with p hp; rw [hp])
      _ = ∫ p, squareRow f p ∂positiveVolume.prod positiveVolume := integral_congr_ae (lift_sq_ae f)
      _ = π * ∫ t, f t ^ 2 ∂positiveVolume := integral_squareRow hf
      _ = _ := by
        congr 1
        exact integral_congr_ae (by filter_upwards [hf.coeFn_toLp] with t ht; rw [ht])
  have hs : (√π * ‖hf.toLp f‖) ^ 2 = π * ‖hf.toLp f‖ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt pi_pos.le]
  nlinarith [norm_nonneg ((memLp_lift hf).toLp (lift f)),
    mul_nonneg (sqrt_nonneg π) (norm_nonneg (hf.toLp f))]

/-- The sharp Carleman bilinear norm bound in physical L². -/
theorem abs_integral_carleman_le {f g : ℝ → ℝ} (hf : MemLp f 2 positiveVolume)
    (hg : MemLp g 2 positiveVolume) :
    |∫ p, f p.1 * g p.2 / (p.1 + p.2) ∂positiveVolume.prod positiveVolume|
      ≤ π * ‖hf.toLp f‖ * ‖hg.toLp g‖ := by
  have hg' : MemLp (fun p : ℝ × ℝ => lift g p.swap) 2 (positiveVolume.prod positiveVolume) :=
    (memLp_lift hg).comp_measurePreserving Measure.measurePreserving_swap
  have he : (fun p : ℝ × ℝ => f p.1 * g p.2 / (p.1 + p.2))
      =ᵐ[positiveVolume.prod positiveVolume] fun p => lift f p * lift g p.swap := by
    rw [Measure.prod_restrict]
    apply ae_restrict_of_forall_mem (measurableSet_Ioi.prod measurableSet_Ioi)
    rintro ⟨t, s⟩ ⟨ht, hs⟩
    change f t * g s / (t + s) = (f t * √(row t s)) * (g s * √(row s t))
    rw [show (f t * √(row t s)) * (g s * √(row s t)) =
      (f t * g s) * (√(row t s) * √(row s t)) by ring, sqrt_row_mul ht hs]
    ring
  have hnorm : ‖hg'.toLp (fun p : ℝ × ℝ => lift g p.swap)‖ = √π * ‖hg.toLp g‖ := by
    have hn : ‖hg'.toLp (fun p : ℝ × ℝ => lift g p.swap)‖ ^ 2
        = ‖(memLp_lift hg).toLp (lift g)‖ ^ 2 := by
      rw [Cvs.L2a.PlaneCorrelationL2.norm_sq_eq_integral, Cvs.L2a.PlaneCorrelationL2.norm_sq_eq_integral]
      calc
        ∫ p, (hg'.toLp (fun p : ℝ × ℝ => lift g p.swap)) p ^ 2 ∂positiveVolume.prod positiveVolume
          = ∫ p, lift g p.swap ^ 2 ∂positiveVolume.prod positiveVolume :=
            integral_congr_ae (by filter_upwards [hg'.coeFn_toLp] with p hp; rw [hp])
        _ = ∫ p, lift g p ^ 2 ∂positiveVolume.prod positiveVolume :=
          integral_prod_swap (fun p : ℝ × ℝ => lift g p ^ 2)
        _ = _ := integral_congr_ae (by filter_upwards [(memLp_lift hg).coeFn_toLp] with p hp; rw [hp])
    have hne := (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) (by omega : 2 ≠ 0)).mp hn
    rw [hne, norm_lift_toLp hg]
  rw [integral_congr_ae he]
  have hi : (∫ p, lift f p * lift g p.swap ∂positiveVolume.prod positiveVolume) =
      inner ℝ ((memLp_lift hf).toLp (lift f)) (hg'.toLp (fun p : ℝ × ℝ => lift g p.swap)) := by
    rw [Cvs.L2a.PlaneCorrelationL2.inner_eq_integral]
    apply integral_congr_ae
    filter_upwards [(memLp_lift hf).coeFn_toLp, hg'.coeFn_toLp] with p h1 h2
    rw [h1, h2]
  rw [hi]
  calc
    _ ≤ ‖(memLp_lift hf).toLp (lift f)‖ * ‖hg'.toLp (fun p : ℝ × ℝ => lift g p.swap)‖ :=
      abs_real_inner_le_norm _ _
    _ = _ := by
      rw [norm_lift_toLp hf, hnorm]
      calc
        _ = (√π * √π) * ‖hf.toLp f‖ * ‖hg.toLp g‖ := by ring
        _ = _ := by rw [Real.mul_self_sqrt pi_pos.le]

/-- The absolute Carleman integral has the same sharp norm bound. -/
theorem integral_abs_carleman_le {f g : ℝ → ℝ} (hf : MemLp f 2 positiveVolume)
    (hg : MemLp g 2 positiveVolume) :
    (∫ p, |f p.1 * g p.2 / (p.1 + p.2)| ∂positiveVolume.prod positiveVolume)
      ≤ π * ‖hf.toLp f‖ * ‖hg.toLp g‖ := by
  have h := abs_integral_carleman_le hf.norm hg.norm
  have he : (fun p : ℝ × ℝ => ‖f p.1‖ * ‖g p.2‖ / (p.1 + p.2))
      =ᵐ[positiveVolume.prod positiveVolume] fun p => |f p.1 * g p.2 / (p.1 + p.2)| := by
    rw [Measure.prod_restrict]
    apply ae_restrict_of_forall_mem (measurableSet_Ioi.prod measurableSet_Ioi)
    rintro ⟨t, s⟩ ⟨ht, hs⟩
    change 0 < t at ht
    change 0 < s at hs
    simp only [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos (by positivity : 0 < t+s)]
  rw [integral_congr_ae he, abs_of_nonneg (integral_nonneg (fun _ => abs_nonneg _))] at h
  simpa only [Lp.norm_toLp, eLpNorm_norm _ hf.aestronglyMeasurable,
    eLpNorm_norm _ hg.aestronglyMeasurable] using h

/-- The physical separated kernel after `η=rθ`. The nonpositive test gate is retained. -/
def kernel (θ η : ℝ) : ℝ := if 0 < θ then θ ^ 2 / (η * (η ^ 2 - θ ^ 2)) else 0

abbrev leftVolume : Measure ℝ := volume.restrict (Iio 1)
abbrev rightVolume : Measure ℝ := volume.restrict (Ioi 1)

/-- Translation and reciprocal-side reflection send the positive Carleman quadrant
onto the separated physical rectangle. -/
def separationMap (p : ℝ × ℝ) : ℝ × ℝ := (1 - p.1, 1 + p.2)

private theorem left_measurePreserving :
    MeasurePreserving (fun t : ℝ => 1 - t) positiveVolume leftVolume := by
  have h := (volume.measurePreserving_sub_left (1 : ℝ)).restrict_preimage
    (s := Iio (1 : ℝ)) measurableSet_Iio
  have he : (fun t : ℝ => 1 - t) ⁻¹' Iio 1 = Ioi 0 := by
    ext t
    simp only [mem_preimage, mem_Iio, mem_Ioi]
    constructor <;> intro ht <;> linarith
  simpa only [he] using h

private theorem right_measurePreserving :
    MeasurePreserving (fun s : ℝ => 1 + s) positiveVolume rightVolume := by
  have h := (measurePreserving_add_left volume (1 : ℝ)).restrict_preimage
    (s := Ioi (1 : ℝ)) measurableSet_Ioi
  have he : (fun s : ℝ => 1 + s) ⁻¹' Ioi 1 = Ioi 0 := by
    ext s
    simp only [mem_preimage, mem_Ioi]
    constructor <;> intro hs <;> linarith
  simpa only [he] using h

private theorem separation_measurePreserving :
    MeasurePreserving separationMap (positiveVolume.prod positiveVolume)
      (leftVolume.prod rightVolume) :=
  left_measurePreserving.prod right_measurePreserving

private theorem separation_measurableEmbedding : MeasurableEmbedding separationMap :=
  (MeasurableEquiv.subLeft (1 : ℝ)).measurableEmbedding.prodMap
    (MeasurableEquiv.addLeft (1 : ℝ)).measurableEmbedding

/-- Half the Carleman kernel dominates the actual cubic physical kernel. -/
theorem kernel_le {θ η : ℝ} (hθ : θ < 1) (hη : 1 < η) :
    0 ≤ kernel θ η ∧ kernel θ η ≤ 1 / (2 * (η - θ)) := by
  by_cases hθ0 : 0 < θ
  · rw [kernel, ite_eq_left hθ0]
    have hη0 : 0 < η := by linarith
    have hdiff : 0 < η - θ := by linarith
    have hsum : 0 < η + θ := by linarith
    have hsq : 0 < η ^ 2 - θ ^ 2 := by nlinarith
    constructor
    · positivity
    · apply (div_le_div_iff₀ (by positivity : 0 < η * (η ^ 2 - θ ^ 2))
        (by positivity : 0 < 2 * (η - θ))).mpr
      nlinarith [sq_nonneg (η-θ), mul_nonneg (by linarith : 0 ≤ η-θ)
        (by nlinarith : 0 ≤ η*(η+θ)-2*θ^2)]
  · rw [kernel, ite_eq_right hθ0]
    constructor
    · exact le_refl 0
    · have : 0 < η-θ := by linarith
      positivity

/-- The actual separated bilinear physical kernel. -/
def kernelPair (F G : ℝ → ℝ) (p : ℝ × ℝ) : ℝ := G p.1 * F p.2 * kernel p.1 p.2

private theorem measurable_kernel : Measurable (fun p : ℝ × ℝ => kernel p.1 p.2) := by
  unfold kernel
  apply Measurable.ite (measurableSet_lt measurable_const measurable_fst)
  · fun_prop
  · fun_prop

private theorem memLp_separation_left {G : ℝ → ℝ} (hG : MemLp G 2 volume) :
    MemLp (fun t => G (1-t)) 2 positiveVolume :=
  (hG.comp_measurePreserving (volume.measurePreserving_sub_left 1)).restrict _

private theorem memLp_separation_right {F : ℝ → ℝ} (hF : MemLp F 2 volume) :
    MemLp (fun s => F (1+s)) 2 positiveVolume :=
  (hF.comp_measurePreserving (measurePreserving_add_left volume 1)).restrict _

private theorem norm_separation_left_le {G : ℝ → ℝ} (hG : MemLp G 2 volume) :
    ‖(memLp_separation_left hG).toLp (fun t => G (1-t))‖ ≤ ‖hG.toLp G‖ := by
  rw [Lp.norm_toLp, Lp.norm_toLp]
  apply ENNReal.toReal_mono hG.eLpNorm_ne_top
  calc
    _ ≤ eLpNorm (fun t => G (1-t)) 2 volume := eLpNorm_mono_measure _ Measure.restrict_le_self
    _ = _ := eLpNorm_comp_measurePreserving hG.aestronglyMeasurable
      (volume.measurePreserving_sub_left 1)

private theorem norm_separation_right_le {F : ℝ → ℝ} (hF : MemLp F 2 volume) :
    ‖(memLp_separation_right hF).toLp (fun s => F (1+s))‖ ≤ ‖hF.toLp F‖ := by
  rw [Lp.norm_toLp, Lp.norm_toLp]
  apply ENNReal.toReal_mono hF.eLpNorm_ne_top
  calc
    _ ≤ eLpNorm (fun s => F (1+s)) 2 volume := eLpNorm_mono_measure _ Measure.restrict_le_self
    _ = _ := eLpNorm_comp_measurePreserving hF.aestronglyMeasurable
      (measurePreserving_add_left volume 1)

private theorem kernelPair_separation_le {t s : ℝ} (ht : 0<t) (hs : 0<s) (F G : ℝ → ℝ) :
    |kernelPair F G (separationMap (t,s))|
      ≤ |G (1-t) * F (1+s) / (t+s)| / 2 := by
  obtain ⟨hn,hk⟩ := kernel_le (by linarith : 1-t<1) (by linarith : 1<1+s)
  change |G (1-t)*F (1+s)*kernel (1-t) (1+s)| ≤ _
  rw [abs_mul, abs_of_nonneg hn, abs_div, abs_of_pos (by positivity : 0<t+s)]
  calc
    _ ≤ |G (1-t)*F (1+s)| * (1/(2*((1+s)-(1-t)))) :=
      mul_le_mul_of_nonneg_left hk (abs_nonneg _)
    _ = _ := by
      have hadd : 0 < t+s := by positivity
      rw [show 2*((1+s)-(1-t)) = 2*(t+s) by ring]
      field_simp [hadd.ne']

/-- Absolute joint integrability of the actual separated cubic kernel on physical L². -/
theorem integrable_kernelPair {F G : ℝ → ℝ} (hFm : Measurable F) (hGm : Measurable G)
    (hF : MemLp F 2 volume) (hG : MemLp G 2 volume) :
    Integrable (kernelPair F G) (leftVolume.prod rightVolume) := by
  have hm : Measurable (kernelPair F G) :=
    ((hGm.comp measurable_fst).mul (hFm.comp measurable_snd)).mul measurable_kernel
  apply (separation_measurePreserving.integrable_comp hm.aestronglyMeasurable).mp
  have hh := (integrable_carleman (memLp_separation_left hG) (memLp_separation_right hF)).norm.div_const 2
  refine hh.mono' (hm.comp separation_measurePreserving.measurable).aestronglyMeasurable ?_
  rw [Measure.prod_restrict]
  apply ae_restrict_of_forall_mem (measurableSet_Ioi.prod measurableSet_Ioi)
  rintro ⟨t,s⟩ ⟨ht,hs⟩
  simpa only [Function.comp_apply, Real.norm_eq_abs] using kernelPair_separation_le ht hs F G

/-- The actual physical cubic kernel has norm at most `π/2`, independent of the window scale. -/
theorem abs_integral_kernelPair_le {F G : ℝ → ℝ} (hFm : Measurable F) (hGm : Measurable G)
    (hF : MemLp F 2 volume) (hG : MemLp G 2 volume) :
    |∫ p, kernelPair F G p ∂leftVolume.prod rightVolume|
      ≤ (π/2) * ‖hF.toLp F‖ * ‖hG.toLp G‖ := by
  rw [← separation_measurePreserving.integral_comp separation_measurableEmbedding]
  have hi := (separation_measurePreserving.integrable_comp
    (integrable_kernelPair hFm hGm hF hG).aestronglyMeasurable).mpr
      (integrable_kernelPair hFm hGm hF hG)
  have hc := integrable_carleman (memLp_separation_left hG) (memLp_separation_right hF)
  calc
    _ ≤ ∫ p, |kernelPair F G (separationMap p)| ∂positiveVolume.prod positiveVolume :=
      abs_integral_le_integral_abs
    _ ≤ ∫ p, |G (1-p.1)*F (1+p.2)/(p.1+p.2)|/2 ∂positiveVolume.prod positiveVolume := by
      apply integral_mono_ae hi.norm (hc.norm.div_const 2)
      rw [Measure.prod_restrict]
      apply ae_restrict_of_forall_mem (measurableSet_Ioi.prod measurableSet_Ioi)
      rintro ⟨t,s⟩ ⟨ht,hs⟩
      exact kernelPair_separation_le ht hs F G
    _ = (∫ p, |G (1-p.1)*F (1+p.2)/(p.1+p.2)| ∂positiveVolume.prod positiveVolume)/2 := by
      rw [integral_div]
    _ ≤ (π * ‖(memLp_separation_left hG).toLp (fun t => G (1-t))‖ *
      ‖(memLp_separation_right hF).toLp (fun s => F (1+s))‖)/2 :=
        div_le_div_of_nonneg_right
          (integral_abs_carleman_le (memLp_separation_left hG) (memLp_separation_right hF))
          (by norm_num)
    _ ≤ (π * ‖hG.toLp G‖ * ‖hF.toLp F‖)/2 := by
      gcongr
      · exact norm_separation_left_le hG
      · exact norm_separation_right_le hF
    _ = _ := by ring

/-- The original real-dilation cubic integrand, with its actual two variables. -/
def cubicIntegrand (F G : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  G p.2 * F (p.1 * p.2) / (p.1 * (p.1 ^ 2 - 1))

/-- The exact physical Jacobian, including the cubic denominator. -/
theorem cubicIntegrand_eq_scaled_kernel {r θ : ℝ} (hr : 1<r) (hθ : 0<θ) (F G : ℝ → ℝ) :
    cubicIntegrand F G (r,θ) = θ * kernelPair F G (θ,θ*r) := by
  have hd : 0 < r*(r^2-1) := mul_pos (by linarith) (by nlinarith)
  have he : (θ*r)*((θ*r)^2-θ^2) = θ^3*(r*(r^2-1)) := by ring
  simp only [cubicIntegrand, kernelPair, kernel, ite_eq_left hθ]
  rw [he, mul_comm r θ]
  field_simp [hθ.ne', hd.ne']

private theorem integral_Ioi_eq_of_zero_le_one {h : ℝ → ℝ}
    (hh : ∀ η ≤ 1, h η = 0) {c : ℝ} (hc : c ≤ 1) :
    (∫ η in Ioi c, h η) = ∫ η in Ioi (1 : ℝ), h η := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun η hη =>
    hh η (by simp only [mem_Ioi, not_lt] at hη; exact hη.trans hc)),
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun η hη =>
      hh η (by simpa only [mem_Ioi, not_lt] using hη))]

/-- The signed fibre change of variables needs no integral interchange. -/
theorem integral_cubic_fiber {θ : ℝ} (hθ : 0<θ) (hθ1 : θ<1)
    {F G : ℝ → ℝ} (hFs : ∀ η ≤ 1, F η=0) :
    (∫ r in Ioi (1 : ℝ), cubicIntegrand F G (r,θ))
      = ∫ η, kernelPair F G (θ,η) ∂rightVolume := by
  rw [setIntegral_congr_fun measurableSet_Ioi
    (fun r hr => cubicIntegrand_eq_scaled_kernel hr hθ F G), integral_const_mul,
    integral_comp_mul_left_Ioi (fun η => kernelPair F G (θ,η)) 1 hθ]
  simp only [smul_eq_mul, mul_one]
  rw [← mul_assoc, mul_inv_cancel₀ hθ.ne', one_mul]
  apply integral_Ioi_eq_of_zero_le_one _ hθ1.le
  intro η hη
  simp only [kernelPair, hFs η hη, mul_zero, zero_mul]

/-- The absolute fibre change of variables is exact as well. -/
theorem integral_norm_cubic_fiber {θ : ℝ} (hθ : 0<θ) (hθ1 : θ<1)
    {F G : ℝ → ℝ} (hFs : ∀ η ≤ 1, F η=0) :
    (∫ r in Ioi (1 : ℝ), ‖cubicIntegrand F G (r,θ)‖)
      = ∫ η, ‖kernelPair F G (θ,η)‖ ∂rightVolume := by
  have he : (∫ r in Ioi (1 : ℝ), ‖cubicIntegrand F G (r,θ)‖) =
      ∫ r in Ioi (1 : ℝ), θ * ‖kernelPair F G (θ,θ*r)‖ := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    change ‖cubicIntegrand F G (r,θ)‖ = θ * ‖kernelPair F G (θ,θ*r)‖
    rw [cubicIntegrand_eq_scaled_kernel hr hθ F G, norm_mul, Real.norm_eq_abs, abs_of_pos hθ]
  rw [he, integral_const_mul,
    integral_comp_mul_left_Ioi (fun η => ‖kernelPair F G (θ,η)‖) 1 hθ]
  simp only [smul_eq_mul, mul_one]
  rw [← mul_assoc, mul_inv_cancel₀ hθ.ne', one_mul]
  apply integral_Ioi_eq_of_zero_le_one _ hθ1.le
  intro η hη
  simp only [kernelPair, hFs η hη, mul_zero, zero_mul, norm_zero]

/-- Genuine fibre integrability passes through the physical Jacobian. -/
theorem integrable_cubic_fiber {θ : ℝ} (hθ : 0<θ) (_hθ1 : θ<1)
    {F G : ℝ → ℝ} (hFs : ∀ η ≤ 1, F η=0)
    (hi : Integrable (fun η => kernelPair F G (θ,η)) rightVolume) :
    Integrable (fun r => cubicIntegrand F G (r,θ)) rightVolume := by
  have hglob : Integrable (fun η => kernelPair F G (θ,η)) volume :=
    IntegrableOn.integrable_of_forall_notMem_eq_zero (s := Ioi 1) hi (fun η hη => by
      simp only [mem_Ioi, not_lt] at hη
      simp only [kernelPair, hFs η hη, mul_zero, zero_mul])
  have hiθ : IntegrableOn (fun η => kernelPair F G (θ,η)) (Ioi (θ*1)) volume := by
    rw [mul_one]
    exact hglob.restrict
  have hs := (integrableOn_Ioi_comp_mul_left_iff
    (fun η => kernelPair F G (θ,η)) 1 hθ).mpr hiθ
  refine IntegrableOn.congr_fun (hs.const_mul θ) (fun r hr => ?_) measurableSet_Ioi
  exact (cubicIntegrand_eq_scaled_kernel hr hθ F G).symm

private theorem kernelPair_zero_left {F G : ℝ → ℝ} {θ : ℝ} (hθ : θ≤0) (η : ℝ) :
    kernelPair F G (θ,η) = 0 := by
  simp only [kernelPair, kernel, ite_eq_right (not_lt.mpr hθ), mul_zero]

/-- The original cubic integral is absolutely jointly integrable. The endpoint `θ=1`
is null; every support and Jacobian used in the proof is retained explicitly. -/
theorem integrable_cubicIntegrand {F G : ℝ → ℝ} (hFm : Measurable F) (hGm : Measurable G)
    (hF : MemLp F 2 volume) (hG : MemLp G 2 volume)
    (hFs : ∀ η ≤ 1, F η=0) (hGs : ∀ θ, 1<θ → G θ=0) :
    Integrable (cubicIntegrand F G) (rightVolume.prod positiveVolume) := by
  have hk := integrable_kernelPair hFm hGm hF hG
  have hkae : ∀ᵐ θ ∂volume, θ<1 → Integrable (fun η => kernelPair F G (θ,η)) rightVolume :=
    (ae_restrict_iff' measurableSet_Iio).mp hk.prod_right_ae
  have hm : Measurable (cubicIntegrand F G) :=
    ((hGm.comp measurable_snd).mul
      (hFm.comp (measurable_fst.mul measurable_snd))).div
        (measurable_fst.mul (measurable_fst.pow_const 2 |>.sub measurable_const))
  apply (integrable_prod_iff' hm.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [ae_restrict_of_ae hkae, positiveVolume.ae_ne 1,
      ae_restrict_mem measurableSet_Ioi] with θ hkθ hθne hθ
    change 0<θ at hθ
    rcases lt_or_gt_of_ne hθne with hθ1 | hθ1
    · exact integrable_cubic_fiber hθ hθ1 hFs (hkθ hθ1)
    · simp only [cubicIntegrand, hGs θ hθ1, zero_mul, zero_div]
      exact integrable_zero _ _ _
  · have hc : Integrable ((Iio (1 : ℝ)).indicator
        (fun θ => ∫ η, ‖kernelPair F G (θ,η)‖ ∂rightVolume)) volume :=
      IntegrableOn.integrable_indicator hk.integral_norm_prod_left measurableSet_Iio
    refine hc.restrict.congr ?_
    filter_upwards [positiveVolume.ae_ne 1, ae_restrict_mem measurableSet_Ioi] with θ hθne hθ
    change 0<θ at hθ
    rcases lt_or_gt_of_ne hθne with hθ1 | hθ1
    · rw [indicator_of_mem (show θ∈Iio (1 : ℝ) from hθ1)]
      exact (integral_norm_cubic_fiber hθ hθ1 hFs).symm
    · simp only [indicator_of_notMem (show θ∉Iio (1 : ℝ) from not_lt.mpr hθ1.le), cubicIntegrand,
        hGs θ hθ1, zero_mul, zero_div, norm_zero, integral_zero]

/-- Exact Fubini and physical change of variables for the actual cubic dilation term. -/
theorem integral_cubic_eq_kernelPair {F G : ℝ → ℝ} (hFm : Measurable F) (hGm : Measurable G)
    (hF : MemLp F 2 volume) (hG : MemLp G 2 volume)
    (hFs : ∀ η ≤ 1, F η=0) (hGs : ∀ θ, 1<θ → G θ=0) :
    (∫ r in Ioi (1 : ℝ), Cvs.WeilForm.PoleTermDilationMean.dilR G F r/(r*(r^2-1)))
      = ∫ p, kernelPair F G p ∂leftVolume.prod rightVolume := by
  have hi := integrable_cubicIntegrand hFm hGm hF hG hFs hGs
  have he : (∫ r in Ioi (1 : ℝ), Cvs.WeilForm.PoleTermDilationMean.dilR G F r/(r*(r^2-1))) =
      ∫ r, ∫ θ, cubicIntegrand F G (r,θ) ∂positiveVolume ∂rightVolume := by
    simp only [Cvs.WeilForm.PoleTermDilationMean.dilR, cubicIntegrand, integral_div]
  have hi' : Integrable (Function.uncurry (fun r θ => cubicIntegrand F G (r,θ)))
      (rightVolume.prod positiveVolume) := hi
  rw [he, integral_integral_swap hi', integral_prod _ (integrable_kernelPair hFm hGm hF hG)]
  change (∫ θ, ∫ r, cubicIntegrand F G (r,θ) ∂rightVolume ∂positiveVolume) =
    ∫ θ in Iio (1 : ℝ), ∫ η, kernelPair F G (θ,η) ∂rightVolume
  rw [← integral_indicator measurableSet_Iio]
  have hz : ∀ θ, θ∉Ioi (0 : ℝ) →
      ((Iio (1 : ℝ)).indicator (fun θ => ∫ η, kernelPair F G (θ,η) ∂rightVolume)) θ=0 := by
    intro θ hθ
    simp only [mem_Ioi, not_lt] at hθ
    by_cases h1 : θ<1
    · rw [indicator_of_mem (show θ∈Iio (1 : ℝ) from h1)]
      simp only [kernelPair_zero_left hθ, integral_zero]
    · exact indicator_of_notMem (show θ∉Iio (1 : ℝ) from h1) _
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz]
  apply integral_congr_ae
  filter_upwards [positiveVolume.ae_ne 1, ae_restrict_mem measurableSet_Ioi] with θ hθne hθ
  change 0<θ at hθ
  rcases lt_or_gt_of_ne hθne with hθ1 | hθ1
  · rw [indicator_of_mem (show θ∈Iio (1 : ℝ) from hθ1)]
    exact integral_cubic_fiber hθ hθ1 hFs
  · simp only [indicator_of_notMem (show θ∉Iio (1 : ℝ) from not_lt.mpr hθ1.le), cubicIntegrand,
      hGs θ hθ1, zero_mul, zero_div, integral_zero]

/-- The actual cubic arch/pole correction is bounded by `π/2` on physical L². -/
theorem abs_integral_cubic_le {F G : ℝ → ℝ} (hFm : Measurable F) (hGm : Measurable G)
    (hF : MemLp F 2 volume) (hG : MemLp G 2 volume)
    (hFs : ∀ η ≤ 1, F η=0) (hGs : ∀ θ, 1<θ → G θ=0) :
    |∫ r in Ioi (1 : ℝ), Cvs.WeilForm.PoleTermDilationMean.dilR G F r/(r*(r^2-1))|
      ≤ (π/2) * ‖hF.toLp F‖ * ‖hG.toLp G‖ := by
  rw [integral_cubic_eq_kernelPair hFm hGm hF hG hFs hGs]
  exact abs_integral_kernelPair_le hFm hGm hF hG

end Cvs.WeilForm.CubicTailSeparatedKernel
