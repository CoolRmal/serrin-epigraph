module

public import SerrinEpigraph.PerimeterLocality
public import SerrinEpigraph.VectorIntegrationByParts
public import SerrinEpigraph.MollificationDerivative
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Analysis.Calculus.Deriv.Abs
public import Mathlib.Topology.MetricSpace.Contracting

/-!
# Diffeomorphism transformation and first variation of variational perimeter

This module establishes BV9 from the perimeter regularity programme:
1. Smoothness and Jacobi linearization of the continuous-linear determinant on `Space d`,
   together with the Piola divergence identity proved via distributional integration by parts.
2. Exact diffeomorphism transformation formulas (`variationalPerimeter_image_diffeomorph_lintegral`
   and `variationalPerimeter_image_diffeomorph`, BV9.1) and affine translation/dilation scaling
   corollaries (`variationalPerimeter_add_smul`, `variationalPerimeter_smul`,
   `variationalPerimeter_add`).
3. Global `C²` perturbation diffeomorphisms `Φ_t x = x + t • X x` via Banach contraction and the
   smooth inverse function theorem, yielding the first variation stationarity identity
   (`perimeter_first_variation_eq_zero`, BV9.2) for compactly supported `C¹` vector fields.
-/

public section

noncomputable section

open Set MeasureTheory Metric Filter InnerProductSpace ContinuousLinearMap
open scoped Topology ENNReal NNReal CompactlySupported Convolution

namespace SerrinEpigraph

/-! ### Section 1: Determinant calculus and the Piola identity -/

/-- Expansion of the determinant of a continuous linear endomorphism in an orthonormal basis. -/
theorem clm_det_eq_sum_perm {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) (L : Space d →L[ℝ] Space d) :
    LinearMap.det L.toLinearMap =
      ∑ σ : Equiv.Perm (Fin d),
        (Equiv.Perm.sign σ : ℝ) * ∏ i : Fin d, inner ℝ (b (σ i)) (L (b i)) := by
  rw [← LinearMap.det_toMatrix b.toBasis, Matrix.det_apply']
  apply Finset.sum_congr rfl
  intro σ _
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [LinearMap.toMatrix_apply, b.coe_toBasis_repr_apply, b.repr_apply_apply]
  simp

/-- The determinant on `Space d →L[ℝ] Space d` is smooth of arbitrary order. -/
theorem contDiff_clm_det {d : ℕ} {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun L : Space d →L[ℝ] Space d ↦ LinearMap.det L.toLinearMap) := by
  let b := EuclideanSpace.basisFun (Fin d) ℝ
  have heq : (fun L : Space d →L[ℝ] Space d ↦ LinearMap.det L.toLinearMap) =
      fun L ↦ ∑ σ : Equiv.Perm (Fin d),
        (Equiv.Perm.sign σ : ℝ) * ∏ i : Fin d, inner ℝ (b (σ i)) (L (b i)) := by
    funext L
    exact clm_det_eq_sum_perm b L
  rw [heq]
  refine ContDiff.sum fun σ _ ↦ contDiff_const.mul (contDiff_prod fun i _ ↦ ?_)
  exact ((innerSL ℝ (b (σ i))).comp (ContinuousLinearMap.apply ℝ (Space d) (b i))).contDiff

/-- If a permutation fixes every element outside `{k}`, it must be the identity permutation. -/
private theorem perm_eq_one_of_forall_erase_eq {d : ℕ} {σ : Equiv.Perm (Fin d)} {k : Fin d}
    (h : ∀ i ∈ Finset.univ.erase k, σ i = i) : σ = 1 := by
  apply Equiv.ext
  intro j
  by_cases hjk : j = k
  · subst hjk
    by_contra hne
    have hne' : σ j ≠ j := hne
    have hinv_ne : σ.symm j ≠ j := fun heq ↦ hne' (by simpa using congrArg σ heq.symm)
    have hfix := h (σ.symm j) (Finset.mem_erase.mpr ⟨hinv_ne, Finset.mem_univ _⟩)
    rw [Equiv.apply_symm_apply] at hfix
    exact hinv_ne hfix.symm
  · exact h j (Finset.mem_erase.mpr ⟨hjk, Finset.mem_univ _⟩)

/-- Jacobi's formula at the identity: differentiating `det (I + t A)` at `t = 0` yields `trace A`. -/
theorem hasDerivAt_det_one_add_smul {d : ℕ} (A : Space d →L[ℝ] Space d) :
    HasDerivAt (fun t : ℝ ↦ LinearMap.det ((1 : Space d →L[ℝ] Space d) + t • A).toLinearMap)
      (LinearMap.trace ℝ (Space d) A.toLinearMap) 0 := by
  let b := EuclideanSpace.basisFun (Fin d) ℝ
  rw [LinearMap.trace_eq_sum_inner A.toLinearMap b]
  let m : ℝ → Fin d → Fin d → ℝ := fun t i j ↦
    inner ℝ (b i) (b j) + t * inner ℝ (b i) (A (b j))
  have hm_eq (t : ℝ) (i j : Fin d) :
      inner ℝ (b i) (((1 : Space d →L[ℝ] Space d) + t • A) (b j)) = m t i j := by
    simp [m, inner_add_right, real_inner_smul_right]
  have hdet (t : ℝ) :
      LinearMap.det ((1 : Space d →L[ℝ] Space d) + t • A).toLinearMap =
        ∑ σ : Equiv.Perm (Fin d), (Equiv.Perm.sign σ : ℝ) * ∏ i : Fin d, m t (σ i) i := by
    rw [clm_det_eq_sum_perm b]
    simp_rw [hm_eq]
  simp_rw [hdet]
  have hm_deriv (i j : Fin d) :
      HasDerivAt (fun t : ℝ ↦ m t i j) (inner ℝ (b i) (A (b j))) 0 := by
    simpa [m] using (hasDerivAt_id (0 : ℝ)).mul_const (inner ℝ (b i) (A (b j)))
      |>.const_add (inner ℝ (b i) (b j))
  have hterm (σ : Equiv.Perm (Fin d)) :
      HasDerivAt (fun t ↦ (Equiv.Perm.sign σ : ℝ) * ∏ i : Fin d, m t (σ i) i)
        (if σ = 1 then ∑ k : Fin d, inner ℝ (b k) (A (b k)) else 0) 0 := by
    have hprod := HasDerivAt.fun_finsetProd (u := (Finset.univ : Finset (Fin d)))
      (f := fun i t ↦ m t (σ i) i) (f' := fun i ↦ inner ℝ (b (σ i)) (A (b i)))
      (fun i _ ↦ hm_deriv (σ i) i)
    have hmul := hprod.const_mul (Equiv.Perm.sign σ : ℝ)
    refine hmul.congr_deriv ?_
    by_cases hσ : σ = 1
    · subst hσ
      simp only [↓reduceIte, Equiv.Perm.sign_one, Units.val_one, Int.cast_one, one_mul,
        Equiv.Perm.coe_one, id_eq, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro k _
      have hp1 : (∏ i ∈ Finset.univ.erase k, m 0 i i) = 1 := by
        apply Finset.prod_eq_one
        intro i _
        simp [m, b.orthonormal.1]
      rw [hp1, one_mul]
    · simp only [hσ, ↓reduceIte, smul_eq_mul]
      suffices hsum0 : (∑ k : Fin d,
          (∏ i ∈ Finset.univ.erase k, m 0 (σ i) i) * inner ℝ (b (σ k)) (A (b k))) = 0 by
        rw [hsum0, mul_zero]
      apply Finset.sum_eq_zero
      intro k _
      suffices hp0 : (∏ i ∈ Finset.univ.erase k, m 0 (σ i) i) = 0 by
        rw [hp0, zero_mul]
      by_contra hne
      have hall : ∀ i ∈ Finset.univ.erase k, σ i = i := by
        intro i hi
        have hmi : m 0 (σ i) i ≠ 0 := fun hz ↦ hne (Finset.prod_eq_zero hi hz)
        by_contra hsi
        apply hmi
        have ho : inner ℝ (b (σ i)) (b i) = 0 := b.orthonormal.2 hsi
        simp [m, ho]
      exact hσ (perm_eq_one_of_forall_erase_eq hall)
  have hsum := HasDerivAt.fun_sum (u := (Finset.univ : Finset (Equiv.Perm (Fin d))))
    (fun σ _ ↦ hterm σ)
  convert hsum using 1
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  rfl

/-- A differentiable map with a differentiable left inverse has nowhere-vanishing Jacobian. -/
theorem det_fderiv_diffeomorph_ne_zero {d : ℕ} {Φ Ψ : Space d → Space d}
    (hΦ : Differentiable ℝ Φ) (hΨ : Differentiable ℝ Ψ)
    (hΨΦ : ∀ x, Ψ (Φ x) = x) (x : Space d) :
    LinearMap.det (fderiv ℝ Φ x).toLinearMap ≠ 0 := by
  have hcomp : ((fderiv ℝ Ψ (Φ x)).comp (fderiv ℝ Φ x)) = ContinuousLinearMap.id ℝ (Space d) := by
    have hd := ((hΨ (Φ x)).hasFDerivAt.comp x (hΦ x).hasFDerivAt).fderiv
    have hid : fderiv ℝ (Ψ ∘ Φ) x = ContinuousLinearMap.id ℝ (Space d) := by
      rw [show Ψ ∘ Φ = id from funext hΨΦ]
      exact (hasFDerivAt_id x).fderiv
    exact hd.symm.trans hid
  have hdet := congrArg (fun L : Space d →L[ℝ] Space d ↦ LinearMap.det L.toLinearMap) hcomp
  change LinearMap.det ((fderiv ℝ Ψ (Φ x)).toLinearMap.comp (fderiv ℝ Φ x).toLinearMap) =
    LinearMap.det LinearMap.id at hdet
  rw [LinearMap.det_comp, LinearMap.det_id] at hdet
  exact right_ne_zero_of_mul_eq_one hdet

/-- For a `C²` map with a differentiable left inverse, `|det DΦ|` is `C¹`. -/
theorem contDiff_abs_det_fderiv {d : ℕ} {Φ Ψ : Space d → Space d}
    (hΦ : ContDiff ℝ 2 Φ) (hΨ : Differentiable ℝ Ψ) (hΨΦ : ∀ x, Ψ (Φ x) = x) :
    ContDiff ℝ 1 (fun x ↦ |LinearMap.det (fderiv ℝ Φ x).toLinearMap|) := by
  have hdet : ContDiff ℝ 1 (fun x ↦ LinearMap.det (fderiv ℝ Φ x).toLinearMap) :=
    contDiff_clm_det.comp (hΦ.fderiv_right (m := 1) (by norm_num))
  rw [contDiff_iff_contDiffAt]
  intro x
  exact (contDiffAt_abs (det_fderiv_diffeomorph_ne_zero (hΦ.differentiable (by norm_num))
    hΨ hΨΦ x)).comp x hdet.contDiffAt

/-- The Piola divergence identity for a global `C²` diffeomorphism `(Φ, Ψ)` and any `C¹` vector
field `Y`, proved without second-derivative index expansions by testing against smooth compactly
supported scalar functions and integrating by parts. -/
theorem fieldDivergence_piola {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d))
    {Φ Ψ Y : Space d → Space d}
    (hΦ : ContDiff ℝ 2 Φ) (hΨ : ContDiff ℝ 2 Ψ)
    (hΨΦ : ∀ x, Ψ (Φ x) = x) (hΦΨ : ∀ y, Φ (Ψ y) = y)
    (hY : ContDiff ℝ 1 Y) (x : Space d) :
    fieldDivergence b
      (fun z ↦ |LinearMap.det (fderiv ℝ Φ z).toLinearMap| • (fderiv ℝ Ψ (Φ z) (Y (Φ z)))) x =
      |LinearMap.det (fderiv ℝ Φ x).toLinearMap| * fieldDivergence b Y (Φ x) := by
  let Z : Space d → Space d :=
    fun z ↦ |LinearMap.det (fderiv ℝ Φ z).toLinearMap| • (fderiv ℝ Ψ (Φ z) (Y (Φ z)))
  have hΦ1 : ContDiff ℝ 1 Φ := hΦ.of_le (by norm_num)
  have hΨ1 : ContDiff ℝ 1 Ψ := hΨ.of_le (by norm_num)
  have hZ : ContDiff ℝ 1 Z := by
    have habs := contDiff_abs_det_fderiv hΦ (hΨ.differentiable (by norm_num)) hΨΦ
    have hdΨ : ContDiff ℝ 1 (fun z ↦ fderiv ℝ Ψ (Φ z)) :=
      (hΨ.fderiv_right (m := 1) (by norm_num)).comp hΦ1
    exact habs.smul (hdΨ.clm_apply (hY.comp hΦ1))
  have hLHS_cont : Continuous (fieldDivergence b Z) :=
    continuous_finsetSum _ fun i _ ↦ continuous_const.inner
      ((hZ.continuous_fderiv one_ne_zero).clm_apply continuous_const)
  have hYdiv_cont : Continuous (fieldDivergence b Y) :=
    continuous_finsetSum _ fun i _ ↦ continuous_const.inner
      ((hY.continuous_fderiv one_ne_zero).clm_apply continuous_const)
  have hRHS_cont : Continuous
      (fun z ↦ |LinearMap.det (fderiv ℝ Φ z).toLinearMap| * fieldDivergence b Y (Φ z)) :=
    (contDiff_abs_det_fderiv hΦ (hΨ.differentiable (by norm_num)) hΨΦ).continuous.mul
      (hYdiv_cont.comp hΦ.continuous)
  let eΦ : Space d ≃ₜ Space d :=
    { toFun := Φ
      invFun := Ψ
      left_inv := hΨΦ
      right_inv := hΦΨ
      continuous_toFun := hΦ.continuous
      continuous_invFun := hΨ.continuous }
  have hinj : Set.InjOn Φ Set.univ := fun _ _ _ _ h ↦ eΦ.injective h
  have himg_univ : Φ '' Set.univ = Set.univ := by
    rw [image_univ]
    exact eΦ.surjective.range_eq
  have hfderiv_within : ∀ z ∈ (Set.univ : Set (Space d)),
      HasFDerivWithinAt Φ (fderiv ℝ Φ z) Set.univ z :=
    fun z _ ↦ hasFDerivWithinAt_univ.mpr (hΦ1.differentiable one_ne_zero z).hasFDerivAt
  have hae : fieldDivergence b Z =ᵐ[volume]
      (fun z ↦ |LinearMap.det (fderiv ℝ Φ z).toLinearMap| * fieldDivergence b Y (Φ z)) := by
    apply ae_eq_of_integral_contDiff_smul_eq hLHS_cont.locallyIntegrable hRHS_cont.locallyIntegrable
    intro η hη hηc
    have hη1 : ContDiff ℝ 1 η := hη.of_le (by simp)
    let φ : Space d → ℝ := fun y ↦ η (Ψ y)
    have hφ1 : ContDiff ℝ 1 φ := hη1.comp hΨ1
    have hφc : HasCompactSupport φ := hηc.comp_homeomorph eΦ.symm
    have hdiv_sum (F : Space d → Space d) (z : Space d) :
        (∑ i, inner ℝ (fderiv ℝ F z (b i)) (b i)) = fieldDivergence b F z := by
      unfold fieldDivergence
      exact Finset.sum_congr rfl fun i _ ↦ real_inner_comm _ _
    have hibp_Z := integral_inner_field_gradient (μ := volume) isOpen_univ hZ.contDiffOn
      hη1 hηc (subset_univ _) b
    simp_rw [hdiv_sum] at hibp_Z
    have hibp_Y := integral_inner_field_gradient (μ := volume) isOpen_univ hY.contDiffOn
      hφ1 hφc (subset_univ _) b
    simp_rw [hdiv_sum] at hibp_Y
    have hcov1 : (∫ y, fieldDivergence b Y y * φ y) =
        ∫ z, |LinearMap.det (fderiv ℝ Φ z).toLinearMap| * (fieldDivergence b Y (Φ z) * η z) := by
      have h := MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul (μ := volume)
        MeasurableSet.univ hfderiv_within hinj (fun y ↦ fieldDivergence b Y y * φ y)
      rw [himg_univ, Measure.restrict_univ] at h
      simpa only [φ, hΨΦ, smul_eq_mul, ContinuousLinearMap.det] using h
    have hcov2 : (∫ y, inner ℝ (Y y) (gradient φ y)) =
        ∫ z, inner ℝ (Z z) (gradient η z) := by
      have h := MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul (μ := volume)
        MeasurableSet.univ hfderiv_within hinj (fun y ↦ inner ℝ (Y y) (gradient φ y))
      rw [himg_univ, Measure.restrict_univ] at h
      refine h.trans (integral_congr_ae (Eventually.of_forall fun z ↦ ?_))
      have hchain : fderiv ℝ φ (Φ z) = (fderiv ℝ η z).comp (fderiv ℝ Ψ (Φ z)) := by
        have hd := ((hη1.differentiable one_ne_zero (Ψ (Φ z))).hasFDerivAt.comp (Φ z)
          (hΨ1.differentiable one_ne_zero (Φ z)).hasFDerivAt).fderiv
        simpa only [Function.comp_def, hΨΦ z] using hd
      have hgrad : inner ℝ (Y (Φ z)) (gradient φ (Φ z)) =
          inner ℝ (fderiv ℝ Ψ (Φ z) (Y (Φ z))) (gradient η z) := by
        rw [real_inner_comm (gradient φ (Φ z)) (Y (Φ z)), inner_gradient_left, hchain,
          ContinuousLinearMap.comp_apply, ← inner_gradient_left,
          real_inner_comm (gradient η z)]
      simp only [Z, smul_eq_mul, ContinuousLinearMap.det, hgrad, real_inner_smul_left]
    have hL : (∫ z, η z • fieldDivergence b Z z) = -∫ z, inner ℝ (Z z) (gradient η z) := by
      have hmul : (fun z ↦ η z • fieldDivergence b Z z) =
          fun z ↦ fieldDivergence b Z z * η z := funext fun z ↦ mul_comm _ _
      rw [hmul]
      linarith [hibp_Z]
    have hR : (∫ z, η z • (|LinearMap.det (fderiv ℝ Φ z).toLinearMap| *
        fieldDivergence b Y (Φ z))) = -∫ y, inner ℝ (Y y) (gradient φ y) := by
      have hmul : (fun z ↦ η z • (|LinearMap.det (fderiv ℝ Φ z).toLinearMap| *
          fieldDivergence b Y (Φ z))) =
          fun z ↦ |LinearMap.det (fderiv ℝ Φ z).toLinearMap| *
            (fieldDivergence b Y (Φ z) * η z) := funext fun z ↦ by simp [smul_eq_mul]; ring
      rw [hmul, ← hcov1]
      linarith [hibp_Y]
    rw [hL, hR, hcov2]
  exact congrFun ((hLHS_cont.ae_eq_iff_eq volume hRHS_cont).mp hae) x

/-! ### Section 2: Diffeomorphism pushforward of variational perimeter (BV9.1) -/

/-- Exact pairing identity transforming divergence tests on `Φ '' O` into polar integrals on `O`. -/
theorem diffeomorph_divergence_pairing_eq {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {E Ω O : Set (Space d)}
    (hO : IsOpen O) (hOΩ : O ⊆ Ω)
    {Φ Ψ : Space d → Space d}
    (hΦ : ContDiff ℝ 2 Φ) (hΨ : ContDiff ℝ 2 Ψ)
    (hΨΦ : ∀ x, Ψ (Φ x) = x) (hΦΨ : ∀ y, Φ (Ψ y) = y)
    (μ : Measure (Space d)) {ν : Space d → Space d}
    (hdist : ∀ F : C_c(Space d, Space d), ContDiff ℝ 1 (F : Space d → Space d) →
      tsupport F ⊆ Ω →
      -(∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F x) =
        ∫ x, inner ℝ (F x) (ν x) ∂μ.restrict Ω)
    {Y : Space d → Space d} (hY : ContDiff ℝ 1 Y) (hYc : HasCompactSupport Y)
    (hYs : tsupport Y ⊆ Φ '' O) :
    -(∫ y, (Φ '' E).indicator (fun _ ↦ (1 : ℝ)) y * fieldDivergence b Y y) =
      ∫ x in O, inner ℝ (Y (Φ x))
        (|LinearMap.det (fderiv ℝ Φ x).toLinearMap| •
          ((fderiv ℝ Ψ (Φ x)).adjoint (ν x))) ∂μ := by
  let eΦ : Space d ≃ₜ Space d :=
    { toFun := Φ
      invFun := Ψ
      left_inv := hΨΦ
      right_inv := hΦΨ
      continuous_toFun := hΦ.continuous
      continuous_invFun := hΨ.continuous }
  let Z : Space d → Space d :=
    fun x ↦ |LinearMap.det (fderiv ℝ Φ x).toLinearMap| • (fderiv ℝ Ψ (Φ x) (Y (Φ x)))
  have hΦ1 : ContDiff ℝ 1 Φ := hΦ.of_le (by norm_num)
  have hZ : ContDiff ℝ 1 Z :=
    (contDiff_abs_det_fderiv hΦ (hΨ.differentiable (by norm_num)) hΨΦ).smul
      (((hΨ.fderiv_right (m := 1) (by norm_num)).comp hΦ1).clm_apply (hY.comp hΦ1))
  have hZ_supp : tsupport Z ⊆ Ψ '' tsupport Y := by
    apply closure_minimal _ (hYc.image hΨ.continuous).isClosed
    intro x hx
    by_contra hnot
    apply hx
    have hy : Φ x ∉ tsupport Y := fun hmem ↦ hnot ⟨Φ x, hmem, hΨΦ x⟩
    simp [Z, image_eq_zero_of_notMem_tsupport hy]
  have hZc : HasCompactSupport Z :=
    (hYc.image hΨ.continuous).of_isClosed_subset (isClosed_tsupport Z) hZ_supp
  have hZO : tsupport Z ⊆ O := by
    refine hZ_supp.trans ?_
    rintro _ ⟨y, hy, rfl⟩
    rcases hYs hy with ⟨x, hxO, rfl⟩
    rwa [hΨΦ]
  let Zc : C_c(Space d, Space d) := ⟨⟨Z, hZ.continuous⟩, hZc⟩
  have hcov : (∫ y, (Φ '' E).indicator (fun _ ↦ (1 : ℝ)) y * fieldDivergence b Y y) =
      ∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b Z x := by
    have hinj : Set.InjOn Φ Set.univ := fun _ _ _ _ h ↦ eΦ.injective h
    have himg : Φ '' Set.univ = Set.univ := by
      rw [image_univ]
      exact eΦ.surjective.range_eq
    have hfderiv_within : ∀ x ∈ (Set.univ : Set (Space d)),
        HasFDerivWithinAt Φ (fderiv ℝ Φ x) Set.univ x :=
      fun x _ ↦ hasFDerivWithinAt_univ.mpr (hΦ1.differentiable one_ne_zero x).hasFDerivAt
    have h := MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul (μ := volume)
      MeasurableSet.univ hfderiv_within hinj
      (fun y ↦ (Φ '' E).indicator (fun _ ↦ (1 : ℝ)) y * fieldDivergence b Y y)
    rw [himg, Measure.restrict_univ] at h
    refine h.trans (integral_congr_ae (Eventually.of_forall fun x ↦ ?_))
    have hind : (Φ '' E).indicator (fun _ ↦ (1 : ℝ)) (Φ x) =
        E.indicator (fun _ ↦ (1 : ℝ)) x := by
      have hmem : Φ x ∈ Φ '' E ↔ x ∈ E := eΦ.injective.mem_set_image
      by_cases hxE : x ∈ E <;> simp [hmem, hxE]
    simp only [Z, hind, smul_eq_mul, ContinuousLinearMap.det]
    rw [← mul_assoc, mul_comm |LinearMap.det (fderiv ℝ Φ x).toLinearMap|, mul_assoc,
      ← fieldDivergence_piola b hΦ hΨ hΨΦ hΦΨ hY x]
  rw [hcov]
  have hid := hdist Zc hZ (hZO.trans hOΩ)
  change -(∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b Z x) =
    ∫ x, inner ℝ (Z x) (ν x) ∂μ.restrict Ω at hid
  rw [hid]
  have hrestrict : (∫ x, inner ℝ (Z x) (ν x) ∂μ.restrict Ω) =
      ∫ x in O, inner ℝ (Z x) (ν x) ∂μ := by
    have h1 : (∫ x, inner ℝ (Z x) (ν x) ∂μ.restrict Ω) =
        ∫ x in O, inner ℝ (Z x) (ν x) ∂(μ.restrict Ω) := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hxO
      have hz : Z x = 0 := image_eq_zero_of_notMem_tsupport (fun hh ↦ hxO (hZO hh))
      simp [hz]
    rw [h1, Measure.restrict_restrict hO.measurableSet, inter_eq_left.mpr hOΩ]
  rw [hrestrict]
  refine setIntegral_congr_fun hO.measurableSet fun x _ ↦ ?_
  simp only [Z, real_inner_smul_left, real_inner_smul_right,
    ContinuousLinearMap.adjoint_inner_right]

/-- Exact `lintegral` diffeomorphism transformation formula for variational perimeter on any open
subset `O ⊆ Ω`, requiring no global boundedness of the derivative of `Φ`. -/
theorem variationalPerimeter_image_diffeomorph_lintegral {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {E Ω O : Set (Space d)}
    (hO : IsOpen O) (hOΩ : O ⊆ Ω)
    {Φ Ψ : Space d → Space d}
    (hΦ : ContDiff ℝ 2 Φ) (hΨ : ContDiff ℝ 2 Ψ)
    (hΨΦ : ∀ x, Ψ (Φ x) = x) (hΦΨ : ∀ y, Φ (Ψ y) = y)
    (μ : Measure (Space d)) {ν : Space d → Space d}
    (hν : Integrable ν (μ.restrict Ω))
    (hνunit : ∀ᵐ x ∂μ.restrict Ω, ‖ν x‖ = 1)
    (hdist : ∀ F : C_c(Space d, Space d), ContDiff ℝ 1 (F : Space d → Space d) →
      tsupport F ⊆ Ω →
      -(∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F x) =
        ∫ x, inner ℝ (F x) (ν x) ∂μ.restrict Ω) :
    variationalPerimeter b (Φ '' E) (Φ '' O) =
      ∫⁻ x in O, ‖|LinearMap.det (fderiv ℝ Φ x).toLinearMap| •
        ((fderiv ℝ Ψ (Φ x)).adjoint (ν x))‖ₑ ∂μ := by
  let A_op : Space d → (Space d →L[ℝ] Space d) :=
    fun x ↦ |LinearMap.det (fderiv ℝ Φ x).toLinearMap| • (fderiv ℝ Ψ (Φ x)).adjoint
  let W : Space d → Space d := fun x ↦ A_op x (ν x)
  have hA_cont : Continuous A_op :=
    (contDiff_abs_det_fderiv hΦ (hΨ.differentiable (by norm_num)) hΨΦ).continuous.smul
      (ContinuousLinearMap.adjoint.continuous.comp
        ((hΨ.fderiv_right (m := 1) (by norm_num)).continuous.comp hΦ.continuous))
  have hνO : Integrable ν (μ.restrict O) := by
    have hsub : μ.restrict O = (μ.restrict Ω).restrict O := by
      rw [Measure.restrict_restrict hO.measurableSet, inter_eq_left.mpr hOΩ]
    rw [hsub]
    exact hν.restrict
  have hνunitO : ∀ᵐ x ∂μ.restrict O, ‖ν x‖ = 1 := by
    have hsub : μ.restrict O = (μ.restrict Ω).restrict O := by
      rw [Measure.restrict_restrict hO.measurableSet, inter_eq_left.mpr hOΩ]
    rw [hsub]
    exact ae_restrict_of_ae hνunit
  have hW_int_compact {K : Set (Space d)} (hK : IsCompact K) (hKO : K ⊆ O) :
      Integrable W (μ.restrict K) := by
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hA_cont.continuousOn
    have hνK : Integrable ν (μ.restrict K) := by
      have hsub : μ.restrict K = (μ.restrict O).restrict K := by
        rw [Measure.restrict_restrict hK.measurableSet, inter_eq_left.mpr hKO]
      rw [hsub]
      exact hνO.restrict
    have hW_meas : AEStronglyMeasurable W (μ.restrict K) :=
      isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable
        (hA_cont.aestronglyMeasurable.prodMk hνK.aestronglyMeasurable)
    refine (hνK.norm.const_mul (max C 0)).mono' hW_meas ?_
    filter_upwards [ae_restrict_mem hK.measurableSet] with x hxK
    calc
      ‖W x‖ ≤ ‖A_op x‖ * ‖ν x‖ := ContinuousLinearMap.le_opNorm (A_op x) (ν x)
      _ ≤ max C 0 * ‖ν x‖ :=
        mul_le_mul_of_nonneg_right ((hC x hxK).trans (le_max_left C 0)) (norm_nonneg _)
  apply le_antisymm
  · refine iSup_le fun Y ↦ iSup_le fun hY ↦ iSup_le fun hYc ↦
      iSup_le fun hYs ↦ iSup_le fun hYunit ↦ ?_
    have hpair : -(∫ y, (Φ '' E).indicator (fun _ ↦ (1 : ℝ)) y * fieldDivergence b Y y) =
        ∫ x in O, inner ℝ (Y (Φ x)) (W x) ∂μ := by
      simpa only [W, A_op, smul_apply] using
        diffeomorph_divergence_pairing_eq b hO hOΩ hΦ hΨ hΨΦ hΦΨ μ hdist hY hYc hYs
    let K := Ψ '' tsupport Y
    have hK : IsCompact K := hYc.image hΨ.continuous
    have hKO : K ⊆ O := by
      rintro _ ⟨y, hy, rfl⟩
      rcases hYs hy with ⟨x, hxO, rfl⟩
      rwa [hΨΦ]
    have hWK : Integrable W (μ.restrict K) := hW_int_compact hK hKO
    have hsupp_in_K : (∫ x in O, inner ℝ (Y (Φ x)) (W x) ∂μ) =
        ∫ x in K, inner ℝ (Y (Φ x)) (W x) ∂μ := by
      have h1 : (∫ x in O, inner ℝ (Y (Φ x)) (W x) ∂μ) =
          ∫ x in K, inner ℝ (Y (Φ x)) (W x) ∂(μ.restrict O) := by
        symm
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro x hxK
        have hy : Φ x ∉ tsupport Y := fun hmem ↦ hxK ⟨Φ x, hmem, hΨΦ x⟩
        simp [image_eq_zero_of_notMem_tsupport hy]
      rw [h1, Measure.restrict_restrict hK.measurableSet, inter_eq_left.mpr hKO]
    have hnorm_le : ‖∫ x in K, inner ℝ (Y (Φ x)) (W x) ∂μ‖ ≤ ∫ x in K, ‖W x‖ ∂μ := by
      apply norm_integral_le_of_norm_le hWK.norm
      exact Eventually.of_forall fun x ↦
        (norm_inner_le_norm _ _).trans (by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right (hYunit (Φ x)) (norm_nonneg _))
    rw [← norm_neg (∫ x, (Φ '' E).indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b Y x),
      hpair, hsupp_in_K]
    calc
      ENNReal.ofReal ‖∫ x in K, inner ℝ (Y (Φ x)) (W x) ∂μ‖
        ≤ ENNReal.ofReal (∫ x in K, ‖W x‖ ∂μ) := ENNReal.ofReal_le_ofReal hnorm_le
      _ = ∫⁻ x in K, ‖W x‖ₑ ∂μ := ofReal_integral_norm_eq_lintegral_enorm hWK
      _ ≤ ∫⁻ x in O, ‖W x‖ₑ ∂μ := lintegral_mono_set hKO
  · by_cases hPΦ : variationalPerimeter b (Φ '' E) (Φ '' O) = ⊤
    · simp [hPΦ]
    let U : ℕ → Set (Space d) := fun n ↦ O ∩ ball 0 ((n : ℝ) + 1)
    have hU_mono : Monotone U := fun n k hnk ↦ inter_subset_inter_right O
      (ball_subset_ball (add_le_add (Nat.cast_le.mpr hnk) le_rfl))
    have hU_union : (⋃ n, U n) = O := by
      ext x
      simp only [U, mem_iUnion, mem_inter_iff]
      refine ⟨fun ⟨_, hxO, _⟩ ↦ hxO, fun hxO ↦ ?_⟩
      obtain ⟨n, hn⟩ := exists_nat_gt ‖x‖
      refine ⟨n, hxO, ?_⟩
      rw [mem_ball, dist_zero_right]
      linarith
    conv_lhs => rw [← hU_union, setLIntegral_iUnion_of_directed _ hU_mono.directed_le]
    refine iSup_le fun n ↦ ?_
    have hUn_open : IsOpen (U n) := hO.inter isOpen_ball
    have hUn_sub_O : U n ⊆ O := inter_subset_left
    have hWU : Integrable W (μ.restrict (U n)) := by
      obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Space d) ((n : ℝ) + 1))
        |>.exists_bound_of_continuousOn hA_cont.continuousOn
      have hνUn : Integrable ν (μ.restrict (U n)) := by
        have hsub : μ.restrict (U n) = (μ.restrict O).restrict (U n) := by
          rw [Measure.restrict_restrict hUn_open.measurableSet, inter_eq_left.mpr hUn_sub_O]
        rw [hsub]
        exact hνO.restrict
      have hW_meas : AEStronglyMeasurable W (μ.restrict (U n)) :=
        isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable
          (hA_cont.aestronglyMeasurable.prodMk hνUn.aestronglyMeasurable)
      refine (hνUn.norm.const_mul (max C 0)).mono' hW_meas ?_
      filter_upwards [ae_restrict_mem hUn_open.measurableSet] with x hxU
      have hx_cb : x ∈ closedBall (0 : Space d) ((n : ℝ) + 1) :=
        ball_subset_closedBall hxU.2
      calc
        ‖W x‖ ≤ ‖A_op x‖ * ‖ν x‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ max C 0 * ‖ν x‖ :=
          mul_le_mul_of_nonneg_right ((hC x hx_cb).trans (le_max_left C 0)) (norm_nonneg _)
    let lam : Measure (Space d) := (μ.restrict (U n)).withDensity (fun x ↦ ‖W x‖ₑ)
    let : IsFiniteMeasure lam := isFiniteMeasure_withDensity hWU.2.ne
    let νW : Space d → Space d := fun x ↦ (‖W x‖)⁻¹ • W x
    have hW_ne_zero : ∀ᵐ x ∂μ.restrict (U n), W x ≠ 0 := by
      have hsub : μ.restrict (U n) = (μ.restrict O).restrict (U n) := by
        rw [Measure.restrict_restrict hUn_open.measurableSet, inter_eq_left.mpr hUn_sub_O]
      rw [hsub]
      filter_upwards [ae_restrict_of_ae hνunitO] with x hx_unit hW0
      have hcomp : (fderiv ℝ Ψ (Φ x)).comp (fderiv ℝ Φ x) =
          ContinuousLinearMap.id ℝ (Space d) := by
        have hd := (((hΨ.differentiable (by norm_num)) (Φ x)).hasFDerivAt.comp x
          ((hΦ.differentiable (by norm_num)) x).hasFDerivAt).fderiv
        have hid : fderiv ℝ (Ψ ∘ Φ) x = ContinuousLinearMap.id ℝ (Space d) := by
          rw [show Ψ ∘ Φ = id from funext hΨΦ]
          exact (hasFDerivAt_id x).fderiv
        exact hd.symm.trans hid
      have hadj : ((fderiv ℝ Φ x).adjoint) (((fderiv ℝ Ψ (Φ x)).adjoint) (ν x)) = ν x := by
        have hc := congrArg ContinuousLinearMap.adjoint hcomp
        rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_id] at hc
        exact congrArg (fun L : Space d →L[ℝ] Space d ↦ L (ν x)) hc
      have h0 : |LinearMap.det (fderiv ℝ Φ x).toLinearMap| • ν x = 0 := by
        have h1 := congrArg ((fderiv ℝ Φ x).adjoint) hW0
        simpa only [W, A_op, smul_apply, map_smul, hadj, map_zero] using h1
      have hdet_ne := det_fderiv_diffeomorph_ne_zero (hΦ.differentiable (by norm_num))
        (hΨ.differentiable (by norm_num)) hΨΦ x
      have hnorm0 := congrArg norm h0
      simp only [norm_smul, Real.norm_eq_abs, abs_abs, hx_unit, mul_one, norm_zero] at hnorm0
      exact hdet_ne (abs_eq_zero.mp hnorm0)
    have hνW_unit_U : ∀ᵐ x ∂μ.restrict (U n), ‖νW x‖ = 1 := by
      filter_upwards [hW_ne_zero] with x hx
      have hn_pos : 0 < ‖W x‖ := norm_pos_iff.mpr hx
      simp [νW, norm_smul, inv_mul_cancel₀ hn_pos.ne']
    have hac : lam ≪ μ.restrict (U n) := withDensity_absolutelyContinuous _ _
    have hνW_unit : ∀ᵐ x ∂lam, ‖νW x‖ = 1 := hac hνW_unit_U
    have hW_meas_lam : AEStronglyMeasurable W lam := hWU.aestronglyMeasurable.mono_ac hac
    have hνW_int : Integrable νW lam := by
      refine Integrable.of_bound
        (hW_meas_lam.norm.aemeasurable.inv.aestronglyMeasurable.smul hW_meas_lam) 1
        (Eventually.of_forall fun x ↦ ?_)
      by_cases hx : W x = 0
      · simp [νW, hx]
      · have hn_pos : 0 < ‖W x‖ := norm_pos_iff.mpr hx
        simp [νW, norm_smul, inv_mul_cancel₀ hn_pos.ne']
    have hlam_apply : lam (U n) = ∫⁻ x in U n,
        ‖|LinearMap.det (fderiv ℝ Φ x).toLinearMap| •
          ((fderiv ℝ Ψ (Φ x)).adjoint (ν x))‖ₑ ∂μ := by
      simp [lam, W, A_op, withDensity_apply _ hUn_open.measurableSet,
        Measure.restrict_restrict hUn_open.measurableSet]
    rw [← hlam_apply, ← ENNReal.ofReal_toReal hPΦ]
    apply measure_open_le_of_unit_polar_tests hνW_int hνW_unit hUn_open
    intro G hG hGc hGs hGu
    have hlam_int : (∫ x, inner ℝ (G x) (νW x) ∂lam) =
        ∫ x in U n, inner ℝ (G x) (W x) ∂μ := by
      rw [integral_withDensity_eq_integral_toReal_smul₀ hWU.aestronglyMeasurable.enorm
        (Eventually.of_forall fun _ ↦ enorm_lt_top)]
      refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
      have hsmul : ‖W x‖ • νW x = W x := by
        by_cases hx : W x = 0
        · simp [νW, hx]
        · simp [νW, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx)]
      simp only [toReal_enorm, smul_eq_mul, ← real_inner_smul_right, hsmul]
    rw [hlam_int]
    let Y : Space d → Space d := fun y ↦ G (Ψ y)
    have hY_cont : Continuous Y := hG.comp hΨ.continuous
    have hY_unit : ∀ y, ‖Y y‖ ≤ 1 := fun y ↦ hGu (Ψ y)
    have hY_supp_G : tsupport Y ⊆ Φ '' tsupport G := by
      apply closure_minimal _ (hGc.image hΦ.continuous).isClosed
      intro y hy
      exact ⟨Ψ y, subset_tsupport G hy, hΦΨ y⟩
    have hYc : HasCompactSupport Y :=
      (hGc.image hΦ.continuous).of_isClosed_subset (isClosed_tsupport Y) hY_supp_G
    have hY_supp_U : tsupport Y ⊆ Φ '' U n := hY_supp_G.trans (image_mono hGs)
    obtain ⟨Yj, hYj, hYju, hYjs, hYjt⟩ := exists_contDiff_unit_field_approx hY_cont hY_unit
    have hdom : Tendsto (fun j ↦ ∫ x in U n, inner ℝ (Yj j (Φ x)) (W x) ∂μ)
        atTop (𝓝 (∫ x in U n, inner ℝ (G x) (W x) ∂μ)) := by
      apply tendsto_integral_of_dominated_convergence (fun x ↦ ‖W x‖)
      · intro j
        exact (((hYj j).continuous.comp hΦ.continuous).aestronglyMeasurable.inner
          hWU.aestronglyMeasurable)
      · exact hWU.norm
      · intro j
        exact Eventually.of_forall fun x ↦
          (norm_inner_le_norm _ _).trans (by
            simpa only [one_mul] using mul_le_mul_of_nonneg_right (hYju j (Φ x)) (norm_nonneg _))
      · refine Eventually.of_forall fun x ↦ ?_
        have ht : Tendsto (fun j ↦ Yj j (Φ x)) atTop (𝓝 (G x)) := by
          simpa only [Y, hΨΦ x] using hYjt (Φ x)
        exact ht.inner tendsto_const_nhds
    apply le_of_tendsto hdom.norm
    refine Eventually.of_forall fun j ↦ ?_
    have hYjc : HasCompactSupport (Yj j) :=
      hYc.of_isClosed_subset (isClosed_tsupport _) (hYjs j)
    have hYjU : tsupport (Yj j) ⊆ Φ '' U n := (hYjs j).trans hY_supp_U
    have hYjO : tsupport (Yj j) ⊆ Φ '' O := hYjU.trans (image_mono hUn_sub_O)
    have hpair : -(∫ y, (Φ '' E).indicator (fun _ ↦ (1 : ℝ)) y * fieldDivergence b (Yj j) y) =
        ∫ x in O, inner ℝ (Yj j (Φ x)) (W x) ∂μ := by
      simpa only [W, A_op, smul_apply] using
        diffeomorph_divergence_pairing_eq b hO hOΩ hΦ hΨ hΨΦ hΦΨ μ hdist (hYj j) hYjc hYjO
    have hrestrict_U : (∫ x in O, inner ℝ (Yj j (Φ x)) (W x) ∂μ) =
        ∫ x in U n, inner ℝ (Yj j (Φ x)) (W x) ∂μ := by
      have h1 : (∫ x in O, inner ℝ (Yj j (Φ x)) (W x) ∂μ) =
          ∫ x in U n, inner ℝ (Yj j (Φ x)) (W x) ∂(μ.restrict O) := by
        symm
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro x hxU
        have hy : Φ x ∉ tsupport (Yj j) := by
          intro hmem
          rcases hYjU hmem with ⟨z, hzU, hzeq⟩
          have hzx : z = x := by
            have := congrArg Ψ hzeq
            rwa [hΨΦ, hΨΦ] at this
          exact hxU (hzx ▸ hzU)
        simp [image_eq_zero_of_notMem_tsupport hy]
      rw [h1, Measure.restrict_restrict hUn_open.measurableSet, inter_eq_left.mpr hUn_sub_O]
    rw [← hrestrict_U, ← hpair, norm_neg]
    apply (ENNReal.ofReal_le_iff_le_toReal hPΦ).mp
    unfold variationalPerimeter
    exact le_iSup_of_le (Yj j) (le_iSup_of_le (hYj j) (le_iSup_of_le hYjc
      (le_iSup_of_le hYjO (le_iSup_of_le (hYju j) le_rfl))))

/-- Exact Bochner-integral diffeomorphism transformation formula for variational perimeter (BV9.1)
whenever the transformed polar density is integrable on `O`. -/
theorem variationalPerimeter_image_diffeomorph {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {E Ω O : Set (Space d)}
    (hO : IsOpen O) (hOΩ : O ⊆ Ω)
    {Φ Ψ : Space d → Space d}
    (hΦ : ContDiff ℝ 2 Φ) (hΨ : ContDiff ℝ 2 Ψ)
    (hΨΦ : ∀ x, Ψ (Φ x) = x) (hΦΨ : ∀ y, Φ (Ψ y) = y)
    (μ : Measure (Space d)) {ν : Space d → Space d}
    (hν : Integrable ν (μ.restrict Ω))
    (hνunit : ∀ᵐ x ∂μ.restrict Ω, ‖ν x‖ = 1)
    (hdist : ∀ F : C_c(Space d, Space d), ContDiff ℝ 1 (F : Space d → Space d) →
      tsupport F ⊆ Ω →
      -(∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F x) =
        ∫ x, inner ℝ (F x) (ν x) ∂μ.restrict Ω)
    (hW : IntegrableOn (fun x ↦ |LinearMap.det (fderiv ℝ Φ x).toLinearMap| •
      ((fderiv ℝ Ψ (Φ x)).adjoint (ν x))) O μ) :
    variationalPerimeter b (Φ '' E) (Φ '' O) =
      ENNReal.ofReal (∫ x in O, ‖|LinearMap.det (fderiv ℝ Φ x).toLinearMap| •
        ((fderiv ℝ Ψ (Φ x)).adjoint (ν x))‖ ∂μ) := by
  rw [variationalPerimeter_image_diffeomorph_lintegral b hO hOΩ hΦ hΨ hΨΦ hΦΨ μ hν hνunit hdist,
    ← ofReal_integral_norm_eq_lintegral_enorm hW]

/-- Exact diffeomorphism transformation formula for any `C²` diffeomorphism equal to the identity
outside a compact set `K` (automatically discharging integrability on `O`). -/
theorem variationalPerimeter_image_diffeomorph_of_eq_id_compl {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {E Ω O K : Set (Space d)}
    (hO : IsOpen O) (hOΩ : O ⊆ Ω) (hK : IsCompact K)
    {Φ Ψ : Space d → Space d}
    (hΦ : ContDiff ℝ 2 Φ) (hΨ : ContDiff ℝ 2 Ψ)
    (hΨΦ : ∀ x, Ψ (Φ x) = x) (hΦΨ : ∀ y, Φ (Ψ y) = y)
    (hΦid : ∀ x, x ∉ K → Φ x = x)
    (μ : Measure (Space d)) {ν : Space d → Space d}
    (hν : Integrable ν (μ.restrict Ω))
    (hνunit : ∀ᵐ x ∂μ.restrict Ω, ‖ν x‖ = 1)
    (hdist : ∀ F : C_c(Space d, Space d), ContDiff ℝ 1 (F : Space d → Space d) →
      tsupport F ⊆ Ω →
      -(∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F x) =
        ∫ x, inner ℝ (F x) (ν x) ∂μ.restrict Ω) :
    variationalPerimeter b (Φ '' E) (Φ '' O) =
      ENNReal.ofReal (∫ x in O, ‖|LinearMap.det (fderiv ℝ Φ x).toLinearMap| •
        ((fderiv ℝ Ψ (Φ x)).adjoint (ν x))‖ ∂μ) := by
  apply variationalPerimeter_image_diffeomorph b hO hOΩ hΦ hΨ hΨΦ hΦΨ μ hν hνunit hdist
  let A_op : Space d → (Space d →L[ℝ] Space d) :=
    fun x ↦ |LinearMap.det (fderiv ℝ Φ x).toLinearMap| • (fderiv ℝ Ψ (Φ x)).adjoint
  have hA_cont : Continuous A_op :=
    (contDiff_abs_det_fderiv hΦ (hΨ.differentiable (by norm_num)) hΨΦ).continuous.smul
      (ContinuousLinearMap.adjoint.continuous.comp
        ((hΨ.fderiv_right (m := 1) (by norm_num)).continuous.comp hΦ.continuous))
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hA_cont.continuousOn
  have hΨid : ∀ y, y ∉ K → Ψ y = y := by
    intro y hy
    have h1 := hΦid y hy
    simpa [h1] using hΨΦ y
  have hA_bound (x : Space d) : ‖A_op x‖ ≤ max C 1 := by
    by_cases hxK : x ∈ K
    · exact (hC x hxK).trans (le_max_left C 1)
    · have hopen : Kᶜ ∈ 𝓝 x := hK.isClosed.isOpen_compl.mem_nhds hxK
      have hΦ_eq : Φ =ᶠ[𝓝 x] id := Filter.eventually_of_mem hopen fun z hz ↦ hΦid z hz
      have hΨ_eq : Ψ =ᶠ[𝓝 (Φ x)] id := by
        rw [hΦid x hxK]
        exact Filter.eventually_of_mem hopen fun z hz ↦ hΨid z hz
      have hdΦ : fderiv ℝ Φ x = ContinuousLinearMap.id ℝ (Space d) := by
        rw [hΦ_eq.fderiv_eq]
        exact (hasFDerivAt_id x).fderiv
      have hdΨ : fderiv ℝ Ψ (Φ x) = ContinuousLinearMap.id ℝ (Space d) := by
        rw [hΨ_eq.fderiv_eq]
        exact (hasFDerivAt_id (Φ x)).fderiv
      have hA_id : A_op x = ContinuousLinearMap.id ℝ (Space d) := by
        simp [A_op, hdΦ, hdΨ, ContinuousLinearMap.adjoint_id]
      rw [hA_id]
      exact ContinuousLinearMap.norm_id_le.trans (le_max_right C 1)
  have hνO : Integrable ν (μ.restrict O) := by
    have hsub : μ.restrict O = (μ.restrict Ω).restrict O := by
      rw [Measure.restrict_restrict hO.measurableSet, inter_eq_left.mpr hOΩ]
    rw [hsub]
    exact hν.restrict
  have hW_meas : AEStronglyMeasurable (fun x ↦ A_op x (ν x)) (μ.restrict O) :=
    isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable
      (hA_cont.aestronglyMeasurable.prodMk hνO.aestronglyMeasurable)
  refine (hνO.norm.const_mul (max C 1)).mono' hW_meas (Eventually.of_forall fun x ↦ ?_)
  calc
    ‖A_op x (ν x)‖ ≤ ‖A_op x‖ * ‖ν x‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ max C 1 * ‖ν x‖ :=
      mul_le_mul_of_nonneg_right (hA_bound x) (norm_nonneg _)

/-! ### Affine dilation and translation corollaries -/

/-- Upper bound on variational perimeter under `x ↦ x₀ + r • x` (`0 < r`). -/
private theorem variationalPerimeter_add_smul_le {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) (E O : Set (Space d))
    (x₀ : Space d) {r : ℝ} (hr : 0 < r) :
    variationalPerimeter b ((fun x ↦ x₀ + r • x) '' E) ((fun x ↦ x₀ + r • x) '' O) ≤
      ENNReal.ofReal (r ^ (d - 1)) * variationalPerimeter b E O := by
  by_cases hd : d = 0
  · subst hd
    unfold variationalPerimeter
    refine iSup_le fun F ↦ iSup_le fun _ ↦ iSup_le fun _ ↦ iSup_le fun _ ↦ iSup_le fun _ ↦ ?_
    simp [fieldDivergence]
  have hd_pos : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hd
  let T : Space d → Space d := fun x ↦ x₀ + r • x
  let S : Space d → Space d := fun y ↦ r⁻¹ • (y - x₀)
  have hST : ∀ x, S (T x) = x := fun x ↦ by simp [T, S, smul_smul, inv_mul_cancel₀ hr.ne']
  have hTS : ∀ y, T (S y) = y := fun y ↦ by simp [T, S, smul_smul, mul_inv_cancel₀ hr.ne']
  let eT : Space d ≃ₜ Space d :=
    { toFun := T
      invFun := S
      left_inv := hST
      right_inv := hTS
      continuous_toFun := continuous_const.add (continuous_id.const_smul r)
      continuous_invFun := (continuous_id.sub continuous_const).const_smul r⁻¹ }
  refine iSup_le fun Y ↦ iSup_le fun hY ↦ iSup_le fun hYc ↦
    iSup_le fun hYs ↦ iSup_le fun hYunit ↦ ?_
  let F : Space d → Space d := fun x ↦ Y (T x)
  have hT_diff : ContDiff ℝ 1 T := contDiff_const.add (contDiff_id.const_smul r)
  have hF : ContDiff ℝ 1 F := hY.comp hT_diff
  have hFc : HasCompactSupport F := hYc.comp_homeomorph eT
  have hFs : tsupport F ⊆ O := by
    refine (tsupport_comp_subset_preimage Y eT.continuous).trans ?_
    intro x hx
    rcases hYs hx with ⟨z, hzO, hzeq⟩
    change T z = T x at hzeq
    have hxz : z = x := by
      have := congrArg S hzeq
      rwa [hST, hST] at this
    exact hxz ▸ hzO
  have hFunit : ∀ x, ‖F x‖ ≤ 1 := fun x ↦ hYunit (T x)
  have hdT_at (x : Space d) : HasFDerivAt T (r • ContinuousLinearMap.id ℝ (Space d)) x :=
    ((hasFDerivAt_id x).const_smul r).const_add x₀
  have hdiv (x : Space d) : fieldDivergence b Y (T x) = r⁻¹ * fieldDivergence b F x := by
    have hdF : fderiv ℝ F x = r • fderiv ℝ Y (T x) := by
      have hc := ((hY.differentiable one_ne_zero (T x)).hasFDerivAt.comp x (hdT_at x)).fderiv
      change fderiv ℝ (Y ∘ T) x = _
      rw [hc]
      exact ContinuousLinearMap.ext fun v ↦ by simp
    have hdivF : fieldDivergence b F x = r * fieldDivergence b Y (T x) := by
      simp only [fieldDivergence, hdF, smul_apply, real_inner_smul_right, ← Finset.mul_sum]
    rw [hdivF, inv_mul_cancel_left₀ hr.ne']
  have hcov : (∫ y, (T '' E).indicator (fun _ ↦ (1 : ℝ)) y * fieldDivergence b Y y) =
      r ^ (d - 1) * ∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F x := by
    have hinj : Set.InjOn T Set.univ := fun _ _ _ _ h ↦ eT.injective h
    have himg : T '' Set.univ = Set.univ := by
      rw [image_univ]
      exact eT.surjective.range_eq
    have hfderiv_within : ∀ x ∈ (Set.univ : Set (Space d)),
        HasFDerivWithinAt T (r • ContinuousLinearMap.id ℝ (Space d)) Set.univ x :=
      fun x _ ↦ hasFDerivWithinAt_univ.mpr (hdT_at x)
    have h := MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul (μ := volume)
      MeasurableSet.univ hfderiv_within hinj
      (fun y ↦ (T '' E).indicator (fun _ ↦ (1 : ℝ)) y * fieldDivergence b Y y)
    rw [himg, Measure.restrict_univ] at h
    have hdet : |((r • ContinuousLinearMap.id ℝ (Space d)).det)| = r ^ d := by
      have hdet_val : LinearMap.det (r • ContinuousLinearMap.id ℝ (Space d)).toLinearMap =
          r ^ d := by
        rw [clm_det_eq_sum_perm b]
        have hterm (σ : Equiv.Perm (Fin d)) :
            (Equiv.Perm.sign σ : ℝ) *
              (∏ i : Fin d, inner ℝ (b (σ i)) ((r • ContinuousLinearMap.id ℝ (Space d)) (b i))) =
              if σ = 1 then r ^ d else 0 := by
          by_cases hσ : σ = 1
          · subst hσ
            simp [real_inner_smul_right, b.orthonormal.1]
          · simp only [hσ, ↓reduceIte]
            obtain ⟨i, hi⟩ : ∃ i : Fin d, σ i ≠ i := by
              by_contra hall
              push Not at hall
              exact hσ (Equiv.ext hall)
            have h0 : inner ℝ (b (σ i)) ((r • ContinuousLinearMap.id ℝ (Space d)) (b i)) = 0 := by
              simp [real_inner_smul_right, b.orthonormal.2 hi]
            rw [Finset.prod_eq_zero (Finset.mem_univ i) h0, mul_zero]
        simp_rw [hterm]
        simp
      change |LinearMap.det (r • ContinuousLinearMap.id ℝ (Space d)).toLinearMap| = r ^ d
      rw [hdet_val, abs_of_pos (pow_pos hr d)]
    have hrpow : r ^ d * r⁻¹ = r ^ (d - 1) := by
      have hd_eq : d = d - 1 + 1 := (Nat.sub_add_cancel hd_pos).symm
      conv_lhs => rw [hd_eq, pow_succ]
      exact mul_inv_cancel_right₀ hr.ne' (r ^ (d - 1))
    rw [h, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    dsimp only
    have hind : (T '' E).indicator (fun _ ↦ (1 : ℝ)) (T x) =
        E.indicator (fun _ ↦ (1 : ℝ)) x := by
      have hmem : T x ∈ T '' E ↔ x ∈ E := eT.injective.mem_set_image
      by_cases hxE : x ∈ E <;> simp [hmem, hxE]
    rw [hdet, hind, hdiv x, smul_eq_mul]
    calc
      r ^ d * (E.indicator (fun _ ↦ (1 : ℝ)) x * (r⁻¹ * fieldDivergence b F x))
        = (r ^ d * r⁻¹) * (E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F x) := by ring
      _ = r ^ (d - 1) * (E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F x) := by
        rw [hrpow]
  rw [hcov, norm_mul, Real.norm_of_nonneg (pow_nonneg hr.le _),
    ENNReal.ofReal_mul (pow_nonneg hr.le _)]
  gcongr
  unfold variationalPerimeter
  exact le_iSup_of_le F (le_iSup_of_le hF (le_iSup_of_le hFc
    (le_iSup_of_le hFs (le_iSup_of_le hFunit le_rfl))))

/-- Exact scaling and translation invariance of variational perimeter under `x ↦ x₀ + r • x`
for `0 < r`. -/
theorem variationalPerimeter_add_smul {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) (E O : Set (Space d))
    (x₀ : Space d) {r : ℝ} (hr : 0 < r) :
    variationalPerimeter b ((fun x ↦ x₀ + r • x) '' E) ((fun x ↦ x₀ + r • x) '' O) =
      ENNReal.ofReal (r ^ (d - 1)) * variationalPerimeter b E O := by
  apply le_antisymm (variationalPerimeter_add_smul_le b E O x₀ hr)
  let T : Space d → Space d := fun x ↦ x₀ + r • x
  let S : Space d → Space d := fun y ↦ -(r⁻¹ • x₀) + r⁻¹ • y
  have hSTE : S '' (T '' E) = E := by
    ext x
    simp only [T, S, mem_image]
    constructor
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      have hzx : -(r⁻¹ • x₀) + r⁻¹ • (x₀ + r • z) = z := by
        rw [smul_add, smul_smul, inv_mul_cancel₀ hr.ne', one_smul, neg_add_cancel_left]
      rwa [hzx]
    · intro hx
      refine ⟨T x, ⟨x, hx, rfl⟩, ?_⟩
      simp [T, smul_add, smul_smul, inv_mul_cancel₀ hr.ne']
  have hSTO : S '' (T '' O) = O := by
    ext x
    simp only [T, S, mem_image]
    constructor
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      have hzx : -(r⁻¹ • x₀) + r⁻¹ • (x₀ + r • z) = z := by
        rw [smul_add, smul_smul, inv_mul_cancel₀ hr.ne', one_smul, neg_add_cancel_left]
      rwa [hzx]
    · intro hx
      refine ⟨T x, ⟨x, hx, rfl⟩, ?_⟩
      simp [T, smul_add, smul_smul, inv_mul_cancel₀ hr.ne']
  have hinv := variationalPerimeter_add_smul_le b (T '' E) (T '' O) (-(r⁻¹ • x₀))
    (inv_pos.mpr hr)
  rw [hSTE, hSTO] at hinv
  calc
    ENNReal.ofReal (r ^ (d - 1)) * variationalPerimeter b E O
      ≤ ENNReal.ofReal (r ^ (d - 1)) *
          (ENNReal.ofReal ((r⁻¹) ^ (d - 1)) * variationalPerimeter b (T '' E) (T '' O)) := by
        gcongr
    _ = (ENNReal.ofReal (r ^ (d - 1)) * ENNReal.ofReal ((r⁻¹) ^ (d - 1))) *
          variationalPerimeter b (T '' E) (T '' O) := (mul_assoc _ _ _).symm
    _ = variationalPerimeter b (T '' E) (T '' O) := by
        rw [← ENNReal.ofReal_mul (pow_nonneg hr.le _), ← mul_pow,
          mul_inv_cancel₀ hr.ne', one_pow, ENNReal.ofReal_one, one_mul]

/-- Positive homogeneous dilation formula for variational perimeter (`0 < r`). -/
theorem variationalPerimeter_smul {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) (E O : Set (Space d))
    {r : ℝ} (hr : 0 < r) :
    variationalPerimeter b ((fun x ↦ r • x) '' E) ((fun x ↦ r • x) '' O) =
      ENNReal.ofReal (r ^ (d - 1)) * variationalPerimeter b E O := by
  simpa only [zero_add] using variationalPerimeter_add_smul b E O 0 hr

/-- Translation invariance of variational perimeter. -/
theorem variationalPerimeter_add {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) (E O : Set (Space d)) (x₀ : Space d) :
    variationalPerimeter b ((fun x ↦ x₀ + x) '' E) ((fun x ↦ x₀ + x) '' O) =
      variationalPerimeter b E O := by
  simpa only [one_smul, one_pow, ENNReal.ofReal_one, one_mul] using
    variationalPerimeter_add_smul b E O x₀ zero_lt_one

/-! ### Section 3: Perturbation diffeomorphism and First Variation Stationarity (BV9.2) -/

/-- For a compactly supported `C²` vector field `X`, `Φ_t x = x + t • X x` is a global
orientation-preserving `C²` diffeomorphism equal to the identity outside `tsupport X` for all
sufficiently small `|t|`. -/
theorem exists_perturbation_diffeomorph {d : ℕ} {X : Space d → Space d}
    (hX : ContDiff ℝ 2 X) (hXc : HasCompactSupport X) :
    ∃ (δ : ℝ) (Ψ : ℝ → Space d → Space d), 0 < δ ∧
      ∀ t : ℝ, |t| < δ →
        ContDiff ℝ 2 (fun x ↦ x + t • X x) ∧
        ContDiff ℝ 2 (Ψ t) ∧
        (∀ x, Ψ t (x + t • X x) = x) ∧
        (∀ y, (Ψ t y + t • X (Ψ t y)) = y) ∧
        (∀ x, x ∉ tsupport X → x + t • X x = x) ∧
        (∀ y, y ∉ tsupport X → Ψ t y = y) ∧
        (∀ x, 0 < LinearMap.det (fderiv ℝ (fun z ↦ z + t • X z) x).toLinearMap) := by
  have hX1 : ContDiff ℝ 1 X := hX.of_le (by norm_num)
  obtain ⟨M₀, hM₀⟩ := hXc.exists_bound_of_continuousOn
    (hX1.continuous_fderiv one_ne_zero).continuousOn
  let M : ℝ := max M₀ 0
  have hM_nonneg : 0 ≤ M := le_max_right M₀ 0
  have hM_bound (x : Space d) : ‖fderiv ℝ X x‖ ≤ M := by
    by_cases hx : x ∈ tsupport X
    · exact (hM₀ x hx).trans (le_max_left M₀ 0)
    · rw [fderiv_of_notMem_tsupport ℝ hx, norm_zero]
      exact hM_nonneg
  have hdet_cont : ContinuousAt
      (fun L : Space d →L[ℝ] Space d ↦ LinearMap.det L.toLinearMap) 1 :=
    (contDiff_clm_det (n := 1)).continuous.continuousAt
  have hdet_one : LinearMap.det (1 : Space d →L[ℝ] Space d).toLinearMap = 1 := LinearMap.det_id
  obtain ⟨r₀, hr₀_pos, hr₀_det⟩ := Metric.continuousAt_iff.mp hdet_cont (1 / 2) (by positivity)
  let r₁ : ℝ := min r₀ (1 / 2)
  have hr₁_pos : 0 < r₁ := lt_min hr₀_pos (by positivity)
  let δ : ℝ := r₁ / (M + 1)
  have hδ_pos : 0 < δ := div_pos hr₁_pos (by linarith)
  have h_norm_lt {t : ℝ} (ht : |t| < δ) (x : Space d) :
      ‖t • fderiv ℝ X x‖ < r₁ := by
    rw [norm_smul, Real.norm_eq_abs]
    calc
      |t| * ‖fderiv ℝ X x‖ ≤ |t| * M :=
        mul_le_mul_of_nonneg_left (hM_bound x) (abs_nonneg t)
      _ ≤ |t| * (M + 1) := by nlinarith [abs_nonneg t]
      _ < δ * (M + 1) := mul_lt_mul_of_pos_right ht (by linarith)
      _ = r₁ := div_mul_cancel₀ r₁ (by linarith)
  have h_contract : ∀ (t : ℝ) (y : Space d),
      ContractingWith (1 / 2 : ℝ≥0)
        (if |t| < δ then fun x ↦ y - t • X x else fun _ ↦ y) := by
    intro t y
    split_ifs with ht
    · refine ⟨by norm_num, ?_⟩
      apply lipschitzWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
      · exact differentiable_const y |>.sub ((hX1.differentiable one_ne_zero).const_smul t)
      · intro x
        rw [← NNReal.coe_le_coe, coe_nnnorm]
        have hdf : fderiv ℝ (fun z ↦ y - t • X z) x = -(t • fderiv ℝ X x) := by
          have hfn : (fun z ↦ y - t • X z) = (fun _ ↦ y) - t • X := by ext z; rfl
          rw [hfn]
          simpa using ((hasFDerivAt_const (𝕜 := ℝ) y x).sub
            (((hX1.differentiable one_ne_zero x).hasFDerivAt).const_smul t)).fderiv
        rw [hdf, norm_neg]
        exact (h_norm_lt ht x).le.trans ((min_le_right r₀ (1 / 2)).trans_eq (by norm_num))
    · refine ⟨by norm_num, ?_⟩
      exact (LipschitzWith.const y).weaken (by norm_num : (0 : ℝ≥0) ≤ 1 / 2)
  let Ψ : ℝ → Space d → Space d := fun t y ↦
    (h_contract t y).fixedPoint (if |t| < δ then fun x ↦ y - t • X x else fun _ ↦ y)
  refine ⟨δ, Ψ, hδ_pos, fun t ht ↦ ?_⟩
  let Φt : Space d → Space d := fun x ↦ x + t • X x
  have hΦt_smooth : ContDiff ℝ 2 Φt := contDiff_id.add (hX.const_smul t)
  have h_g_eq (y : Space d) :
      (if |t| < δ then fun x ↦ y - t • X x else fun _ ↦ y) = fun x ↦ y - t • X x := by
    simp [ht]
  have hΦΨ (y : Space d) : Ψ t y + t • X (Ψ t y) = y := by
    have hfp : (if |t| < δ then fun x ↦ y - t • X x else fun _ ↦ y) (Ψ t y) = Ψ t y :=
      (h_contract t y).fixedPoint_isFixedPt
    rw [h_g_eq y] at hfp
    dsimp only at hfp
    calc
      Ψ t y + t • X (Ψ t y) = (y - t • X (Ψ t y)) + t • X (Ψ t y) := by rw [hfp]
      _ = y := sub_add_cancel _ _
  have hΨΦ (x : Space d) : Ψ t (x + t • X x) = x := by
    symm
    apply (h_contract t (x + t • X x)).fixedPoint_unique
    rw [h_g_eq]
    change (x + t • X x) - t • X x = x
    exact add_sub_cancel_right x (t • X x)
  have hΦ_compl (x : Space d) (hx : x ∉ tsupport X) : x + t • X x = x := by
    simp [image_eq_zero_of_notMem_tsupport hx]
  have hΨ_compl (y : Space d) (hy : y ∉ tsupport X) : Ψ t y = y := by
    have h := hΨΦ y
    rwa [hΦ_compl y hy] at h
  have hfderiv_Φ (x : Space d) :
      HasFDerivAt Φt ((1 : Space d →L[ℝ] Space d) + t • fderiv ℝ X x) x :=
    (hasFDerivAt_id x).add (((hX1.differentiable one_ne_zero x).hasFDerivAt).const_smul t)
  have hdet_pos (x : Space d) :
      0 < LinearMap.det (fderiv ℝ Φt x).toLinearMap := by
    rw [(hfderiv_Φ x).fderiv]
    have hd : dist ((1 : Space d →L[ℝ] Space d) + t • fderiv ℝ X x) 1 < r₀ := by
      rw [dist_eq_norm, add_sub_cancel_left]
      exact (h_norm_lt ht x).trans_le (min_le_left r₀ (1 / 2))
    have hclose := hr₀_det hd
    rw [hdet_one, Real.dist_eq] at hclose
    linarith [(abs_lt.mp hclose).1]
  have hΨ_smooth : ContDiff ℝ 2 (Ψ t) := by
    rw [contDiff_iff_contDiffAt]
    intro y
    let x := Ψ t y
    have hΦx : Φt x = y := hΦΨ y
    have hnorm_half : ‖-(t • fderiv ℝ X x)‖ < 1 := by
      rw [norm_neg]
      exact (h_norm_lt ht x).trans_le ((min_le_right r₀ (1 / 2)).trans (by norm_num))
    have hu : IsUnit ((1 : Space d →L[ℝ] Space d) + t • fderiv ℝ X x) := by
      simpa [sub_neg_eq_add] using isUnit_one_sub_of_norm_lt_one hnorm_half
    let u := hu.unit
    let f' : Space d ≃L[ℝ] Space d :=
      { toLinearEquiv := LinearEquiv.ofLinearMap u.val.toLinearMap u.inv.toLinearMap
          (congrArg ContinuousLinearMap.toLinearMap u.val_inv)
          (congrArg ContinuousLinearMap.toLinearMap u.inv_val)
        continuous_toFun := u.val.continuous
        continuous_invFun := u.inv.continuous }
    have hf'_coe : (f' : Space d →L[ℝ] Space d) = 1 + t • fderiv ℝ X x := rfl
    have hf'_at : HasFDerivAt Φt (f' : Space d →L[ℝ] Space d) x := by
      rw [hf'_coe]
      exact hfderiv_Φ x
    have hn2 : (2 : WithTop ℕ∞) ≠ 0 := by norm_num
    have hloc_smooth : ContDiffAt ℝ 2 (hΦt_smooth.contDiffAt.localInverse hf'_at hn2) (Φt x) :=
      hΦt_smooth.contDiffAt.to_localInverse hf'_at hn2
    have hloc_eq : Ψ t =ᶠ[𝓝 (Φt x)] hΦt_smooth.contDiffAt.localInverse hf'_at hn2 :=
      (hΦt_smooth.contDiffAt.hasStrictFDerivAt' hf'_at hn2).localInverse_unique
        (Eventually.of_forall hΨΦ)
    rw [← hΦx]
    exact hloc_smooth.congr_of_eventuallyEq hloc_eq
  exact ⟨hΦt_smooth, hΨ_smooth, hΨΦ, hΦΨ, hΦ_compl, hΨ_compl, hdet_pos⟩

private theorem clm_zero_smul {d : ℕ} (A : Space d →L[ℝ] Space d) :
    (0 : ℝ) • A = 0 :=
  ContinuousLinearMap.ext fun _ ↦ zero_smul ℝ _

/-- Differentiating `t ↦ Ring.inverse (I + t A)` at `t = 0` yields `-A`. -/
private theorem hasDerivAt_ringInverse_one_add_smul {d : ℕ} (A : Space d →L[ℝ] Space d) :
    HasDerivAt (fun t : ℝ ↦ Ring.inverse ((1 : Space d →L[ℝ] Space d) + t • A)) (-A) 0 := by
  let g : ℝ → Space d →L[ℝ] Space d := fun t ↦ (1 : Space d →L[ℝ] Space d) + t • A
  have hg0 : g 0 = 1 := by simp [g, clm_zero_smul]
  have hg_cont : Continuous g := continuous_const.add (continuous_id.smul continuous_const)
  have hinv_cont : ContinuousAt Ring.inverse (1 : Space d →L[ℝ] Space d) :=
    (contDiffAt_ringInverse ℝ (n := 1) (1 : (Space d →L[ℝ] Space d)ˣ)).continuousAt
  have hR_cont : ContinuousAt (fun t ↦ Ring.inverse (g t)) 0 :=
    (hg0 ▸ hinv_cont).comp hg_cont.continuousAt
  rw [hasDerivAt_iff_tendsto_slope_zero]
  have hlim : Tendsto (fun t : ℝ ↦ -(A * Ring.inverse (g t))) (𝓝[≠] 0) (𝓝 (-A)) := by
    have ht0 : Tendsto (fun t : ℝ ↦ -(A * Ring.inverse (g t))) (𝓝 0)
        (𝓝 (-(A * Ring.inverse (g 0)))) :=
      ((continuous_const.mul continuous_id).neg.continuousAt.comp hR_cont)
    have hg0_val : -(A * Ring.inverse (g 0)) = -A := by
      rw [hg0, Ring.inverse_one, mul_one]
    rw [hg0_val] at ht0
    exact ht0.mono_left nhdsWithin_le_nhds
  refine hlim.congr' ?_
  have hball : ball (0 : ℝ) ((‖A‖ + 1)⁻¹) ∈ 𝓝[≠] (0 : ℝ) :=
    nhdsWithin_le_nhds (ball_mem_nhds 0 (inv_pos.mpr (by positivity)))
  filter_upwards [hball, self_mem_nhdsWithin] with t ht_ball ht_ne
  have ht0 : t ≠ 0 := ht_ne
  have hnorm_lt : ‖-(t • A)‖ < 1 := by
    rw [norm_neg, norm_smul, Real.norm_eq_abs]
    have ht_lt : |t| < (‖A‖ + 1)⁻¹ := by simpa [mem_ball, Real.dist_eq] using ht_ball
    calc
      |t| * ‖A‖ ≤ |t| * (‖A‖ + 1) := by nlinarith [abs_nonneg t]
      _ < (‖A‖ + 1)⁻¹ * (‖A‖ + 1) := mul_lt_mul_of_pos_right ht_lt (by positivity)
      _ = 1 := inv_mul_cancel₀ (by positivity)
  have hu : IsUnit (g t) := by
    simpa [g, sub_neg_eq_add] using isUnit_one_sub_of_norm_lt_one hnorm_lt
  have hmul : g t * Ring.inverse (g t) = 1 := Ring.mul_inverse_cancel (g t) hu
  have hsmul_mul : (t • A) * Ring.inverse (g t) = t • (A * Ring.inverse (g t)) :=
    ContinuousLinearMap.ext fun _ ↦ by simp
  have hdiff : Ring.inverse (g (0 + t)) - Ring.inverse (g 0) =
      t • (-(A * Ring.inverse (g t))) := by
    rw [zero_add, hg0, Ring.inverse_one]
    dsimp only [g] at hmul
    rw [add_mul, one_mul, hsmul_mul] at hmul
    change Ring.inverse (g t) - 1 = t • (-(A * Ring.inverse (g t)))
    rw [← hmul, sub_add_cancel_left, smul_neg]
  rw [hdiff, inv_smul_smul₀ ht0]

/-- Pointwise first variation derivative of `‖det (I + t A) • ((I + t A)⁻¹)† u‖` at `t = 0`
for any unit vector `u`. -/
private theorem hasDerivAt_norm_cofactor_apply {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d))
    {X : Space d → Space d} (x : Space d) {u : Space d} (hu : ‖u‖ = 1) :
    HasDerivAt
      (fun t : ℝ ↦
        ‖LinearMap.det ((1 : Space d →L[ℝ] Space d) + t • fderiv ℝ X x).toLinearMap •
          ((Ring.inverse ((1 : Space d →L[ℝ] Space d) + t • fderiv ℝ X x)).adjoint u)‖)
      (fieldDivergence b X x - inner ℝ u (fderiv ℝ X x u)) 0 := by
  let A : Space d →L[ℝ] Space d := fderiv ℝ X x
  let d_fn : ℝ → ℝ := fun t ↦ LinearMap.det ((1 : Space d →L[ℝ] Space d) + t • A).toLinearMap
  let g_fn : ℝ → Space d →L[ℝ] Space d := fun t ↦ (1 : Space d →L[ℝ] Space d) + t • A
  let v_fn : ℝ → Space d := fun t ↦ (Ring.inverse (g_fn t)).adjoint u
  let w_fn : ℝ → Space d := fun t ↦ d_fn t • v_fn t
  have hd_deriv : HasDerivAt d_fn (fieldDivergence b X x) 0 := by
    rw [fieldDivergence_eq_trace b X x]
    exact hasDerivAt_det_one_add_smul A
  have hinv_deriv : HasDerivAt (fun t ↦ Ring.inverse (g_fn t)) (-A) 0 :=
    hasDerivAt_ringInverse_one_add_smul A
  let adj_eval : (Space d →L[ℝ] Space d) →L[ℝ] Space d :=
    (ContinuousLinearMap.apply ℝ (Space d) u).comp
      ContinuousLinearMap.adjoint.toLinearIsometry.toContinuousLinearMap
  have hv_deriv : HasDerivAt v_fn (-(A.adjoint u)) 0 := by
    have hc := adj_eval.hasFDerivAt.comp_hasDerivAt 0 hinv_deriv
    have hfun : (adj_eval ∘ fun t ↦ Ring.inverse (g_fn t)) = v_fn := rfl
    have hval : adj_eval (-A) = -(A.adjoint u) := map_neg adj_eval A
    rwa [hfun, hval] at hc
  have hd0 : d_fn 0 = 1 := by
    dsimp only [d_fn]
    simp [clm_zero_smul]
  have hv0 : v_fn 0 = u := by
    dsimp only [v_fn, g_fn]
    simp [clm_zero_smul, Ring.inverse_one, ContinuousLinearMap.adjoint_one]
  have hw0 : w_fn 0 = u := by simp [w_fn, hd0, hv0]
  have hw_deriv : HasDerivAt w_fn (fieldDivergence b X x • u - A.adjoint u) 0 := by
    refine (hd_deriv.smul hv_deriv).congr_deriv ?_
    rw [hd0, hv0, one_smul]
    abel
  have hsq := hw_deriv.norm_sq
  have hw0_sq : ‖w_fn 0‖ ^ 2 ≠ 0 := by rw [hw0, hu]; norm_num
  have hsqrt := hsq.sqrt hw0_sq
  have hfun_eq : (fun t : ℝ ↦ Real.sqrt (‖w_fn t‖ ^ 2)) = fun t ↦ ‖w_fn t‖ := by
    funext t
    exact Real.sqrt_sq (norm_nonneg _)
  rw [hfun_eq] at hsqrt
  refine hsqrt.congr_deriv ?_
  rw [hw0, hu, one_pow, Real.sqrt_one, mul_one, mul_div_cancel_left₀ _ two_ne_zero,
    inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hu, one_pow, mul_one,
    ContinuousLinearMap.adjoint_inner_right, real_inner_comm]

/-- First Variation Stationarity (BV9.2) for `C²` compactly supported vector fields. -/
theorem perimeter_first_variation_eq_zero_of_contDiff_two {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {E Ω : Set (Space d)}
    (hE : MeasurableSet E) (hΩ : IsOpen Ω)
    (hmin : ∀ D, MeasurableSet D →
      (∃ K, IsCompact K ∧ K ⊆ Ω ∧ ∀ᵐ x ∂volume, x ∉ K → (x ∈ E ↔ x ∈ D)) →
      variationalPerimeter b E Ω ≤ variationalPerimeter b D Ω)
    (μ : Measure (Space d)) {ν : Space d → Space d}
    (hν : Integrable ν (μ.restrict Ω))
    (hνunit : ∀ᵐ x ∂μ.restrict Ω, ‖ν x‖ = 1)
    (hdist : ∀ F : C_c(Space d, Space d), ContDiff ℝ 1 (F : Space d → Space d) →
      tsupport F ⊆ Ω →
      -(∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F x) =
        ∫ x, inner ℝ (F x) (ν x) ∂μ.restrict Ω)
    {X : Space d → Space d} (hX : ContDiff ℝ 2 X)
    (hXc : HasCompactSupport X) (hXΩ : tsupport X ⊆ Ω) :
    ∫ x, (fieldDivergence b X x - inner ℝ (ν x) (fderiv ℝ X x (ν x))) ∂(μ.restrict Ω) = 0 := by
  have hμ_fin : IsFiniteMeasure (μ.restrict Ω) := by
    constructor
    have heq : ∫⁻ _, (1 : ℝ≥0∞) ∂(μ.restrict Ω) = ∫⁻ x, ‖ν x‖ₑ ∂(μ.restrict Ω) := by
      apply lintegral_congr_ae
      filter_upwards [hνunit] with x hx
      simp [← ofReal_norm, hx]
    rw [lintegral_const, one_mul] at heq
    exact heq ▸ hν.2
  obtain ⟨δ, Ψ, hδ_pos, hdiff_family⟩ := exists_perturbation_diffeomorph hX hXc
  have hX1 : ContDiff ℝ 1 X := hX.of_le (by norm_num)
  obtain ⟨M₀, hM₀⟩ := hXc.exists_bound_of_continuousOn
    (hX1.continuous_fderiv one_ne_zero).continuousOn
  let M : ℝ := max M₀ 0
  have hM_nonneg : 0 ≤ M := le_max_right M₀ 0
  have hM_bound (x : Space d) : ‖fderiv ℝ X x‖ ≤ M := by
    by_cases hx : x ∈ tsupport X
    · exact (hM₀ x hx).trans (le_max_left M₀ 0)
    · rw [fderiv_of_notMem_tsupport ℝ hx, norm_zero]
      exact hM_nonneg
  let H : (Space d →L[ℝ] Space d) → (Space d →L[ℝ] Space d) := fun T ↦
    LinearMap.det ((1 : Space d →L[ℝ] Space d) + T).toLinearMap •
      (Ring.inverse ((1 : Space d →L[ℝ] Space d) + T)).adjoint
  have hH_smooth : ContDiffOn ℝ 1 H (ball 0 (1 / 2)) := by
    intro T hT
    have hnorm : ‖-T‖ < 1 := by
      rw [norm_neg]
      exact (by simpa [mem_ball, dist_zero_right] using hT : ‖T‖ < 1 / 2).trans (by norm_num)
    have hu : IsUnit ((1 : Space d →L[ℝ] Space d) + T) := by
      simpa [sub_neg_eq_add] using isUnit_one_sub_of_norm_lt_one hnorm
    let uT := hu.unit
    have hdet_at : ContDiffAt ℝ 1
        (fun S : Space d →L[ℝ] Space d ↦
          LinearMap.det ((1 : Space d →L[ℝ] Space d) + S).toLinearMap) T :=
      contDiff_clm_det.contDiffAt.comp T (contDiffAt_const.add contDiffAt_id)
    have hinv_at : ContDiffAt ℝ 1
        (fun S : Space d →L[ℝ] Space d ↦ Ring.inverse ((1 : Space d →L[ℝ] Space d) + S)) T := by
      have hc : ContDiffAt ℝ 1 Ring.inverse ((1 : Space d →L[ℝ] Space d) + T) := by
        simpa [show (uT : Space d →L[ℝ] Space d) = 1 + T from rfl] using
          contDiffAt_ringInverse ℝ uT
      exact hc.comp T (contDiffAt_const.add contDiffAt_id)
    let adjCLM : (Space d →L[ℝ] Space d) →L[ℝ] (Space d →L[ℝ] Space d) :=
      ContinuousLinearMap.adjoint.toLinearIsometry.toContinuousLinearMap
    have hadj_at : ContDiffAt ℝ 1
        (fun S : Space d →L[ℝ] Space d ↦
          (Ring.inverse ((1 : Space d →L[ℝ] Space d) + S)).adjoint) T :=
      adjCLM.contDiff.contDiffAt.comp T hinv_at
    exact (hdet_at.smul hadj_at).contDiffWithinAt
  obtain ⟨K_H, hK_H⟩ := (hH_smooth.mono (closedBall_subset_ball (by norm_num : (1 / 4 : ℝ) < 1 / 2)))
    |>.exists_lipschitzOnWith one_ne_zero (convex_closedBall 0 (1 / 4))
      (isCompact_closedBall 0 (1 / 4))
  let δ₁ : ℝ := min (δ / 2) (1 / (4 * (M + 1)))
  have hδ₁_pos : 0 < δ₁ := lt_min (half_pos hδ_pos) (by positivity)
  have hδ₁_lt_δ : δ₁ < δ := (min_le_left _ _).trans_lt (half_lt_self hδ_pos)
  let F : ℝ → Space d → ℝ := fun t x ↦ ‖H (t • fderiv ℝ X x) (ν x)‖
  let F' : Space d → ℝ := fun x ↦ fieldDivergence b X x - inner ℝ (ν x) (fderiv ℝ X x (ν x))
  have hF0 : F 0 = fun x ↦ ‖ν x‖ := by
    funext x
    dsimp only [F, H]
    simp [clm_zero_smul, Ring.inverse_one, ContinuousLinearMap.adjoint_one]
  have ht_mem_quarter {t : ℝ} (ht : t ∈ closedBall (0 : ℝ) δ₁) (x : Space d) :
      t • fderiv ℝ X x ∈ closedBall (0 : Space d →L[ℝ] Space d) (1 / 4) := by
    rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs]
    have ht_le : |t| ≤ 1 / (4 * (M + 1)) := by
      have h1 : |t| ≤ δ₁ := by simpa [mem_closedBall, Real.dist_eq] using ht
      exact h1.trans (min_le_right _ _)
    calc
      |t| * ‖fderiv ℝ X x‖ ≤ |t| * M :=
        mul_le_mul_of_nonneg_left (hM_bound x) (abs_nonneg t)
      _ ≤ (1 / (4 * (M + 1))) * (M + 1) :=
        mul_le_mul ht_le (by linarith) hM_nonneg (by positivity)
      _ = 1 / 4 := by field_simp
  have hderiv_int : Integrable F' (μ.restrict Ω) ∧
      HasDerivAt (fun t ↦ ∫ x, F t x ∂(μ.restrict Ω))
        (∫ x, F' x ∂(μ.restrict Ω)) 0 := by
    apply hasDerivAt_integral_of_dominated_loc_of_lip (s := closedBall (0 : ℝ) δ₁)
      (bound := fun _ ↦ (K_H : ℝ) * M) (closedBall_mem_nhds 0 hδ₁_pos)
    · filter_upwards [closedBall_mem_nhds (0 : ℝ) hδ₁_pos] with t ht
      have hHt_cont : Continuous (fun x ↦ H (t • fderiv ℝ X x)) :=
        hH_smooth.continuousOn.comp_continuous
          ((hX1.continuous_fderiv one_ne_zero).const_smul t)
          fun x ↦ closedBall_subset_ball (by norm_num : (1 / 4 : ℝ) < 1 / 2) (ht_mem_quarter ht x)
      exact (isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable
        (hHt_cont.aestronglyMeasurable.prodMk hν.aestronglyMeasurable)).norm
    · rw [hF0]
      exact hν.norm
    · have hdiv_cont : Continuous (fieldDivergence b X) :=
        continuous_finsetSum _ fun i _ ↦ continuous_const.inner
          ((hX1.continuous_fderiv one_ne_zero).clm_apply continuous_const)
      have hAX_meas : AEStronglyMeasurable (fun x ↦ fderiv ℝ X x (ν x)) (μ.restrict Ω) :=
        isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable
          ((hX1.continuous_fderiv one_ne_zero).aestronglyMeasurable.prodMk
            hν.aestronglyMeasurable)
      exact hdiv_cont.aestronglyMeasurable.sub (hν.aestronglyMeasurable.inner hAX_meas)
    · filter_upwards [hνunit] with x hx_unit
      refine LipschitzOnWith.of_dist_le_mul fun t₁ ht₁ t₂ ht₂ ↦ ?_
      have hH_lip := hK_H.dist_le_mul _ (ht_mem_quarter ht₁ x) _ (ht_mem_quarter ht₂ x)
      rw [Real.dist_eq]
      calc
        |‖H (t₁ • fderiv ℝ X x) (ν x)‖ - ‖H (t₂ • fderiv ℝ X x) (ν x)‖|
          ≤ ‖(H (t₁ • fderiv ℝ X x) - H (t₂ • fderiv ℝ X x)) (ν x)‖ := by
            simpa only [sub_apply] using
              abs_norm_sub_norm_le (H (t₁ • fderiv ℝ X x) (ν x)) (H (t₂ • fderiv ℝ X x) (ν x))
        _ ≤ ‖H (t₁ • fderiv ℝ X x) - H (t₂ • fderiv ℝ X x)‖ * ‖ν x‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ = dist (H (t₁ • fderiv ℝ X x)) (H (t₂ • fderiv ℝ X x)) := by
            rw [hx_unit, mul_one, dist_eq_norm]
        _ ≤ K_H * dist (t₁ • fderiv ℝ X x) (t₂ • fderiv ℝ X x) := hH_lip
        _ = K_H * (|t₁ - t₂| * ‖fderiv ℝ X x‖) := by
            rw [dist_eq_norm, ← sub_smul t₁ t₂ (fderiv ℝ X x), norm_smul, Real.norm_eq_abs]
        _ ≤ ((K_H : ℝ) * M) * dist t₁ t₂ := by
            rw [Real.dist_eq]
            have hm := mul_le_mul_of_nonneg_left (hM_bound x)
              (mul_nonneg K_H.coe_nonneg (abs_nonneg (t₁ - t₂)))
            linarith
        _ = ↑(Real.nnabs ((K_H : ℝ) * M)) * dist t₁ t₂ := by
            rw [Real.coe_nnabs, abs_of_nonneg (mul_nonneg K_H.coe_nonneg hM_nonneg)]
    · exact integrable_const _
    · filter_upwards [hνunit] with x hx_unit
      exact hasDerivAt_norm_cofactor_apply b x hx_unit
  have hlocal_min : IsLocalMin (fun t ↦ ∫ x, F t x ∂(μ.restrict Ω)) 0 := by
    filter_upwards [ball_mem_nhds (0 : ℝ) hδ₁_pos] with t ht_ball
    have ht_abs : |t| < δ :=
      (by simpa [mem_ball, Real.dist_eq] using ht_ball : |t| < δ₁).trans hδ₁_lt_δ
    obtain ⟨hΦt, hΨt, hΨΦ, hΦΨ, hΦid, hΨid, hdet_pos⟩ := hdiff_family t ht_abs
    let Φt : Space d → Space d := fun x ↦ x + t • X x
    have hΦ_Ω : Φt '' Ω = Ω := by
      ext y
      constructor
      · rintro ⟨x, hxΩ, rfl⟩
        by_contra hyΩ
        have hyX : Φt x ∉ tsupport X := fun hh ↦ hyΩ (hXΩ hh)
        have hfix := hΨid (Φt x) hyX
        rw [hΨΦ x] at hfix
        exact hyΩ (hfix ▸ hxΩ)
      · intro hyΩ
        refine ⟨Ψ t y, ?_, hΦΨ y⟩
        by_contra hxΩ
        have hxX : Ψ t y ∉ tsupport X := fun hh ↦ hxΩ (hXΩ hh)
        have hfix : Ψ t y + t • X (Ψ t y) = Ψ t y := hΦid (Ψ t y) hxX
        rw [hΦΨ y] at hfix
        exact hxΩ (hfix ▸ hyΩ)
    have hDt_eq : Φt '' E = Ψ t ⁻¹' E := by
      ext y
      simp only [mem_image, mem_preimage]
      exact ⟨fun ⟨x, hxE, hxy⟩ ↦ hxy ▸ (hΨΦ x).symm ▸ hxE,
        fun hyE ↦ ⟨Ψ t y, hyE, hΦΨ y⟩⟩
    have hDt_meas : MeasurableSet (Φt '' E) := by
      rw [hDt_eq]
      exact hE.preimage hΨt.continuous.measurable
    have hcomp_t : variationalPerimeter b E Ω ≤ variationalPerimeter b (Φt '' E) Ω := by
      apply hmin (Φt '' E) hDt_meas
      refine ⟨tsupport X, hXc, hXΩ, Eventually.of_forall fun x hxX ↦ ?_⟩
      rw [hDt_eq, mem_preimage, hΨid x hxX]
    have hPV_t : variationalPerimeter b (Φt '' E) Ω =
        ENNReal.ofReal (∫ x, F t x ∂(μ.restrict Ω)) := by
      have hΦt' : ContDiff ℝ 2 Φt := hΦt
      conv_lhs => rw [← hΦ_Ω]
      rw [variationalPerimeter_image_diffeomorph_of_eq_id_compl b hΩ Subset.rfl hXc
        hΦt' hΨt hΨΦ hΦΨ hΦid μ hν hνunit hdist]
      congr 1
      refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
      have hdfΦ : fderiv ℝ Φt x = (1 : Space d →L[ℝ] Space d) + t • fderiv ℝ X x :=
        ((hasFDerivAt_id x).add
          (((hX1.differentiable one_ne_zero x).hasFDerivAt).const_smul t)).fderiv
      have h1 : (fderiv ℝ (Ψ t) (Φt x)).comp (fderiv ℝ Φt x) = 1 := by
        have hd := ((hΨt.differentiable (by norm_num) (Φt x)).hasFDerivAt.comp x
          (hΦt'.differentiable (by norm_num) x).hasFDerivAt).fderiv
        have hid : fderiv ℝ (Ψ t ∘ Φt) x = 1 := by
          rw [show Ψ t ∘ Φt = id from funext hΨΦ]
          exact (hasFDerivAt_id x).fderiv
        exact hd.symm.trans hid
      have h2 : (fderiv ℝ Φt x).comp (fderiv ℝ (Ψ t) (Φt x)) = 1 := by
        have hd := ((hΦt'.differentiable (by norm_num) (Ψ t (Φt x))).hasFDerivAt.comp (Φt x)
          (hΨt.differentiable (by norm_num) (Φt x)).hasFDerivAt).fderiv
        have hid : fderiv ℝ (Φt ∘ Ψ t) (Φt x) = 1 := by
          rw [show Φt ∘ Ψ t = id from funext hΦΨ]
          exact (hasFDerivAt_id (Φt x)).fderiv
        have hΨΦx : Ψ t (Φt x) = x := hΨΦ x
        rw [hΨΦx] at hd
        exact hd.symm.trans hid
      let u_tx : (Space d →L[ℝ] Space d)ˣ := ⟨fderiv ℝ Φt x, fderiv ℝ (Ψ t) (Φt x), h2, h1⟩
      have hinv_eq : Ring.inverse ((1 : Space d →L[ℝ] Space d) + t • fderiv ℝ X x) =
          fderiv ℝ (Ψ t) (Φt x) := by
        rw [← hdfΦ]
        exact Ring.inverse_unit u_tx
      have hdet_abs : |LinearMap.det (fderiv ℝ Φt x).toLinearMap| =
          LinearMap.det ((1 : Space d →L[ℝ] Space d) + t • fderiv ℝ X x).toLinearMap := by
        have hp : 0 < LinearMap.det (fderiv ℝ Φt x).toLinearMap := hdet_pos x
        rw [abs_of_pos hp, hdfΦ]
      dsimp only [F, H]
      rw [hdet_abs, hinv_eq, smul_apply]
    have hPV_0 : variationalPerimeter b E Ω =
        ENNReal.ofReal (∫ x, F 0 x ∂(μ.restrict Ω)) := by
      have h0_eq : variationalPerimeter b ((id : Space d → Space d) '' E)
          ((id : Space d → Space d) '' Ω) =
          ENNReal.ofReal (∫ x in Ω, ‖|LinearMap.det (fderiv ℝ id x).toLinearMap| •
            ((fderiv ℝ id (id x)).adjoint (ν x))‖ ∂μ) :=
        variationalPerimeter_image_diffeomorph_of_eq_id_compl b hΩ Subset.rfl isCompact_empty
          contDiff_id contDiff_id (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl) μ hν hνunit hdist
      rw [Set.image_id, Set.image_id] at h0_eq
      rw [hF0, h0_eq]
      congr 1
      refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
      have hid_fderiv : fderiv ℝ (id : Space d → Space d) x =
          ContinuousLinearMap.id ℝ (Space d) := (hasFDerivAt_id x).fderiv
      have hid_fderiv2 : fderiv ℝ (id : Space d → Space d) (id x) =
          ContinuousLinearMap.id ℝ (Space d) := (hasFDerivAt_id (id x)).fderiv
      have hdet1 : LinearMap.det (ContinuousLinearMap.id ℝ (Space d)).toLinearMap = 1 :=
        LinearMap.det_id
      dsimp only
      rw [hid_fderiv, hid_fderiv2, hdet1, abs_one, ContinuousLinearMap.adjoint_id,
        one_smul, ContinuousLinearMap.id_apply]
    rw [hPV_0, hPV_t] at hcomp_t
    exact (ENNReal.ofReal_le_ofReal_iff
      (integral_nonneg fun x ↦ norm_nonneg _)).mp hcomp_t
  exact hlocal_min.hasDerivAt_eq_zero hderiv_int.2

/-- First Variation Stationarity (BV9.2) for local perimeter minimizers in an open set `Ω`
against arbitrary compactly supported `C¹` vector fields `X` with `tsupport X ⊆ Ω`. -/
theorem perimeter_first_variation_eq_zero {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) {E Ω : Set (Space d)}
    (hE : MeasurableSet E) (hΩ : IsOpen Ω)
    (hmin : ∀ D, MeasurableSet D →
      (∃ K, IsCompact K ∧ K ⊆ Ω ∧ ∀ᵐ x ∂volume, x ∉ K → (x ∈ E ↔ x ∈ D)) →
      variationalPerimeter b E Ω ≤ variationalPerimeter b D Ω)
    (μ : Measure (Space d)) {ν : Space d → Space d}
    (hν : Integrable ν (μ.restrict Ω))
    (hνunit : ∀ᵐ x ∂μ.restrict Ω, ‖ν x‖ = 1)
    (hdist : ∀ F : C_c(Space d, Space d), ContDiff ℝ 1 (F : Space d → Space d) →
      tsupport F ⊆ Ω →
      -(∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F x) =
        ∫ x, inner ℝ (F x) (ν x) ∂μ.restrict Ω)
    {X : Space d → Space d} (hX : ContDiff ℝ 1 X)
    (hXc : HasCompactSupport X) (hXΩ : tsupport X ⊆ Ω) :
    ∫ x, (fieldDivergence b X x - inner ℝ (ν x) (fderiv ℝ X x (ν x))) ∂(μ.restrict Ω) = 0 := by
  have hμ_fin : IsFiniteMeasure (μ.restrict Ω) := by
    constructor
    have heq : ∫⁻ _, (1 : ℝ≥0∞) ∂(μ.restrict Ω) = ∫⁻ x, ‖ν x‖ₑ ∂(μ.restrict Ω) := by
      apply lintegral_congr_ae
      filter_upwards [hνunit] with x hx
      simp [← ofReal_norm, hx]
    rw [lintegral_const, one_mul] at heq
    exact heq ▸ hν.2
  obtain ⟨L, hL_comp, hXL_int, hLΩ⟩ := exists_compact_between hXc hΩ hXΩ
  obtain ⟨ε, hε_pos, hε_sub⟩ := hXc.exists_thickening_subset_open isOpen_interior hXL_int
  let Xi : Fin d → Space d → ℝ := fun i y ↦ inner ℝ (b i) (X y)
  have hXi (i : Fin d) : ContDiff ℝ 1 (Xi i) := (innerSL ℝ (b i)).contDiff.comp hX
  have hXi_supp (i : Fin d) : tsupport (Xi i) ⊆ tsupport X := by
    apply closure_minimal _ (isClosed_tsupport X)
    intro y hy
    by_contra hnot
    exact hy (by simp [Xi, image_eq_zero_of_notMem_tsupport hnot])
  have hXic (i : Fin d) : HasCompactSupport (Xi i) :=
    hXc.of_isClosed_subset (isClosed_tsupport _) (hXi_supp i)
  let Xn : ℕ → Space d → Space d := fun n x ↦ ∑ i : Fin d, mollify (Xi i) n x • b i
  have hXn_smooth (n : ℕ) : ContDiff ℝ 2 (Xn n) :=
    ContDiff.sum fun i _ ↦ ((mollify_contDiff (hXi i).continuous n).of_le (by simp)).smul
      contDiff_const
  have hXn_fderiv (n : ℕ) (x : Space d) :
      fderiv ℝ (Xn n) x =
        ∑ i : Fin d, (fderiv ℝ (mollify (Xi i) n) x).smulRight (b i) := by
    have hd := HasFDerivAt.sum (u := (Finset.univ : Finset (Fin d))) fun i _ ↦
      (((mollify_contDiff (hXi i).continuous n).differentiable (by simp) x).hasFDerivAt).smul_const
        (b i)
    have hfun : (∑ i : Fin d, fun y ↦ mollify (Xi i) n y • b i) = Xn n := by
      ext y
      simp [Xn]
    rw [hfun] at hd
    exact hd.fderiv
  have hX_fderiv_sum (x : Space d) :
      fderiv ℝ X x = ∑ i : Fin d, (fderiv ℝ (Xi i) x).smulRight (b i) := by
    have hd := HasFDerivAt.sum (u := (Finset.univ : Finset (Fin d))) fun i _ ↦
      (((hXi i).differentiable one_ne_zero x).hasFDerivAt).smul_const (b i)
    have hfun : (∑ i : Fin d, fun y ↦ Xi i y • b i) = X := by
      funext y
      simpa only [Finset.sum_apply] using b.sum_repr' (X y)
    rw [hfun] at hd
    exact hd.fderiv
  have hXn_fderiv_tendsto (x : Space d) :
      Tendsto (fun n ↦ fderiv ℝ (Xn n) x) atTop (𝓝 (fderiv ℝ X x)) := by
    simp_rw [hXn_fderiv, hX_fderiv_sum]
    refine tendsto_finsetSum _ fun i _ ↦ ?_
    have hclm : Continuous (fun f : Space d →L[ℝ] ℝ ↦ f.smulRight (b i)) :=
      ((ContinuousLinearMap.smulRightL ℝ (Space d) (Space d)).flip (b i)).continuous
    exact (hclm.tendsto _).comp (mollify_fderiv_tendsto (hXi i) (hXic i) x)
  obtain ⟨M₀, hM₀⟩ := hXc.exists_bound_of_continuousOn
    (hX.continuous_fderiv one_ne_zero).continuousOn
  let M : ℝ := max M₀ 0
  have hM_nonneg : 0 ≤ M := le_max_right M₀ 0
  have hX_fderiv_bound (x : Space d) : ‖fderiv ℝ X x‖ ≤ M := by
    by_cases hx : x ∈ tsupport X
    · exact (hM₀ x hx).trans (le_max_left M₀ 0)
    · rw [fderiv_of_notMem_tsupport ℝ hx, norm_zero]
      exact hM_nonneg
  have hXi_fderiv_bound (i : Fin d) (x : Space d) : ‖fderiv ℝ (Xi i) x‖ ≤ M := by
    have hd : fderiv ℝ (Xi i) x = (innerSL ℝ (b i)).comp (fderiv ℝ X x) :=
      ((innerSL ℝ (b i)).hasFDerivAt.comp x (hX.differentiable one_ne_zero x).hasFDerivAt).fderiv
    rw [hd]
    calc
      ‖(innerSL ℝ (b i)).comp (fderiv ℝ X x)‖
        ≤ ‖innerSL ℝ (b i)‖ * ‖fderiv ℝ X x‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * M := mul_le_mul (by rw [innerSL_apply_norm, b.orthonormal.1])
          (hX_fderiv_bound x) (norm_nonneg _) zero_le_one
      _ = M := one_mul M
  have hmollify_fderiv_bound (i : Fin d) (n : ℕ) (x : Space d) :
      ‖fderiv ℝ (mollify (Xi i) n) x‖ ≤ M := by
    rw [mollify_fderiv (hXi i) (hXic i) n x]
    change ‖∫ t, (averagingBump d n).normed volume t • fderiv ℝ (Xi i) (x - t)‖ ≤ M
    calc
      ‖∫ t, (averagingBump d n).normed volume t • fderiv ℝ (Xi i) (x - t)‖
        ≤ ∫ t, ‖(averagingBump d n).normed volume t • fderiv ℝ (Xi i) (x - t)‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ t, (averagingBump d n).normed volume t * M := by
          apply integral_mono_of_nonneg (Eventually.of_forall fun _ ↦ norm_nonneg _)
            (((averagingBump d n).integrable_normed (μ := volume)).mul_const M)
          exact Eventually.of_forall fun t ↦ by
            dsimp only
            rw [norm_smul, Real.norm_of_nonneg ((averagingBump d n).nonneg_normed t)]
            exact mul_le_mul_of_nonneg_left (hXi_fderiv_bound i (x - t))
              ((averagingBump d n).nonneg_normed t)
      _ = M := by rw [integral_mul_const, (averagingBump d n).integral_normed, one_mul]
  have hXn_fderiv_bound (n : ℕ) (x : Space d) : ‖fderiv ℝ (Xn n) x‖ ≤ (d : ℝ) * M := by
    rw [hXn_fderiv]
    calc
      ‖∑ i : Fin d, (fderiv ℝ (mollify (Xi i) n) x).smulRight (b i)‖
        ≤ ∑ i : Fin d, ‖(fderiv ℝ (mollify (Xi i) n) x).smulRight (b i)‖ := norm_sum_le _ _
      _ ≤ ∑ _ : Fin d, M := by
          apply Finset.sum_le_sum
          intro i _
          rw [ContinuousLinearMap.norm_smulRight_apply, b.orthonormal.1, mul_one]
          exact hmollify_fderiv_bound i n x
      _ = (d : ℝ) * M := by simp
  have hev_zero :
      (fun n ↦ ∫ x, (fieldDivergence b (Xn n) x -
        inner ℝ (ν x) (fderiv ℝ (Xn n) x (ν x))) ∂(μ.restrict Ω)) =ᶠ[atTop] fun _ ↦ 0 := by
    have hsmall : ∀ᶠ n : ℕ in atTop, (averagingBump d n).rOut < ε :=
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually (gt_mem_nhds hε_pos)
    filter_upwards [hsmall] with n hn_eps
    have hXn_supp : tsupport (Xn n) ⊆ L := by
      apply closure_minimal _ hL_comp.isClosed
      intro x hx
      by_contra hxL
      have hx_th : x ∉ thickening ε (tsupport X) :=
        fun hth ↦ hxL (interior_subset (hε_sub hth))
      apply hx
      suffices h0 : ∀ i : Fin d, mollify (Xi i) n x = 0 by
        simp [Xn, h0]
      intro i
      apply integral_eq_zero_of_ae
      filter_upwards with t
      change (averagingBump d n).normed volume t * Xi i (x - t) = 0
      by_cases hk : (averagingBump d n).normed volume t = 0
      · rw [hk, zero_mul]
      · have ht_ball : t ∈ ball (0 : Space d) (averagingBump d n).rOut := by
          rw [← (averagingBump d n).support_normed_eq (μ := volume)]
          exact hk
        have ht_lt : ‖t‖ < (averagingBump d n).rOut := by
          simpa [mem_ball, dist_zero_right] using ht_ball
        have ht_eps : ‖t‖ < ε := ht_lt.trans hn_eps
        have hxt_not : x - t ∉ tsupport X := by
          intro hmem
          apply hx_th
          rw [mem_thickening_iff]
          exact ⟨x - t, hmem, by simpa [dist_eq_norm] using ht_eps⟩
        have hXi0 : Xi i (x - t) = 0 :=
          image_eq_zero_of_notMem_tsupport (fun hh ↦ hxt_not (hXi_supp i hh))
        rw [hXi0, mul_zero]
    have hXnc : HasCompactSupport (Xn n) :=
      hL_comp.of_isClosed_subset (isClosed_tsupport _) hXn_supp
    exact perimeter_first_variation_eq_zero_of_contDiff_two b hE hΩ hmin μ hν hνunit hdist
      (hXn_smooth n) hXnc (hXn_supp.trans hLΩ)
  have hlim : Tendsto
      (fun n ↦ ∫ x, (fieldDivergence b (Xn n) x -
        inner ℝ (ν x) (fderiv ℝ (Xn n) x (ν x))) ∂(μ.restrict Ω))
      atTop
      (𝓝 (∫ x, (fieldDivergence b X x - inner ℝ (ν x) (fderiv ℝ X x (ν x))) ∂(μ.restrict Ω))) := by
    apply tendsto_integral_of_dominated_convergence (fun _ ↦ ((d : ℝ) + 1) * ((d : ℝ) * M))
    · intro n
      have hXn1 : ContDiff ℝ 1 (Xn n) := (hXn_smooth n).of_le (by norm_num)
      have hdiv_c : Continuous (fieldDivergence b (Xn n)) :=
        continuous_finsetSum _ fun i _ ↦ continuous_const.inner
          ((hXn1.continuous_fderiv one_ne_zero).clm_apply continuous_const)
      have hAX_m : AEStronglyMeasurable (fun x ↦ fderiv ℝ (Xn n) x (ν x)) (μ.restrict Ω) :=
        isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable
          ((hXn1.continuous_fderiv one_ne_zero).aestronglyMeasurable.prodMk
            hν.aestronglyMeasurable)
      exact hdiv_c.aestronglyMeasurable.sub (hν.aestronglyMeasurable.inner hAX_m)
    · exact integrable_const _
    · intro n
      filter_upwards [hνunit] with x hx_unit
      have hdiv_le : ‖fieldDivergence b (Xn n) x‖ ≤ (d : ℝ) * ((d : ℝ) * M) := by
        unfold fieldDivergence
        calc
          ‖∑ i : Fin d, inner ℝ (b i) (fderiv ℝ (Xn n) x (b i))‖
            ≤ ∑ i : Fin d, ‖inner ℝ (b i) (fderiv ℝ (Xn n) x (b i))‖ := norm_sum_le _ _
          _ ≤ ∑ _ : Fin d, ((d : ℝ) * M) := by
              apply Finset.sum_le_sum
              intro i _
              calc
                ‖inner ℝ (b i) (fderiv ℝ (Xn n) x (b i))‖
                  ≤ ‖b i‖ * ‖fderiv ℝ (Xn n) x (b i)‖ := norm_inner_le_norm _ _
                _ ≤ ‖b i‖ * (‖fderiv ℝ (Xn n) x‖ * ‖b i‖) :=
                    mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
                _ = ‖fderiv ℝ (Xn n) x‖ := by rw [b.orthonormal.1, mul_one, one_mul]
                _ ≤ (d : ℝ) * M := hXn_fderiv_bound n x
          _ = (d : ℝ) * ((d : ℝ) * M) := by simp
      have hinn_le : ‖inner ℝ (ν x) (fderiv ℝ (Xn n) x (ν x))‖ ≤ (d : ℝ) * M := by
        calc
          ‖inner ℝ (ν x) (fderiv ℝ (Xn n) x (ν x))‖
            ≤ ‖ν x‖ * (‖fderiv ℝ (Xn n) x‖ * ‖ν x‖) :=
              (norm_inner_le_norm _ _).trans
                (mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _))
          _ = ‖fderiv ℝ (Xn n) x‖ := by rw [hx_unit, one_mul, mul_one]
          _ ≤ (d : ℝ) * M := hXn_fderiv_bound n x
      calc
        ‖fieldDivergence b (Xn n) x - inner ℝ (ν x) (fderiv ℝ (Xn n) x (ν x))‖
          ≤ ‖fieldDivergence b (Xn n) x‖ + ‖inner ℝ (ν x) (fderiv ℝ (Xn n) x (ν x))‖ :=
            norm_sub_le _ _
        _ ≤ (d : ℝ) * ((d : ℝ) * M) + (d : ℝ) * M := add_le_add hdiv_le hinn_le
        _ = ((d : ℝ) + 1) * ((d : ℝ) * M) := by ring
    · refine Eventually.of_forall fun x ↦ ?_
      have hdiv_t : Tendsto (fun n ↦ fieldDivergence b (Xn n) x)
          atTop (𝓝 (fieldDivergence b X x)) := by
        unfold fieldDivergence
        refine tendsto_finsetSum _ fun i _ ↦ tendsto_const_nhds.inner ?_
        exact ((ContinuousLinearMap.apply ℝ (Space d) (b i)).continuous.tendsto _).comp
          (hXn_fderiv_tendsto x)
      have hinn_t : Tendsto (fun n ↦ inner ℝ (ν x) (fderiv ℝ (Xn n) x (ν x)))
          atTop (𝓝 (inner ℝ (ν x) (fderiv ℝ X x (ν x)))) :=
        tendsto_const_nhds.inner
          (((ContinuousLinearMap.apply ℝ (Space d) (ν x)).continuous.tendsto _).comp
            (hXn_fderiv_tendsto x))
      exact hdiv_t.sub hinn_t
  exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' hev_zero.symm)

end SerrinEpigraph
