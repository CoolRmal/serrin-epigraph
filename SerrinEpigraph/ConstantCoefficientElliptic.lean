module

public import SerrinEpigraph.HarmonicWeyl
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.Calculus.Rademacher

/-!
# Constant-coefficient elliptic equations

For a continuous linear map `A : Space d →L[ℝ] Space d` we study the operator
`aLaplacian A φ x = ∑ᵢ D²φ(x)[eᵢ, A eᵢ]` (the trace of `D²φ(x) ∘ A` in the standard orthonormal
basis; for symmetric `A` this is `∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼφ`, and `aLaplacian_id` identifies it with `Δ` for
`A = id`). Uniform ellipticity is the bundled hypothesis `IsUniformlyElliptic A ν Λ`: `A` is
symmetric and `ν ‖ξ‖² ≤ ⟪A ξ, ξ⟫ ≤ Λ ‖ξ‖²` with `0 < ν ≤ Λ`.

* `IsVeryWeaklyAHarmonicOn A U w`: local integrability and `∫ w * L_A φ = 0` for all smooth
  compactly supported tests in `U`.
* `laplacian_comp_eq_aLaplacian`, `isVeryWeaklyAHarmonicOn_iff_comp`: if `T Tᵀ = A` then
  `Δ (φ ∘ T) = (L_A φ) ∘ T`, and `w` is very weakly `A`-harmonic on `U` iff `w ∘ T` is very
  weakly harmonic on `T⁻¹ U`. `exists_symm_sqrt_of_pos_def` constructs the symmetric square root
  of a symmetric positive definite `A` from its eigenbasis.
* `aWeyl_lemma`: a very weakly `A`-harmonic function agrees a.e. with a smooth classical solution;
  `isVeryWeaklyAHarmonicOn_of_aHarmonic` is the converse.
* `integral_mul_aLaplacian_eq_neg_of_lipschitz`, `integral_mul_aLaplacian_eq_neg_of_contDiffOn`,
  `isVeryWeaklyAHarmonicOn_of_lipschitz`, `isVeryWeaklyAHarmonicOn_iff_of_lipschitz`,
  `isVeryWeaklyAHarmonicOn_of_contDiffOn`: the weak form `∫ ⟪A ∇w, ∇φ⟫ = 0`.
* `norm_fderiv_le_of_aHarmonic`, `norm_iteratedFDeriv_two_le_of_aHarmonic`,
  `norm_iteratedFDeriv_two_le_of_aHarmonic_grad`, `aHarmonic_fderiv_excess_le`,
  `aHarmonic_taylor_excess_le`: interior estimates and excess decay with constants depending only
  on `d`, `ν`, `Λ`, obtained from the harmonic ones through `w ∘ A^{1/2}` (balls are compared
  with the ellipsoids `A^{1/2}(B)` using `√ν ‖u‖ ≤ ‖A^{1/2} u‖ ≤ √Λ ‖u‖` and
  `|det A^{1/2}| ≥ ν^{d/2}`).
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory Filter InnerProductSpace
open scoped Topology Laplacian ContDiff

namespace SerrinEpigraph

variable {d : ℕ}

/-! ### The operator and very weak solutions -/

/-- The constant-coefficient operator `L_A φ (x) = ∑ᵢ D²φ(x)[eᵢ, A eᵢ]` in the standard
orthonormal basis `(eᵢ)`. -/
def aLaplacian (A : Space d →L[ℝ] Space d) (φ : Space d → ℝ) (x : Space d) : ℝ :=
  ∑ i, fderiv ℝ (fderiv ℝ φ) x (stdOrthonormalBasis ℝ (Space d) i)
    (A (stdOrthonormalBasis ℝ (Space d) i))

/-- Very weak `A`-harmonicity on an open set: `w` is locally integrable on `U` and
`∫ w * L_A φ = 0` for every smooth (`C^∞`) compactly supported `φ` with `tsupport φ ⊆ U`. -/
def IsVeryWeaklyAHarmonicOn (A : Space d →L[ℝ] Space d) (U : Set (Space d))
    (w : Space d → ℝ) : Prop :=
  LocallyIntegrableOn w U ∧
    ∀ φ : Space d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ U →
      ∫ x, w x * aLaplacian A φ x = 0

/-- Uniform ellipticity: `A` is symmetric and `ν ‖ξ‖² ≤ ⟪A ξ, ξ⟫ ≤ Λ ‖ξ‖²` with `0 < ν ≤ Λ`. -/
structure IsUniformlyElliptic (A : Space d →L[ℝ] Space d) (ν Λ : ℝ) : Prop where
  symm : ∀ u v, inner ℝ (A u) v = inner ℝ u (A v)
  pos : 0 < ν
  le : ν ≤ Λ
  lower : ∀ ξ, ν * ‖ξ‖ ^ 2 ≤ inner ℝ (A ξ) ξ
  upper : ∀ ξ, inner ℝ (A ξ) ξ ≤ Λ * ‖ξ‖ ^ 2

private theorem laplacian_eq_sum_fderiv_fderiv_aux (u : Space d → ℝ) (y : Space d) :
    Δ u y = ∑ i, fderiv ℝ (fderiv ℝ u) y (stdOrthonormalBasis ℝ (Space d) i)
      (stdOrthonormalBasis ℝ (Space d) i) := by
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  simp [iteratedFDeriv_two_apply]

private theorem fderiv_fderiv_apply_eq_aux {u : Space d → ℝ} {x : Space d}
    (hu : DifferentiableAt ℝ (fderiv ℝ u) x) (v w : Space d) :
    fderiv ℝ (fun y ↦ fderiv ℝ u y w) x v = fderiv ℝ (fderiv ℝ u) x v w := by
  rw [fderiv_clm_apply hu (differentiableAt_const w)]
  simp

theorem aLaplacian_id (φ : Space d → ℝ) (x : Space d) :
    aLaplacian (ContinuousLinearMap.id ℝ (Space d)) φ x = Δ φ x := by
  rw [laplacian_eq_sum_fderiv_fderiv_aux]
  rfl

theorem isVeryWeaklyAHarmonicOn_id_iff {U : Set (Space d)} {w : Space d → ℝ} :
    IsVeryWeaklyAHarmonicOn (ContinuousLinearMap.id ℝ (Space d)) U w ↔
      IsVeryWeaklyHarmonicOn U w := by
  simp only [IsVeryWeaklyAHarmonicOn, IsVeryWeaklyHarmonicOn, aLaplacian_id]

/-! ### Linear changes of variables -/

/-- `∑ᵢ D (T bᵢ) (T bᵢ) = ∑ⱼ D bⱼ (T (Tᵀ bⱼ))` for a bilinear form `D` and a linear map `T`. -/
private theorem sum_apply_comp_eq_sum_adjoint {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (Space d)) (D : Space d →L[ℝ] Space d →L[ℝ] ℝ)
    (T : Space d →L[ℝ] Space d) :
    ∑ i, D (T (b i)) (T (b i)) = ∑ j, D (b j) (T (ContinuousLinearMap.adjoint T (b j))) := by
  have h1 : ∀ i, D (T (b i)) (T (b i)) = ∑ j, inner ℝ (b j) (T (b i)) * D (b j) (T (b i)) := by
    intro i
    have hD : D (T (b i)) = ∑ j, inner ℝ (b j) (T (b i)) • D (b j) := by
      conv_lhs => rw [← b.sum_repr' (T (b i))]
      rw [map_sum]
      simp_rw [map_smul]
    rw [hD]
    simp
  have h2 : ∀ j, ∑ i, inner ℝ (b j) (T (b i)) • b i = ContinuousLinearMap.adjoint T (b j) := by
    intro j
    conv_rhs => rw [← b.sum_repr' (ContinuousLinearMap.adjoint T (b j))]
    congr 1
    funext i
    rw [ContinuousLinearMap.adjoint_inner_right, real_inner_comm]
  simp_rw [h1]
  rw [Finset.sum_comm]
  congr 1
  funext j
  rw [← h2 j, map_sum, map_sum]
  congr 1
  funext i
  rw [map_smul, map_smul, smul_eq_mul]

/-- **Pointwise change of variables**: if `T Tᵀ = A`, then `Δ (φ ∘ T) y = L_A φ (T y)`. -/
theorem laplacian_comp_eq_aLaplacian {A : Space d →L[ℝ] Space d} (T : Space d ≃L[ℝ] Space d)
    (hT : ∀ u, T (ContinuousLinearMap.adjoint (T : Space d →L[ℝ] Space d) u) = A u)
    {φ : Space d → ℝ} {y : Space d} (hφ : ContDiffAt ℝ 2 φ (T y)) :
    Δ (fun y ↦ φ (T y)) y = aLaplacian A φ (T y) := by
  set b := stdOrthonormalBasis ℝ (Space d) with hb
  have hcomp : ∀ z, fderiv ℝ (fun y ↦ φ (T y)) z =
      (fderiv ℝ φ (T z)).comp (T : Space d →L[ℝ] Space d) :=
    fun z ↦ T.comp_right_fderiv (f := φ) (x := z)
  have hu : ContDiffAt ℝ 2 (fun y ↦ φ (T y)) y := hφ.comp y T.contDiff.contDiffAt
  have hdu : DifferentiableAt ℝ (fderiv ℝ (fun y ↦ φ (T y))) y :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hdφ : DifferentiableAt ℝ (fderiv ℝ φ) (T y) :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h2 : ∀ v w, fderiv ℝ (fderiv ℝ (fun y ↦ φ (T y))) y v w =
      fderiv ℝ (fderiv ℝ φ) (T y) (T v) (T w) := by
    intro v w
    rw [← fderiv_fderiv_apply_eq_aux hdu]
    have hfun : (fun z ↦ fderiv ℝ (fun y ↦ φ (T y)) z w) =
        (fun z' ↦ fderiv ℝ φ z' (T w)) ∘ T := by
      funext z
      rw [hcomp z]
      rfl
    rw [hfun, T.comp_right_fderiv]
    exact fderiv_fderiv_apply_eq_aux hdφ (T v) (T w)
  rw [laplacian_eq_sum_fderiv_fderiv_aux]
  simp_rw [h2]
  have h3 := sum_apply_comp_eq_sum_adjoint b (fderiv ℝ (fderiv ℝ φ) (T y))
    (T : Space d →L[ℝ] Space d)
  simp only [ContinuousLinearEquiv.coe_coe] at h3
  rw [h3]
  simp_rw [hT]
  rfl

private theorem det_ne_zero_aux (T : Space d ≃L[ℝ] Space d) :
    LinearMap.det (T : Space d →ₗ[ℝ] Space d) ≠ 0 :=
  (LinearEquiv.isUnit_det' T.toLinearEquiv).ne_zero

theorem map_continuousLinearEquiv_volume (T : Space d ≃L[ℝ] Space d) :
    Measure.map T (volume : Measure (Space d)) =
      ENNReal.ofReal |(LinearMap.det (T : Space d →ₗ[ℝ] Space d))⁻¹| • volume :=
  Measure.map_linearMap_addHaar_eq_smul_addHaar volume (det_ne_zero_aux T)

/-- Change of variables under a linear isomorphism. -/
theorem integral_comp_continuousLinearEquiv (T : Space d ≃L[ℝ] Space d) (g : Space d → ℝ) :
    ∫ y, g (T y) = |(LinearMap.det (T : Space d →ₗ[ℝ] Space d))⁻¹| * ∫ z, g z := by
  have h1 := integral_map_equiv (μ := (volume : Measure (Space d)))
    T.toHomeomorph.toMeasurableEquiv g
  have hmap : Measure.map T.toHomeomorph.toMeasurableEquiv (volume : Measure (Space d)) =
      ENNReal.ofReal |(LinearMap.det (T : Space d →ₗ[ℝ] Space d))⁻¹| • volume :=
    map_continuousLinearEquiv_volume T
  rw [hmap, integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _), smul_eq_mul] at h1
  exact h1.symm

theorem integrable_comp_continuousLinearEquiv_iff (T : Space d ≃L[ℝ] Space d)
    {g : Space d → ℝ} : Integrable (fun y ↦ g (T y)) ↔ Integrable g := by
  have hmap : Measure.map T.toHomeomorph.toMeasurableEquiv (volume : Measure (Space d)) =
      ENNReal.ofReal |(LinearMap.det (T : Space d →ₗ[ℝ] Space d))⁻¹| • volume :=
    map_continuousLinearEquiv_volume T
  have hc0 : ENNReal.ofReal |(LinearMap.det (T : Space d →ₗ[ℝ] Space d))⁻¹| ≠ 0 :=
    (ENNReal.ofReal_pos.2 (abs_pos.2 (inv_ne_zero (det_ne_zero_aux T)))).ne'
  have h1 := integrable_map_equiv (μ := (volume : Measure (Space d)))
    T.toHomeomorph.toMeasurableEquiv g
  rw [hmap, integrable_smul_measure hc0 ENNReal.ofReal_ne_top] at h1
  exact h1.symm

theorem quasiMeasurePreserving_continuousLinearEquiv (T : Space d ≃L[ℝ] Space d) :
    Measure.QuasiMeasurePreserving T (volume : Measure (Space d)) volume :=
  ⟨T.continuous.measurable, by
    rw [map_continuousLinearEquiv_volume]
    exact Measure.smul_absolutelyContinuous⟩

theorem ae_restrict_comp_continuousLinearEquiv (T : Space d ≃L[ℝ] Space d)
    {U : Set (Space d)} {f g : Space d → ℝ} (h : f =ᵐ[volume.restrict U] g) :
    (fun y ↦ f (T y)) =ᵐ[volume.restrict (T ⁻¹' U)] fun y ↦ g (T y) :=
  ((quasiMeasurePreserving_continuousLinearEquiv T).restrict (mapsTo_preimage T U)).ae_eq_comp h

theorem locallyIntegrableOn_comp_continuousLinearEquiv {U : Set (Space d)} (hU : IsOpen U)
    {g : Space d → ℝ} (hg : LocallyIntegrableOn g U) (T : Space d ≃L[ℝ] Space d) :
    LocallyIntegrableOn (fun y ↦ g (T y)) (T ⁻¹' U) := by
  rw [locallyIntegrableOn_iff (hU.preimage T.continuous).isLocallyClosed]
  intro K hKU hK
  have hTK : IsCompact (T '' K) := hK.image T.continuous
  have hTKU : T '' K ⊆ U := by
    rintro _ ⟨y, hy, rfl⟩
    exact hKU hy
  have hint : IntegrableOn g (T '' K) :=
    (locallyIntegrableOn_iff hU.isLocallyClosed).1 hg _ hTKU hTK
  have h1 : Integrable ((T '' K).indicator g) :=
    (integrable_indicator_iff hTK.measurableSet).2 hint
  have h2 : Integrable (fun y ↦ (T '' K).indicator g (T y)) :=
    (integrable_comp_continuousLinearEquiv_iff T).2 h1
  have h3 : (fun y ↦ (T '' K).indicator g (T y)) = K.indicator (fun y ↦ g (T y)) := by
    funext y
    by_cases hy : y ∈ K
    · rw [indicator_of_mem hy, indicator_of_mem (mem_image_of_mem T hy)]
    · have hy' : T y ∉ T '' K := fun h ↦ hy (T.injective.mem_set_image.1 h)
      rw [indicator_of_notMem hy, indicator_of_notMem hy']
  rw [h3] at h2
  exact (integrable_indicator_iff hK.measurableSet).1 h2

/-- **Change of variables for very weak solutions**: if `T Tᵀ = A` then `w` is very weakly
`A`-harmonic on `U` iff `w ∘ T` is very weakly harmonic on `T⁻¹ U`. -/
theorem isVeryWeaklyAHarmonicOn_iff_comp {A : Space d →L[ℝ] Space d}
    (T : Space d ≃L[ℝ] Space d)
    (hT : ∀ u, T (ContinuousLinearMap.adjoint (T : Space d →L[ℝ] Space d) u) = A u)
    {U : Set (Space d)} (hU : IsOpen U) {w : Space d → ℝ} :
    IsVeryWeaklyAHarmonicOn A U w ↔ IsVeryWeaklyHarmonicOn (T ⁻¹' U) (fun y ↦ w (T y)) := by
  have hdet : 0 < |(LinearMap.det (T : Space d →ₗ[ℝ] Space d))⁻¹| :=
    abs_pos.2 (inv_ne_zero (det_ne_zero_aux T))
  have key : ∀ φ : Space d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
      ∫ y, w (T y) * Δ (fun y ↦ φ (T y)) y =
        |(LinearMap.det (T : Space d →ₗ[ℝ] Space d))⁻¹| * ∫ z, w z * aLaplacian A φ z := by
    intro φ hφ
    have hpt : ∀ y, Δ (fun y ↦ φ (T y)) y = aLaplacian A φ (T y) := fun y ↦
      laplacian_comp_eq_aLaplacian T hT (hφ.of_le (by simp)).contDiffAt
    simp_rw [hpt]
    exact integral_comp_continuousLinearEquiv T (fun z ↦ w z * aLaplacian A φ z)
  constructor
  · rintro ⟨hloc, hw⟩
    refine ⟨locallyIntegrableOn_comp_continuousLinearEquiv hU hloc T,
      fun ψ hψ hψc hψU ↦ ?_⟩
    let φ : Space d → ℝ := fun z ↦ ψ (T.symm z)
    have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := hψ.comp T.symm.contDiff
    have hφc : HasCompactSupport φ := hψc.comp_homeomorph T.symm.toHomeomorph
    have hφU : tsupport φ ⊆ U := by
      have he : tsupport φ = T.symm.toHomeomorph ⁻¹' tsupport ψ :=
        tsupport_comp_eq_preimage ψ T.symm.toHomeomorph
      rw [he]
      intro z hz
      have h1 := hψU hz
      simpa using h1
    have hψφ : (fun y ↦ φ (T y)) = ψ := by
      funext y
      simp [φ]
    have h1 := key φ hφ
    rw [hψφ] at h1
    rw [h1, hw φ hφ hφc hφU, mul_zero]
  · rintro ⟨hloc, hw⟩
    refine ⟨?_, fun φ hφ hφc hφU ↦ ?_⟩
    · have h1 := locallyIntegrableOn_comp_continuousLinearEquiv (hU.preimage T.continuous)
        hloc T.symm
      have hset : T.symm ⁻¹' (T ⁻¹' U) = U := by
        ext z
        simp
      have hfun : (fun y ↦ w (T (T.symm y))) = w := by
        funext y
        simp
      rw [hset, hfun] at h1
      exact h1
    · have hψ : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ φ (T y)) := hφ.comp T.contDiff
      have hψc : HasCompactSupport (fun y ↦ φ (T y)) := hφc.comp_homeomorph T.toHomeomorph
      have hψU : tsupport (fun y ↦ φ (T y)) ⊆ T ⁻¹' U := by
        have he : tsupport (fun y ↦ φ (T y)) = T.toHomeomorph ⁻¹' tsupport φ :=
          tsupport_comp_eq_preimage φ T.toHomeomorph
        rw [he]
        exact preimage_mono hφU
      have h0 := hw _ hψ hψc hψU
      rw [key φ hφ] at h0
      exact (mul_eq_zero.1 h0).resolve_left hdet.ne'


/-! ### Symmetric square roots and Weyl's lemma for `L_A` -/

/-- A symmetric positive definite `A` has a symmetric square root `T`, `T ∘ T = A`. -/
theorem exists_symm_sqrt_of_pos_def {A : Space d →L[ℝ] Space d}
    (hsymm : ∀ u v, inner ℝ (A u) v = inner ℝ u (A v)) {ν : ℝ} (hν : 0 < ν)
    (hell : ∀ ξ, ν * ‖ξ‖ ^ 2 ≤ inner ℝ (A ξ) ξ) :
    ∃ T : Space d ≃L[ℝ] Space d, (∀ u v, inner ℝ (T u) v = inner ℝ u (T v)) ∧
      ∀ u, T (T u) = A u := by
  have hS : (A : Space d →ₗ[ℝ] Space d).IsSymmetric := fun u v ↦ hsymm u v
  have hn : Module.finrank ℝ (Space d) = d := finrank_euclideanSpace_fin
  set q := hS.eigenvectorBasis hn with hqdef
  set μ := hS.eigenvalues hn with hμdef
  have hq : ∀ i, A (q i) = μ i • q i := fun i ↦ by
    have h1 := hS.apply_eigenvectorBasis hn i
    exact h1
  have hμ : ∀ i, ν ≤ μ i := by
    intro i
    have h1 := hell (q i)
    rw [hq i, real_inner_smul_left, real_inner_self_eq_norm_sq, q.orthonormal.1 i] at h1
    simpa using h1
  let S : Space d →L[ℝ] Space d := ∑ i, Real.sqrt (μ i) • (innerSL ℝ (q i)).smulRight (q i)
  have hSapp : ∀ u, S u = ∑ i, (Real.sqrt (μ i) * inner ℝ (q i) u) • q i := by
    intro u
    simp [S, smul_smul]
  have hinner : ∀ i u, inner ℝ (q i) (S u) = Real.sqrt (μ i) * inner ℝ (q i) u := by
    intro i u
    rw [hSapp, inner_sum]
    simp_rw [inner_smul_right, q.inner_eq_ite]
    simp
  have hSS : ∀ u, S (S u) = A u := by
    intro u
    rw [hSapp (S u)]
    simp_rw [hinner]
    conv_rhs => rw [← q.sum_repr' u]
    rw [map_sum]
    congr 1
    funext i
    rw [map_smul, hq i, smul_smul, ← mul_assoc, Real.mul_self_sqrt (by linarith [hμ i, hν])]
    ring_nf
  have hSsymm : ∀ u v, inner ℝ (S u) v = inner ℝ u (S v) := by
    intro u v
    rw [hSapp, hSapp, sum_inner, inner_sum]
    congr 1
    funext i
    rw [real_inner_smul_left, real_inner_smul_right, real_inner_comm (q i) u]
    ring
  have hinj : Function.Injective S := by
    intro u v huv
    have h1 : A (u - v) = 0 := by rw [← hSS, map_sub, huv, sub_self, map_zero]
    have h2 := hell (u - v)
    rw [h1, inner_zero_left] at h2
    have h3 : ‖u - v‖ ^ 2 ≤ 0 := by
      by_contra hc
      have h5 := mul_pos hν (lt_of_not_ge hc)
      linarith
    have h4 : ‖u - v‖ ^ 2 = 0 := le_antisymm h3 (sq_nonneg _)
    exact sub_eq_zero.1 (norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h4))
  exact ⟨(LinearEquiv.ofInjectiveEndo (S : Space d →ₗ[ℝ] Space d) hinj).toContinuousLinearEquiv,
    hSsymm, hSS⟩

theorem adjoint_eq_self_of_symm {T : Space d →L[ℝ] Space d}
    (hT : ∀ u v, inner ℝ (T u) v = inner ℝ u (T v)) : ContinuousLinearMap.adjoint T = T :=
  ((ContinuousLinearMap.eq_adjoint_iff T T).2 hT).symm

/-- A symmetric square root `T` of `A`, in the form used by the change of variables. -/
theorem exists_sqrt_comp_adjoint {A : Space d →L[ℝ] Space d}
    (hsymm : ∀ u v, inner ℝ (A u) v = inner ℝ u (A v)) {ν : ℝ} (hν : 0 < ν)
    (hell : ∀ ξ, ν * ‖ξ‖ ^ 2 ≤ inner ℝ (A ξ) ξ) :
    ∃ T : Space d ≃L[ℝ] Space d, (∀ u v, inner ℝ (T u) v = inner ℝ u (T v)) ∧
      (∀ u, T (T u) = A u) ∧
      ∀ u, T (ContinuousLinearMap.adjoint (T : Space d →L[ℝ] Space d) u) = A u := by
  obtain ⟨T, hTs, hTT⟩ := exists_symm_sqrt_of_pos_def hsymm hν hell
  refine ⟨T, hTs, hTT, fun u ↦ ?_⟩
  rw [adjoint_eq_self_of_symm (T := (T : Space d →L[ℝ] Space d)) hTs]
  exact hTT u

/-- **Weyl's lemma for constant coefficients**: a very weakly `A`-harmonic function agrees almost
everywhere with a smooth classical solution of `L_A w = 0`. -/
theorem aWeyl_lemma {A : Space d →L[ℝ] Space d}
    (hsymm : ∀ u v, inner ℝ (A u) v = inner ℝ u (A v)) {ν : ℝ} (hν : 0 < ν)
    (hell : ∀ ξ, ν * ‖ξ‖ ^ 2 ≤ inner ℝ (A ξ) ξ) {U : Set (Space d)} (hU : IsOpen U)
    {w : Space d → ℝ} (hw : IsVeryWeaklyAHarmonicOn A U w) :
    ∃ w' : Space d → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) w' U ∧ (∀ x ∈ U, aLaplacian A w' x = 0) ∧
      w =ᵐ[volume.restrict U] w' := by
  obtain ⟨T, -, -, hT⟩ := exists_sqrt_comp_adjoint hsymm hν hell
  have hv := (isVeryWeaklyAHarmonicOn_iff_comp T hT hU).1 hw
  obtain ⟨h', hh', hΔ', hae⟩ := weyl_lemma (hU.preimage T.continuous) hv
  have hmaps : MapsTo (fun z ↦ T.symm z) U (T ⁻¹' U) := fun z hz ↦ by simpa using hz
  have hw' : ContDiffOn ℝ (⊤ : ℕ∞) (fun z ↦ h' (T.symm z)) U :=
    hh'.comp T.symm.contDiff.contDiffOn hmaps
  refine ⟨fun z ↦ h' (T.symm z), hw', ?_, ?_⟩
  · intro x hx
    have hxU : T (T.symm x) ∈ U := by simpa using hx
    have hcd : ContDiffAt ℝ 2 (fun z ↦ h' (T.symm z)) (T (T.symm x)) :=
      (hw'.of_le (by simp)).contDiffAt (hU.mem_nhds hxU)
    have h1 := laplacian_comp_eq_aLaplacian T hT hcd
    have hfun : (fun y ↦ h' (T.symm (T y))) = h' := by
      funext y
      simp
    rw [hfun] at h1
    simp only [ContinuousLinearEquiv.apply_symm_apply] at h1
    rw [← h1]
    exact hΔ' _ (hmaps hx)
  · have h1 := ae_restrict_comp_continuousLinearEquiv T.symm hae
    have hset : T.symm ⁻¹' (T ⁻¹' U) = U := by
      ext z
      simp
    rw [hset] at h1
    simpa using h1

/-- A classical `C²` solution of `L_A w = 0` is very weakly `A`-harmonic. -/
theorem isVeryWeaklyAHarmonicOn_of_aHarmonic {A : Space d →L[ℝ] Space d}
    (hsymm : ∀ u v, inner ℝ (A u) v = inner ℝ u (A v)) {ν : ℝ} (hν : 0 < ν)
    (hell : ∀ ξ, ν * ‖ξ‖ ^ 2 ≤ inner ℝ (A ξ) ξ) {U : Set (Space d)} (hU : IsOpen U)
    {w : Space d → ℝ} (hw : ContDiffOn ℝ 2 w U) (hLw : ∀ y ∈ U, aLaplacian A w y = 0) :
    IsVeryWeaklyAHarmonicOn A U w := by
  obtain ⟨T, -, -, hT⟩ := exists_sqrt_comp_adjoint hsymm hν hell
  rw [isVeryWeaklyAHarmonicOn_iff_comp T hT hU]
  apply isVeryWeaklyHarmonicOn_of_harmonic (hU.preimage T.continuous)
  · exact hw.comp T.contDiff.contDiffOn (fun y hy ↦ hy)
  · intro y hy
    rw [laplacian_comp_eq_aLaplacian T hT (hw.contDiffAt (hU.mem_nhds hy))]
    exact hLw _ hy


/-! ### The weak form with gradients -/

private theorem integral_fderiv_apply_mul_eq_neg_of_lipschitz_aux {f ψ : Space d → ℝ}
    {K : NNReal} (hf : LipschitzWith K f) (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ)
    (v : Space d) :
    ∫ y, fderiv ℝ f y v * ψ y = -∫ y, f y * fderiv ℝ ψ y v := by
  obtain ⟨D, hD⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hψc hψ one_ne_zero
  have h := hf.integral_lineDeriv_mul_eq hD hψc v (μ := volume)
  have hl : ∫ y, fderiv ℝ f y v * ψ y = ∫ y, lineDeriv ℝ f y v * ψ y := by
    apply integral_congr_ae
    filter_upwards [hf.ae_differentiableAt (μ := volume)] with y hy
    rw [hy.lineDeriv_eq_fderiv]
  have hr : ∫ y, lineDeriv ℝ ψ y (-v) * f y = -∫ y, f y * fderiv ℝ ψ y v := by
    rw [← integral_neg]
    congr 1
    funext y
    rw [(hψ.differentiable one_ne_zero y).lineDeriv_eq_fderiv, map_neg]
    ring
  rw [hl, h, hr]

private theorem integrable_mul_of_continuousOn_of_tsupport_aux {c ψ : Space d → ℝ}
    {U : Set (Space d)} (hc : ContinuousOn c U) (hψ : Continuous ψ) (hψc : HasCompactSupport ψ)
    (hsub : tsupport ψ ⊆ U) : Integrable (fun x ↦ c x * ψ x) :=
  (integrableOn_iff_integrable_of_support_subset
    ((Function.support_mul_subset_right c ψ).trans (subset_tsupport ψ))).mp
    (((hc.mono hsub).mul hψ.continuousOn).integrableOn_compact hψc)

/-- The pointwise identity `⟪A ∇w, ∇φ⟫ = ∑ᵢ ∂_{eᵢ} w · ∂_{A eᵢ} φ`. -/
theorem inner_apply_gradient_eq_sum (A : Space d →L[ℝ] Space d) (w φ : Space d → ℝ)
    (x : Space d) :
    inner ℝ (A (gradient w x)) (gradient φ x) =
      ∑ i, fderiv ℝ w x (stdOrthonormalBasis ℝ (Space d) i) *
        fderiv ℝ φ x (A (stdOrthonormalBasis ℝ (Space d) i)) := by
  set b := stdOrthonormalBasis ℝ (Space d) with hb
  rw [real_inner_comm, inner_gradient_left]
  conv_lhs => rw [← b.sum_repr' (gradient w x)]
  rw [map_sum, map_sum]
  congr 1
  funext i
  rw [map_smul, map_smul, smul_eq_mul, real_inner_comm, inner_gradient_left]

/-- The summands of `L_A φ` as directional derivatives of the first derivatives. -/
private theorem aLaplacian_eq_sum_fderiv_apply {A : Space d →L[ℝ] Space d} {φ : Space d → ℝ}
    (hd : ContDiff ℝ 1 (fderiv ℝ φ)) (x : Space d) :
    aLaplacian A φ x = ∑ i, fderiv ℝ (fun y ↦ fderiv ℝ φ y (A (stdOrthonormalBasis ℝ (Space d) i)))
      x (stdOrthonormalBasis ℝ (Space d) i) := by
  unfold aLaplacian
  congr 1
  funext i
  exact (fderiv_fderiv_apply_eq_aux (hd.differentiable one_ne_zero x) _ _).symm

/-- **Integration by parts** for a Lipschitz function: `∫ w L_A φ = -∫ ⟪A ∇w, ∇φ⟫`. -/
theorem integral_mul_aLaplacian_eq_neg_of_lipschitz (A : Space d →L[ℝ] Space d)
    {w : Space d → ℝ} {K : NNReal} (hw : LipschitzWith K w) {φ : Space d → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) :
    ∫ x, w x * aLaplacian A φ x = -∫ x, inner ℝ (A (gradient w x)) (gradient φ x) := by
  set b := stdOrthonormalBasis ℝ (Space d) with hb
  have hd : ContDiff ℝ 1 (fderiv ℝ φ) := hφ.fderiv_right (m := 1) (by norm_num)
  have hψ : ∀ i, ContDiff ℝ 1 (fun y ↦ fderiv ℝ φ y (A (b i))) := fun i ↦
    hd.clm_apply contDiff_const
  have hψc : ∀ i, HasCompactSupport (fun y ↦ fderiv ℝ φ y (A (b i))) := fun i ↦
    hφc.fderiv_apply ℝ _
  have hint1 : ∀ i, Integrable
      (fun x ↦ w x * fderiv ℝ (fun y ↦ fderiv ℝ φ y (A (b i))) x (b i)) := by
    intro i
    have hcont : Continuous (fun x ↦ fderiv ℝ (fun y ↦ fderiv ℝ φ y (A (b i))) x (b i)) :=
      ((hψ i).continuous_fderiv one_ne_zero).clm_apply continuous_const
    exact (hw.continuous.mul hcont).integrable_of_hasCompactSupport
      ((hψc i).fderiv_apply ℝ (b i)).mul_left
  have hint2 : ∀ i, Integrable (fun x ↦ fderiv ℝ w x (b i) * fderiv ℝ φ x (A (b i))) := by
    intro i
    refine ((hψ i).continuous.integrable_of_hasCompactSupport (hψc i)).bdd_mul
      (c := K * ‖b i‖) (measurable_fderiv_apply_const ℝ w (b i)).aestronglyMeasurable
      (Eventually.of_forall (fun y ↦ ?_))
    exact ((fderiv ℝ w y).le_opNorm (b i)).trans
      (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hw) (norm_nonneg _))
  simp_rw [aLaplacian_eq_sum_fderiv_apply hd, Finset.mul_sum, inner_apply_gradient_eq_sum A w φ]
  rw [integral_finsetSum _ (fun i _ ↦ hint1 i), integral_finsetSum _ (fun i _ ↦ hint2 i),
    ← Finset.sum_neg_distrib]
  congr 1
  funext i
  rw [integral_fderiv_apply_mul_eq_neg_of_lipschitz_aux hw (hψ i) (hψc i) (b i), neg_neg]

/-- **Integration by parts** for a function that is `C¹` on an open set containing the support
of the test: `∫ w L_A φ = -∫ ⟪A ∇w, ∇φ⟫`. -/
theorem integral_mul_aLaplacian_eq_neg_of_contDiffOn (A : Space d →L[ℝ] Space d)
    {U : Set (Space d)} (hU : IsOpen U) {w : Space d → ℝ} (hw : ContDiffOn ℝ 1 w U)
    {φ : Space d → ℝ} (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) :
    ∫ x, w x * aLaplacian A φ x = -∫ x, inner ℝ (A (gradient w x)) (gradient φ x) := by
  set b := stdOrthonormalBasis ℝ (Space d) with hb
  have hd : ContDiff ℝ 1 (fderiv ℝ φ) := hφ.fderiv_right (m := 1) (by norm_num)
  have hψ : ∀ i, ContDiff ℝ 1 (fun y ↦ fderiv ℝ φ y (A (b i))) := fun i ↦
    hd.clm_apply contDiff_const
  have hψc : ∀ i, HasCompactSupport (fun y ↦ fderiv ℝ φ y (A (b i))) := fun i ↦
    hφc.fderiv_apply ℝ _
  have hψU : ∀ i, tsupport (fun y ↦ fderiv ℝ φ y (A (b i))) ⊆ U := fun i ↦
    (tsupport_fderiv_apply_subset ℝ _).trans hφU
  have hdw : ∀ i, ContinuousOn (fun x ↦ fderiv ℝ w x (b i)) U := fun i ↦
    (hw.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const
  have hint1 : ∀ i, Integrable
      (fun x ↦ w x * fderiv ℝ (fun y ↦ fderiv ℝ φ y (A (b i))) x (b i)) := fun i ↦
    integrable_mul_of_continuousOn_of_tsupport_aux hw.continuousOn
      (((hψ i).continuous_fderiv one_ne_zero).clm_apply continuous_const)
      ((hψc i).fderiv_apply ℝ (b i)) ((tsupport_fderiv_apply_subset ℝ _).trans (hψU i))
  have hint2 : ∀ i, Integrable (fun x ↦ fderiv ℝ w x (b i) * fderiv ℝ φ x (A (b i))) :=
    fun i ↦ integrable_mul_of_continuousOn_of_tsupport_aux (hdw i) (hψ i).continuous (hψc i)
      (hψU i)
  simp_rw [aLaplacian_eq_sum_fderiv_apply hd, Finset.mul_sum, inner_apply_gradient_eq_sum A w φ]
  rw [integral_finsetSum _ (fun i _ ↦ hint1 i), integral_finsetSum _ (fun i _ ↦ hint2 i),
    ← Finset.sum_neg_distrib]
  congr 1
  funext i
  exact integral_mul_fderiv_eq_neg_of_hasCompactSupport hU hw (hψ i) (hψc i) (hψU i) (b i)

/-- **Weak form with gradients** (Lipschitz version): if `∫ ⟪A ∇w, ∇φ⟫ = 0` for all smooth
tests supported in `U`, then `w` is very weakly `A`-harmonic on `U`. -/
theorem isVeryWeaklyAHarmonicOn_of_lipschitz (A : Space d →L[ℝ] Space d)
    {U : Set (Space d)} {w : Space d → ℝ} {K : NNReal} (hw : LipschitzWith K w)
    (hweak : ∀ φ : Space d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ U →
      ∫ x, inner ℝ (A (gradient w x)) (gradient φ x) = 0) :
    IsVeryWeaklyAHarmonicOn A U w :=
  ⟨hw.continuous.locallyIntegrable.locallyIntegrableOn U, fun φ hφ hφc hφU ↦ by
    rw [integral_mul_aLaplacian_eq_neg_of_lipschitz A hw (hφ.of_le (by simp)) hφc,
      hweak φ hφ hφc hφU, neg_zero]⟩

/-- For Lipschitz functions, very weak `A`-harmonicity is equivalent to the weak form. -/
theorem isVeryWeaklyAHarmonicOn_iff_of_lipschitz (A : Space d →L[ℝ] Space d)
    {U : Set (Space d)} {w : Space d → ℝ} {K : NNReal} (hw : LipschitzWith K w) :
    IsVeryWeaklyAHarmonicOn A U w ↔
      ∀ φ : Space d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ U →
        ∫ x, inner ℝ (A (gradient w x)) (gradient φ x) = 0 := by
  refine ⟨fun h φ hφ hφc hφU ↦ ?_, isVeryWeaklyAHarmonicOn_of_lipschitz A hw⟩
  have h1 := h.2 φ hφ hφc hφU
  rw [integral_mul_aLaplacian_eq_neg_of_lipschitz A hw (hφ.of_le (by simp)) hφc] at h1
  exact neg_eq_zero.1 h1

/-- **Weak form with gradients** (`C¹` version on an open set). -/
theorem isVeryWeaklyAHarmonicOn_of_contDiffOn (A : Space d →L[ℝ] Space d)
    {U : Set (Space d)} (hU : IsOpen U) {w : Space d → ℝ} (hw : ContDiffOn ℝ 1 w U)
    (hweak : ∀ φ : Space d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ U →
      ∫ x, inner ℝ (A (gradient w x)) (gradient φ x) = 0) :
    IsVeryWeaklyAHarmonicOn A U w :=
  ⟨hw.continuousOn.locallyIntegrableOn hU.measurableSet, fun φ hφ hφc hφU ↦ by
    rw [integral_mul_aLaplacian_eq_neg_of_contDiffOn A hU hw (hφ.of_le (by simp)) hφc hφU,
      hweak φ hφ hφc hφU, neg_zero]⟩


/-! ### Interior estimates for `A`-harmonic functions -/

section Estimates

variable {A : Space d →L[ℝ] Space d} {ν Λ : ℝ}

/-- A uniformly elliptic `A` has a square root `T` (`T Tᵀ = A`) with
`√ν ‖u‖ ≤ ‖T u‖ ≤ √Λ ‖u‖`. -/
theorem IsUniformlyElliptic.exists_sqrt (hA : IsUniformlyElliptic A ν Λ) :
    ∃ T : Space d ≃L[ℝ] Space d,
      (∀ u, T (ContinuousLinearMap.adjoint (T : Space d →L[ℝ] Space d) u) = A u) ∧
      (∀ u, ‖T u‖ ≤ Real.sqrt Λ * ‖u‖) ∧ ∀ u, Real.sqrt ν * ‖u‖ ≤ ‖T u‖ := by
  obtain ⟨T, hTs, hTT, hT⟩ := exists_sqrt_comp_adjoint hA.symm hA.pos hA.lower
  have hnorm : ∀ u, ‖T u‖ ^ 2 = inner ℝ (A u) u := by
    intro u
    rw [← real_inner_self_eq_norm_sq, hTs, hTT, real_inner_comm]
  refine ⟨T, hT, fun u ↦ ?_, fun u ↦ ?_⟩
  · calc ‖T u‖ = Real.sqrt (‖T u‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (Λ * ‖u‖ ^ 2) := Real.sqrt_le_sqrt (by rw [hnorm]; exact hA.upper u)
      _ = Real.sqrt Λ * ‖u‖ := by
          rw [Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  · calc Real.sqrt ν * ‖u‖ = Real.sqrt (ν * ‖u‖ ^ 2) := by
          rw [Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]
      _ ≤ Real.sqrt (‖T u‖ ^ 2) := Real.sqrt_le_sqrt (by rw [hnorm]; exact hA.lower u)
      _ = ‖T u‖ := Real.sqrt_sq (norm_nonneg _)

private theorem volume_real_ball_aux (x : Space d) {r : ℝ} (hr : 0 < r) :
    volume.real (ball x r) = r ^ d * volume.real (ball (0 : Space d) 1) := by
  rw [measureReal_def, Measure.addHaar_ball_of_pos volume x hr, finrank_euclideanSpace_fin,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hr.le d), measureReal_def]

private theorem volume_real_unit_ball_pos : 0 < volume.real (ball (0 : Space d) 1) :=
  ENNReal.toReal_pos (measure_ball_pos volume 0 one_pos).ne' measure_ball_lt_top.ne

/-- A lower bound `√ν ‖u‖ ≤ ‖T u‖` controls the Jacobian of `T⁻¹`. -/
theorem abs_det_inv_le_of_le_norm {T : Space d ≃L[ℝ] Space d} (hν : 0 < ν)
    (hT : ∀ u, Real.sqrt ν * ‖u‖ ≤ ‖T u‖) :
    |(LinearMap.det (T : Space d →ₗ[ℝ] Space d))⁻¹| ≤ (Real.sqrt ν ^ d)⁻¹ := by
  have hsν : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have hsub : ball (0 : Space d) (Real.sqrt ν) ⊆ T '' ball 0 1 := by
    intro z hz
    refine ⟨T.symm z, ?_, T.apply_symm_apply z⟩
    rw [mem_ball, dist_zero_right] at hz ⊢
    have h1 := hT (T.symm z)
    rw [T.apply_symm_apply] at h1
    by_contra hc
    have h2 : Real.sqrt ν * 1 ≤ Real.sqrt ν * ‖T.symm z‖ :=
      mul_le_mul_of_nonneg_left (not_lt.mp hc) hsν.le
    linarith
  have himg : volume.real (T '' ball (0 : Space d) 1) =
      |LinearMap.det (T : Space d →ₗ[ℝ] Space d)| * volume.real (ball (0 : Space d) 1) := by
    rw [measureReal_def, Measure.addHaar_image_continuousLinearEquiv, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (abs_nonneg _), measureReal_def]
  have hfin : volume (T '' ball (0 : Space d) 1) ≠ ⊤ := by
    rw [Measure.addHaar_image_continuousLinearEquiv]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne
  have hmono : volume.real (ball (0 : Space d) (Real.sqrt ν)) ≤
      volume.real (T '' ball (0 : Space d) 1) := measureReal_mono hsub hfin
  rw [volume_real_ball_aux 0 hsν, himg] at hmono
  have hle : Real.sqrt ν ^ d ≤ |LinearMap.det (T : Space d →ₗ[ℝ] Space d)| :=
    le_of_mul_le_mul_right hmono volume_real_unit_ball_pos
  rw [abs_inv]
  exact inv_anti₀ (pow_pos hsν d) hle

/-- Transfer of a set integral of a nonnegative function under a linear change of variables. -/
theorem setIntegral_comp_continuousLinearEquiv_le (T : Space d ≃L[ℝ] Space d)
    {g : Space d → ℝ} {S B : Set (Space d)} (hB : MeasurableSet B) (hg0 : ∀ z, 0 ≤ g z)
    (hgB : IntegrableOn g B) (hSB : S ⊆ T ⁻¹' B) :
    ∫ y in S, g (T y) ≤ |(LinearMap.det (T : Space d →ₗ[ℝ] Space d))⁻¹| * ∫ z in B, g z := by
  have hTB : MeasurableSet (T ⁻¹' B) := hB.preimage T.continuous.measurable
  have hind : (T ⁻¹' B).indicator (fun y ↦ g (T y)) = fun y ↦ B.indicator g (T y) := by
    funext y
    exact indicator_comp_right (s := B) T (g := g)
  have hint : IntegrableOn (fun y ↦ g (T y)) (T ⁻¹' B) := by
    rw [← integrable_indicator_iff hTB, hind]
    exact (integrable_comp_continuousLinearEquiv_iff T).2
      ((integrable_indicator_iff hB).2 hgB)
  calc ∫ y in S, g (T y) ≤ ∫ y in T ⁻¹' B, g (T y) :=
        setIntegral_mono_set hint (Eventually.of_forall fun y ↦ hg0 _) hSB.eventuallyLE
    _ = ∫ y, B.indicator g (T y) := by rw [← integral_indicator hTB, hind]
    _ = |(LinearMap.det (T : Space d →ₗ[ℝ] Space d))⁻¹| * ∫ z, B.indicator g z :=
        integral_comp_continuousLinearEquiv T _
    _ = _ := by rw [integral_indicator hB]

private theorem norm_symm_le_aux {T : Space d ≃L[ℝ] Space d} (hν : 0 < ν)
    (hT : ∀ u, Real.sqrt ν * ‖u‖ ≤ ‖T u‖) :
    ‖(T.symm : Space d →L[ℝ] Space d)‖ ≤ (Real.sqrt ν)⁻¹ := by
  have hsν : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  refine ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.2 hsν.le) fun z ↦ ?_
  have h1 := hT (T.symm z)
  rw [T.apply_symm_apply] at h1
  rw [ContinuousLinearEquiv.coe_coe, inv_mul_eq_div, le_div_iff₀ hsν, mul_comm]
  exact h1

private theorem norm_coe_le_aux {T : Space d ≃L[ℝ] Space d}
    (hT : ∀ u, ‖T u‖ ≤ Real.sqrt Λ * ‖u‖) :
    ‖(T : Space d →L[ℝ] Space d)‖ ≤ Real.sqrt Λ :=
  ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) hT

private theorem norm_iteratedFDeriv_two_comp_le_aux (v : Space d → ℝ)
    (S : Space d ≃L[ℝ] Space d) (x : Space d) :
    ‖iteratedFDeriv ℝ 2 (fun z ↦ v (S z)) x‖ ≤
      ‖iteratedFDeriv ℝ 2 v (S x)‖ * ‖(S : Space d →L[ℝ] Space d)‖ ^ 2 := by
  have h := S.iteratedFDerivWithin_comp_right v uniqueDiffOn_univ (mem_univ (S x)) 2
  simp only [iteratedFDerivWithin_univ, preimage_univ] at h
  rw [show (fun z ↦ v (S z)) = v ∘ S from rfl, h]
  calc _ ≤ ‖iteratedFDeriv ℝ 2 v (S x)‖ * ∏ _i : Fin 2, ‖(S : Space d →L[ℝ] Space d)‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ = _ := by simp

private theorem rpow_div_eq_aux {r a : ℝ} (hr : 0 < r) (ha : 0 < a) (s : ℝ) :
    (r / a) ^ s = a ^ (-s) * r ^ s := by
  rw [Real.div_rpow hr.le ha.le, Real.rpow_neg ha.le]
  ring

/-- Setup shared by the interior estimates: the harmonic function `w ∘ T` on a ball around
`T⁻¹ x` of radius `r / √Λ`. -/
private theorem aHarmonic_setup (hA : IsUniformlyElliptic A ν Λ) {U : Set (Space d)}
    (hU : IsOpen U) {w : Space d → ℝ} (hw : ContDiffOn ℝ 2 w U)
    (hLw : ∀ y ∈ U, aLaplacian A w y = 0) {x : Space d} {r : ℝ} (hxr : closedBall x r ⊆ U)
    (hr : 0 < r) :
    ∃ T : Space d ≃L[ℝ] Space d,
      (∀ u, ‖T u‖ ≤ Real.sqrt Λ * ‖u‖) ∧ (∀ u, Real.sqrt ν * ‖u‖ ≤ ‖T u‖) ∧
      ContDiffOn ℝ 2 (fun y ↦ w (T y)) (T ⁻¹' U) ∧
      (∀ y ∈ T ⁻¹' U, Δ (fun y ↦ w (T y)) y = 0) ∧
      closedBall (T.symm x) (r / Real.sqrt Λ) ⊆ T ⁻¹' U ∧
      ball (T.symm x) (r / Real.sqrt Λ) ⊆ T ⁻¹' ball x r := by
  obtain ⟨T, hT, hTu, hTl⟩ := hA.exists_sqrt
  have hΛ : 0 < Λ := hA.pos.trans_le hA.le
  have hsΛ : 0 < Real.sqrt Λ := Real.sqrt_pos.2 hΛ
  have hTy : ∀ y, ‖T y - x‖ ≤ Real.sqrt Λ * ‖y - T.symm x‖ := fun y ↦ by
    have h1 : T y - x = T (y - T.symm x) := by rw [map_sub, T.apply_symm_apply]
    rw [h1]
    exact hTu _
  have hρ : Real.sqrt Λ * (r / Real.sqrt Λ) = r := by field_simp
  refine ⟨T, hTu, hTl, hw.comp T.contDiff.contDiffOn (fun y hy ↦ hy), fun y hy ↦ ?_, ?_, ?_⟩
  · rw [laplacian_comp_eq_aLaplacian T hT (hw.contDiffAt (hU.mem_nhds hy))]
    exact hLw _ hy
  · intro y hy
    apply hxr
    rw [mem_closedBall, dist_eq_norm] at hy ⊢
    calc ‖T y - x‖ ≤ Real.sqrt Λ * ‖y - T.symm x‖ := hTy y
      _ ≤ Real.sqrt Λ * (r / Real.sqrt Λ) := by gcongr
      _ = r := hρ
  · intro y hy
    rw [mem_ball, dist_eq_norm] at hy
    rw [mem_preimage, mem_ball, dist_eq_norm]
    calc ‖T y - x‖ ≤ Real.sqrt Λ * ‖y - T.symm x‖ := hTy y
      _ < Real.sqrt Λ * (r / Real.sqrt Λ) := by gcongr
      _ = r := hρ

/-- The constant in the interior gradient estimate for `L_A`. -/
def aHarmonicGradConst (d : ℕ) (ν Λ : ℝ) : ℝ :=
  (Real.sqrt ν)⁻¹ * harmonicGradConst d * Real.sqrt Λ ^ ((1 : ℝ) + d / 2) *
    ((Real.sqrt ν ^ d)⁻¹) ^ (1 / 2 : ℝ)

/-- **Interior gradient estimate** for solutions of `L_A w = 0`. -/
theorem norm_fderiv_le_of_aHarmonic (hA : IsUniformlyElliptic A ν Λ) {U : Set (Space d)}
    (hU : IsOpen U) {w : Space d → ℝ} (hw : ContDiffOn ℝ 2 w U)
    (hLw : ∀ y ∈ U, aLaplacian A w y = 0) {x : Space d} {r : ℝ} (hxr : closedBall x r ⊆ U)
    (hr : 0 < r) :
    ‖fderiv ℝ w x‖ ≤ aHarmonicGradConst d ν Λ * r ^ (-(1 : ℝ) - d / 2) *
      (∫ y in ball x r, w y ^ 2) ^ (1 / 2 : ℝ) := by
  obtain ⟨T, hTu, hTl, hv, hΔv, hball, hball'⟩ := aHarmonic_setup hA hU hw hLw hxr hr
  have hν := hA.pos
  have hΛ : 0 < Λ := hν.trans_le hA.le
  have hsν : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have hsΛ : 0 < Real.sqrt Λ := Real.sqrt_pos.2 hΛ
  have hρ : 0 < r / Real.sqrt Λ := div_pos hr hsΛ
  have h1 := norm_fderiv_le_of_harmonic (hU.preimage T.continuous) hv hΔv hball hρ
  have hI : ∫ y in ball (T.symm x) (r / Real.sqrt Λ), w (T y) ^ 2 ≤
      (Real.sqrt ν ^ d)⁻¹ * ∫ y in ball x r, w y ^ 2 := by
    have h2 := setIntegral_comp_continuousLinearEquiv_le T (g := fun z ↦ w z ^ 2)
      measurableSet_ball (fun z ↦ sq_nonneg _)
      (((hw.continuousOn.mono hxr).pow 2).integrableOn_compact
        (isCompact_closedBall x r) |>.mono_set ball_subset_closedBall) hball'
    exact h2.trans (mul_le_mul_of_nonneg_right (abs_det_inv_le_of_le_norm hν hTl)
      (integral_nonneg fun _ ↦ sq_nonneg _))
  have hcomp : (fun y ↦ w (T y)) ∘ T.symm = w := by
    funext z
    simp
  have hDw : ‖fderiv ℝ w x‖ ≤ ‖fderiv ℝ (fun y ↦ w (T y)) (T.symm x)‖ * (Real.sqrt ν)⁻¹ := by
    have h2 := T.symm.comp_right_fderiv (f := fun y ↦ w (T y)) (x := x)
    rw [hcomp] at h2
    rw [h2]
    calc _ ≤ ‖fderiv ℝ (fun y ↦ w (T y)) (T.symm x)‖ *
          ‖(T.symm : Space d →L[ℝ] Space d)‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (norm_symm_le_aux hν hTl)
          (ContinuousLinearMap.opNorm_nonneg _)
  have hC0 : 0 ≤ harmonicGradConst d * (r / Real.sqrt Λ) ^ (-(1 : ℝ) - d / 2) :=
    mul_nonneg harmonicGradConst_nonneg (Real.rpow_nonneg hρ.le _)
  calc ‖fderiv ℝ w x‖
      ≤ ‖fderiv ℝ (fun y ↦ w (T y)) (T.symm x)‖ * (Real.sqrt ν)⁻¹ := hDw
    _ ≤ harmonicGradConst d * (r / Real.sqrt Λ) ^ (-(1 : ℝ) - d / 2) *
          (∫ y in ball (T.symm x) (r / Real.sqrt Λ), w (T y) ^ 2) ^ (1 / 2 : ℝ) *
            (Real.sqrt ν)⁻¹ := mul_le_mul_of_nonneg_right h1 (by positivity)
    _ ≤ harmonicGradConst d * (r / Real.sqrt Λ) ^ (-(1 : ℝ) - d / 2) *
          ((Real.sqrt ν ^ d)⁻¹ * ∫ y in ball x r, w y ^ 2) ^ (1 / 2 : ℝ) *
            (Real.sqrt ν)⁻¹ := by
        gcongr
    _ = aHarmonicGradConst d ν Λ * r ^ (-(1 : ℝ) - d / 2) *
          (∫ y in ball x r, w y ^ 2) ^ (1 / 2 : ℝ) := by
        rw [Real.mul_rpow (by positivity) (integral_nonneg fun _ ↦ sq_nonneg _),
          rpow_div_eq_aux hr hsΛ, show -(-(1 : ℝ) - d / 2) = 1 + d / 2 by ring]
        unfold aHarmonicGradConst
        ring

/-- The constant in the interior Hessian estimate in terms of the gradient, for `L_A`. -/
def aHarmonicHessGradConst (d : ℕ) (ν Λ : ℝ) : ℝ :=
  ((Real.sqrt ν)⁻¹) ^ 2 * harmonicGradConst d * Real.sqrt Λ ^ ((1 : ℝ) + d / 2) *
    (Λ * (Real.sqrt ν ^ d)⁻¹) ^ (1 / 2 : ℝ)

/-- **Interior Hessian estimate in terms of the gradient** for solutions of `L_A w = 0`. -/
theorem norm_iteratedFDeriv_two_le_of_aHarmonic_grad (hA : IsUniformlyElliptic A ν Λ)
    {U : Set (Space d)} (hU : IsOpen U) {w : Space d → ℝ} (hw : ContDiffOn ℝ 2 w U)
    (hLw : ∀ y ∈ U, aLaplacian A w y = 0) {x : Space d} {r : ℝ} (hxr : closedBall x r ⊆ U)
    (hr : 0 < r) :
    ‖iteratedFDeriv ℝ 2 w x‖ ≤ aHarmonicHessGradConst d ν Λ * r ^ (-(1 : ℝ) - d / 2) *
      (∫ y in ball x r, ‖fderiv ℝ w y‖ ^ 2) ^ (1 / 2 : ℝ) := by
  obtain ⟨T, hTu, hTl, hv, hΔv, hball, hball'⟩ := aHarmonic_setup hA hU hw hLw hxr hr
  have hν := hA.pos
  have hΛ : 0 < Λ := hν.trans_le hA.le
  have hsν : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have hsΛ : 0 < Real.sqrt Λ := Real.sqrt_pos.2 hΛ
  have hρ : 0 < r / Real.sqrt Λ := div_pos hr hsΛ
  have h1 := norm_iteratedFDeriv_two_le_of_harmonic_grad (hU.preimage T.continuous) hv hΔv
    hball hρ
  have hdfc : ContinuousOn (fderiv ℝ w) U := hw.continuousOn_fderiv_of_isOpen hU (by norm_num)
  have hdv : ∀ y, fderiv ℝ (fun y ↦ w (T y)) y = (fderiv ℝ w (T y)).comp
      (T : Space d →L[ℝ] Space d) := fun y ↦ T.comp_right_fderiv (f := w) (x := y)
  have hptv : ∀ y, ‖fderiv ℝ (fun y ↦ w (T y)) y‖ ^ 2 ≤ Λ * ‖fderiv ℝ w (T y)‖ ^ 2 := by
    intro y
    rw [hdv y]
    have h2 : ‖(fderiv ℝ w (T y)).comp (T : Space d →L[ℝ] Space d)‖ ≤
        ‖fderiv ℝ w (T y)‖ * Real.sqrt Λ :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (norm_coe_le_aux hTu) (norm_nonneg _))
    calc ‖(fderiv ℝ w (T y)).comp (T : Space d →L[ℝ] Space d)‖ ^ 2
        ≤ (‖fderiv ℝ w (T y)‖ * Real.sqrt Λ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
      _ = Λ * ‖fderiv ℝ w (T y)‖ ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hΛ.le]
          ring
  have hcl : closedBall (T.symm x) (r / Real.sqrt Λ) ⊆ T ⁻¹' U := hball
  have hJ : ∫ y in ball (T.symm x) (r / Real.sqrt Λ), ‖fderiv ℝ (fun y ↦ w (T y)) y‖ ^ 2 ≤
      Λ * ((Real.sqrt ν ^ d)⁻¹ * ∫ y in ball x r, ‖fderiv ℝ w y‖ ^ 2) := by
    have hdvc : ContinuousOn (fderiv ℝ (fun y ↦ w (T y))) (T ⁻¹' U) :=
      hv.continuousOn_fderiv_of_isOpen (hU.preimage T.continuous) (by norm_num)
    have hi1 : IntegrableOn (fun y ↦ ‖fderiv ℝ (fun y ↦ w (T y)) y‖ ^ 2)
        (ball (T.symm x) (r / Real.sqrt Λ)) :=
      ((hdvc.norm.pow 2).mono hcl |>.integrableOn_compact (isCompact_closedBall _ _)).mono_set
        ball_subset_closedBall
    have hi2 : IntegrableOn (fun y ↦ Λ * ‖fderiv ℝ w (T y)‖ ^ 2)
        (ball (T.symm x) (r / Real.sqrt Λ)) := by
      have hc : ContinuousOn (fun y ↦ Λ * ‖fderiv ℝ w (T y)‖ ^ 2) (T ⁻¹' U) :=
        continuousOn_const.mul
          ((hdfc.comp T.continuous.continuousOn (fun y hy ↦ hy)).norm.pow 2)
      exact (hc.mono hcl |>.integrableOn_compact (isCompact_closedBall _ _)).mono_set
        ball_subset_closedBall
    have h3 := setIntegral_comp_continuousLinearEquiv_le T (g := fun z ↦ ‖fderiv ℝ w z‖ ^ 2)
      measurableSet_ball (fun z ↦ sq_nonneg _)
      (((hdfc.mono hxr).norm.pow 2).integrableOn_compact
        (isCompact_closedBall x r) |>.mono_set ball_subset_closedBall) hball'
    calc ∫ y in ball (T.symm x) (r / Real.sqrt Λ), ‖fderiv ℝ (fun y ↦ w (T y)) y‖ ^ 2
        ≤ ∫ y in ball (T.symm x) (r / Real.sqrt Λ), Λ * ‖fderiv ℝ w (T y)‖ ^ 2 :=
          setIntegral_mono_on hi1 hi2 measurableSet_ball fun y _ ↦ hptv y
      _ = Λ * ∫ y in ball (T.symm x) (r / Real.sqrt Λ), ‖fderiv ℝ w (T y)‖ ^ 2 :=
          integral_const_mul _ _
      _ ≤ Λ * ((Real.sqrt ν ^ d)⁻¹ * ∫ y in ball x r, ‖fderiv ℝ w y‖ ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ hΛ.le
          exact h3.trans (mul_le_mul_of_nonneg_right (abs_det_inv_le_of_le_norm hν hTl)
            (integral_nonneg fun _ ↦ sq_nonneg _))
  have hcomp : (fun z ↦ w (T (T.symm z))) = w := by
    funext z
    simp
  have hD2 : ‖iteratedFDeriv ℝ 2 w x‖ ≤
      ‖iteratedFDeriv ℝ 2 (fun y ↦ w (T y)) (T.symm x)‖ * ((Real.sqrt ν)⁻¹) ^ 2 := by
    have h2 := norm_iteratedFDeriv_two_comp_le_aux (fun y ↦ w (T y)) T.symm x
    rw [hcomp] at h2
    refine h2.trans ?_
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (ContinuousLinearMap.opNorm_nonneg _)
      (norm_symm_le_aux hν hTl) 2) (norm_nonneg _)
  have hJ0 : 0 ≤ ∫ y in ball x r, ‖fderiv ℝ w y‖ ^ 2 := integral_nonneg fun _ ↦ sq_nonneg _
  calc ‖iteratedFDeriv ℝ 2 w x‖
      ≤ ‖iteratedFDeriv ℝ 2 (fun y ↦ w (T y)) (T.symm x)‖ * ((Real.sqrt ν)⁻¹) ^ 2 := hD2
    _ ≤ harmonicGradConst d * (r / Real.sqrt Λ) ^ (-(1 : ℝ) - d / 2) *
          (∫ y in ball (T.symm x) (r / Real.sqrt Λ),
            ‖fderiv ℝ (fun y ↦ w (T y)) y‖ ^ 2) ^ (1 / 2 : ℝ) * ((Real.sqrt ν)⁻¹) ^ 2 :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ ≤ harmonicGradConst d * (r / Real.sqrt Λ) ^ (-(1 : ℝ) - d / 2) *
          (Λ * ((Real.sqrt ν ^ d)⁻¹ * ∫ y in ball x r, ‖fderiv ℝ w y‖ ^ 2)) ^ (1 / 2 : ℝ) *
            ((Real.sqrt ν)⁻¹) ^ 2 := by
        have hC0 : 0 ≤ harmonicGradConst d * (r / Real.sqrt Λ) ^ (-(1 : ℝ) - d / 2) :=
          mul_nonneg harmonicGradConst_nonneg (Real.rpow_nonneg hρ.le _)
        gcongr
    _ = aHarmonicHessGradConst d ν Λ * r ^ (-(1 : ℝ) - d / 2) *
          (∫ y in ball x r, ‖fderiv ℝ w y‖ ^ 2) ^ (1 / 2 : ℝ) := by
        rw [← mul_assoc Λ, Real.mul_rpow (by positivity) hJ0, rpow_div_eq_aux hr hsΛ,
          show -(-(1 : ℝ) - d / 2) = 1 + d / 2 by ring]
        unfold aHarmonicHessGradConst
        ring


theorem aHarmonicGradConst_nonneg (d : ℕ) (ν Λ : ℝ) : 0 ≤ aHarmonicGradConst d ν Λ := by
  unfold aHarmonicGradConst
  have h1 := harmonicGradConst_nonneg (d := d)
  positivity

theorem aHarmonicHessGradConst_nonneg (hA : IsUniformlyElliptic A ν Λ) :
    0 ≤ aHarmonicHessGradConst d ν Λ := by
  unfold aHarmonicHessGradConst
  have hΛ : 0 ≤ Λ := (hA.pos.trans_le hA.le).le
  have h1 := harmonicGradConst_nonneg (d := d)
  positivity

private theorem norm_iteratedFDeriv_two_eq_aux (h : Space d → ℝ) (x : Space d) :
    ‖iteratedFDeriv ℝ 2 h x‖ = ‖fderiv ℝ (fderiv ℝ h) x‖ := by
  rw [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one]

/-- Gradient excess on a small ball from a Hessian bound on the half ball (mean value
inequality). -/
private theorem fderiv_excess_le_of_hessian_bound {U : Set (Space d)} (hU : IsOpen U)
    {w : Space d → ℝ} (hw : ContDiffOn ℝ 2 w U) {x : Space d} {r : ℝ}
    (hxr : closedBall x r ⊆ U) (hr : 0 < r) {M : ℝ}
    (hM : ∀ z ∈ closedBall x (r / 2), ‖fderiv ℝ (fderiv ℝ w) z‖ ≤ M) {θ : ℝ} (hθ0 : 0 < θ)
    (hθ : θ ≤ 1 / 2) :
    ∫ y in ball x (θ * r), ‖fderiv ℝ w y - fderiv ℝ w x‖ ^ 2 ≤
      (θ * r) ^ d * volume.real (ball (0 : Space d) 1) * (M * (θ * r)) ^ 2 := by
  have hθr : 0 < θ * r := mul_pos hθ0 hr
  have hθr2 : θ * r ≤ r / 2 := by nlinarith
  have hhalf : closedBall x (r / 2) ⊆ U :=
    (closedBall_subset_closedBall (by linarith)).trans hxr
  have hM0 : 0 ≤ M := (ContinuousLinearMap.opNorm_nonneg _).trans
    (hM x (mem_closedBall_self (by linarith)))
  have hdiff : ∀ z ∈ closedBall x (r / 2), HasFDerivWithinAt (fderiv ℝ w)
      (fderiv ℝ (fderiv ℝ w) z) (closedBall x (r / 2)) z := by
    intro z hz
    have hzU := hhalf hz
    have hd : DifferentiableAt ℝ (fderiv ℝ w) z :=
      ((hw.fderiv_of_isOpen hU (m := 1) (by norm_num)).differentiableOn (by norm_num) z
        hzU).differentiableAt (hU.mem_nhds hzU)
    exact hd.hasFDerivAt.hasFDerivWithinAt
  have hpt : ∀ y ∈ ball x (θ * r), ‖fderiv ℝ w y - fderiv ℝ w x‖ ^ 2 ≤ (M * (θ * r)) ^ 2 := by
    intro y hy
    have hyc : y ∈ closedBall x (r / 2) :=
      closedBall_subset_closedBall hθr2 (ball_subset_closedBall hy)
    have hmvt := (convex_closedBall x (r / 2)).norm_image_sub_le_of_norm_hasFDerivWithin_le
      hdiff hM (mem_closedBall_self (by linarith)) hyc
    have hyx : ‖y - x‖ ≤ θ * r := by
      rw [← dist_eq_norm]
      exact (mem_ball.1 hy).le
    exact pow_le_pow_left₀ (norm_nonneg _)
      (hmvt.trans (mul_le_mul_of_nonneg_left hyx hM0)) 2
  have hint : IntegrableOn (fun y ↦ ‖fderiv ℝ w y - fderiv ℝ w x‖ ^ 2) (ball x (θ * r)) := by
    have hc : ContinuousOn (fun y ↦ ‖fderiv ℝ w y - fderiv ℝ w x‖ ^ 2) U :=
      ((hw.continuousOn_fderiv_of_isOpen hU (by norm_num)).sub continuousOn_const).norm.pow 2
    exact ((hc.mono ((closedBall_subset_closedBall hθr2).trans hhalf)).integrableOn_compact
      (isCompact_closedBall _ _)).mono_set ball_subset_closedBall
  calc ∫ y in ball x (θ * r), ‖fderiv ℝ w y - fderiv ℝ w x‖ ^ 2
      ≤ ∫ y in ball x (θ * r), (M * (θ * r)) ^ 2 :=
        setIntegral_mono_on hint (integrableOn_const (C := (M * (θ * r)) ^ 2)
          measure_ball_lt_top.ne) measurableSet_ball hpt
    _ = _ := by
        rw [setIntegral_const, smul_eq_mul, volume_real_ball_aux x hθr]

private theorem rpow_sq_aux {a : ℝ} (ha : 0 < a) :
    (a ^ (-(1 : ℝ) - d / 2)) ^ 2 = (a ^ (d + 2))⁻¹ := by
  rw [← Real.rpow_natCast (a ^ _) 2, ← Real.rpow_mul ha.le, ← Real.rpow_natCast a (d + 2),
    ← Real.rpow_neg ha.le]
  congr 1
  push_cast
  ring

private theorem rpow_half_sq_aux {J : ℝ} (hJ : 0 ≤ J) : (J ^ (1 / 2 : ℝ)) ^ 2 = J := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hJ]
  norm_num

private theorem excess_algebra_aux {r : ℝ} (hr : 0 < r) (θ V C J : ℝ) :
    (θ * r) ^ d * V * (C ^ 2 * ((r / 2) ^ (d + 2))⁻¹ * J * (θ * r) ^ 2) =
      V * C ^ 2 * 2 ^ (d + 2) * θ ^ (d + 2) * J := by
  obtain ⟨ρ, rfl⟩ : ∃ ρ, r = 2 * ρ := ⟨r / 2, by ring⟩
  have hρ : 0 < ρ := by linarith
  rw [show 2 * ρ / 2 = ρ by ring]
  field_simp
  ring

private theorem closedBall_half_subset_aux {x z : Space d} {r : ℝ}
    (hz : z ∈ closedBall x (r / 2)) : closedBall z (r / 2) ⊆ closedBall x r := by
  intro y hy
  rw [mem_closedBall] at hy hz ⊢
  linarith [dist_triangle y z x]

private theorem ball_half_subset_aux {x z : Space d} {r : ℝ}
    (hz : z ∈ closedBall x (r / 2)) : ball z (r / 2) ⊆ ball x r := by
  intro y hy
  rw [mem_ball] at hy ⊢
  rw [mem_closedBall] at hz
  linarith [dist_triangle y z x]

/-- The constant in the gradient excess decay estimate for `L_A`. -/
def aHarmonicGradExcessConst (d : ℕ) (ν Λ : ℝ) : ℝ :=
  volume.real (ball (0 : Space d) 1) * aHarmonicHessGradConst d ν Λ ^ 2 * 2 ^ (d + 2)

/-- **Gradient excess decay** for solutions of `L_A w = 0`:
`∫_{B(x, θ r)} ‖∇w - ∇w(x)‖² ≤ C θ^{d+2} ∫_{B(x, r)} ‖∇w‖²` for `0 < θ ≤ 1/2`. -/
theorem aHarmonic_fderiv_excess_le (hA : IsUniformlyElliptic A ν Λ) {U : Set (Space d)}
    (hU : IsOpen U) {w : Space d → ℝ} (hw : ContDiffOn ℝ 2 w U)
    (hLw : ∀ y ∈ U, aLaplacian A w y = 0) {x : Space d} {r : ℝ} (hxr : closedBall x r ⊆ U)
    (hr : 0 < r) {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ ≤ 1 / 2) :
    ∫ y in ball x (θ * r), ‖fderiv ℝ w y - fderiv ℝ w x‖ ^ 2 ≤
      aHarmonicGradExcessConst d ν Λ * θ ^ (d + 2) * ∫ y in ball x r, ‖fderiv ℝ w y‖ ^ 2 := by
  have hC0 : 0 ≤ aHarmonicHessGradConst d ν Λ := aHarmonicHessGradConst_nonneg hA
  have hJ0 : 0 ≤ ∫ y in ball x r, ‖fderiv ℝ w y‖ ^ 2 := integral_nonneg fun _ ↦ sq_nonneg _
  have hs0 : 0 < r / 2 := half_pos hr
  have hdfc : ContinuousOn (fderiv ℝ w) U := hw.continuousOn_fderiv_of_isOpen hU (by norm_num)
  have hpos : 0 ≤ aHarmonicHessGradConst d ν Λ * (r / 2) ^ (-(1 : ℝ) - d / 2) :=
    mul_nonneg hC0 (Real.rpow_nonneg hs0.le _)
  have hbound : ∀ z ∈ closedBall x (r / 2), ‖fderiv ℝ (fderiv ℝ w) z‖ ≤
      aHarmonicHessGradConst d ν Λ * (r / 2) ^ (-(1 : ℝ) - d / 2) *
        (∫ y in ball x r, ‖fderiv ℝ w y‖ ^ 2) ^ (1 / 2 : ℝ) := by
    intro z hz
    have hzsub := closedBall_half_subset_aux hz
    have h1 := norm_iteratedFDeriv_two_le_of_aHarmonic_grad hA hU hw hLw (hzsub.trans hxr) hs0
    rw [norm_iteratedFDeriv_two_eq_aux] at h1
    have hmono : ∫ y in ball z (r / 2), ‖fderiv ℝ w y‖ ^ 2 ≤
        ∫ y in ball x r, ‖fderiv ℝ w y‖ ^ 2 :=
      setIntegral_mono_set (((hdfc.mono hxr).norm.pow 2).integrableOn_compact
        (isCompact_closedBall x r) |>.mono_set ball_subset_closedBall)
        (Eventually.of_forall fun y ↦ sq_nonneg _) (ball_half_subset_aux hz).eventuallyLE
    exact h1.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow
      (integral_nonneg fun _ ↦ sq_nonneg _) hmono (by norm_num)) hpos)
  have hexc := fderiv_excess_le_of_hessian_bound hU hw hxr hr hbound hθ0 hθ
  refine hexc.trans (le_of_eq ?_)
  have hM2 : (aHarmonicHessGradConst d ν Λ * (r / 2) ^ (-(1 : ℝ) - d / 2) *
      (∫ y in ball x r, ‖fderiv ℝ w y‖ ^ 2) ^ (1 / 2 : ℝ) * (θ * r)) ^ 2 =
      aHarmonicHessGradConst d ν Λ ^ 2 * ((r / 2) ^ (-(1 : ℝ) - d / 2)) ^ 2 *
        ((∫ y in ball x r, ‖fderiv ℝ w y‖ ^ 2) ^ (1 / 2 : ℝ)) ^ 2 * (θ * r) ^ 2 := by
    ring
  rw [hM2, rpow_sq_aux hs0, rpow_half_sq_aux hJ0]
  have halg := excess_algebra_aux (d := d) hr θ (volume.real (ball (0 : Space d) 1))
    (aHarmonicHessGradConst d ν Λ) (∫ y in ball x r, ‖fderiv ℝ w y‖ ^ 2)
  unfold aHarmonicGradExcessConst
  rw [← halg]


/-- The constant in the interior Hessian estimate for `L_A`. -/
def aHarmonicHessConst (d : ℕ) (ν Λ : ℝ) : ℝ :=
  ((Real.sqrt ν)⁻¹) ^ 2 * harmonicHessConst d * Real.sqrt Λ ^ ((2 : ℝ) + d / 2) *
    ((Real.sqrt ν ^ d)⁻¹) ^ (1 / 2 : ℝ)

theorem aHarmonicHessConst_nonneg (d : ℕ) (ν Λ : ℝ) : 0 ≤ aHarmonicHessConst d ν Λ := by
  unfold aHarmonicHessConst
  have h1 := harmonicHessConst_nonneg (d := d)
  positivity

/-- **Interior Hessian estimate** for solutions of `L_A w = 0`. -/
theorem norm_iteratedFDeriv_two_le_of_aHarmonic (hA : IsUniformlyElliptic A ν Λ)
    {U : Set (Space d)} (hU : IsOpen U) {w : Space d → ℝ} (hw : ContDiffOn ℝ 2 w U)
    (hLw : ∀ y ∈ U, aLaplacian A w y = 0) {x : Space d} {r : ℝ} (hxr : closedBall x r ⊆ U)
    (hr : 0 < r) :
    ‖iteratedFDeriv ℝ 2 w x‖ ≤ aHarmonicHessConst d ν Λ * r ^ (-(2 : ℝ) - d / 2) *
      (∫ y in ball x r, w y ^ 2) ^ (1 / 2 : ℝ) := by
  obtain ⟨T, hTu, hTl, hv, hΔv, hball, hball'⟩ := aHarmonic_setup hA hU hw hLw hxr hr
  have hν := hA.pos
  have hΛ : 0 < Λ := hν.trans_le hA.le
  have hsν : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have hsΛ : 0 < Real.sqrt Λ := Real.sqrt_pos.2 hΛ
  have hρ : 0 < r / Real.sqrt Λ := div_pos hr hsΛ
  have h1 := norm_iteratedFDeriv_two_le_of_harmonic (hU.preimage T.continuous) hv hΔv hball hρ
  have hI : ∫ y in ball (T.symm x) (r / Real.sqrt Λ), w (T y) ^ 2 ≤
      (Real.sqrt ν ^ d)⁻¹ * ∫ y in ball x r, w y ^ 2 := by
    have h2 := setIntegral_comp_continuousLinearEquiv_le T (g := fun z ↦ w z ^ 2)
      measurableSet_ball (fun z ↦ sq_nonneg _)
      (((hw.continuousOn.mono hxr).pow 2).integrableOn_compact
        (isCompact_closedBall x r) |>.mono_set ball_subset_closedBall) hball'
    exact h2.trans (mul_le_mul_of_nonneg_right (abs_det_inv_le_of_le_norm hν hTl)
      (integral_nonneg fun _ ↦ sq_nonneg _))
  have hcomp : (fun z ↦ w (T (T.symm z))) = w := by
    funext z
    simp
  have hD2 : ‖iteratedFDeriv ℝ 2 w x‖ ≤
      ‖iteratedFDeriv ℝ 2 (fun y ↦ w (T y)) (T.symm x)‖ * ((Real.sqrt ν)⁻¹) ^ 2 := by
    have h2 := norm_iteratedFDeriv_two_comp_le_aux (fun y ↦ w (T y)) T.symm x
    rw [hcomp] at h2
    refine h2.trans ?_
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (ContinuousLinearMap.opNorm_nonneg _)
      (norm_symm_le_aux hν hTl) 2) (norm_nonneg _)
  have hI0 : 0 ≤ ∫ y in ball x r, w y ^ 2 := integral_nonneg fun _ ↦ sq_nonneg _
  calc ‖iteratedFDeriv ℝ 2 w x‖
      ≤ ‖iteratedFDeriv ℝ 2 (fun y ↦ w (T y)) (T.symm x)‖ * ((Real.sqrt ν)⁻¹) ^ 2 := hD2
    _ ≤ harmonicHessConst d * (r / Real.sqrt Λ) ^ (-(2 : ℝ) - d / 2) *
          (∫ y in ball (T.symm x) (r / Real.sqrt Λ), w (T y) ^ 2) ^ (1 / 2 : ℝ) *
            ((Real.sqrt ν)⁻¹) ^ 2 := mul_le_mul_of_nonneg_right h1 (by positivity)
    _ ≤ harmonicHessConst d * (r / Real.sqrt Λ) ^ (-(2 : ℝ) - d / 2) *
          ((Real.sqrt ν ^ d)⁻¹ * ∫ y in ball x r, w y ^ 2) ^ (1 / 2 : ℝ) *
            ((Real.sqrt ν)⁻¹) ^ 2 := by
        have hC0 : 0 ≤ harmonicHessConst d * (r / Real.sqrt Λ) ^ (-(2 : ℝ) - d / 2) :=
          mul_nonneg harmonicHessConst_nonneg (Real.rpow_nonneg hρ.le _)
        gcongr
    _ = aHarmonicHessConst d ν Λ * r ^ (-(2 : ℝ) - d / 2) *
          (∫ y in ball x r, w y ^ 2) ^ (1 / 2 : ℝ) := by
        rw [Real.mul_rpow (by positivity) hI0, rpow_div_eq_aux hr hsΛ,
          show -(-(2 : ℝ) - d / 2) = 2 + d / 2 by ring]
        unfold aHarmonicHessConst
        ring

/-- First-order Taylor excess on a small ball from a Hessian bound on the half ball. -/
private theorem taylor_excess_le_of_hessian_bound {U : Set (Space d)} (hU : IsOpen U)
    {w : Space d → ℝ} (hw : ContDiffOn ℝ 2 w U) {x : Space d} {r : ℝ}
    (hxr : closedBall x r ⊆ U) (hr : 0 < r) {M : ℝ}
    (hM : ∀ z ∈ closedBall x (r / 2), ‖fderiv ℝ (fderiv ℝ w) z‖ ≤ M) {θ : ℝ} (hθ0 : 0 < θ)
    (hθ : θ ≤ 1 / 2) :
    ∫ y in ball x (θ * r), (w y - w x - fderiv ℝ w x (y - x)) ^ 2 ≤
      (θ * r) ^ d * volume.real (ball (0 : Space d) 1) * (M * (θ * r) ^ 2) ^ 2 := by
  have hθr : 0 < θ * r := mul_pos hθ0 hr
  have hθr2 : θ * r ≤ r / 2 := by nlinarith
  have hhalf : closedBall x (r / 2) ⊆ U :=
    (closedBall_subset_closedBall (by linarith)).trans hxr
  have hsmall : closedBall x (θ * r) ⊆ U := (closedBall_subset_closedBall hθr2).trans hhalf
  have hM0 : 0 ≤ M := (ContinuousLinearMap.opNorm_nonneg _).trans
    (hM x (mem_closedBall_self (by linarith)))
  have hdiff : ∀ z ∈ closedBall x (r / 2), HasFDerivWithinAt (fderiv ℝ w)
      (fderiv ℝ (fderiv ℝ w) z) (closedBall x (r / 2)) z := by
    intro z hz
    have hzU := hhalf hz
    have hd : DifferentiableAt ℝ (fderiv ℝ w) z :=
      ((hw.fderiv_of_isOpen hU (m := 1) (by norm_num)).differentiableOn (by norm_num) z
        hzU).differentiableAt (hU.mem_nhds hzU)
    exact hd.hasFDerivAt.hasFDerivWithinAt
  have hgrad : ∀ z ∈ closedBall x (θ * r), ‖fderiv ℝ w z - fderiv ℝ w x‖ ≤ M * (θ * r) := by
    intro z hz
    have hzc : z ∈ closedBall x (r / 2) := closedBall_subset_closedBall hθr2 hz
    have hmvt := (convex_closedBall x (r / 2)).norm_image_sub_le_of_norm_hasFDerivWithin_le
      hdiff hM (mem_closedBall_self (by linarith)) hzc
    have hzx : ‖z - x‖ ≤ θ * r := by
      rw [← dist_eq_norm]
      exact mem_closedBall.1 hz
    exact hmvt.trans (mul_le_mul_of_nonneg_left hzx hM0)
  let g : Space d → ℝ := fun y ↦ w y - w x - fderiv ℝ w x (y - x)
  have hgd : ∀ z ∈ closedBall x (θ * r),
      HasFDerivWithinAt g (fderiv ℝ w z - fderiv ℝ w x) (closedBall x (θ * r)) z := by
    intro z hz
    have hzU := hsmall hz
    have hdh : HasFDerivAt w (fderiv ℝ w z) z :=
      ((hw.differentiableOn (by norm_num) z hzU).differentiableAt
        (hU.mem_nhds hzU)).hasFDerivAt
    have hlin : HasFDerivAt (fun y ↦ fderiv ℝ w x (y - x)) (fderiv ℝ w x) z := by
      have h1 := (fderiv ℝ w x).hasFDerivAt.comp z ((hasFDerivAt_id (𝕜 := ℝ) z).sub_const x)
      rwa [ContinuousLinearMap.comp_id] at h1
    exact ((hdh.sub_const (w x)).sub hlin).hasFDerivWithinAt
  have hpt : ∀ y ∈ ball x (θ * r), (w y - w x - fderiv ℝ w x (y - x)) ^ 2 ≤
      (M * (θ * r) ^ 2) ^ 2 := by
    intro y hy
    have hyc : y ∈ closedBall x (θ * r) := ball_subset_closedBall hy
    have hmvt := (convex_closedBall x (θ * r)).norm_image_sub_le_of_norm_hasFDerivWithin_le
      hgd hgrad (mem_closedBall_self hθr.le) hyc
    have hgx : g x = 0 := by simp [g]
    rw [hgx, sub_zero, Real.norm_eq_abs] at hmvt
    have hyx : ‖y - x‖ ≤ θ * r := by
      rw [← dist_eq_norm]
      exact (mem_ball.1 hy).le
    have hgy : |g y| ≤ M * (θ * r) ^ 2 := by
      calc |g y| ≤ M * (θ * r) * ‖y - x‖ := hmvt
        _ ≤ M * (θ * r) * (θ * r) := mul_le_mul_of_nonneg_left hyx (by positivity)
        _ = M * (θ * r) ^ 2 := by ring
    calc (w y - w x - fderiv ℝ w x (y - x)) ^ 2 = |g y| ^ 2 := (sq_abs _).symm
      _ ≤ (M * (θ * r) ^ 2) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hgy 2
  have hint : IntegrableOn (fun y ↦ (w y - w x - fderiv ℝ w x (y - x)) ^ 2) (ball x (θ * r)) := by
    have hc : ContinuousOn (fun y ↦ (w y - w x - fderiv ℝ w x (y - x)) ^ 2) U :=
      ((hw.continuousOn.sub continuousOn_const).sub
        ((fderiv ℝ w x).continuous.comp (continuous_id.sub continuous_const)).continuousOn).pow 2
    exact ((hc.mono hsmall).integrableOn_compact (isCompact_closedBall _ _)).mono_set
      ball_subset_closedBall
  calc ∫ y in ball x (θ * r), (w y - w x - fderiv ℝ w x (y - x)) ^ 2
      ≤ ∫ y in ball x (θ * r), (M * (θ * r) ^ 2) ^ 2 :=
        setIntegral_mono_on hint (integrableOn_const (C := (M * (θ * r) ^ 2) ^ 2)
          measure_ball_lt_top.ne) measurableSet_ball hpt
    _ = _ := by
        rw [setIntegral_const, smul_eq_mul, volume_real_ball_aux x hθr]

private theorem rpow_sq_two_aux {a : ℝ} (ha : 0 < a) :
    (a ^ (-(2 : ℝ) - d / 2)) ^ 2 = (a ^ (d + 4))⁻¹ := by
  rw [← Real.rpow_natCast (a ^ _) 2, ← Real.rpow_mul ha.le, ← Real.rpow_natCast a (d + 4),
    ← Real.rpow_neg ha.le]
  congr 1
  push_cast
  ring

private theorem taylor_algebra_aux {r : ℝ} (hr : 0 < r) (θ V C I : ℝ) :
    (θ * r) ^ d * V * (C ^ 2 * ((r / 2) ^ (d + 4))⁻¹ * I * ((θ * r) ^ 2) ^ 2) =
      V * C ^ 2 * 2 ^ (d + 4) * θ ^ (d + 4) * I := by
  obtain ⟨ρ, rfl⟩ : ∃ ρ, r = 2 * ρ := ⟨r / 2, by ring⟩
  have hρ : 0 < ρ := by linarith
  rw [show 2 * ρ / 2 = ρ by ring]
  field_simp
  ring

/-- The constant in the first-order Taylor excess decay estimate for `L_A`. -/
def aHarmonicTaylorExcessConst (d : ℕ) (ν Λ : ℝ) : ℝ :=
  volume.real (ball (0 : Space d) 1) * aHarmonicHessConst d ν Λ ^ 2 * 2 ^ (d + 4)

/-- **First-order Taylor excess decay** for solutions of `L_A w = 0`:
`∫_{B(x, θ r)} (w - w(x) - ∇w(x)·(y - x))² ≤ C θ^{d+4} ∫_{B(x, r)} w²` for `0 < θ ≤ 1/2`. -/
theorem aHarmonic_taylor_excess_le (hA : IsUniformlyElliptic A ν Λ) {U : Set (Space d)}
    (hU : IsOpen U) {w : Space d → ℝ} (hw : ContDiffOn ℝ 2 w U)
    (hLw : ∀ y ∈ U, aLaplacian A w y = 0) {x : Space d} {r : ℝ} (hxr : closedBall x r ⊆ U)
    (hr : 0 < r) {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ ≤ 1 / 2) :
    ∫ y in ball x (θ * r), (w y - w x - fderiv ℝ w x (y - x)) ^ 2 ≤
      aHarmonicTaylorExcessConst d ν Λ * θ ^ (d + 4) * ∫ y in ball x r, w y ^ 2 := by
  have hC0 : 0 ≤ aHarmonicHessConst d ν Λ := aHarmonicHessConst_nonneg d ν Λ
  have hI0 : 0 ≤ ∫ y in ball x r, w y ^ 2 := integral_nonneg fun _ ↦ sq_nonneg _
  have hs0 : 0 < r / 2 := half_pos hr
  have hpos : 0 ≤ aHarmonicHessConst d ν Λ * (r / 2) ^ (-(2 : ℝ) - d / 2) :=
    mul_nonneg hC0 (Real.rpow_nonneg hs0.le _)
  have hbound : ∀ z ∈ closedBall x (r / 2), ‖fderiv ℝ (fderiv ℝ w) z‖ ≤
      aHarmonicHessConst d ν Λ * (r / 2) ^ (-(2 : ℝ) - d / 2) *
        (∫ y in ball x r, w y ^ 2) ^ (1 / 2 : ℝ) := by
    intro z hz
    have hzsub := closedBall_half_subset_aux hz
    have h1 := norm_iteratedFDeriv_two_le_of_aHarmonic hA hU hw hLw (hzsub.trans hxr) hs0
    rw [norm_iteratedFDeriv_two_eq_aux] at h1
    have hmono : ∫ y in ball z (r / 2), w y ^ 2 ≤ ∫ y in ball x r, w y ^ 2 :=
      setIntegral_mono_set (((hw.continuousOn.mono hxr).pow 2).integrableOn_compact
        (isCompact_closedBall x r) |>.mono_set ball_subset_closedBall)
        (Eventually.of_forall fun y ↦ sq_nonneg _) (ball_half_subset_aux hz).eventuallyLE
    exact h1.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow
      (integral_nonneg fun _ ↦ sq_nonneg _) hmono (by norm_num)) hpos)
  have hexc := taylor_excess_le_of_hessian_bound hU hw hxr hr hbound hθ0 hθ
  refine hexc.trans (le_of_eq ?_)
  have hM2 : (aHarmonicHessConst d ν Λ * (r / 2) ^ (-(2 : ℝ) - d / 2) *
      (∫ y in ball x r, w y ^ 2) ^ (1 / 2 : ℝ) * (θ * r) ^ 2) ^ 2 =
      aHarmonicHessConst d ν Λ ^ 2 * ((r / 2) ^ (-(2 : ℝ) - d / 2)) ^ 2 *
        ((∫ y in ball x r, w y ^ 2) ^ (1 / 2 : ℝ)) ^ 2 * ((θ * r) ^ 2) ^ 2 := by
    ring
  rw [hM2, rpow_sq_two_aux hs0, rpow_half_sq_aux hI0]
  have halg := taylor_algebra_aux (d := d) hr θ (volume.real (ball (0 : Space d) 1))
    (aHarmonicHessConst d ν Λ) (∫ y in ball x r, w y ^ 2)
  unfold aHarmonicTaylorExcessConst
  rw [← halg]

end Estimates

end SerrinEpigraph
