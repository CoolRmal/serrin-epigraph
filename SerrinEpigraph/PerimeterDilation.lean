module

public import SerrinEpigraph.HarmonicApproximation

/-!
# Perimeter representations under dilations and similarities

* `fieldDivergence_comp_smul`: `div (F (c ·)) = c (div F)(c ·)`.
* `IsPerimeterRepresentation.preimage_smul`: if `(μ, ν)` represents the perimeter of `E` on `W`,
  then `(θ^{1-d} (θ⁻¹ ·)_# μ, ν (θ ·))` represents the perimeter of `θ⁻¹ E` on `θ⁻¹ W`.
* `similarity Q c θ x = c + θ Q x`; `IsPerimeterRepresentation.preimage_similarity`,
  `IsLocalPerimeterMinimizer.preimage_similarity`,
  `measureTheoreticBoundary_preimage_similarity`.
* `integral_similarityMeasure`: integrals against the transported measure, used to transport the
  projected excess.
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory InnerProductSpace Filter
open scoped Topology ENNReal NNReal CompactlySupported

namespace SerrinEpigraph

/-- Divergence of a field precomposed with a dilation. -/
theorem fieldDivergence_comp_smul {d : ℕ} (b : OrthonormalBasis (Fin d) ℝ (Space d))
    {F : Space d → Space d} (hF : Differentiable ℝ F) (c : ℝ) (y : Space d) :
    fieldDivergence b (fun z ↦ F (c • z)) y = c * fieldDivergence b F (c • y) := by
  have h1 : HasFDerivAt (fun z : Space d ↦ c • z) (c • ContinuousLinearMap.id ℝ (Space d)) y :=
    (c • ContinuousLinearMap.id ℝ (Space d)).hasFDerivAt
  have hd : fderiv ℝ (fun z ↦ F (c • z)) y =
      (fderiv ℝ F (c • y)).comp (c • ContinuousLinearMap.id ℝ (Space d)) :=
    ((hF _).hasFDerivAt.comp y h1).fderiv
  unfold fieldDivergence
  rw [hd, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [ContinuousLinearMap.comp_apply]
  simp only [FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.id_apply, map_smul,
    real_inner_smul_right]

theorem measurableEmbedding_smul_inv {d : ℕ} {θ : ℝ} (hθ : θ ≠ 0) :
    MeasurableEmbedding (fun y : Space d ↦ θ⁻¹ • y) := by
  have h := (Homeomorph.smulOfNeZero θ⁻¹ (inv_ne_zero hθ) : Space d ≃ₜ Space d).measurableEmbedding
  rwa [Homeomorph.smulOfNeZero_apply] at h

/-- **Transport of perimeter representations by dilations.** -/
theorem IsPerimeterRepresentation.preimage_smul {d : ℕ} (hd : 1 ≤ d)
    {b : OrthonormalBasis (Fin d) ℝ (Space d)} {E W : Set (Space d)} {μ : Measure (Space d)}
    {ν : Space d → Space d} (h : IsPerimeterRepresentation b E W μ ν) {θ : ℝ} (hθ : 0 < θ) :
    IsPerimeterRepresentation b ((fun x ↦ θ • x) ⁻¹' E) ((fun x ↦ θ • x) ⁻¹' W)
      (Real.toNNReal ((θ ^ (d - 1))⁻¹) • μ.map (fun y ↦ θ⁻¹ • y)) (fun x ↦ ν (θ • x)) := by
  have := h.isFiniteMeasure
  have hSe : MeasurableEmbedding (fun y : Space d ↦ θ⁻¹ • y) := measurableEmbedding_smul_inv hθ.ne'
  set κ : ℝ≥0 := Real.toNNReal ((θ ^ (d - 1))⁻¹) with hκ_def
  have hθd : 0 < θ ^ (d - 1) := pow_pos hθ _
  have hκ : (κ : ℝ) = (θ ^ (d - 1))⁻¹ := Real.coe_toNNReal _ (inv_nonneg.mpr hθd.le)
  have hTS : ∀ y : Space d, θ • (θ⁻¹ • y) = y := fun y ↦ by
    rw [smul_smul, mul_inv_cancel₀ hθ.ne', one_smul]
  have hST : ∀ x : Space d, θ⁻¹ • (θ • x) = x := fun x ↦ by
    rw [smul_smul, inv_mul_cancel₀ hθ.ne', one_smul]
  refine ⟨inferInstance, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Measure.smul_apply, hSe.map_apply]
    have hpre : (fun y : Space d ↦ θ⁻¹ • y) ⁻¹' ((fun x ↦ θ • x) ⁻¹' W)ᶜ = Wᶜ := by
      ext y
      simp [hTS]
    rw [hpre, h.measure_compl, smul_zero]
  · intro V hV hVW
    rw [Measure.smul_apply, hSe.map_apply]
    have hVo : IsOpen ((fun y : Space d ↦ θ⁻¹ • y) ⁻¹' V) := hV.preimage (continuous_const_smul _)
    have hVsub : (fun y : Space d ↦ θ⁻¹ • y) ⁻¹' V ⊆ W := by
      intro y hy
      have := hVW hy
      simpa [hTS] using this
    rw [h.measure_open _ hVo hVsub]
    have hscale := variationalPerimeter_preimage_add_smul hd b E
      ((fun y : Space d ↦ θ⁻¹ • y) ⁻¹' V) 0 hθ
    have hset : (fun y : Space d ↦ (0 : Space d) + θ • y) ⁻¹'
        ((fun y : Space d ↦ θ⁻¹ • y) ⁻¹' V) = V := by
      ext x
      simp [hST]
    have hset2 : (fun y : Space d ↦ (0 : Space d) + θ • y) ⁻¹' E = (fun x ↦ θ • x) ⁻¹' E := by
      ext x
      simp
    rw [hset, hset2] at hscale
    rw [hscale, ENNReal.smul_def, smul_eq_mul]
    rfl
  · refine Integrable.smul_measure_nnreal ?_
    rw [hSe.integrable_map_iff]
    have heq : ((fun x ↦ ν (θ • x)) ∘ fun y : Space d ↦ θ⁻¹ • y) = ν := by
      funext y
      simp [hTS]
    rw [heq]
    exact h.integrable
  · refine Measure.ae_smul_measure ?_ κ
    rw [hSe.ae_map_iff]
    filter_upwards [h.norm_eq_one] with y hy
    simp [hTS, hy]
  · intro F hF hFs
    set G : Space d → Space d := fun y ↦ F (θ⁻¹ • y) with hG_def
    have hG : ContDiff ℝ 1 G := hF.comp (contDiff_const_smul θ⁻¹)
    have hFc : IsCompact (tsupport (F : Space d → Space d)) := F.hasCompactSupport
    have hGsub : tsupport G ⊆ (fun x : Space d ↦ θ • x) '' tsupport (F : Space d → Space d) := by
      apply closure_minimal _ (hFc.image (continuous_const_smul θ)).isClosed
      intro z hz
      refine ⟨θ⁻¹ • z, subset_tsupport _ fun h0 ↦ hz ?_, hTS z⟩
      simp only [G, h0]
    have hGc : HasCompactSupport G :=
      (hFc.image (continuous_const_smul θ)).of_isClosed_subset (isClosed_tsupport _) hGsub
    have hGs : tsupport G ⊆ W := by
      intro z hz
      obtain ⟨x, hx, rfl⟩ := hGsub hz
      exact hFs hx
    let Gc : C_c(Space d, Space d) := ⟨⟨G, hG.continuous⟩, hGc⟩
    have hdG : -(∫ y, E.indicator (fun _ ↦ (1 : ℝ)) y * fieldDivergence b G y) =
        ∫ y, inner ℝ (G y) (ν y) ∂μ := h.dist Gc hG hGs
    have hdivG : ∀ y, fieldDivergence b G y = θ⁻¹ * fieldDivergence b F (θ⁻¹ • y) :=
      fun y ↦ fieldDivergence_comp_smul b (hF.differentiable one_ne_zero) θ⁻¹ y
    have hL : (∫ x, ((fun x ↦ θ • x) ⁻¹' E).indicator (fun _ ↦ (1 : ℝ)) x *
          fieldDivergence b F x) =
        (θ ^ (d - 1))⁻¹ * ∫ y, E.indicator (fun _ ↦ (1 : ℝ)) y * fieldDivergence b G y := by
      have hcv := MeasureTheory.Measure.integral_comp_smul (μ := (volume : Measure (Space d)))
        (fun y ↦ E.indicator (fun _ ↦ (1 : ℝ)) y * fieldDivergence b F (θ⁻¹ • y)) θ
      rw [finrank_euclideanSpace_fin] at hcv
      have hlhs : (fun x ↦ ((fun x ↦ θ • x) ⁻¹' E).indicator (fun _ ↦ (1 : ℝ)) x *
          fieldDivergence b F x) =
          fun x ↦ E.indicator (fun _ ↦ (1 : ℝ)) (θ • x) *
            fieldDivergence b F (θ⁻¹ • (θ • x)) := by
        funext x
        rw [hST]
        rfl
      rw [hlhs, hcv]
      simp_rw [hdivG]
      have hpt : ∀ y, E.indicator (fun _ ↦ (1 : ℝ)) y * (θ⁻¹ * fieldDivergence b F (θ⁻¹ • y)) =
          θ⁻¹ * (E.indicator (fun _ ↦ (1 : ℝ)) y * fieldDivergence b F (θ⁻¹ • y)) :=
        fun y ↦ by ring
      simp_rw [hpt]
      rw [integral_const_mul, smul_eq_mul, abs_of_pos (inv_pos.mpr (pow_pos hθ d))]
      have hd' : θ ^ d = θ ^ (d - 1) * θ := by
        rw [← pow_succ]
        congr 1
        omega
      rw [hd', mul_inv]
      ring
    have hR : (∫ x, inner ℝ (F x) (ν (θ • x)) ∂(κ • μ.map (fun y ↦ θ⁻¹ • y))) =
        (θ ^ (d - 1))⁻¹ * ∫ y, inner ℝ (G y) (ν y) ∂μ := by
      rw [integral_smul_nnreal_measure, hSe.integral_map, NNReal.smul_def, smul_eq_mul, hκ]
      congr 1
      refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
      simp only [G, hTS]
    rw [hL, hR, ← hdG]
    ring

/-- The similarity `x ↦ c + θ Q x`. -/
def similarity {d : ℕ} (Q : Space d ≃ₗᵢ[ℝ] Space d) (c : Space d) (θ : ℝ) (x : Space d) :
    Space d :=
  c + θ • Q x

theorem similarity_eq_affineIsometry {d : ℕ} (Q : Space d ≃ₗᵢ[ℝ] Space d) (c : Space d) (θ : ℝ)
    (x : Space d) : similarity Q c θ x = affineIsometryHomeomorph Q c (θ • x) := by
  simp [similarity, affineIsometryHomeomorph_apply, map_smul, add_comm]

theorem preimage_similarity_eq {d : ℕ} (Q : Space d ≃ₗᵢ[ℝ] Space d) (c : Space d) (θ : ℝ)
    (A : Set (Space d)) :
    similarity Q c θ ⁻¹' A = (fun x ↦ θ • x) ⁻¹' (affineIsometryHomeomorph Q c ⁻¹' A) := by
  ext x
  simp [similarity_eq_affineIsometry]

/-- The measure transported by a similarity. -/
def similarityMeasure {d : ℕ} (μ : Measure (Space d)) (Q : Space d ≃ₗᵢ[ℝ] Space d)
    (c : Space d) (θ : ℝ) : Measure (Space d) :=
  Real.toNNReal ((θ ^ (d - 1))⁻¹) •
    (μ.map (affineIsometryHomeomorph Q c).symm).map (fun y ↦ θ⁻¹ • y)

/-- **Transport of perimeter representations by similarities.** -/
theorem IsPerimeterRepresentation.preimage_similarity {d : ℕ} (hd : 1 ≤ d)
    {b : OrthonormalBasis (Fin d) ℝ (Space d)} {E W : Set (Space d)} {μ : Measure (Space d)}
    {ν : Space d → Space d} (h : IsPerimeterRepresentation b E W μ ν)
    (Q : Space d ≃ₗᵢ[ℝ] Space d) (c : Space d) {θ : ℝ} (hθ : 0 < θ) :
    IsPerimeterRepresentation b (similarity Q c θ ⁻¹' E) (similarity Q c θ ⁻¹' W)
      (similarityMeasure μ Q c θ) (fun x ↦ Q.symm (ν (similarity Q c θ x))) := by
  have h2 := (h.preimage_affineIsometry Q c).preimage_smul hd hθ
  rw [← preimage_similarity_eq, ← preimage_similarity_eq] at h2
  have hν : (fun x ↦ Q.symm (ν (affineIsometryHomeomorph Q c (θ • x)))) =
      fun x ↦ Q.symm (ν (similarity Q c θ x)) := by
    funext x
    rw [similarity_eq_affineIsometry]
  rw [hν] at h2
  exact h2

/-- Local minimality is preserved by similarities. -/
theorem IsLocalPerimeterMinimizer.preimage_similarity {d : ℕ} (hd : 1 ≤ d)
    {b : OrthonormalBasis (Fin d) ℝ (Space d)} {E Ω : Set (Space d)}
    (h : IsLocalPerimeterMinimizer b E Ω) (Q : Space d ≃ₗᵢ[ℝ] Space d) (c : Space d) {θ : ℝ}
    (hθ : 0 < θ) :
    IsLocalPerimeterMinimizer b (similarity Q c θ ⁻¹' E) (similarity Q c θ ⁻¹' Ω) := by
  have h2 := (h.preimage_affineIsometry hd Q c).preimage_add_smul hd 0 hθ
  have hset : ∀ A : Set (Space d), (fun y : Space d ↦ (0 : Space d) + θ • y) ⁻¹'
      (affineIsometryHomeomorph Q c ⁻¹' A) = similarity Q c θ ⁻¹' A := by
    intro A
    rw [preimage_similarity_eq]
    ext x
    simp
  rw [hset, hset] at h2
  exact h2

theorem measureTheoreticBoundary_preimage_affineIsometry {d : ℕ} (E : Set (Space d))
    (Q : Space d ≃ₗᵢ[ℝ] Space d) (c : Space d) :
    measureTheoreticBoundary (affineIsometryHomeomorph Q c ⁻¹' E) =
      affineIsometryHomeomorph Q c ⁻¹' measureTheoreticBoundary E := by
  set T := affineIsometryHomeomorph Q c with hT_def
  have hmp : MeasurePreserving T.toMeasurableEquiv volume volume :=
    measurePreserving_affineIsometryHomeomorph Q c
  have hball : ∀ x r, T ⁻¹' ball (T x) r = ball x r := by
    intro x r
    ext y
    simp only [mem_preimage, mem_ball, hT_def, affineIsometryHomeomorph_apply, dist_eq_norm,
      add_sub_add_right_eq_sub, ← map_sub, LinearIsometryEquiv.norm_map]
  have h1 : ∀ x r, volume (T ⁻¹' E ∩ ball x r) = volume (E ∩ ball (T x) r) := by
    intro x r
    rw [← hball x r, ← preimage_inter]
    exact hmp.measure_preimage_equiv _
  have h2 : ∀ x r, volume (ball x r \ T ⁻¹' E) = volume (ball (T x) r \ E) := by
    intro x r
    rw [← hball x r, ← preimage_sdiff]
    exact hmp.measure_preimage_equiv _
  ext x
  simp only [measureTheoreticBoundary, mem_ofPred_eq, mem_preimage, h1, h2]

theorem measureTheoreticBoundary_preimage_similarity {d : ℕ} (E : Set (Space d))
    (Q : Space d ≃ₗᵢ[ℝ] Space d) (c : Space d) {θ : ℝ} (hθ : 0 < θ) :
    measureTheoreticBoundary (similarity Q c θ ⁻¹' E) =
      similarity Q c θ ⁻¹' measureTheoreticBoundary E := by
  have hset : ∀ A : Set (Space d), similarity Q c θ ⁻¹' A =
      (fun z : Space d ↦ (0 : Space d) + θ • z) ⁻¹' (affineIsometryHomeomorph Q c ⁻¹' A) := by
    intro A
    rw [preimage_similarity_eq]
    ext x
    simp
  rw [hset, hset, measureTheoreticBoundary_preimage_add_smul _ 0 hθ,
    measureTheoreticBoundary_preimage_affineIsometry]

/-- Integrals against the measure transported by a similarity. -/
theorem integral_similarityMeasure {d : ℕ} (μ : Measure (Space d))
    (Q : Space d ≃ₗᵢ[ℝ] Space d) (c : Space d) {θ : ℝ} (hθ : 0 < θ) (f : Space d → ℝ) :
    ∫ x, f x ∂(similarityMeasure μ Q c θ) =
      (θ ^ (d - 1))⁻¹ * ∫ y, f (θ⁻¹ • (affineIsometryHomeomorph Q c).symm y) ∂μ := by
  unfold similarityMeasure
  rw [integral_smul_nnreal_measure, (measurableEmbedding_smul_inv hθ.ne').integral_map,
    (affineIsometryHomeomorph Q c).symm.measurableEmbedding.integral_map, NNReal.smul_def,
    smul_eq_mul, Real.coe_toNNReal _ (inv_nonneg.mpr (pow_pos hθ _).le)]

theorem similarity_inv_apply {d : ℕ} (Q : Space d ≃ₗᵢ[ℝ] Space d) (c : Space d) {θ : ℝ}
    (hθ : θ ≠ 0) (y : Space d) :
    similarity Q c θ (θ⁻¹ • (affineIsometryHomeomorph Q c).symm y) = y := by
  rw [similarity_eq_affineIsometry, smul_smul, mul_inv_cancel₀ hθ, one_smul,
    Homeomorph.apply_symm_apply]

end SerrinEpigraph
