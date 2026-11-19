module

public import SerrinEpigraph.PerimeterFlattening
public import SerrinEpigraph.PerimeterVariation

/-!
# Perimeter representations under affine isometries

This module packages the hypotheses of the `BVColumnGraph` / `PerimeterFlattening` API into the
predicate `IsPerimeterRepresentation b E W μ ν`: `μ` is a finite measure concentrated on the open
set `W` that agrees with the variational perimeter of `E` on open subsets of `W`, and `ν` is a unit
polar vector realizing the distributional gradient of `1_E` against `C¹` tests supported in `W`.

For an affine isometry `T x = Q x + c` (`Q` a linear isometry equivalence), the representation of
`T⁻¹ E` on `T⁻¹ W` is the transport of the representation of `E` on `W`:
`μ' = (T⁻¹)_# μ` and `ν' = Q⁻¹ ∘ ν ∘ T` (`IsPerimeterRepresentation.preimage_affineIsometry`).
Consequently the directed excess of the rotated frame is the excess of `μ` in the rotated
direction `Q e_n` over the tilted region (`projectedExcessMeasure_real_transport`), and `GR8.2`
holds in every tilted frame with all integrals written against the original `μ`
(`IsLocalPerimeterMinimizer.flattening_excess_le_tilted`), as used in `GR12`.
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory InnerProductSpace Filter
open scoped Topology ENNReal CompactlySupported

namespace SerrinEpigraph

/-! ### 1. Perimeter representations -/

/-- `(μ, ν)` represents the perimeter of `E` on the open set `W`. These are exactly the
hypotheses `[IsFiniteMeasure μ]`, `hμcompl`, `hμopen`, `hν`, `hνunit`, `hdist` of the
`BVColumnGraph` and `PerimeterFlattening` API (with `W` the cylinder). -/
structure IsPerimeterRepresentation {d : ℕ} (b : OrthonormalBasis (Fin d) ℝ (Space d))
    (E W : Set (Space d)) (μ : Measure (Space d)) (ν : Space d → Space d) : Prop where
  isFiniteMeasure : IsFiniteMeasure μ
  measure_compl : μ Wᶜ = 0
  measure_open : ∀ V, IsOpen V → V ⊆ W → μ V = variationalPerimeter b E V
  integrable : Integrable ν μ
  norm_eq_one : ∀ᵐ x ∂μ, ‖ν x‖ = 1
  dist : ∀ F : C_c(Space d, Space d), ContDiff ℝ 1 (F : Space d → Space d) →
    tsupport (F : Space d → Space d) ⊆ W →
    -(∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F x) =
      ∫ x, inner ℝ (F x) (ν x) ∂μ

/-- A finite-perimeter open set carries a perimeter representation. -/
theorem exists_isPerimeterRepresentation {d : ℕ} (b : OrthonormalBasis (Fin d) ℝ (Space d))
    {E W : Set (Space d)} (hE : MeasurableSet E) (hW : IsOpen W)
    (hP : variationalPerimeter b E W ≠ ⊤) :
    ∃ (μ : Measure (Space d)) (ν : Space d → Space d), IsPerimeterRepresentation b E W μ ν := by
  obtain ⟨μ, ν, hfin, -, huniv, hopen, hν, hunit, hdist⟩ :=
    exists_localized_perimeter_polar_measure b hE hP
  have hWμ : μ W = μ univ := by
    rw [hopen _ hW subset_rfl, huniv]
  have hcompl : μ Wᶜ = 0 := by
    have hsum := measure_add_measure_compl (μ := μ) hW.measurableSet
    rw [hWμ] at hsum
    exact (ENNReal.add_right_inj (measure_ne_top μ univ)).mp (hsum.trans (add_zero _).symm)
  exact ⟨μ, ν, ⟨hfin, hcompl, hopen, hν, hunit, hdist⟩⟩

/-- Restricting a perimeter representation to an open subset. -/
theorem IsPerimeterRepresentation.restrict {d : ℕ} {b : OrthonormalBasis (Fin d) ℝ (Space d)}
    {E W : Set (Space d)} {μ : Measure (Space d)} {ν : Space d → Space d}
    (h : IsPerimeterRepresentation b E W μ ν) {W' : Set (Space d)} (hW' : IsOpen W')
    (hW'W : W' ⊆ W) : IsPerimeterRepresentation b E W' (μ.restrict W') ν := by
  have := h.isFiniteMeasure
  refine ⟨inferInstance, ?_, ?_, h.integrable.restrict, ae_restrict_of_ae h.norm_eq_one, ?_⟩
  · rw [Measure.restrict_apply hW'.measurableSet.compl, compl_inter_self, measure_empty]
  · intro V hV hVW'
    rw [Measure.restrict_apply hV.measurableSet, inter_eq_left.mpr hVW']
    exact h.measure_open V hV (hVW'.trans hW'W)
  · intro F hF hFs
    rw [h.dist F hF (hFs.trans hW'W)]
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ ?_).symm
    have hFx : F x = 0 := image_eq_zero_of_notMem_tsupport fun hmem ↦ hx (hFs hmem)
    rw [hFx, inner_zero_left]

/-- The measure of a perimeter representation is unique. -/
theorem IsPerimeterRepresentation.measure_eq {d : ℕ}
    {b : OrthonormalBasis (Fin d) ℝ (Space d)} {E W : Set (Space d)} (hW : IsOpen W)
    {μ μ' : Measure (Space d)} {ν ν' : Space d → Space d}
    (h : IsPerimeterRepresentation b E W μ ν) (h' : IsPerimeterRepresentation b E W μ' ν') :
    μ = μ' := by
  have := h.isFiniteMeasure
  have := h'.isFiniteMeasure
  have h1 := measure_restrict_eq_of_open_values hW h.measure_compl
    (fun U hU hUW ↦ (h.measure_open U hU hUW).trans (h'.measure_open U hU hUW).symm)
  have h2 : μ'.restrict W = μ' :=
    Measure.restrict_eq_self_of_ae_mem (by rw [ae_iff]; exact h'.measure_compl)
  rw [← h1, h2]

/-! ### 2. Affine isometries -/

/-- The affine isometry `x ↦ Q x + c` as a homeomorphism of `Space d`. -/
def affineIsometryHomeomorph {d : ℕ} (Q : Space d ≃ₗᵢ[ℝ] Space d) (c : Space d) :
    Space d ≃ₜ Space d :=
  Q.toHomeomorph.trans (Homeomorph.addRight c)

@[simp]
theorem affineIsometryHomeomorph_apply {d : ℕ} (Q : Space d ≃ₗᵢ[ℝ] Space d) (c x : Space d) :
    affineIsometryHomeomorph Q c x = Q x + c := rfl

@[simp]
theorem affineIsometryHomeomorph_symm_apply {d : ℕ} (Q : Space d ≃ₗᵢ[ℝ] Space d)
    (c y : Space d) : (affineIsometryHomeomorph Q c).symm y = Q.symm (y - c) := by
  rfl

theorem measurePreserving_affineIsometryHomeomorph {d : ℕ} (Q : Space d ≃ₗᵢ[ℝ] Space d)
    (c : Space d) :
    MeasurePreserving (affineIsometryHomeomorph Q c) (volume : Measure (Space d)) volume :=
  (measurePreserving_add_right volume c).comp Q.measurePreserving

theorem preimage_affineIsometryHomeomorph_eq {d : ℕ} (Q : Space d ≃ₗᵢ[ℝ] Space d)
    (c : Space d) (A : Set (Space d)) :
    affineIsometryHomeomorph Q c ⁻¹' A = Q ⁻¹' ((fun y : Space d ↦ -c + y) '' A) := by
  ext x
  simp only [mem_preimage, affineIsometryHomeomorph_apply, mem_image]
  constructor
  · intro hx
    exact ⟨Q x + c, hx, by abel⟩
  · rintro ⟨z, hz, hzx⟩
    have : z = Q x + c := by rw [← hzx]; abel
    rwa [this] at hz

/-- Variational perimeter is invariant under affine isometries. -/
theorem variationalPerimeter_preimage_affineIsometry {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) (Q : Space d ≃ₗᵢ[ℝ] Space d) (c : Space d)
    (E V : Set (Space d)) :
    variationalPerimeter b (affineIsometryHomeomorph Q c ⁻¹' E)
        (affineIsometryHomeomorph Q c ⁻¹' V) = variationalPerimeter b E V := by
  rw [preimage_affineIsometryHomeomorph_eq, preimage_affineIsometryHomeomorph_eq,
    variationalPerimeter_preimage_isometry, variationalPerimeter_add]

/-- Divergence of a translated field. -/
theorem fieldDivergence_comp_add_right {d : ℕ} (b : OrthonormalBasis (Fin d) ℝ (Space d))
    (F : Space d → Space d) (c x : Space d) :
    fieldDivergence b (fun y ↦ F (y + c)) x = fieldDivergence b F (x + c) := by
  unfold fieldDivergence
  rw [fderiv_comp_add_right]

/-- Divergence of the transport `y ↦ Q (F (T⁻¹ y))` of a field by the affine isometry
`T x = Q x + c`. -/
theorem fieldDivergence_affineIsometry_transport {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) (Q : Space d ≃ₗᵢ[ℝ] Space d) (c : Space d)
    (F : Space d → Space d) (y : Space d) :
    fieldDivergence b (fun z ↦ Q (F ((affineIsometryHomeomorph Q c).symm z))) y =
      fieldDivergence b F ((affineIsometryHomeomorph Q c).symm y) := by
  set G' : Space d → Space d := fun w ↦ Q.symm.symm (F (Q.symm w)) with hG'_def
  have h1 : (fun z ↦ Q (F ((affineIsometryHomeomorph Q c).symm z))) =
      fun z ↦ G' (z + -c) := by
    funext z
    simp [hG'_def, sub_eq_add_neg]
  rw [h1, fieldDivergence_comp_add_right b G' (-c) y, hG'_def,
    fieldDivergence_isometry_conjugate, affineIsometryHomeomorph_symm_apply, sub_eq_add_neg]

/-- **Transport of perimeter representations by affine isometries.** If `(μ, ν)` represents the
perimeter of `E` on `W`, then for `T x = Q x + c` the pair `((T⁻¹)_# μ, Q⁻¹ ∘ ν ∘ T)` represents
the perimeter of `T⁻¹ E` on `T⁻¹ W`. -/
theorem IsPerimeterRepresentation.preimage_affineIsometry {d : ℕ}
    {b : OrthonormalBasis (Fin d) ℝ (Space d)} {E W : Set (Space d)} {μ : Measure (Space d)}
    {ν : Space d → Space d} (h : IsPerimeterRepresentation b E W μ ν)
    (Q : Space d ≃ₗᵢ[ℝ] Space d) (c : Space d) :
    IsPerimeterRepresentation b (affineIsometryHomeomorph Q c ⁻¹' E)
      (affineIsometryHomeomorph Q c ⁻¹' W)
      (μ.map (affineIsometryHomeomorph Q c).symm)
      (fun x ↦ Q.symm (ν (affineIsometryHomeomorph Q c x))) := by
  set T := affineIsometryHomeomorph Q c with hT_def
  have := h.isFiniteMeasure
  have hSe : MeasurableEmbedding T.symm := T.symm.measurableEmbedding
  have hTS : ∀ y, T (T.symm y) = y := T.apply_symm_apply
  have hST : ∀ x, T.symm (T x) = x := T.symm_apply_apply
  refine ⟨Measure.isFiniteMeasure_map μ _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hSe.map_apply]
    have hpre : T.symm ⁻¹' (T ⁻¹' W)ᶜ = Wᶜ := by
      ext y
      simp [hTS]
    rw [hpre, h.measure_compl]
  · intro V hV hVW
    rw [hSe.map_apply]
    have hVo : IsOpen (T.symm ⁻¹' V) := hV.preimage T.symm.continuous
    have hVsub : T.symm ⁻¹' V ⊆ W := by
      intro y hy
      have := hVW hy
      simpa [hTS] using this
    rw [h.measure_open _ hVo hVsub, ← variationalPerimeter_preimage_affineIsometry b Q c E]
    congr 1
    ext x
    simp [hT_def]
  · rw [hSe.integrable_map_iff]
    have heq : ((fun x ↦ Q.symm (ν (T x))) ∘ T.symm) = fun y ↦ Q.symm (ν y) := by
      funext y
      simp [hTS]
    rw [heq]
    exact (Q.symm.toContinuousLinearEquiv.toContinuousLinearMap.integrable_comp h.integrable)
  · rw [hSe.ae_map_iff]
    filter_upwards [h.norm_eq_one] with y hy
    simp [hTS, hy]
  · intro F hF hFs
    have hTsymm : (T.symm : Space d → Space d) = fun y ↦ Q.symm (y - c) := by
      funext y
      simp [hT_def]
    have hScd : ContDiff ℝ 1 (T.symm : Space d → Space d) := by
      rw [hTsymm]
      exact Q.symm.contDiff.comp (contDiff_id.sub contDiff_const)
    -- the transported test field
    let G : Space d → Space d := fun z ↦ Q (F (T.symm z))
    have hG : ContDiff ℝ 1 G := Q.contDiff.comp (hF.comp hScd)
    have hFc : IsCompact (tsupport (F : Space d → Space d)) := F.hasCompactSupport
    have hGsub : tsupport G ⊆ T '' tsupport (F : Space d → Space d) := by
      apply closure_minimal _ (hFc.image T.continuous).isClosed
      intro z hz
      refine ⟨T.symm z, subset_tsupport _ fun h0 ↦ hz ?_, hTS z⟩
      simp only [G, h0, map_zero]
    have hGc : HasCompactSupport G :=
      (hFc.image T.continuous).of_isClosed_subset (isClosed_tsupport _) hGsub
    have hGs : tsupport G ⊆ W := by
      intro z hz
      obtain ⟨x, hx, rfl⟩ := hGsub hz
      exact hFs hx
    let Gc : C_c(Space d, Space d) := ⟨⟨G, hG.continuous⟩, hGc⟩
    have hd : -(∫ y, E.indicator (fun _ ↦ (1 : ℝ)) y * fieldDivergence b G y) =
        ∫ y, inner ℝ (G y) (ν y) ∂μ := h.dist Gc hG hGs
    have hL : (∫ x, (T ⁻¹' E).indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F x) =
        ∫ y, E.indicator (fun _ ↦ (1 : ℝ)) y * fieldDivergence b G y := by
      rw [← (measurePreserving_affineIsometryHomeomorph Q c).integral_comp
        T.measurableEmbedding (fun y ↦ E.indicator (fun _ ↦ (1 : ℝ)) y * fieldDivergence b G y)]
      congr 1
      funext x
      have hdiv := fieldDivergence_affineIsometry_transport b Q c F (T x)
      rw [← hT_def] at hdiv
      rw [hST] at hdiv
      change (T ⁻¹' E).indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F x =
        E.indicator (fun _ ↦ (1 : ℝ)) (T x) * fieldDivergence b G (T x)
      rw [show fieldDivergence b G (T x) = fieldDivergence b F x from hdiv]
      rfl
    have hR : (∫ y, inner ℝ (G y) (ν y) ∂μ) =
        ∫ x, inner ℝ (F x) (Q.symm (ν (T x))) ∂(μ.map T.symm) := by
      rw [hSe.integral_map]
      congr 1
      funext y
      simp only [G, hTS]
      rw [← Q.inner_map_map (F (T.symm y)) (Q.symm (ν y)), Q.apply_symm_apply]
    rw [hL, hd, hR]

/-- Local minimality is preserved by affine isometries. -/
theorem IsLocalPerimeterMinimizer.preimage_affineIsometry {d : ℕ} (hd : 1 ≤ d)
    {b : OrthonormalBasis (Fin d) ℝ (Space d)} {E Ω : Set (Space d)}
    (h : IsLocalPerimeterMinimizer b E Ω) (Q : Space d ≃ₗᵢ[ℝ] Space d) (c : Space d) :
    IsLocalPerimeterMinimizer b (affineIsometryHomeomorph Q c ⁻¹' E)
      (affineIsometryHomeomorph Q c ⁻¹' Ω) := by
  have h₂ := (h.preimage_add_smul hd c one_pos).preimage_isometry Q
  have hset : ∀ A : Set (Space d),
      Q ⁻¹' ((fun y ↦ c + (1 : ℝ) • y) ⁻¹' A) = affineIsometryHomeomorph Q c ⁻¹' A := by
    intro A
    ext x
    simp [add_comm]
  rwa [hset, hset] at h₂

/-! ### 3. Transport of integrals and of the directed excess -/

/-- Set integrals against the transported measure. -/
theorem setIntegral_map_affineIsometry_symm {d : ℕ} (μ : Measure (Space d))
    (Q : Space d ≃ₗᵢ[ℝ] Space d) (c : Space d) (B : Set (Space d)) (f : Space d → ℝ) :
    ∫ x in B, f x ∂(μ.map (affineIsometryHomeomorph Q c).symm) =
      ∫ y in (affineIsometryHomeomorph Q c).symm ⁻¹' B,
        f ((affineIsometryHomeomorph Q c).symm y) ∂μ := by
  have hSe := (affineIsometryHomeomorph Q c).symm.measurableEmbedding
  rw [hSe.restrict_map, hSe.integral_map]

/-- **Directed excess in a tilted frame.** For the transported representation, the projected
excess over a horizontal set `A` is the excess of the original `μ` in the rotated direction
`Q e_n` over the tilted region `T (π⁻¹ A)`. -/
theorem projectedExcessMeasure_real_transport {m : ℕ} {μ : Measure (Space (m + 1))}
    [IsFiniteMeasure μ] {ν : Space (m + 1) → Space (m + 1)} (hν : Integrable ν μ)
    (hνunit : ∀ᵐ x ∂μ, ‖ν x‖ = 1) (Q : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1))
    (c : Space (m + 1)) {A : Set (Space m)} (hA : MeasurableSet A) :
    (projectedExcessMeasure (μ.map (affineIsometryHomeomorph Q c).symm)
        (fun x ↦ Q.symm (ν (affineIsometryHomeomorph Q c x)))).real A =
      ∫ y in (affineIsometryHomeomorph Q c).symm ⁻¹' (horizontal ⁻¹' A),
        (1 - inner ℝ (ν y) (Q (verticalDirection m))) ∂μ := by
  set T := affineIsometryHomeomorph Q c with hT_def
  have hSe : MeasurableEmbedding T.symm := T.symm.measurableEmbedding
  have hπm : Measurable (horizontal : Space (m + 1) → Space m) :=
    continuous_horizontal.measurable
  have hBm : MeasurableSet (horizontal ⁻¹' A : Set (Space (m + 1))) := hA.preimage hπm
  have hinner : ∀ y, inner ℝ (Q.symm (ν (T (T.symm y)))) (verticalDirection m) =
      inner ℝ (ν y) (Q (verticalDirection m)) := by
    intro y
    rw [T.apply_symm_apply, ← Q.inner_map_map, Q.apply_symm_apply]
  have hlin : projectedExcessMeasure (μ.map T.symm) (fun x ↦ Q.symm (ν (T x))) A =
      ∫⁻ y in T.symm ⁻¹' (horizontal ⁻¹' A),
        ENNReal.ofReal (1 - inner ℝ (ν y) (Q (verticalDirection m))) ∂μ := by
    unfold projectedExcessMeasure
    rw [Measure.map_apply hπm hA, withDensity_apply _ hBm, hSe.restrict_map,
      hSe.lintegral_map]
    simp only [hinner]
  have hf_int : Integrable (fun y ↦ 1 - inner ℝ (ν y) (Q (verticalDirection m))) μ :=
    (integrable_const 1).sub (hν.inner_const _)
  have hf_nonneg : ∀ᵐ y ∂μ, 0 ≤ 1 - inner ℝ (ν y) (Q (verticalDirection m)) := by
    filter_upwards [hνunit] with y hy
    have hcs := real_inner_le_norm (ν y) (Q (verticalDirection m))
    rw [hy, Q.norm_map, norm_verticalDirection, mul_one] at hcs
    linarith
  rw [Measure.real, hlin, integral_eq_lintegral_of_nonneg_ae (ae_restrict_of_ae hf_nonneg)
    hf_int.aestronglyMeasurable.restrict]

/-! ### 4. `GR8.2` with perimeter representations and in tilted frames -/

/-- `GR8.2` stated with a perimeter representation of the cylinder. -/
theorem IsLocalPerimeterMinimizer.flattening_excess_closedBall_le_of_rep {m : ℕ}
    {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))}
    {E Ω : Set (Space (m + 1))} (hmin : IsLocalPerimeterMinimizer b E Ω)
    {U : Set (Space m)} (hU : IsOpen U) {H H' : ℝ} (hH : 0 < H) (hHH' : H < H')
    (hcyl : cylinderSet U H' ⊆ Ω) {μ : Measure (Space (m + 1))}
    {ν : Space (m + 1) → Space (m + 1)}
    (hrep : IsPerimeterRepresentation b E (cylinderSet U H') μ ν)
    (hbot : ∀ᵐ x ∂volume, horizontal x ∈ U → x (Fin.last m) ∈ Ioo (-H') (-H) → x ∉ E)
    (htop : ∀ᵐ x ∂volume, horizontal x ∈ U → x (Fin.last m) ∈ Ioo H H' → x ∈ E)
    (y₀ : Space m) {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R) (hball : closedBall y₀ R ⊆ U)
    (lam : ℝ) :
    (projectedExcessMeasure μ ν).real (closedBall y₀ r) ≤
      flatteningConstant / (R - r) ^ 2 *
        ∫ x in horizontal ⁻¹' ball y₀ R, (x (Fin.last m) - lam) ^ 2 ∂μ := by
  have := hrep.isFiniteMeasure
  exact hmin.flattening_excess_closedBall_le hU hH hHH' hcyl μ hrep.measure_compl
    hrep.measure_open hrep.integrable hrep.norm_eq_one hrep.dist hbot htop y₀ hr hrR hball lam

/-- **`GR8.2` in a tilted frame** (`GR12`). Let `T x = Q x + c` be an affine isometry and
suppose that in the tilted cylinder `T (U × (-H', H'))` the boundary of `E` is trapped in the
tilted slab: `T x ∉ E` for `x_n ∈ (-H', -H)` and `T x ∈ E` for `x_n ∈ (H, H')`. If `(μ, ν)`
represents the perimeter of `E` on an open set containing the tilted cylinder, then the excess of
`μ` in the rotated direction `Q e_n` over the tilted inner cylinder is bounded by the squared
tilted height deviation over the tilted outer cylinder; all integrals are against `μ`. -/
theorem IsLocalPerimeterMinimizer.flattening_excess_closedBall_le_tilted {m : ℕ}
    {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))}
    {E Ω : Set (Space (m + 1))} (hmin : IsLocalPerimeterMinimizer b E Ω)
    (Q : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1)) (c : Space (m + 1))
    {U : Set (Space m)} (hU : IsOpen U) {H H' : ℝ} (hH : 0 < H) (hHH' : H < H')
    (hcyl : affineIsometryHomeomorph Q c '' cylinderSet U H' ⊆ Ω)
    {W : Set (Space (m + 1))} {μ : Measure (Space (m + 1))}
    {ν : Space (m + 1) → Space (m + 1)} (hrep : IsPerimeterRepresentation b E W μ ν)
    (hcylW : affineIsometryHomeomorph Q c '' cylinderSet U H' ⊆ W)
    (hbot : ∀ᵐ x ∂volume, horizontal x ∈ U → x (Fin.last m) ∈ Ioo (-H') (-H) → Q x + c ∉ E)
    (htop : ∀ᵐ x ∂volume, horizontal x ∈ U → x (Fin.last m) ∈ Ioo H H' → Q x + c ∈ E)
    (y₀ : Space m) {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R) (hball : closedBall y₀ R ⊆ U)
    (lam : ℝ) :
    ∫ y in (affineIsometryHomeomorph Q c).symm ⁻¹' (horizontal ⁻¹' closedBall y₀ r) ∩
        affineIsometryHomeomorph Q c '' cylinderSet U H',
        (1 - inner ℝ (ν y) (Q (verticalDirection m))) ∂μ ≤
      flatteningConstant / (R - r) ^ 2 *
        ∫ y in (affineIsometryHomeomorph Q c).symm ⁻¹' (horizontal ⁻¹' ball y₀ R) ∩
          affineIsometryHomeomorph Q c '' cylinderSet U H',
          ((affineIsometryHomeomorph Q c).symm y (Fin.last m) - lam) ^ 2 ∂μ := by
  set T := affineIsometryHomeomorph Q c with hT_def
  set C := cylinderSet U H' with hC_def
  have hCo : IsOpen C := isOpen_cylinderSet hU H'
  have hTCo : IsOpen (T '' C) := T.isOpenMap C hCo
  have hrepT := hrep.restrict hTCo hcylW
  have hrep' := hrepT.preimage_affineIsometry Q c
  rw [← hT_def, T.preimage_image] at hrep'
  have hmin' := hmin.preimage_affineIsometry (by omega) Q c
  rw [← hT_def] at hmin'
  have hcyl' : C ⊆ T ⁻¹' Ω := fun x hx ↦ hcyl ⟨x, hx, rfl⟩
  have hmain := hmin'.flattening_excess_closedBall_le_of_rep hU hH hHH' hcyl' hrep' hbot htop y₀
    hr hrR hball lam
  have := hrep.isFiniteMeasure
  have hint := (hrep.integrable).restrict (s := T '' C)
  have hunit := ae_restrict_of_ae (s := T '' C) hrep.norm_eq_one
  rw [projectedExcessMeasure_real_transport hint hunit Q c isClosed_closedBall.measurableSet,
    setIntegral_map_affineIsometry_symm _ Q c,
    Measure.restrict_restrict (isClosed_closedBall.measurableSet.preimage
      continuous_horizontal.measurable |>.preimage T.symm.continuous.measurable),
    Measure.restrict_restrict (measurableSet_ball.preimage continuous_horizontal.measurable
      |>.preimage T.symm.continuous.measurable)] at hmain
  exact hmain

end SerrinEpigraph
