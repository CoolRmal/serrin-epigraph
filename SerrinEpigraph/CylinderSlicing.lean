module

public import SerrinEpigraph.MinimizerCompactness
public import SerrinEpigraph.BVColumnGraph

/-!
# Vertical slicing of divergence pairings and minimality of cylinder cross-sections (GR6)

Split `Space (k + 1)` into horizontal coordinates `Space k` and one vertical coordinate.
This module proves, without any rectifiability or trace theory:
- an exact Fubini slicing identity for `∫ 1_W div Y`
  (`integral_indicator_mul_fieldDivergence_eq_slices`): the divergence splits into the
  horizontal divergence of the slice fields
  `z ↦ horizontal (Y (point z t))` and the vertical derivative of the profiles
  `s ↦ Y (point y s) (Fin.last k)`;
- the lower bound `2 L · P(A, U) ≤ P(horizontal ⁻¹' A, cylinderSet U (L + 1))` for cylinders
  (`ofReal_two_mul_variationalPerimeter_le_cylinder`);
- the upper bound `P(W, cylinderSet U (L + 1)) ≤ 2 L P(G, U) + 2 P(A, U) + 2 |(A ∆ G) ∩ U|` for the
  layered competitor `W` equal to `G × (-L, L)` inside the slab and to `A × ℝ` outside it
  (`variationalPerimeter_layeredSet_le`);
- **GR6** of `docs/rigidity-proof/gmt-regularity.md`: the cross-section of a local perimeter
  minimizing cylinder is a local perimeter minimizer one dimension lower
  (`IsLocalPerimeterMinimizer.of_preimage_horizontal`);
- volume and null-set formulas for cylinders `horizontal ⁻¹' A`.
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory InnerProductSpace Filter
open scoped Topology CompactlySupported ENNReal

namespace SerrinEpigraph

/-! ### 1. Euclidean coordinates -/

/-- The squared Euclidean norm splits into horizontal and vertical parts. -/
private theorem norm_sq_eq_norm_horizontal_sq_add_last_sq {k : ℕ} (x : Space (k + 1)) :
    ‖x‖ ^ 2 = ‖horizontal x‖ ^ 2 + x (Fin.last k) ^ 2 := by
  conv_lhs => rw [← point_horizontal_last x]
  rw [← real_inner_self_eq_norm_sq, inner_point_point, real_inner_self_eq_norm_sq]
  ring

/-- Horizontal projection does not increase the Euclidean norm. -/
private theorem norm_horizontal_le_norm {k : ℕ} (x : Space (k + 1)) : ‖horizontal x‖ ≤ ‖x‖ := by
  have h := norm_sq_eq_norm_horizontal_sq_add_last_sq x
  have h2 : ‖horizontal x‖ ^ 2 ≤ ‖x‖ ^ 2 := by nlinarith [sq_nonneg (x (Fin.last k))]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2

/-- The vertical coordinate is bounded by the Euclidean norm. -/
private theorem abs_last_le_norm {k : ℕ} (x : Space (k + 1)) : |x (Fin.last k)| ≤ ‖x‖ := by
  have h := norm_sq_eq_norm_horizontal_sq_add_last_sq x
  have h2 : |x (Fin.last k)| ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [sq_abs]
    nlinarith [sq_nonneg ‖horizontal x‖]
  exact (pow_le_pow_iff_left₀ (abs_nonneg _) (norm_nonneg _) two_ne_zero).mp h2

/-- The Euclidean norm is bounded by the sum of the horizontal norm and the vertical height. -/
private theorem norm_le_norm_horizontal_add_abs_last {k : ℕ} (x : Space (k + 1)) :
    ‖x‖ ≤ ‖horizontal x‖ + |x (Fin.last k)| := by
  have h := norm_sq_eq_norm_horizontal_sq_add_last_sq x
  have h2 : ‖x‖ ^ 2 ≤ (‖horizontal x‖ + |x (Fin.last k)|) ^ 2 := by
    rw [h, add_sq, sq_abs]
    nlinarith [norm_nonneg (horizontal x), abs_nonneg (x (Fin.last k))]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h2

private theorem horizontal_zero {k : ℕ} : horizontal (0 : Space (k + 1)) = 0 := by
  ext i
  simp [horizontal]

private theorem horizontal_smul_space {k : ℕ} (c : ℝ) (x : Space (k + 1)) :
    horizontal (c • x) = c • horizontal x := by
  ext i
  simp [horizontal]

private theorem horizontal_apply_castSucc {k : ℕ} (x : Space (k + 1)) (j : Fin k) :
    horizontal x j = x j.castSucc := by
  simp [horizontal]

/-- The horizontal embedding `v ↦ point v 0` as a continuous linear map. -/
def horizontalEmbedding (k : ℕ) : Space k →L[ℝ] Space (k + 1) :=
  pointContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ (Space k) ℝ)

@[simp]
theorem horizontalEmbedding_apply {k : ℕ} (v : Space k) :
    horizontalEmbedding k v = point v 0 := rfl

private theorem point_eq_horizontalEmbedding_add {k : ℕ} (z : Space k) (t : ℝ) :
    point z t = horizontalEmbedding k z + point 0 t := by
  rw [horizontalEmbedding_apply]
  ext i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i <;> simp [point]

private theorem contDiff_point_left {k : ℕ} (t : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun z : Space k ↦ point z t) := by
  have h : (fun z : Space k ↦ point z t) = fun z ↦ horizontalEmbedding k z + point 0 t := by
    funext z
    exact point_eq_horizontalEmbedding_add z t
  rw [h]
  exact (horizontalEmbedding k).contDiff.add contDiff_const

private theorem continuous_point_left {k : ℕ} (t : ℝ) : Continuous (fun z : Space k ↦ point z t) :=
  (contDiff_point_left (n := 0) t).continuous

private theorem hasFDerivAt_point_left {k : ℕ} (z : Space k) (t : ℝ) :
    HasFDerivAt (fun z' : Space k ↦ point z' t) (horizontalEmbedding k) z := by
  have h := ((horizontalEmbedding k).hasFDerivAt (x := z)).add_const (point 0 t)
  convert h using 1
  funext z'
  exact point_eq_horizontalEmbedding_add z' t

private theorem point_single_zero {k : ℕ} (j : Fin k) :
    point (EuclideanSpace.single j (1 : ℝ)) 0 =
      (EuclideanSpace.single j.castSucc 1 : Space (k + 1)) := by
  ext i
  refine Fin.lastCases ?_ (fun l ↦ ?_) i
  · simp [point]
  · simp [point]

private theorem hasDerivAt_point_right {k : ℕ} (y : Space k) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ point y s) (verticalDirection k) t := by
  have h := ((hasDerivAt_id t).smul_const (verticalDirection k)).const_add (point y 0)
  convert h using 1
  · funext s
    rw [point_add_vertical]
    simp
  · simp

/-! ### 2. Divergence in slices -/

/-- Coordinate formula for the divergence in the standard basis. -/
private theorem fieldDivergence_basisFun_eq_sum {d : ℕ} (F : Space d → Space d) (x : Space d) :
    fieldDivergence (EuclideanSpace.basisFun (Fin d) ℝ) F x =
      ∑ i, fderiv ℝ F x (EuclideanSpace.single i 1) i := by
  simp [fieldDivergence, EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left]

/-- The divergence of a horizontal slice field consists of the horizontal diagonal entries of
the ambient derivative. -/
theorem fieldDivergence_slice_eq {k : ℕ} {Y : Space (k + 1) → Space (k + 1)}
    (hY : Differentiable ℝ Y) (t : ℝ) (y : Space k) :
    fieldDivergence (EuclideanSpace.basisFun (Fin k) ℝ) (fun z ↦ horizontal (Y (point z t))) y =
      ∑ j : Fin k, fderiv ℝ Y (point y t) (EuclideanSpace.single j.castSucc 1) j.castSucc := by
  have hd : HasFDerivAt (fun z ↦ horizontal (Y (point z t)))
      (horizontalContinuousLinearMap.comp
        ((fderiv ℝ Y (point y t)).comp (horizontalEmbedding k))) y := by
    have h1 := (hY (point y t)).hasFDerivAt.comp y (hasFDerivAt_point_left y t)
    exact horizontalContinuousLinearMap.hasFDerivAt.comp y h1
  rw [fieldDivergence_basisFun_eq_sum, hd.fderiv]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  change horizontal (fderiv ℝ Y (point y t) (point (EuclideanSpace.single j 1) 0)) j = _
  rw [point_single_zero, horizontal_apply_castSucc]

/-- The vertical profile of a differentiable field has derivative given by the last diagonal
entry of the ambient derivative. -/
theorem hasDerivAt_vertical_profile {k : ℕ} {Y : Space (k + 1) → Space (k + 1)}
    (hY : Differentiable ℝ Y) (y : Space k) (t : ℝ) :
    HasDerivAt (fun s ↦ Y (point y s) (Fin.last k))
      (fderiv ℝ Y (point y t) (EuclideanSpace.single (Fin.last k) 1) (Fin.last k)) t := by
  have h2 := (hY (point y t)).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_point_right y t)
  have h3 := (EuclideanSpace.proj (𝕜 := ℝ) (Fin.last k)).hasFDerivAt.comp_hasDerivAt t h2
  exact h3

/-- Fubini decomposition with the vertical integral outside. -/
theorem integral_space_eq_integral_vertical_horizontal {k : ℕ}
    {g : Space (k + 1) → ℝ} (hg : Integrable g volume) :
    (∫ x, g x) = ∫ t : ℝ, ∫ y : Space k, g (point y t) := by
  let Q : Space k × ℝ → ℝ := fun p ↦ g (point p.1 p.2)
  have hmp := measurePreserving_point k
  have hQi : Integrable Q ((volume : Measure (Space k)).prod volume) :=
    hmp.integrable_comp_of_integrable hg
  have hmap := integral_map hmp.measurable.aemeasurable
    (show AEStronglyMeasurable g
      (Measure.map (fun p : Space k × ℝ ↦ point p.1 p.2)
        ((volume : Measure (Space k)).prod volume))
      from by rw [hmp.map_eq]; exact hg.aestronglyMeasurable)
  rw [hmp.map_eq] at hmap
  rw [hmap, integral_prod_symm _ hQi]

/-- **Slicing identity.** For a measurable phase `W ⊆ Space (k + 1)` and a compactly supported
`C¹` field `Y`, the divergence pairing splits into horizontal slice pairings, integrated in the
height, plus vertical profile derivatives, integrated over the horizontal variable. -/
theorem integral_indicator_mul_fieldDivergence_eq_slices {k : ℕ} {W : Set (Space (k + 1))}
    (hW : MeasurableSet W) {Y : Space (k + 1) → Space (k + 1)} (hY : ContDiff ℝ 1 Y)
    (hc : HasCompactSupport Y) :
    (∫ x, W.indicator (fun _ ↦ (1 : ℝ)) x *
        fieldDivergence (EuclideanSpace.basisFun (Fin (k + 1)) ℝ) Y x) =
      (∫ t : ℝ, ∫ y : Space k, W.indicator (fun _ ↦ (1 : ℝ)) (point y t) *
        fieldDivergence (EuclideanSpace.basisFun (Fin k) ℝ)
          (fun z ↦ horizontal (Y (point z t))) y) +
      ∫ y : Space k, ∫ t : ℝ, W.indicator (fun _ ↦ (1 : ℝ)) (point y t) *
        deriv (fun s ↦ Y (point y s) (Fin.last k)) t := by
  have hYd : Differentiable ℝ Y := hY.differentiable one_ne_zero
  have hDY : Continuous (fderiv ℝ Y) := hY.continuous_fderiv one_ne_zero
  set χ : Space (k + 1) → ℝ := W.indicator (fun _ ↦ (1 : ℝ)) with hχ
  set Hh : Space (k + 1) → ℝ := fun x ↦
    ∑ j : Fin k, fderiv ℝ Y x (EuclideanSpace.single j.castSucc 1) j.castSucc with hHh
  set Hv : Space (k + 1) → ℝ := fun x ↦
    fderiv ℝ Y x (EuclideanSpace.single (Fin.last k) 1) (Fin.last k) with hHv
  have hdiv (x : Space (k + 1)) :
      fieldDivergence (EuclideanSpace.basisFun (Fin (k + 1)) ℝ) Y x = Hh x + Hv x := by
    rw [fieldDivergence_basisFun_eq_sum, Fin.sum_univ_castSucc]
  have hHh_cont : Continuous Hh := by
    refine continuous_finsetSum _ fun j _ ↦ ?_
    exact (PiLp.continuous_apply 2 (fun _ : Fin (k + 1) ↦ ℝ) j.castSucc).comp
      (hDY.clm_apply continuous_const)
  have hHv_cont : Continuous Hv :=
    (PiLp.continuous_apply 2 (fun _ : Fin (k + 1) ↦ ℝ) (Fin.last k)).comp
      (hDY.clm_apply continuous_const)
  have hzero (x : Space (k + 1)) (hx : x ∉ tsupport Y) : fderiv ℝ Y x = 0 :=
    fderiv_of_notMem_tsupport ℝ hx
  have hHh_c : HasCompactSupport Hh := by
    refine hc.mono' fun x hx ↦ ?_
    by_contra hxs
    exact hx (by simp [Hh, hzero x hxs])
  have hHv_c : HasCompactSupport Hv := by
    refine hc.mono' fun x hx ↦ ?_
    by_contra hxs
    exact hx (by simp [Hv, hzero x hxs])
  have hih : Integrable (fun x ↦ χ x * Hh x) volume := by
    have hi := (hHh_cont.integrable_of_hasCompactSupport (μ := volume) hHh_c).indicator hW
    refine hi.congr (Eventually.of_forall fun x ↦ ?_)
    by_cases hx : x ∈ W <;> simp [χ, hx]
  have hiv : Integrable (fun x ↦ χ x * Hv x) volume := by
    have hi := (hHv_cont.integrable_of_hasCompactSupport (μ := volume) hHv_c).indicator hW
    refine hi.congr (Eventually.of_forall fun x ↦ ?_)
    by_cases hx : x ∈ W <;> simp [χ, hx]
  have hsplit : (∫ x, χ x * fieldDivergence (EuclideanSpace.basisFun (Fin (k + 1)) ℝ) Y x) =
      (∫ x, χ x * Hh x) + ∫ x, χ x * Hv x := by
    rw [← integral_add hih hiv]
    congr 1
    funext x
    rw [hdiv x]
    ring
  have hh : (∫ x, χ x * Hh x) = ∫ t : ℝ, ∫ y : Space k, χ (point y t) * Hh (point y t) :=
    integral_space_eq_integral_vertical_horizontal hih
  have hv : (∫ x, χ x * Hv x) = ∫ y : Space k, ∫ t : ℝ, χ (point y t) * Hv (point y t) :=
    integral_space_eq_integral_horizontal_vertical hiv
  rw [hsplit, hh, hv]
  congr 1
  · congr 1
    funext t
    congr 1
    funext y
    rw [fieldDivergence_slice_eq hYd t y]
  · congr 1
    funext y
    congr 1
    funext t
    rw [(hasDerivAt_vertical_profile hYd y t).deriv]

/-! ### 3. Admissible test fields -/

/-- A single admissible test field bounds the variational perimeter from below. -/
private theorem ofReal_norm_integral_le_variationalPerimeter {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) (E : Set (Space d)) {U : Set (Space d)}
    {F : Space d → Space d} (hF : ContDiff ℝ 1 F) (hc : HasCompactSupport F)
    (hs : tsupport F ⊆ U) (hunit : ∀ x, ‖F x‖ ≤ 1) :
    ENNReal.ofReal ‖∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F x‖ ≤
      variationalPerimeter b E U := by
  unfold variationalPerimeter
  exact le_iSup_of_le F (le_iSup_of_le hF (le_iSup_of_le hc
    (le_iSup_of_le hs (le_iSup_of_le hunit le_rfl))))

/-- Real form of `ofReal_norm_integral_le_variationalPerimeter` for finite perimeter. -/
private theorem norm_integral_le_variationalPerimeter_toReal {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) (E : Set (Space d)) {U : Set (Space d)}
    (hP : variationalPerimeter b E U ≠ ⊤)
    {F : Space d → Space d} (hF : ContDiff ℝ 1 F) (hc : HasCompactSupport F)
    (hs : tsupport F ⊆ U) (hunit : ∀ x, ‖F x‖ ≤ 1) :
    ‖∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F x‖ ≤
      (variationalPerimeter b E U).toReal :=
  (ENNReal.ofReal_le_iff_le_toReal hP).mp
    (ofReal_norm_integral_le_variationalPerimeter b E hF hc hs hunit)

/-- To bound `c * P(E, U)` it suffices to bound `c` times every admissible test pairing. -/
private theorem mul_variationalPerimeter_le_of_forall {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) (E U : Set (Space d)) (c R : ℝ≥0∞)
    (h : ∀ F : Space d → Space d, ContDiff ℝ 1 F → HasCompactSupport F → tsupport F ⊆ U →
      (∀ x, ‖F x‖ ≤ 1) →
      c * ENNReal.ofReal ‖∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F x‖ ≤ R) :
    c * variationalPerimeter b E U ≤ R := by
  unfold variationalPerimeter
  simp only [ENNReal.mul_iSup]
  exact iSup_le fun F ↦ iSup_le fun hF ↦ iSup_le fun hc ↦ iSup_le fun hs ↦
    iSup_le fun hu ↦ h F hF hc hs hu

/-- Horizontal slices of a `C¹` field are `C¹`. -/
theorem contDiff_horizontal_slice {k : ℕ} {Y : Space (k + 1) → Space (k + 1)}
    (hY : ContDiff ℝ 1 Y) (t : ℝ) : ContDiff ℝ 1 (fun z ↦ horizontal (Y (point z t))) :=
  horizontalContinuousLinearMap.contDiff.comp (hY.comp (contDiff_point_left t))

private theorem tsupport_horizontal_slice_subset {k : ℕ} (Y : Space (k + 1) → Space (k + 1))
    (t : ℝ) : tsupport (fun z ↦ horizontal (Y (point z t))) ⊆
      (fun z ↦ point z t) ⁻¹' tsupport Y := by
  apply closure_minimal _ ((isClosed_tsupport Y).preimage (continuous_point_left t))
  intro z hz
  apply subset_tsupport Y
  intro h0
  apply hz
  simp [h0, horizontal_zero]

/-- Horizontal slices of a compactly supported field are compactly supported. -/
theorem hasCompactSupport_horizontal_slice {k : ℕ} {Y : Space (k + 1) → Space (k + 1)}
    (hc : HasCompactSupport Y) (t : ℝ) :
    HasCompactSupport (fun z ↦ horizontal (Y (point z t))) :=
  (hc.image continuous_horizontal).of_isClosed_subset (isClosed_tsupport _)
    (fun z hz ↦ ⟨point z t, tsupport_horizontal_slice_subset Y t hz, horizontal_point z t⟩)

/-- Vertical profiles of a `C¹` field are `C¹`. -/
theorem contDiff_vertical_profile {k : ℕ} {Y : Space (k + 1) → Space (k + 1)}
    (hY : ContDiff ℝ 1 Y) (y : Space k) : ContDiff ℝ 1 (fun s ↦ Y (point y s) (Fin.last k)) := by
  have hpt : ContDiff ℝ 1 (fun s : ℝ ↦ point y s) := by
    have h : (fun s : ℝ ↦ point y s) = fun s ↦ point y 0 + s • verticalDirection k := by
      funext s
      rw [point_add_vertical]
      simp
    rw [h]
    exact contDiff_const.add (contDiff_id.smul contDiff_const)
  exact (EuclideanSpace.proj (𝕜 := ℝ) (Fin.last k)).contDiff.comp (hY.comp hpt)

/-- Vertical profiles of a compactly supported field are compactly supported. -/
theorem hasCompactSupport_vertical_profile {k : ℕ} {Y : Space (k + 1) → Space (k + 1)}
    (hc : HasCompactSupport Y) (y : Space k) :
    HasCompactSupport (fun s ↦ Y (point y s) (Fin.last k)) := by
  have hK : IsCompact ((fun x : Space (k + 1) ↦ x (Fin.last k)) '' tsupport Y) :=
    hc.image (PiLp.continuous_apply 2 (fun _ : Fin (k + 1) ↦ ℝ) (Fin.last k))
  refine hK.of_isClosed_subset (isClosed_tsupport _)
    (closure_minimal (fun s hs ↦ ?_) hK.isClosed)
  have hs' : Y (point y s) (Fin.last k) ≠ 0 := hs
  refine ⟨point y s, subset_tsupport Y fun h0 ↦ hs' ?_, last_point y s⟩
  simp [h0]

/-- Horizontal slices of a test field on `cylinderSet U H` are test fields on `U`. -/
private theorem slice_testField {k : ℕ} {Y : Space (k + 1) → Space (k + 1)} (hY : ContDiff ℝ 1 Y)
    (hc : HasCompactSupport Y) {U : Set (Space k)} {H : ℝ} (hs : tsupport Y ⊆ cylinderSet U H)
    (hunit : ∀ x, ‖Y x‖ ≤ 1) (t : ℝ) :
    ContDiff ℝ 1 (fun z ↦ horizontal (Y (point z t))) ∧
      HasCompactSupport (fun z ↦ horizontal (Y (point z t))) ∧
      tsupport (fun z ↦ horizontal (Y (point z t))) ⊆ U ∧
      ∀ z, ‖horizontal (Y (point z t))‖ ≤ 1 := by
  refine ⟨contDiff_horizontal_slice hY t, hasCompactSupport_horizontal_slice hc t,
    fun z hz ↦ ?_, fun z ↦ (norm_horizontal_le_norm _).trans (hunit _)⟩
  have h1 := hs (tsupport_horizontal_slice_subset Y t hz)
  simpa using h1.1

/-- A test field on `cylinderSet U H` vanishes above horizontal points outside `U` and at heights
`|t| ≥ H`. -/
private theorem eq_zero_of_tsupport_subset_cylinderSet {k : ℕ} {Y : Space (k + 1) → Space (k + 1)}
    {U : Set (Space k)} {H : ℝ} (hs : tsupport Y ⊆ cylinderSet U H) {y : Space k} {t : ℝ}
    (h : y ∉ U ∨ H ≤ |t|) : Y (point y t) = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  have h1 := hs hmem
  rw [point_mem_cylinderSet] at h1
  rcases h with hy | ht
  · exact hy h1.1
  · have h2 : |t| < H := abs_lt.mpr h1.2
    linarith

/-! ### 4. Lower bound for cylinders -/

/-- A smooth plateau equal to one on `[-L, L]` and supported in `(-L - 1, L + 1)`. -/
private def plateauBump (L : ℝ) (hL : 0 ≤ L) : ContDiffBump (0 : ℝ) where
  rIn := L + 1 / 3
  rOut := L + 2 / 3
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

private theorem plateauBump_rIn (L : ℝ) (hL : 0 ≤ L) : (plateauBump L hL).rIn = L + 1 / 3 := rfl

private theorem plateauBump_rOut (L : ℝ) (hL : 0 ≤ L) : (plateauBump L hL).rOut = L + 2 / 3 := rfl

private theorem two_mul_le_integral_plateauBump {L : ℝ} (hL : 0 ≤ L) :
    2 * L ≤ ∫ t, plateauBump L hL t := by
  set ψ := plateauBump L hL with hψ
  have hint : Integrable (fun t ↦ ψ t) volume :=
    ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport
  have hone : ∀ t ∈ Icc (-L) L, ψ t = 1 := fun t ht ↦ by
    apply ψ.one_of_mem_closedBall
    rw [mem_closedBall, dist_zero_right, Real.norm_eq_abs, hψ, plateauBump_rIn]
    have := abs_le.mpr ht
    linarith
  have h1 : (∫ t in Icc (-L) L, ψ t) = 2 * L := by
    rw [setIntegral_congr_fun measurableSet_Icc hone, setIntegral_const,
      Real.volume_real_Icc_of_le (by linarith), smul_eq_mul, mul_one]
    ring
  calc 2 * L = ∫ t in Icc (-L) L, ψ t := h1.symm
    _ ≤ ∫ t, ψ t := setIntegral_le_integral hint (Eventually.of_forall fun t ↦ ψ.nonneg)

private theorem point_zero_zero_eq {k : ℕ} : point (0 : Space k) 0 = 0 := by
  simpa using (horizontalEmbedding k).map_zero

/-- **Cylinder lower bound.** Every test pairing of `A` on `U` lifts, through a vertical plateau,
to a test pairing of the cylinder over `A` on `cylinderSet U (L + 1)` with weight at least
`2 L`. -/
theorem ofReal_two_mul_variationalPerimeter_le_cylinder {k : ℕ}
    (b : OrthonormalBasis (Fin (k + 1)) ℝ (Space (k + 1)))
    (b' : OrthonormalBasis (Fin k) ℝ (Space k)) {A U : Set (Space k)}
    (hA : MeasurableSet A) {L : ℝ} (hL : 0 ≤ L) :
    ENNReal.ofReal (2 * L) * variationalPerimeter b' A U ≤
      variationalPerimeter b (horizontal ⁻¹' A) (cylinderSet U (L + 1)) := by
  rw [variationalPerimeter_basis_independent b' (EuclideanSpace.basisFun (Fin k) ℝ),
    variationalPerimeter_basis_independent b (EuclideanSpace.basisFun (Fin (k + 1)) ℝ)]
  refine mul_variationalPerimeter_le_of_forall _ _ _ _ _ fun X hX hXc hXs hXu ↦ ?_
  set ψ := plateauBump L hL with hψ
  set Y : Space (k + 1) → Space (k + 1) := fun x ↦
    ψ (x (Fin.last k)) • point (X (horizontal x)) 0 with hYdef
  have hYc1 : ContDiff ℝ 1 Y := by
    have h1 : ContDiff ℝ 1 (fun x : Space (k + 1) ↦ ψ (x (Fin.last k))) :=
      ψ.contDiff.comp (EuclideanSpace.proj (𝕜 := ℝ) (Fin.last k)).contDiff
    have h2 : ContDiff ℝ 1 (fun x : Space (k + 1) ↦ point (X (horizontal x)) 0) :=
      (horizontalEmbedding k).contDiff.comp (hX.comp horizontalContinuousLinearMap.contDiff)
    exact h1.smul h2
  set S : Set (Space (k + 1)) :=
    {x | horizontal x ∈ tsupport X ∧ |x (Fin.last k)| ≤ L + 2 / 3} with hS
  have hS_closed : IsClosed S :=
    ((isClosed_tsupport X).preimage continuous_horizontal).inter
      (isClosed_le (continuous_abs.comp (PiLp.continuous_apply 2 (fun _ : Fin (k + 1) ↦ ℝ)
        (Fin.last k))) continuous_const)
  obtain ⟨RX, hRX⟩ := hXc.isBounded.subset_closedBall (0 : Space k)
  have hS_bdd : Bornology.IsBounded S := by
    refine (Metric.isBounded_closedBall (x := (0 : Space (k + 1)))
      (r := RX + (L + 2 / 3))).subset fun x hx ↦ ?_
    have h1 : ‖horizontal x‖ ≤ RX := by simpa using hRX hx.1
    rw [mem_closedBall, dist_zero_right]
    linarith [norm_le_norm_horizontal_add_abs_last x, hx.2]
  have hYS : tsupport Y ⊆ S := by
    refine closure_minimal (fun x hx ↦ ?_) hS_closed
    have hx' : ψ (x (Fin.last k)) • point (X (horizontal x)) 0 ≠ 0 := hx
    rw [smul_ne_zero_iff] at hx'
    obtain ⟨hψx, hXx⟩ := hx'
    refine ⟨subset_tsupport X fun h0 ↦ hXx (by simp [h0, point_zero_zero_eq]), ?_⟩
    have hmem : x (Fin.last k) ∈ Function.support ψ := hψx
    rw [ψ.support_eq, mem_ball, dist_zero_right, Real.norm_eq_abs, hψ, plateauBump_rOut] at hmem
    exact hmem.le
  have hYcpt : HasCompactSupport Y :=
    (Metric.isCompact_of_isClosed_isBounded hS_closed hS_bdd).of_isClosed_subset
      (isClosed_tsupport _) hYS
  have hYU : tsupport Y ⊆ cylinderSet U (L + 1) := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := hYS hx
    refine ⟨hXs hx1, ?_⟩
    have : |x (Fin.last k)| < L + 1 := by linarith
    exact abs_lt.mp this
  have hYu : ∀ x, ‖Y x‖ ≤ 1 := by
    intro x
    change ‖ψ (x (Fin.last k)) • point (X (horizontal x)) 0‖ ≤ 1
    rw [norm_smul, Real.norm_of_nonneg ψ.nonneg, norm_point_zero]
    exact (mul_le_mul ψ.le_one (hXu _) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hslice := integral_indicator_mul_fieldDivergence_eq_slices
    (W := horizontal ⁻¹' A) (hA.preimage continuous_horizontal.measurable) hYc1 hYcpt
  have hsl (t : ℝ) : (fun z ↦ horizontal (Y (point z t))) = ψ t • X := by
    funext z
    simp [Y, horizontal_smul_space]
  have hprof (y : Space k) : (fun s ↦ Y (point y s) (Fin.last k)) = fun _ ↦ 0 := by
    funext s
    simp [Y]
  have hind (y : Space k) (t : ℝ) :
      (horizontal ⁻¹' A).indicator (fun _ ↦ (1 : ℝ)) (point y t) =
        A.indicator (fun _ ↦ (1 : ℝ)) y := by
    by_cases hy : y ∈ A <;> simp [hy]
  have hdivs (t : ℝ) (y : Space k) :
      fieldDivergence (EuclideanSpace.basisFun (Fin k) ℝ) (ψ t • X) y =
        ψ t * fieldDivergence (EuclideanSpace.basisFun (Fin k) ℝ) X y :=
    fieldDivergence_const_smul _ hX _ _
  have hinner (t : ℝ) :
      (∫ y, A.indicator (fun _ ↦ (1 : ℝ)) y *
          (ψ t * fieldDivergence (EuclideanSpace.basisFun (Fin k) ℝ) X y)) =
        ψ t * ∫ y, A.indicator (fun _ ↦ (1 : ℝ)) y *
          fieldDivergence (EuclideanSpace.basisFun (Fin k) ℝ) X y := by
    rw [← integral_const_mul]
    congr 1
    funext y
    ring
  simp only [hsl, hprof, hind, hdivs, hinner, deriv_const', mul_zero, integral_zero,
    add_zero, integral_mul_const] at hslice
  have hint := two_mul_le_integral_plateauBump hL
  set I := ∫ y, A.indicator (fun _ ↦ (1 : ℝ)) y *
    fieldDivergence (EuclideanSpace.basisFun (Fin k) ℝ) X y with hI
  calc ENNReal.ofReal (2 * L) * ENNReal.ofReal ‖I‖ = ENNReal.ofReal (2 * L * ‖I‖) :=
        (ENNReal.ofReal_mul (by positivity)).symm
    _ ≤ ENNReal.ofReal ‖(∫ t, ψ t) * I‖ := by
        apply ENNReal.ofReal_le_ofReal
        rw [norm_mul, Real.norm_of_nonneg (le_trans (by positivity) hint)]
        exact mul_le_mul_of_nonneg_right hint (norm_nonneg _)
    _ = ENNReal.ofReal ‖∫ x, (horizontal ⁻¹' A).indicator (fun _ ↦ (1 : ℝ)) x *
          fieldDivergence (EuclideanSpace.basisFun (Fin (k + 1)) ℝ) Y x‖ := by
        rw [hslice]
    _ ≤ variationalPerimeter (EuclideanSpace.basisFun (Fin (k + 1)) ℝ) (horizontal ⁻¹' A)
          (cylinderSet U (L + 1)) :=
        ofReal_norm_integral_le_variationalPerimeter _ _ hYc1 hYcpt hYU hYu

/-! ### 5. Upper bound for layered competitors -/

/-- The layered competitor: `G` inside the slab `|x_last| < L`, and `A` outside it. -/
def layeredSet {k : ℕ} (A G : Set (Space k)) (L : ℝ) : Set (Space (k + 1)) :=
  {x | (|x (Fin.last k)| < L ∧ horizontal x ∈ G) ∨ (L ≤ |x (Fin.last k)| ∧ horizontal x ∈ A)}

theorem measurableSet_layeredSet {k : ℕ} {A G : Set (Space k)} (hA : MeasurableSet A)
    (hG : MeasurableSet G) (L : ℝ) : MeasurableSet (layeredSet A G L) := by
  have hlast : Measurable (fun x : Space (k + 1) ↦ |x (Fin.last k)|) :=
    (continuous_abs.comp (PiLp.continuous_apply 2 (fun _ : Fin (k + 1) ↦ ℝ)
      (Fin.last k))).measurable
  have hh : Measurable (horizontal : Space (k + 1) → Space k) := continuous_horizontal.measurable
  exact ((measurableSet_lt hlast measurable_const).inter (hG.preimage hh)).union
    ((measurableSet_le measurable_const hlast).inter (hA.preimage hh))

theorem indicator_layeredSet_point {k : ℕ} (A G : Set (Space k)) (L : ℝ) (y : Space k)
    (t : ℝ) :
    (layeredSet A G L).indicator (fun _ ↦ (1 : ℝ)) (point y t) =
      if |t| < L then G.indicator (fun _ ↦ (1 : ℝ)) y else A.indicator (fun _ ↦ (1 : ℝ)) y := by
  by_cases ht : |t| < L
  · have hn : ¬ L ≤ |t| := not_le.mpr ht
    by_cases hy : y ∈ G <;> simp [layeredSet, ht, hn, hy]
  · have hn : L ≤ |t| := le_of_not_gt ht
    by_cases hy : y ∈ A <;> simp [layeredSet, ht, hn, hy]

/-- Integrating a two-valued height step against the derivative of a compactly supported
profile only sees the two jumps at heights `± L`. -/
private theorem integral_step_mul_deriv {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hfc : HasCompactSupport f) {L : ℝ} (hL : 0 ≤ L) (a g : ℝ) :
    (∫ t, (if |t| < L then g else a) * deriv f t) = (g - a) * (f L - f (-L)) := by
  have hfd : ∀ t, HasDerivAt f (deriv f t) t := fun t ↦
    ((hf.differentiable one_ne_zero) t).hasDerivAt
  have hf'c : Continuous (deriv f) := hf.continuous_deriv le_rfl
  have hf'i : Integrable (deriv f) volume :=
    hf'c.integrable_of_hasCompactSupport hfc.deriv
  have hfi : Integrable f volume := hf.continuous.integrable_of_hasCompactSupport hfc
  have hzero : (∫ t, deriv f t) = 0 := integral_eq_zero_of_hasDerivAt_of_integrable hfd hf'i hfi
  have hIoo : (∫ t in Ioo (-L) L, deriv f t) = f L - f (-L) := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith)]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hfd t)
      (hf'c.intervalIntegrable _ _)
  have hpt : (fun t ↦ (if |t| < L then g else a) * deriv f t) =
      fun t ↦ a * deriv f t + (g - a) * (Ioo (-L) L).indicator (deriv f) t := by
    funext t
    by_cases ht : |t| < L
    · have htm : t ∈ Ioo (-L) L := abs_lt.mp ht
      simp only [ht, ite_true, htm, indicator_of_mem]
      ring
    · have htm : t ∉ Ioo (-L) L := fun h ↦ ht (abs_lt.mpr h)
      simp [ht, htm]
  rw [hpt, integral_add (hf'i.const_mul a) ((hf'i.indicator measurableSet_Ioo).const_mul _),
    integral_const_mul, integral_const_mul, integral_indicator measurableSet_Ioo, hzero, hIoo]
  ring

/-- **Layered competitor upper bound.** Inside `cylinderSet U (L + 1)`, the layered competitor
equal to `G` on the slab `|x_last| < L` and to `A` elsewhere has perimeter at most
`2 L P(G, U) + 2 P(A, U) + 2 |(A ∆ G) ∩ U|`. -/
theorem variationalPerimeter_layeredSet_le {k : ℕ}
    (b : OrthonormalBasis (Fin (k + 1)) ℝ (Space (k + 1)))
    (b' : OrthonormalBasis (Fin k) ℝ (Space k)) {A G U : Set (Space k)}
    (hA : MeasurableSet A) (hG : MeasurableSet G) (hU : IsOpen U) {L : ℝ} (hL : 0 ≤ L)
    (hPA : variationalPerimeter b' A U ≠ ⊤) (hPG : variationalPerimeter b' G U ≠ ⊤)
    (hV : volume (symmDiff A G ∩ U) ≠ ⊤) :
    variationalPerimeter b (layeredSet A G L) (cylinderSet U (L + 1)) ≤
      ENNReal.ofReal (2 * L * (variationalPerimeter b' G U).toReal +
        2 * (variationalPerimeter b' A U).toReal + 2 * volume.real (symmDiff A G ∩ U)) := by
  set b₀ := EuclideanSpace.basisFun (Fin k) ℝ with hb₀
  rw [variationalPerimeter_basis_independent b' b₀ A U] at hPA ⊢
  rw [variationalPerimeter_basis_independent b' b₀ G U] at hPG ⊢
  rw [variationalPerimeter_basis_independent b (EuclideanSpace.basisFun (Fin (k + 1)) ℝ)]
  set pA := (variationalPerimeter b₀ A U).toReal with hpA
  set pG := (variationalPerimeter b₀ G U).toReal with hpG
  set S := symmDiff A G ∩ U with hSdef
  have hSmeas : MeasurableSet S := (hA.symmDiff hG).inter hU.measurableSet
  have hpA0 : 0 ≤ pA := ENNReal.toReal_nonneg
  have hpG0 : 0 ≤ pG := ENNReal.toReal_nonneg
  have hW : MeasurableSet (layeredSet A G L) := measurableSet_layeredSet hA hG L
  have key : ∀ Y : Space (k + 1) → Space (k + 1), ContDiff ℝ 1 Y → HasCompactSupport Y →
      tsupport Y ⊆ cylinderSet U (L + 1) → (∀ x, ‖Y x‖ ≤ 1) →
      ‖∫ x, (layeredSet A G L).indicator (fun _ ↦ (1 : ℝ)) x *
          fieldDivergence (EuclideanSpace.basisFun (Fin (k + 1)) ℝ) Y x‖ ≤
        2 * L * pG + 2 * pA + 2 * volume.real S := by
    intro Y hY hYc hYs hYu
    rw [integral_indicator_mul_fieldDivergence_eq_slices hW hY hYc]
    simp only [indicator_layeredSet_point]
    -- horizontal part
    set h : ℝ → ℝ := fun t ↦ (Ioo (-L) L).indicator (fun _ ↦ pG) t +
      (Ioo (-(L + 1)) (L + 1) \ Ioo (-L) L).indicator (fun _ ↦ pA) t with hhdef
    have hsub : Ioo (-L) L ⊆ Ioo (-(L + 1)) (L + 1) := Ioo_subset_Ioo (by linarith) (by linarith)
    have hh_int : Integrable h volume := by
      refine Integrable.add ?_ ?_
      · exact (integrableOn_const (by simp [Real.volume_Ioo])).integrable_indicator
          measurableSet_Ioo
      · exact (integrableOn_const (measure_ne_top_of_subset sdiff_subset
          (by simp [Real.volume_Ioo]))).integrable_indicator
          (measurableSet_Ioo.diff measurableSet_Ioo)
    have hh_val : (∫ t, h t) = 2 * L * pG + 2 * pA := by
      rw [integral_add ((integrableOn_const (by simp [Real.volume_Ioo])).integrable_indicator
          measurableSet_Ioo)
        ((integrableOn_const (measure_ne_top_of_subset sdiff_subset
          (by simp [Real.volume_Ioo]))).integrable_indicator
          (measurableSet_Ioo.diff measurableSet_Ioo)),
        integral_indicator_const _ measurableSet_Ioo,
        integral_indicator_const _ (measurableSet_Ioo.diff measurableSet_Ioo),
        measureReal_sdiff hsub measurableSet_Ioo (by simp [Real.volume_Ioo]),
        Real.volume_real_Ioo_of_le (by linarith), Real.volume_real_Ioo_of_le (by linarith),
        smul_eq_mul, smul_eq_mul]
      ring
    have hIh : ‖∫ t : ℝ, ∫ y : Space k,
        (if |t| < L then G.indicator (fun _ ↦ (1 : ℝ)) y else A.indicator (fun _ ↦ (1 : ℝ)) y) *
          fieldDivergence b₀ (fun z ↦ horizontal (Y (point z t))) y‖ ≤ 2 * L * pG + 2 * pA := by
      rw [← hh_val]
      refine norm_integral_le_of_norm_le hh_int (Eventually.of_forall fun t ↦ ?_)
      obtain ⟨hsc, hscc, hscs, hscu⟩ := slice_testField hY hYc hYs hYu t
      by_cases ht : |t| < L
      · have htm : t ∈ Ioo (-L) L := abs_lt.mp ht
        have htd : t ∉ Ioo (-(L + 1)) (L + 1) \ Ioo (-L) L := fun h ↦ h.2 htm
        simp only [ht, ite_true, hhdef, indicator_of_mem htm, indicator_of_notMem htd, add_zero]
        exact norm_integral_le_variationalPerimeter_toReal b₀ G hPG hsc hscc hscs hscu
      · by_cases ht' : |t| < L + 1
        · have htm : t ∉ Ioo (-L) L := fun h ↦ ht (abs_lt.mpr h)
          have htd : t ∈ Ioo (-(L + 1)) (L + 1) \ Ioo (-L) L := ⟨abs_lt.mp ht', htm⟩
          simp only [ht, ite_false, hhdef, indicator_of_notMem htm, indicator_of_mem htd, zero_add]
          exact norm_integral_le_variationalPerimeter_toReal b₀ A hPA hsc hscc hscs hscu
        · have hzero : (fun z ↦ horizontal (Y (point z t))) = fun _ ↦ 0 := by
            funext z
            rw [eq_zero_of_tsupport_subset_cylinderSet hYs (Or.inr (le_of_not_gt ht')),
              horizontal_zero]
          have hdiv0 : ∀ y, fieldDivergence b₀ (fun z ↦ horizontal (Y (point z t))) y = 0 := by
            intro y
            rw [hzero]
            simp [fieldDivergence]
          simp only [hdiv0, mul_zero, integral_zero, norm_zero]
          exact add_nonneg (indicator_nonneg (fun _ _ ↦ hpG0) _)
            (indicator_nonneg (fun _ _ ↦ hpA0) _)
    -- vertical part
    have hS_int : Integrable (S.indicator (fun _ ↦ (2 : ℝ))) volume :=
      (integrableOn_const hV).integrable_indicator hSmeas
    have hIv : ‖∫ y : Space k, ∫ t : ℝ,
        (if |t| < L then G.indicator (fun _ ↦ (1 : ℝ)) y else A.indicator (fun _ ↦ (1 : ℝ)) y) *
          deriv (fun s ↦ Y (point y s) (Fin.last k)) t‖ ≤ 2 * volume.real S := by
      have hval : (∫ y, S.indicator (fun _ ↦ (2 : ℝ)) y) = 2 * volume.real S := by
        rw [integral_indicator_const _ hSmeas, smul_eq_mul, mul_comm]
      rw [← hval]
      refine norm_integral_le_of_norm_le hS_int (Eventually.of_forall fun y ↦ ?_)
      by_cases hyU : y ∈ U
      · set f : ℝ → ℝ := fun s ↦ Y (point y s) (Fin.last k) with hfdef
        have hfc1 : ContDiff ℝ 1 f := contDiff_vertical_profile hY y
        have hfcs : HasCompactSupport f := hasCompactSupport_vertical_profile hYc y
        have hf1 : ∀ s, |f s| ≤ 1 := fun s ↦ (abs_last_le_norm _).trans (hYu _)
        have hb : |f L - f (-L)| ≤ 2 := by
          have h1 := abs_le.mp (hf1 L)
          have h2 := abs_le.mp (hf1 (-L))
          exact abs_le.mpr ⟨by linarith, by linarith⟩
        rw [integral_step_mul_deriv hfc1 hfcs hL]
        by_cases hyA : y ∈ A <;> by_cases hyG : y ∈ G
        · have hyS : y ∉ S := fun h ↦
            (mem_symmDiff.mp h.1).elim (fun h' ↦ h'.2 hyG) (fun h' ↦ h'.2 hyA)
          simp [hyA, hyG, hyS]
        · have hyS : y ∈ S := ⟨mem_symmDiff.mpr (Or.inl ⟨hyA, hyG⟩), hyU⟩
          simp only [indicator_of_mem hyA, indicator_of_notMem hyG, indicator_of_mem hyS,
            Real.norm_eq_abs, abs_mul]
          norm_num
          exact hb
        · have hyS : y ∈ S := ⟨mem_symmDiff.mpr (Or.inr ⟨hyG, hyA⟩), hyU⟩
          simp only [indicator_of_notMem hyA, indicator_of_mem hyG, indicator_of_mem hyS,
            Real.norm_eq_abs, abs_mul]
          norm_num
          exact hb
        · have hyS : y ∉ S := fun h ↦
            (mem_symmDiff.mp h.1).elim (fun h' ↦ hyA h'.1) (fun h' ↦ hyG h'.1)
          simp [hyA, hyG, hyS]
      · have hprof : (fun s ↦ Y (point y s) (Fin.last k)) = fun _ ↦ 0 := by
          funext s
          rw [eq_zero_of_tsupport_subset_cylinderSet hYs (Or.inl hyU)]
          rfl
        have hyS : y ∉ S := fun h ↦ hyU h.2
        simp [hprof, hyS]
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ 2 * L * pG + 2 * pA + 2 * volume.real S := by linarith
  have h1 := mul_variationalPerimeter_le_of_forall (EuclideanSpace.basisFun (Fin (k + 1)) ℝ)
    (layeredSet A G L) (cylinderSet U (L + 1)) 1
    (ENNReal.ofReal (2 * L * pG + 2 * pA + 2 * volume.real S))
    (fun Y hY hYc hYs hYu ↦ by
      rw [one_mul]
      exact ENNReal.ofReal_le_ofReal (key Y hY hYc hYs hYu))
  simpa using h1

/-! ### 6. Volume of cylinders -/

/-- Volume of the cylinder over a measurable horizontal set. -/
theorem volume_preimage_horizontal {k : ℕ} {A : Set (Space k)} (hA : MeasurableSet A) :
    volume (horizontal ⁻¹' A : Set (Space (k + 1))) = volume A * ⊤ := by
  have hσ := measurePreserving_horizontal_last k
  have hpre : (horizontal ⁻¹' A : Set (Space (k + 1))) =
      (fun x : Space (k + 1) ↦ (horizontal x, x (Fin.last k))) ⁻¹' (A ×ˢ univ) := by
    ext x
    simp
  rw [hpre, hσ.measure_preimage (hA.prod MeasurableSet.univ).nullMeasurableSet,
    Measure.prod_prod, Real.volume_univ]

theorem volume_preimage_horizontal_eq_zero_iff {k : ℕ} {A : Set (Space k)}
    (hA : MeasurableSet A) :
    volume (horizontal ⁻¹' A : Set (Space (k + 1))) = 0 ↔ volume A = 0 := by
  rw [volume_preimage_horizontal hA, mul_eq_zero]
  simp

/-- Cylinders over null sets are null. -/
theorem volume_preimage_horizontal_eq_zero {k : ℕ} {N : Set (Space k)} (hN : volume N = 0) :
    volume (horizontal ⁻¹' N : Set (Space (k + 1))) = 0 := by
  have hM := measurableSet_toMeasurable volume N
  have h0 : volume (toMeasurable volume N) = 0 := by rw [measure_toMeasurable]; exact hN
  exact measure_mono_null (preimage_mono (subset_toMeasurable volume N))
    ((volume_preimage_horizontal_eq_zero_iff hM).mpr h0)

/-- Almost-everywhere horizontal statements lift to cylinders. -/
theorem ae_comp_horizontal {k : ℕ} {P : Space k → Prop} (h : ∀ᵐ y ∂volume, P y) :
    ∀ᵐ x ∂(volume : Measure (Space (k + 1))), P (horizontal x) := by
  rw [ae_iff] at h ⊢
  exact volume_preimage_horizontal_eq_zero h

/-- Almost-everywhere equal horizontal sets have almost-everywhere equal cylinders. -/
theorem preimage_horizontal_ae_eq {k : ℕ} {A B : Set (Space k)} (h : A =ᵐ[volume] B) :
    (horizontal ⁻¹' A : Set (Space (k + 1))) =ᵐ[volume] (horizontal ⁻¹' B) := by
  have h' : ∀ᵐ y ∂volume, y ∈ A ↔ y ∈ B := by
    filter_upwards [h] with y hy
    exact Iff.of_eq hy
  filter_upwards [ae_comp_horizontal (k := k) h'] with x hx
  exact propext hx

/-! ### 7. GR6: minimality of the cross-section -/

/-- **GR6 (cross-section minimality).** If the cylinder over `A ⊆ Space k` is a local perimeter
minimizer in `Space (k + 1)`, then `A` is a local perimeter minimizer in `Space k`.

Compare the cylinder with the layered competitor `G` on `|x_last| < L` and `A` elsewhere inside
`cylinderSet B (L + 1)`: the cylinder lower bound and the layered upper bound give
`2 L P(A, B) ≤ 2 L P(G, B) + 2 P(A, B) + 2 |(A ∆ G) ∩ B|`; divide by `2 L` and let `L → ∞`. -/
theorem IsLocalPerimeterMinimizer.of_preimage_horizontal {k : ℕ}
    {b : OrthonormalBasis (Fin (k + 1)) ℝ (Space (k + 1))}
    (b' : OrthonormalBasis (Fin k) ℝ (Space k)) {A : Set (Space k)} (hA : MeasurableSet A)
    (h : IsLocalPerimeterMinimizer b (horizontal ⁻¹' A) univ) :
    IsLocalPerimeterMinimizer b' A univ := by
  have hfin : ∀ R : ℝ, 0 < R → variationalPerimeter b' A (ball 0 R) ≠ ⊤ := by
    intro R hR
    have hlow := ofReal_two_mul_variationalPerimeter_le_cylinder b b' (U := ball (0 : Space k) R)
      hA zero_le_one
    have hsub : cylinderSet (ball (0 : Space k) R) (1 + 1) ⊆ ball 0 (R + 2) := by
      intro x hx
      obtain ⟨hx1, hx2⟩ := hx
      have h1 : ‖horizontal x‖ < R := by simpa using hx1
      have h2 : |x (Fin.last k)| < 2 := by
        have := abs_lt.mpr hx2
        linarith
      rw [mem_ball, dist_zero_right]
      linarith [norm_le_norm_horizontal_add_abs_last x]
    have hcyl : variationalPerimeter b (horizontal ⁻¹' A)
        (cylinderSet (ball (0 : Space k) R) (1 + 1)) ≠ ⊤ :=
      ne_top_of_le_ne_top (h.perimeter_ball_ne_top 0 (R + 2) (by linarith) (subset_univ _))
        (variationalPerimeter_mono b _ hsub)
    intro htop
    rw [htop, ENNReal.mul_top (by norm_num)] at hlow
    exact hcyl (top_le_iff.mp hlow)
  have hball : ∀ R : ℝ, 0 < R → ∀ (G K : Set (Space k)), MeasurableSet G → IsCompact K →
      K ⊆ ball 0 R → (∀ᵐ y ∂volume, y ∉ K → (y ∈ A ↔ y ∈ G)) →
      variationalPerimeter b' A (ball 0 R) ≤ variationalPerimeter b' G (ball 0 R) := by
    intro R hR G K hG hK hKB hAG
    set B : Set (Space k) := ball 0 R with hBdef
    by_cases hPG : variationalPerimeter b' G B = ⊤
    · rw [hPG]
      exact le_top
    have hPA := hfin R hR
    have hVfin : volume (symmDiff A G ∩ B) ≠ ⊤ :=
      ((measure_mono inter_subset_right).trans_lt measure_ball_lt_top).ne
    set a := (variationalPerimeter b' A B).toReal with ha
    set g := (variationalPerimeter b' G B).toReal with hg
    set V := volume.real (symmDiff A G ∩ B) with hV
    have ha0 : 0 ≤ a := ENNReal.toReal_nonneg
    have hg0 : 0 ≤ g := ENNReal.toReal_nonneg
    have hV0 : 0 ≤ V := measureReal_nonneg
    obtain ⟨RK, hRK⟩ := hK.isBounded.subset_closedBall (0 : Space k)
    have hAG' : ∀ᵐ x ∂(volume : Measure (Space (k + 1))),
        horizontal x ∉ K → (horizontal x ∈ A ↔ horizontal x ∈ G) := ae_comp_horizontal hAG
    have hineq : ∀ L : ℝ, 1 ≤ L → 2 * L * a ≤ 2 * L * g + 2 * a + 2 * V := by
      intro L hL
      have hL0 : 0 ≤ L := by linarith
      have hW : MeasurableSet (layeredSet A G L) := measurableSet_layeredSet hA hG L
      set KL : Set (Space (k + 1)) := {x | horizontal x ∈ K ∧ |x (Fin.last k)| ≤ L} with hKLdef
      have hKL_closed : IsClosed KL :=
        (hK.isClosed.preimage continuous_horizontal).inter
          (isClosed_le (continuous_abs.comp (PiLp.continuous_apply 2 (fun _ : Fin (k + 1) ↦ ℝ)
            (Fin.last k))) continuous_const)
      have hKL_bdd : Bornology.IsBounded KL := by
        refine (Metric.isBounded_closedBall (x := (0 : Space (k + 1))) (r := RK + L)).subset
          fun x hx ↦ ?_
        have h1 : ‖horizontal x‖ ≤ RK := by simpa using hRK hx.1
        rw [mem_closedBall, dist_zero_right]
        linarith [norm_le_norm_horizontal_add_abs_last x, hx.2]
      have hKL : IsCompact KL := Metric.isCompact_of_isClosed_isBounded hKL_closed hKL_bdd
      have hKLsub : KL ⊆ cylinderSet B (L + 1) := by
        intro x hx
        refine ⟨hKB hx.1, abs_lt.mp ?_⟩
        linarith [hx.2]
      have hae : ∀ᵐ x ∂volume, x ∉ KL →
          (x ∈ horizontal ⁻¹' A ↔ x ∈ layeredSet A G L) := by
        filter_upwards [hAG'] with x hx hxKL
        simp only [mem_preimage, layeredSet, mem_ofPred_eq]
        by_cases ht : |x (Fin.last k)| < L
        · have hxK : horizontal x ∉ K := fun hK' ↦ hxKL ⟨hK', ht.le⟩
          rw [hx hxK]
          have hn : ¬ L ≤ |x (Fin.last k)| := not_le.mpr ht
          simp [ht, hn]
        · have hn : L ≤ |x (Fin.last k)| := le_of_not_gt ht
          simp [ht, hn]
      have hmin := h.minimizes (cylinderSet B (L + 1)) (layeredSet A G L) KL
        (isOpen_cylinderSet isOpen_ball _) (subset_univ _) hW hKL hKLsub hae
      have hlow := ofReal_two_mul_variationalPerimeter_le_cylinder b b' (U := B) hA hL0
      have hup := variationalPerimeter_layeredSet_le b b' hA hG isOpen_ball hL0 hPA hPG hVfin
      have hchain := hlow.trans (hmin.trans hup)
      have hPA' : variationalPerimeter b' A B ≠ ⊤ := hPA
      have hleft : ENNReal.ofReal (2 * L) * variationalPerimeter b' A B =
          ENNReal.ofReal (2 * L * a) := by
        rw [ENNReal.ofReal_mul (by linarith : (0 : ℝ) ≤ 2 * L), ha, ENNReal.ofReal_toReal hPA']
      rw [hleft] at hchain
      have hrhs : 0 ≤ 2 * L * g + 2 * a + 2 * V := by positivity
      exact (ENNReal.ofReal_le_ofReal_iff hrhs).mp hchain
    have hag : a ≤ g := by
      by_contra hlt
      have hpos : 0 < a - g := by linarith [lt_of_not_ge hlt]
      obtain ⟨n, hn⟩ := exists_nat_gt ((a + V) / (a - g))
      have hn' : (a + V) / (a - g) < (n : ℝ) + 1 := by linarith
      have hmul : a + V < ((n : ℝ) + 1) * (a - g) := by
        rwa [div_lt_iff₀ hpos] at hn'
      have := hineq ((n : ℝ) + 1) (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
      nlinarith
    exact (ENNReal.toReal_le_toReal hPA hPG).mp hag
  refine isLocalPerimeterMinimizer_univ b' hA (fun n ↦ hfin _ (by positivity)) ?_
  intro U G K hU hG hK hKU hAG
  obtain ⟨n, hn⟩ := compact_subset_perimeter_ball hK
  exact perimeter_comparison_localize_of_compact_perturbation b' hA hG hK isOpen_ball hU hn hKU
    (hfin _ (by positivity)) hAG (hball _ (by positivity) G K hG hK hn hAG)

end SerrinEpigraph
