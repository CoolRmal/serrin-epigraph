module

public import SerrinEpigraph.ExcessEpsilonRegularity
public import SerrinEpigraph.MinimizerCompactness
public import SerrinEpigraph.DimensionReduction
public import SerrinEpigraph.PlaneTiltPerimeter
public import SerrinEpigraph.BoundaryChartGeometry
public import SerrinEpigraph.DirectionalInvariance
public import SerrinEpigraph.BVTranslation
public import SerrinEpigraph.PerimeterDilation

/-!
# From excess-form ε-regularity to `EpsilonRegularityHyp` and `SingularSetUSCHyp`

`ExcessEpsilonRegularityHyp` is the normalized De Giorgi statement (flat configuration in the unit
slab over `B₂`, small cylindrical excess ⇒ `C¹` regularity near the origin). This module derives
from it the two blow-up hypotheses used by the dimension reduction:

* `epsilonRegularityHyp_of_excess : ExcessEpsilonRegularityHyp → EpsilonRegularityHyp`;
* `singularSetUSCHyp_of_excess : ExcessEpsilonRegularityHyp → SingularSetUSCHyp`.

**Key lemma** (`ExcessEpsilonRegularityHyp.exists_isC1BoundaryPoint_zero`). There is `η > 0` such
that a local perimeter minimizer `G` in `Ω ⊇ B̄₅` with `0 ∈ ∂G` and
`|(G Δ {xₙ > 0}) ∩ B̄₅| < η` has `0` as a `C¹` boundary point. Indeed:
* (*trapping*, `trapped_of_volume_symmDiff_lt`) the density bounds forbid boundary points in the
  regions `{|x'| < 2, ±xₙ ∈ (1/2, 1)}`, which are convex, so the phase is constant on each of them,
  and `L¹`-closeness to the half-space selects the correct constants;
* (*small excess*, `exists_excess_le_of_volume_symmDiff_lt`) for a cutoff `φ` equal to one near the
  cylinder, the excess is at most `P(G, B₃) + ∫_G ∂ₙφ`; along minimizers converging to the
  half-space, the perimeters on `B₃` converge (BV8) and the fluxes converge, and for the half-space
  the limit is `P({xₙ > 0}, B₃) - ∫ φ dμ`, which is small when `φ = 1` on most of `B₃`;
* the restriction to the cylinder of a representation on `B₃` makes `G` a flat configuration with
  small projected excess, and the hypothesis applies.

**ε-regularity.** At a point with a half-space tangent cone, the rotated blow-ups converge to
`{xₙ > 0}`, so the key lemma applies at a small scale, and `C¹` regularity transfers back.

**Upper semicontinuity of singular sets.** If `xⱼ ∈ Sing Eⱼ → x₀`, then `x₀ ∈ ∂F` by the uniform
density bounds; if `x₀` were a `C¹` point of `F`, a blow-up of `F` at `x₀` would be close to a
half-space at some scale `s`, hence so would the blow-ups of `Eⱼ` at `xⱼ` at the same scale (for
large `j`, after a small translation), and the key lemma would make `xⱼ` regular.
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory InnerProductSpace Filter
open scoped Topology ENNReal ContDiff

namespace SerrinEpigraph

/-! ### 1. Elementary facts -/

/-- In `Space 0` the measure-theoretic boundary of every set is empty. -/
theorem measureTheoreticBoundary_eq_empty_of_space_zero (E : Set (Space 0)) :
    measureTheoreticBoundary E = ∅ := by
  refine eq_empty_of_forall_notMem fun x hx ↦ ?_
  have hsub : ∀ y z : Space 0, y = z := fun y z ↦ by
    ext i
    exact i.elim0
  have h := hx 1 one_pos
  rcases E.eq_empty_or_nonempty with hE | ⟨y, hy⟩
  · exact h.1 (by rw [hE, empty_inter, measure_empty])
  · have hEu : E = univ := eq_univ_of_forall fun z ↦ by rw [hsub z y]; exact hy
    exact h.2 (by simp [hEu])

theorem mem_positiveHalfspace_verticalDirection_iff {m : ℕ} (z : Space (m + 1)) :
    z ∈ positiveHalfspace (verticalDirection m) ↔ 0 < z (Fin.last m) := by
  show 0 < inner ℝ (verticalDirection m) z ↔ _
  rw [real_inner_comm, inner_verticalDirection_right]

private theorem norm_sq_lt_of_horizontal_last_aux {m : ℕ} {z : Space (m + 1)} {a b : ℝ}
    (ha : ‖horizontal z‖ < a) (hb : |z (Fin.last m)| < b) : ‖z‖ ^ 2 < a ^ 2 + b ^ 2 := by
  rw [norm_sq_eq_norm_horizontal_sq_add]
  have h1 : ‖horizontal z‖ ^ 2 < a ^ 2 := by
    have := norm_nonneg (horizontal z)
    nlinarith
  have h2 : z (Fin.last m) ^ 2 < b ^ 2 := by
    rw [← sq_abs]
    have := abs_nonneg (z (Fin.last m))
    nlinarith
  linarith

/-- Points of the flat cylinder `B₂ × (-1, 1)` have norm less than `9/4`. -/
theorem norm_lt_of_mem_flatCylinder {m : ℕ} {z : Space (m + 1)}
    (hz : z ∈ cylinderSet (ball (0 : Space m) 2) 1) : ‖z‖ < 9 / 4 := by
  obtain ⟨hz1, hz2⟩ := hz
  have h1 : ‖horizontal z‖ < 2 := by simpa using hz1
  have h2 : |z (Fin.last m)| < 1 := abs_lt.mpr ⟨hz2.1, hz2.2⟩
  have h3 := norm_sq_lt_of_horizontal_last_aux h1 h2
  nlinarith [norm_nonneg z]

private theorem horizontal_zero_bridge_aux {m : ℕ} : horizontal (0 : Space (m + 1)) = 0 := by
  ext i
  simp [horizontal]

/-- `C¹` boundary points are transported by similarities. -/
theorem isC1BoundaryPoint_preimage_similarity_iff {d : ℕ} {E : Set (Space d)}
    (Q : Space d ≃ₗᵢ[ℝ] Space d) (c : Space d) {θ : ℝ} (hθ : 0 < θ) (y : Space d) :
    IsC1BoundaryPoint (similarity Q c θ ⁻¹' E) y ↔ IsC1BoundaryPoint E (similarity Q c θ y) := by
  have hset : similarity Q c θ ⁻¹' E = Q ⁻¹' ((fun z ↦ c + θ • z) ⁻¹' E) := rfl
  rw [hset, isC1BoundaryPoint_preimage_linearIsometryEquiv_iff,
    isC1BoundaryPoint_preimage_add_smul_iff hθ]
  rfl

/-- Lebesgue measure under a similarity. -/
theorem volume_preimage_similarity {d : ℕ} (Q : Space d ≃ₗᵢ[ℝ] Space d) (c : Space d) {θ : ℝ}
    (hθ : 0 < θ) (A : Set (Space d)) :
    volume (similarity Q c θ ⁻¹' A) = ENNReal.ofReal ((θ ^ d)⁻¹) * volume A := by
  have hset : similarity Q c θ ⁻¹' A =
      Q ⁻¹' ((fun v ↦ θ • v) ⁻¹' ((fun u ↦ c + u) ⁻¹' A)) := rfl
  rw [hset, Q.measurePreserving.measure_preimage_emb Q.toHomeomorph.measurableEmbedding,
    Measure.addHaar_preimage_smul volume hθ.ne', measure_preimage_add,
    finrank_euclideanSpace_fin, abs_of_pos (inv_pos.mpr (pow_pos hθ d))]

theorem preimage_similarity_closedBall {d : ℕ} (Q : Space d ≃ₗᵢ[ℝ] Space d) (c : Space d)
    {θ : ℝ} (hθ : 0 < θ) (r : ℝ) :
    similarity Q c θ ⁻¹' closedBall c (θ * r) = closedBall 0 r := by
  ext w
  simp only [mem_preimage, mem_closedBall, similarity, dist_eq_norm, add_sub_cancel_left,
    norm_smul, Real.norm_of_nonneg hθ.le, LinearIsometryEquiv.norm_map, sub_zero]
  constructor
  · intro h
    exact le_of_mul_le_mul_left h hθ
  · intro h
    exact mul_le_mul_of_nonneg_left h hθ.le

theorem preimage_linearIsometryEquiv_positiveHalfspace {d : ℕ} (Q : Space d ≃ₗᵢ[ℝ] Space d)
    (e : Space d) : Q ⁻¹' positiveHalfspace (Q e) = positiveHalfspace e := by
  ext z
  show 0 < inner ℝ (Q e) (Q z) ↔ 0 < inner ℝ e z
  rw [Q.inner_map_map]

theorem symmDiff_preimage_similarity_inter_closedBall {d : ℕ} (Q : Space d ≃ₗᵢ[ℝ] Space d)
    (c : Space d) (θ : ℝ) (E : Set (Space d)) (v : Space d) (r : ℝ) :
    symmDiff (similarity Q c θ ⁻¹' E) (positiveHalfspace v) ∩ closedBall 0 r =
      Q ⁻¹' (symmDiff ((fun z ↦ c + θ • z) ⁻¹' E) (positiveHalfspace (Q v)) ∩
        closedBall 0 r) := by
  rw [preimage_inter, preimage_symmDiff, preimage_linearIsometryEquiv_positiveHalfspace,
    Q.preimage_closedBall, map_zero]
  rfl

private theorem measure_symmDiff_inter_le_aux {d : ℕ} (A B C K : Set (Space d)) :
    volume (symmDiff A C ∩ K) ≤ volume (symmDiff A B ∩ K) + volume (symmDiff B C ∩ K) := by
  calc volume (symmDiff A C ∩ K) ≤ volume ((symmDiff A B ∩ K) ∪ (symmDiff B C ∩ K)) := by
        refine measure_mono ?_
        rw [← union_inter_distrib_right]
        exact inter_subset_inter_left K (symmDiff_triangle A B C)
    _ ≤ _ := measure_union_le _ _

private theorem tendsto_volume_symmDiff_of_integral_aux {d : ℕ} {E : ℕ → Set (Space d)}
    {F K : Set (Space d)} (hF : MeasurableSet F) (hK : IsCompact K)
    (hE : ∀ᶠ j in atTop, MeasurableSet (E j))
    (h : Tendsto (fun j ↦ ∫ y in K, ‖(E j).indicator (fun _ ↦ (1 : ℝ)) y -
      F.indicator (fun _ ↦ (1 : ℝ)) y‖) atTop (𝓝 0)) :
    Tendsto (fun j ↦ volume (symmDiff (E j) F ∩ K)) atTop (𝓝 0) := by
  have hreal : Tendsto (fun j ↦ volume.real (symmDiff (E j) F ∩ K)) atTop (𝓝 0) := by
    refine h.congr' ?_
    filter_upwards [hE] with j hj
    exact setIntegral_norm_indicator_sub_eq_volume_symmDiff hj hF
  have h2 := ENNReal.tendsto_ofReal hreal
  rw [ENNReal.ofReal_zero] at h2
  refine h2.congr fun j ↦ ?_
  exact ofReal_measureReal (measure_ne_top_of_subset inter_subset_right hK.measure_lt_top.ne)

/-- A perimeter representation on an open set is a polar representation there. -/
theorem IsPerimeterRepresentation.isPerimeterPolarOn {d : ℕ}
    {b : OrthonormalBasis (Fin d) ℝ (Space d)} {E W : Set (Space d)} {μ : Measure (Space d)}
    {ν : Space d → Space d} (h : IsPerimeterRepresentation b E W μ ν) (hW : IsOpen W) :
    IsPerimeterPolarOn b E W μ ν := by
  have hself : μ.restrict W = μ :=
    Measure.restrict_eq_self_of_ae_mem (by rw [ae_iff]; exact h.measure_compl)
  refine ⟨hW, ?_, ?_, ?_⟩
  · rw [hself]
    exact h.integrable
  · rw [hself]
    exact h.norm_eq_one
  · intro X hX hXW
    rw [hself]
    exact h.dist X hX hXW

/-- The projected excess of a representation restricted to a set `C` lying over `A`. -/
theorem projectedExcessMeasure_restrict_real_eq {m : ℕ} {μ : Measure (Space (m + 1))}
    [IsFiniteMeasure μ] {ν : Space (m + 1) → Space (m + 1)} (hν : Integrable ν μ)
    (hνunit : ∀ᵐ x ∂μ, ‖ν x‖ = 1) {C : Set (Space (m + 1))} {A : Set (Space m)}
    (hA : MeasurableSet A) (hCA : C ⊆ horizontal ⁻¹' A) :
    (projectedExcessMeasure (μ.restrict C) ν).real A =
      ∫ y in C, (1 - inner ℝ (ν y) (verticalDirection m)) ∂μ := by
  have hπm : Measurable (horizontal : Space (m + 1) → Space m) :=
    continuous_horizontal.measurable
  have hBm : MeasurableSet (horizontal ⁻¹' A : Set (Space (m + 1))) := hA.preimage hπm
  have hlin : projectedExcessMeasure (μ.restrict C) ν A =
      ∫⁻ y in C, ENNReal.ofReal (1 - inner ℝ (ν y) (verticalDirection m)) ∂μ := by
    unfold projectedExcessMeasure
    rw [Measure.map_apply hπm hA, withDensity_apply _ hBm, Measure.restrict_restrict hBm,
      inter_eq_right.mpr hCA]
  have hf_int : Integrable (fun y ↦ 1 - inner ℝ (ν y) (verticalDirection m)) μ :=
    (integrable_const 1).sub (hν.inner_const _)
  have hf_nonneg : ∀ᵐ y ∂μ, 0 ≤ 1 - inner ℝ (ν y) (verticalDirection m) := by
    filter_upwards [hνunit] with y hy
    have hcs := real_inner_le_norm (ν y) (verticalDirection m)
    rw [hy, norm_verticalDirection, mul_one] at hcs
    linarith
  rw [Measure.real, hlin, integral_eq_lintegral_of_nonneg_ae (ae_restrict_of_ae hf_nonneg)
    hf_int.aestronglyMeasurable.restrict]

/-! ### 2. Trapping in the middle slab -/

/-- Threshold of the trapping lemma. -/
def flatTrapThreshold (m : ℕ) : ℝ :=
  min (minimizerVolumeDensityConst m * (1 / 4) ^ (m + 1))
    (volume.real (ball (0 : Space (m + 1)) (1 / 4)))

theorem flatTrapThreshold_pos (m : ℕ) : 0 < flatTrapThreshold m :=
  lt_min (mul_pos (minimizerVolumeDensityConst_pos m) (by positivity))
    (ENNReal.toReal_pos (measure_ball_pos volume _ (by norm_num)).ne' measure_ball_lt_top.ne)

private theorem convex_flatSlab_aux {m : ℕ} (a b : ℝ) :
    Convex ℝ {z : Space (m + 1) | horizontal z ∈ ball (0 : Space m) 2 ∧
      z (Fin.last m) ∈ Ioo a b} := by
  intro z hz w hw s t hs ht hst
  refine ⟨?_, ?_⟩
  · have h1 : horizontal (s • z + t • w) = s • horizontal z + t • horizontal w := by
      ext i
      simp [horizontal]
    rw [h1]
    exact (convex_ball (0 : Space m) 2) hz.1 hw.1 hs ht hst
  · have h1 : (s • z + t • w) (Fin.last m) = s • z (Fin.last m) + t • w (Fin.last m) := by
      simp
    rw [h1]
    exact (convex_Ioo a b) hz.2 hw.2 hs ht hst

/-- **Trapping.** A local perimeter minimizer in `Ω ⊇ B̄₅` which is `L¹`-close to the half-space
`{xₙ > 0}` on `B̄₅` is empty below and full above the middle slab of `B₂ × (-1, 1)`. -/
theorem trapped_of_volume_symmDiff_lt {m : ℕ} {G Ω : Set (Space (m + 1))}
    (hmin : IsLocalPerimeterMinimizer (EuclideanSpace.basisFun (Fin (m + 1)) ℝ) G Ω)
    (hΩ : closedBall 0 5 ⊆ Ω)
    (hclose : volume.real (symmDiff G (positiveHalfspace (verticalDirection m)) ∩
      closedBall 0 5) < flatTrapThreshold m) :
    (∀ᵐ z ∂volume, horizontal z ∈ ball (0 : Space m) 2 →
      z (Fin.last m) ∈ Ioo (-1) (-(1 / 2)) → z ∉ G) ∧
    (∀ᵐ z ∂volume, horizontal z ∈ ball (0 : Space m) 2 →
      z (Fin.last m) ∈ Ioo (1 / 2) 1 → z ∈ G) := by
  set H := positiveHalfspace (verticalDirection m) with hH
  set S := symmDiff G H ∩ closedBall (0 : Space (m + 1)) 5 with hS
  have hSfin : volume S ≠ ⊤ :=
    measure_ne_top_of_subset inter_subset_right (isCompact_closedBall _ _).measure_lt_top.ne
  have hthr1 : flatTrapThreshold m ≤ minimizerVolumeDensityConst m * (1 / 4) ^ (m + 1) :=
    min_le_left _ _
  have hthr2 : flatTrapThreshold m ≤ volume.real (ball (0 : Space (m + 1)) (1 / 4)) :=
    min_le_right _ _
  have hnorm : ∀ z : Space (m + 1), horizontal z ∈ ball (0 : Space m) 2 →
      |z (Fin.last m)| < 1 → ‖z‖ < 3 := by
    intro z hz1 hz2
    have h1 := norm_sq_lt_of_horizontal_last_aux (by simpa using hz1 : ‖horizontal z‖ < 2) hz2
    nlinarith [norm_nonneg z]
  have hnear : ∀ z w : Space (m + 1), w ∈ ball z (1 / 4) → ‖w‖ < ‖z‖ + 1 / 4 := by
    intro z w hw
    rw [mem_ball, dist_eq_norm] at hw
    have := norm_add_le z (w - z)
    rw [add_sub_cancel] at this
    linarith
  have hcb : ∀ z : Space (m + 1), ‖z‖ < 3 → closedBall z (1 / 4) ⊆ Ω := by
    intro z hz w hw
    apply hΩ
    rw [mem_closedBall, dist_eq_norm] at hw
    rw [mem_closedBall, dist_zero_right]
    have := norm_add_le z (w - z)
    rw [add_sub_cancel] at this
    linarith
  have hlast : ∀ z w : Space (m + 1), w ∈ ball z (1 / 4) →
      |w (Fin.last m) - z (Fin.last m)| < 1 / 4 := by
    intro z w hw
    rw [mem_ball, dist_eq_norm] at hw
    have := abs_apply_last_le_norm (w - z)
    rw [PiLp.sub_apply] at this
    linarith
  have hS5 : ∀ w : Space (m + 1), ‖w‖ < 5 → w ∈ closedBall (0 : Space (m + 1)) 5 := by
    intro w hw
    rw [mem_closedBall, dist_zero_right]
    exact hw.le
  -- no boundary points in the upper and lower parts
  have hnotB_top : ∀ z : Space (m + 1), horizontal z ∈ ball (0 : Space m) 2 →
      z (Fin.last m) ∈ Ioo (1 / 2) 1 → z ∉ measureTheoreticBoundary G := by
    intro z hz1 hz2 hzB
    have hz3 : ‖z‖ < 3 := hnorm z hz1 (abs_lt.mpr ⟨by linarith [hz2.1], hz2.2⟩)
    have hdens := hmin.volume_sdiff_ball_ge hzB (by norm_num : (0 : ℝ) < 1 / 4) (hcb z hz3)
    have hsub : ball z (1 / 4) \ G ⊆ S := by
      intro w hw
      refine ⟨Set.mem_symmDiff.mpr (Or.inr ⟨?_, hw.2⟩), hS5 w ?_⟩
      · rw [hH, mem_positiveHalfspace_verticalDirection_iff]
        have := hlast z w hw.1
        rw [abs_lt] at this
        linarith [hz2.1, this.1]
      · have := hnear z w hw.1
        linarith
    have h2 : volume.real (ball z (1 / 4) \ G) ≤ volume.real S := measureReal_mono hsub hSfin
    linarith
  have hnotB_bot : ∀ z : Space (m + 1), horizontal z ∈ ball (0 : Space m) 2 →
      z (Fin.last m) ∈ Ioo (-1) (-(1 / 2)) → z ∉ measureTheoreticBoundary G := by
    intro z hz1 hz2 hzB
    have hz3 : ‖z‖ < 3 := hnorm z hz1 (abs_lt.mpr ⟨hz2.1, by linarith [hz2.2]⟩)
    have hdens := hmin.volume_inter_ball_ge hzB (by norm_num : (0 : ℝ) < 1 / 4) (hcb z hz3)
    have hsub : G ∩ ball z (1 / 4) ⊆ S := by
      intro w hw
      refine ⟨Set.mem_symmDiff.mpr (Or.inl ⟨hw.1, ?_⟩), hS5 w ?_⟩
      · rw [hH, mem_positiveHalfspace_verticalDirection_iff]
        have := hlast z w hw.2
        rw [abs_lt] at this
        linarith [hz2.2, this.2]
      · have := hnear z w hw.2
        linarith
    have h2 : volume.real (G ∩ ball z (1 / 4)) ≤ volume.real S := measureReal_mono hsub hSfin
    linarith
  -- the cover of each part by the measure-theoretic interior and exterior
  have hcov : ∀ a b : ℝ, (∀ z : Space (m + 1), horizontal z ∈ ball (0 : Space m) 2 →
      z (Fin.last m) ∈ Ioo a b → z ∉ measureTheoreticBoundary G) →
      {z : Space (m + 1) | horizontal z ∈ ball (0 : Space m) 2 ∧ z (Fin.last m) ∈ Ioo a b} ⊆
        measureTheoreticInterior G ∪ measureTheoreticExterior G := by
    intro a b hnot z hz
    by_contra hcon
    apply hnot z hz.1 hz.2
    rw [← compl_measureTheoreticInterior_union_exterior]
    exact hcon
  have hball_vol : ∀ p : Space (m + 1),
      volume.real (ball p (1 / 4)) = volume.real (ball (0 : Space (m + 1)) (1 / 4)) := by
    intro p
    rw [measureReal_def, measureReal_def, Measure.addHaar_ball_center]
  have hp_ball : ∀ (c : ℝ) (w : Space (m + 1)), w ∈ ball (c • verticalDirection m) (1 / 4) →
      ‖horizontal w‖ < 1 / 4 ∧ |w (Fin.last m) - c| < 1 / 4 ∧ ‖w‖ < |c| + 1 / 4 := by
    intro c w hw
    rw [mem_ball, dist_eq_norm] at hw
    refine ⟨?_, ?_, ?_⟩
    · have := norm_horizontal_le_norm_of_space (w - c • verticalDirection m)
      rw [horizontal_sub_smul_verticalDirection] at this
      linarith
    · have := abs_apply_last_le_norm (w - c • verticalDirection m)
      rw [last_sub_smul_verticalDirection] at this
      linarith
    · have h1 := norm_add_le (c • verticalDirection m) (w - c • verticalDirection m)
      rw [add_sub_cancel, norm_smul, norm_verticalDirection, mul_one, Real.norm_eq_abs] at h1
      linarith
  refine ⟨?_, ?_⟩
  · -- the lower part lies in the exterior
    rcases (convex_flatSlab_aux (-1) (-(1 / 2))).isPreconnected.subset_or_subset
      (isOpen_measureTheoreticInterior G) (isOpen_measureTheoreticExterior G)
      (disjoint_measureTheoreticInterior_exterior G) (hcov _ _ hnotB_bot) with hint | hext
    · exfalso
      set p : Space (m + 1) := (-(3 / 4) : ℝ) • verticalDirection m with hp
      have hpball : ∀ w ∈ ball p (1 / 4), horizontal w ∈ ball (0 : Space m) 2 ∧
          w (Fin.last m) ∈ Ioo (-1) (-(1 / 2)) := by
        intro w hw
        obtain ⟨h1, h2, -⟩ := hp_ball _ w hw
        rw [abs_lt] at h2
        refine ⟨by rw [mem_ball, dist_zero_right]; linarith, ⟨by linarith, by linarith⟩⟩
      have hnull : volume (ball p (1 / 4) \ G) = 0 := by
        refine measure_mono_null (fun w hw ↦ ?_)
          (ae_iff.mp hmin.ae_mem_iff_measureTheoreticInterior)
        intro hw'
        have hwΩ : w ∈ Ω := by
          apply hΩ
          obtain ⟨-, -, h3⟩ := hp_ball _ w hw.1
          rw [mem_closedBall, dist_zero_right]
          norm_num at h3
          linarith
        exact hw.2 ((hw' hwΩ).mpr (hint (hpball w hw.1)))
      have hsub : G ∩ ball p (1 / 4) ⊆ S := by
        intro w hw
        obtain ⟨-, h2, h3⟩ := hp_ball _ w hw.2
        rw [abs_lt] at h2
        refine ⟨Set.mem_symmDiff.mpr (Or.inl ⟨hw.1, ?_⟩), hS5 w ?_⟩
        · rw [hH, mem_positiveHalfspace_verticalDirection_iff]
          linarith
        · norm_num at h3
          linarith
      have hle : volume (ball p (1 / 4)) ≤ volume S := by
        calc volume (ball p (1 / 4))
            ≤ volume (ball p (1 / 4) ∩ G) + volume (ball p (1 / 4) \ G) :=
              measure_le_inter_add_sdiff _ _ _
          _ = volume (G ∩ ball p (1 / 4)) := by rw [hnull, add_zero, inter_comm]
          _ ≤ volume S := measure_mono hsub
      have hle' : volume.real (ball p (1 / 4)) ≤ volume.real S := ENNReal.toReal_mono hSfin hle
      rw [hball_vol] at hle'
      linarith
    · filter_upwards [hmin.ae_mem_compl_iff_measureTheoreticExterior] with z hz hz1 hz2
      have hzΩ : z ∈ Ω := by
        apply hΩ
        have := hnorm z hz1 (abs_lt.mpr ⟨hz2.1, by linarith [hz2.2]⟩)
        rw [mem_closedBall, dist_zero_right]
        linarith
      exact (hz hzΩ).mpr (hext ⟨hz1, hz2⟩)
  · -- the upper part lies in the interior
    rcases (convex_flatSlab_aux (1 / 2) 1).isPreconnected.subset_or_subset
      (isOpen_measureTheoreticInterior G) (isOpen_measureTheoreticExterior G)
      (disjoint_measureTheoreticInterior_exterior G) (hcov _ _ hnotB_top) with hint | hext
    · filter_upwards [hmin.ae_mem_iff_measureTheoreticInterior] with z hz hz1 hz2
      have hzΩ : z ∈ Ω := by
        apply hΩ
        have := hnorm z hz1 (abs_lt.mpr ⟨by linarith [hz2.1], hz2.2⟩)
        rw [mem_closedBall, dist_zero_right]
        linarith
      exact (hz hzΩ).mpr (hint ⟨hz1, hz2⟩)
    · exfalso
      set p : Space (m + 1) := (3 / 4 : ℝ) • verticalDirection m with hp
      have hpball : ∀ w ∈ ball p (1 / 4), horizontal w ∈ ball (0 : Space m) 2 ∧
          w (Fin.last m) ∈ Ioo (1 / 2) 1 := by
        intro w hw
        obtain ⟨h1, h2, -⟩ := hp_ball _ w hw
        rw [abs_lt] at h2
        refine ⟨by rw [mem_ball, dist_zero_right]; linarith, ⟨by linarith, by linarith⟩⟩
      have hnull : volume (G ∩ ball p (1 / 4)) = 0 := by
        refine measure_mono_null (fun w hw ↦ ?_)
          (ae_iff.mp hmin.ae_mem_compl_iff_measureTheoreticExterior)
        intro hw'
        have hwΩ : w ∈ Ω := by
          apply hΩ
          obtain ⟨-, -, h3⟩ := hp_ball _ w hw.2
          rw [mem_closedBall, dist_zero_right]
          norm_num at h3
          linarith
        exact ((hw' hwΩ).mpr (hext (hpball w hw.2))) hw.1
      have hsub : ball p (1 / 4) \ G ⊆ S := by
        intro w hw
        obtain ⟨-, h2, h3⟩ := hp_ball _ w hw.1
        rw [abs_lt] at h2
        refine ⟨Set.mem_symmDiff.mpr (Or.inr ⟨?_, hw.2⟩), hS5 w ?_⟩
        · rw [hH, mem_positiveHalfspace_verticalDirection_iff]
          linarith
        · norm_num at h3
          linarith
      have hle : volume (ball p (1 / 4)) ≤ volume S := by
        calc volume (ball p (1 / 4))
            ≤ volume (ball p (1 / 4) ∩ G) + volume (ball p (1 / 4) \ G) :=
              measure_le_inter_add_sdiff _ _ _
          _ = volume (ball p (1 / 4) \ G) := by rw [inter_comm, hnull, zero_add]
          _ ≤ volume S := measure_mono hsub
      have hle' : volume.real (ball p (1 / 4)) ≤ volume.real S := ENNReal.toReal_mono hSfin hle
      rw [hball_vol] at hle'
      linarith

/-! ### 3. Small excess -/

/-- A smooth cutoff equal to one on `closedBall 0 ρ` and supported in `ball 0 3`. -/
def flatCutoff (m : ℕ) {ρ : ℝ} (hρ : 0 < ρ) (hρ3 : ρ < 3) : ContDiffBump (0 : Space (m + 1)) where
  rIn := ρ
  rOut := (ρ + 3) / 2
  rIn_pos := hρ
  rIn_lt_rOut := by linarith

/-- **Excess bound by a flux.** For a perimeter representation on `B₃` and a cutoff `φ` equal to
one on the flat cylinder and supported in `B₃`, the excess on the cylinder is at most
`μ(B₃) + ∫_G ∂ₙφ`. -/
theorem integral_flatCylinder_excess_le {m : ℕ} {G : Set (Space (m + 1))}
    {μ : Measure (Space (m + 1))} {ν : Space (m + 1) → Space (m + 1)}
    (hrep : IsPerimeterRepresentation (EuclideanSpace.basisFun (Fin (m + 1)) ℝ) G (ball 0 3) μ ν)
    {φ : Space (m + 1) → ℝ} (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ ball 0 3) (hφ01 : ∀ z, 0 ≤ φ z ∧ φ z ≤ 1)
    (hφ1 : ∀ z ∈ cylinderSet (ball (0 : Space m) 2) 1, φ z = 1) :
    ∫ y in cylinderSet (ball (0 : Space m) 2) 1, (1 - inner ℝ (ν y) (verticalDirection m)) ∂μ ≤
      μ.real (ball 0 3) +
        ∫ z, G.indicator (fun _ ↦ (1 : ℝ)) z * fderiv ℝ φ z (verticalDirection m) := by
  have := hrep.isFiniteMeasure
  set b := EuclideanSpace.basisFun (Fin (m + 1)) ℝ with hb
  set e := verticalDirection m with he
  set C := cylinderSet (ball (0 : Space m) 2) 1 with hC
  have hCm : MeasurableSet C := (isOpen_cylinderSet isOpen_ball 1).measurableSet
  set f : Space (m + 1) → ℝ := fun y ↦ 1 - inner ℝ (ν y) e with hf
  have hνe : Integrable (fun y ↦ inner ℝ (ν y) e) μ := hrep.integrable.inner_const e
  have hfint : Integrable f μ := (integrable_const 1).sub hνe
  have hfnn : ∀ᵐ y ∂μ, 0 ≤ f y := by
    filter_upwards [hrep.norm_eq_one] with y hy
    have h1 := real_inner_le_norm (ν y) e
    rw [hy, he, norm_verticalDirection, mul_one] at h1
    simp only [hf]
    linarith
  have hφcont : Continuous φ := hφ.continuous
  have hφint : Integrable φ μ := hφcont.integrable_of_hasCompactSupport hφc
  have hφbd : ∀ᵐ y ∂μ, ‖φ y‖ ≤ 1 := Eventually.of_forall fun y ↦ by
    rw [Real.norm_of_nonneg (hφ01 y).1]
    exact (hφ01 y).2
  have hφνe : Integrable (fun y ↦ φ y * inner ℝ (ν y) e) μ :=
    hνe.bdd_mul hφcont.aestronglyMeasurable hφbd
  have hφf : Integrable (fun y ↦ φ y * f y) μ := hfint.bdd_mul hφcont.aestronglyMeasurable hφbd
  have h1 : ∫ y in C, f y ∂μ ≤ ∫ y, φ y * f y ∂μ := by
    rw [← integral_indicator hCm]
    refine integral_mono_ae (hfint.indicator hCm) hφf ?_
    filter_upwards [hfnn] with y hy
    by_cases hyC : y ∈ C
    · rw [indicator_of_mem hyC, hφ1 y hyC, one_mul]
    · rw [indicator_of_notMem hyC]
      exact mul_nonneg (hφ01 y).1 hy
  have h2 : ∫ y, φ y * f y ∂μ = ∫ y, φ y ∂μ - ∫ y, φ y * inner ℝ (ν y) e ∂μ := by
    rw [← integral_sub hφint hφνe]
    congr 1
    funext y
    simp only [hf]
    ring
  have hX : ContDiff ℝ 1 (fun z ↦ φ z • e) := hφ.smul contDiff_const
  have hXc : HasCompactSupport (fun z ↦ φ z • e) := hasCompactSupport_smul_left' hφc fun _ ↦ e
  have hd : -(∫ x, G.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b (fun z ↦ φ z • e) x) =
      ∫ x, inner ℝ (φ x • e) (ν x) ∂μ :=
    hrep.dist ⟨⟨fun z ↦ φ z • e, hX.continuous⟩, hXc⟩ hX
      ((tsupport_smul_subset_left' _ _).trans hφs)
  have hdiv : ∀ x, fieldDivergence b (fun z ↦ φ z • e) x = fderiv ℝ φ x e := fun x ↦
    fieldDivergence_smul_const_eq_fderiv b ((hφ.differentiable one_ne_zero) x) e
  simp only [hdiv] at hd
  have h3 : ∫ y, φ y * inner ℝ (ν y) e ∂μ = ∫ y, inner ℝ (φ y • e) (ν y) ∂μ := by
    congr 1
    funext y
    rw [real_inner_smul_left, real_inner_comm]
  have h4 : ∫ y, φ y ∂μ ≤ μ.real (ball 0 3) := by
    have hμ : μ univ = μ (ball 0 3) := by
      have h := measure_add_measure_compl (μ := μ)
        (isOpen_ball : IsOpen (ball (0 : Space (m + 1)) 3)).measurableSet
      rw [hrep.measure_compl, add_zero] at h
      exact h.symm
    calc ∫ y, φ y ∂μ ≤ ∫ _y, (1 : ℝ) ∂μ :=
          integral_mono hφint (integrable_const 1) fun y ↦ (hφ01 y).2
      _ = μ.real (ball 0 3) := by
          rw [integral_const, smul_eq_mul, mul_one, measureReal_def, measureReal_def, hμ]
  linarith

/-- **Flux of the half-space.** For a cutoff `φ ≤ 1` supported in `B₃` and equal to one on `B_ρ`,
`∫_{xₙ > 0} ∂ₙφ ≤ -P({xₙ > 0}, B_ρ)`. -/
theorem integral_indicator_halfspace_mul_fderiv_le {m : ℕ} {φ : Space (m + 1) → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ ball 0 3)
    (hφ01 : ∀ z, 0 ≤ φ z ∧ φ z ≤ 1) {ρ : ℝ} (hρ3 : ρ ≤ 3)
    (hφ1 : ∀ z ∈ ball (0 : Space (m + 1)) ρ, φ z = 1) :
    ∫ z, (positiveHalfspace (verticalDirection m)).indicator (fun _ ↦ (1 : ℝ)) z *
        fderiv ℝ φ z (verticalDirection m) ≤
      -(variationalPerimeter (EuclideanSpace.basisFun (Fin (m + 1)) ℝ)
        (positiveHalfspace (verticalDirection m)) (ball 0 ρ)).toReal := by
  set b := EuclideanSpace.basisFun (Fin (m + 1)) ℝ with hb
  set e := verticalDirection m with he
  set H := positiveHalfspace e with hH
  have he1 : ‖e‖ = 1 := norm_verticalDirection m
  have he0 : e ≠ 0 := by
    intro h
    rw [h, norm_zero] at he1
    exact zero_ne_one he1
  have hHmeas : MeasurableSet H := (isOpen_positiveHalfspace e).measurableSet
  have hP : variationalPerimeter b H (ball 0 3) ≠ ⊤ := by
    rw [show H = {x : Space (m + 1) | 0 < inner ℝ e x} from rfl,
      positive_halfspace_perimeter_closedBall_volume b he1 (by norm_num)]
    exact measure_closedBall_lt_top.ne
  obtain ⟨μ, ν, hrep⟩ := exists_isPerimeterRepresentation b hHmeas isOpen_ball hP
  have := hrep.isFiniteMeasure
  have hpolar := hrep.isPerimeterPolarOn isOpen_ball
  have hchart := isSmoothBoundaryChart_inner (E := H)
    (isOpen_ball : IsOpen (ball (0 : Space (m + 1)) 3)) he0
    (Eventually.of_forall fun z _ ↦ Iff.rfl)
  have hν := hchart.ae_restrict_eq_chartNormal hpolar subset_rfl
  have hself : μ.restrict (ball 0 3) = μ :=
    Measure.restrict_eq_self_of_ae_mem (by rw [ae_iff]; exact hrep.measure_compl)
  rw [hself] at hν
  have hX : ContDiff ℝ 1 (fun z ↦ φ z • e) := hφ.smul contDiff_const
  have hXc : HasCompactSupport (fun z ↦ φ z • e) := hasCompactSupport_smul_left' hφc fun _ ↦ e
  have hd : -(∫ x, H.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b (fun z ↦ φ z • e) x) =
      ∫ x, inner ℝ (φ x • e) (ν x) ∂μ :=
    hrep.dist ⟨⟨fun z ↦ φ z • e, hX.continuous⟩, hXc⟩ hX
      ((tsupport_smul_subset_left' _ _).trans hφs)
  have hdiv : ∀ x, fieldDivergence b (fun z ↦ φ z • e) x = fderiv ℝ φ x e := fun x ↦
    fieldDivergence_smul_const_eq_fderiv b ((hφ.differentiable one_ne_zero) x) e
  simp only [hdiv] at hd
  have hφint : Integrable φ μ := hφ.continuous.integrable_of_hasCompactSupport hφc
  have hR : ∫ x, inner ℝ (φ x • e) (ν x) ∂μ = ∫ x, φ x ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hν] with x hx
    rw [hx, chartNormal_inner_left_const he1, real_inner_smul_left, real_inner_self_eq_norm_sq,
      he1]
    ring
  have hball : μ.real (ball 0 ρ) ≤ ∫ x, φ x ∂μ := by
    rw [← integral_indicator_one measurableSet_ball]
    refine integral_mono ((integrable_const (1 : ℝ)).indicator measurableSet_ball) hφint ?_
    intro x
    by_cases hx : x ∈ ball (0 : Space (m + 1)) ρ
    · rw [indicator_of_mem hx, hφ1 x hx]
      rfl
    · rw [indicator_of_notMem hx]
      exact (hφ01 x).1
  have hμρ : μ.real (ball 0 ρ) = (variationalPerimeter b H (ball 0 ρ)).toReal := by
    rw [measureReal_def, hrep.measure_open _ isOpen_ball (ball_subset_ball hρ3)]
  linarith

/-- **Perimeter convergence on `B₃`** for minimizers converging to the half-space. -/
theorem tendsto_perimeter_ball_three_of_tendsto_halfspace {m : ℕ}
    {G : ℕ → Set (Space (m + 1))}
    (hmin : ∀ j, IsLocalPerimeterMinimizer (EuclideanSpace.basisFun (Fin (m + 1)) ℝ) (G j)
      (ball 0 5))
    (hconv : Tendsto (fun j ↦ volume.real (symmDiff (G j)
      (positiveHalfspace (verticalDirection m)) ∩ closedBall 0 5)) atTop (𝓝 0)) :
    Tendsto (fun j ↦ (variationalPerimeter (EuclideanSpace.basisFun (Fin (m + 1)) ℝ) (G j)
        (ball 0 3)).toReal) atTop
      (𝓝 (variationalPerimeter (EuclideanSpace.basisFun (Fin (m + 1)) ℝ)
        (positiveHalfspace (verticalDirection m)) (ball 0 3)).toReal) := by
  set b := EuclideanSpace.basisFun (Fin (m + 1)) ℝ with hb
  set H := positiveHalfspace (verticalDirection m) with hH
  have hHmeas : MeasurableSet H := (isOpen_positiveHalfspace _).measurableSet
  have he1 := norm_verticalDirection m
  have hformula : ∀ s : ℝ, 0 < s →
      variationalPerimeter b H (ball 0 s) = volume (closedBall (0 : Space m) s) := fun s hs ↦
    positive_halfspace_perimeter_closedBall_volume b he1 hs
  obtain ⟨μ, hμloc, -, hμ⟩ := exists_global_perimeter_measure b hHmeas fun n ↦ by
    rw [hformula _ (by positivity)]
    exact measure_closedBall_lt_top.ne
  have := hμloc
  have heq : ∀ s : ℝ, 0 < s → variationalPerimeter b H (ball 0 s) =
      ENNReal.ofReal (s ^ m) * volume (closedBall (0 : Space m) 1) := by
    intro s hs
    rw [hformula s hs, Measure.addHaar_closedBall' volume (0 : Space m) hs.le,
      finrank_euclideanSpace_fin]
  have hsph : μ (sphere 0 3) = 0 := by
    refine (sphere_measure_eq_zero_iff_tendsto_variationalPerimeter_ball b μ (δ := 1) one_pos
      (fun U hU _ ↦ hμ U hU)).mpr ?_
    have hc : volume (closedBall (0 : Space m) 1) ≠ ⊤ := measure_closedBall_lt_top.ne
    have hlim : Tendsto (fun s : ℝ ↦ ENNReal.ofReal (s ^ m) * volume (closedBall (0 : Space m) 1))
        (𝓝 3) (𝓝 (ENNReal.ofReal (3 ^ m) * volume (closedBall (0 : Space m) 1))) :=
      ENNReal.Tendsto.mul_const
        ((ENNReal.continuous_ofReal.tendsto _).comp ((continuous_pow m).tendsto 3)) (Or.inr hc)
    rw [heq 3 (by norm_num)]
    refine (hlim.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (heq s (lt_trans (by norm_num) hs)).symm
  refine tendsto_variationalPerimeter_ball_toReal_of_sphere_zero (by omega) b hmin hHmeas
    (fun K hK hKsub ↦ ?_) (by norm_num : (0 : ℝ) < 3) one_pos
    (closedBall_subset_ball (by norm_num : (3 : ℝ) < 5)) μ (fun U hU _ ↦ hμ U hU) hsph
  refine squeeze_zero (fun j ↦ integral_nonneg fun x ↦ norm_nonneg _) (fun j ↦ ?_) hconv
  rw [setIntegral_norm_indicator_sub_eq_volume_symmDiff (hmin j).measurableSet hHmeas]
  exact measureReal_mono (inter_subset_inter_right _ (hKsub.trans ball_subset_closedBall))
    (measure_ne_top_of_subset inter_subset_right (isCompact_closedBall _ _).measure_lt_top.ne)

private theorem abs_integral_indicator_mul_sub_le_aux {d : ℕ} {A B K : Set (Space d)}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hK : IsCompact K) {g : Space d → ℝ}
    (hg : Integrable g) {M : ℝ} (hM : ∀ z, ‖g z‖ ≤ M) (hgK : ∀ z, z ∉ K → g z = 0) :
    |(∫ z, A.indicator (fun _ ↦ (1 : ℝ)) z * g z) - ∫ z, B.indicator (fun _ ↦ (1 : ℝ)) z * g z| ≤
      M * volume.real (symmDiff A B ∩ K) := by
  have hiA : Integrable (fun z ↦ A.indicator (fun _ ↦ (1 : ℝ)) z * g z) :=
    (hg.indicator hA).congr (Eventually.of_forall fun z ↦ by by_cases hz : z ∈ A <;> simp [hz])
  have hiB : Integrable (fun z ↦ B.indicator (fun _ ↦ (1 : ℝ)) z * g z) :=
    (hg.indicator hB).congr (Eventually.of_forall fun z ↦ by by_cases hz : z ∈ B <;> simp [hz])
  have hS : MeasurableSet (symmDiff A B ∩ K) := (hA.symmDiff hB).inter hK.measurableSet
  have hSfin : volume (symmDiff A B ∩ K) ≠ ⊤ :=
    measure_ne_top_of_subset inter_subset_right hK.measure_lt_top.ne
  have hint : Integrable ((symmDiff A B ∩ K).indicator (fun _ ↦ M)) :=
    (integrableOn_const hSfin).integrable_indicator hS
  rw [← integral_sub hiA hiB]
  refine abs_integral_le_integral_abs.trans ?_
  calc ∫ z, |A.indicator (fun _ ↦ (1 : ℝ)) z * g z - B.indicator (fun _ ↦ (1 : ℝ)) z * g z|
      ≤ ∫ z, (symmDiff A B ∩ K).indicator (fun _ ↦ M) z := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun z ↦ abs_nonneg _) hint
          (Eventually.of_forall fun z ↦ ?_)
        have hMz : |g z| ≤ M := by rw [← Real.norm_eq_abs]; exact hM z
        by_cases hzS : z ∈ symmDiff A B ∩ K
        · rw [indicator_of_mem hzS]
          rcases Set.mem_symmDiff.mp hzS.1 with ⟨hzA, hzB⟩ | ⟨hzB, hzA⟩
          · simpa [indicator_of_mem hzA, indicator_of_notMem hzB] using hMz
          · simpa [indicator_of_mem hzB, indicator_of_notMem hzA] using hMz
        · rw [indicator_of_notMem hzS]
          by_cases hzK : z ∈ K
          · have hAB : z ∈ A ↔ z ∈ B := by
              by_contra hne
              apply hzS
              refine ⟨Set.mem_symmDiff.mpr ?_, hzK⟩
              tauto
            by_cases hzA : z ∈ A
            · simp [indicator_of_mem hzA, indicator_of_mem (hAB.mp hzA)]
            · simp [indicator_of_notMem hzA, indicator_of_notMem (fun h ↦ hzA (hAB.mpr h))]
          · simp [hgK z hzK]
    _ = M * volume.real (symmDiff A B ∩ K) := by
        rw [integral_indicator hS, setIntegral_const, smul_eq_mul, mul_comm]

/-- **Small excess.** For every `ε > 0` there is `η > 0` such that every local perimeter
minimizer in `Ω ⊇ B̄₅` which is `η`-close in `L¹(B̄₅)` to `{xₙ > 0}` has excess at most `ε` on the
flat cylinder, for every perimeter representation on `B₃`. -/
theorem exists_excess_le_of_volume_symmDiff_lt {m : ℕ} {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ (G Ω : Set (Space (m + 1))),
      IsLocalPerimeterMinimizer (EuclideanSpace.basisFun (Fin (m + 1)) ℝ) G Ω →
      closedBall 0 5 ⊆ Ω →
      volume.real (symmDiff G (positiveHalfspace (verticalDirection m)) ∩ closedBall 0 5) < η →
      ∀ (μ : Measure (Space (m + 1))) (ν : Space (m + 1) → Space (m + 1)),
        IsPerimeterRepresentation (EuclideanSpace.basisFun (Fin (m + 1)) ℝ) G (ball 0 3) μ ν →
        ∫ y in cylinderSet (ball (0 : Space m) 2) 1,
          (1 - inner ℝ (ν y) (verticalDirection m)) ∂μ ≤ ε := by
  set b := EuclideanSpace.basisFun (Fin (m + 1)) ℝ with hb
  set e := verticalDirection m with he
  set H := positiveHalfspace e with hH
  have he1 : ‖e‖ = 1 := norm_verticalDirection m
  have hHmeas : MeasurableSet H := (isOpen_positiveHalfspace e).measurableSet
  set vol₁ := volume.real (closedBall (0 : Space m) 1) with hvol₁
  -- a radius `ρ < 3` with `P(H, B₃) - P(H, B_ρ) < ε / 2`
  have hcont : Tendsto (fun r : ℝ ↦ r ^ m * vol₁) (𝓝[<] 3) (𝓝 (3 ^ m * vol₁)) :=
    (((continuous_pow m).tendsto 3).mul_const vol₁).mono_left nhdsWithin_le_nhds
  obtain ⟨ρ, hρ1, hρ2⟩ := ((hcont.eventually (lt_mem_nhds
    (show 3 ^ m * vol₁ - ε / 2 < 3 ^ m * vol₁ by linarith))).and
      (Ioo_mem_nhdsLT (show (9 / 4 : ℝ) < 3 by norm_num))).exists
  have hρ1' : 3 ^ m * vol₁ - ε / 2 < ρ ^ m * vol₁ := hρ1
  have hρpos : 0 < ρ := by linarith [hρ2.1]
  set φ : Space (m + 1) → ℝ := ⇑(flatCutoff m hρpos hρ2.2) with hφdef
  have hφs : ContDiff ℝ 1 φ := (flatCutoff m hρpos hρ2.2).contDiff
  have hφc : HasCompactSupport φ := (flatCutoff m hρpos hρ2.2).hasCompactSupport
  have hφsupp : tsupport φ ⊆ ball 0 3 := by
    rw [hφdef, ContDiffBump.tsupport_eq]
    exact closedBall_subset_ball (by show (ρ + 3) / 2 < 3; linarith [hρ2.2])
  have hφ01 : ∀ z, 0 ≤ φ z ∧ φ z ≤ 1 := fun z ↦
    ⟨(flatCutoff m hρpos hρ2.2).nonneg, (flatCutoff m hρpos hρ2.2).le_one⟩
  have hφball : ∀ z ∈ closedBall (0 : Space (m + 1)) ρ, φ z = 1 := fun z hz ↦
    (flatCutoff m hρpos hρ2.2).one_of_mem_closedBall hz
  have hφ1 : ∀ z ∈ cylinderSet (ball (0 : Space m) 2) 1, φ z = 1 := by
    intro z hz
    apply hφball
    rw [mem_closedBall, dist_zero_right]
    linarith [norm_lt_of_mem_flatCylinder hz, hρ2.1]
  -- the limit of the bounds
  set L : ℝ := (variationalPerimeter b H (ball 0 3)).toReal +
    ∫ z, H.indicator (fun _ ↦ (1 : ℝ)) z * fderiv ℝ φ z e with hL
  have hLle : L < ε := by
    have h1 := integral_indicator_halfspace_mul_fderiv_le hφs hφc hφsupp hφ01 hρ2.2.le
      (fun z hz ↦ hφball z (ball_subset_closedBall hz))
    have h2 : (variationalPerimeter b H (ball 0 3)).toReal = 3 ^ m * vol₁ :=
      positive_halfspace_perimeter_toReal b he1 (by norm_num)
    have h3 : (variationalPerimeter b H (ball 0 ρ)).toReal = ρ ^ m * vol₁ :=
      positive_halfspace_perimeter_toReal b he1 hρpos
    rw [hL, h2]
    rw [h3] at h1
    linarith [hρ1']
  by_contra hcon
  have key : ∀ j : ℕ, ∃ (G Ω : Set (Space (m + 1))) (μ : Measure (Space (m + 1)))
      (ν : Space (m + 1) → Space (m + 1)), IsLocalPerimeterMinimizer b G Ω ∧
        closedBall 0 5 ⊆ Ω ∧
        volume.real (symmDiff G H ∩ closedBall 0 5) < 1 / ((j : ℝ) + 1) ∧
        IsPerimeterRepresentation b G (ball 0 3) μ ν ∧
        ε < ∫ y in cylinderSet (ball (0 : Space m) 2) 1, (1 - inner ℝ (ν y) e) ∂μ := by
    intro j
    by_contra h
    apply hcon
    refine ⟨1 / ((j : ℝ) + 1), by positivity, fun G Ω h1 h2 h3 μ ν h4 ↦ ?_⟩
    by_contra h5
    exact h ⟨G, Ω, μ, ν, h1, h2, h3, h4, not_le.mp h5⟩
  choose G Ω μ ν hmin hΩ hclose hrep hexc using key
  have hmin5 : ∀ j, IsLocalPerimeterMinimizer b (G j) (ball 0 5) := fun j ↦
    (hmin j).mono isOpen_ball (ball_subset_closedBall.trans (hΩ j))
  have hconv : Tendsto (fun j ↦ volume.real (symmDiff (G j) H ∩ closedBall 0 5)) atTop (𝓝 0) :=
    squeeze_zero (fun j ↦ measureReal_nonneg) (fun j ↦ (hclose j).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hper := tendsto_perimeter_ball_three_of_tendsto_halfspace hmin5 hconv
  -- the fluxes converge
  set g : Space (m + 1) → ℝ := fun z ↦ fderiv ℝ φ z e with hg
  have hgcont : Continuous g := (hφs.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hgc : HasCompactSupport g := hφc.fderiv_apply (𝕜 := ℝ) e
  have hgint : Integrable g := hgcont.integrable_of_hasCompactSupport hgc
  obtain ⟨M, hM⟩ := hgcont.bounded_above_of_compact_support hgc
  have hgK : ∀ z, z ∉ closedBall (0 : Space (m + 1)) 5 → g z = 0 := by
    intro z hz
    have hz' : z ∉ tsupport φ := fun h ↦ hz (ball_subset_closedBall
      (ball_subset_ball (by norm_num : (3 : ℝ) ≤ 5) (hφsupp h)))
    simp [hg, fderiv_of_notMem_tsupport ℝ hz']
  have hflux : Tendsto (fun j ↦ ∫ z, (G j).indicator (fun _ ↦ (1 : ℝ)) z * g z) atTop
      (𝓝 (∫ z, H.indicator (fun _ ↦ (1 : ℝ)) z * g z)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun j ↦ norm_nonneg _) (fun j ↦ ?_) (by simpa using hconv.const_mul M)
    rw [Real.norm_eq_abs]
    exact abs_integral_indicator_mul_sub_le_aux (hmin j).measurableSet hHmeas
      (isCompact_closedBall _ _) hgint hM hgK
  have hlim := hper.add hflux
  have hbound : ∀ j, ε ≤ (variationalPerimeter b (G j) (ball 0 3)).toReal +
      ∫ z, (G j).indicator (fun _ ↦ (1 : ℝ)) z * g z := by
    intro j
    have h1 := integral_flatCylinder_excess_le (hrep j) hφs hφc hφsupp hφ01 hφ1
    have := (hrep j).isFiniteMeasure
    have h2 : (μ j).real (ball 0 3) = (variationalPerimeter b (G j) (ball 0 3)).toReal := by
      rw [measureReal_def, (hrep j).measure_open _ isOpen_ball subset_rfl]
    rw [h2] at h1
    exact (hexc j).le.trans h1
  have hεL : ε ≤ L := ge_of_tendsto' hlim hbound
  linarith

/-! ### 4. The normalized consequence of `ExcessEpsilonRegularityHyp` -/

/-- **Key lemma.** Under `ExcessEpsilonRegularityHyp`, there is `η > 0` such that every local
perimeter minimizer `G` in `Ω ⊇ B̄₅` with `0 ∈ ∂G` which is `η`-close in `L¹(B̄₅)` to the
half-space `{xₙ > 0}` has `0` as a `C¹` boundary point. -/
theorem ExcessEpsilonRegularityHyp.exists_isC1BoundaryPoint_zero
    (hyp : ExcessEpsilonRegularityHyp) (m : ℕ) :
    ∃ η : ℝ, 0 < η ∧ ∀ (G Ω : Set (Space (m + 1))),
      IsLocalPerimeterMinimizer (EuclideanSpace.basisFun (Fin (m + 1)) ℝ) G Ω →
      closedBall 0 5 ⊆ Ω →
      volume.real (symmDiff G (positiveHalfspace (verticalDirection m)) ∩ closedBall 0 5) < η →
      (0 : Space (m + 1)) ∈ measureTheoreticBoundary G → IsC1BoundaryPoint G 0 := by
  set b := EuclideanSpace.basisFun (Fin (m + 1)) ℝ with hb
  obtain ⟨ε₀, hε₀, hhyp⟩ := hyp m
  obtain ⟨η₂, hη₂, hexc⟩ := exists_excess_le_of_volume_symmDiff_lt (m := m) hε₀
  refine ⟨min (flatTrapThreshold m) η₂, lt_min (flatTrapThreshold_pos m) hη₂,
    fun G Ω hmin hΩ hclose h0 ↦ ?_⟩
  obtain ⟨hbot, htop⟩ := trapped_of_volume_symmDiff_lt hmin hΩ
    (hclose.trans_le (min_le_left _ _))
  have hP : variationalPerimeter b G (ball 0 3) ≠ ⊤ :=
    hmin.perimeter_ball_ne_top 0 3 (by norm_num)
      ((closedBall_subset_closedBall (by norm_num)).trans hΩ)
  obtain ⟨μ, ν, hrep⟩ := exists_isPerimeterRepresentation b hmin.measurableSet isOpen_ball hP
  have := hrep.isFiniteMeasure
  have hex := hexc G Ω hmin hΩ (hclose.trans_le (min_le_right _ _)) μ ν hrep
  set C := cylinderSet (ball (0 : Space m) 2) 1 with hC
  have hCopen : IsOpen C := isOpen_cylinderSet isOpen_ball 1
  have hC3 : C ⊆ ball 0 3 := fun z hz ↦
    mem_ball_zero_iff.mpr ((norm_lt_of_mem_flatCylinder hz).trans (by norm_num))
  have hflat : IsFlatConfig b G Ω (μ.restrict C) ν :=
    { min := hmin
      slab :=
        { measurableSet := hmin.measurableSet
          isOpen := isOpen_ball
          pos := by norm_num
          lt := by norm_num
          rep := hrep.restrict hCopen hC3
          bot := hbot
          top := htop }
      cyl := hC3.trans (ball_subset_closedBall.trans
        ((closedBall_subset_closedBall (by norm_num)).trans hΩ))
      zero_mem := h0 }
  have hexcess : (projectedExcessMeasure (μ.restrict C) ν).real (ball 0 2) ≤ ε₀ := by
    rw [projectedExcessMeasure_restrict_real_eq hrep.integrable hrep.norm_eq_one
      measurableSet_ball (fun z hz ↦ hz.1)]
    exact hex
  exact hhyp G Ω (μ.restrict C) ν hflat hexcess 0 h0 (by rw [horizontal_zero_bridge_aux]; simp)
    (by simp)

/-! ### 5. ε-regularity -/

/-- **ε-regularity from excess-form ε-regularity.** -/
theorem epsilonRegularityHyp_of_excess (hyp : ExcessEpsilonRegularityHyp) :
    EpsilonRegularityHyp := by
  intro d E Ω x hmin hx hT
  rcases d with _ | m
  · exact absurd hx.1
      (by rw [measureTheoreticBoundary_eq_empty_of_space_zero]; exact notMem_empty x)
  obtain ⟨η, hη, hreg⟩ := hyp.exists_isC1BoundaryPoint_zero m
  obtain ⟨T, ⟨-, r, hblow⟩, e, he, hTe⟩ := hT
  obtain ⟨Q, hQ⟩ := exists_linearIsometryEquiv_verticalDirection he
  have hEmeas := hmin.measurableSet
  have hvol := (hblow.congr_ae hTe).tendsto_volume_symmDiff hEmeas
    (isOpen_positiveHalfspace e).measurableSet (isCompact_closedBall (0 : Space (m + 1)) 5)
  obtain ⟨δ, hδ, hδΩ⟩ := Metric.isOpen_iff.mp hmin.isOpen_domain x hx.2
  have hsmall : ∀ᶠ j in atTop, 5 * r j < δ := by
    have h1 := hblow.2.1.const_mul 5
    rw [mul_zero] at h1
    exact h1.eventually (gt_mem_nhds hδ)
  obtain ⟨j, hj1, hj2⟩ :=
    (hsmall.and (hvol.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr hη)))).exists
  set s := r j with hsdef
  have hs : 0 < s := hblow.1 j
  have hGmin := hmin.preimage_similarity (by omega) Q x hs
  have hΩ' : closedBall 0 5 ⊆ similarity Q x s ⁻¹' Ω := by
    intro w hw
    apply hδΩ
    rw [mem_closedBall, dist_zero_right] at hw
    show x + s • Q w ∈ ball x δ
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hs.le,
      Q.norm_map]
    nlinarith
  have hclose : volume.real (symmDiff (similarity Q x s ⁻¹' E)
      (positiveHalfspace (verticalDirection m)) ∩ closedBall 0 5) < η := by
    rw [symmDiff_preimage_similarity_inter_closedBall, hQ, measureReal_def,
      Q.measurePreserving.measure_preimage_emb Q.toHomeomorph.measurableEmbedding]
    exact ENNReal.toReal_lt_of_lt_ofReal hj2
  have h0 : (0 : Space (m + 1)) ∈ measureTheoreticBoundary (similarity Q x s ⁻¹' E) := by
    rw [measureTheoreticBoundary_preimage_similarity E Q x hs, mem_preimage]
    simpa [similarity] using hx.1
  have hC1 := hreg _ _ hGmin hΩ' hclose h0
  rw [isC1BoundaryPoint_preimage_similarity_iff Q x hs] at hC1
  simpa [similarity] using hC1

/-! ### 6. Upper semicontinuity of singular sets -/

/-- **Upper semicontinuity of singular sets from excess-form ε-regularity.** -/
theorem singularSetUSCHyp_of_excess (hyp : ExcessEpsilonRegularityHyp) : SingularSetUSCHyp := by
  intro d E F hminE hminF hconv x x₀ hsing hlim
  rcases d with _ | m
  · exact absurd (hsing 0).1
      (by rw [measureTheoreticBoundary_eq_empty_of_space_zero]; exact notMem_empty _)
  set b := EuclideanSpace.basisFun (Fin (m + 1)) ℝ with hb
  have hFmeas := hminF.measurableSet
  have hEmeas : ∀ᶠ j in atTop, MeasurableSet (E j) :=
    (hminE 1 one_pos).mono fun j hj ↦ hj.measurableSet
  have hvolconv : ∀ K : Set (Space (m + 1)), IsCompact K →
      Tendsto (fun j ↦ volume (symmDiff (E j) F ∩ K)) atTop (𝓝 0) := fun K hK ↦
    tendsto_volume_symmDiff_of_integral_aux hFmeas hK hEmeas (hconv K hK)
  -- `x₀` is a boundary point of `F`
  have hx₀B : x₀ ∈ measureTheoreticBoundary F := by
    intro ρ hρ
    set ρ' := min ρ 1 with hρ'
    have hρ'pos : 0 < ρ' := lt_min hρ one_pos
    have hρ'ρ : ρ' ≤ ρ := min_le_left _ _
    have hρ'1 : ρ' ≤ 1 := min_le_right _ _
    set c := minimizerVolumeDensityConst m * (ρ' / 2) ^ (m + 1) with hc
    have hcpos : 0 < c := mul_pos (minimizerVolumeDensityConst_pos m) (by positivity)
    have hev1 := hminE (‖x₀‖ + 2) (by positivity)
    have hev2 : ∀ᶠ j in atTop, x j ∈ ball x₀ (ρ' / 2) :=
      hlim.eventually (ball_mem_nhds x₀ (by positivity))
    have hev3 : ∀ᶠ j in atTop,
        volume (symmDiff (E j) F ∩ closedBall x₀ ρ') < ENNReal.ofReal c :=
      (hvolconv _ (isCompact_closedBall x₀ ρ')).eventually
        (gt_mem_nhds (ENNReal.ofReal_pos.mpr hcpos))
    obtain ⟨j, hj1, hj2, hj3⟩ := (hev1.and (hev2.and hev3)).exists
    have hxjB : x j ∈ measureTheoreticBoundary (E j) := (hsing j).1
    have hdist : dist (x j) x₀ < ρ' / 2 := hj2
    have hsub : closedBall (x j) (ρ' / 2) ⊆ ball 0 (‖x₀‖ + 2) := by
      intro z hz
      rw [mem_closedBall] at hz
      rw [mem_ball, dist_zero_right]
      have h1 := dist_triangle z (x j) x₀
      have h2 : ‖z‖ ≤ ‖x₀‖ + dist z x₀ := by
        have := norm_add_le x₀ (z - x₀)
        rw [add_sub_cancel] at this
        rw [dist_eq_norm]
        linarith
      linarith
    have hball : ∀ z ∈ ball (x j) (ρ' / 2), z ∈ closedBall x₀ ρ' ∧ z ∈ ball x₀ ρ := by
      intro z hz
      rw [mem_ball] at hz
      have h1 := dist_triangle z (x j) x₀
      exact ⟨by rw [mem_closedBall]; linarith, by rw [mem_ball]; linarith⟩
    have hlt : volume.real (symmDiff (E j) F ∩ closedBall x₀ ρ') < c :=
      ENNReal.toReal_lt_of_lt_ofReal hj3
    have hSfin : volume (symmDiff (E j) F ∩ closedBall x₀ ρ') ≠ ⊤ :=
      measure_ne_top_of_subset inter_subset_right (isCompact_closedBall _ _).measure_lt_top.ne
    constructor
    · intro hF0
      have hdens := hj1.volume_inter_ball_ge hxjB (by positivity) hsub
      have h1 : volume (E j ∩ ball (x j) (ρ' / 2)) ≤
          volume (symmDiff (E j) F ∩ closedBall x₀ ρ') := by
        calc volume (E j ∩ ball (x j) (ρ' / 2))
            ≤ volume ((symmDiff (E j) F ∩ closedBall x₀ ρ') ∪ (F ∩ ball x₀ ρ)) := by
              refine measure_mono fun z hz ↦ ?_
              by_cases hzF : z ∈ F
              · exact Or.inr ⟨hzF, (hball z hz.2).2⟩
              · exact Or.inl ⟨Set.mem_symmDiff.mpr (Or.inl ⟨hz.1, hzF⟩), (hball z hz.2).1⟩
          _ ≤ volume (symmDiff (E j) F ∩ closedBall x₀ ρ') + volume (F ∩ ball x₀ ρ) :=
              measure_union_le _ _
          _ = _ := by rw [hF0, add_zero]
      have h2 := ENNReal.toReal_mono hSfin h1
      rw [← measureReal_def, ← measureReal_def] at h2
      linarith
    · intro hF0
      have hdens := hj1.volume_sdiff_ball_ge hxjB (by positivity) hsub
      have h1 : volume (ball (x j) (ρ' / 2) \ E j) ≤
          volume (symmDiff (E j) F ∩ closedBall x₀ ρ') := by
        calc volume (ball (x j) (ρ' / 2) \ E j)
            ≤ volume ((symmDiff (E j) F ∩ closedBall x₀ ρ') ∪ (ball x₀ ρ \ F)) := by
              refine measure_mono fun z hz ↦ ?_
              by_cases hzF : z ∈ F
              · exact Or.inl ⟨Set.mem_symmDiff.mpr (Or.inr ⟨hzF, hz.2⟩), (hball z hz.1).1⟩
              · exact Or.inr ⟨(hball z hz.1).2, hzF⟩
          _ ≤ volume (symmDiff (E j) F ∩ closedBall x₀ ρ') + volume (ball x₀ ρ \ F) :=
              measure_union_le _ _
          _ = _ := by rw [hF0, add_zero]
      have h2 := ENNReal.toReal_mono hSfin h1
      rw [← measureReal_def, ← measureReal_def] at h2
      linarith
  refine ⟨hx₀B, fun hC1 ↦ ?_⟩
  -- a regular point of `F`: a blow-up of `F` is close to a half-space at a fixed scale
  obtain ⟨η, hη, hreg⟩ := hyp.exists_isC1BoundaryPoint_zero m
  obtain ⟨e, he, hblow⟩ := hC1.exists_isBlowupLimit_positiveHalfspace hFmeas
  obtain ⟨Q, hQ⟩ := exists_linearIsometryEquiv_verticalDirection he
  set H := positiveHalfspace (verticalDirection m) with hHdef
  have hHmeas : MeasurableSet H := (isOpen_positiveHalfspace _).measurableSet
  have hblow' := hblow (fun k : ℕ ↦ 1 / ((k : ℝ) + 1)) (fun k ↦ by positivity)
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hvolF := hblow'.tendsto_volume_symmDiff hFmeas (isOpen_positiveHalfspace e).measurableSet
    (isCompact_closedBall (0 : Space (m + 1)) 6)
  obtain ⟨k, hk⟩ :=
    (hvolF.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr (by positivity : 0 < η / 3)))).exists
  set s : ℝ := 1 / ((k : ℝ) + 1) with hsdef
  have hs : 0 < s := by positivity
  have hF₀ : volume (symmDiff (similarity Q x₀ s ⁻¹' F) H ∩ closedBall 0 6) <
      ENNReal.ofReal (η / 3) := by
    rw [symmDiff_preimage_similarity_inter_closedBall, hQ,
      Q.measurePreserving.measure_preimage_emb Q.toHomeomorph.measurableEmbedding]
    exact hk
  -- the translation constant of `H`
  have hHfin : variationalPerimeter b H (ball 0 7) ≠ ⊤ := by
    rw [show H = {x : Space (m + 1) | 0 < inner ℝ (verticalDirection m) x} from rfl,
      positive_halfspace_perimeter_closedBall_volume b (norm_verticalDirection m)
        (by norm_num)]
    exact measure_closedBall_lt_top.ne
  set B : ℝ := (variationalPerimeter b H (ball 0 7)).toReal with hBdef
  have hB0 : 0 ≤ B := ENNReal.toReal_nonneg
  have hBP : variationalPerimeter b H (ball 0 7) ≤ ENNReal.ofReal B := by
    rw [hBdef, ENNReal.ofReal_toReal hHfin]
  -- choice of `j`
  set R : ℝ := ‖x₀‖ + 6 * s + 1 with hR
  set τ : ℝ := min s (s * η / (3 * (B + 1))) with hτ
  have hτpos : 0 < τ := lt_min hs (by positivity)
  have hev1 := hminE R (by positivity)
  have hev2 : ∀ᶠ j in atTop, x j ∈ ball x₀ τ := hlim.eventually (ball_mem_nhds x₀ hτpos)
  have hev3 : ∀ᶠ j in atTop, volume (symmDiff (E j) F ∩ closedBall x₀ (6 * s)) <
      ENNReal.ofReal (s ^ (m + 1) * (η / 3)) :=
    (hvolconv _ (isCompact_closedBall x₀ (6 * s))).eventually
      (gt_mem_nhds (ENNReal.ofReal_pos.mpr (by positivity)))
  obtain ⟨j, hj1, hj2, hj3⟩ := (hev1.and (hev2.and hev3)).exists
  have hdj : ‖x j - x₀‖ < τ := by rw [← dist_eq_norm]; exact hj2
  have hdjs : ‖x j - x₀‖ < s := lt_of_lt_of_le hdj (min_le_left _ _)
  -- the configuration at `x j`
  set G := similarity Q (x j) s ⁻¹' E j with hG
  have hGmin := hj1.preimage_similarity (by omega) Q (x j) hs
  have hΩ' : closedBall 0 5 ⊆ similarity Q (x j) s ⁻¹' ball 0 R := by
    intro w hw
    rw [mem_closedBall, dist_zero_right] at hw
    rw [mem_preimage, mem_ball, dist_zero_right, similarity]
    have h1 : ‖x j + s • Q w‖ ≤ ‖x j‖ + s * ‖w‖ := by
      calc ‖x j + s • Q w‖ ≤ ‖x j‖ + ‖s • Q w‖ := norm_add_le _ _
        _ = ‖x j‖ + s * ‖w‖ := by rw [norm_smul, Real.norm_of_nonneg hs.le, Q.norm_map]
    have h2 : ‖x j‖ ≤ ‖x₀‖ + ‖x j - x₀‖ := by
      have := norm_add_le x₀ (x j - x₀)
      rwa [add_sub_cancel] at this
    nlinarith
  have h0 : (0 : Space (m + 1)) ∈ measureTheoreticBoundary G := by
    rw [hG, measureTheoreticBoundary_preimage_similarity (E j) Q (x j) hs, mem_preimage]
    simpa [similarity] using (hsing j).1
  -- closeness of `G` to `H`
  set z : Space (m + 1) := s⁻¹ • Q.symm (x j - x₀) with hz
  have hzn : ‖z‖ = ‖x j - x₀‖ / s := by
    rw [hz, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hs.le), LinearIsometryEquiv.norm_map]
    ring
  have hz1 : ‖z‖ < 1 := by
    rw [hzn, div_lt_one hs]
    exact hdjs
  have hzB : ‖z‖ * B ≤ η / 3 := by
    have h1 : ‖x j - x₀‖ < s * η / (3 * (B + 1)) := lt_of_lt_of_le hdj (min_le_right _ _)
    have h2 : ‖z‖ < η / (3 * (B + 1)) := by
      rw [hzn, div_lt_iff₀ hs]
      calc ‖x j - x₀‖ < s * η / (3 * (B + 1)) := h1
        _ = η / (3 * (B + 1)) * s := by ring
    have h3 : ‖z‖ * B ≤ ‖z‖ * (B + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
    have h4 : ‖z‖ * (B + 1) < η / 3 := by
      have := (lt_div_iff₀ (by positivity : (0 : ℝ) < 3 * (B + 1))).mp h2
      nlinarith
    linarith
  set F' := similarity Q (x j) s ⁻¹' F with hF'
  set F₀ := similarity Q x₀ s ⁻¹' F with hF₀def
  have hF'F₀ : F' = (fun w ↦ w + z) ⁻¹' F₀ := by
    ext w
    simp only [hF', hF₀def, mem_preimage, similarity]
    have : x₀ + s • Q (w + z) = x j + s • Q w := by
      rw [hz, map_add, map_smul, Q.apply_symm_apply, smul_add, smul_smul,
        mul_inv_cancel₀ hs.ne', one_smul]
      abel
    rw [this]
  -- (a) `G` versus `F'`
  have ha : volume (symmDiff G F' ∩ closedBall 0 5) < ENNReal.ofReal (η / 3) := by
    have hset : symmDiff G F' ∩ closedBall 0 5 =
        similarity Q (x j) s ⁻¹' (symmDiff (E j) F ∩ closedBall (x j) (s * 5)) := by
      rw [preimage_inter, preimage_symmDiff, preimage_similarity_closedBall Q (x j) hs]
    have hsub : closedBall (x j) (s * 5) ⊆ closedBall x₀ (6 * s) := by
      intro w hw
      rw [mem_closedBall] at hw ⊢
      have h1 := dist_triangle w (x j) x₀
      rw [dist_eq_norm (x j) x₀] at h1
      linarith
    rw [hset, volume_preimage_similarity Q (x j) hs]
    calc ENNReal.ofReal ((s ^ (m + 1))⁻¹) * volume (symmDiff (E j) F ∩ closedBall (x j) (s * 5))
        ≤ ENNReal.ofReal ((s ^ (m + 1))⁻¹) * volume (symmDiff (E j) F ∩ closedBall x₀ (6 * s)) :=
          mul_le_mul_right (measure_mono (inter_subset_inter_right _ hsub)) _
      _ < ENNReal.ofReal ((s ^ (m + 1))⁻¹) * ENNReal.ofReal (s ^ (m + 1) * (η / 3)) :=
          ENNReal.mul_lt_mul_right (ENNReal.ofReal_pos.mpr (by positivity)).ne'
            ENNReal.ofReal_ne_top hj3
      _ = ENNReal.ofReal (η / 3) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← mul_assoc,
            inv_mul_cancel₀ (pow_pos hs _).ne', one_mul]
  -- (b) `F'` versus the translated half-space
  have hb1 : volume (symmDiff F' ((fun w ↦ w + z) ⁻¹' H) ∩ closedBall 0 5) <
      ENNReal.ofReal (η / 3) := by
    have hset : symmDiff F' ((fun w ↦ w + z) ⁻¹' H) ∩ closedBall 0 5 =
        (fun w ↦ w + z) ⁻¹' (symmDiff F₀ H ∩ closedBall z 5) := by
      rw [hF'F₀, preimage_inter, preimage_symmDiff]
      congr 1
      ext w
      simp [dist_eq_norm]
    rw [hset, measure_preimage_add_right]
    refine lt_of_le_of_lt (measure_mono (inter_subset_inter_right _ ?_)) hF₀
    intro w hw
    rw [mem_closedBall] at hw ⊢
    rw [dist_zero_right]
    have h1 := dist_triangle w z 0
    simp only [dist_zero_right] at h1
    linarith
  -- (c) the translation of the half-space
  have hc1 : volume (symmDiff ((fun w ↦ w + z) ⁻¹' H) H ∩ closedBall 0 5) ≤
      ENNReal.ofReal (η / 3) := by
    have hpre : MeasurableSet ((fun w ↦ w + z) ⁻¹' H) := hHmeas.preimage (by fun_prop)
    have htr := integral_phase_translation_le_perimeter_bound b hHmeas z
      (by linarith : (5 : ℝ) + ‖z‖ < 7) hB0 hBP
    have heq : ∫ w in closedBall (0 : Space (m + 1)) 5,
        ‖H.indicator (fun _ ↦ (1 : ℝ)) (w + z) - H.indicator (fun _ ↦ (1 : ℝ)) w‖ =
        volume.real (symmDiff ((fun w ↦ w + z) ⁻¹' H) H ∩ closedBall 0 5) := by
      rw [← setIntegral_norm_indicator_sub_eq_volume_symmDiff hpre hHmeas]
      rfl
    rw [heq] at htr
    rw [← ofReal_measureReal (measure_ne_top_of_subset inter_subset_right
      (isCompact_closedBall _ _).measure_lt_top.ne)]
    exact ENNReal.ofReal_le_ofReal (htr.trans hzB)
  -- the sum
  have hGclose : volume (symmDiff G H ∩ closedBall 0 5) < ENNReal.ofReal η := by
    have h1 := measure_symmDiff_inter_le_aux G F' H (closedBall 0 5)
    have h2 := measure_symmDiff_inter_le_aux F' ((fun w ↦ w + z) ⁻¹' H) H (closedBall 0 5)
    have h3 : ENNReal.ofReal (η / 3) + ENNReal.ofReal (η / 3) + ENNReal.ofReal (η / 3) =
        ENNReal.ofReal η := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring
    calc volume (symmDiff G H ∩ closedBall 0 5)
        ≤ volume (symmDiff G F' ∩ closedBall 0 5) +
            (volume (symmDiff F' ((fun w ↦ w + z) ⁻¹' H) ∩ closedBall 0 5) +
              volume (symmDiff ((fun w ↦ w + z) ⁻¹' H) H ∩ closedBall 0 5)) :=
          h1.trans (add_le_add le_rfl h2)
      _ < ENNReal.ofReal (η / 3) + (ENNReal.ofReal (η / 3) + ENNReal.ofReal (η / 3)) :=
          ENNReal.add_lt_add_of_lt_of_le
            (ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top,
              ENNReal.ofReal_ne_top⟩) (add_le_add hb1.le hc1)) ha (add_le_add hb1.le hc1)
      _ = ENNReal.ofReal η := by rw [← add_assoc, h3]
  have hclose : volume.real (symmDiff G H ∩ closedBall 0 5) < η :=
    ENNReal.toReal_lt_of_lt_ofReal hGclose
  have hC1j := hreg G _ hGmin hΩ' hclose h0
  rw [hG, isC1BoundaryPoint_preimage_similarity_iff Q (x j) hs] at hC1j
  exact (hsing j).2 (by simpa [similarity] using hC1j)

end SerrinEpigraph
