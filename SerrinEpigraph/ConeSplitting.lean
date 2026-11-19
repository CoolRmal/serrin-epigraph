module

public import SerrinEpigraph.PerimeterMonotonicity
public import SerrinEpigraph.CylinderSlicing
public import SerrinEpigraph.DirectedMinimizingCone

/-!
# Minimizing cones, tangent cones, cone splitting (GR5) and cylindrical reduction (GR6)

This module packages the classification-of-cones toolkit of
`docs/rigidity-proof/gmt-regularity.md` (GR5, GR6, the induction step of GR16) and
`docs/rigidity-proof/bv-minimizers.md` (BV11):

1. `IsMinimizingCone E`: a measurable, nontrivial, a.e. dilation invariant set which locally
   minimizes perimeter in all of `Space d`; stability under null sets, complements and linear
   isometries; the origin lies in its measure-theoretic boundary
   (`IsMinimizingCone.zero_mem_measureTheoreticBoundary`); its boundary is the frontier of the
   canonical open representative and the support of any perimeter measure.
2. Blow-up limits and tangent cones (`IsBlowupLimit`, `IsTangentCone`, BV11): every measurable
   `L¹_loc` blow-up limit of a local minimizer at a measure-theoretic boundary point is a
   minimizing cone with constant density ratio
   (`IsLocalPerimeterMinimizer.isMinimizingCone_of_isBlowupLimit`), and minimizing cones admit
   tangent cones at all boundary points along subsequences of any scale sequence
   (`IsMinimizingCone.exists_isBlowupLimit`).
3. **GR5** (`ae_mem_add_smul_iff_of_isBlowupLimit`): blow-up limits of a cone at `x₀` which are
   themselves cones are a.e. invariant under all translations along `x₀`. Translation
   invariances of the original cone are inherited
   (`ae_mem_add_smul_iff_of_isBlowupLimit_of_invariant`).
4. **GR6** (`IsMinimizingCone.exists_cylinder_of_vertical_invariant`,
   `IsMinimizingCone.exists_cylinder_of_invariant`): a minimizing cone invariant along a unit
   direction is, after a linear isometry, a.e. the cylinder over a minimizing cone one dimension
   lower.
5. Cylinders over half-spaces are half-spaces.
6. The base case: a nontrivial a.e. dilation invariant subset of `Space 1` is a.e. a half-line
   (`ae_eq_positiveHalfspace_of_ae_cone_one`).
7. The dimension-reduction step of GR16
   (`IsMinimizingCone.isTangentCone_ae_eq_halfspace_of_lower`) and its consequences in ambient
   dimension two.
8. Half-spaces are minimizing cones (`isMinimizingCone_positiveHalfspace`, by calibration), so on
   the line minimizing cones are exactly the half-lines.
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory InnerProductSpace Filter
open scoped Topology ENNReal Pointwise

namespace SerrinEpigraph

/-! ### 1. Minimizing cones -/

/-- A nontrivial, a.e. dilation invariant local perimeter minimizer in all of `Space d`. -/
structure IsMinimizingCone {d : ℕ} (E : Set (Space d)) : Prop where
  measurableSet : MeasurableSet E
  nontrivial : volume E ≠ 0 ∧ volume Eᶜ ≠ 0
  dilation : ∀ a : ℝ, 0 < a → ∀ᵐ x ∂volume, x ∈ E ↔ a • x ∈ E
  minimizer : IsLocalPerimeterMinimizer (EuclideanSpace.basisFun (Fin d) ℝ) E univ

theorem IsMinimizingCone.isLocalPerimeterMinimizer {d : ℕ} {E : Set (Space d)}
    (hE : IsMinimizingCone E) (b : OrthonormalBasis (Fin d) ℝ (Space d)) :
    IsLocalPerimeterMinimizer b E univ :=
  hE.minimizer.of_basis b

theorem IsMinimizingCone.of_isLocalPerimeterMinimizer {d : ℕ}
    {b : OrthonormalBasis (Fin d) ℝ (Space d)} {E : Set (Space d)}
    (hmin : IsLocalPerimeterMinimizer b E univ) (hnt : volume E ≠ 0 ∧ volume Eᶜ ≠ 0)
    (hdil : ∀ a : ℝ, 0 < a → ∀ᵐ x ∂volume, x ∈ E ↔ a • x ∈ E) : IsMinimizingCone E :=
  ⟨hmin.measurableSet, hnt, hdil, hmin.of_basis _⟩

theorem IsDirectedMinimizingCone.isMinimizingCone {m : ℕ} {E : Set (Space (m + 1))}
    (hE : IsDirectedMinimizingCone E) : IsMinimizingCone E :=
  ⟨hE.measurableSet, hE.nontrivial, hE.dilation, hE.minimizer⟩

/-- Almost-everywhere statements pull back along nondegenerate affine maps `y ↦ x₀ + c • y`. -/
private theorem ae_comp_add_smul {d : ℕ} {P : Space d → Prop} (h : ∀ᵐ z ∂volume, P z) (x₀ : Space d)
    {c : ℝ} (hc : c ≠ 0) : ∀ᵐ y ∂volume, P (x₀ + c • y) := by
  have h1 : ∀ᵐ w ∂volume, P (x₀ + w) :=
    (measurePreserving_add_left volume x₀).quasiMeasurePreserving.ae h
  exact (Measure.quasiMeasurePreserving_smul volume hc).ae h1

theorem IsMinimizingCone.congr_ae {d : ℕ} {E E' : Set (Space d)} (hE : IsMinimizingCone E)
    (hE' : MeasurableSet E') (h : E =ᵐ[volume] E') : IsMinimizingCone E' := by
  have hiff : ∀ᵐ x ∂volume, x ∈ E ↔ x ∈ E' := by
    filter_upwards [h] with x hx
    exact Iff.of_eq hx
  have hc : Eᶜ =ᵐ[volume] E'ᶜ := ae_eq_set_compl_compl.mpr h
  refine ⟨hE', ⟨?_, ?_⟩, fun a ha ↦ ?_, hE.minimizer.congr_ae hE' ?_⟩
  · rw [← measure_congr h]
    exact hE.nontrivial.1
  · rw [← measure_congr hc]
    exact hE.nontrivial.2
  · have h2 := (Measure.quasiMeasurePreserving_smul volume ha.ne').ae hiff
    filter_upwards [hiff, h2, hE.dilation a ha] with x h1 h2 h3
    exact h1.symm.trans (h3.trans h2)
  · filter_upwards [hiff] with x hx _
    exact hx

theorem IsMinimizingCone.compl {d : ℕ} {E : Set (Space d)} (hE : IsMinimizingCone E) :
    IsMinimizingCone Eᶜ := by
  refine ⟨hE.measurableSet.compl, ⟨hE.nontrivial.2, by simpa using hE.nontrivial.1⟩,
    fun a ha ↦ ?_, hE.minimizer.compl⟩
  filter_upwards [hE.dilation a ha] with x hx
  simp only [mem_compl_iff]
  exact not_congr hx

theorem IsMinimizingCone.preimage_linearIsometryEquiv {d : ℕ} {E : Set (Space d)}
    (hE : IsMinimizingCone E) (Q : Space d ≃ₗᵢ[ℝ] Space d) : IsMinimizingCone (Q ⁻¹' E) := by
  have hmp := Q.measurePreserving
  refine ⟨hE.measurableSet.preimage Q.continuous.measurable, ⟨?_, ?_⟩, fun a ha ↦ ?_, ?_⟩
  · rw [hmp.measure_preimage hE.measurableSet.nullMeasurableSet]
    exact hE.nontrivial.1
  · rw [← preimage_compl, hmp.measure_preimage hE.measurableSet.compl.nullMeasurableSet]
    exact hE.nontrivial.2
  · have h := hmp.quasiMeasurePreserving.ae (hE.dilation a ha)
    filter_upwards [h] with x hx
    simp only [mem_preimage, map_smul]
    exact hx
  · simpa using hE.minimizer.preimage_isometry Q

/-- A set which is a.e. dilation invariant and null near the origin is null. -/
theorem volume_eq_zero_of_ae_cone_of_ball {d : ℕ} {E : Set (Space d)}
    (hcone : ∀ a : ℝ, 0 < a → ∀ᵐ x ∂volume, x ∈ E ↔ a • x ∈ E) {r : ℝ} (hr : 0 < r)
    (h0 : volume (E ∩ ball 0 r) = 0) : volume E = 0 := by
  have hR : ∀ R : ℝ, 0 < R → volume (E ∩ ball 0 R) = 0 := by
    intro R hR
    set a : ℝ := r / R with ha_def
    have ha : 0 < a := div_pos hr hR
    have hnull : volume ((fun x : Space d ↦ a • x) ⁻¹' (E ∩ ball 0 r)) = 0 := by
      rw [Measure.addHaar_preimage_smul volume ha.ne', h0, mul_zero]
    have hsub : E ∩ ball 0 R ⊆ ((fun x : Space d ↦ a • x) ⁻¹' (E ∩ ball 0 r)) ∪
        {x | ¬(x ∈ E ↔ a • x ∈ E)} := by
      rintro x ⟨hxE, hxB⟩
      by_cases hx : x ∈ E ↔ a • x ∈ E
      · left
        refine ⟨hx.mp hxE, ?_⟩
        rw [mem_ball, dist_zero_right] at hxB
        rw [mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg ha.le]
        calc a * ‖x‖ < a * R := mul_lt_mul_of_pos_left hxB ha
          _ = r := by rw [ha_def]; field_simp
      · right
        exact hx
    exact measure_mono_null hsub (measure_union_null hnull (ae_iff.mp (hcone a ha)))
  have hcover : E ⊆ ⋃ n : ℕ, E ∩ ball 0 ((n : ℝ) + 1) := by
    intro x hx
    obtain ⟨n, hn⟩ := exists_nat_gt ‖x‖
    exact mem_iUnion.mpr ⟨n, hx, by rw [mem_ball, dist_zero_right]; linarith⟩
  exact measure_mono_null hcover (measure_iUnion_null fun n ↦ hR _ (by positivity))

/-- The vertex of a minimizing cone lies in its measure-theoretic boundary. -/
theorem IsMinimizingCone.zero_mem_measureTheoreticBoundary {d : ℕ} {E : Set (Space d)}
    (hE : IsMinimizingCone E) : (0 : Space d) ∈ measureTheoreticBoundary E := by
  intro r hr
  refine ⟨fun h0 ↦ hE.nontrivial.1 (volume_eq_zero_of_ae_cone_of_ball hE.dilation hr h0),
    fun h0 ↦ ?_⟩
  have h0' : volume (Eᶜ ∩ ball 0 r) = 0 := by
    rw [inter_comm, ← sdiff_eq]
    exact h0
  exact hE.nontrivial.2 (volume_eq_zero_of_ae_cone_of_ball hE.compl.dilation hr h0')

/-- The measure-theoretic boundary of a minimizing cone is the frontier of its canonical open
representative. -/
theorem IsMinimizingCone.frontier_measureTheoreticInterior {m : ℕ} {E : Set (Space (m + 1))}
    (hE : IsMinimizingCone E) :
    frontier (measureTheoreticInterior E) = measureTheoreticBoundary E := by
  simpa using hE.minimizer.frontier_measureTheoreticInterior_inter_eq

/-- The measure-theoretic boundary of a minimizing cone is the support of any of its perimeter
measures. -/
theorem IsMinimizingCone.support_eq_measureTheoreticBoundary {m : ℕ}
    {E : Set (Space (m + 1))} (hE : IsMinimizingCone E)
    (b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))) (μ : Measure (Space (m + 1)))
    (hμ : ∀ U, IsOpen U → μ U = variationalPerimeter b E U) :
    μ.support = measureTheoreticBoundary E := by
  simpa using (hE.isLocalPerimeterMinimizer b).support_measure_inter_eq μ
    (fun U hU _ ↦ hμ U hU)

/-- A minimizing cone agrees a.e. with its canonical open representative. -/
theorem IsMinimizingCone.ae_eq_measureTheoreticInterior {m : ℕ} {E : Set (Space (m + 1))}
    (hE : IsMinimizingCone E) : E =ᵐ[volume] measureTheoreticInterior E := by
  filter_upwards [hE.minimizer.ae_mem_iff_measureTheoreticInterior] with x hx
  exact propext (hx (mem_univ x))

/-- The measure-theoretic boundary of a minimizing cone is exactly dilation invariant. -/
theorem IsMinimizingCone.smul_mem_measureTheoreticBoundary_iff {d : ℕ} {E : Set (Space d)}
    (hE : IsMinimizingCone E) {a : ℝ} (ha : 0 < a) (x : Space d) :
    a • x ∈ measureTheoreticBoundary E ↔ x ∈ measureTheoreticBoundary E :=
  mem_measureTheoreticBoundary_smul_iff_of_ae_cone hE.dilation ha x

/-! ### 2. Blow-up limits and tangent cones (BV11) -/

/-- `T` is the `L¹_loc` limit of the blow-ups `(E - x₀) / r j` along scales `r j → 0+`. -/
def IsBlowupLimit {d : ℕ} (E : Set (Space d)) (x₀ : Space d) (r : ℕ → ℝ)
    (T : Set (Space d)) : Prop :=
  (∀ j, 0 < r j) ∧ Tendsto r atTop (𝓝 0) ∧
    ∀ K : Set (Space d), IsCompact K →
      Tendsto (fun j ↦ ∫ y in K,
        ‖((fun z ↦ x₀ + r j • z) ⁻¹' E).indicator (fun _ ↦ (1 : ℝ)) y -
          T.indicator (fun _ ↦ (1 : ℝ)) y‖) atTop (𝓝 0)

/-- A tangent cone of `E` at `x₀`: a measurable `L¹_loc` limit of blow-ups of `E` at `x₀` along
some scale sequence tending to zero. -/
def IsTangentCone {d : ℕ} (E : Set (Space d)) (x₀ : Space d) (T : Set (Space d)) : Prop :=
  MeasurableSet T ∧ ∃ r : ℕ → ℝ, IsBlowupLimit E x₀ r T

theorem IsBlowupLimit.comp_strictMono {d : ℕ} {E T : Set (Space d)} {x₀ : Space d}
    {r : ℕ → ℝ} (h : IsBlowupLimit E x₀ r T) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    IsBlowupLimit E x₀ (r ∘ φ) T :=
  ⟨fun j ↦ h.1 (φ j), h.2.1.comp hφ.tendsto_atTop,
    fun K hK ↦ (h.2.2 K hK).comp hφ.tendsto_atTop⟩

theorem IsBlowupLimit.congr_ae {d : ℕ} {E T T' : Set (Space d)} {x₀ : Space d}
    {r : ℕ → ℝ} (h : IsBlowupLimit E x₀ r T) (hTT' : T =ᵐ[volume] T') :
    IsBlowupLimit E x₀ r T' := by
  refine ⟨h.1, h.2.1, fun K hK ↦ (h.2.2 K hK).congr fun j ↦ ?_⟩
  have hind : T.indicator (fun _ ↦ (1 : ℝ)) =ᵐ[volume] T'.indicator (fun _ ↦ (1 : ℝ)) :=
    indicator_ae_eq_of_ae_eq_set hTT'
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_of_ae hind] with y hy
  rw [hy]

/-- Volume form of blow-up convergence. -/
theorem IsBlowupLimit.tendsto_volume_symmDiff {d : ℕ} {E T : Set (Space d)} {x₀ : Space d}
    {r : ℕ → ℝ} (h : IsBlowupLimit E x₀ r T) (hE : MeasurableSet E) (hT : MeasurableSet T)
    {K : Set (Space d)} (hK : IsCompact K) :
    Tendsto (fun j ↦ volume (symmDiff ((fun z ↦ x₀ + r j • z) ⁻¹' E) T ∩ K)) atTop (𝓝 0) := by
  have hEj : ∀ j, MeasurableSet ((fun z ↦ x₀ + r j • z) ⁻¹' E) := fun j ↦
    hE.preimage (by fun_prop)
  have hreal : Tendsto (fun j ↦ volume.real (symmDiff ((fun z ↦ x₀ + r j • z) ⁻¹' E) T ∩ K))
      atTop (𝓝 0) :=
    (h.2.2 K hK).congr fun j ↦ setIntegral_norm_indicator_sub_eq_volume_symmDiff (hEj j) hT
  have h2 := ENNReal.tendsto_ofReal hreal
  rw [ENNReal.ofReal_zero] at h2
  refine h2.congr fun j ↦ ?_
  exact ofReal_measureReal (measure_ne_top_of_subset inter_subset_right hK.measure_lt_top.ne)

/-- Triangle inequality for symmetric differences localized to a set. -/
private theorem measure_symmDiff_inter_le {d : ℕ} (A B C K : Set (Space d)) :
    volume (symmDiff A C ∩ K) ≤ volume (symmDiff A B ∩ K) + volume (symmDiff B C ∩ K) := by
  refine (measure_mono ?_).trans (measure_union_le _ _)
  intro x ⟨hx, hxK⟩
  rw [mem_symmDiff] at hx
  by_cases h1 : x ∈ symmDiff A B
  · exact Or.inl ⟨h1, hxK⟩
  · right
    refine ⟨?_, hxK⟩
    rw [mem_symmDiff] at h1 ⊢
    tauto

/-- Blow-up limits are unique up to null sets. -/
theorem IsBlowupLimit.ae_eq {d : ℕ} {E T₁ T₂ : Set (Space d)} {x₀ : Space d} {r : ℕ → ℝ}
    (h₁ : IsBlowupLimit E x₀ r T₁) (h₂ : IsBlowupLimit E x₀ r T₂) (hE : MeasurableSet E)
    (hT₁ : MeasurableSet T₁) (hT₂ : MeasurableSet T₂) : T₁ =ᵐ[volume] T₂ := by
  have hK : ∀ n : ℕ, volume (symmDiff T₁ T₂ ∩ closedBall 0 (n : ℝ)) = 0 := by
    intro n
    have hc := isCompact_closedBall (0 : Space d) (n : ℝ)
    have t1 := h₁.tendsto_volume_symmDiff hE hT₁ hc
    have t2 := h₂.tendsto_volume_symmDiff hE hT₂ hc
    have hsum := t1.add t2
    rw [add_zero] at hsum
    refine nonpos_iff_eq_zero.mp (ge_of_tendsto hsum (Eventually.of_forall fun j ↦ ?_))
    calc volume (symmDiff T₁ T₂ ∩ closedBall 0 (n : ℝ))
        ≤ volume (symmDiff T₁ ((fun z ↦ x₀ + r j • z) ⁻¹' E) ∩ closedBall 0 (n : ℝ)) +
          volume (symmDiff ((fun z ↦ x₀ + r j • z) ⁻¹' E) T₂ ∩ closedBall 0 (n : ℝ)) :=
          measure_symmDiff_inter_le _ _ _ _
      _ = _ := by rw [symmDiff_comm T₁]
  have hcover : symmDiff T₁ T₂ ⊆ ⋃ n : ℕ, symmDiff T₁ T₂ ∩ closedBall 0 (n : ℝ) := by
    intro x hx
    obtain ⟨n, hn⟩ := exists_nat_ge ‖x‖
    exact mem_iUnion.mpr ⟨n, hx, by rw [mem_closedBall, dist_zero_right]; exact hn⟩
  exact measure_symmDiff_eq_zero_iff.mp
    (measure_mono_null hcover (measure_iUnion_null hK))

/-- **Tangent cones of minimizers are minimizing cones (BV11).** Every measurable `L¹_loc`
blow-up limit of a local perimeter minimizer at a measure-theoretic boundary point is a minimizing
cone containing the origin in its boundary, with constant density ratio equal to the density of
`E` at `x₀`. -/
theorem IsLocalPerimeterMinimizer.isMinimizingCone_of_isBlowupLimit {m : ℕ}
    {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))} {E Ω : Set (Space (m + 1))}
    (hmin : IsLocalPerimeterMinimizer b E Ω) {x₀ : Space (m + 1)}
    (hx₀ : x₀ ∈ measureTheoreticBoundary E ∩ Ω) {r : ℕ → ℝ} {T : Set (Space (m + 1))}
    (hT : MeasurableSet T) (hlim : IsBlowupLimit E x₀ r T) :
    IsMinimizingCone T ∧ (0 : Space (m + 1)) ∈ measureTheoreticBoundary T ∧
      ∀ R : ℝ, 0 < R →
        (variationalPerimeter b T (ball 0 R)).toReal = perimeterDensity b E x₀ * R ^ m := by
  obtain ⟨φ, C, hφ, hCm, hCmin, h0C, hvC, hvCc, hconv, hP, hdil⟩ :=
    hmin.exists_tangent_cone hx₀ hlim.1 hlim.2.1
  have hC : IsMinimizingCone C := IsMinimizingCone.of_isLocalPerimeterMinimizer hCmin
    ⟨hvC, hvCc⟩ hdil
  have hlimC : IsBlowupLimit E x₀ (r ∘ φ) C :=
    ⟨fun j ↦ hlim.1 (φ j), hlim.2.1.comp hφ.tendsto_atTop, hconv⟩
  have hCT : C =ᵐ[volume] T :=
    hlimC.ae_eq (hlim.comp_strictMono hφ) hmin.measurableSet hCm hT
  refine ⟨hC.congr_ae hT hCT, ?_, fun R hR ↦ ?_⟩
  · rw [← measureTheoreticBoundary_congr_ae hCT]
    exact h0C
  · rw [← hP R hR]
    congr 1
    apply variationalPerimeter_congr_ae_on b
    filter_upwards [hCT] with x hx _
    exact (Iff.of_eq hx).symm

/-- **Existence of tangent cones (BV11).** At a measure-theoretic boundary point of a local
perimeter minimizer, every scale sequence `r j → 0+` has a subsequence along which the blow-ups
converge in `L¹_loc` to a minimizing cone with `0` in its boundary and constant density ratio. -/
theorem IsLocalPerimeterMinimizer.exists_isBlowupLimit {m : ℕ}
    {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))} {E Ω : Set (Space (m + 1))}
    (hmin : IsLocalPerimeterMinimizer b E Ω) {x₀ : Space (m + 1)}
    (hx₀ : x₀ ∈ measureTheoreticBoundary E ∩ Ω) {r : ℕ → ℝ} (hr_pos : ∀ j, 0 < r j)
    (hr : Tendsto r atTop (𝓝 0)) :
    ∃ (φ : ℕ → ℕ) (T : Set (Space (m + 1))), StrictMono φ ∧ IsMinimizingCone T ∧
      IsBlowupLimit E x₀ (r ∘ φ) T ∧ (0 : Space (m + 1)) ∈ measureTheoreticBoundary T ∧
      ∀ R : ℝ, 0 < R →
        (variationalPerimeter b T (ball 0 R)).toReal = perimeterDensity b E x₀ * R ^ m := by
  obtain ⟨φ, C, hφ, hCm, hCmin, h0C, hvC, hvCc, hconv, hP, hdil⟩ :=
    hmin.exists_tangent_cone hx₀ hr_pos hr
  exact ⟨φ, C, hφ, IsMinimizingCone.of_isLocalPerimeterMinimizer hCmin ⟨hvC, hvCc⟩ hdil,
    ⟨fun j ↦ hr_pos (φ j), hr.comp hφ.tendsto_atTop, hconv⟩, h0C, hP⟩

/-! ### 3. GR5: tangent cones of cones split off the direction of the base point -/

/-- **GR5 (cone splitting).** Let `E` and `T` be a.e. dilation invariant about the origin and let
`T` be the `L¹_loc` limit of the blow-ups of `E` at `x₀`. Then `T` is a.e. invariant under every
translation along `x₀`.

For `a = 1 + r t` and `c = a⁻¹`, dilation invariance of `E` gives the exact a.e. identity
`y + t x₀ ∈ (E - x₀) / r ↔ c y ∈ (E - x₀) / r`; dilation invariance of `T` gives
`c y ∈ T ↔ y ∈ T`; and the two `L¹_loc` errors are controlled by a translation and a dilation of
the blow-up error on fixed balls. -/
theorem ae_mem_add_smul_iff_of_isBlowupLimit {d : ℕ} {E T : Set (Space d)}
    (hE : MeasurableSet E) (hT : MeasurableSet T)
    (hEcone : ∀ a : ℝ, 0 < a → ∀ᵐ x ∂volume, x ∈ E ↔ a • x ∈ E)
    (hTcone : ∀ a : ℝ, 0 < a → ∀ᵐ y ∂volume, y ∈ T ↔ a • y ∈ T)
    {x₀ : Space d} {r : ℕ → ℝ} (hlim : IsBlowupLimit E x₀ r T) (t : ℝ) :
    ∀ᵐ y ∂volume, y ∈ T ↔ y + t • x₀ ∈ T := by
  set Ej : ℕ → Set (Space d) := fun j ↦ (fun z ↦ x₀ + r j • z) ⁻¹' E with hEjdef
  set S : Set (Space d) := {y | ¬(y ∈ T ↔ y + t • x₀ ∈ T)} with hSdef
  have hrt : Tendsto (fun j ↦ r j * t) atTop (𝓝 0) := by
    simpa using hlim.2.1.mul_const t
  have hev : ∀ᶠ j in atTop, |r j * t| < 1 / 2 := by
    filter_upwards [Metric.tendsto_nhds.mp hrt (1 / 2) (by norm_num)] with j hj
    simpa [Real.dist_eq] using hj
  have hbound : ∀ j, |r j * t| < 1 / 2 → ∀ ρ : ℝ, 0 < ρ →
      volume (S ∩ closedBall 0 ρ) ≤ volume (symmDiff (Ej j) T ∩ closedBall (t • x₀) ρ) +
        ENNReal.ofReal (2 ^ d) * volume (symmDiff (Ej j) T ∩ closedBall 0 (2 * ρ)) := by
    intro j hj ρ hρ
    have hj' := abs_lt.mp hj
    set a : ℝ := 1 + r j * t with ha_def
    have ha : 0 < a := by linarith
    set c : ℝ := a⁻¹ with hc_def
    have hc : 0 < c := inv_pos.mpr ha
    have hac : a * c = 1 := mul_inv_cancel₀ ha.ne'
    have hc2 : c ≤ 2 := by
      rw [hc_def, inv_le_comm₀ ha (by norm_num : (0 : ℝ) < 2)]
      linarith
    have hcinv : c⁻¹ ≤ 2 := by
      rw [hc_def, inv_inv]
      linarith
    have hN₁ : ∀ᵐ y ∂volume, y + t • x₀ ∈ Ej j ↔ c • y ∈ Ej j := by
      have hrc : r j * c ≠ 0 := mul_ne_zero (hlim.1 j).ne' hc.ne'
      have h1 := ae_comp_add_smul (hEcone a ha) x₀ hrc
      filter_upwards [h1] with y hy
      have e1 : x₀ + r j • (c • y) = x₀ + (r j * c) • y := by rw [smul_smul]
      have e2 : x₀ + r j • (y + t • x₀) = a • (x₀ + (r j * c) • y) := by
        rw [smul_add, smul_smul, smul_add, smul_smul, ha_def]
        have h3 : (1 + r j * t) * (r j * c) = r j := by
          have : (1 + r j * t) * c = 1 := hac
          calc (1 + r j * t) * (r j * c) = r j * ((1 + r j * t) * c) := by ring
            _ = r j := by rw [this, mul_one]
        rw [h3, add_smul, one_smul]
        abel
      simp only [hEjdef, mem_preimage]
      rw [e1, e2]
      exact hy.symm
    have hN₂ : ∀ᵐ y ∂volume, c • y ∈ T ↔ y ∈ T := by
      filter_upwards [hTcone c hc] with y hy
      exact hy.symm
    set N : Set (Space d) := {y | ¬((y + t • x₀ ∈ Ej j ↔ c • y ∈ Ej j) ∧ (c • y ∈ T ↔ y ∈ T))}
      with hNdef
    have hN0 : volume N = 0 := ae_iff.mp (hN₁.and hN₂)
    have hsub : S ∩ closedBall 0 ρ ⊆ N ∪
        ((fun y ↦ y + t • x₀) ⁻¹' (symmDiff (Ej j) T ∩ closedBall (t • x₀) ρ)) ∪
        ((fun y ↦ c • y) ⁻¹' (symmDiff (Ej j) T ∩ closedBall 0 (2 * ρ))) := by
      rintro y ⟨hyS, hyB⟩
      have hyS' : ¬(y ∈ T ↔ y + t • x₀ ∈ T) := hyS
      have hy1 : y + t • x₀ ∈ closedBall (t • x₀) ρ := by
        rw [mem_closedBall, dist_eq_norm, add_sub_cancel_right]
        simpa [mem_closedBall, dist_zero_right] using hyB
      have hy2 : c • y ∈ closedBall (0 : Space d) (2 * ρ) := by
        rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg hc.le]
        have hyn : ‖y‖ ≤ ρ := by simpa [mem_closedBall, dist_zero_right] using hyB
        nlinarith [norm_nonneg y]
      by_cases hgood : (y + t • x₀ ∈ Ej j ↔ c • y ∈ Ej j) ∧ (c • y ∈ T ↔ y ∈ T)
      · by_cases h1 : y + t • x₀ ∈ symmDiff (Ej j) T
        · exact Or.inl (Or.inr ⟨h1, hy1⟩)
        · by_cases h2 : c • y ∈ symmDiff (Ej j) T
          · exact Or.inr ⟨h2, hy2⟩
          · exfalso
            rw [mem_symmDiff] at h1 h2
            apply hyS'
            tauto
      · exact Or.inl (Or.inl hgood)
    have hpre1 : volume ((fun y ↦ y + t • x₀) ⁻¹' (symmDiff (Ej j) T ∩ closedBall (t • x₀) ρ)) =
        volume (symmDiff (Ej j) T ∩ closedBall (t • x₀) ρ) :=
      measure_preimage_add_right volume (t • x₀) _
    have hpre2 : volume ((fun y ↦ c • y) ⁻¹' (symmDiff (Ej j) T ∩ closedBall 0 (2 * ρ))) ≤
        ENNReal.ofReal (2 ^ d) * volume (symmDiff (Ej j) T ∩ closedBall 0 (2 * ρ)) := by
      rw [Measure.addHaar_preimage_smul volume hc.ne']
      gcongr
      rw [finrank_euclideanSpace_fin, abs_of_pos (inv_pos.mpr (pow_pos hc d)), ← inv_pow]
      exact pow_le_pow_left₀ (inv_nonneg.mpr hc.le) hcinv d
    calc volume (S ∩ closedBall 0 ρ)
        ≤ volume (N ∪
            ((fun y ↦ y + t • x₀) ⁻¹' (symmDiff (Ej j) T ∩ closedBall (t • x₀) ρ)) ∪
            ((fun y ↦ c • y) ⁻¹' (symmDiff (Ej j) T ∩ closedBall 0 (2 * ρ)))) :=
          measure_mono hsub
      _ ≤ volume N +
            volume ((fun y ↦ y + t • x₀) ⁻¹' (symmDiff (Ej j) T ∩ closedBall (t • x₀) ρ)) +
            volume ((fun y ↦ c • y) ⁻¹' (symmDiff (Ej j) T ∩ closedBall 0 (2 * ρ))) :=
          (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
      _ ≤ _ := by
          rw [hN0, zero_add, hpre1]
          exact add_le_add le_rfl hpre2
  have hball : ∀ ρ : ℝ, 0 < ρ → volume (S ∩ closedBall 0 ρ) = 0 := by
    intro ρ hρ
    have h1 := hlim.tendsto_volume_symmDiff hE hT (isCompact_closedBall (t • x₀) ρ)
    have h2 := hlim.tendsto_volume_symmDiff hE hT (isCompact_closedBall (0 : Space d) (2 * ρ))
    have hlimit : Tendsto (fun j ↦ volume (symmDiff (Ej j) T ∩ closedBall (t • x₀) ρ) +
        ENNReal.ofReal (2 ^ d) * volume (symmDiff (Ej j) T ∩ closedBall 0 (2 * ρ)))
        atTop (𝓝 0) := by
      have := h1.add (ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (2 ^ d)) h2
        (Or.inr ENNReal.ofReal_ne_top))
      simpa using this
    exact nonpos_iff_eq_zero.mp (ge_of_tendsto hlimit (hev.mono fun j hj ↦ hbound j hj ρ hρ))
  rw [ae_iff]
  have hcover : {y | ¬(y ∈ T ↔ y + t • x₀ ∈ T)} ⊆ ⋃ n : ℕ, S ∩ closedBall 0 ((n : ℝ) + 1) := by
    intro y hy
    obtain ⟨n, hn⟩ := exists_nat_gt ‖y‖
    exact mem_iUnion.mpr ⟨n, hy, by rw [mem_closedBall, dist_zero_right]; linarith⟩
  exact measure_mono_null hcover (measure_iUnion_null fun n ↦ hball _ (by positivity))

/-- Translation invariances of `E` pass to all of its blow-up limits (used to accumulate
translation directions when GR5 is iterated). -/
theorem ae_mem_add_smul_iff_of_isBlowupLimit_of_invariant {d : ℕ} {E T : Set (Space d)}
    (hE : MeasurableSet E) (hT : MeasurableSet T) {x₀ : Space d} {r : ℕ → ℝ}
    (hlim : IsBlowupLimit E x₀ r T) {v : Space d}
    (hinv : ∀ s : ℝ, ∀ᵐ x ∂volume, x ∈ E ↔ x + s • v ∈ E) (t : ℝ) :
    ∀ᵐ y ∂volume, y ∈ T ↔ y + t • v ∈ T := by
  set Ej : ℕ → Set (Space d) := fun j ↦ (fun z ↦ x₀ + r j • z) ⁻¹' E with hEjdef
  set S : Set (Space d) := {y | ¬(y ∈ T ↔ y + t • v ∈ T)} with hSdef
  have hbound : ∀ j, ∀ ρ : ℝ, 0 < ρ →
      volume (S ∩ closedBall 0 ρ) ≤ volume (symmDiff (Ej j) T ∩ closedBall 0 ρ) +
        volume (symmDiff (Ej j) T ∩ closedBall (t • v) ρ) := by
    intro j ρ hρ
    have hN : ∀ᵐ y ∂volume, y ∈ Ej j ↔ y + t • v ∈ Ej j := by
      have h1 := ae_comp_add_smul (hinv (r j * t)) x₀ (hlim.1 j).ne'
      filter_upwards [h1] with y hy
      have e : x₀ + r j • (y + t • v) = x₀ + r j • y + (r j * t) • v := by
        rw [smul_add, smul_smul, add_assoc]
      simp only [hEjdef, mem_preimage]
      rw [e]
      exact hy
    set N : Set (Space d) := {y | ¬(y ∈ Ej j ↔ y + t • v ∈ Ej j)} with hNdef
    have hN0 : volume N = 0 := ae_iff.mp hN
    have hsub : S ∩ closedBall 0 ρ ⊆ N ∪ (symmDiff (Ej j) T ∩ closedBall 0 ρ) ∪
        ((fun y ↦ y + t • v) ⁻¹' (symmDiff (Ej j) T ∩ closedBall (t • v) ρ)) := by
      rintro y ⟨hyS, hyB⟩
      have hyS' : ¬(y ∈ T ↔ y + t • v ∈ T) := hyS
      have hy1 : y + t • v ∈ closedBall (t • v) ρ := by
        rw [mem_closedBall, dist_eq_norm, add_sub_cancel_right]
        simpa [mem_closedBall, dist_zero_right] using hyB
      by_cases hgood : y ∈ Ej j ↔ y + t • v ∈ Ej j
      · by_cases h1 : y ∈ symmDiff (Ej j) T
        · exact Or.inl (Or.inr ⟨h1, hyB⟩)
        · by_cases h2 : y + t • v ∈ symmDiff (Ej j) T
          · exact Or.inr ⟨h2, hy1⟩
          · exfalso
            rw [mem_symmDiff] at h1 h2
            apply hyS'
            tauto
      · exact Or.inl (Or.inl hgood)
    calc volume (S ∩ closedBall 0 ρ)
        ≤ volume (N ∪ (symmDiff (Ej j) T ∩ closedBall 0 ρ) ∪
            ((fun y ↦ y + t • v) ⁻¹' (symmDiff (Ej j) T ∩ closedBall (t • v) ρ))) :=
          measure_mono hsub
      _ ≤ volume N + volume (symmDiff (Ej j) T ∩ closedBall 0 ρ) +
            volume ((fun y ↦ y + t • v) ⁻¹' (symmDiff (Ej j) T ∩ closedBall (t • v) ρ)) :=
          (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
      _ = _ := by rw [hN0, zero_add, measure_preimage_add_right]
  have hball : ∀ ρ : ℝ, 0 < ρ → volume (S ∩ closedBall 0 ρ) = 0 := by
    intro ρ hρ
    have h1 := hlim.tendsto_volume_symmDiff hE hT (isCompact_closedBall (0 : Space d) ρ)
    have h2 := hlim.tendsto_volume_symmDiff hE hT (isCompact_closedBall (t • v) ρ)
    have hlimit := h1.add h2
    rw [add_zero] at hlimit
    exact nonpos_iff_eq_zero.mp
      (ge_of_tendsto hlimit (Eventually.of_forall fun j ↦ hbound j ρ hρ))
  rw [ae_iff]
  have hcover : {y | ¬(y ∈ T ↔ y + t • v ∈ T)} ⊆ ⋃ n : ℕ, S ∩ closedBall 0 ((n : ℝ) + 1) := by
    intro y hy
    obtain ⟨n, hn⟩ := exists_nat_gt ‖y‖
    exact mem_iUnion.mpr ⟨n, hy, by rw [mem_closedBall, dist_zero_right]; linarith⟩
  exact measure_mono_null hcover (measure_iUnion_null fun n ↦ hball _ (by positivity))

/-- Tangent cones of local perimeter minimizers at measure-theoretic boundary points are
minimizing cones. -/
theorem IsTangentCone.isMinimizingCone {m : ℕ}
    {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))} {E Ω : Set (Space (m + 1))}
    {x₀ : Space (m + 1)} {T : Set (Space (m + 1))} (hT : IsTangentCone E x₀ T)
    (hmin : IsLocalPerimeterMinimizer b E Ω) (hx₀ : x₀ ∈ measureTheoreticBoundary E ∩ Ω) :
    IsMinimizingCone T := by
  obtain ⟨hTm, r, hlim⟩ := hT
  exact (hmin.isMinimizingCone_of_isBlowupLimit hx₀ hTm hlim).1

/-- **GR5 for minimizing cones.** Every tangent cone of a minimizing cone `E` at a boundary point
`x₀` is a minimizing cone which is a.e. invariant under all translations along `x₀`. -/
theorem IsTangentCone.ae_mem_add_smul_iff {m : ℕ} {E : Set (Space (m + 1))}
    {x₀ : Space (m + 1)} {T : Set (Space (m + 1))} (hT : IsTangentCone E x₀ T)
    (hE : IsMinimizingCone E) (hx₀ : x₀ ∈ measureTheoreticBoundary E) (t : ℝ) :
    ∀ᵐ y ∂volume, y ∈ T ↔ y + t • x₀ ∈ T := by
  have hTc := hT.isMinimizingCone hE.minimizer ⟨hx₀, mem_univ x₀⟩
  obtain ⟨hTm, r, hlim⟩ := hT
  exact ae_mem_add_smul_iff_of_isBlowupLimit hE.measurableSet hTm hE.dilation hTc.dilation hlim t

/-- **Existence of split tangent cones (BV11 + GR5).** At every boundary point `x₀` of a
minimizing cone and along every scale sequence `r j → 0+`, a subsequence of blow-ups converges in
`L¹_loc` to a minimizing cone `T` with `0 ∈ ∂T`, ball perimeters `θ R ^ m` with `θ` the density
of `E` at `x₀`, and which is a.e. invariant under all translations along `x₀`. -/
theorem IsMinimizingCone.exists_isBlowupLimit {m : ℕ} {E : Set (Space (m + 1))}
    (hE : IsMinimizingCone E) {x₀ : Space (m + 1)} (hx₀ : x₀ ∈ measureTheoreticBoundary E)
    {r : ℕ → ℝ} (hr_pos : ∀ j, 0 < r j) (hr : Tendsto r atTop (𝓝 0)) :
    ∃ (φ : ℕ → ℕ) (T : Set (Space (m + 1))), StrictMono φ ∧ IsMinimizingCone T ∧
      IsBlowupLimit E x₀ (r ∘ φ) T ∧ (0 : Space (m + 1)) ∈ measureTheoreticBoundary T ∧
      (∀ R : ℝ, 0 < R →
        (variationalPerimeter (EuclideanSpace.basisFun (Fin (m + 1)) ℝ) T (ball 0 R)).toReal =
          perimeterDensity (EuclideanSpace.basisFun (Fin (m + 1)) ℝ) E x₀ * R ^ m) ∧
      ∀ t : ℝ, ∀ᵐ y ∂volume, y ∈ T ↔ y + t • x₀ ∈ T := by
  obtain ⟨φ, C, hφ, hC, hlimC, h0C, hP⟩ :=
    hE.minimizer.exists_isBlowupLimit ⟨hx₀, mem_univ x₀⟩ hr_pos hr
  exact ⟨φ, C, hφ, hC, hlimC, h0C, hP, fun t ↦ ae_mem_add_smul_iff_of_isBlowupLimit
    hE.measurableSet hC.measurableSet hE.dilation hC.dilation hlimC t⟩

/-- Every boundary point of a minimizing cone carries a tangent cone, which is a minimizing cone
invariant along the base point. -/
theorem IsMinimizingCone.exists_isTangentCone {m : ℕ} {E : Set (Space (m + 1))}
    (hE : IsMinimizingCone E) {x₀ : Space (m + 1)} (hx₀ : x₀ ∈ measureTheoreticBoundary E) :
    ∃ T : Set (Space (m + 1)), IsTangentCone E x₀ T ∧ IsMinimizingCone T ∧
      ∀ t : ℝ, ∀ᵐ y ∂volume, y ∈ T ↔ y + t • x₀ ∈ T := by
  obtain ⟨φ, T, -, hT, hlim, -, -, hinv⟩ := hE.exists_isBlowupLimit hx₀
    (r := fun j ↦ 1 / ((j : ℝ) + 1)) (fun j ↦ by positivity)
    tendsto_one_div_add_atTop_nhds_zero_nat
  exact ⟨T, ⟨hT.measurableSet, _, hlim⟩, hT, hinv⟩

/-! ### 4. GR6: cylindrical splitting of translation invariant minimizing cones -/

private theorem point_smul_zero_eq {k : ℕ} (a : ℝ) (y : Space k) :
    point (a • y) 0 = a • point y 0 := by
  have h := (horizontalEmbedding k).map_smul a y
  rwa [horizontalEmbedding_apply, horizontalEmbedding_apply] at h

/-- **GR6 (vertical form).** A minimizing cone in `Space (k + 1)` which is a.e. invariant under
all vertical translations is a.e. the cylinder over an open minimizing cone in `Space k`.

The canonical open representative is exactly vertically invariant, hence a cylinder over its
slice at height zero; the slice inherits nontriviality and exact dilation invariance, and its
minimality is `IsLocalPerimeterMinimizer.of_preimage_horizontal`. -/
theorem IsMinimizingCone.exists_cylinder_of_vertical_invariant {k : ℕ}
    {T : Set (Space (k + 1))} (hT : IsMinimizingCone T)
    (hinv : ∀ t : ℝ, ∀ᵐ x ∂volume, x ∈ T ↔ x + t • verticalDirection k ∈ T) :
    ∃ T' : Set (Space k), IsOpen T' ∧ IsMinimizingCone T' ∧
      T =ᵐ[volume] (horizontal ⁻¹' T' : Set (Space (k + 1))) := by
  have hIinv : ∀ (x : Space (k + 1)) (t : ℝ),
      x + t • verticalDirection k ∈ measureTheoreticInterior T ↔
        x ∈ measureTheoreticInterior T := by
    intro x t
    have hae : T =ᵐ[volume] (fun z ↦ t • verticalDirection k + (1 : ℝ) • z) ⁻¹' T := by
      filter_upwards [hinv t] with z hz
      show (z ∈ T) = (z ∈ (fun z ↦ t • verticalDirection k + (1 : ℝ) • z) ⁻¹' T)
      rw [mem_preimage, one_smul, add_comm (t • verticalDirection k) z]
      exact propext hz
    have heq := (measureTheoreticInterior_congr_ae hae).trans
      (measureTheoreticInterior_preimage_add_smul T (t • verticalDirection k) one_pos)
    have hmem := Set.ext_iff.mp heq x
    rw [mem_preimage, one_smul] at hmem
    rw [add_comm x (t • verticalDirection k)]
    exact hmem.symm
  set T' : Set (Space k) := {y | point y 0 ∈ measureTheoreticInterior T} with hT'def
  have hT'open : IsOpen T' :=
    (isOpen_measureTheoreticInterior T).preimage (horizontalEmbedding k).continuous
  have hT'meas : MeasurableSet T' := hT'open.measurableSet
  have hcyl : (horizontal ⁻¹' T' : Set (Space (k + 1))) = measureTheoreticInterior T := by
    ext x
    show point (horizontal x) 0 ∈ measureTheoreticInterior T ↔ x ∈ measureTheoreticInterior T
    have h := hIinv (point (horizontal x) 0) (x (Fin.last k))
    rw [point_add_vertical, zero_add, point_horizontal_last] at h
    exact h.symm
  have hTcyl : T =ᵐ[volume] (horizontal ⁻¹' T' : Set (Space (k + 1))) := by
    rw [hcyl]
    exact hT.ae_eq_measureTheoreticInterior
  have hD : IsMinimizingCone (horizontal ⁻¹' T' : Set (Space (k + 1))) :=
    hT.congr_ae (hT'meas.preimage continuous_horizontal.measurable) hTcyl
  refine ⟨T', hT'open, ⟨hT'meas, ⟨fun h0 ↦ ?_, fun h0 ↦ ?_⟩, fun a ha ↦ ?_, ?_⟩, hTcyl⟩
  · exact hD.nontrivial.1 ((volume_preimage_horizontal_eq_zero_iff hT'meas).mpr h0)
  · apply hD.nontrivial.2
    rw [← preimage_compl]
    exact (volume_preimage_horizontal_eq_zero_iff hT'meas.compl).mpr h0
  · refine Eventually.of_forall fun y ↦ ?_
    show point y 0 ∈ measureTheoreticInterior T ↔ point (a • y) 0 ∈ measureTheoreticInterior T
    rw [point_smul_zero_eq]
    exact (mem_measureTheoreticInterior_smul_iff_of_ae_cone hT.dilation ha _).symm
  · exact hD.minimizer.of_preimage_horizontal _ hT'meas

/-- A linear isometry of `Space (k + 1)` taking the vertical direction to a given unit vector. -/
theorem exists_linearIsometryEquiv_verticalDirection {k : ℕ} {v : Space (k + 1)}
    (hv : ‖v‖ = 1) :
    ∃ Q : Space (k + 1) ≃ₗᵢ[ℝ] Space (k + 1), Q (verticalDirection k) = v := by
  refine ⟨(ℝ ∙ (verticalDirection k - v))ᗮ.reflection, Submodule.reflection_sub ?_⟩
  rw [hv]
  simp [verticalDirection]

/-- **GR6 (general direction).** A minimizing cone in `Space (k + 1)` which is a.e. invariant
under all translations along a unit vector `v` is, after a linear isometry `Q` sending the
vertical direction to `v`, a.e. the cylinder over an open minimizing cone in `Space k`. -/
theorem IsMinimizingCone.exists_cylinder_of_invariant {k : ℕ} {T : Set (Space (k + 1))}
    (hT : IsMinimizingCone T) {v : Space (k + 1)} (hv : ‖v‖ = 1)
    (hinv : ∀ t : ℝ, ∀ᵐ x ∂volume, x ∈ T ↔ x + t • v ∈ T) :
    ∃ (Q : Space (k + 1) ≃ₗᵢ[ℝ] Space (k + 1)) (T' : Set (Space k)),
      Q (verticalDirection k) = v ∧ IsOpen T' ∧ IsMinimizingCone T' ∧
      T =ᵐ[volume] {x | horizontal (Q.symm x) ∈ T'} := by
  obtain ⟨Q, hQ⟩ := exists_linearIsometryEquiv_verticalDirection hv
  have hT₁ := hT.preimage_linearIsometryEquiv Q
  have hinv₁ : ∀ t : ℝ, ∀ᵐ x ∂volume,
      x ∈ Q ⁻¹' T ↔ x + t • verticalDirection k ∈ Q ⁻¹' T := by
    intro t
    have h := Q.measurePreserving.quasiMeasurePreserving.ae (hinv t)
    filter_upwards [h] with x hx
    simp only [mem_preimage, map_add, map_smul, hQ]
    exact hx
  obtain ⟨T', hT'o, hT'c, hae⟩ := hT₁.exists_cylinder_of_vertical_invariant hinv₁
  refine ⟨Q, T', hQ, hT'o, hT'c, ?_⟩
  have h2 := Q.symm.measurePreserving.quasiMeasurePreserving.preimage_ae_eq hae
  have h3 : Q.symm ⁻¹' (Q ⁻¹' T) = T := by
    ext x
    simp
  rw [h3] at h2
  exact h2

/-! ### 5. Cylinders over half-spaces -/

/-- The cylinder over a horizontal half-space is a half-space. -/
theorem preimage_horizontal_positiveHalfspace {k : ℕ} (e : Space k) :
    (horizontal ⁻¹' positiveHalfspace e : Set (Space (k + 1))) =
      positiveHalfspace (point e 0) := by
  ext x
  show 0 < inner ℝ e (horizontal x) ↔ 0 < inner ℝ (point e 0) x
  rw [← real_inner_comm (point e 0) x, inner_point_zero_right, real_inner_comm (horizontal x) e]

/-- If the cross-section is a.e. a half-space, then so is the cylinder; the normal is
`point e 0`, of the same length as `e`. -/
theorem preimage_horizontal_ae_eq_positiveHalfspace {k : ℕ} {T' : Set (Space k)} {e : Space k}
    (h : T' =ᵐ[volume] positiveHalfspace e) :
    (horizontal ⁻¹' T' : Set (Space (k + 1))) =ᵐ[volume] positiveHalfspace (point e 0) := by
  rw [← preimage_horizontal_positiveHalfspace]
  exact preimage_horizontal_ae_eq h

theorem preimage_linearIsometryEquiv_symm_positiveHalfspace {d : ℕ}
    (Q : Space d ≃ₗᵢ[ℝ] Space d) (e : Space d) :
    Q.symm ⁻¹' positiveHalfspace e = positiveHalfspace (Q e) := by
  ext x
  show 0 < inner ℝ e (Q.symm x) ↔ 0 < inner ℝ (Q e) x
  rw [← Q.inner_map_map e (Q.symm x), Q.apply_symm_apply]

/-- A rotated cylinder over an a.e. half-space is a.e. a half-space. -/
theorem ae_eq_positiveHalfspace_of_ae_eq_cylinder {k : ℕ} {T : Set (Space (k + 1))}
    (Q : Space (k + 1) ≃ₗᵢ[ℝ] Space (k + 1)) {T' : Set (Space k)} {e : Space k}
    (hT : T =ᵐ[volume] {x | horizontal (Q.symm x) ∈ T'})
    (hT' : T' =ᵐ[volume] positiveHalfspace e) :
    T =ᵐ[volume] positiveHalfspace (Q (point e 0)) := by
  have h1 := Q.symm.measurePreserving.quasiMeasurePreserving.preimage_ae_eq
    (preimage_horizontal_ae_eq_positiveHalfspace (k := k) hT')
  rw [preimage_linearIsometryEquiv_symm_positiveHalfspace] at h1
  exact hT.trans h1

/-! ### 6. Minimizing cones on the line -/

/-- Lebesgue density ratios of an a.e. dilation invariant set are invariant under the dilations of
center and radius. -/
theorem measure_inter_closedBall_div_smul_eq {d : ℕ} {E : Set (Space d)}
    (hcone : ∀ a : ℝ, 0 < a → ∀ᵐ x ∂volume, x ∈ E ↔ a • x ∈ E) {a : ℝ} (ha : 0 < a)
    (x : Space d) (r : ℝ) :
    volume (E ∩ closedBall (a • x) (a * r)) / volume (closedBall (a • x) (a * r)) =
      volume (E ∩ closedBall x r) / volume (closedBall x r) := by
  set c : ℝ≥0∞ := ENNReal.ofReal |(a ^ Module.finrank ℝ (Space d))⁻¹| with hc_def
  have hc0 : c ≠ 0 := by
    rw [hc_def]
    exact (ENNReal.ofReal_pos.mpr (abs_pos.mpr (inv_ne_zero (pow_ne_zero _ ha.ne')))).ne'
  have hctop : c ≠ ⊤ := ENNReal.ofReal_ne_top
  have hball : (fun y : Space d ↦ a • y) ⁻¹' closedBall (a • x) (a * r) = closedBall x r := by
    ext y
    simp only [mem_preimage, mem_closedBall, dist_eq_norm, ← smul_sub, norm_smul,
      Real.norm_of_nonneg ha.le]
    exact mul_le_mul_iff_right₀ ha
  have hE' : (fun y : Space d ↦ a • y) ⁻¹' E =ᵐ[volume] E := by
    filter_upwards [hcone a ha] with y hy
    exact propext hy.symm
  have h1 : c * volume (E ∩ closedBall (a • x) (a * r)) = volume (E ∩ closedBall x r) := by
    rw [hc_def, ← Measure.addHaar_preimage_smul volume ha.ne', preimage_inter, hball]
    exact measure_congr (hE'.inter (ae_eq_refl _))
  have h2 : c * volume (closedBall (a • x) (a * r)) = volume (closedBall x r) := by
    rw [hc_def, ← Measure.addHaar_preimage_smul volume ha.ne', hball]
  rw [← h1, ← h2, ENNReal.mul_div_mul_left _ _ hc0 hctop]

/-- **Base case, general form.** A measurable, nontrivial, a.e. dilation invariant subset of the
line is a.e. one of the two open half-lines. The proof compares Lebesgue density ratios along
dilations. -/
theorem ae_eq_positiveHalfspace_of_ae_cone_one {E : Set (Space 1)} (hE : MeasurableSet E)
    (hnt : volume E ≠ 0 ∧ volume Eᶜ ≠ 0)
    (hcone : ∀ a : ℝ, 0 < a → ∀ᵐ x ∂volume, x ∈ E ↔ a • x ∈ E) :
    ∃ e : Space 1, ‖e‖ = 1 ∧ E =ᵐ[volume] positiveHalfspace e := by
  set q : Space 1 → ℝ → ℝ≥0∞ := fun x r ↦
    volume (E ∩ closedBall x r) / volume (closedBall x r) with hq
  set G : Set (Space 1) :=
    {x | Tendsto (q x) (𝓝[>] 0) (𝓝 (E.indicator 1 x))} with hGdef
  have hG : volume Gᶜ = 0 :=
    ae_iff.mp (Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet volume hE)
  -- density values are constant along dilations within the good set
  have hconst : ∀ x ∈ G, ∀ a : ℝ, 0 < a → a • x ∈ G → (a • x ∈ E ↔ x ∈ E) := by
    intro x hx a ha hax
    have hmap : Tendsto (fun r : ℝ ↦ r / a) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have h := ((continuous_id.div_const a).tendsto (0 : ℝ)).mono_left
          (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
        simpa using h
      · filter_upwards [self_mem_nhdsWithin] with r hr
        exact div_pos hr ha
    have h1 : Tendsto (q (a • x)) (𝓝[>] 0) (𝓝 (E.indicator 1 x)) := by
      refine (hx.comp hmap).congr fun r ↦ ?_
      have h := measure_inter_closedBall_div_smul_eq hcone ha x (r / a)
      rw [mul_div_cancel₀ r ha.ne'] at h
      simpa [hq] using h.symm
    have hlim := tendsto_nhds_unique hax h1
    by_cases hxE : x ∈ E <;> by_cases haxE : a • x ∈ E <;>
      simp_all [indicator_of_mem, indicator_of_notMem]
  set e₀ : Space 1 := EuclideanSpace.single 0 1 with he₀
  have he₀n : ‖e₀‖ = 1 := by simp [he₀]
  have hinner : ∀ y : Space 1, inner ℝ e₀ y = y 0 := fun y ↦ by
    simp [he₀, EuclideanSpace.inner_single_left]
  have hP : ∀ y : Space 1, y ∈ positiveHalfspace e₀ ↔ 0 < y 0 := fun y ↦ by
    show 0 < inner ℝ e₀ y ↔ _
    rw [hinner]
  have hN : ∀ y : Space 1, y ∈ positiveHalfspace (-e₀) ↔ y 0 < 0 := fun y ↦ by
    show 0 < inner ℝ (-e₀) y ↔ _
    rw [inner_neg_left, hinner]
    constructor <;> intro h <;> linarith
  have hscale : ∀ p y : Space 1, 0 < y 0 / p 0 → y = (y 0 / p 0) • p := by
    intro p y hpos
    have hp : p 0 ≠ 0 := by
      intro h0
      rw [h0, div_zero] at hpos
      exact lt_irrefl _ hpos
    ext i
    fin_cases i
    simp [hp]
  have hzero : ∀ y : Space 1, y 0 = 0 → y = 0 := by
    intro y hy
    ext i
    fin_cases i
    simpa using hy
  have hnull0 : volume ({0} : Set (Space 1)) = 0 := measure_singleton 0
  -- good points on both sides
  have hexists : ∀ U : Set (Space 1), IsOpen U → U.Nonempty → ∃ x ∈ G, x ∈ U := by
    intro U hU hne
    by_contra hcon
    push Not at hcon
    have hsub : U ⊆ Gᶜ := fun x hxU hxG ↦ hcon x hxG hxU
    exact (hU.measure_pos volume hne).ne' (measure_mono_null hsub hG)
  have hPopen : IsOpen (positiveHalfspace e₀) :=
    isOpen_lt continuous_const (continuous_const.inner continuous_id)
  have hNopen : IsOpen (positiveHalfspace (-e₀)) :=
    isOpen_lt continuous_const (continuous_const.inner continuous_id)
  obtain ⟨x₁, hx₁G, hx₁P⟩ := hexists _ hPopen ⟨e₀, by rw [hP]; simp [he₀]⟩
  obtain ⟨x₂, hx₂G, hx₂N⟩ := hexists _ hNopen ⟨-e₀, by rw [hN]; simp [he₀]⟩
  rw [hP] at hx₁P
  rw [hN] at hx₂N
  -- every good point on a side has the same membership as the chosen point
  have hside₁ : ∀ y ∈ G, 0 < y 0 → (y ∈ E ↔ x₁ ∈ E) := by
    intro y hyG hy
    have hpos : 0 < y 0 / x₁ 0 := div_pos hy hx₁P
    have h := hconst x₁ hx₁G _ hpos (by rw [← hscale x₁ y hpos]; exact hyG)
    rwa [← hscale x₁ y hpos] at h
  have hside₂ : ∀ y ∈ G, y 0 < 0 → (y ∈ E ↔ x₂ ∈ E) := by
    intro y hyG hy
    have hpos : 0 < y 0 / x₂ 0 := div_pos_of_neg_of_neg hy hx₂N
    have h := hconst x₂ hx₂G _ hpos (by rw [← hscale x₂ y hpos]; exact hyG)
    rwa [← hscale x₂ y hpos] at h
  have hbad : volume (Gᶜ ∪ {0}) = 0 := measure_union_null hG hnull0
  have hcases : ∀ y : Space 1, y ∉ Gᶜ ∪ {0} →
      ((0 < y 0 ∧ (y ∈ E ↔ x₁ ∈ E)) ∨ (y 0 < 0 ∧ (y ∈ E ↔ x₂ ∈ E))) := by
    intro y hy
    simp only [mem_union, mem_compl_iff, not_or, not_not, mem_singleton_iff] at hy
    obtain ⟨hyG, hy0⟩ := hy
    have hy0' : y 0 ≠ 0 := fun h ↦ hy0 (hzero y h)
    rcases lt_or_gt_of_ne hy0' with hlt | hgt
    · exact Or.inr ⟨hlt, hside₂ y hyG hlt⟩
    · exact Or.inl ⟨hgt, hside₁ y hyG hgt⟩
  by_cases h₁ : x₁ ∈ E <;> by_cases h₂ : x₂ ∈ E
  · exfalso
    apply hnt.2
    refine measure_mono_null (fun y hyc ↦ ?_) hbad
    by_contra hy
    rcases hcases y hy with ⟨-, h⟩ | ⟨-, h⟩
    · exact hyc (h.mpr h₁)
    · exact hyc (h.mpr h₂)
  · refine ⟨e₀, he₀n, ae_eq_set.mpr ⟨?_, ?_⟩⟩
    · refine measure_mono_null (fun y hy ↦ ?_) hbad
      obtain ⟨hyE, hyP⟩ := hy
      rw [hP] at hyP
      by_contra hyb
      rcases hcases y hyb with ⟨hpos, -⟩ | ⟨-, h⟩
      · exact hyP hpos
      · exact h₂ (h.mp hyE)
    · refine measure_mono_null (fun y hy ↦ ?_) hbad
      obtain ⟨hyP, hyE⟩ := hy
      rw [hP] at hyP
      by_contra hyb
      rcases hcases y hyb with ⟨-, h⟩ | ⟨hneg, -⟩
      · exact hyE (h.mpr h₁)
      · linarith
  · refine ⟨-e₀, by rw [norm_neg, he₀n], ae_eq_set.mpr ⟨?_, ?_⟩⟩
    · refine measure_mono_null (fun y hy ↦ ?_) hbad
      obtain ⟨hyE, hyN⟩ := hy
      rw [hN] at hyN
      by_contra hyb
      rcases hcases y hyb with ⟨-, h⟩ | ⟨hneg, -⟩
      · exact h₁ (h.mp hyE)
      · exact hyN hneg
    · refine measure_mono_null (fun y hy ↦ ?_) hbad
      obtain ⟨hyN, hyE⟩ := hy
      rw [hN] at hyN
      by_contra hyb
      rcases hcases y hyb with ⟨hpos, -⟩ | ⟨-, h⟩
      · linarith
      · exact hyE (h.mpr h₂)
  · exfalso
    apply hnt.1
    refine measure_mono_null (fun y hyE ↦ ?_) hbad
    by_contra hy
    rcases hcases y hy with ⟨-, h⟩ | ⟨-, h⟩
    · exact h₁ (h.mp hyE)
    · exact h₂ (h.mp hyE)

/-- **Base case.** A minimizing cone in `Space 1` is a.e. one of the two open half-lines. -/
theorem IsMinimizingCone.ae_eq_positiveHalfspace_one {E : Set (Space 1)}
    (hE : IsMinimizingCone E) : ∃ e : Space 1, ‖e‖ = 1 ∧ E =ᵐ[volume] positiveHalfspace e :=
  ae_eq_positiveHalfspace_of_ae_cone_one hE.measurableSet hE.nontrivial hE.dilation

/-! ### 7. The dimension-reduction step of GR16 -/

/-- **Dimension reduction (GR5 + GR6, induction step of GR16).** If every minimizing cone in
`Space k` is a.e. a half-space, then every tangent cone of a minimizing cone in `Space (k + 1)` at
a nonzero boundary point `x₀` is a.e. a half-space, whose unit normal is orthogonal to `x₀`. -/
theorem IsMinimizingCone.isTangentCone_ae_eq_halfspace_of_lower {k : ℕ}
    (hlow : ∀ T' : Set (Space k), IsMinimizingCone T' →
      ∃ e : Space k, ‖e‖ = 1 ∧ T' =ᵐ[volume] positiveHalfspace e)
    {E : Set (Space (k + 1))} (hE : IsMinimizingCone E) {x₀ : Space (k + 1)}
    (hx₀ : x₀ ∈ measureTheoreticBoundary E) (hx₀0 : x₀ ≠ 0) {T : Set (Space (k + 1))}
    (hT : IsTangentCone E x₀ T) :
    ∃ e : Space (k + 1), ‖e‖ = 1 ∧ inner ℝ e x₀ = 0 ∧ T =ᵐ[volume] positiveHalfspace e := by
  have hTc := hT.isMinimizingCone hE.minimizer ⟨hx₀, mem_univ x₀⟩
  have hinv := hT.ae_mem_add_smul_iff hE hx₀
  set v : Space (k + 1) := ‖x₀‖⁻¹ • x₀ with hvdef
  have hn : 0 < ‖x₀‖ := norm_pos_iff.mpr hx₀0
  have hv : ‖v‖ = 1 := by
    rw [hvdef, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
  have hinv' : ∀ t : ℝ, ∀ᵐ x ∂volume, x ∈ T ↔ x + t • v ∈ T := by
    intro t
    filter_upwards [hinv (t * ‖x₀‖⁻¹)] with x hx
    rw [hvdef, smul_smul]
    exact hx
  obtain ⟨Q, T', hQ, -, hT'c, hae⟩ := hTc.exists_cylinder_of_invariant hv hinv'
  obtain ⟨e', he', hT'e⟩ := hlow T' hT'c
  have hx₀v : x₀ = ‖x₀‖ • v := by
    rw [hvdef, smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
  refine ⟨Q (point e' 0), by rw [Q.norm_map, norm_point_zero, he'], ?_,
    ae_eq_positiveHalfspace_of_ae_eq_cylinder Q hae hT'e⟩
  rw [hx₀v, inner_smul_right, ← hQ, Q.inner_map_map, inner_verticalDirection_right, last_point,
    mul_zero]

/-- In `Space 2`, every tangent cone of a minimizing cone at a nonzero boundary point is a.e. a
half-plane whose boundary line contains the base point. -/
theorem IsMinimizingCone.isTangentCone_ae_eq_halfspace_two {E : Set (Space 2)}
    (hE : IsMinimizingCone E) {x₀ : Space 2} (hx₀ : x₀ ∈ measureTheoreticBoundary E)
    (hx₀0 : x₀ ≠ 0) {T : Set (Space 2)} (hT : IsTangentCone E x₀ T) :
    ∃ e : Space 2, ‖e‖ = 1 ∧ inner ℝ e x₀ = 0 ∧ T =ᵐ[volume] positiveHalfspace e :=
  hE.isTangentCone_ae_eq_halfspace_of_lower (k := 1)
    (fun _ hT' ↦ hT'.ae_eq_positiveHalfspace_one) hx₀ hx₀0 hT

/-- **Reduction of vertically invariant cones.** If every minimizing cone in `Space k` is a.e. a
half-space, then so is every vertically invariant minimizing cone in `Space (k + 1)`. -/
theorem IsMinimizingCone.ae_eq_halfspace_of_vertical_invariant_of_lower {k : ℕ}
    (hlow : ∀ T' : Set (Space k), IsMinimizingCone T' →
      ∃ e : Space k, ‖e‖ = 1 ∧ T' =ᵐ[volume] positiveHalfspace e)
    {T : Set (Space (k + 1))} (hT : IsMinimizingCone T)
    (hinv : ∀ t : ℝ, ∀ᵐ x ∂volume, x ∈ T ↔ x + t • verticalDirection k ∈ T) :
    ∃ e : Space (k + 1), ‖e‖ = 1 ∧ T =ᵐ[volume] positiveHalfspace e := by
  obtain ⟨T', -, hT'c, hae⟩ := hT.exists_cylinder_of_vertical_invariant hinv
  obtain ⟨e', he', hT'e⟩ := hlow T' hT'c
  exact ⟨point e' 0, by rw [norm_point_zero, he'],
    hae.trans (preimage_horizontal_ae_eq_positiveHalfspace hT'e)⟩

/-- The open obligation `IsDirectedMinimizingCone.halfspace_of_verticalInvariant_le_eight` reduces,
via GR6, to the classification of minimizing cones one dimension lower. -/
theorem IsDirectedMinimizingCone.halfspace_of_verticalInvariant_of_lower {m : ℕ}
    (hlow : ∀ T' : Set (Space m), IsMinimizingCone T' →
      ∃ e : Space m, ‖e‖ = 1 ∧ T' =ᵐ[volume] positiveHalfspace e)
    {E : Set (Space (m + 1))} (hE : IsDirectedMinimizingCone E)
    (hinv : ∀ t : ℝ, ∀ᵐ x ∂volume, x ∈ E ↔ x + t • verticalDirection m ∈ E) :
    ∃ e : Space (m + 1), ‖e‖ = 1 ∧ E =ᵐ[volume] positiveHalfspace e :=
  hE.isMinimizingCone.ae_eq_halfspace_of_vertical_invariant_of_lower hlow hinv

/-- In ambient dimension two, vertically invariant directed minimizing cones are half-planes. -/
theorem IsDirectedMinimizingCone.halfspace_of_verticalInvariant_two {E : Set (Space (1 + 1))}
    (hE : IsDirectedMinimizingCone E)
    (hinv : ∀ t : ℝ, ∀ᵐ x ∂volume, x ∈ E ↔ x + t • verticalDirection 1 ∈ E) :
    ∃ e : Space (1 + 1), ‖e‖ = 1 ∧ E =ᵐ[volume] positiveHalfspace e :=
  hE.halfspace_of_verticalInvariant_of_lower (fun _ hT' ↦ hT'.ae_eq_positiveHalfspace_one) hinv

/-! ### 8. Half-spaces are minimizing cones -/

theorem isOpen_positiveHalfspace {d : ℕ} (e : Space d) : IsOpen (positiveHalfspace e) :=
  isOpen_lt continuous_const (continuous_const.inner continuous_id)

private theorem inner_verticalDirection_point {k : ℕ} (y : Space k) (t : ℝ) :
    inner ℝ (verticalDirection k) (point y t) = t := by
  rw [real_inner_comm, inner_verticalDirection_right, last_point]

private theorem abs_apply_le_norm_space {d : ℕ} (w : Space d) (i : Fin d) : |w i| ≤ ‖w‖ := by
  have h := abs_real_inner_le_norm (EuclideanSpace.single i (1 : ℝ)) w
  simpa [EuclideanSpace.inner_single_left] using h

/-- Divergence pairing of the upper half-space `{x | 0 < x_last}`: only the trace of the field on
the horizontal hyperplane survives. -/
theorem integral_indicator_upperHalfspace_mul_fieldDivergence {k : ℕ}
    {Y : Space (k + 1) → Space (k + 1)} (hY : ContDiff ℝ 1 Y) (hc : HasCompactSupport Y) :
    (∫ x, (positiveHalfspace (verticalDirection k)).indicator (fun _ ↦ (1 : ℝ)) x *
        fieldDivergence (EuclideanSpace.basisFun (Fin (k + 1)) ℝ) Y x) =
      -∫ y : Space k, Y (point y 0) (Fin.last k) := by
  rw [integral_indicator_mul_fieldDivergence_eq_slices
    (isOpen_positiveHalfspace _).measurableSet hY hc]
  have hind : ∀ (y : Space k) (t : ℝ),
      (positiveHalfspace (verticalDirection k)).indicator (fun _ ↦ (1 : ℝ)) (point y t) =
        (Ioi (0 : ℝ)).indicator (fun _ ↦ (1 : ℝ)) t := by
    intro y t
    by_cases ht : 0 < t
    · have h1 : point y t ∈ positiveHalfspace (verticalDirection k) := by
        show 0 < inner ℝ (verticalDirection k) (point y t)
        rw [inner_verticalDirection_point]
        exact ht
      rw [indicator_of_mem h1, indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht)]
    · have h1 : point y t ∉ positiveHalfspace (verticalDirection k) := by
        show ¬ 0 < inner ℝ (verticalDirection k) (point y t)
        rw [inner_verticalDirection_point]
        exact ht
      rw [indicator_of_notMem h1, indicator_of_notMem (show t ∉ Ioi (0 : ℝ) from ht)]
  simp only [hind]
  have hhor : ∀ t : ℝ, (∫ y : Space k, (Ioi (0 : ℝ)).indicator (fun _ ↦ (1 : ℝ)) t *
      fieldDivergence (EuclideanSpace.basisFun (Fin k) ℝ)
        (fun z ↦ horizontal (Y (point z t))) y) = 0 := by
    intro t
    rw [integral_const_mul, integral_fieldDivergence_eq_zero _ (contDiff_horizontal_slice hY t)
      (hasCompactSupport_horizontal_slice hc t), mul_zero]
  have hver : ∀ y : Space k, (∫ t : ℝ, (Ioi (0 : ℝ)).indicator (fun _ ↦ (1 : ℝ)) t *
      deriv (fun s ↦ Y (point y s) (Fin.last k)) t) = -Y (point y 0) (Fin.last k) := by
    intro y
    have h := (hasCompactSupport_vertical_profile hc y).integral_Ioi_deriv_eq
      (contDiff_vertical_profile hY y) 0
    rw [← h, ← integral_indicator measurableSet_Ioi]
    congr 1
    funext t
    by_cases ht : t ∈ Ioi (0 : ℝ) <;> simp [ht]
  simp only [hhor, integral_zero, zero_add, hver, integral_neg]

/-- The perimeter of the upper half-space in an open set is at most the area of the trace of the
open set on the horizontal hyperplane. -/
theorem variationalPerimeter_upperHalfspace_le {k : ℕ} {U : Set (Space (k + 1))}
    (hU : IsOpen U) :
    variationalPerimeter (EuclideanSpace.basisFun (Fin (k + 1)) ℝ)
        (positiveHalfspace (verticalDirection k)) U ≤ volume {y : Space k | point y 0 ∈ U} := by
  have hU' : MeasurableSet {y : Space k | point y 0 ∈ U} :=
    (hU.preimage (horizontalEmbedding k).continuous).measurableSet
  unfold variationalPerimeter
  refine iSup_le fun Y ↦ iSup_le fun hY ↦ iSup_le fun hc ↦ iSup_le fun hs ↦ iSup_le fun hu ↦ ?_
  rw [integral_indicator_upperHalfspace_mul_fieldDivergence hY hc, norm_neg, ofReal_norm]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  rw [← lintegral_indicator_one hU']
  refine lintegral_mono fun y ↦ ?_
  by_cases hy : point y 0 ∈ U
  · rw [indicator_of_mem (show y ∈ {y : Space k | point y 0 ∈ U} from hy), Pi.one_apply,
      Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_one.mpr ((abs_apply_le_norm_space _ _).trans (hu _))
  · have h0 : Y (point y 0) = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hy (hs h))
    simp [h0]

/-- **Calibration lower bound.** Every compact perturbation of the upper half-space inside `U`
has perimeter in `U` at least the area of the trace of `U` on the horizontal hyperplane. -/
theorem volume_le_variationalPerimeter_of_upperHalfspace_perturbation {k : ℕ}
    {U D K : Set (Space (k + 1))} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hHD : ∀ᵐ x ∂volume, x ∉ K → (x ∈ positiveHalfspace (verticalDirection k) ↔ x ∈ D)) :
    volume {y : Space k | point y 0 ∈ U} ≤
      variationalPerimeter (EuclideanSpace.basisFun (Fin (k + 1)) ℝ) D U := by
  have hU'o : IsOpen {y : Space k | point y 0 ∈ U} :=
    hU.preimage (horizontalEmbedding k).continuous
  rw [hU'o.measure_eq_iSup_isCompact volume]
  refine iSup_le fun K' ↦ iSup_le fun hK'U ↦ iSup_le fun hK' ↦ ?_
  set L : Set (Space (k + 1)) := K ∪ (horizontalEmbedding k) '' K' with hLdef
  have hL : IsCompact L := hK.union (hK'.image (horizontalEmbedding k).continuous)
  have hLU : L ⊆ U := union_subset hKU (by rintro _ ⟨y, hy, rfl⟩; exact hK'U hy)
  obtain ⟨W, hWo, hLW, hWU, hWc⟩ := exists_open_between_and_isCompact_closure hL hU hLU
  obtain ⟨V, hVo, hWV, hVU, hVc⟩ := exists_open_between_and_isCompact_closure hWc hU hWU
  obtain ⟨χ, hχ, hχrange, hχsupp, hχone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := 1) hVo isClosed_closure hWV
  have hχval (x : Space (k + 1)) : χ x ∈ Icc (0 : ℝ) 1 := hχrange ⟨x, rfl⟩
  set Y : Space (k + 1) → Space (k + 1) := fun x ↦ (-χ x) • verticalDirection k with hYdef
  have hYc1 : ContDiff ℝ 1 Y := hχ.neg.smul contDiff_const
  have hYts : tsupport Y ⊆ closure V := by
    apply closure_minimal _ isClosed_closure
    intro x hx
    apply subset_closure
    rw [← hχsupp]
    intro h0
    apply hx
    simp [Y, h0]
  have hYc : HasCompactSupport Y := hVc.of_isClosed_subset (isClosed_tsupport _) hYts
  have hYU : tsupport Y ⊆ U := hYts.trans hVU
  have hen : ‖verticalDirection k‖ = 1 := by simp [verticalDirection]
  have hYu : ∀ x, ‖Y x‖ ≤ 1 := by
    intro x
    change ‖(-χ x) • verticalDirection k‖ ≤ 1
    rw [norm_smul, norm_neg, Real.norm_of_nonneg (hχval x).1, hen, mul_one]
    exact (hχval x).2
  have hdivW : ∀ x ∈ W,
      fieldDivergence (EuclideanSpace.basisFun (Fin (k + 1)) ℝ) Y x = 0 := by
    intro x hx
    have hev : Y =ᶠ[𝓝 x] fun _ ↦ (-1 : ℝ) • verticalDirection k := by
      filter_upwards [hWo.mem_nhds hx] with z hz
      simp [Y, (hχone z).mp (subset_closure hz)]
    simp [fieldDivergence, hev.fderiv_eq]
  have hpair : (∫ x, D.indicator (fun _ ↦ (1 : ℝ)) x *
        fieldDivergence (EuclideanSpace.basisFun (Fin (k + 1)) ℝ) Y x) =
      ∫ x, (positiveHalfspace (verticalDirection k)).indicator (fun _ ↦ (1 : ℝ)) x *
        fieldDivergence (EuclideanSpace.basisFun (Fin (k + 1)) ℝ) Y x := by
    apply integral_congr_ae
    filter_upwards [hHD] with x hx
    by_cases hxK : x ∈ K
    · rw [hdivW x (hLW (Or.inl hxK)), mul_zero, mul_zero]
    · have h := hx hxK
      by_cases hxD : x ∈ D
      · rw [indicator_of_mem hxD, indicator_of_mem (h.mpr hxD)]
      · rw [indicator_of_notMem hxD, indicator_of_notMem (fun h' ↦ hxD (h.mp h'))]
  have hval : (∫ x, (positiveHalfspace (verticalDirection k)).indicator (fun _ ↦ (1 : ℝ)) x *
        fieldDivergence (EuclideanSpace.basisFun (Fin (k + 1)) ℝ) Y x) =
      ∫ y : Space k, χ (point y 0) := by
    rw [integral_indicator_upperHalfspace_mul_fieldDivergence hYc1 hYc, ← integral_neg]
    congr 1
    funext y
    simp [Y, verticalDirection]
  have hsuppχ : Function.support (fun y : Space k ↦ χ (point y 0)) ⊆
      horizontal '' closure V := by
    intro y hy
    refine ⟨point y 0, subset_closure ?_, horizontal_point y 0⟩
    rw [← hχsupp]
    exact hy
  have hcK : IsCompact (horizontal '' closure V : Set (Space k)) :=
    hVc.image continuous_horizontal
  have hint : Integrable (fun y : Space k ↦ χ (point y 0)) volume :=
    (hχ.continuous.comp (horizontalEmbedding k).continuous).integrable_of_hasCompactSupport
      (hcK.of_isClosed_subset (isClosed_tsupport _) (closure_minimal hsuppχ hcK.isClosed))
  have hK'le : volume.real K' ≤ ∫ y : Space k, χ (point y 0) := by
    have hle : (fun y ↦ K'.indicator (fun _ ↦ (1 : ℝ)) y) ≤ fun y ↦ χ (point y 0) := by
      intro y
      show K'.indicator (fun _ ↦ (1 : ℝ)) y ≤ χ (point y 0)
      by_cases hy : y ∈ K'
      · rw [indicator_of_mem hy]
        exact le_of_eq ((hχone _).mp (subset_closure (hLW (Or.inr ⟨y, hy, rfl⟩)))).symm
      · rw [indicator_of_notMem hy]
        exact (hχval _).1
    calc volume.real K' = ∫ y, K'.indicator (fun _ ↦ (1 : ℝ)) y := by
          rw [integral_indicator_const _ hK'.measurableSet, smul_eq_mul, mul_one]
      _ ≤ _ := integral_mono ((integrableOn_const hK'.measure_lt_top.ne).integrable_indicator
          hK'.measurableSet) hint hle
  calc volume K' = ENNReal.ofReal (volume.real K') :=
        (ofReal_measureReal hK'.measure_lt_top.ne).symm
    _ ≤ ENNReal.ofReal ‖∫ x, D.indicator (fun _ ↦ (1 : ℝ)) x *
          fieldDivergence (EuclideanSpace.basisFun (Fin (k + 1)) ℝ) Y x‖ := by
        apply ENNReal.ofReal_le_ofReal
        rw [hpair, hval, Real.norm_eq_abs]
        exact hK'le.trans (le_abs_self _)
    _ ≤ variationalPerimeter (EuclideanSpace.basisFun (Fin (k + 1)) ℝ) D U := by
        unfold variationalPerimeter
        exact le_iSup_of_le Y (le_iSup_of_le hYc1 (le_iSup_of_le hYc
          (le_iSup_of_le hYU (le_iSup_of_le hYu le_rfl))))

/-- The upper half-space is a local perimeter minimizer in all of `Space (k + 1)`. -/
theorem isLocalPerimeterMinimizer_upperHalfspace (k : ℕ) :
    IsLocalPerimeterMinimizer (EuclideanSpace.basisFun (Fin (k + 1)) ℝ)
      (positiveHalfspace (verticalDirection k)) univ := by
  refine isLocalPerimeterMinimizer_univ _ (isOpen_positiveHalfspace _).measurableSet
    (fun n ↦ ?_) (fun U D K hU _ hK hKU hHD ↦ (variationalPerimeter_upperHalfspace_le hU).trans
      (volume_le_variationalPerimeter_of_upperHalfspace_perturbation hU hK hKU hHD))
  refine ne_top_of_le_ne_top ?_ (variationalPerimeter_upperHalfspace_le isOpen_ball)
  have h : {y : Space k | point y 0 ∈ ball (0 : Space (k + 1)) ((n : ℝ) + 1)} =
      ball 0 ((n : ℝ) + 1) := by
    ext y
    simp [norm_point_zero]
  rw [h]
  exact measure_ball_lt_top.ne

/-- Every open half-space with unit normal is a minimizing cone. -/
theorem isMinimizingCone_positiveHalfspace {k : ℕ} {e : Space (k + 1)} (he : ‖e‖ = 1) :
    IsMinimizingCone (positiveHalfspace e) := by
  have hen : inner ℝ (verticalDirection k) (verticalDirection k) = 1 := by
    rw [real_inner_self_eq_norm_sq]
    simp [verticalDirection]
  have h0 : IsMinimizingCone (positiveHalfspace (verticalDirection k)) := by
    refine ⟨(isOpen_positiveHalfspace _).measurableSet, ⟨?_, ?_⟩,
      fun a ha ↦ Eventually.of_forall fun x ↦ ?_, isLocalPerimeterMinimizer_upperHalfspace k⟩
    · refine ((isOpen_positiveHalfspace _).measure_pos volume ⟨verticalDirection k, ?_⟩).ne'
      show 0 < inner ℝ (verticalDirection k) (verticalDirection k)
      rw [hen]
      exact one_pos
    · have hsub : positiveHalfspace (-verticalDirection k) ⊆
          (positiveHalfspace (verticalDirection k))ᶜ := by
        intro x hx hx'
        have h1 : 0 < inner ℝ (-verticalDirection k) x := hx
        have h2 : 0 < inner ℝ (verticalDirection k) x := hx'
        rw [inner_neg_left] at h1
        linarith
      refine fun hnull ↦ ((isOpen_positiveHalfspace _).measure_pos volume
        ⟨-verticalDirection k, ?_⟩).ne' (measure_mono_null hsub hnull)
      show 0 < inner ℝ (-verticalDirection k) (-verticalDirection k)
      rw [inner_neg_left, inner_neg_right, neg_neg, hen]
      exact one_pos
    · show 0 < inner ℝ (verticalDirection k) x ↔ 0 < inner ℝ (verticalDirection k) (a • x)
      rw [inner_smul_right]
      exact ⟨fun h ↦ mul_pos ha h, fun h ↦ (pos_iff_pos_of_mul_pos h).mp ha⟩
  obtain ⟨Q, hQ⟩ := exists_linearIsometryEquiv_verticalDirection he
  have h1 := h0.preimage_linearIsometryEquiv Q.symm
  rwa [preimage_linearIsometryEquiv_symm_positiveHalfspace, hQ] at h1

/-- On the line, minimizing cones are exactly the sets a.e. equal to an open half-line. -/
theorem isMinimizingCone_iff_ae_eq_positiveHalfspace_one {E : Set (Space 1)} :
    IsMinimizingCone E ↔
      MeasurableSet E ∧ ∃ e : Space 1, ‖e‖ = 1 ∧ E =ᵐ[volume] positiveHalfspace e := by
  constructor
  · intro hE
    exact ⟨hE.measurableSet, hE.ae_eq_positiveHalfspace_one⟩
  · rintro ⟨hE, e, he, hEe⟩
    exact (isMinimizingCone_positiveHalfspace (k := 0) he).congr_ae hE hEe.symm

end SerrinEpigraph
