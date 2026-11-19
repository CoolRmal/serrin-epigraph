module

public import SerrinEpigraph.MinimalSurfaceIdentities
public import SerrinEpigraph.RegularBoundary

/-!
# Geometry of smooth boundary charts

For smooth boundary charts `IsSmoothBoundaryChart E U F` (defining-function form) this module
proves:

* on a chart, the level set `{F = 0}` is exactly the measure-theoretic boundary of `E`
  (`IsSmoothBoundaryChart.eq_zero_iff_mem_measureTheoreticBoundary`), and chart points of the
  boundary are `C¹` boundary points;
* **compatibility of charts**: two charts have the same sign pattern on their common domain
  (`IsSmoothBoundaryChart.pos_iff_pos_of_mem`), and at a common boundary point the same unit normal,
  second fundamental form and tangential gradients of normal components;
* the pointwise bounds `‖A v‖² ≤ |A|² ‖v‖²` and `‖δ f‖ ≤ ‖Df‖`;
* for cones: the position vector is tangent and annihilated by the shape operator, hence
  `⟪δ ⟪ν, e⟫, x⟫ = 0` (`IsSmoothBoundaryChart.inner_tangentialGradient_inner_chartNormal_self`);
* for vertically monotone sets: the normal has nonnegative vertical component
  (`IsSmoothBoundaryChart.fderiv_apply_nonneg_of_monotone`);
* a **constancy lemma** along level sets, proved with the inverse function theorem
  (`exists_forall_eq_of_fderiv_eq_zero_on_level`), and **local flatness**: where the second
  fundamental form vanishes, `E` is locally a.e. the half-space bounded by the tangent plane
  (`IsSmoothBoundaryChart.exists_ae_eq_halfspace_of_sqNorm_eq_zero`).
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory InnerProductSpace Filter
open scoped Topology ContDiff ENNReal NNReal

namespace SerrinEpigraph

/-! ### 1. Elementary helpers -/

private theorem tendsto_norm_natCast_add_one_aux :
    Tendsto (fun n : ℕ ↦ ‖((n : ℝ) + 1)‖) atTop atTop := by
  refine (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop).congr fun n ↦ ?_
  rw [Real.norm_of_nonneg (by positivity)]

/-- Along `t = (n + 1)⁻¹`, a function vanishing at `y` with positive directional derivative is
eventually positive. -/
private theorem eventually_pos_of_hasFDerivAt_aux {d : ℕ} {f : Space d → ℝ}
    {L : Space d →L[ℝ] ℝ} {y v : Space d} (hf : HasFDerivAt f L y) (hfy : f y = 0)
    (hv : 0 < L v) : ∀ᶠ n : ℕ in atTop, 0 < f (y + ((n : ℝ) + 1)⁻¹ • v) := by
  have hlim := hf.lim v tendsto_norm_natCast_add_one_aux
  simp only [hfy, sub_zero, smul_eq_mul] at hlim
  filter_upwards [hlim.eventually (lt_mem_nhds hv)] with n hn
  exact pos_of_mul_pos_right hn (by positivity)

private theorem tendsto_add_inv_smul_aux {d : ℕ} (y v : Space d) :
    Tendsto (fun n : ℕ ↦ y + ((n : ℝ) + 1)⁻¹ • v) atTop (𝓝 y) := by
  have h : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.congr fun n ↦ one_div _
  simpa using tendsto_const_nhds.add (h.smul_const v)

/-- A ball cannot be both a.e. inside and a.e. outside a set. -/
private theorem ball_not_ae_both_aux {d : ℕ} {E : Set (Space d)} {q : Space d} {δ : ℝ}
    (hδ : 0 < δ) (h1 : ∀ᵐ z ∂volume, z ∈ ball q δ → z ∈ E)
    (h2 : ∀ᵐ z ∂volume, z ∈ ball q δ → z ∉ E) : False := by
  have hnull : volume (ball q δ) = 0 := by
    refine measure_mono_null (fun z hz ↦ ?_) (ae_iff.mp (h1.and h2))
    intro hz'
    exact hz'.2 hz (hz'.1 hz)
  exact (measure_ball_pos volume q hδ).ne' hnull

/-- The tangential gradient pairs with a vector through the derivative. -/
theorem inner_tangentialGradient_eq_fderiv {d : ℕ} (F f : Space d → ℝ) (y v : Space d) :
    inner ℝ (tangentialGradient F f y) v = fderiv ℝ f y (tangentialProj F y v) := by
  rw [tangentialGradient, inner_tangentialProj_left, inner_gradient_left]

/-- The tangential gradient is no longer than the full derivative. -/
theorem norm_tangentialGradient_le_norm_fderiv {d : ℕ} {F f : Space d → ℝ} {y : Space d}
    (hy : gradient F y ≠ 0) : ‖tangentialGradient F f y‖ ≤ ‖fderiv ℝ f y‖ := by
  rw [tangentialGradient]
  refine (norm_tangentialProj_le hy _).trans (le_of_eq ?_)
  rw [gradient, LinearIsometryEquiv.norm_map]

/-- The gradient of a linear functional `⟪ν, ·⟫` is `ν`. -/
theorem gradient_inner_left_const {d : ℕ} (ν z : Space d) :
    gradient (fun x ↦ inner ℝ ν x) z = ν := by
  have hd : HasFDerivAt (fun x : Space d ↦ inner ℝ ν x)
      ((fderivInnerCLM ℝ (ν, z)).comp
        ((0 : Space d →L[ℝ] Space d).prod (ContinuousLinearMap.id ℝ (Space d)))) z :=
    (hasFDerivAt_const ν z).inner ℝ (hasFDerivAt_id z)
  refine ext_inner_right ℝ fun w ↦ ?_
  rw [inner_gradient_left, hd.fderiv]
  simp

theorem chartNormal_inner_left_const {d : ℕ} {ν : Space d} (hν : ‖ν‖ = 1) (z : Space d) :
    chartNormal (fun x ↦ inner ℝ ν x) z = ν := by
  rw [chartNormal, gradient_inner_left_const, hν, inv_one, one_smul]

/-! ### 2. Charts and the measure-theoretic boundary -/

namespace IsSmoothBoundaryChart

variable {d : ℕ} {E U : Set (Space d)} {F : Space d → ℝ} {y : Space d}

theorem fderiv_ne_zero (h : IsSmoothBoundaryChart E U F) (hy : y ∈ U) : fderiv ℝ F y ≠ 0 := by
  intro h0
  apply h.gradient_ne_zero y hy
  simp [gradient, h0]

theorem ae_mem_iff_of_mem (h : IsSmoothBoundaryChart E U F) :
    ∀ᵐ z ∂volume, z ∈ U → (z ∈ E ↔ 0 < F z) :=
  (ae_restrict_iff' h.isOpen.measurableSet).mp h.ae_mem_iff

theorem continuousOn (h : IsSmoothBoundaryChart E U F) : ContinuousOn F U :=
  h.contDiffOn.continuousOn

theorem hasFDerivAt (h : IsSmoothBoundaryChart E U F) (hy : y ∈ U) :
    HasFDerivAt F (fderiv ℝ F y) y :=
  ((h.contDiffAt hy).differentiableAt (by simp)).hasFDerivAt

theorem contDiffOn_one (h : IsSmoothBoundaryChart E U F) : ContDiffOn ℝ 1 F U :=
  h.contDiffOn.of_le (by simp)

/-- Restriction of a chart to a smaller open set. -/
theorem mono (h : IsSmoothBoundaryChart E U F) {V : Set (Space d)} (hV : IsOpen V)
    (hVU : V ⊆ U) : IsSmoothBoundaryChart E V F where
  isOpen := hV
  contDiffOn := h.contDiffOn.mono hVU
  gradient_ne_zero z hz := h.gradient_ne_zero z (hVU hz)
  ae_mem_iff := by
    rw [ae_restrict_iff' hV.measurableSet]
    filter_upwards [h.ae_mem_iff_of_mem] with z hz hzV
    exact hz (hVU hzV)

/-- Chart points on the level set are `C¹` boundary points. -/
theorem isC1BoundaryPoint (h : IsSmoothBoundaryChart E U F) (hy : y ∈ U) (hFy : F y = 0) :
    IsC1BoundaryPoint E y := by
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp h.isOpen y hy
  refine ⟨F, r, hr, h.contDiffOn_one.mono hrU, hFy, h.fderiv_ne_zero hy, ?_⟩
  filter_upwards [h.ae_mem_iff_of_mem] with z hz hzB
  exact hz (hrU hzB)

theorem mem_measureTheoreticBoundary (h : IsSmoothBoundaryChart E U F) (hy : y ∈ U)
    (hFy : F y = 0) : y ∈ measureTheoreticBoundary E :=
  (h.isC1BoundaryPoint hy hFy).mem_measureTheoreticBoundary

/-- Boundary points of `E` in a chart lie on the level set. -/
theorem eq_zero_of_mem_measureTheoreticBoundary (h : IsSmoothBoundaryChart E U F)
    (hy : y ∈ U) (hyB : y ∈ measureTheoreticBoundary E) : F y = 0 := by
  have hcont : ContinuousAt F y := h.continuousOn.continuousAt (h.isOpen.mem_nhds hy)
  by_contra hne
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · obtain ⟨δ, hδ, hδsub⟩ := Metric.eventually_nhds_iff_ball.mp
      ((hcont.eventually (gt_mem_nhds hneg)).and (h.isOpen.mem_nhds hy))
    apply (hyB δ hδ).1
    refine measure_mono_null (fun z hz ↦ ?_) (ae_iff.mp h.ae_mem_iff_of_mem)
    intro hz'
    have h1 := (hz' (hδsub z hz.2).2).mp hz.1
    have h2 := (hδsub z hz.2).1
    linarith
  · obtain ⟨δ, hδ, hδsub⟩ := Metric.eventually_nhds_iff_ball.mp
      ((hcont.eventually (lt_mem_nhds hpos)).and (h.isOpen.mem_nhds hy))
    apply (hyB δ hδ).2
    refine measure_mono_null (fun z hz ↦ ?_) (ae_iff.mp h.ae_mem_iff_of_mem)
    intro hz'
    exact hz.2 ((hz' (hδsub z hz.1).2).mpr (hδsub z hz.1).1)

theorem eq_zero_iff_mem_measureTheoreticBoundary (h : IsSmoothBoundaryChart E U F)
    (hy : y ∈ U) : F y = 0 ↔ y ∈ measureTheoreticBoundary E :=
  ⟨h.mem_measureTheoreticBoundary hy, h.eq_zero_of_mem_measureTheoreticBoundary hy⟩

end IsSmoothBoundaryChart

/-- A set which is a.e. the half-space `{⟪ν, ·⟫ > 0}` on an open set has the linear chart there. -/
theorem isSmoothBoundaryChart_inner {d : ℕ} {E V : Set (Space d)} (hV : IsOpen V) {ν : Space d}
    (hν : ν ≠ 0) (hEV : ∀ᵐ z ∂volume, z ∈ V → (z ∈ E ↔ 0 < inner ℝ ν z)) :
    IsSmoothBoundaryChart E V (fun z ↦ inner ℝ ν z) where
  isOpen := hV
  contDiffOn := ((contDiff_const (c := ν)).inner ℝ contDiff_id).contDiffOn
  gradient_ne_zero z _ := by rw [gradient_inner_left_const]; exact hν
  ae_mem_iff := (ae_restrict_iff' hV.measurableSet).mpr hEV

/-! ### 3. Compatibility of two charts -/

namespace IsSmoothBoundaryChart

variable {d : ℕ} {E U₁ U₂ : Set (Space d)} {F₁ F₂ : Space d → ℝ} {y : Space d}

/-- Two charts of the same set have the same sign pattern on their common domain. -/
theorem pos_iff_pos_of_mem (h₁ : IsSmoothBoundaryChart E U₁ F₁)
    (h₂ : IsSmoothBoundaryChart E U₂ F₂) {x : Space d} (hx₁ : x ∈ U₁) (hx₂ : x ∈ U₂) :
    0 < F₁ x ↔ 0 < F₂ x := by
  suffices key : ∀ {V₁ V₂ : Set (Space d)} {G₁ G₂ : Space d → ℝ},
      IsSmoothBoundaryChart E V₁ G₁ → IsSmoothBoundaryChart E V₂ G₂ → x ∈ V₁ → x ∈ V₂ →
        0 < G₁ x → 0 < G₂ x from ⟨key h₁ h₂ hx₁ hx₂, key h₂ h₁ hx₂ hx₁⟩
  intro V₁ V₂ G₁ G₂ g₁ g₂ hy₁ hy₂ hpos
  have hne : G₂ x ≠ 0 := by
    intro h0
    have := g₁.eq_zero_of_mem_measureTheoreticBoundary hy₁
      (g₂.mem_measureTheoreticBoundary hy₂ h0)
    linarith
  rcases lt_or_gt_of_ne hne with hneg | hpos₂
  · exfalso
    have hc₁ : ContinuousAt G₁ x := g₁.continuousOn.continuousAt (g₁.isOpen.mem_nhds hy₁)
    have hc₂ : ContinuousAt G₂ x := g₂.continuousOn.continuousAt (g₂.isOpen.mem_nhds hy₂)
    obtain ⟨δ, hδ, hδsub⟩ := Metric.eventually_nhds_iff_ball.mp
      (((hc₁.eventually (lt_mem_nhds hpos)).and (hc₂.eventually (gt_mem_nhds hneg))).and
        ((g₁.isOpen.inter g₂.isOpen).mem_nhds ⟨hy₁, hy₂⟩))
    refine ball_not_ae_both_aux (E := E) (q := x) hδ ?_ ?_
    · filter_upwards [g₁.ae_mem_iff_of_mem] with z hz hzB
      exact (hz (hδsub z hzB).2.1).mpr (hδsub z hzB).1.1
    · filter_upwards [g₂.ae_mem_iff_of_mem] with z hz hzB hzE
      have h1 := (hz (hδsub z hzB).2.2).mp hzE
      have h2 := (hδsub z hzB).1.2
      linarith
  · exact hpos₂

/-- Two charts at a common boundary point have the same unit normal. -/
theorem chartNormal_eq_of_mem_boundary (h₁ : IsSmoothBoundaryChart E U₁ F₁)
    (h₂ : IsSmoothBoundaryChart E U₂ F₂) (hy₁ : y ∈ U₁) (hy₂ : y ∈ U₂)
    (hyB : y ∈ measureTheoreticBoundary E) : chartNormal F₂ y = chartNormal F₁ y := by
  have hF₁y := h₁.eq_zero_of_mem_measureTheoreticBoundary hy₁ hyB
  have hF₂y := h₂.eq_zero_of_mem_measureTheoreticBoundary hy₂ hyB
  have hne₁ := h₁.gradient_ne_zero y hy₁
  have hne₂ := h₂.gradient_ne_zero y hy₂
  have hzero : ∀ z ∈ U₁ ∩ U₂, F₁ z = 0 → F₂ z = 0 := fun z hz hz0 ↦
    h₂.eq_zero_of_mem_measureTheoreticBoundary hz.2 (h₁.mem_measureTheoreticBoundary hz.1 hz0)
  have htg := SerrinEpigraph.tangentialGradient_eq_zero_of_eq_zero_on_level
    (h₁.isOpen.inter h₂.isOpen) (h₁.contDiffOn_one.mono inter_subset_left)
    (h₂.contDiffOn_one.mono inter_subset_right) hzero ⟨hy₁, hy₂⟩ hF₁y hne₁
  set ν₁ := chartNormal F₁ y with hν₁
  set lam := inner ℝ ν₁ (gradient F₂ y) with hlam
  have hgrad : gradient F₂ y = lam • ν₁ := by
    rw [tangentialGradient, tangentialProj_apply, sub_eq_zero] at htg
    exact htg
  have hν₁n : ‖ν₁‖ = 1 := norm_chartNormal hne₁
  have hd₁ : 0 < fderiv ℝ F₁ y ν₁ := by
    rw [← inner_gradient_left, real_inner_comm, hν₁, inner_chartNormal_gradient]
    exact norm_pos_iff.mpr hne₁
  have hlam_eq : fderiv ℝ F₂ y ν₁ = lam := by
    rw [← inner_gradient_left, hgrad, real_inner_smul_left, real_inner_self_eq_norm_sq, hν₁n]
    ring
  have hlam0 : 0 ≤ lam := by
    rw [← hlam_eq]
    refine ge_of_tendsto ((h₂.hasFDerivAt hy₂).lim ν₁ tendsto_norm_natCast_add_one_aux) ?_
    filter_upwards [eventually_pos_of_hasFDerivAt_aux (h₁.hasFDerivAt hy₁) hF₁y hd₁,
      (tendsto_add_inv_smul_aux y ν₁).eventually
        ((h₁.isOpen.inter h₂.isOpen).mem_nhds ⟨hy₁, hy₂⟩)] with n hn hnU
    have h2pos := (pos_iff_pos_of_mem h₁ h₂ hnU.1 hnU.2).mp hn
    rw [hF₂y, sub_zero, smul_eq_mul]
    exact (mul_pos (by positivity) h2pos).le
  have hlampos : 0 < lam := by
    refine lt_of_le_of_ne hlam0 fun h0 ↦ hne₂ ?_
    rw [hgrad, ← h0, zero_smul]
  rw [chartNormal, hgrad, norm_smul, hν₁n, mul_one, Real.norm_of_nonneg hlam0, smul_smul,
    inv_mul_cancel₀ hlampos.ne', one_smul]

theorem tangentialProj_eq_of_mem_boundary (h₁ : IsSmoothBoundaryChart E U₁ F₁)
    (h₂ : IsSmoothBoundaryChart E U₂ F₂) (hy₁ : y ∈ U₁) (hy₂ : y ∈ U₂)
    (hyB : y ∈ measureTheoreticBoundary E) : tangentialProj F₂ y = tangentialProj F₁ y := by
  unfold tangentialProj
  rw [h₁.chartNormal_eq_of_mem_boundary h₂ hy₁ hy₂ hyB]

/-- The derivative of a normal component `z ↦ ⟪ν z, v⟫`. -/
private theorem hasFDerivAt_inner_chartNormal_aux {E U : Set (Space d)} {F : Space d → ℝ}
    (h : IsSmoothBoundaryChart E U F) (hy : y ∈ U) (v : Space d) :
    HasFDerivAt (fun z ↦ inner ℝ (chartNormal F z) v)
      ((innerSL ℝ v).comp (fderiv ℝ (chartNormal F) y)) y := by
  have h1 := (innerSL ℝ v).hasFDerivAt.comp y (h.differentiableAt_chartNormal hy).hasFDerivAt
  refine h1.congr_of_eventuallyEq (Eventually.of_forall fun z ↦ ?_)
  simp [real_inner_comm]

/-- Tangential derivatives of the normal agree for two charts at a common boundary point. -/
theorem fderiv_chartNormal_tangentialProj_eq (h₁ : IsSmoothBoundaryChart E U₁ F₁)
    (h₂ : IsSmoothBoundaryChart E U₂ F₂) (hy₁ : y ∈ U₁) (hy₂ : y ∈ U₂)
    (hyB : y ∈ measureTheoreticBoundary E) (u : Space d) :
    fderiv ℝ (chartNormal F₂) y (tangentialProj F₁ y u) =
      fderiv ℝ (chartNormal F₁) y (tangentialProj F₁ y u) := by
  have hF₁y := h₁.eq_zero_of_mem_measureTheoreticBoundary hy₁ hyB
  have hne₁ := h₁.gradient_ne_zero y hy₁
  rw [← sub_eq_zero]
  refine ext_inner_right ℝ fun v ↦ ?_
  rw [inner_zero_left]
  have hfC : ContDiffOn ℝ 1
      (fun z ↦ inner ℝ (chartNormal F₂ z) v - inner ℝ (chartNormal F₁ z) v) (U₁ ∩ U₂) :=
    (((h₂.contDiffOn_inner_chartNormal v).of_le (by simp)).mono inter_subset_right).sub
      (((h₁.contDiffOn_inner_chartNormal v).of_le (by simp)).mono inter_subset_left)
  have hzero : ∀ z ∈ U₁ ∩ U₂, F₁ z = 0 →
      inner ℝ (chartNormal F₂ z) v - inner ℝ (chartNormal F₁ z) v = 0 := by
    intro z hz hz0
    rw [h₁.chartNormal_eq_of_mem_boundary h₂ hz.1 hz.2 (h₁.mem_measureTheoreticBoundary hz.1 hz0),
      sub_self]
  have htg := SerrinEpigraph.tangentialGradient_eq_zero_of_eq_zero_on_level
    (h₁.isOpen.inter h₂.isOpen) (h₁.contDiffOn_one.mono inter_subset_left) hfC hzero
    ⟨hy₁, hy₂⟩ hF₁y hne₁
  have hinner := congrArg (fun w ↦ inner ℝ w u) htg
  simp only [inner_zero_left] at hinner
  rw [inner_tangentialGradient_eq_fderiv,
    ((hasFDerivAt_inner_chartNormal_aux h₂ hy₂ v).fun_sub
      (hasFDerivAt_inner_chartNormal_aux h₁ hy₁ v)).fderiv] at hinner
  simpa [real_inner_comm, inner_sub_left] using hinner

theorem secondFundamentalForm_eq_of_mem_boundary (h₁ : IsSmoothBoundaryChart E U₁ F₁)
    (h₂ : IsSmoothBoundaryChart E U₂ F₂) (hy₁ : y ∈ U₁) (hy₂ : y ∈ U₂)
    (hyB : y ∈ measureTheoreticBoundary E) :
    secondFundamentalForm F₂ y = secondFundamentalForm F₁ y := by
  ext1 u
  rw [h₂.secondFundamentalForm_apply hy₂, h₁.secondFundamentalForm_apply hy₁,
    h₁.tangentialProj_eq_of_mem_boundary h₂ hy₁ hy₂ hyB,
    h₁.fderiv_chartNormal_tangentialProj_eq h₂ hy₁ hy₂ hyB]

theorem sqNormSecondFundamentalForm_eq_of_mem_boundary (h₁ : IsSmoothBoundaryChart E U₁ F₁)
    (h₂ : IsSmoothBoundaryChart E U₂ F₂) (hy₁ : y ∈ U₁) (hy₂ : y ∈ U₂)
    (hyB : y ∈ measureTheoreticBoundary E) :
    sqNormSecondFundamentalForm F₂ y = sqNormSecondFundamentalForm F₁ y := by
  unfold sqNormSecondFundamentalForm
  rw [h₁.secondFundamentalForm_eq_of_mem_boundary h₂ hy₁ hy₂ hyB]

theorem tangentialGradient_inner_chartNormal_eq_of_mem_boundary
    (h₁ : IsSmoothBoundaryChart E U₁ F₁) (h₂ : IsSmoothBoundaryChart E U₂ F₂) (hy₁ : y ∈ U₁)
    (hy₂ : y ∈ U₂) (hyB : y ∈ measureTheoreticBoundary E) (e : Space d) :
    tangentialGradient F₂ (fun z ↦ inner ℝ (chartNormal F₂ z) e) y =
      tangentialGradient F₁ (fun z ↦ inner ℝ (chartNormal F₁ z) e) y := by
  rw [h₂.tangentialGradient_inner_chartNormal hy₂ e, h₁.tangentialGradient_inner_chartNormal hy₁ e,
    h₁.secondFundamentalForm_eq_of_mem_boundary h₂ hy₁ hy₂ hyB]

end IsSmoothBoundaryChart

/-! ### 4. Pointwise bounds -/

namespace IsSmoothBoundaryChart

variable {d : ℕ} {E U : Set (Space d)} {F : Space d → ℝ} {y : Space d}

/-- The operator norm of `A` is bounded by its Hilbert-Schmidt norm. -/
theorem norm_sq_secondFundamentalForm_apply_le (h : IsSmoothBoundaryChart E U F) (hy : y ∈ U)
    (v : Space d) :
    ‖secondFundamentalForm F y v‖ ^ 2 ≤ sqNormSecondFundamentalForm F y * ‖v‖ ^ 2 := by
  set b := EuclideanSpace.basisFun (Fin d) ℝ
  calc ‖secondFundamentalForm F y v‖ ^ 2
      = ∑ i, inner ℝ (b i) (secondFundamentalForm F y v) ^ 2 := norm_sq_eq_sum_inner_sq b _
    _ = ∑ i, inner ℝ (secondFundamentalForm F y (b i)) v ^ 2 := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [h.inner_secondFundamentalForm_comm hy]
    _ ≤ ∑ i, ‖secondFundamentalForm F y (b i)‖ ^ 2 * ‖v‖ ^ 2 := by
        refine Finset.sum_le_sum fun i _ ↦ ?_
        rw [← mul_pow, ← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm _ _) 2
    _ = sqNormSecondFundamentalForm F y * ‖v‖ ^ 2 := by
        rw [sqNormSecondFundamentalForm_eq_sum b, Finset.sum_mul]

/-- `‖δ ⟪ν, e⟫‖² ≤ |A|² ‖e‖²`. -/
theorem norm_sq_tangentialGradient_inner_chartNormal_le (h : IsSmoothBoundaryChart E U F)
    (hy : y ∈ U) (e : Space d) :
    ‖tangentialGradient F (fun z ↦ inner ℝ (chartNormal F z) e) y‖ ^ 2 ≤
      sqNormSecondFundamentalForm F y * ‖e‖ ^ 2 := by
  rw [h.tangentialGradient_inner_chartNormal hy e]
  exact h.norm_sq_secondFundamentalForm_apply_le hy e

theorem secondFundamentalForm_eq_zero_of_sqNorm_eq_zero (h : IsSmoothBoundaryChart E U F)
    (hy : y ∈ U) (hA : sqNormSecondFundamentalForm F y = 0) : secondFundamentalForm F y = 0 := by
  refine ContinuousLinearMap.ext fun v ↦ ?_
  have h1 := h.norm_sq_secondFundamentalForm_apply_le hy v
  rw [hA, zero_mul] at h1
  have h2 : ‖secondFundamentalForm F y v‖ ^ 2 = 0 := le_antisymm h1 (sq_nonneg _)
  exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h2)

/-- Tangential gradients are tangent. -/
theorem tangentialProj_tangentialGradient (h : IsSmoothBoundaryChart E U F) (hy : y ∈ U)
    (f : Space d → ℝ) :
    tangentialProj F y (tangentialGradient F f y) = tangentialGradient F f y :=
  tangentialProj_tangentialProj (h.gradient_ne_zero y hy) _

/-- The pairing of two tangential gradients is the derivative of the first along the second. -/
theorem inner_tangentialGradient_tangentialGradient_eq_fderiv (h : IsSmoothBoundaryChart E U F)
    (hy : y ∈ U) (f g : Space d → ℝ) :
    inner ℝ (tangentialGradient F f y) (tangentialGradient F g y) =
      fderiv ℝ f y (tangentialGradient F g y) := by
  rw [inner_tangentialGradient_eq_fderiv, h.tangentialProj_tangentialGradient hy]

end IsSmoothBoundaryChart

/-! ### 5. Cones -/

namespace IsSmoothBoundaryChart

variable {d : ℕ} {E U : Set (Space d)} {F : Space d → ℝ} {y : Space d}

/-- On a chart of a cone, the position vector is tangent: `DF(y) y = 0` at boundary points. -/
theorem fderiv_apply_self_eq_zero (h : IsSmoothBoundaryChart E U F)
    (hcone : ∀ x ∈ measureTheoreticBoundary E, ∀ a : ℝ, 0 < a →
      a • x ∈ measureTheoreticBoundary E)
    (hy : y ∈ U) (hFy : F y = 0) : fderiv ℝ F y y = 0 := by
  have hyB := h.mem_measureTheoreticBoundary hy hFy
  have hcurve : HasDerivAt (fun t : ℝ ↦ (1 + t) • y) y 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_add 1).smul_const y
  have h1 : HasFDerivAt F (fderiv ℝ F y) ((fun t : ℝ ↦ (1 + t) • y) 0) := by
    simpa using h.hasFDerivAt hy
  have hcomp : HasDerivAt (fun t : ℝ ↦ F ((1 + t) • y)) (fderiv ℝ F y y) 0 :=
    h1.comp_hasDerivAt (0 : ℝ) hcurve
  have hU : ∀ᶠ t in 𝓝 (0 : ℝ), (1 + t) • y ∈ U :=
    hcurve.continuousAt.preimage_mem_nhds (h.isOpen.mem_nhds (by simpa using hy))
  have hzero : (fun t : ℝ ↦ F ((1 + t) • y)) =ᶠ[𝓝 0] fun _ ↦ (0 : ℝ) := by
    filter_upwards [hU, Ioo_mem_nhds (show (-1 : ℝ) < 0 by norm_num)
      (show (0 : ℝ) < 1 by norm_num)] with t ht ht'
    exact h.eq_zero_of_mem_measureTheoreticBoundary ht (hcone y hyB _ (by linarith [ht'.1]))
  exact hcomp.unique ((hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq hzero)

/-- On a chart of a cone, the normal is orthogonal to the position vector. -/
theorem inner_chartNormal_self_eq_zero (h : IsSmoothBoundaryChart E U F)
    (hcone : ∀ x ∈ measureTheoreticBoundary E, ∀ a : ℝ, 0 < a →
      a • x ∈ measureTheoreticBoundary E)
    (hy : y ∈ U) (hFy : F y = 0) : inner ℝ (chartNormal F y) y = 0 := by
  rw [chartNormal, real_inner_smul_left, inner_gradient_left,
    h.fderiv_apply_self_eq_zero hcone hy hFy, mul_zero]

/-- On a chart of a cone, the shape operator annihilates the position vector: `Dν(y) y = 0`. -/
theorem fderiv_chartNormal_apply_self_eq_zero (h : IsSmoothBoundaryChart E U F)
    (hcone : ∀ x ∈ measureTheoreticBoundary E, ∀ a : ℝ, 0 < a →
      a • x ∈ measureTheoreticBoundary E)
    (hy : y ∈ U) (hFy : F y = 0) : fderiv ℝ (chartNormal F) y y = 0 := by
  have hne := h.gradient_ne_zero y hy
  have hfC : ContDiffOn ℝ 1 (fun z ↦ inner ℝ (chartNormal F z) z) U :=
    (h.contDiffOn_chartNormal.of_le (by simp)).inner ℝ contDiffOn_id
  have hzero : ∀ z ∈ U, F z = 0 → inner ℝ (chartNormal F z) z = 0 :=
    fun z hz hFz ↦ h.inner_chartNormal_self_eq_zero hcone hz hFz
  have htg := h.tangentialGradient_eq_zero_of_eq_zero_on_level hfC hzero hy hFy
  have hd : HasFDerivAt (fun z ↦ inner ℝ (chartNormal F z) z)
      ((fderivInnerCLM ℝ (chartNormal F y, y)).comp
        ((fderiv ℝ (chartNormal F) y).prod (ContinuousLinearMap.id ℝ (Space d)))) y :=
    (h.differentiableAt_chartNormal hy).hasFDerivAt.inner ℝ (hasFDerivAt_id y)
  have hPy : tangentialProj F y y = y :=
    tangentialProj_eq_self_of_inner_eq_zero (h.inner_chartNormal_self_eq_zero hcone hy hFy)
  refine ext_inner_left ℝ fun v ↦ ?_
  rw [inner_zero_right]
  have h1 := congrArg (fun w ↦ inner ℝ w v) htg
  simp only [inner_zero_left] at h1
  rw [inner_tangentialGradient_eq_fderiv, hd.fderiv] at h1
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    fderivInnerCLM_apply, ContinuousLinearMap.id_apply] at h1
  have h2 := h.inner_fderiv_chartNormal_tangentialProj_comm hy v y
  rw [hPy] at h2
  rw [inner_chartNormal_tangentialProj hne, zero_add, h2, inner_tangentialProj_left,
    h.tangentialProj_fderiv_chartNormal hy] at h1
  exact h1

/-- On a chart of a cone, `⟪δ ⟪ν, e⟫ (y), y⟫ = 0` at boundary points. -/
theorem inner_tangentialGradient_inner_chartNormal_self (h : IsSmoothBoundaryChart E U F)
    (hcone : ∀ x ∈ measureTheoreticBoundary E, ∀ a : ℝ, 0 < a →
      a • x ∈ measureTheoreticBoundary E)
    (hy : y ∈ U) (hFy : F y = 0) (e : Space d) :
    inner ℝ (tangentialGradient F (fun z ↦ inner ℝ (chartNormal F z) e) y) y = 0 := by
  rw [h.tangentialGradient_inner_chartNormal hy e, h.inner_secondFundamentalForm_comm hy,
    h.secondFundamentalForm_apply hy,
    tangentialProj_eq_self_of_inner_eq_zero (h.inner_chartNormal_self_eq_zero hcone hy hFy),
    h.fderiv_chartNormal_apply_self_eq_zero hcone hy hFy, inner_zero_right]

end IsSmoothBoundaryChart

/-! ### 6. Monotone sets -/

namespace IsSmoothBoundaryChart

variable {d : ℕ} {E U : Set (Space d)} {F : Space d → ℝ} {y : Space d}

/-- **Monotonicity makes the normal point along the direction of monotonicity.** If
`x ∈ E ⇒ x + t v ∈ E` a.e. for every `t ≥ 0`, then `DF(y) v ≥ 0` at every boundary point of a
chart. -/
theorem fderiv_apply_nonneg_of_monotone (h : IsSmoothBoundaryChart E U F) {v : Space d}
    (hmono : ∀ t : ℝ, 0 ≤ t → ∀ᵐ x ∂volume, x ∈ E → x + t • v ∈ E) (hy : y ∈ U)
    (hFy : F y = 0) : 0 ≤ fderiv ℝ F y v := by
  by_contra hneg
  have hneg' : fderiv ℝ F y v < 0 := not_le.mp hneg
  have hd₁ : 0 < fderiv ℝ F y (-v) := by rw [map_neg]; linarith
  have hd₂ : 0 < fderiv ℝ (fun z ↦ -F z) y v := by
    rw [fderiv_fun_neg, neg_apply]; linarith
  have hF₂ : HasFDerivAt (fun z ↦ -F z) (fderiv ℝ (fun z ↦ -F z) y) y :=
    (h.hasFDerivAt hy).fun_neg.differentiableAt.hasFDerivAt
  obtain ⟨n, hn₁, hn₂, hn₃, hn₄⟩ :=
    ((eventually_pos_of_hasFDerivAt_aux (h.hasFDerivAt hy) hFy hd₁).and
      ((eventually_pos_of_hasFDerivAt_aux hF₂ (by simp [hFy]) hd₂).and
        (((tendsto_add_inv_smul_aux y (-v)).eventually (h.isOpen.mem_nhds hy)).and
          ((tendsto_add_inv_smul_aux y v).eventually (h.isOpen.mem_nhds hy))))).exists
  set s : ℝ := ((n : ℝ) + 1)⁻¹ with hs
  have hs0 : 0 ≤ 2 * s := by positivity
  have hb : F (y + s • v) < 0 := by simpa using hn₂
  have hab : y + s • v = (y + s • (-v)) + (2 * s) • v := by
    rw [smul_neg, two_mul, add_smul]
    abel
  have hca : ContinuousAt F (y + s • (-v)) :=
    h.continuousOn.continuousAt (h.isOpen.mem_nhds hn₃)
  have hcb : ContinuousAt F (y + s • v) := h.continuousOn.continuousAt (h.isOpen.mem_nhds hn₄)
  obtain ⟨δ, hδ, hδa⟩ := Metric.eventually_nhds_iff_ball.mp
    ((hca.eventually (lt_mem_nhds hn₁)).and (h.isOpen.mem_nhds hn₃))
  obtain ⟨δ', hδ', hδb⟩ := Metric.eventually_nhds_iff_ball.mp
    ((hcb.eventually (gt_mem_nhds hb)).and (h.isOpen.mem_nhds hn₄))
  have htr : ∀ᵐ z ∂volume, z + (2 * s) • v ∈ U →
      (z + (2 * s) • v ∈ E ↔ 0 < F (z + (2 * s) • v)) :=
    (measurePreserving_add_right volume ((2 * s) • v)).quasiMeasurePreserving.ae
      h.ae_mem_iff_of_mem
  have hnull : volume (ball (y + s • (-v)) (min δ δ')) = 0 := by
    refine measure_mono_null (fun z hz ↦ ?_)
      (ae_iff.mp ((h.ae_mem_iff_of_mem.and (hmono (2 * s) hs0)).and htr))
    intro hz'
    have hzδ : z ∈ ball (y + s • (-v)) δ := ball_subset_ball (min_le_left _ _) hz
    have hzδ' : z + (2 * s) • v ∈ ball (y + s • v) δ' := by
      rw [hab, mem_ball, dist_add_right]
      exact ball_subset_ball (min_le_right _ _) hz
    have hzE : z ∈ E := (hz'.1.1 (hδa z hzδ).2).mpr (hδa z hzδ).1
    have h1 := (hz'.2 (hδb _ hzδ').2).mp (hz'.1.2 hzE)
    have h2 := (hδb _ hzδ').1
    linarith
  exact (Metric.measure_ball_pos volume _ (lt_min hδ hδ')).ne' hnull

/-- The normal of a chart of a monotone set has nonnegative component along the direction of
monotonicity. -/
theorem inner_chartNormal_nonneg_of_monotone (h : IsSmoothBoundaryChart E U F) {v : Space d}
    (hmono : ∀ t : ℝ, 0 ≤ t → ∀ᵐ x ∂volume, x ∈ E → x + t • v ∈ E) (hy : y ∈ U)
    (hFy : F y = 0) : 0 ≤ inner ℝ (chartNormal F y) v := by
  rw [chartNormal, real_inner_smul_left, inner_gradient_left]
  exact mul_nonneg (inv_nonneg.mpr (norm_nonneg _))
    (h.fderiv_apply_nonneg_of_monotone hmono hy hFy)

end IsSmoothBoundaryChart

/-! ### 7. Constancy along level sets and flat pieces -/

section Constancy

variable {d : ℕ}

private theorem exists_smul_of_ker_le_aux {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (ℓ : Space d →L[ℝ] ℝ) (L : Space d →L[ℝ] G) (h : ∀ v, ℓ v = 0 → L v = 0) :
    ∃ c : G, ∀ v, L v = ℓ v • c := by
  by_cases hℓ : ∃ u, ℓ u ≠ 0
  · obtain ⟨u, hu⟩ := hℓ
    refine ⟨(ℓ u)⁻¹ • L u, fun v ↦ ?_⟩
    have hker : ℓ (v - (ℓ v / ℓ u) • u) = 0 := by
      rw [map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hu, sub_self]
    have h1 := h _ hker
    rw [map_sub, map_smul, sub_eq_zero] at h1
    rw [h1, smul_smul, div_eq_mul_inv]
  · simp only [not_exists, not_not] at hℓ
    exact ⟨0, fun v ↦ by rw [smul_zero]; exact h v (hℓ v)⟩

/-- A function with zero derivative at `γ t`, composed with a curve which is Lipschitz at `t`, has
zero derivative at `t`. -/
private theorem hasDerivAt_comp_of_hasFDerivAt_zero_aux {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] {φ : Space d → G} {γ : ℝ → Space d} {t C : ℝ}
    (hφ : HasFDerivAt φ (0 : Space d →L[ℝ] G) (γ t))
    (hγ : ∀ᶠ s in 𝓝 t, ‖γ s - γ t‖ ≤ C * ‖s - t‖) :
    HasDerivAt (fun s ↦ φ (γ s)) 0 t := by
  have hγc : Tendsto γ (𝓝 t) (𝓝 (γ t)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun s ↦ norm_nonneg _) hγ ?_
    have : Tendsto (fun s ↦ C * ‖s - t‖) (𝓝 t) (𝓝 (C * ‖t - t‖)) :=
      (continuous_const.mul (continuous_id.sub continuous_const).norm).tendsto t
    simpa using this
  have h1 := hφ.isLittleO.comp_tendsto hγc
  have h2 : (fun s ↦ γ s - γ t) =O[𝓝 t] (fun s ↦ s - t) :=
    Asymptotics.IsBigO.of_bound C (by filter_upwards [hγ] with s hs; simpa using hs)
  rw [hasDerivAt_iff_isLittleO]
  refine (h1.trans_isBigO h2).congr_left fun s ↦ ?_
  simp

/-- **Constancy along a level set.** Let `F` be `C¹` on `U` with `F y = 0` and `∇F(y) ≠ 0`, and let
`f` be differentiable on `U`, with `Df(z)` vanishing on `ker DF(z)` at every point `z` of the level
set `U ∩ {F = 0}`. Then `f` is constant on the level set near `y`. The proof straightens the level
set with the inverse function theorem and integrates along segments of the straightened level
set. -/
theorem exists_forall_eq_of_fderiv_eq_zero_on_level {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] {F : Space d → ℝ} {f : Space d → G} {U : Set (Space d)} (hU : IsOpen U)
    (hF : ContDiffOn ℝ 1 F U) (hf : DifferentiableOn ℝ f U) {y : Space d} (hyU : y ∈ U)
    (hy : F y = 0) (hne : gradient F y ≠ 0)
    (hker : ∀ z ∈ U, F z = 0 → ∀ v, fderiv ℝ F z v = 0 → fderiv ℝ f z v = 0) :
    ∃ r > 0, ∀ z ∈ ball y r, F z = 0 → f z = f y := by
  set g := gradient F y with hg
  have hg2 : ‖g‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hne)
  have hFs : HasStrictFDerivAt F (fderiv ℝ F y) y :=
    (hF.contDiffAt (hU.mem_nhds hyU)).hasStrictFDerivAt one_ne_zero
  -- the correction term has vanishing strict derivative at `y`
  have hlin : HasStrictFDerivAt (fun z ↦ F z - inner ℝ g z) (0 : Space d →L[ℝ] ℝ) y := by
    have h1 := hFs.sub (innerSL ℝ g).hasStrictFDerivAt
    have h2 : fderiv ℝ F y - innerSL ℝ g = 0 := by
      ext v
      simp [hg, inner_gradient_left]
    rw [h2] at h1
    exact h1.congr_of_eventuallyEq (Eventually.of_forall fun z ↦ by simp)
  -- the straightening map `Ψ`, with `DΨ(y) = id` and `⟪g, Ψ z⟫ = F z`
  set g' : Space d := (‖g‖ ^ 2)⁻¹ • g with hg'
  set Ψ : Space d → Space d := fun z ↦ (z - y) + (F z - inner ℝ g z + inner ℝ g y) • g' with hΨ
  have hΨs : HasStrictFDerivAt Ψ (ContinuousLinearMap.id ℝ (Space d)) y := by
    have h1 := ((hasStrictFDerivAt_id y).sub_const y).add
      ((hlin.add_const (inner ℝ g y)).smul_const g')
    have h2 : ContinuousLinearMap.id ℝ (Space d) + (0 : Space d →L[ℝ] ℝ).smulRight g' =
        ContinuousLinearMap.id ℝ (Space d) := by
      ext v
      simp
    rw [h2] at h1
    exact h1
  have hΨy : Ψ y = 0 := by simp [hΨ, hy]
  have hgg' : inner ℝ g g' = 1 := by
    rw [hg', real_inner_smul_right, real_inner_self_eq_norm_sq, inv_mul_cancel₀ hg2]
  have hgΨ : ∀ z, inner ℝ g (Ψ z) = F z := by
    intro z
    simp only [hΨ, inner_add_right, inner_sub_right, real_inner_smul_right, hgg']
    ring
  -- `Ψ` is bi-Lipschitz near `y`
  obtain ⟨s, hs, hsA⟩ :=
    hΨs.approximates_deriv_on_nhds (c := (1 / 2 : ℝ≥0)) (Or.inr (by norm_num))
  obtain ⟨ρ₀, hρ₀, hρ₀s⟩ := Metric.mem_nhds_iff.mp (inter_mem hs (hU.mem_nhds hyU))
  have hest : ∀ x ∈ ball y ρ₀, ∀ x' ∈ ball y ρ₀,
      ‖Ψ x - Ψ x' - (x - x')‖ ≤ 1 / 2 * ‖x - x'‖ := by
    intro x hx x' hx'
    have h1 := hsA x (hρ₀s hx).1 x' (hρ₀s hx').1
    simpa using h1
  have hlow : ∀ x ∈ ball y ρ₀, ∀ x' ∈ ball y ρ₀, ‖x - x'‖ ≤ 2 * ‖Ψ x - Ψ x'‖ := by
    intro x hx x' hx'
    have h1 := hest x hx x' hx'
    have h2 : ‖x - x'‖ ≤ ‖Ψ x - Ψ x'‖ + ‖Ψ x - Ψ x' - (x - x')‖ := by
      calc ‖x - x'‖ = ‖(Ψ x - Ψ x') - (Ψ x - Ψ x' - (x - x'))‖ := by congr 1; abel
        _ ≤ _ := norm_sub_le _ _
    linarith
  have hup : ∀ x ∈ ball y ρ₀, ‖Ψ x‖ ≤ 2 * ‖x - y‖ := by
    intro x hx
    have h1 := hest x hx y (mem_ball_self hρ₀)
    rw [hΨy, sub_zero] at h1
    have h2 : ‖Ψ x‖ ≤ ‖x - y‖ + ‖Ψ x - (x - y)‖ := by
      calc ‖Ψ x‖ = ‖(x - y) + (Ψ x - (x - y))‖ := by congr 1; abel
        _ ≤ _ := norm_add_le _ _
    nlinarith [norm_nonneg (x - y)]
  have hinj : ∀ x ∈ ball y ρ₀, ∀ x' ∈ ball y ρ₀, Ψ x = Ψ x' → x = x' := by
    intro x hx x' hx' hxx'
    have h1 := hlow x hx x' hx'
    rw [hxx', sub_self, norm_zero, mul_zero] at h1
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h1)
  -- `Ψ` maps the ball onto a neighbourhood of `0`
  have hΨs' : HasStrictFDerivAt Ψ
      ((ContinuousLinearEquiv.refl ℝ (Space d) : Space d ≃L[ℝ] Space d) : Space d →L[ℝ] Space d)
      y := by
    simpa using hΨs
  have himg : Ψ '' ball y ρ₀ ∈ 𝓝 (Ψ y) := by
    rw [← hΨs'.map_nhds_eq_of_equiv]
    exact image_mem_map (ball_mem_nhds y hρ₀)
  rw [hΨy] at himg
  obtain ⟨ρ₁, hρ₁, hρ₁sub⟩ := Metric.mem_nhds_iff.mp himg
  refine ⟨min ρ₀ (ρ₁ / 4), lt_min hρ₀ (by positivity), fun z hz hFz ↦ ?_⟩
  have hzρ₀ : z ∈ ball y ρ₀ := ball_subset_ball (min_le_left _ _) hz
  have hzr : ‖z - y‖ < ρ₁ / 4 := by
    have h1 := mem_ball.mp hz
    rw [dist_eq_norm] at h1
    exact lt_of_lt_of_le h1 (min_le_right _ _)
  set q := Ψ z with hq
  have hqn : ‖q‖ < ρ₁ / 2 := by
    have := hup z hzρ₀
    linarith
  have hgq : inner ℝ g q = 0 := by rw [hq, hgΨ, hFz]
  -- the path `γ τ = Ψ⁻¹ (τ q)` in the level set
  have hmem : ∀ τ : ℝ, |τ| < 2 → τ • q ∈ Ψ '' ball y ρ₀ := by
    intro τ hτ
    apply hρ₁sub
    rw [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs]
    calc |τ| * ‖q‖ ≤ 2 * ‖q‖ := mul_le_mul_of_nonneg_right hτ.le (norm_nonneg _)
      _ < ρ₁ := by linarith
  set γ : ℝ → Space d := fun τ ↦ Function.invFunOn Ψ (ball y ρ₀) (τ • q) with hγ
  have hγmem : ∀ τ : ℝ, |τ| < 2 → γ τ ∈ ball y ρ₀ := fun τ hτ ↦
    Function.invFunOn_mem (hmem τ hτ)
  have hγΨ : ∀ τ : ℝ, |τ| < 2 → Ψ (γ τ) = τ • q := fun τ hτ ↦
    Function.invFunOn_eq (hmem τ hτ)
  have hγF : ∀ τ : ℝ, |τ| < 2 → F (γ τ) = 0 := by
    intro τ hτ
    rw [← hgΨ, hγΨ τ hτ, real_inner_smul_right, hgq, mul_zero]
  have hγlip : ∀ τ τ' : ℝ, |τ| < 2 → |τ'| < 2 → ‖γ τ' - γ τ‖ ≤ (2 * ‖q‖) * ‖τ' - τ‖ := by
    intro τ τ' hτ hτ'
    calc ‖γ τ' - γ τ‖ ≤ 2 * ‖Ψ (γ τ') - Ψ (γ τ)‖ := hlow _ (hγmem τ' hτ') _ (hγmem τ hτ)
      _ = 2 * ‖(τ' - τ) • q‖ := by rw [hγΨ τ' hτ', hγΨ τ hτ, sub_smul]
      _ = (2 * ‖q‖) * ‖τ' - τ‖ := by rw [norm_smul]; ring
  have hγ1 : γ 1 = z :=
    hinj _ (hγmem 1 (by norm_num)) _ hzρ₀ (by rw [hγΨ 1 (by norm_num), one_smul])
  have hγ0 : γ 0 = y :=
    hinj _ (hγmem 0 (by norm_num)) _ (mem_ball_self hρ₀)
      (by rw [hγΨ 0 (by norm_num), zero_smul, hΨy])
  -- `f ∘ γ` has zero derivative
  have hderiv : ∀ τ : ℝ, |τ| < 2 → HasDerivAt (fun τ ↦ f (γ τ)) 0 τ := by
    intro τ hτ
    have hzτU : γ τ ∈ U := (hρ₀s (hγmem τ hτ)).2
    have hFd : HasFDerivAt F (fderiv ℝ F (γ τ)) (γ τ) :=
      ((hF.contDiffAt (hU.mem_nhds hzτU)).differentiableAt one_ne_zero).hasFDerivAt
    have hfd : HasFDerivAt f (fderiv ℝ f (γ τ)) (γ τ) :=
      (hf.differentiableAt (hU.mem_nhds hzτU)).hasFDerivAt
    obtain ⟨c, hc⟩ := exists_smul_of_ker_le_aux (fderiv ℝ F (γ τ)) (fderiv ℝ f (γ τ))
      (hker _ hzτU (hγF τ hτ))
    have hφd : HasFDerivAt (fun x ↦ f x - F x • c) (0 : Space d →L[ℝ] G) (γ τ) := by
      have h1 := hfd.fun_sub (hFd.smul_const c)
      have h2 : fderiv ℝ f (γ τ) - (fderiv ℝ F (γ τ)).smulRight c = 0 := by
        ext v
        simp [hc v]
      rwa [h2] at h1
    have hnhds : ∀ᶠ τ' in 𝓝 τ, |τ'| < 2 :=
      (continuous_abs.tendsto τ).eventually (gt_mem_nhds hτ)
    have hlip : ∀ᶠ τ' in 𝓝 τ, ‖γ τ' - γ τ‖ ≤ (2 * ‖q‖) * ‖τ' - τ‖ := by
      filter_upwards [hnhds] with τ' hτ'
      exact hγlip τ τ' hτ hτ'
    have h3 := hasDerivAt_comp_of_hasFDerivAt_zero_aux hφd hlip
    refine h3.congr_of_eventuallyEq ?_
    filter_upwards [hnhds] with τ' hτ'
    simp [hγF τ' hτ']
  have hτ2 : ∀ τ ∈ Icc (0 : ℝ) 1, |τ| < 2 := fun τ hτ ↦ by
    rw [abs_lt]
    constructor <;> linarith [hτ.1, hτ.2]
  have hconst := constant_of_has_deriv_right_zero (f := fun τ ↦ f (γ τ)) (a := 0) (b := 1)
    (fun τ hτ ↦ (hderiv τ (hτ2 τ hτ)).continuousAt.continuousWithinAt)
    (fun τ hτ ↦ (hderiv τ (hτ2 τ (Ico_subset_Icc_self hτ))).hasDerivWithinAt)
    1 ⟨zero_le_one, le_rfl⟩
  simp only [hγ1, hγ0] at hconst
  exact hconst

end Constancy

namespace IsSmoothBoundaryChart

variable {d : ℕ} {E U : Set (Space d)} {F : Space d → ℝ} {y : Space d}

/-- **Flat pieces.** If the second fundamental form vanishes on the level set of a chart, then
near each level point `y`, the sign of `F` is the sign of `⟪ν(y), · - y⟫`. -/
theorem exists_ball_pos_iff_of_sqNorm_eq_zero (h : IsSmoothBoundaryChart E U F)
    (hA : ∀ z ∈ U, F z = 0 → sqNormSecondFundamentalForm F z = 0) (hy : y ∈ U)
    (hFy : F y = 0) :
    ∃ r > 0, ball y r ⊆ U ∧
      ∀ z ∈ ball y r, (0 < F z ↔ 0 < inner ℝ (chartNormal F y) (z - y)) := by
  set ν₀ := chartNormal F y with hν₀
  have hne := h.gradient_ne_zero y hy
  have hν₀n : ‖ν₀‖ = 1 := norm_chartNormal hne
  -- vectors in the kernel of `DF(z)` are tangent and killed by `Dν(z)`
  have hker_tan : ∀ z ∈ U, ∀ v, fderiv ℝ F z v = 0 → tangentialProj F z v = v := by
    intro z _ v hv
    apply tangentialProj_eq_self_of_inner_eq_zero
    rw [chartNormal, real_inner_smul_left, inner_gradient_left, hv, mul_zero]
  have hDν : ∀ z ∈ U, F z = 0 → ∀ v, fderiv ℝ F z v = 0 →
      fderiv ℝ (chartNormal F) z v = 0 := by
    intro z hz hFz v hv
    rw [← hker_tan z hz v hv, ← h.secondFundamentalForm_apply hz,
      h.secondFundamentalForm_eq_zero_of_sqNorm_eq_zero hz (hA z hz hFz)]
    rfl
  -- the normal is constant on the level set near `y`
  obtain ⟨r₁, hr₁, hν⟩ := exists_forall_eq_of_fderiv_eq_zero_on_level h.isOpen h.contDiffOn_one
    (h.contDiffOn_chartNormal.differentiableOn (by simp)) hy hFy hne hDν
  -- the level set lies in the tangent hyperplane near `y`
  have hf₂d : ∀ z ∈ U, HasFDerivAt (fun x ↦ inner ℝ (chartNormal F x) (x - y))
      ((fderivInnerCLM ℝ (chartNormal F z, z - y)).comp
        ((fderiv ℝ (chartNormal F) z).prod (ContinuousLinearMap.id ℝ (Space d)))) z :=
    fun z hz ↦ (h.differentiableAt_chartNormal hz).hasFDerivAt.inner ℝ
      ((hasFDerivAt_id z).sub_const y)
  obtain ⟨r₂, hr₂, hplane⟩ := exists_forall_eq_of_fderiv_eq_zero_on_level h.isOpen
    h.contDiffOn_one (fun z hz ↦ (hf₂d z hz).differentiableAt.differentiableWithinAt) hy hFy hne
    (fun z hz hFz v hv ↦ by
      rw [(hf₂d z hz).fderiv]
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
        fderivInnerCLM_apply, ContinuousLinearMap.id_apply]
      rw [hDν z hz hFz v hv, inner_zero_left, add_zero, chartNormal, real_inner_smul_left,
        inner_gradient_left, hv, mul_zero])
  obtain ⟨ρ, hρ, hρU⟩ := Metric.isOpen_iff.mp h.isOpen y hy
  set r := min ρ (min r₁ r₂) with hr
  have hr0 : 0 < r := lt_min hρ (lt_min hr₁ hr₂)
  have hrU : ball y r ⊆ U := (ball_subset_ball (min_le_left _ _)).trans hρU
  have hplane' : ∀ w ∈ ball y r, F w = 0 → inner ℝ ν₀ w = inner ℝ ν₀ y := by
    intro w hw hFw
    have hw₁ : w ∈ ball y r₁ :=
      ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _)) hw
    have hw₂ : w ∈ ball y r₂ :=
      ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _)) hw
    have h1 := hplane w hw₂ hFw
    rw [sub_self, inner_zero_right, hν w hw₁ hFw, inner_sub_right, sub_eq_zero] at h1
    exact h1
  have hDFν₀ : 0 < fderiv ℝ F y ν₀ := by
    rw [← inner_gradient_left, real_inner_comm, hν₀, inner_chartNormal_gradient]
    exact norm_pos_iff.mpr hne
  have hlinear : IsLinearMap ℝ (fun w : Space d ↦ inner ℝ ν₀ w) :=
    ⟨fun a b ↦ inner_add_right _ _ _, fun c a ↦ by rw [real_inner_smul_right, smul_eq_mul]⟩
  have hBp : IsPreconnected (ball y r ∩ {w | inner ℝ ν₀ y < inner ℝ ν₀ w}) :=
    ((convex_ball y r).inter (convex_halfSpace_gt hlinear _)).isPreconnected
  have hBm : IsPreconnected (ball y r ∩ {w | inner ℝ ν₀ w < inner ℝ ν₀ y}) :=
    ((convex_ball y r).inter (convex_halfSpace_lt hlinear _)).isPreconnected
  have hFcont : ContinuousOn F (ball y r) := h.continuousOn.mono hrU
  -- the positive side
  obtain ⟨n, hn₁, hn₂⟩ := ((eventually_pos_of_hasFDerivAt_aux (h.hasFDerivAt hy) hFy hDFν₀).and
    ((tendsto_add_inv_smul_aux y ν₀).eventually (ball_mem_nhds y hr0))).exists
  have hpos_side : ∀ w ∈ ball y r, inner ℝ ν₀ y < inner ℝ ν₀ w → 0 < F w := by
    intro w hw hwν
    by_contra hle
    have hmemBp : y + ((n : ℝ) + 1)⁻¹ • ν₀ ∈ ball y r ∩ {w | inner ℝ ν₀ y < inner ℝ ν₀ w} := by
      refine ⟨hn₂, ?_⟩
      show inner ℝ ν₀ y < inner ℝ ν₀ (y + ((n : ℝ) + 1)⁻¹ • ν₀)
      rw [inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hν₀n]
      have : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := by positivity
      nlinarith
    obtain ⟨u, hu, hu0⟩ := hBp.intermediate_value ⟨hw, hwν⟩ hmemBp
      (hFcont.mono inter_subset_left) ⟨not_lt.mp hle, hn₁.le⟩
    have h1 := hplane' u hu.1 hu0
    have h2 : inner ℝ ν₀ y < inner ℝ ν₀ u := hu.2
    linarith
  -- the negative side
  have hDFν₀' : 0 < fderiv ℝ (fun x ↦ -F x) y (-ν₀) := by
    rw [fderiv_fun_neg, neg_apply, map_neg, neg_neg]
    exact hDFν₀
  have hFn : HasFDerivAt (fun x ↦ -F x) (fderiv ℝ (fun x ↦ -F x) y) y :=
    (h.hasFDerivAt hy).fun_neg.differentiableAt.hasFDerivAt
  obtain ⟨n', hn₁', hn₂'⟩ := ((eventually_pos_of_hasFDerivAt_aux hFn (by simp [hFy])
    hDFν₀').and ((tendsto_add_inv_smul_aux y (-ν₀)).eventually (ball_mem_nhds y hr0))).exists
  have hneg_side : ∀ w ∈ ball y r, inner ℝ ν₀ w < inner ℝ ν₀ y → F w < 0 := by
    intro w hw hwν
    by_contra hle
    have hmemBm : y + ((n' : ℝ) + 1)⁻¹ • (-ν₀) ∈
        ball y r ∩ {w | inner ℝ ν₀ w < inner ℝ ν₀ y} := by
      refine ⟨hn₂', ?_⟩
      show inner ℝ ν₀ (y + ((n' : ℝ) + 1)⁻¹ • (-ν₀)) < inner ℝ ν₀ y
      rw [inner_add_right, real_inner_smul_right, inner_neg_right, real_inner_self_eq_norm_sq,
        hν₀n]
      have : (0 : ℝ) < ((n' : ℝ) + 1)⁻¹ := by positivity
      nlinarith
    obtain ⟨u, hu, hu0⟩ := hBm.intermediate_value ⟨hw, hwν⟩ hmemBm
      (hFcont.neg.mono inter_subset_left) ⟨by rw [Pi.neg_apply]; linarith [not_lt.mp hle], hn₁'.le⟩
    have hFu : F u = 0 := by simpa using hu0
    have h1 := hplane' u hu.1 hFu
    have h2 : inner ℝ ν₀ u < inner ℝ ν₀ y := hu.2
    linarith
  -- points of the hyperplane
  have hzero_side : ∀ w ∈ ball y r, inner ℝ ν₀ w = inner ℝ ν₀ y → F w ≤ 0 := by
    intro w hw hwν
    have hcw : ContinuousAt F w := h.continuousOn.continuousAt (h.isOpen.mem_nhds (hrU hw))
    have hlim : Tendsto (fun k : ℕ ↦ F (w + ((k : ℝ) + 1)⁻¹ • (-ν₀))) atTop (𝓝 (F w)) :=
      hcw.tendsto.comp (tendsto_add_inv_smul_aux w (-ν₀))
    refine le_of_tendsto hlim ?_
    filter_upwards [(tendsto_add_inv_smul_aux w (-ν₀)).eventually (isOpen_ball.mem_nhds hw)]
      with k hk
    refine (hneg_side _ hk ?_).le
    rw [inner_add_right, real_inner_smul_right, inner_neg_right, real_inner_self_eq_norm_sq,
      hν₀n, hwν]
    have : (0 : ℝ) < ((k : ℝ) + 1)⁻¹ := by positivity
    nlinarith
  refine ⟨r, hr0, hrU, fun z hz ↦ ?_⟩
  rw [inner_sub_right, sub_pos]
  constructor
  · intro hFz
    by_contra hle
    rcases (not_lt.mp hle).lt_or_eq with hlt | heq
    · exact absurd hFz (not_lt.mpr (hneg_side z hz hlt).le)
    · exact absurd hFz (not_lt.mpr (hzero_side z hz heq))
  · exact hpos_side z hz

/-- **Local flatness.** If the second fundamental form vanishes on the level set of a chart, then
near each boundary point `y` of the chart, `E` is a.e. the half-space bounded by the tangent
hyperplane at `y`, on the side of the normal. -/
theorem exists_ae_eq_halfspace_of_sqNorm_eq_zero (h : IsSmoothBoundaryChart E U F)
    (hA : ∀ z ∈ U, F z = 0 → sqNormSecondFundamentalForm F z = 0) (hy : y ∈ U)
    (hFy : F y = 0) :
    ∃ r > 0, ∀ᵐ z ∂volume, z ∈ ball y r → (z ∈ E ↔ 0 < inner ℝ (chartNormal F y) (z - y)) := by
  obtain ⟨r, hr, hrU, hsign⟩ := h.exists_ball_pos_iff_of_sqNorm_eq_zero hA hy hFy
  refine ⟨r, hr, ?_⟩
  filter_upwards [h.ae_mem_iff_of_mem] with z hz hzB
  rw [hz (hrU hzB), hsign z hzB]

end IsSmoothBoundaryChart

end SerrinEpigraph
