module

public import SerrinEpigraph.SimonsConeVanishing
public import SerrinEpigraph.ExcessPhaseBand
public import SerrinEpigraph.SingularCutoff

/-!
# Simons' theorem for regular minimizing cones (GR1–GR4)

A minimizing cone `T ⊆ ℝᵏ`, `3 ≤ k ≤ 7`, whose boundary points other than the vertex lie in smooth
boundary charts is a.e. a half-space (`Simons.ae_eq_positiveHalfspace_of_regular_cone`). Relative to
the Schauder regularity hypothesis `C1RegularSmoothHyp`, this discharges `SimonsHyp k` for
`3 ≤ k ≤ 7` (`simonsHyp_of_smooth_of_three_le`).

Proof. By `Simons.secondFundamentalForm_eq_zero_of_cone` the second fundamental form vanishes at
every nonzero boundary point. Hence near such a point `w` the cone is the half-space bounded by the
tangent hyperplane `ν(w)^⊥`, which passes through the vertex (`Simons.flat_near`). A clopen
argument in the connected set `ν(w)^⊥ \ {0}` (`k ≥ 3`) shows that the whole punctured hyperplane
consists of boundary points with normal `ν(w)` (`Simons.hyperplane_subset`). Two such hyperplanes
meet in a nonzero point, where the normal is unique, so they coincide: the boundary lies in one
hyperplane, and the two open half-spaces are a.e. inside and outside `T`.

The case `k = 2` is not covered: in the plane every minimal cone with regular rays has vanishing
curvature, and the argument above (which uses `k ≥ 3`) does not exclude several rays; there minimality
must be used through a topology changing comparison (the chord argument at the end of GR4).
`simonsHyp_of_smooth_of_simonsHyp_two` records the reduction of the range `2 ≤ k ≤ 7` to that case.
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory InnerProductSpace Filter
open scoped Topology ContDiff ENNReal

namespace SerrinEpigraph

namespace Simons

variable {d : ℕ}

/-- Every smooth chart of `T` at `w` has unit normal `n` at `w`. -/
def HasNormal (T : Set (Space d)) (w n : Space d) : Prop :=
  ∀ (U : Set (Space d)) (F : Space d → ℝ), IsSmoothBoundaryChart T U F → w ∈ U →
    chartNormal F w = n

theorem hasNormal_of_chart {T U : Set (Space d)} {F : Space d → ℝ}
    (h : IsSmoothBoundaryChart T U F) {w : Space d} (hwU : w ∈ U)
    (hwB : w ∈ measureTheoreticBoundary T) : HasNormal T w (chartNormal F w) :=
  fun _ _ h₂ hw₂ ↦ h.chartNormal_eq_of_mem_boundary h₂ hwU hw₂ hwB

private theorem tendsto_add_smul_nhdsGT_aux (y v : Space d) :
    Tendsto (fun t : ℝ ↦ y + t • v) (𝓝[>] 0) (𝓝 y) := by
  have h : Tendsto (fun t : ℝ ↦ y + t • v) (𝓝 0) (𝓝 (y + (0 : ℝ) • v)) :=
    (continuous_const.add (continuous_id.smul continuous_const)).tendsto 0
  rw [zero_smul, add_zero] at h
  exact h.mono_left nhdsWithin_le_nhds

private theorem eventually_pos_along_aux {f : Space d → ℝ} {y v : Space d}
    (hf : DifferentiableAt ℝ f y) (hfy : f y = 0) (hv : 0 < fderiv ℝ f y v) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < f (y + t • v) := by
  have h1 : HasDerivAt (fun t : ℝ ↦ y + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add y
  have hg : HasDerivAt (fun t : ℝ ↦ f (y + t • v)) (fderiv ℝ f y v) 0 := by
    have h2 := hf.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) h1 (by simp)
    simpa [Function.comp_def] using h2
  filter_upwards [hg.tendsto_slope_zero_right.eventually (lt_mem_nhds hv), self_mem_nhdsWithin]
    with t ht htpos
  simp only [zero_add, zero_smul, add_zero, hfy, sub_zero, smul_eq_mul] at ht
  exact pos_of_mul_pos_right ht (inv_nonneg.mpr (le_of_lt htpos))

/-! ### 1. Local flatness -/

/-- **Local flatness.** If the second fundamental form vanishes at all nonzero boundary points, then
near a nonzero boundary point `w` of a chart, the boundary of the cone `T` is the hyperplane
`{⟪ν(w), ·⟫ = 0}` (which passes through the vertex), every boundary point there has normal `ν(w)`,
and the chart function is positive exactly on the side of `ν(w)`. -/
theorem flat_near {T U : Set (Space d)} {F : Space d → ℝ}
    (hcone : ∀ a : ℝ, 0 < a → ∀ᵐ x ∂volume, x ∈ T ↔ a • x ∈ T)
    (hA : ∀ (U' : Set (Space d)) (F' : Space d → ℝ), IsSmoothBoundaryChart T U' F' →
      ∀ z ∈ U', F' z = 0 → z ≠ 0 → secondFundamentalForm F' z = 0)
    (h : IsSmoothBoundaryChart T U F) {w : Space d} (hwU : w ∈ U) (hFw : F w = 0)
    (hw0 : w ≠ 0) :
    ∃ r > 0, ball w r ⊆ U ∧ ∀ v ∈ ball w r,
      (v ∈ measureTheoreticBoundary T ↔ inner ℝ (chartNormal F w) v = 0) ∧
      (v ∈ measureTheoreticBoundary T → HasNormal T v (chartNormal F w)) ∧
      (0 < F v ↔ 0 < inner ℝ (chartNormal F w) v) := by
  set n := chartNormal F w with hn
  have hne := h.gradient_ne_zero w hwU
  have hn1 : ‖n‖ = 1 := norm_chartNormal hne
  have hnw : inner ℝ n w = 0 := inner_chartNormal_self_eq_zero h hcone hwU hFw
  have hU' : IsOpen (U ∩ {x | x ≠ 0}) := h.isOpen.inter isOpen_ne
  have h' := h.mono hU' inter_subset_left
  have hA' : ∀ z ∈ U ∩ {x | x ≠ 0}, F z = 0 → sqNormSecondFundamentalForm F z = 0 := by
    intro z hz hFz
    rw [sqNormSecondFundamentalForm, hA _ F h' z hz hFz hz.2]
    simp
  obtain ⟨r, hr, hrU', hsign⟩ := h'.exists_ball_pos_iff_of_sqNorm_eq_zero hA' ⟨hwU, hw0⟩ hFw
  have hrU : ball w r ⊆ U := hrU'.trans inter_subset_left
  have hsign' : ∀ v ∈ ball w r, 0 < F v ↔ 0 < inner ℝ n v := fun v hv ↦ by
    rw [hsign v hv, inner_sub_right, hnw, sub_zero]
  have hzero : ∀ v ∈ ball w r, F v = 0 ↔ inner ℝ n v = 0 := by
    intro v hv
    have hvU := hrU hv
    have hcontn : Continuous (fun x : Space d ↦ inner ℝ n x) := continuous_const.inner continuous_id
    constructor
    · intro hFv
      rcases lt_trichotomy (inner ℝ n v) 0 with hlt | heq | hgt
      · exfalso
        have hgv := h.gradient_ne_zero v hvU
        have hdir : 0 < fderiv ℝ F v (gradient F v) := by
          rw [← inner_gradient_left, real_inner_self_eq_norm_sq]
          exact pow_pos (norm_pos_iff.mpr hgv) 2
        have hev1 := eventually_pos_along_aux (h.hasFDerivAt hvU).differentiableAt hFv hdir
        have hb : ∀ᶠ x in 𝓝 v, x ∈ ball w r := isOpen_ball.mem_nhds hv
        have hev2 : ∀ᶠ x in 𝓝 v, x ∈ ball w r ∧ inner ℝ n x < 0 :=
          hb.and (hcontn.continuousAt.eventually (gt_mem_nhds hlt))
        obtain ⟨t, ht1, ht2⟩ :=
          (hev1.and ((tendsto_add_smul_nhdsGT_aux v (gradient F v)).eventually hev2)).exists
        have := (hsign' _ ht2.1).mp ht1
        linarith [ht2.2]
      · exact heq
      · exfalso
        have := (hsign' v hv).mpr hgt
        rw [hFv] at this
        exact lt_irrefl 0 this
    · intro hnv
      have hle : ¬ 0 < F v := fun h1 ↦ by
        have := (hsign' v hv).mp h1
        linarith
      rcases (not_lt.mp hle).lt_or_eq with hlt | heq
      · exfalso
        have hb : ∀ᶠ x in 𝓝 v, x ∈ ball w r := isOpen_ball.mem_nhds hv
        have hev1 : ∀ᶠ x in 𝓝 v, x ∈ ball w r ∧ F x < 0 :=
          hb.and ((h.continuousOn.continuousAt (h.isOpen.mem_nhds hvU)).eventually
            (gt_mem_nhds hlt))
        obtain ⟨t, ht, htpos⟩ :=
          (((tendsto_add_smul_nhdsGT_aux v n).eventually hev1).and self_mem_nhdsWithin).exists
        have hpos : 0 < inner ℝ n (v + t • n) := by
          rw [inner_add_right, hnv, real_inner_smul_right, real_inner_self_eq_norm_sq, hn1]
          simpa using htpos
        have := (hsign' _ ht.1).mpr hpos
        linarith [ht.2]
      · exact heq
  have hn0 : n ≠ 0 := fun h0 ↦ by
    rw [h0, norm_zero] at hn1
    exact zero_ne_one hn1
  have hlin : IsSmoothBoundaryChart T (ball w r) (fun z ↦ inner ℝ n z) := by
    refine isSmoothBoundaryChart_inner isOpen_ball hn0 ?_
    filter_upwards [h.ae_mem_iff_of_mem] with z hz hzb
    rw [hz (hrU hzb), hsign' z hzb]
  refine ⟨r, hr, hrU, fun v hv ↦ ⟨?_, ?_, hsign' v hv⟩⟩
  · rw [← h.eq_zero_iff_mem_measureTheoreticBoundary (hrU hv), hzero v hv]
  · intro hvB U₂ F₂ h₂ hv₂
    rw [hlin.chartNormal_eq_of_mem_boundary h₂ hv hv₂ hvB]
    exact chartNormal_inner_left_const hn1 v

/-! ### 2. Punctured hyperplanes of boundary points -/

/-- **Boundary hyperplanes.** In dimension at least three, if the second fundamental form vanishes
at all nonzero boundary points of a cone whose nonzero boundary points are regular, and some
nonzero boundary point `w₀` with normal `n` lies on `n^⊥`, then every nonzero point of `n^⊥` is a
boundary point with normal `n`. -/
theorem hyperplane_subset {k : ℕ} (hk : 3 ≤ k) {T : Set (Space k)}
    (hcone : ∀ a : ℝ, 0 < a → ∀ᵐ x ∂volume, x ∈ T ↔ a • x ∈ T)
    (hchart : ∀ x ∈ measureTheoreticBoundary T, x ≠ 0 →
      ∃ (U : Set (Space k)) (F : Space k → ℝ), x ∈ U ∧ IsSmoothBoundaryChart T U F)
    (hA : ∀ (U : Set (Space k)) (F : Space k → ℝ), IsSmoothBoundaryChart T U F →
      ∀ z ∈ U, F z = 0 → z ≠ 0 → secondFundamentalForm F z = 0)
    {n w₀ : Space k} (hn : n ≠ 0) (hw₀ : inner ℝ n w₀ = 0) (hw₀0 : w₀ ≠ 0)
    (hw₀B : w₀ ∈ measureTheoreticBoundary T) (hw₀n : HasNormal T w₀ n) :
    ∀ w, inner ℝ n w = 0 → w ≠ 0 → w ∈ measureTheoreticBoundary T ∧ HasNormal T w n := by
  set P := {x : Space k | inner ℝ n x = 0} \ {0} with hPdef
  set S := {w | w ∈ P ∧ w ∈ measureTheoreticBoundary T ∧ HasNormal T w n} with hSdef
  have hPconn : IsPreconnected P :=
    (isPathConnected_hyperplane_diff_space_of_dimH_lt hk hn (C := {0}) (by
      rw [dimH_singleton]
      exact_mod_cast (by omega : 0 < k - 2))).isConnected.isPreconnected
  have hopen : ∀ w ∈ S, ∃ ρ > 0, ∀ v ∈ ball w ρ, v ∈ P → v ∈ S := by
    rintro w ⟨hwP, hwB, hwn⟩
    have hw0 : w ≠ 0 := hwP.2
    obtain ⟨U, F, hwU, hF⟩ := hchart w hwB hw0
    have hFw := hF.eq_zero_of_mem_measureTheoreticBoundary hwU hwB
    obtain ⟨ρ, hρ, -, hflat⟩ := flat_near hcone hA hF hwU hFw hw0
    have hnF : chartNormal F w = n := hwn U F hF hwU
    refine ⟨ρ, hρ, fun v hv hvP ↦ ?_⟩
    have hvn : inner ℝ (chartNormal F w) v = 0 := by
      rw [hnF]
      exact hvP.1
    have hvB := (hflat v hv).1.mpr hvn
    have hvN := (hflat v hv).2.1 hvB
    rw [hnF] at hvN
    exact ⟨hvP, hvB, hvN⟩
  have hclosed : ∀ w ∈ P, w ∈ closure S → w ∈ S := by
    intro w hwP hwcl
    have hwB : w ∈ measureTheoreticBoundary T :=
      (isClosed_measureTheoreticBoundary T).closure_subset_iff.mpr (fun x hx ↦ hx.2.1) hwcl
    have hw0 : w ≠ 0 := hwP.2
    obtain ⟨U, F, hwU, hF⟩ := hchart w hwB hw0
    have hnF : chartNormal F w = n := by
      by_contra hne
      have hcont : ContinuousAt (chartNormal F) w :=
        (hF.differentiableAt_chartNormal hwU).continuousAt
      have hUev : ∀ᶠ x in 𝓝 w, x ∈ U := hF.isOpen.mem_nhds hwU
      have hev : ∀ᶠ x in 𝓝 w, x ∈ U ∧ chartNormal F x ≠ n :=
        hUev.and (hcont.eventually (isOpen_ne.mem_nhds hne))
      obtain ⟨x, ⟨hxU, hxn⟩, hxS⟩ := mem_closure_iff_nhds.mp hwcl _ hev
      exact hxn (hxS.2.2 U F hF hxU)
    exact ⟨hwP, hwB, fun U₂ F₂ h₂ hw₂ ↦ (hF.chartNormal_eq_of_mem_boundary h₂ hwU hw₂ hwB).trans
      hnF⟩
  choose! ρ hρ hρS using hopen
  intro w hw hw0
  have hwP : w ∈ P := ⟨hw, hw0⟩
  by_contra hcon
  have hwS : w ∉ S := fun h' ↦ hcon ⟨h'.2.1, h'.2.2⟩
  have hw₀S : w₀ ∈ S := ⟨⟨hw₀, hw₀0⟩, hw₀B, hw₀n⟩
  have hu : IsOpen (⋃ x ∈ S, ball x (ρ x)) := isOpen_biUnion fun x _ ↦ isOpen_ball
  have hv : IsOpen (closure S)ᶜ := isClosed_closure.isOpen_compl
  have hcover : P ⊆ (⋃ x ∈ S, ball x (ρ x)) ∪ (closure S)ᶜ := by
    intro x hxP
    by_cases hx : x ∈ closure S
    · exact Or.inl (mem_biUnion (hclosed x hxP hx) (mem_ball_self (hρ x (hclosed x hxP hx))))
    · exact Or.inr hx
  obtain ⟨x, hxP, hxu, hxv⟩ := hPconn _ _ hu hv hcover
    ⟨w₀, hw₀S.1, mem_biUnion hw₀S (mem_ball_self (hρ w₀ hw₀S))⟩
    ⟨w, hwP, fun hcl ↦ hwS (hclosed w hwP hcl)⟩
  obtain ⟨y, hyS, hxy⟩ := mem_iUnion₂.mp hxu
  exact hxv (subset_closure (hρS y hyS x hxy hxP))

/-! ### 3. Simons' theorem -/

/-- **Simons' theorem for regular cones.** A minimizing cone in `ℝ^{m+1}`, `2 ≤ m ≤ 6`, whose
nonzero boundary points lie in smooth boundary charts is a.e. a half-space. -/
theorem ae_eq_positiveHalfspace_of_regular_cone {m : ℕ} (hm2 : 2 ≤ m) (hm6 : m ≤ 6)
    {T : Set (Space (m + 1))} (hT : IsMinimizingCone T)
    (hchart : ∀ x ∈ measureTheoreticBoundary T, x ≠ 0 →
      ∃ (U : Set (Space (m + 1))) (F : Space (m + 1) → ℝ), x ∈ U ∧ IsSmoothBoundaryChart T U F) :
    ∃ e : Space (m + 1), ‖e‖ = 1 ∧ T =ᵐ[volume] positiveHalfspace e := by
  set b := EuclideanSpace.basisFun (Fin (m + 1)) ℝ with hb
  have hA : ∀ (U : Set (Space (m + 1))) (F : Space (m + 1) → ℝ), IsSmoothBoundaryChart T U F →
      ∀ z ∈ U, F z = 0 → z ≠ 0 → secondFundamentalForm F z = 0 :=
    fun _ _ h _ hz hFz hz0 ↦ secondFundamentalForm_eq_zero_of_cone hm2 hm6 hT hchart h hz hFz hz0
  -- a nonzero boundary point
  have hP : ∀ n : ℕ, variationalPerimeter b T (ball 0 ((n : ℝ) + 1)) ≠ ⊤ := fun n ↦
    hT.minimizer.perimeter_ball_ne_top 0 _ (by positivity) (subset_univ _)
  obtain ⟨y₀, hy₀B, hy₀0⟩ : ∃ y ∈ measureTheoreticBoundary T, y ≠ 0 := by
    by_contra hcon
    have hcon' : ∀ y ∈ measureTheoreticBoundary T, y = 0 := fun y hy ↦
      not_not.mp fun h ↦ hcon ⟨y, hy, h⟩
    set μ := perimeterRadonMeasure b hT.measurableSet hP
    have hμ : ∀ U, IsOpen U → U ⊆ univ → μ U = variationalPerimeter b T U := fun U hU _ ↦
      perimeterRadonMeasure_apply_open b hT.measurableSet hP hU
    have h1 := hT.minimizer.measure_sdiff_boundary_eq_zero μ hμ
    have h2 := hT.minimizer.measure_singleton_eq_zero (by omega : 0 < m) μ hμ
      (mem_univ (0 : Space (m + 1)))
    have hsub : ball (0 : Space (m + 1)) 1 ⊆ (univ \ measureTheoreticBoundary T) ∪ {0} := by
      intro x _
      by_cases hx : x ∈ measureTheoreticBoundary T
      · exact Or.inr (hcon' x hx)
      · exact Or.inl ⟨mem_univ _, hx⟩
    have h3 : μ (ball 0 1) = 0 := measure_mono_null hsub (measure_union_null h1 h2)
    have hge := hT.minimizer.variationalPerimeter_ball_toReal_ge
      hT.zero_mem_measureTheoreticBoundary one_pos (subset_univ _)
    rw [← hμ _ isOpen_ball (subset_univ _), h3, ENNReal.toReal_zero, one_pow, mul_one] at hge
    exact absurd hge (not_le.mpr (minimizerPerimeterLowerConst_pos m))
  obtain ⟨U₀, F₀, hy₀U, hF₀⟩ := hchart y₀ hy₀B hy₀0
  have hFy₀ := hF₀.eq_zero_of_mem_measureTheoreticBoundary hy₀U hy₀B
  set n₀ := chartNormal F₀ y₀ with hn₀def
  have hn₀1 : ‖n₀‖ = 1 := norm_chartNormal (hF₀.gradient_ne_zero y₀ hy₀U)
  have hnorm0 : ∀ v : Space (m + 1), ‖v‖ = 1 → v ≠ 0 := fun v hv h0 ↦ by
    rw [h0, norm_zero] at hv
    exact zero_ne_one hv
  have hy₀n : inner ℝ n₀ y₀ = 0 := inner_chartNormal_self_eq_zero hF₀ hT.dilation hy₀U hFy₀
  have hplane := hyperplane_subset (by omega) hT.dilation hchart hA (hnorm0 n₀ hn₀1) hy₀n hy₀0
    hy₀B (hasNormal_of_chart hF₀ hy₀U hy₀B)
  -- the boundary lies in the hyperplane `n₀^⊥`
  have hBsub : ∀ z ∈ measureTheoreticBoundary T, inner ℝ n₀ z = 0 := by
    intro z hzB
    by_cases hz0 : z = 0
    · rw [hz0, inner_zero_right]
    obtain ⟨U₁, F₁, hzU, hF₁⟩ := hchart z hzB hz0
    have hFz := hF₁.eq_zero_of_mem_measureTheoreticBoundary hzU hzB
    have hn₁1 : ‖chartNormal F₁ z‖ = 1 := norm_chartNormal (hF₁.gradient_ne_zero z hzU)
    have hzn : inner ℝ (chartNormal F₁ z) z = 0 :=
      inner_chartNormal_self_eq_zero hF₁ hT.dilation hzU hFz
    have hplane1 := hyperplane_subset (by omega) hT.dilation hchart hA
      (hnorm0 _ hn₁1) hzn hz0 hzB (hasNormal_of_chart hF₁ hzU hzB)
    obtain ⟨p, hp0, hp₀, hp₁⟩ : ∃ p : Space (m + 1), p ≠ 0 ∧ inner ℝ n₀ p = 0 ∧
        inner ℝ (chartNormal F₁ z) p = 0 := by
      let L : Space (m + 1) →ₗ[ℝ] ℝ × ℝ :=
        ((innerSL ℝ n₀).prod (innerSL ℝ (chartNormal F₁ z))).toLinearMap
      have hker : LinearMap.ker L ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by
        rw [Module.finrank_prod, Module.finrank_self, finrank_euclideanSpace_fin]
        omega)
      obtain ⟨p, hpL, hp0⟩ := (Submodule.ne_bot_iff _).mp hker
      have hLp : L p = 0 := hpL
      simp only [L, ContinuousLinearMap.coe_coe, ContinuousLinearMap.prod_apply,
        innerSL_apply_apply, Prod.mk_eq_zero] at hLp
      exact ⟨p, hp0, hLp.1, hLp.2⟩
    obtain ⟨hpB, hpn₀⟩ := hplane p hp₀ hp0
    obtain ⟨-, hpn₁⟩ := hplane1 p hp₁ hp0
    obtain ⟨U₂, F₂, hpU, hF₂⟩ := hchart p hpB hp0
    have heq : n₀ = chartNormal F₁ z := (hpn₀ U₂ F₂ hF₂ hpU).symm.trans (hpn₁ U₂ F₂ hF₂ hpU)
    rw [heq]
    exact hzn
  -- interior and exterior points near `y₀`
  obtain ⟨r, hr, hrU, hflat⟩ := flat_near hT.dilation hA hF₀ hy₀U hFy₀ hy₀0
  have hball_pos : ∀ q : Space (m + 1), ball q (r / 4) ⊆ ball y₀ r →
      (∀ x ∈ ball q (r / 4), 0 < inner ℝ n₀ x) → q ∈ measureTheoreticInterior T := by
    intro q hsub hq
    refine ⟨r / 4, by positivity, ?_⟩
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hF₀.ae_mem_iff_of_mem] with x hx hxb
    exact hxb.2 ((hx (hrU (hsub hxb.1))).mpr ((hflat x (hsub hxb.1)).2.2.mpr (hq x hxb.1)))
  have hball_neg : ∀ q : Space (m + 1), ball q (r / 4) ⊆ ball y₀ r →
      (∀ x ∈ ball q (r / 4), inner ℝ n₀ x < 0) → q ∈ measureTheoreticExterior T := by
    intro q hsub hq
    refine ⟨r / 4, by positivity, ?_⟩
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hF₀.ae_mem_iff_of_mem] with x hx hxb
    have hpos := (hx (hrU (hsub hxb.2))).mp hxb.1
    have := (hflat x (hsub hxb.2)).2.2.mp hpos
    linarith [hq x hxb.2]
  have hcontn : ∀ x y : Space (m + 1), |inner ℝ n₀ x - inner ℝ n₀ y| ≤ ‖x - y‖ := by
    intro x y
    rw [← inner_sub_right]
    calc |inner ℝ n₀ (x - y)| ≤ ‖n₀‖ * ‖x - y‖ := abs_real_inner_le_norm _ _
      _ = ‖x - y‖ := by rw [hn₀1, one_mul]
  have hsubq : ∀ s : ℝ, |s| = r / 2 → ball (y₀ + s • n₀) (r / 4) ⊆ ball y₀ r := by
    intro s hs x hx
    rw [mem_ball] at hx ⊢
    calc dist x y₀ ≤ dist x (y₀ + s • n₀) + dist (y₀ + s • n₀) y₀ := dist_triangle _ _ _
      _ < r / 4 + r / 2 := by
          refine add_lt_add_of_lt_of_le hx (le_of_eq ?_)
          rw [dist_eq_norm, add_sub_cancel_left, norm_smul, hn₀1, mul_one, Real.norm_eq_abs, hs]
      _ < r := by linarith
  have hqval : ∀ s : ℝ, inner ℝ n₀ (y₀ + s • n₀) = s := by
    intro s
    rw [inner_add_right, hy₀n, real_inner_smul_right, real_inner_self_eq_norm_sq, hn₀1]
    ring
  have hqpos : y₀ + (r / 2) • n₀ ∈ measureTheoreticInterior T := by
    refine hball_pos _ (hsubq _ (abs_of_pos (by positivity))) fun x hx ↦ ?_
    have h1 := hcontn x (y₀ + (r / 2) • n₀)
    rw [hqval, abs_le] at h1
    rw [mem_ball, dist_eq_norm] at hx
    linarith [h1.1]
  have hqneg : y₀ + (-(r / 2)) • n₀ ∈ measureTheoreticExterior T := by
    refine hball_neg _ (hsubq _ (by rw [abs_neg, abs_of_pos (by positivity)])) fun x hx ↦ ?_
    have h1 := hcontn x (y₀ + (-(r / 2)) • n₀)
    rw [hqval, abs_le] at h1
    rw [mem_ball, dist_eq_norm] at hx
    linarith [h1.2]
  -- the open half-spaces avoid the boundary
  have hpre : ∀ c : ℝ, IsPreconnected {x : Space (m + 1) | c * inner ℝ n₀ x > 0} := by
    intro c
    have hconv : Convex ℝ {x : Space (m + 1) | c * inner ℝ n₀ x > 0} := by
      intro x hx y hy a β ha hβ hab
      simp only [mem_ofPred_eq, gt_iff_lt] at hx hy ⊢
      rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
      rcases ha.lt_or_eq with ha' | ha'
      · nlinarith [mul_pos ha' hx, mul_nonneg hβ hy.le]
      · rw [← ha', zero_add] at hab
        rw [← ha', hab]
        linarith
    exact hconv.isPreconnected
  have hnb : ∀ c : ℝ, ∀ x ∈ {x : Space (m + 1) | c * inner ℝ n₀ x > 0},
      x ∉ measureTheoreticBoundary T := by
    intro c x hx hxB
    simp only [mem_ofPred_eq, hBsub x hxB, mul_zero, gt_iff_lt, lt_irrefl] at hx
  have hint : {x : Space (m + 1) | (1 : ℝ) * inner ℝ n₀ x > 0} ⊆ measureTheoreticInterior T := by
    rcases subset_measureTheoreticInterior_or_exterior (hpre 1) (hnb 1) with h | h
    · exact h
    · exfalso
      have hmem : y₀ + (r / 2) • n₀ ∈ {x : Space (m + 1) | (1 : ℝ) * inner ℝ n₀ x > 0} := by
        simp only [mem_ofPred_eq, one_mul, hqval]
        positivity
      exact (disjoint_left.mp (disjoint_measureTheoreticInterior_exterior T)) hqpos (h hmem)
  have hext : {x : Space (m + 1) | (-1 : ℝ) * inner ℝ n₀ x > 0} ⊆
      measureTheoreticExterior T := by
    rcases subset_measureTheoreticInterior_or_exterior (hpre (-1)) (hnb (-1)) with h | h
    · exfalso
      have hmem : y₀ + (-(r / 2)) • n₀ ∈
          {x : Space (m + 1) | (-1 : ℝ) * inner ℝ n₀ x > 0} := by
        simp only [mem_ofPred_eq, hqval]
        linarith
      exact (disjoint_left.mp (disjoint_measureTheoreticInterior_exterior T)) (h hmem) hqneg
    · exact h
  -- conclusion
  refine ⟨n₀, hn₀1, ?_⟩
  have hnull : ∀ᵐ x ∂volume, inner ℝ n₀ x ≠ 0 := by
    have := volume_orthogonal_hyperplane_eq_zero (hnorm0 n₀ hn₀1)
    rw [measure_eq_zero_iff_ae_notMem] at this
    exact this
  filter_upwards [hT.minimizer.ae_mem_iff_measureTheoreticInterior, hnull] with x hx hx0
  have hxi := hx (mem_univ x)
  apply propext
  rw [hxi]
  show x ∈ measureTheoreticInterior T ↔ 0 < inner ℝ n₀ x
  rcases lt_or_gt_of_ne hx0 with hneg | hpos
  · constructor
    · intro hxint
      exfalso
      have hxext : x ∈ measureTheoreticExterior T := hext (by
        simp only [mem_ofPred_eq]
        linarith)
      exact (disjoint_left.mp (disjoint_measureTheoreticInterior_exterior T)) hxint hxext
    · intro h
      linarith
  · exact ⟨fun _ ↦ hpos, fun _ ↦ hint (by simp only [mem_ofPred_eq, one_mul]; exact hpos)⟩

end Simons

/-- **Simons' theorem, `3 ≤ k ≤ 7`, relative to Schauder regularity.** -/
theorem simonsHyp_of_smooth_of_three_le (hsmooth : C1RegularSmoothHyp) {k : ℕ} (hk3 : 3 ≤ k)
    (hk7 : k ≤ 7) : SimonsHyp k := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  intro T hT hreg
  exact Simons.ae_eq_positiveHalfspace_of_regular_cone (by omega) (by omega) hT
    fun x hx hx0 ↦ hsmooth (m + 1) T x hT.minimizer (hreg x hx hx0)

/-- **Simons' theorem, `2 ≤ k ≤ 7`,** relative to Schauder regularity and the planar case
`SimonsHyp 2`. -/
theorem simonsHyp_of_smooth_of_simonsHyp_two (hsmooth : C1RegularSmoothHyp) (h2 : SimonsHyp 2)
    {k : ℕ} (hk2 : 2 ≤ k) (hk7 : k ≤ 7) : SimonsHyp k := by
  rcases Nat.lt_or_ge k 3 with hk | hk
  · obtain rfl : k = 2 := by omega
    exact h2
  · exact simonsHyp_of_smooth_of_three_le hsmooth hk hk7

end SerrinEpigraph
