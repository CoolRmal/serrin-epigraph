module

public import SerrinEpigraph.MovingPhaseCompactness
public import SerrinEpigraph.HalfspaceTangents
public import SerrinEpigraph.PerimeterMonotonicity
public import SerrinEpigraph.PlaneTiltTranslatedPlanarLimit

/-!
# Sharp perimeter density forces planar moving-center limits (SD2, SD4)

This module formalizes `docs/rigidity-proof/sharp-density.md` SD2 and the compactness part of
SD4, for free-boundary centers that move with the sequence:
- a nontrivial global perimeter minimizer has a measure-theoretic boundary point, hence a point
  with a halfspace tangent and unit perimeter density
  (`IsLocalPerimeterMinimizer.exists_halfspace_tangent_point`);
- **SD2**: if moreover `P(E, B_r(z)) ≤ ω_m r ^ m` at every center and radius, the perimeter ratio
  is constant at that point, the minimizer is a cone there, and therefore it is almost everywhere
  an affine halfspace (`IsLocalPerimeterMinimizer.ae_eq_affine_halfspace_of_sharp_density`);
- **SD4**: under the sharp all-center planar energy bound, every free-boundary-centered family of
  diverging dilations has a subsequence converging locally in `L¹` to a halfspace whose boundary
  plane passes through the origin (`RigidityHypotheses.exists_frontier_halfspace_subseq`).
  The plane passes through the origin because the shifted family would otherwise have no free
  boundary near the original centers (`translated_eventually_no_freeBoundary_away_plane`).
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory Filter InnerProductSpace
open scoped Topology ENNReal

namespace SerrinEpigraph

/-! ## SD2. Sharp perimeter density forces a halfspace -/

/-- A global perimeter minimizer whose two phases both have positive measure has a point of
measure-theoretic boundary: otherwise the open canonical interior would be clopen. -/
theorem IsLocalPerimeterMinimizer.measureTheoreticBoundary_nonempty {m : ℕ}
    {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))} {E : Set (Space (m + 1))}
    (hmin : IsLocalPerimeterMinimizer b E univ) (hE : volume E ≠ 0) (hEc : volume Eᶜ ≠ 0) :
    (measureTheoreticBoundary E).Nonempty := by
  by_contra hempty
  rw [not_nonempty_iff_eq_empty] at hempty
  have hunion : measureTheoreticInterior E ∪ measureTheoreticExterior E = univ := by
    have hc := compl_measureTheoreticInterior_union_exterior E
    rw [hempty] at hc
    exact compl_empty_iff.mp hc
  have hcompl : (measureTheoreticInterior E)ᶜ = measureTheoreticExterior E := by
    apply Subset.antisymm
    · intro x hx
      have hxu : x ∈ measureTheoreticInterior E ∪ measureTheoreticExterior E := by
        rw [hunion]
        exact mem_univ x
      rcases hxu with hxi | hxe
      · exact absurd hxi hx
      · exact hxe
    · intro x hxe hxi
      exact disjoint_left.mp (disjoint_measureTheoreticInterior_exterior E) hxi hxe
  have hclopen : IsClopen (measureTheoreticInterior E) := by
    refine ⟨?_, isOpen_measureTheoreticInterior E⟩
    rw [← isOpen_compl_iff, hcompl]
    exact isOpen_measureTheoreticExterior E
  have hae := hmin.ae_mem_iff_measureTheoreticInterior
  rcases isClopen_iff.mp hclopen with h0 | h1
  · apply hE
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hae] with x hx hxE
    have hx' := (hx (mem_univ x)).mp hxE
    rw [h0] at hx'
    exact hx'
  · apply hEc
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hae] with x hx hxE
    apply hxE
    exact (hx (mem_univ x)).mpr (by rw [h1]; exact mem_univ x)

/-- A nontrivial global perimeter minimizer has a point at which the blowups converge to a
halfspace and the perimeter ratio tends to the unit density `ω_m` (BV12 applied to the nonzero
perimeter measure). -/
theorem IsLocalPerimeterMinimizer.exists_halfspace_tangent_point {m : ℕ}
    {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))} {E : Set (Space (m + 1))}
    (hmin : IsLocalPerimeterMinimizer b E univ) (hE : volume E ≠ 0) (hEc : volume Eᶜ ≠ 0) :
    ∃ x₀ e : Space (m + 1), ‖e‖ = 1 ∧
      (∀ K : Set (Space (m + 1)), IsCompact K →
        Tendsto (fun r : ℝ ↦ ∫ y in K,
          ‖((fun z ↦ x₀ + r • z) ⁻¹' E).indicator (fun _ ↦ (1 : ℝ)) y -
            {y : Space (m + 1) | 0 < inner ℝ e y}.indicator (fun _ ↦ (1 : ℝ)) y‖)
          (𝓝[>] 0) (𝓝 0)) ∧
      Tendsto (fun r : ℝ ↦ r ^ (-(m : ℤ)) * (variationalPerimeter b E (ball x₀ r)).toReal)
        (𝓝[>] 0) (𝓝 (volume.real (closedBall (0 : Space m) 1))) := by
  have hP : ∀ n : ℕ, variationalPerimeter b E (ball 0 ((n : ℝ) + 1)) ≠ ⊤ :=
    fun n ↦ hmin.perimeter_ball_ne_top 0 ((n : ℝ) + 1) (by positivity) (subset_univ _)
  obtain ⟨x₁, hx₁⟩ := hmin.measureTheoreticBoundary_nonempty hE hEc
  have hμ_ball : perimeterRadonMeasure b hmin.measurableSet hP (ball x₁ 1) =
      variationalPerimeter b E (ball x₁ 1) :=
    perimeterRadonMeasure_apply_open b hmin.measurableSet hP isOpen_ball
  have hpos : 0 < variationalPerimeter b E (ball x₁ 1) := by
    refine lt_of_lt_of_le ?_ (hmin.variationalPerimeter_ball_ge hx₁ zero_lt_one (subset_univ _))
    rw [one_pow, mul_one]
    exact ENNReal.ofReal_pos.mpr (minimizerPerimeterLowerConst_pos m)
  have hμ0 : perimeterRadonMeasure b hmin.measurableSet hP ≠ 0 := by
    intro h0
    rw [h0, Measure.coe_zero, Pi.zero_apply] at hμ_ball
    rw [← hμ_ball] at hpos
    exact lt_irrefl _ hpos
  have : (ae (perimeterRadonMeasure b hmin.measurableSet hP)).NeBot := ae_neBot.mpr hμ0
  obtain ⟨x₀, e, -, he, hblow, hdens, -⟩ := (hmin.ae_exists_halfspace_tangent_global hP).exists
  exact ⟨x₀, e, he, hblow, hdens⟩

/-- At a point of unit tangent density, the sharp density bound on all concentric balls makes the
perimeter ratio constant, by the monotonicity formula. -/
theorem IsLocalPerimeterMinimizer.perimeter_ratio_eq_of_sharp {m : ℕ}
    {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))} {E : Set (Space (m + 1))}
    (hmin : IsLocalPerimeterMinimizer b E univ) {x₀ : Space (m + 1)} {ω : ℝ} (hω : 0 ≤ ω)
    (hdens : Tendsto (fun r : ℝ ↦ r ^ (-(m : ℤ)) * (variationalPerimeter b E (ball x₀ r)).toReal)
      (𝓝[>] 0) (𝓝 ω))
    (hsharp : ∀ r : ℝ, 0 < r →
      variationalPerimeter b E (ball x₀ r) ≤ ENNReal.ofReal (ω * r ^ m)) :
    ∀ r > 0, r ^ (-(m : ℤ)) * (variationalPerimeter b E (ball x₀ r)).toReal = ω := by
  intro r hr
  have : (𝓝[>] (0 : ℝ)).NeBot := nhdsWithin_Ioi_neBot le_rfl
  apply le_antisymm
  · have hle : (variationalPerimeter b E (ball x₀ r)).toReal ≤ ω * r ^ m :=
      ENNReal.toReal_le_of_le_ofReal (by positivity) (hsharp r hr)
    calc r ^ (-(m : ℤ)) * (variationalPerimeter b E (ball x₀ r)).toReal
        ≤ r ^ (-(m : ℤ)) * (ω * r ^ m) := mul_le_mul_of_nonneg_left hle (zpow_nonneg hr.le _)
      _ = ω := by
        rw [zpow_neg, zpow_natCast]
        have hne : r ^ m ≠ 0 := pow_ne_zero m hr.ne'
        field_simp
  · refine le_of_tendsto hdens ?_
    filter_upwards [Ioo_mem_nhdsGT hr] with s hs
    exact hmin.perimeter_ratio_le hs.1 hs.2.le (subset_univ _)

/-- **SD2.** A nontrivial global perimeter minimizer satisfying the sharp unit-density bound
`P(E, B_r(z)) ≤ ω_m r ^ m` at every center and radius is almost everywhere an affine halfspace. -/
theorem IsLocalPerimeterMinimizer.ae_eq_affine_halfspace_of_sharp_density {m : ℕ}
    {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))} {E : Set (Space (m + 1))}
    (hmin : IsLocalPerimeterMinimizer b E univ) (hE : volume E ≠ 0) (hEc : volume Eᶜ ≠ 0)
    (hsharp : ∀ z : Space (m + 1), ∀ r : ℝ, 0 < r →
      variationalPerimeter b E (ball z r) ≤
        ENNReal.ofReal (volume.real (closedBall (0 : Space m) 1) * r ^ m)) :
    ∃ x₀ e : Space (m + 1), ‖e‖ = 1 ∧ ∀ᵐ x ∂volume, x ∈ E ↔ 0 < inner ℝ e (x - x₀) := by
  obtain ⟨x₀, e, he, hblow, hdens⟩ := hmin.exists_halfspace_tangent_point hE hEc
  have hconst := hmin.perimeter_ratio_eq_of_sharp measureReal_nonneg hdens (hsharp x₀)
  have hcone (a : ℝ) (ha : 0 < a) : ∀ᵐ y ∂volume, x₀ + y ∈ E ↔ x₀ + a • y ∈ E :=
    hmin.ae_mem_add_smul_iff_of_constant_perimeter_ratio x₀ hconst ha
  let H : Set (Space (m + 1)) := {y | 0 < inner ℝ e y}
  let E₀ : Set (Space (m + 1)) := (fun z ↦ x₀ + z) ⁻¹' E
  have hHm : MeasurableSet H :=
    (isOpen_lt continuous_const (continuous_const.inner continuous_id)).measurableSet
  have hE₀m : MeasurableSet E₀ := hmin.measurableSet.preimage (measurable_const_add x₀)
  have hzero (K : Set (Space (m + 1))) (hK : IsCompact K) :
      (∫ y in K, ‖E₀.indicator (fun _ ↦ (1 : ℝ)) y - H.indicator (fun _ ↦ (1 : ℝ)) y‖) = 0 := by
    have : (𝓝[>] (0 : ℝ)).NeBot := nhdsWithin_Ioi_neBot le_rfl
    refine tendsto_nhds_unique (tendsto_const_nhds.congr' ?_) (hblow K hK)
    filter_upwards [self_mem_nhdsWithin] with r hr
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae (hcone r hr)] with y hy
    have hind : E₀.indicator (fun _ ↦ (1 : ℝ)) y =
        ((fun z ↦ x₀ + r • z) ⁻¹' E).indicator (fun _ ↦ (1 : ℝ)) y := by
      by_cases hyE : x₀ + y ∈ E
      · rw [indicator_of_mem (show y ∈ E₀ from hyE),
          indicator_of_mem (show y ∈ (fun z ↦ x₀ + r • z) ⁻¹' E from hy.mp hyE)]
      · rw [indicator_of_notMem (show y ∉ E₀ from hyE),
          indicator_of_notMem (show y ∉ (fun z ↦ x₀ + r • z) ⁻¹' E from
            fun h' ↦ hyE (hy.mpr h'))]
    rw [hind]
  have hae_ball (n : ℕ) : ∀ᵐ y ∂volume.restrict (closedBall (0 : Space (m + 1)) (n + 1 : ℝ)),
      (x₀ + y ∈ E ↔ 0 < inner ℝ e y) := by
    have hK := isCompact_closedBall (0 : Space (m + 1)) (n + 1 : ℝ)
    have hint : IntegrableOn (fun y ↦ ‖E₀.indicator (fun _ ↦ (1 : ℝ)) y -
        H.indicator (fun _ ↦ (1 : ℝ)) y‖) (closedBall (0 : Space (m + 1)) (n + 1 : ℝ)) :=
      (((continuousOn_const.integrableOn_compact hK).indicator hE₀m).sub
        ((continuousOn_const.integrableOn_compact hK).indicator hHm)).norm
    have h0 := (integral_eq_zero_iff_of_nonneg (fun y ↦ norm_nonneg _) hint).mp (hzero _ hK)
    filter_upwards [h0] with y hy
    have hy' : E₀.indicator (fun _ ↦ (1 : ℝ)) y = H.indicator (fun _ ↦ (1 : ℝ)) y := by
      have hy0 : ‖E₀.indicator (fun _ ↦ (1 : ℝ)) y - H.indicator (fun _ ↦ (1 : ℝ)) y‖ = 0 := hy
      exact sub_eq_zero.mp (norm_eq_zero.mp hy0)
    constructor
    · intro h1
      by_contra h2
      rw [indicator_of_mem (show y ∈ E₀ from h1), indicator_of_notMem (show y ∉ H from h2)] at hy'
      norm_num at hy'
    · intro h2
      by_contra h1
      rw [indicator_of_notMem (show y ∉ E₀ from h1), indicator_of_mem (show y ∈ H from h2)] at hy'
      norm_num at hy'
  have hall : ∀ᵐ y ∂volume, (x₀ + y ∈ E ↔ 0 < inner ℝ e y) := by
    have hu := (ae_restrict_iUnion_iff
      (fun n : ℕ ↦ closedBall (0 : Space (m + 1)) (n + 1 : ℝ))
      (fun y ↦ (x₀ + y ∈ E ↔ 0 < inner ℝ e y))).mpr hae_ball
    simpa only [iUnion_integer_closedBall, Measure.restrict_univ] using hu
  refine ⟨x₀, e, he, ?_⟩
  have hqmp : Measure.QuasiMeasurePreserving (fun x : Space (m + 1) ↦ x - x₀) volume volume :=
    (measurePreserving_sub_right volume x₀).quasiMeasurePreserving
  filter_upwards [hqmp.ae hall] with x hx
  rwa [add_sub_cancel] at hx

/-! ## Local convergence transfers -/

/-- Local `L¹` convergence to a phase transfers to any a.e. equal phase. -/
theorem tendsto_local_indicator_congr_ae {d : ℕ} {U : ℕ → Space d → ℝ}
    {E H : Set (Space d)} (hEH : E =ᵐ[volume] H)
    (hlocal : ∀ K : Set (Space d), IsCompact K →
      Tendsto (fun j ↦ ∫ x in K, ‖U j x - E.indicator (fun _ ↦ (1 : ℝ)) x‖) atTop (𝓝 0))
    (K : Set (Space d)) (hK : IsCompact K) :
    Tendsto (fun j ↦ ∫ x in K, ‖U j x - H.indicator (fun _ ↦ (1 : ℝ)) x‖) atTop (𝓝 0) := by
  have hind : E.indicator (fun _ ↦ (1 : ℝ)) =ᵐ[volume] H.indicator (fun _ ↦ (1 : ℝ)) :=
    indicator_ae_eq_of_ae_eq_set hEH
  refine (hlocal K hK).congr fun j ↦ ?_
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_of_ae hind] with x hx
  rw [hx]

/-- Local `L¹` convergence to the affine halfspace `{x | 0 < ⟪e, x - x₀⟫}` is local `L¹`
convergence of the translated functions to the halfspace `{y | 0 < ⟪e, y⟫}`. -/
theorem tendsto_local_halfspace_indicator_shift {d : ℕ} {U : ℕ → Space d → ℝ}
    (hU : ∀ j, Continuous (U j)) (e x₀ : Space d)
    (hlocal : ∀ K : Set (Space d), IsCompact K →
      Tendsto (fun j ↦ ∫ x in K, ‖U j x -
        {x : Space d | 0 < inner ℝ e (x - x₀)}.indicator (fun _ ↦ (1 : ℝ)) x‖) atTop (𝓝 0))
    (K : Set (Space d)) (hK : IsCompact K) :
    Tendsto (fun j ↦ ∫ y in K, ‖U j (x₀ + y) -
      {y : Space d | 0 < inner ℝ e y}.indicator (fun _ ↦ (1 : ℝ)) y‖) atTop (𝓝 0) := by
  obtain ⟨s, hs⟩ := hK.isBounded.subset_closedBall (0 : Space d)
  have hHm : MeasurableSet {y : Space d | 0 < inner ℝ e y} :=
    (isOpen_lt continuous_const (continuous_const.inner continuous_id)).measurableSet
  have hball : Tendsto (fun j ↦ ∫ y in closedBall (0 : Space d) s, ‖U j (x₀ + y) -
      {y : Space d | 0 < inner ℝ e y}.indicator (fun _ ↦ (1 : ℝ)) y‖) atTop (𝓝 0) := by
    refine (hlocal (closedBall x₀ s) (isCompact_closedBall x₀ s)).congr fun j ↦ ?_
    rw [← setIntegral_closedBall_comp_add_left (fun x ↦ ‖U j x -
      {x : Space d | 0 < inner ℝ e (x - x₀)}.indicator (fun _ ↦ (1 : ℝ)) x‖) x₀ s]
    refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
    simp only [indicator_apply, mem_ofPred_eq, add_sub_cancel_left]
  exact integral_limit_mono_set hs (fun j y ↦ U j (x₀ + y))
    ({y : Space d | 0 < inner ℝ e y}.indicator (fun _ ↦ (1 : ℝ)))
    (fun j ↦ ((hU j).comp (continuous_const.add continuous_id)).continuousOn.integrableOn_compact
      (isCompact_closedBall _ _))
    ((continuousOn_const.integrableOn_compact (isCompact_closedBall _ _)).indicator hHm) hball

/-! ## SD4. Planar limits through the origin at moving free-boundary centers -/

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}

/-- **SD2–SD4 at moving free-boundary centers.** Under the sharp all-center planar energy bound,
every free-boundary-centered family of diverging dilations has a subsequence converging locally in
`L¹` to a halfspace whose boundary plane passes through the origin. -/
theorem RigidityHypotheses.exists_frontier_halfspace_subseq
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hsharp : ∀ z : Space (m + 1), ∀ ρ : ℝ, 0 < ρ →
      (∫ x in closedBall z ρ, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤
        phasePrimitive f 1 * volume.real (closedBall (0 : Space m) 1) * ρ ^ m)
    (c : ℕ → Space (m + 1)) (hc : ∀ j, c j ∈ frontier (epigraph g))
    {R : ℕ → ℝ} (hR : ∀ j, 1 ≤ R j) (hRt : Tendsto R atTop atTop) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ e : Space (m + 1), ‖e‖ = 1 ∧
      ∀ K : Set (Space (m + 1)), IsCompact K →
        Tendsto (fun j ↦ ∫ x in K, ‖zeroExtension g u (c (φ j) + R (φ j) • x) -
          {y : Space (m + 1) | 0 < inner ℝ e y}.indicator (fun _ ↦ (1 : ℝ)) x‖)
          atTop (𝓝 0) := by
  obtain ⟨φ, hφ, E, hEm, hE0, hEc0, hlim⟩ :=
    hr.translated_nontrivial_measurable_phase_limit h hsharp c hc hR hRt
  let c' : ℕ → Space (m + 1) := fun j ↦ c (φ j)
  let R' : ℕ → ℝ := fun j ↦ R (φ j)
  have hR' : ∀ j, 1 ≤ R' j := fun j ↦ hR (φ j)
  have hR'pos : ∀ j, 0 < R' j := fun j ↦ zero_lt_one.trans_le (hR' j)
  have hRt' : Tendsto R' atTop atTop := hRt.comp hφ.tendsto_atTop
  have hlimE : ∀ K : Set (Space (m + 1)), IsCompact K →
      Tendsto (fun j ↦ ∫ x in K, ‖zeroExtension g u (c' j + R' j • x) -
        E.indicator (fun _ ↦ (1 : ℝ)) x‖) atTop (𝓝 0) := fun K hK ↦ (hlim K hK).2
  let b := EuclideanSpace.basisFun (Fin (m + 1)) ℝ
  have hPbound (z : Space (m + 1)) (r : ℝ) (hr0 : 0 < r) :
      variationalPerimeter b E (ball z r) ≤
        ENNReal.ofReal (volume.real (closedBall (0 : Space m) 1) * r ^ m) :=
    hr.translated_limiting_phase_sharp_perimeter_bound h hsharp c' hR'pos hEm hlimE b z r hr0
  have hPE (n : ℕ) : variationalPerimeter b E (ball 0 ((n : ℝ) + 1)) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hPbound 0 _ (by positivity))
  have hmin : IsLocalPerimeterMinimizer b E univ :=
    isLocalPerimeterMinimizer_univ b hEm hPE fun U D K hU hD hK hKU hED ↦
      hr.translated_limiting_phase_open_minimality h hsharp b c' hR' hRt' hEm hD hlimE
        hK hU hKU hED
  obtain ⟨x₀, e, he, hae⟩ := hmin.ae_eq_affine_halfspace_of_sharp_density hE0 hEc0 hPbound
  have hEH : E =ᵐ[volume] {x : Space (m + 1) | 0 < inner ℝ e (x - x₀)} :=
    eventuallyEqSet_iff.mpr hae
  have hlimH := tendsto_local_indicator_congr_ae hEH hlimE
  let c'' : ℕ → Space (m + 1) := fun j ↦ c' j + R' j • x₀
  have hUcont (j : ℕ) : Continuous (fun x ↦ zeroExtension g u (c' j + R' j • x)) :=
    (locallyLipschitz_comp_translate_dilation h.zeroExtension_locallyLipschitz
      (c' j) (R' j)).continuous
  have hshift : ∀ K : Set (Space (m + 1)), IsCompact K →
      Tendsto (fun j ↦ ∫ x in K, ‖zeroExtension g u (c'' j + R' j • x) -
        {y : Space (m + 1) | 0 < inner ℝ e y}.indicator (fun _ ↦ (1 : ℝ)) x‖)
        atTop (𝓝 0) := by
    intro K hK
    have hs := tendsto_local_halfspace_indicator_shift
      (U := fun j x ↦ zeroExtension g u (c' j + R' j • x)) hUcont e x₀ hlimH K hK
    refine hs.congr fun j ↦ ?_
    refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
    simp only [c'', smul_add, add_assoc]
  have hplane : inner ℝ e x₀ = 0 := by
    by_contra hne
    have hev := hr.translated_eventually_no_freeBoundary_away_plane h hsharp c'' hR'pos hRt' he
      hshift (isCompact_singleton (x := -x₀)) (by
        intro x hx
        rw [mem_singleton_iff.mp hx, inner_neg_right]
        exact neg_ne_zero.mpr hne)
    obtain ⟨j, hj⟩ := hev.exists
    apply hj (-x₀) (mem_singleton _)
    have hpt : c'' j + R' j • (-x₀) = c (φ j) := by
      simp only [c'', c', R', smul_neg]
      exact add_neg_cancel_right _ _
    rw [hpt]
    exact hc (φ j)
  refine ⟨φ, hφ, e, he, fun K hK ↦ ?_⟩
  have hset : {x : Space (m + 1) | 0 < inner ℝ e (x - x₀)} =
      {y : Space (m + 1) | 0 < inner ℝ e y} := by
    ext x
    simp only [mem_ofPred_eq, inner_sub_right, hplane, sub_zero]
  have hK' := hlimH K hK
  rw [hset] at hK'
  exact hK'

end SerrinEpigraph
