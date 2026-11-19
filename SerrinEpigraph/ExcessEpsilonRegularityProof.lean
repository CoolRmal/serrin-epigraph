module

public import SerrinEpigraph.FlatGraph

/-!
# Proof of the excess form of ε-regularity (`GR13`)

`excessEpsilonRegularityHyp : ExcessEpsilonRegularityHyp`. For a flat configuration with excess
`e ≤ ε₀`:

1. the boundary over `B_{3/4}` lies in a band `|t - a| ≤ flatBand m e` (`IsFlatConfig.band`),
   with interior points above and exterior points below it;
2. around every boundary point `p` of the half cylinder the configuration rescaled by `1/8` is
   flat with excess `≤ 8^m e` (`IsFlatConfig.recenter`), so the iterated tilt-excess decay
   (`IsFlatConfig.exists_normal`) yields a normal `n(p)` with scale-wise flatness;
3. `isC1BoundaryPoint_of_flat_normals` turns these into a `C¹` graph near every boundary point
   of the half cylinder.
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory InnerProductSpace Filter
open scoped Topology ENNReal NNReal

namespace SerrinEpigraph

/-- **The excess form of ε-regularity** (`GR13`). -/
theorem excessEpsilonRegularityHyp : ExcessEpsilonRegularityHyp := by
  intro m
  set b := EuclideanSpace.basisFun (Fin (m + 1)) ℝ with hb_def
  obtain ⟨η₀, hη₀, hdec⟩ := exists_tiltDecayProp m b
  set θ := decayTheta m with hθ_def
  have hθ0 : 0 < θ := decayTheta_pos m
  have hθ1 : θ ≤ 1 / 10 := decayTheta_le m
  have hc0 := minimizerVolumeDensityConst_pos m
  have hr1 : 0 < 1 - Real.sqrt (1 / 2) := by linarith [sqrt_half_lt_one]
  -- the smallness conditions
  have hsq : Tendsto (fun ε : ℝ ↦ Real.sqrt (8 ^ m * ε)) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun ε : ℝ ↦ Real.sqrt (8 ^ m * ε)) := by fun_prop
    simpa using hc.tendsto (0 : ℝ)
  have hsq1 : Tendsto (fun ε : ℝ ↦ Real.sqrt ε) (𝓝 0) (𝓝 0) := by
    have := Real.continuous_sqrt.tendsto (0 : ℝ)
    simpa using this
  have hlin : Tendsto (fun ε : ℝ ↦ 8 ^ m * ε) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun ε : ℝ ↦ 8 ^ m * ε) := by fun_prop
    simpa using hc.tendsto (0 : ℝ)
  have hid : Tendsto (fun ε : ℝ ↦ ε) (𝓝 0) (𝓝 0) := tendsto_id
  have t1 : ∀ᶠ ε in 𝓝 (0 : ℝ), 8 ^ m * ε < η₀ := hlin.eventually (gt_mem_nhds hη₀)
  have t2 : ∀ᶠ ε in 𝓝 (0 : ℝ), 8 ^ m * ε < 1 := hlin.eventually (gt_mem_nhds one_pos)
  have t3 : ∀ᶠ ε in 𝓝 (0 : ℝ), ε < 1 := hid.eventually (gt_mem_nhds one_pos)
  have t4 : ∀ᶠ ε in 𝓝 (0 : ℝ), bandOscConst m * Real.sqrt (8 ^ m * ε) + 2 * 1 * (8 ^ m * ε) <
      minimizerVolumeDensityConst m * (1 / 4) ^ (m + 1) := by
    have h := (hsq.const_mul (bandOscConst m)).add (hlin.const_mul (2 * 1))
    simp only [mul_zero, add_zero] at h
    exact h.eventually (gt_mem_nhds (by positivity))
  have t5 : ∀ᶠ ε in 𝓝 (0 : ℝ), tiltConst m * Real.sqrt (8 ^ m * ε) / (1 - Real.sqrt (1 / 2)) <
      1 / 4 := by
    have h := (hsq.const_mul (tiltConst m)).div_const (1 - Real.sqrt (1 / 2))
    simp only [mul_zero, zero_div] at h
    exact h.eventually (gt_mem_nhds (by norm_num))
  have t6 : ∀ᶠ ε in 𝓝 (0 : ℝ), flatModulus m (8 ^ m * ε) 0 < θ / 128 := by
    have h1 := ((tendsto_flatBand m).comp hlin).const_mul 2
    have h2 := (hsq.const_mul (tiltConst m)).div_const (1 - Real.sqrt (1 / 2))
    have h := h1.add h2
    simp only [mul_zero, zero_div, add_zero] at h
    have h' : Tendsto (fun ε : ℝ ↦ flatModulus m (8 ^ m * ε) 0) (𝓝 0) (𝓝 0) := by
      refine h.congr fun ε ↦ ?_
      simp only [flatModulus, Function.comp_apply, pow_zero, div_one, mul_one]
    exact h'.eventually (gt_mem_nhds (by positivity))
  have t7 : ∀ᶠ ε in 𝓝 (0 : ℝ), bandOscConst m * Real.sqrt ε + 2 * 1 * ε <
      minimizerVolumeDensityConst m * (1 / 8) ^ (m + 1) := by
    have h := (hsq1.const_mul (bandOscConst m)).add (hid.const_mul (2 * 1))
    simp only [mul_zero, add_zero] at h
    exact h.eventually (gt_mem_nhds (by positivity))
  have t8 : ∀ᶠ ε in 𝓝 (0 : ℝ), flatBand m ε < 1 / 128 :=
    (tendsto_flatBand m).eventually (gt_mem_nhds (by norm_num))
  have hev := (eventually_mem_nhdsWithin (s := Ioi (0 : ℝ)) (a := 0)).and
    (nhdsWithin_le_nhds (t1.and (t2.and (t3.and (t4.and (t5.and (t6.and (t7.and t8))))))))
  obtain ⟨ε₀, hε₀, c1, c2, c3, c4, c5, c6, c7, c8⟩ := hev.exists
  have hε₀' : 0 < ε₀ := hε₀
  refine ⟨ε₀, hε₀', ?_⟩
  intro E Ω μ ν hF he x hx hxπ hxn
  set e := (projectedExcessMeasure μ ν).real (ball (0 : Space m) 2) with he_def
  have he0 : 0 ≤ e := measureReal_nonneg
  set η := 8 ^ m * ε₀ with hη_def
  -- the band of `E`
  have hsmall : bandOscConst m * Real.sqrt e + 2 * 1 * e <
      minimizerVolumeDensityConst m * (1 / 8) ^ (m + 1) := by
    have h1 := Real.sqrt_le_sqrt he
    have h2 := bandOscConst_nonneg m
    nlinarith
  obtain ⟨a, haδ, hband⟩ := hF.band (he.trans c3.le) hsmall
  set δ := flatBand m e with hδ_def
  have hδ : δ ≤ 1 / 128 := (flatBand_mono m he0 he).trans c8.le
  have hδ0 : 0 ≤ δ := flatBand_nonneg m he0
  have ha : |a| ≤ 1 / 2 := haδ.trans (by linarith)
  have hint : ∀ y, horizontal y ∈ ball (0 : Space m) (3 / 4) → a + δ < y (Fin.last m) →
      y (Fin.last m) < 1 → y ∈ measureTheoreticInterior E :=
    fun y hy h1 h2 ↦ hF.slab.mem_interior_of_band (convex_ball (0 : Space m) (3 / 4))
      (ball_subset_ball (by norm_num)) ha hδ0 hband hy h1 h2
  have hext : ∀ y, horizontal y ∈ ball (0 : Space m) (3 / 4) → -1 < y (Fin.last m) →
      y (Fin.last m) < a - δ → y ∈ measureTheoreticExterior E :=
    fun y hy h1 h2 ↦ hF.slab.mem_exterior_of_band (convex_ball (0 : Space m) (3 / 4))
      (ball_subset_ball (by norm_num)) ha hδ0 hband hy h1 h2
  -- the normals at the boundary points of the half cylinder
  have hnormal : ∀ p ∈ measureTheoreticBoundary E, horizontal p ∈ ball (0 : Space m) (1 / 2) →
      |p (Fin.last m)| < 1 / 2 → ∃ n : Space (m + 1), ‖n - verticalDirection m‖ ≤ 1 / 4 ∧
        ∀ k : ℕ, ∀ q ∈ measureTheoreticBoundary E, ‖q - p‖ ≤ θ ^ k / 32 →
          |inner ℝ (q - p) n| ≤ flatModulus m η k * θ ^ k / 8 := by
    intro p hp hpπ hpn
    obtain ⟨hFp, hep⟩ := hF.recenter haδ (by linarith) hband hp hpπ hpn
    have hepη : (projectedExcessMeasure ((similarityMeasure μ
        (LinearIsometryEquiv.refl ℝ (Space (m + 1))) p (1 / 8)).restrict
        (cylinderSet (ball (0 : Space m) 2) 1))
        (fun x ↦ (LinearIsometryEquiv.refl ℝ (Space (m + 1))).symm
          (ν (similarity (LinearIsometryEquiv.refl ℝ (Space (m + 1))) p (1 / 8) x)))).real
        (ball 0 2) ≤ η :=
      hep.trans (mul_le_mul_of_nonneg_left he (by positivity))
    obtain ⟨n, -, hn, hflat⟩ := hFp.exists_normal hdec hepη c1.le c2.le c4
    refine ⟨n, hn.trans c5.le, fun k q hq hqp ↦ ?_⟩
    set S := similarity (LinearIsometryEquiv.refl ℝ (Space (m + 1))) p (1 / 8) with hS_def
    set y := (8 : ℝ) • (q - p) with hy_def
    have hSy : S y = q := by
      simp only [hS_def, similarity, hy_def, LinearIsometryEquiv.coe_refl, id, smul_smul]
      norm_num
    have hyb : y ∈ measureTheoreticBoundary (S ⁻¹' E) := by
      rw [measureTheoreticBoundary_preimage_similarity E _ p (by norm_num : (0 : ℝ) < 1 / 8)]
      show S y ∈ measureTheoreticBoundary E
      rw [hSy]
      exact hq
    have hynorm : ‖y‖ ≤ θ ^ k / 4 := by
      rw [hy_def, norm_smul, Real.norm_of_nonneg (by norm_num)]
      linarith
    have h := hflat k y hyb hynorm
    rw [hy_def, real_inner_smul_left, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 8)] at h
    linarith
  have hη0 : 0 ≤ η := by positivity
  exact isC1BoundaryPoint_of_flat_normals hθ0 (by linarith) (flatModulus_nonneg m hη0)
    (fun k ↦ (flatModulus_anti m hη0 (Nat.zero_le k)).trans c6.le) (tendsto_flatModulus m η)
    haδ hδ hband hint hext hnormal hx hxπ hxn

end SerrinEpigraph
