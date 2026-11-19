module

public import SerrinEpigraph.DiffuseLayerHeights
public import SerrinEpigraph.PlaneTiltTranslatedPlanarLimit
public import SerrinEpigraph.HarmonicBadSetEnergy
public import SerrinEpigraph.HarmonicOneDimensionalLimit
public import SerrinEpigraph.SobolevBallCompactness

/-!
# Diffuse good layers: HA8, HA9 and HA2–HA3 for the rescaled solution

This file connects the function-theoretic level-height calculus of
`SerrinEpigraph.DiffuseLayerHeights` (McShane extension, change of variables, HA2 energy
identity, HA3 comparison) with the actual rescaled solution, following
`docs/rigidity-proof/harmonic-approximation.md`, sections HA1.2, HA2, HA3, HA8 and HA9.

## Coordinates and scales

The working coordinates are vertical: `x = point y t`, `y = horizontal x ∈ Space m`,
`t = x (Fin.last m)`. For a contradiction sequence of HA0 (free-boundary centers `c_j`, scales
`R_j → ∞`, directions `e_j`) the rescaled functions are
`v_j x = zeroExtension g u (c_j + R_j • Q_j x)` with linear isometries `Q_j` carrying
`verticalDirection m` to `e_j`, so that the HA0 tilt in direction `e_j` is the vertical tilt of
`v_j`. The diffuse parameter is `ε_j = R_j⁻¹`; densities are `diffuseTiltDensity (R j) (v j) _`.

## Results

* **HA8** (`VerticalPlanarLayers`, `RigidityHypotheses.verticalPlanarLayers_of_rotated`,
  `RigidityHypotheses.verticalPlanarLayers_of_translated`): if the unrotated rescalings converge
  locally in `L¹` to the half-space `{⟪e, y⟫ > 0}` and `Q_j (verticalDirection m) → e`, then on
  every bounded ball the values in each `[a, b] ⊆ (0, 1)` eventually lie in an arbitrarily thin
  horizontal slab, the region above the slab is uniformly close to `1`, and the region below it
  is identically `0`. Consequences: `VerticalPlanarLayers.eventually_exists_level_Icc` (every
  vertical line over a bounded ball crosses every level of `[a, b]` inside the slab) and
  `VerticalPlanarLayers.eventually_abs_lt_of_mem_Icc` (thin-layer containment).
* **HA9.e good points** (`IsLayerGoodPoint`, `layerGoodSet`, `goodProjection`,
  `verticalGoodSet`): an actual good point has value in `(0, 1 - b)` and normalized tilt
  `r⁻ᵐ ∫_{B_r(x)} ε (|∇v|² - (e·∇v)²) < ℓ` at every radius `0 < r ≤ r₀`; the good projection is
  the horizontal projection of the actual good points (not the complement of the projection of
  the bad points). For Lipschitz `v` both sets are open (`isOpen_layerGoodSet`,
  `isOpen_goodProjection`, via `isOpen_setOf_forall_setIntegral_ball_lt`), and they are nested
  in the thresholds (`layerGoodSet_mono`, `goodProjection_mono`).
* **HA1.2 on the good projection** (`exists_bad_radius_of_horizontal_notMem_goodProjection`,
  `volume_sdiff_goodProjection_le`,
  `VerticalPlanarLayers.eventually_volume_sdiff_goodProjection_le`): a point of the value window
  over the complement of the good projection is an actual bad point; with the HA8 crossings this
  gives `|B_s \ D| ≤ 5ᵐ |B₁| ℓ⁻¹ ∫_{B_{s+η+r₀}} ε |∇_y v|²` for any slab half-height `η > 0`.
* **HA9 microscopic limits** (`RigidityHypotheses.exists_oneDimensional_limit_at_good_points`):
  physical translates about good points with thresholds `ℓ_j → 0` converge, along a
  subsequence, to a `κ`-Lipschitz profile depending only on the coordinate along `e`, with all
  translation orders of the solution and `V 0 ∈ [0, 1 - b]`. This uses the scale invariance
  `setIntegral_ball_diffuseTiltDensity_rescaled` of the normalized tilt.
* **HA9.e transfer to nearby points** (`setIntegral_ball_lt_of_near`): radii `r ≥ ρ` at a point
  within `d` of a good point inherit the bound with the factor `(1 + d / ρ)ᵐ`.
* **No repeated layers on vertical lines of the original frame**
  (`Hypotheses.eq_of_zeroExtension_point_eq`, `Hypotheses.eq_of_rescaled_point_eq`), from the
  proved strict vertical monotonicity of the solution.
* **HA2.1 assembled** (`HasLevelCone`, `HasLevelSlope`, `slabLevelHeight`,
  `levelGraphFamily_slabLevelHeight`, `VerticalPlanarLayers.eventually_levelGraphFamily`):
  crossings, the HA9 cone condition, the microscopic slope bound and differentiability at level
  points give a `LevelGraphFamily` whose heights are the slab crossings `slabLevelHeight`.
* **Orientation of the layers** (`HasLevelSlopeAbs`, `hasLevelSlope_of_cone`,
  `VerticalPlanarLayers.eventually_hasLevelSlope_of_cone`): under HA8, uniqueness of the
  crossings (`HasLevelCone`) turns the unsigned bound `c ≤ |ε ∂ₜ v|` into `c ≤ ε ∂ₜ v`; no
  separate orientation argument is needed.
* **HA2.3 and HA3.1 along sequences** (`exists_normalizedHeight_limit`,
  `exists_normalizedHeight_limit_of_eventually`): with tilt budget `Θ δ_j²` and bad volume
  `M δ_j²`, the mean-value reference level `σ_j` and the center `a_j = ⨍_{B_ρ} h̃_{σ_j}` give
  normalized heights bounded in `W^{1,2}(B_ρ)` (`integral_sq_normalizedHeight_le_poincare`);
  a Rellich subsequence converges in `L²(B_r)`, `r < ρ`, to some `H`, and if `T_j δ_j → ∞` the
  normalized heights of every choice of levels `s_j ∈ [s₁, s₂]` (same centers) converge to `H`.
* **HA9.2 along sequences** (`tendsto_integral_sq_sub_div_of_near_good`): extensions built on
  different good sets have the same normalized limit.

## Interface for HA4–HA7, HA10–HA11

The assembled output is `RigidityHypotheses.exists_normalizedHeight_limit_of_cone` (general form
`VerticalPlanarLayers.exists_normalizedHeight_limit`). For the rotated rescalings `v_j`, with
`D_j = verticalGoodSet (R j) (v j) ℓ r₀ b ρ` and level heights `slabLevelHeight (v j) τ`, it
yields a subsequence `φ`, reference levels `σ_j ∈ [s₁, s₂]`, centers
`a_j = ⨍_{B_ρ} extendedHeight (D (φ j)) L τ s₁ s₂ _ (σ j)`, the explicit uniform `W^{1,2}(B_ρ)`
bound, and an `L²`-limit `H` shared by the normalized extended heights of all levels in
`[s₁, s₂]`. Its hypotheses supplied by HA11 are the half-space limit `hlocal` with
`Q_j (verticalDirection m) → e`, `δ_j → 0`, `R_j δ_j → ∞`, and the total tilt bound
`∫_{B_{ρ+τ+|r₀|}} ε |∇_y v_j|² ≤ Θ δ_j²` (for `ρ` slightly above `1` and small `τ`, `r₀` this
ball lies in the HA0 cylinder `Q_2`). The level graph family itself is available through
`VerticalPlanarLayers.eventually_levelGraphFamily` for the HA4 change of variables
(`LevelGraphFamily.lintegral_levelRegion_eq`, `LevelGraphFamily.horizontal_gradient_eq`).

## Not proved here

The two genuinely microscopic HA9 inputs remain hypotheses of the assembled statements:
`HasLevelCone (v j) (D j) τ s₁ s₂ L` (HA9.d: no repeated layers at all scales between `ε` and
`r₀`, which needs the classification HA9.a of one-dimensional profiles and the mesoscopic limits
HA9.b–HA9.c) and `HasLevelSlopeAbs (v j) (D j) τ s₁ s₂ (R j) c` (the unsigned bound
`|ε ∂ₜ v| ≥ c` at level points over the good projection: it needs microscopic `C¹` convergence
in the positive phase, e.g. via `semilinear_gradient_difference_sq_le`, and the vanishing of the
one-dimensional Hamiltonian, which gives `|q'| = √(2W)`). The microscopic part of the HA9.e
transfer (radii below `c_I ε`) is not formalized either.
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory Filter InnerProductSpace
open scoped Topology ENNReal NNReal

namespace SerrinEpigraph

/-! ### HA8 in vertical coordinates -/

/-- HA8 in vertical coordinates for a sequence of rescaled functions: on every bounded ball, the
values in each fixed interior interval are eventually trapped in an arbitrarily thin horizontal
slab, the region above the slab is eventually uniformly close to `1`, and the region below it is
eventually identically zero. -/
structure VerticalPlanarLayers {m : ℕ} (v : ℕ → Space (m + 1) → ℝ) : Prop where
  continuous : ∀ j, Continuous (v j)
  mem_Icc : ∀ j x, v j x ∈ Icc (0 : ℝ) 1
  levels : ∀ s δ a b : ℝ, 0 < δ → 0 < a → b < 1 →
    ∀ᶠ j in atTop, ∀ x ∈ closedBall (0 : Space (m + 1)) s,
      v j x ∈ Icc a b → |x (Fin.last m)| < δ
  upper : ∀ s δ η : ℝ, 0 < δ → 0 < η →
    ∀ᶠ j in atTop, ∀ x ∈ closedBall (0 : Space (m + 1)) s,
      δ ≤ x (Fin.last m) → 1 - η < v j x
  lower : ∀ s δ : ℝ, 0 < δ →
    ∀ᶠ j in atTop, ∀ x ∈ closedBall (0 : Space (m + 1)) s,
      x (Fin.last m) ≤ -δ → v j x = 0

/-- The normal coordinate after a rotation differs from the vertical coordinate by at most the
rotation defect times the norm. -/
theorem abs_inner_isometry_sub_last_le {m : ℕ} (Q : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1))
    (e x : Space (m + 1)) :
    |inner ℝ e (Q x) - x (Fin.last m)| ≤ ‖e - Q (verticalDirection m)‖ * ‖x‖ := by
  have hlast : x (Fin.last m) = inner ℝ (Q (verticalDirection m)) (Q x) := by
    rw [LinearIsometryEquiv.inner_map_map, real_inner_comm, inner_verticalDirection_right]
  rw [hlast, ← inner_sub_left]
  calc
    |inner ℝ (e - Q (verticalDirection m)) (Q x)| ≤ ‖e - Q (verticalDirection m)‖ * ‖Q x‖ :=
      abs_real_inner_le_norm _ _
    _ = ‖e - Q (verticalDirection m)‖ * ‖x‖ := by rw [LinearIsometryEquiv.norm_map]

/-- Eventually the rotation defect times a fixed radius is below any positive threshold. -/
theorem eventually_rotation_defect_mul_lt {m : ℕ} {Q : ℕ → Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1)}
    {e : Space (m + 1)} (hQ : Tendsto (fun j ↦ Q j (verticalDirection m)) atTop (𝓝 e))
    (s : ℝ) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ j in atTop, ‖e - Q j (verticalDirection m)‖ * |s| < η := by
  have hn : Tendsto (fun j ↦ ‖e - Q j (verticalDirection m)‖) atTop (𝓝 0) := by
    have := (tendsto_iff_norm_sub_tendsto_zero.mp hQ)
    simpa only [norm_sub_rev] using this
  have hpos : 0 < η / (|s| + 1) := by positivity
  filter_upwards [hn.eventually (gt_mem_nhds hpos)] with j hj
  have hs1 : |s| < |s| + 1 := lt_add_one _
  calc
    ‖e - Q j (verticalDirection m)‖ * |s| ≤ η / (|s| + 1) * |s| := by
      gcongr
    _ < η := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [abs_nonneg s]

theorem norm_le_abs_of_mem_closedBall {d : ℕ} {x : Space d} {s : ℝ}
    (hx : x ∈ closedBall (0 : Space d) s) : ‖x‖ ≤ |s| := by
  rw [mem_closedBall, dist_zero_right] at hx
  exact hx.trans (le_abs_self s)

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}

/-- **HA8 in rotated vertical coordinates.** Let `w_j y = zeroExtension g u (c_j + R_j • y)`
converge locally in `L¹` to the indicator of the half-space `{⟪e, y⟫ > 0}`, and let the rotations
`Q_j` carry the vertical direction to unit vectors converging to `e`. Then the rotated rescalings
`v_j x = zeroExtension g u (c_j + R_j • Q_j x)` have planar layers in vertical coordinates. -/
theorem RigidityHypotheses.verticalPlanarLayers_of_rotated
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hsharp : ∀ z : Space (m + 1), ∀ r : ℝ, 0 < r →
      (∫ x in closedBall z r, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤
        phasePrimitive f 1 * volume.real (closedBall (0 : Space m) 1) * r ^ m)
    (c : ℕ → Space (m + 1)) {R : ℕ → ℝ} (hR : ∀ j, 0 < R j) (hRt : Tendsto R atTop atTop)
    {e : Space (m + 1)} (he : ‖e‖ = 1)
    (hlocal : ∀ K : Set (Space (m + 1)), IsCompact K →
      Tendsto (fun j ↦ ∫ x in K, ‖zeroExtension g u (c j + R j • x) -
        {y : Space (m + 1) | 0 < inner ℝ e y}.indicator (fun _ ↦ (1 : ℝ)) x‖)
          atTop (𝓝 0))
    {Q : ℕ → Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1)}
    (hQ : Tendsto (fun j ↦ Q j (verticalDirection m)) atTop (𝓝 e)) :
    VerticalPlanarLayers (fun j x ↦ zeroExtension g u (c j + R j • Q j x)) where
  continuous j := h.zeroExtension_continuous.comp (by fun_prop)
  mem_Icc j x := ⟨h.zeroExtension_nonneg _, (hr.zeroExtension_lt_one _).le⟩
  levels s δ a b hδ ha hb := by
    have hδ2 : 0 < δ / 2 := half_pos hδ
    filter_upwards [hr.translated_eventually_interior_levels_in_planar_slab h hsharp c hR hRt he
      hlocal |s| hδ2 ha hb, eventually_rotation_defect_mul_lt hQ s hδ2] with j hj hdef
    intro x hx hval
    have hxn := norm_le_abs_of_mem_closedBall hx
    have hQx : Q j x ∈ closedBall (0 : Space (m + 1)) |s| := by
      rw [mem_closedBall, dist_zero_right, LinearIsometryEquiv.norm_map]
      exact hxn
    have h1 := hj (Q j x) hQx hval
    have h2 := abs_inner_isometry_sub_last_le (Q j) e x
    have h3 : ‖e - Q j (verticalDirection m)‖ * ‖x‖ ≤ ‖e - Q j (verticalDirection m)‖ * |s| :=
      mul_le_mul_of_nonneg_left hxn (norm_nonneg _)
    have h4 := abs_sub_abs_le_abs_sub (x (Fin.last m)) (inner ℝ e (Q j x))
    rw [abs_sub_comm] at h4
    linarith
  upper s δ η hδ hη := by
    have hδ2 : 0 < δ / 2 := half_pos hδ
    let K := closedBall (0 : Space (m + 1)) |s| ∩ {y | δ / 2 ≤ inner ℝ e y}
    have hK : IsCompact K := (isCompact_closedBall _ _).inter_right
      (isClosed_le continuous_const (continuous_const.inner continuous_id))
    have hpos : ∀ y ∈ K, 0 < inner ℝ e y := fun y hy ↦ hδ2.trans_le hy.2
    have hunif := Metric.tendstoUniformlyOn_iff.mp
      (hr.translated_tendstoUniformlyOn_one_positive_halfspace h hsharp c hR hRt he hlocal hK hpos)
      η hη
    filter_upwards [hunif, eventually_rotation_defect_mul_lt hQ s hδ2] with j hj hdef
    intro x hx hlast
    have hxn := norm_le_abs_of_mem_closedBall hx
    have hQx : Q j x ∈ closedBall (0 : Space (m + 1)) |s| := by
      rw [mem_closedBall, dist_zero_right, LinearIsometryEquiv.norm_map]
      exact hxn
    have h2 := abs_inner_isometry_sub_last_le (Q j) e x
    have h3 : ‖e - Q j (verticalDirection m)‖ * ‖x‖ ≤ ‖e - Q j (verticalDirection m)‖ * |s| :=
      mul_le_mul_of_nonneg_left hxn (norm_nonneg _)
    have hin : δ / 2 ≤ inner ℝ e (Q j x) := by
      have := (abs_le.mp h2).1
      linarith
    have h1 := hj (Q j x) ⟨hQx, hin⟩
    rw [Real.dist_eq] at h1
    have := (abs_lt.mp h1).2
    linarith
  lower s δ hδ := by
    have hδ2 : 0 < δ / 2 := half_pos hδ
    let K := closedBall (0 : Space (m + 1)) |s| ∩ {y | inner ℝ e y ≤ -(δ / 2)}
    have hK : IsCompact K := (isCompact_closedBall _ _).inter_right
      (isClosed_le (continuous_const.inner continuous_id) continuous_const)
    have hneg : ∀ y ∈ K, inner ℝ e y < 0 := fun y hy ↦ hy.2.trans_lt (by linarith)
    filter_upwards [hr.translated_eventually_eq_zero_negative_halfspace h hsharp c hR hRt he hlocal
      hK hneg, eventually_rotation_defect_mul_lt hQ s hδ2] with j hj hdef
    intro x hx hlast
    have hxn := norm_le_abs_of_mem_closedBall hx
    have hQx : Q j x ∈ closedBall (0 : Space (m + 1)) |s| := by
      rw [mem_closedBall, dist_zero_right, LinearIsometryEquiv.norm_map]
      exact hxn
    have h2 := abs_inner_isometry_sub_last_le (Q j) e x
    have h3 : ‖e - Q j (verticalDirection m)‖ * ‖x‖ ≤ ‖e - Q j (verticalDirection m)‖ * |s| :=
      mul_le_mul_of_nonneg_left hxn (norm_nonneg _)
    have hin : inner ℝ e (Q j x) ≤ -(δ / 2) := by
      have := (abs_le.mp h2).2
      linarith
    exact hj ⟨hQx, hin⟩

/-- The unrotated case: the vertical half-space limit gives vertical planar layers. -/
theorem RigidityHypotheses.verticalPlanarLayers_of_translated
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hsharp : ∀ z : Space (m + 1), ∀ r : ℝ, 0 < r →
      (∫ x in closedBall z r, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤
        phasePrimitive f 1 * volume.real (closedBall (0 : Space m) 1) * r ^ m)
    (c : ℕ → Space (m + 1)) {R : ℕ → ℝ} (hR : ∀ j, 0 < R j) (hRt : Tendsto R atTop atTop)
    (hlocal : ∀ K : Set (Space (m + 1)), IsCompact K →
      Tendsto (fun j ↦ ∫ x in K, ‖zeroExtension g u (c j + R j • x) -
        {y : Space (m + 1) | 0 < inner ℝ (verticalDirection m) y}.indicator
          (fun _ ↦ (1 : ℝ)) x‖) atTop (𝓝 0)) :
    VerticalPlanarLayers (fun j x ↦ zeroExtension g u (c j + R j • x)) := by
  have hv : ‖verticalDirection m‖ = 1 := by
    simp [verticalDirection]
  have hh := hr.verticalPlanarLayers_of_rotated h hsharp c hR hRt hv hlocal
    (Q := fun _ ↦ LinearIsometryEquiv.refl ℝ (Space (m + 1))) tendsto_const_nhds
  simpa using hh

/-! ### Crossing every interior level inside the thin slab -/

theorem norm_point_le (y : Space m) (t : ℝ) : ‖point y t‖ ≤ ‖y‖ + |t| := by
  have he : point y t = point y 0 + t • verticalDirection m := by
    rw [point_add_vertical, zero_add]
  have hv : ‖verticalDirection m‖ = 1 := by simp [verticalDirection]
  rw [he]
  calc
    ‖point y 0 + t • verticalDirection m‖ ≤ ‖point y 0‖ + ‖t • verticalDirection m‖ :=
      norm_add_le _ _
    _ = ‖y‖ + |t| := by rw [norm_point_zero, norm_smul, hv, mul_one, Real.norm_eq_abs]

namespace VerticalPlanarLayers

variable {v : ℕ → Space (m + 1) → ℝ}

/-- HA8 crossing, uniformly in the level: over every point of a bounded horizontal ball, each
value in a fixed interval `[a, b] ⊆ (0, 1)` is eventually attained inside the slab `|t| < δ`. -/
theorem eventually_exists_level_Icc (hV : VerticalPlanarLayers v) (s : ℝ) {δ a b : ℝ}
    (hδ : 0 < δ) (ha : 0 < a) (hb : b < 1) :
    ∀ᶠ j in atTop, ∀ y : Space m, ‖y‖ ≤ s → ∀ lam ∈ Icc a b,
      ∃ t ∈ Ioo (-δ) δ, v j (point y t) = lam := by
  have hδ2 : 0 < δ / 2 := half_pos hδ
  filter_upwards [hV.upper (s + δ) (δ / 2) (1 - b) hδ2 (by linarith),
    hV.lower (s + δ) (δ / 2) hδ2] with j hup hlow
  intro y hy lam hlam
  have hp : point y (δ / 2) ∈ closedBall (0 : Space (m + 1)) (s + δ) := by
    rw [mem_closedBall, dist_zero_right]
    have := norm_point_le y (δ / 2)
    rw [abs_of_pos hδ2] at this
    linarith
  have hq : point y (-(δ / 2)) ∈ closedBall (0 : Space (m + 1)) (s + δ) := by
    rw [mem_closedBall, dist_zero_right]
    have := norm_point_le y (-(δ / 2))
    rw [abs_neg, abs_of_pos hδ2] at this
    linarith
  have h1 : 1 - (1 - b) < v j (point y (δ / 2)) := hup _ hp (by simp)
  have h2 : v j (point y (-(δ / 2))) = 0 := hlow _ hq (by simp)
  have hcont : ContinuousOn (fun t ↦ v j (point y t)) (Icc (-(δ / 2)) (δ / 2)) :=
    ((hV.continuous j).comp (continuous_point y)).continuousOn
  obtain ⟨t, ht, hval⟩ := intermediate_value_Ioo (by linarith) hcont
    (show lam ∈ Ioo (v j (point y (-(δ / 2)))) (v j (point y (δ / 2))) from
      ⟨by rw [h2]; exact ha.trans_le hlam.1, by linarith [hlam.2]⟩)
  exact ⟨t, ⟨by linarith [ht.1], by linarith [ht.2]⟩, hval⟩

/-- HA8 crossing for one level `lam ∈ (0, 1)`. -/
theorem eventually_exists_level (hV : VerticalPlanarLayers v) (s : ℝ) {δ lam : ℝ} (hδ : 0 < δ)
    (hl0 : 0 < lam) (hl1 : lam < 1) :
    ∀ᶠ j in atTop, ∀ y : Space m, ‖y‖ ≤ s → ∃ t ∈ Ioo (-δ) δ, v j (point y t) = lam := by
  filter_upwards [hV.eventually_exists_level_Icc s hδ hl0 hl1] with j hj
  exact fun y hy ↦ hj y hy lam ⟨le_rfl, le_rfl⟩

/-- HA8 thin-layer containment over a horizontal ball: values in a fixed interior interval are
eventually attained only inside the slab `|t| < δ`. -/
theorem eventually_abs_lt_of_mem_Icc (hV : VerticalPlanarLayers v) (s : ℝ) {δ a b : ℝ}
    (hδ : 0 < δ) (ha : 0 < a) (hb : b < 1) :
    ∀ᶠ j in atTop, ∀ y : Space m, ‖y‖ ≤ s → ∀ t : ℝ, |t| ≤ s →
      v j (point y t) ∈ Icc a b → |t| < δ := by
  filter_upwards [hV.levels (2 * s) δ a b hδ ha hb] with j hj
  intro y hy t ht hval
  have hmem : point y t ∈ closedBall (0 : Space (m + 1)) (2 * s) := by
    rw [mem_closedBall, dist_zero_right]
    have := norm_point_le y t
    linarith
  simpa using hj _ hmem hval

end VerticalPlanarLayers

/-! ### Actual good points and the good projection (HA9.e) -/

/-- An actual good point of HA9.e at scale `T` (with `ε = T⁻¹`): its value lies in `(0, 1 - b)`
and the normalized tilt `r⁻ᵐ ∫_{B_r(x)} ε (|∇v|² - (e·∇v)²)` is strictly below `ℓ` at every
radius `0 < r ≤ r₀`. -/
def IsLayerGoodPoint (T : ℝ) (v : Space (m + 1) → ℝ) (e : Space (m + 1)) (ℓ r₀ b : ℝ)
    (x : Space (m + 1)) : Prop :=
  v x ∈ Ioo 0 (1 - b) ∧ ∀ r ∈ Ioc 0 r₀, ∫ y in ball x r, diffuseTiltDensity T v e y < ℓ * r ^ m

/-- The set `A_{ℓ,b}` of actual good points. -/
def layerGoodSet (T : ℝ) (v : Space (m + 1) → ℝ) (e : Space (m + 1)) (ℓ r₀ b : ℝ) :
    Set (Space (m + 1)) :=
  {x | IsLayerGoodPoint T v e ℓ r₀ b x}

/-- The good projection `D_{ℓ,b} = π(A_{ℓ,b})`: the horizontal projection of the actual good
points. It is *not* the complement of the projection of the bad points. -/
def goodProjection (T : ℝ) (v : Space (m + 1) → ℝ) (e : Space (m + 1)) (ℓ r₀ b : ℝ) :
    Set (Space m) :=
  horizontal '' layerGoodSet T v e ℓ r₀ b

theorem lipschitzWith_one_horizontal : LipschitzWith 1 (horizontal : Space (m + 1) → Space m) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
  have hlin : horizontal x - horizontal y = horizontal (x - y) :=
    (map_sub (horizontalContinuousLinearMap (m := m)) x y).symm
  rw [hlin]
  have h := norm_sq_eq_horizontal_add_last_sq (x - y)
  have h2 : ‖horizontal (x - y)‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
    nlinarith [sq_nonneg ((x - y) (Fin.last m))]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h2

theorem isOpenMap_horizontal : IsOpenMap (horizontal : Space (m + 1) → Space m) :=
  (horizontalContinuousLinearMap (m := m)).isOpenMap
    (fun y ↦ ⟨point y 0, horizontal_point y 0⟩)

/-! #### Ball integrals of bounded densities -/

section BallIntegral

variable {d : ℕ} {F : Space d → ℝ} {C : ℝ}

theorem integrableOn_ball_of_bounded (hFm : Measurable F) (hF0 : ∀ x, 0 ≤ F x)
    (hFC : ∀ x, F x ≤ C) (x : Space d) (r : ℝ) : IntegrableOn F (ball x r) := by
  refine Measure.integrableOn_of_bounded (M := C) measure_ball_lt_top.ne
    hFm.aestronglyMeasurable (Eventually.of_forall fun y ↦ ?_)
  rw [Real.norm_of_nonneg (hF0 y)]
  exact hFC y

theorem setIntegral_ball_le_mul_volume (hFm : Measurable F) (hF0 : ∀ x, 0 ≤ F x)
    (hFC : ∀ x, F x ≤ C) (x : Space d) (r : ℝ) :
    ∫ y in ball x r, F y ≤ C * volume.real (ball x r) := by
  have hi := integrableOn_ball_of_bounded hFm hF0 hFC x r
  calc
    ∫ y in ball x r, F y ≤ ∫ _ in ball x r, C :=
      setIntegral_mono hi (integrableOn_const measure_ball_lt_top.ne) hFC
    _ = C * volume.real (ball x r) := by rw [setIntegral_const, smul_eq_mul, mul_comm]

theorem setIntegral_ball_mono (hFm : Measurable F) (hF0 : ∀ x, 0 ≤ F x)
    (hFC : ∀ x, F x ≤ C) {x x' : Space d} {r r' : ℝ} (h : r + dist x x' ≤ r') :
    ∫ y in ball x r, F y ≤ ∫ y in ball x' r', F y :=
  setIntegral_mono_set (integrableOn_ball_of_bounded hFm hF0 hFC x' r')
    (Eventually.of_forall hF0) (Eventually.of_forall (ball_subset_ball' h))

theorem setIntegral_ball_le_add (hFm : Measurable F) (hF0 : ∀ x, 0 ≤ F x)
    (hFC : ∀ x, F x ≤ C) (x : Space d) {r r' : ℝ} (hrr' : r ≤ r') :
    ∫ y in ball x r', F y ≤
      (∫ y in ball x r, F y) + C * (volume.real (ball x r') - volume.real (ball x r)) := by
  have hsub : ball x r ⊆ ball x r' := ball_subset_ball hrr'
  have hdiff : ∫ y in ball x r' \ ball x r, F y =
      (∫ y in ball x r', F y) - ∫ y in ball x r, F y :=
    setIntegral_sdiff measurableSet_ball (integrableOn_ball_of_bounded hFm hF0 hFC x r') hsub
  have hvol : volume.real (ball x r' \ ball x r) =
      volume.real (ball x r') - volume.real (ball x r) :=
    measureReal_sdiff hsub measurableSet_ball measure_ball_lt_top.ne
  have hle : ∫ y in ball x r' \ ball x r, F y ≤ C * volume.real (ball x r' \ ball x r) := by
    have hi : IntegrableOn F (ball x r' \ ball x r) :=
      (integrableOn_ball_of_bounded hFm hF0 hFC x r').mono_set sdiff_subset
    calc
      ∫ y in ball x r' \ ball x r, F y ≤ ∫ _ in ball x r' \ ball x r, C :=
        setIntegral_mono hi (integrableOn_const
          ((measure_mono sdiff_subset).trans_lt measure_ball_lt_top).ne) hFC
      _ = C * volume.real (ball x r' \ ball x r) := by
        rw [setIntegral_const, smul_eq_mul, mul_comm]
  rw [hvol] at hle
  linarith

end BallIntegral

theorem volume_real_ball_eq_pow (x : Space (m + 1)) {r : ℝ} (hr : 0 ≤ r) :
    volume.real (ball x r) = r ^ (m + 1) * volume.real (ball (0 : Space (m + 1)) 1) := by
  rw [measureReal_def, measureReal_def, Measure.addHaar_ball volume x hr,
    finrank_euclideanSpace_fin, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]

theorem volume_real_ball_one_pos : 0 < volume.real (ball (0 : Space (m + 1)) 1) := by
  rw [measureReal_def]
  exact ENNReal.toReal_pos (measure_ball_pos volume _ one_pos).ne' measure_ball_lt_top.ne

theorem measurable_diffuseTiltDensity {d : ℕ} (T : ℝ) (v : Space d → ℝ) (e : Space d) :
    Measurable (diffuseTiltDensity T v e) := by
  unfold diffuseTiltDensity
  exact (((measurable_gradient v).norm.pow_const 2).sub
    (((measurable_gradient v).inner (𝕜 := ℝ) measurable_const).pow_const 2)).div_const T

theorem diffuseTiltDensity_le_of_lipschitzWith {d : ℕ} {T : ℝ} (hT : 0 < T) {v : Space d → ℝ}
    {K : ℝ≥0} (hv : LipschitzWith K v) (e x : Space d) :
    diffuseTiltDensity T v e x ≤ (K : ℝ) ^ 2 / T := by
  unfold diffuseTiltDensity
  have hg : ‖gradient v x‖ ≤ K := by
    rw [norm_gradient_eq_norm_fderiv]
    exact norm_fderiv_le_of_lipschitz ℝ hv
  apply div_le_div_of_nonneg_right _ hT.le
  have h2 : ‖gradient v x‖ ^ 2 ≤ (K : ℝ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hg 2
  nlinarith [sq_nonneg (inner ℝ (gradient v x) e)]

/-- Ball integrals of a bounded nonnegative density vary continuously with the radius. -/
theorem continuousOn_setIntegral_ball_radius {F : Space (m + 1) → ℝ} {C : ℝ}
    (hFm : Measurable F) (hF0 : ∀ x, 0 ≤ F x) (hFC : ∀ x, F x ≤ C) (hC : 0 ≤ C)
    (x₀ : Space (m + 1)) :
    ContinuousOn (fun r ↦ ∫ y in ball x₀ r, F y) (Ici 0) := by
  set ω := volume.real (ball (0 : Space (m + 1)) 1)
  have hω : 0 < ω := volume_real_ball_one_pos
  have hbound : ∀ r ∈ Ici (0 : ℝ), ∀ r' ∈ Ici (0 : ℝ),
      |(∫ y in ball x₀ r', F y) - ∫ y in ball x₀ r, F y| ≤
        C * ω * |r' ^ (m + 1) - r ^ (m + 1)| := by
    have key : ∀ a b : ℝ, 0 ≤ a → a ≤ b →
        |(∫ y in ball x₀ b, F y) - ∫ y in ball x₀ a, F y| ≤
          C * ω * |b ^ (m + 1) - a ^ (m + 1)| := by
      intro a b ha hab
      have hmono : ∫ y in ball x₀ a, F y ≤ ∫ y in ball x₀ b, F y :=
        setIntegral_ball_mono hFm hF0 hFC (by simpa using hab)
      have hadd := setIntegral_ball_le_add hFm hF0 hFC x₀ hab
      rw [volume_real_ball_eq_pow x₀ (ha.trans hab), volume_real_ball_eq_pow x₀ ha] at hadd
      have hpow : a ^ (m + 1) ≤ b ^ (m + 1) := pow_le_pow_left₀ ha hab _
      rw [abs_of_nonneg (sub_nonneg.mpr hmono), abs_of_nonneg (sub_nonneg.mpr hpow)]
      nlinarith
    intro r hr r' hr'
    rcases le_total r r' with h | h
    · exact key r r' hr h
    · rw [abs_sub_comm, abs_sub_comm (r' ^ (m + 1))]
      exact key r' r hr' h
  rw [Metric.continuousOn_iff]
  intro r hr ε hε
  have hcont : ContinuousAt (fun s : ℝ ↦ s ^ (m + 1)) r := (continuous_pow (m + 1)).continuousAt
  obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.mp hcont (ε / ((C + 1) * ω)) (by positivity)
  refine ⟨δ, hδ, fun r' hr' hd ↦ ?_⟩
  have h1 := hbound r hr r' hr'
  have h2 := hδ' hd
  rw [Real.dist_eq] at h2 ⊢
  have h3 : C * ω * |r' ^ (m + 1) - r ^ (m + 1)| ≤ (C + 1) * ω * |r' ^ (m + 1) - r ^ (m + 1)| := by
    gcongr
    linarith
  have h4 : (C + 1) * ω * |r' ^ (m + 1) - r ^ (m + 1)| < ε := by
    rw [lt_div_iff₀ (by positivity)] at h2
    linarith
  linarith

/-- **Openness of the strict good-ball condition (HA9.e).** For a bounded nonnegative density, the
centers whose ball integrals are strictly below `ℓ r^m` at every radius `0 < r ≤ r₀` form an open
set. Small radii are handled uniformly by the bound `∫_{B_r} F ≤ C |B_r|`, the remaining radii by
the positive margin on the compact range `[ρ₁, r₀]` and uniform continuity of `r ↦ r^(m+1)`. -/
theorem isOpen_setOf_forall_setIntegral_ball_lt {F : Space (m + 1) → ℝ} {C : ℝ}
    (hFm : Measurable F) (hF0 : ∀ x, 0 ≤ F x) (hFC : ∀ x, F x ≤ C) (ℓ r₀ : ℝ) :
    IsOpen {x : Space (m + 1) | ∀ r ∈ Ioc 0 r₀, ∫ y in ball x r, F y < ℓ * r ^ m} := by
  rw [Metric.isOpen_iff]
  intro x₀ hx₀
  by_cases hr₀ : r₀ ≤ 0
  · exact ⟨1, one_pos, fun x _ r hr ↦ absurd (hr.1.trans_le hr.2) (not_lt.mpr hr₀)⟩
  push Not at hr₀
  have hℓ : 0 < ℓ := by
    have h1 := hx₀ r₀ ⟨hr₀, le_rfl⟩
    have h2 : 0 ≤ ∫ y in ball x₀ r₀, F y :=
      setIntegral_nonneg measurableSet_ball (fun y _ ↦ hF0 y)
    have h3 : 0 < r₀ ^ m := pow_pos hr₀ m
    by_contra hn
    push Not at hn
    nlinarith
  set C' := max C 0 + 1 with hC'
  have hC'pos : 0 < C' := by positivity
  have hFC' : ∀ x, F x ≤ C' := fun x ↦
    (hFC x).trans ((le_max_left _ _).trans (le_add_of_nonneg_right zero_le_one))
  set ω := volume.real (ball (0 : Space (m + 1)) 1) with hωdef
  have hω : 0 < ω := volume_real_ball_one_pos
  set ρ₁ := min r₀ (ℓ / (2 * C' * ω)) with hρ₁
  have hρ₁pos : 0 < ρ₁ := lt_min hr₀ (by positivity)
  have hsmall : ∀ x : Space (m + 1), ∀ r ∈ Ioc 0 ρ₁, ∫ y in ball x r, F y < ℓ * r ^ m := by
    intro x r hr
    have h1 := setIntegral_ball_le_mul_volume hFm hF0 hFC' x r
    rw [volume_real_ball_eq_pow x hr.1.le] at h1
    have hrle : r ≤ ℓ / (2 * C' * ω) := hr.2.trans (min_le_right _ _)
    have h2 : C' * ω * r ≤ ℓ / 2 := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * C' * ω)] at hrle
      nlinarith
    have hrm : 0 < r ^ m := pow_pos hr.1 m
    calc
      ∫ y in ball x r, F y ≤ C' * (r ^ (m + 1) * ω) := h1
      _ = (C' * ω * r) * r ^ m := by ring
      _ ≤ (ℓ / 2) * r ^ m := by gcongr
      _ < ℓ * r ^ m := by nlinarith
  -- the positive margin on the remaining compact range of radii
  have hcontΦ : ContinuousOn (fun r ↦ ℓ * r ^ m - ∫ y in ball x₀ r, F y) (Icc ρ₁ r₀) := by
    apply ContinuousOn.sub (by fun_prop)
    exact (continuousOn_setIntegral_ball_radius hFm hF0 hFC' hC'pos.le x₀).mono
      (fun r hr ↦ hρ₁pos.le.trans hr.1)
  obtain ⟨rmin, hrmin, hmin⟩ := isCompact_Icc.exists_isMinOn
    (nonempty_Icc.mpr (min_le_left _ _)) hcontΦ
  set μ := ℓ * rmin ^ m - ∫ y in ball x₀ rmin, F y with hμdef
  have hμ : 0 < μ := by
    have := hx₀ rmin ⟨hρ₁pos.trans_le hrmin.1, hrmin.2⟩
    linarith
  have hmargin : ∀ r ∈ Icc ρ₁ r₀, (∫ y in ball x₀ r, F y) + μ ≤ ℓ * r ^ m := by
    intro r hr
    have := hmin hr
    simp only [mem_ofPred_eq] at this
    linarith
  -- uniform continuity of the ball volume
  have huc := isCompact_Icc.uniformContinuousOn_of_continuous
    ((continuous_pow (m + 1)).continuousOn (s := Icc (0 : ℝ) (r₀ + 1)))
  obtain ⟨η, hη, hηuc⟩ := Metric.uniformContinuousOn_iff.mp huc (μ / (C' * ω)) (by positivity)
  refine ⟨min η 1, lt_min hη one_pos, fun x hx r hr ↦ ?_⟩
  rcases le_or_gt r ρ₁ with hrρ | hrρ
  · exact hsmall x r ⟨hr.1, hrρ⟩
  · have hdd : dist x x₀ < min η 1 := hx
    have hdd0 : 0 ≤ dist x x₀ := dist_nonneg
    have h1 : ∫ y in ball x r, F y ≤ ∫ y in ball x₀ (r + dist x x₀), F y :=
      setIntegral_ball_mono hFm hF0 hFC' le_rfl
    have h2 := setIntegral_ball_le_add hFm hF0 hFC' x₀
      (le_add_of_nonneg_right hdd0 : r ≤ r + dist x x₀)
    rw [volume_real_ball_eq_pow x₀ (by linarith [hr.1]), volume_real_ball_eq_pow x₀ hr.1.le] at h2
    have h3 := hηuc (r + dist x x₀)
      ⟨by linarith [hr.1], by linarith [hr.2, min_le_right η 1]⟩ r
      ⟨hr.1.le, by linarith [hr.2]⟩
      (by rw [Real.dist_eq, add_sub_cancel_left, abs_of_nonneg hdd0]
          exact hdd.trans_le (min_le_left _ _))
    rw [Real.dist_eq] at h3
    have h4 : C' * ((r + dist x x₀) ^ (m + 1) * ω - r ^ (m + 1) * ω) < μ := by
      have h5 := (abs_lt.mp h3).2
      rw [lt_div_iff₀ (by positivity)] at h5
      nlinarith
    have h6 := hmargin r ⟨hrρ.le, hr.2⟩
    linarith

/-- The actual good set is open. -/
theorem isOpen_layerGoodSet {T : ℝ} (hT : 0 < T) {v : Space (m + 1) → ℝ} {K : ℝ≥0}
    (hv : LipschitzWith K v) {e : Space (m + 1)} (he : ‖e‖ = 1) (ℓ r₀ b : ℝ) :
    IsOpen (layerGoodSet T v e ℓ r₀ b) := by
  have h1 : IsOpen {x | v x ∈ Ioo 0 (1 - b)} := isOpen_Ioo.preimage hv.continuous
  have h2 := isOpen_setOf_forall_setIntegral_ball_lt (measurable_diffuseTiltDensity T v e)
    (diffuseTiltDensity_nonneg hT v he) (diffuseTiltDensity_le_of_lipschitzWith hT hv e) ℓ r₀
  exact h1.inter h2

/-- The good projection is open, hence measurable. -/
theorem isOpen_goodProjection {T : ℝ} (hT : 0 < T) {v : Space (m + 1) → ℝ} {K : ℝ≥0}
    (hv : LipschitzWith K v) {e : Space (m + 1)} (he : ‖e‖ = 1) (ℓ r₀ b : ℝ) :
    IsOpen (goodProjection T v e ℓ r₀ b) :=
  isOpenMap_horizontal _ (isOpen_layerGoodSet hT hv he ℓ r₀ b)

/-- Actual good sets shrink when the threshold `ℓ` decreases, the admissible radius `r₀` grows,
or the upper cut `b` grows (HA9.e nesting of good sets). -/
theorem layerGoodSet_mono {T : ℝ} {v : Space (m + 1) → ℝ} {e : Space (m + 1)}
    {ℓ ℓ' r₀ r₀' b b' : ℝ} (hℓ : ℓ ≤ ℓ') (hr : r₀' ≤ r₀) (hb : b' ≤ b) :
    layerGoodSet T v e ℓ r₀ b ⊆ layerGoodSet T v e ℓ' r₀' b' := by
  rintro x ⟨hval, hgood⟩
  refine ⟨⟨hval.1, hval.2.trans_le (by linarith)⟩, fun r hr' ↦ ?_⟩
  have h1 := hgood r ⟨hr'.1, hr'.2.trans hr⟩
  have h2 : ℓ * r ^ m ≤ ℓ' * r ^ m :=
    mul_le_mul_of_nonneg_right hℓ (pow_nonneg hr'.1.le m)
  linarith

theorem goodProjection_mono {T : ℝ} {v : Space (m + 1) → ℝ} {e : Space (m + 1)}
    {ℓ ℓ' r₀ r₀' b b' : ℝ} (hℓ : ℓ ≤ ℓ') (hr : r₀' ≤ r₀) (hb : b' ≤ b) :
    goodProjection T v e ℓ r₀ b ⊆ goodProjection T v e ℓ' r₀' b' :=
  image_mono (layerGoodSet_mono hℓ hr hb)

/-- A point in the value window whose projection misses the good projection is an actual bad
point: some admissible ball carries normalized tilt at least `ℓ`. -/
theorem exists_bad_radius_of_horizontal_notMem_goodProjection {T : ℝ} {v : Space (m + 1) → ℝ}
    {e : Space (m + 1)} {ℓ r₀ b : ℝ} {x : Space (m + 1)} (hx : v x ∈ Ioo 0 (1 - b))
    (hD : horizontal x ∉ goodProjection T v e ℓ r₀ b) :
    ∃ r ∈ Ioc 0 r₀, ℓ * r ^ m ≤ ∫ y in ball x r, diffuseTiltDensity T v e y := by
  by_contra hn
  push Not at hn
  exact hD ⟨x, ⟨hx, hn⟩, rfl⟩

/-- **HA1.2 for the good projection.** If every horizontal point of `B` lies under some point
in the value window whose admissible balls stay in the compact set `A`, then the part of `B`
outside the good projection has volume at most `5ᵐ |B₁| / ℓ` times the total tilt on `A`. -/
theorem volume_sdiff_goodProjection_le {T : ℝ} (hT : 0 < T) {v : Space (m + 1) → ℝ}
    (hv : LocallyLipschitz v) {e : Space (m + 1)} (he : ‖e‖ = 1) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (r₀ b : ℝ) {A : Set (Space (m + 1))} (hA : IsCompact A) {B : Set (Space m)}
    (hcross : ∀ y ∈ B, ∃ x : Space (m + 1), horizontal x = y ∧ v x ∈ Ioo 0 (1 - b) ∧
      ball x r₀ ⊆ A) :
    volume (B \ goodProjection T v e ℓ r₀ b) ≤
      (ENNReal.ofReal ((5 : ℝ) ^ m) * volume (ball (0 : Space m) 1) / ENNReal.ofReal ℓ) *
        ENNReal.ofReal (∫ x in A, diffuseTiltDensity T v e x) := by
  refine le_trans (measure_mono ?_)
    (measure_projected_tilt_bad_set_le lipschitzWith_one_horizontal hv he hT hA r₀ hℓ)
  rintro y ⟨hyB, hyD⟩
  obtain ⟨x, rfl, hxv, hxA⟩ := hcross y hyB
  obtain ⟨r, hr, hbad⟩ := exists_bad_radius_of_horizontal_notMem_goodProjection hxv hyD
  exact ⟨x, ⟨r, hr.1, hr.2, (ball_subset_ball hr.2).trans hxA, hbad⟩, rfl⟩

/-- **HA1.2 + HA8 for a sequence.** Under vertical planar layers, eventually the complement of the
good projection in a horizontal ball `B_s` is controlled by the tilt on the ball of radius
`|s| + η + |r₀|`, for any slab half-height `η > 0` (the crossing points used lie in `|t| < η`). -/
theorem VerticalPlanarLayers.eventually_volume_sdiff_goodProjection_le
    {v : ℕ → Space (m + 1) → ℝ} (hV : VerticalPlanarLayers v) {T : ℕ → ℝ} (hT : ∀ j, 0 < T j)
    (hv : ∀ j, LocallyLipschitz (v j)) {e : Space (m + 1)} (he : ‖e‖ = 1) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (r₀ : ℝ) {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1) (s : ℝ) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ j in atTop, volume (closedBall (0 : Space m) s \ goodProjection (T j) (v j) e ℓ r₀ b) ≤
      (ENNReal.ofReal ((5 : ℝ) ^ m) * volume (ball (0 : Space m) 1) / ENNReal.ofReal ℓ) *
        ENNReal.ofReal (∫ x in closedBall (0 : Space (m + 1)) (|s| + η + |r₀|),
          diffuseTiltDensity (T j) (v j) e x) := by
  have hl0 : 0 < (1 - b) / 2 := by linarith
  have hl1 : (1 - b) / 2 < 1 := by linarith
  filter_upwards [hV.eventually_exists_level |s| hη hl0 hl1] with j hj
  apply volume_sdiff_goodProjection_le (hT j) (hv j) he hℓ r₀ b (isCompact_closedBall _ _)
  intro y hy
  have hyn : ‖y‖ ≤ |s| := norm_le_abs_of_mem_closedBall hy
  obtain ⟨t, ht, hval⟩ := hj y hyn
  refine ⟨point y t, horizontal_point y t, ?_, ?_⟩
  · rw [hval]
    exact ⟨hl0, by linarith⟩
  · intro z hz
    rw [mem_closedBall, dist_zero_right]
    rw [mem_ball] at hz
    have h1 := norm_point_le y t
    have h2 : ‖z‖ ≤ ‖point y t‖ + dist z (point y t) := by
      calc
        ‖z‖ = ‖(z - point y t) + point y t‖ := by rw [sub_add_cancel]
        _ ≤ ‖z - point y t‖ + ‖point y t‖ := norm_add_le _ _
        _ = ‖point y t‖ + dist z (point y t) := by rw [dist_eq_norm, add_comm]
    have h3 : |t| < η := abs_lt.mpr ⟨ht.1, ht.2⟩
    have h4 : r₀ ≤ |r₀| := le_abs_self r₀
    linarith

/-! ### From the HA9 graph conditions to the HA2 input -/

/-- **HA9.d output (cone condition).** Over `D`, inside the slab `|t| < τ`, any two points with
the same value `s ∈ [s₁, s₂]` satisfy `|t - t'| ≤ L |y - y'|`. In particular each such level is
crossed at most once on each vertical line over `D`. -/
def HasLevelCone (v : Space (m + 1) → ℝ) (D : Set (Space m)) (τ s₁ s₂ : ℝ) (L : ℝ≥0) : Prop :=
  ∀ s ∈ Icc s₁ s₂, ∀ y ∈ D, ∀ y' ∈ D, ∀ t ∈ Ioo (-τ) τ, ∀ t' ∈ Ioo (-τ) τ,
    v (point y t) = s → v (point y' t') = s → |t - t'| ≤ L * dist y y'

/-- **HA9/HA11 output (microscopic slope).** At every point over `D` in the slab whose value lies
in `[s₁, s₂]`, the diffuse vertical derivative `T⁻¹ ∂ₜ v` is at least `c`. -/
def HasLevelSlope (v : Space (m + 1) → ℝ) (D : Set (Space m)) (τ s₁ s₂ T c : ℝ) : Prop :=
  ∀ s ∈ Icc s₁ s₂, ∀ y ∈ D, ∀ t ∈ Ioo (-τ) τ, v (point y t) = s →
    c ≤ T⁻¹ * verticalDerivative v (point y t)

open scoped Classical in
/-- The level height: the crossing of the level `s` in the slab `|t| < τ` above `y`, when one
exists (chosen; it is unique under `HasLevelCone`), and `0` otherwise. -/
def slabLevelHeight (v : Space (m + 1) → ℝ) (τ s : ℝ) (y : Space m) : ℝ :=
  if hy : ∃ t ∈ Ioo (-τ) τ, v (point y t) = s then hy.choose else 0

theorem slabLevelHeight_spec {v : Space (m + 1) → ℝ} {τ s : ℝ} {y : Space m}
    (hy : ∃ t ∈ Ioo (-τ) τ, v (point y t) = s) :
    slabLevelHeight v τ s y ∈ Ioo (-τ) τ ∧ v (point y (slabLevelHeight v τ s y)) = s := by
  unfold slabLevelHeight
  split_ifs
  exact hy.choose_spec

/-- **HA2.1 assembled.** Crossings in the slab, the HA9 cone condition, the microscopic slope
bound, and differentiability at level points give the level graph family of HA2, with the chosen
level heights `slabLevelHeight v τ s`. -/
theorem levelGraphFamily_slabLevelHeight {v : Space (m + 1) → ℝ} (hv : Continuous v)
    {D : Set (Space m)} {τ s₁ s₂ T c : ℝ} {L : ℝ≥0}
    (hcross : ∀ s ∈ Icc s₁ s₂, ∀ y ∈ D, ∃ t ∈ Ioo (-τ) τ, v (point y t) = s)
    (hcone : HasLevelCone v D τ s₁ s₂ L) (hslope : HasLevelSlope v D τ s₁ s₂ T c)
    (hdiff : ∀ s ∈ Icc s₁ s₂, ∀ y ∈ D, ∀ t ∈ Ioo (-τ) τ, v (point y t) = s →
      DifferentiableAt ℝ v (point y t)) :
    LevelGraphFamily v D τ s₁ s₂ T c L (fun s y ↦ slabLevelHeight v τ s y) where
  continuous := hv
  mem_slab s hs y hy := (slabLevelHeight_spec (hcross s hs y hy)).1
  level s hs y hy := (slabLevelHeight_spec (hcross s hs y hy)).2
  unique s hs y hy t ht hvt := by
    have hspec := slabLevelHeight_spec (hcross s hs y hy)
    have hh := hcone s hs y hy y hy t ht _ hspec.1 hvt hspec.2
    rw [dist_self, mul_zero] at hh
    exact sub_eq_zero.mp (abs_nonpos_iff.mp hh)
  lipschitzOnWith s hs := by
    apply LipschitzOnWith.of_dist_le_mul
    intro y hy y' hy'
    have h1 := slabLevelHeight_spec (hcross s hs y hy)
    have h2 := slabLevelHeight_spec (hcross s hs y' hy')
    rw [Real.dist_eq]
    exact hcone s hs y hy y' hy' _ h1.1 _ h2.1 h1.2 h2.2
  differentiableAt s hs y hy := by
    have h1 := slabLevelHeight_spec (hcross s hs y hy)
    exact hdiff s hs y hy _ h1.1 h1.2
  vertical_lower s hs y hy := by
    have h1 := slabLevelHeight_spec (hcross s hs y hy)
    exact hslope s hs y hy _ h1.1 h1.2

/-- **HA2.1 for a sequence with planar layers.** Eventually, on every horizontal set inside a
fixed ball on which the cone and slope conditions hold, the chosen level heights form a level
graph family. Crossings come from HA8; differentiability holds at all positive values. -/
theorem VerticalPlanarLayers.eventually_levelGraphFamily {v : ℕ → Space (m + 1) → ℝ}
    (hV : VerticalPlanarLayers v) (hdiff : ∀ j x, 0 < v j x → DifferentiableAt ℝ (v j) x)
    (ρ : ℝ) {τ s₁ s₂ c : ℝ} (hτ : 0 < τ) (hs₁ : 0 < s₁) (hs₂ : s₂ < 1) (T : ℕ → ℝ)
    (L : ℝ≥0) :
    ∀ᶠ j in atTop, ∀ D ⊆ closedBall (0 : Space m) ρ,
      HasLevelCone (v j) D τ s₁ s₂ L → HasLevelSlope (v j) D τ s₁ s₂ (T j) c →
        LevelGraphFamily (v j) D τ s₁ s₂ (T j) c L (fun s y ↦ slabLevelHeight (v j) τ s y) := by
  filter_upwards [hV.eventually_exists_level_Icc ρ hτ hs₁ hs₂] with j hj
  intro D hD hcone hslope
  refine levelGraphFamily_slabLevelHeight (hV.continuous j) ?_ hcone hslope ?_
  · intro s hs y hy
    have hyn : ‖y‖ ≤ ρ := by
      have := hD hy
      rwa [mem_closedBall, dist_zero_right] at this
    exact hj y hyn s hs
  · intro s hs y hy t ht hvt
    exact hdiff j _ (by rw [hvt]; exact hs₁.trans_le hs.1)

/-! #### The sign of the slope comes from uniqueness of the crossings -/

/-- **Unsigned microscopic slope.** At every point over `D` in the slab whose value lies in
`[s₁, s₂]`, the diffuse vertical derivative satisfies `c ≤ |T⁻¹ ∂ₜ v|`. This is what the
one-dimensional microscopic limits give directly (`|q'| = √(2W)` on the profile); the sign is
recovered from `HasLevelCone` and HA8 by `hasLevelSlope_of_cone`. -/
def HasLevelSlopeAbs (v : Space (m + 1) → ℝ) (D : Set (Space m)) (τ s₁ s₂ T c : ℝ) : Prop :=
  ∀ s ∈ Icc s₁ s₂, ∀ y ∈ D, ∀ t ∈ Ioo (-τ) τ, v (point y t) = s →
    c ≤ |T⁻¹ * verticalDerivative v (point y t)|

theorem HasLevelSlope.hasLevelSlopeAbs {v : Space (m + 1) → ℝ} {D : Set (Space m)}
    {τ s₁ s₂ T c : ℝ} (h : HasLevelSlope v D τ s₁ s₂ T c) : HasLevelSlopeAbs v D τ s₁ s₂ T c :=
  fun s hs y hy t ht hvt ↦ (h s hs y hy t ht hvt).trans (le_abs_self _)

/-- A function crossing the value `s` at `t₀` for the last time before `b`, with `s < F b`, has
nonnegative derivative at `t₀`. -/
theorem nonneg_of_hasDerivAt_of_unique_crossing {F : ℝ → ℝ} {t₀ b s F' : ℝ}
    (hF : ContinuousOn F (Icc t₀ b)) (ht₀b : t₀ < b) (hFt₀ : F t₀ = s) (hFb : s < F b)
    (huniq : ∀ t ∈ Ioc t₀ b, F t ≠ s) (hd : HasDerivAt F F' t₀) : 0 ≤ F' := by
  have habove : ∀ t ∈ Ioc t₀ b, s < F t := by
    intro t ht
    by_contra hn
    push Not at hn
    have hlt : F t < s := lt_of_le_of_ne hn (huniq t ht)
    obtain ⟨t₂, ht₂, hFt₂⟩ := intermediate_value_Icc ht.2 (hF.mono (Icc_subset_Icc ht.1.le le_rfl))
      (show s ∈ Icc (F t) (F b) from ⟨hlt.le, hFb.le⟩)
    exact huniq t₂ ⟨ht.1.trans_le ht₂.1, ht₂.2⟩ hFt₂
  have hslope : Tendsto (slope F t₀) (𝓝[>] t₀) (𝓝 F') :=
    (hasDerivAt_iff_tendsto_slope.mp hd).mono_left
      (nhdsWithin_mono _ fun t ht ↦ ne_of_gt ht)
  refine ge_of_tendsto hslope ?_
  filter_upwards [Ioo_mem_nhdsGT ht₀b] with t ht
  rw [slope_def_field]
  have h1 := habove t ⟨ht.1, ht.2.le⟩
  exact div_nonneg (by rw [hFt₀]; linarith) (by linarith [ht.1])

/-- **The sign of the slope.** If the level crossings over `D` are unique (`HasLevelCone`), every
level point lies below the height `δ' < τ`, and the value at height `δ'` exceeds `s₂`, then the
unsigned slope bound is a signed one: `v` increases through each of its levels. -/
theorem hasLevelSlope_of_cone {v : Space (m + 1) → ℝ} (hv : Continuous v) {D : Set (Space m)}
    {τ s₁ s₂ T c δ' : ℝ} {L : ℝ≥0} (hT : 0 < T) (hδ' : δ' < τ)
    (hcone : HasLevelCone v D τ s₁ s₂ L) (habs : HasLevelSlopeAbs v D τ s₁ s₂ T c)
    (hdiff : ∀ s ∈ Icc s₁ s₂, ∀ y ∈ D, ∀ t ∈ Ioo (-τ) τ, v (point y t) = s →
      DifferentiableAt ℝ v (point y t))
    (hupper : ∀ y ∈ D, s₂ < v (point y δ'))
    (hslab : ∀ s ∈ Icc s₁ s₂, ∀ y ∈ D, ∀ t ∈ Ioo (-τ) τ, v (point y t) = s → t < δ') :
    HasLevelSlope v D τ s₁ s₂ T c := by
  intro s hs y hy t ht hvt
  have htδ := hslab s hs y hy t ht hvt
  have huniq : ∀ t' ∈ Ioc t δ', v (point y t') ≠ s := by
    intro t' ht' hvt'
    have ht'slab : t' ∈ Ioo (-τ) τ := ⟨ht.1.trans ht'.1, ht'.2.trans_lt hδ'⟩
    have hh := hcone s hs y hy y hy t ht t' ht'slab hvt hvt'
    rw [dist_self, mul_zero] at hh
    have := abs_nonpos_iff.mp hh
    linarith [ht'.1]
  have hd := hasDerivAt_vertical_section (hdiff s hs y hy t ht hvt)
  have hnonneg := nonneg_of_hasDerivAt_of_unique_crossing
    ((hv.comp (continuous_point y)).continuousOn) htδ hvt
    ((hs.2.trans_lt (hupper y hy))) huniq hd
  have habs' := habs s hs y hy t ht hvt
  rwa [abs_of_nonneg (mul_nonneg (inv_nonneg.mpr hT.le) hnonneg)] at habs'

/-- **The sign of the slope for a sequence with planar layers.** Eventually, on every horizontal
set inside a fixed ball, the cone condition and the unsigned slope bound give the signed one. -/
theorem VerticalPlanarLayers.eventually_hasLevelSlope_of_cone {v : ℕ → Space (m + 1) → ℝ}
    (hV : VerticalPlanarLayers v) (hdiff : ∀ j x, 0 < v j x → DifferentiableAt ℝ (v j) x)
    {ρ τ s₁ s₂ c : ℝ} (hτ : 0 < τ) (hs₁ : 0 < s₁) (hs₂ : s₂ < 1) {T : ℕ → ℝ}
    (hT : ∀ j, 0 < T j) (L : ℝ≥0) :
    ∀ᶠ j in atTop, ∀ D ⊆ closedBall (0 : Space m) ρ,
      HasLevelCone (v j) D τ s₁ s₂ L → HasLevelSlopeAbs (v j) D τ s₁ s₂ (T j) c →
        HasLevelSlope (v j) D τ s₁ s₂ (T j) c := by
  have hτ2 : 0 < τ / 2 := half_pos hτ
  filter_upwards [hV.upper (ρ + τ) (τ / 2) (1 - s₂) hτ2 (by linarith),
    hV.levels (ρ + τ) (τ / 2) s₁ s₂ hτ2 hs₁ hs₂] with j hup hlev
  intro D hD hcone habs
  have hyn : ∀ y ∈ D, ‖y‖ ≤ ρ := by
    intro y hy
    have := hD hy
    rwa [mem_closedBall, dist_zero_right] at this
  refine hasLevelSlope_of_cone (hV.continuous j) (hT j) (by linarith : τ / 2 < τ) hcone habs
    ?_ ?_ ?_
  · intro s hs y hy t ht hvt
    exact hdiff j _ (by rw [hvt]; exact hs₁.trans_le hs.1)
  · intro y hy
    have hmem : point y (τ / 2) ∈ closedBall (0 : Space (m + 1)) (ρ + τ) := by
      rw [mem_closedBall, dist_zero_right]
      have h1 := norm_point_le y (τ / 2)
      rw [abs_of_pos hτ2] at h1
      linarith [hyn y hy]
    have h2 := hup _ hmem (by simp)
    linarith
  · intro s hs y hy t ht hvt
    have hmem : point y t ∈ closedBall (0 : Space (m + 1)) (ρ + τ) := by
      rw [mem_closedBall, dist_zero_right]
      have h1 := norm_point_le y t
      have h2 : |t| < τ := abs_lt.mpr ⟨ht.1, ht.2⟩
      linarith [hyn y hy]
    have h3 := hlev _ hmem (by rw [hvt]; exact hs)
    simp only [last_point] at h3
    exact (abs_lt.mp h3).2

/-! #### The actual solution: differentiability and vertical uniqueness -/

/-- The zero extension is differentiable at every point of its positive phase. -/
theorem Hypotheses.differentiableAt_zeroExtension_of_pos (h : Hypotheses g u f κ)
    {x : Space (m + 1)} (hx : 0 < zeroExtension g u x) :
    DifferentiableAt ℝ (zeroExtension g u) x := by
  have hxi := (h.zeroExtension_pos_iff x).mp hx
  have hd : DifferentiableAt ℝ u x :=
    (h.solution_contDiffOn.differentiableOn (by norm_num) x hxi).differentiableAt
      ((isOpen_epigraph h.graph_contDiff.continuous).mem_nhds hxi)
  exact hd.congr_of_eventuallyEq (zeroExtension_eventuallyEq h.graph_contDiff.continuous hxi)

/-- Rotated rescalings of the zero extension are differentiable wherever they are positive. -/
theorem Hypotheses.differentiableAt_rescaled_of_pos (h : Hypotheses g u f κ)
    (c : Space (m + 1)) (R : ℝ) (Q : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1)) {x : Space (m + 1)}
    (hx : 0 < zeroExtension g u (c + R • Q x)) :
    DifferentiableAt ℝ (fun y ↦ zeroExtension g u (c + R • Q y)) x := by
  have hU := h.differentiableAt_zeroExtension_of_pos hx
  have hA : DifferentiableAt ℝ (fun y : Space (m + 1) ↦ c + R • Q y) x := by fun_prop
  exact hU.comp x hA

theorem add_smul_point (c : Space (m + 1)) (R : ℝ) (y : Space m) (t : ℝ) :
    c + R • point y t = point (horizontal c + R • y) (c (Fin.last m) + R * t) := by
  ext i
  refine Fin.lastCases ?_ (fun k ↦ ?_) i
  · simp [point]
  · simp [point, horizontal]

/-- **No repeated layers along vertical lines, in the original frame.** By the strict vertical
monotonicity of the solution, two points on one vertical line with the same positive value
coincide. -/
theorem Hypotheses.eq_of_zeroExtension_point_eq (h : Hypotheses g u f κ) {y : Space m}
    {t t' : ℝ} (hpos : 0 < zeroExtension g u (point y t))
    (heq : zeroExtension g u (point y t) = zeroExtension g u (point y t')) : t = t' := by
  have hpos' : 0 < zeroExtension g u (point y t') := heq ▸ hpos
  have h1 := (h.zeroExtension_pos_iff _).mp hpos
  have h2 := (h.zeroExtension_pos_iff _).mp hpos'
  have h1' : t ∈ Ioi (g y) := by simpa [epigraph] using h1
  have h2' : t' ∈ Ioi (g y) := by simpa [epigraph] using h2
  rw [zeroExtension_of_mem h1, zeroExtension_of_mem h2] at heq
  exact (h.vertical_section_strictMonoOn y).injOn h1' h2' heq

/-- The same uniqueness for unrotated rescalings with positive scale. -/
theorem Hypotheses.eq_of_rescaled_point_eq (h : Hypotheses g u f κ) (c : Space (m + 1))
    {R : ℝ} (hR : 0 < R) {y : Space m} {t t' : ℝ}
    (hpos : 0 < zeroExtension g u (c + R • point y t))
    (heq : zeroExtension g u (c + R • point y t) = zeroExtension g u (c + R • point y t')) :
    t = t' := by
  rw [add_smul_point] at hpos heq
  rw [add_smul_point] at heq
  have := h.eq_of_zeroExtension_point_eq hpos heq
  have hR' : R ≠ 0 := hR.ne'
  have : R * t = R * t' := by linarith
  exact mul_left_cancel₀ hR' this

/-! ### HA2–HA3 along a sequence -/

theorem integrableOn_ball_of_continuous' {d : ℕ} {F : Space d → ℝ} (hF : Continuous F)
    (x : Space d) (r : ℝ) : IntegrableOn F (ball x r) :=
  (hF.continuousOn.integrableOn_compact (isCompact_closedBall x r)).mono_set ball_subset_closedBall

theorem memLp_two_ball_of_continuous' {d : ℕ} {F : Space d → ℝ} (hF : Continuous F)
    (x : Space d) (r : ℝ) : MemLp F 2 (volume.restrict (ball x r)) := by
  rw [memLp_two_iff_integrable_sq hF.aestronglyMeasurable]
  exact integrableOn_ball_of_continuous' (hF.pow 2) x r

theorem integrableOn_norm_fderiv_sq_of_lipschitzWith {d : ℕ} {F : Space d → ℝ} {K : ℝ≥0}
    (hF : LipschitzWith K F) (x : Space d) (r : ℝ) :
    IntegrableOn (fun y ↦ ‖fderiv ℝ F y‖ ^ 2) (ball x r) := by
  refine Measure.integrableOn_of_bounded (M := (K : ℝ) ^ 2) measure_ball_lt_top.ne
    ((measurable_fderiv ℝ F).norm.pow_const 2).aestronglyMeasurable
    (Eventually.of_forall fun y ↦ ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_fderiv_le_of_lipschitz ℝ hF) 2

theorem normalizedHeight_lipschitzWith {φ : Space m → ℝ} {K : ℝ≥0} (hφ : LipschitzWith K φ)
    (a : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    LipschitzWith (K * Real.toNNReal δ⁻¹) (normalizedHeight φ a δ) := by
  apply LipschitzWith.of_dist_le_mul
  intro y z
  simp only [normalizedHeight, Real.dist_eq]
  rw [← sub_div, sub_sub_sub_cancel_right, abs_div, abs_of_pos hδ]
  have h1 := hφ.dist_le_mul y z
  rw [Real.dist_eq] at h1
  push_cast
  rw [Real.coe_toNNReal _ (inv_nonneg.mpr hδ.le), div_eq_mul_inv]
  have hδi : 0 ≤ δ⁻¹ := inv_nonneg.mpr hδ.le
  nlinarith

theorem norm_fderiv_normalizedHeight_sq (φ : Space m → ℝ) (a : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (y : Space m) :
    ‖fderiv ℝ (normalizedHeight φ a δ) y‖ ^ 2 = δ⁻¹ ^ 2 * ‖fderiv ℝ φ y‖ ^ 2 := by
  rw [← norm_gradient_eq_norm_fderiv, ← norm_gradient_eq_norm_fderiv, gradient_normalizedHeight,
    norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hδ), mul_pow]

/-- **Poincaré for the normalized height.** With the ball average of a Lipschitz height as its
center, the normalized height satisfies `∫_{B_ρ} H² ≤ 2^(m+1) ρ² ∫_{B_ρ} |∇H|²`. -/
theorem integral_sq_normalizedHeight_le_poincare {φ : Space m → ℝ} {K : ℝ≥0}
    (hφ : LipschitzWith K φ) {ρ δ : ℝ} (hρ : 0 < ρ) (hδ : 0 < δ) :
    ∫ y in ball (0 : Space m) ρ,
        normalizedHeight φ (⨍ z in ball (0 : Space m) ρ, φ z) δ y ^ 2 ≤
      2 ^ (m + 1) * ρ ^ 2 * ∫ y in ball (0 : Space m) ρ,
        ‖fderiv ℝ (normalizedHeight φ (⨍ z in ball (0 : Space m) ρ, φ z) δ) y‖ ^ 2 := by
  set a := ⨍ z in ball (0 : Space m) ρ, φ z
  have hP := poincare_ball (0 : Space m) hρ hφ
  have h1 : ∫ y in ball (0 : Space m) ρ, normalizedHeight φ a δ y ^ 2 =
      δ⁻¹ ^ 2 * ∫ y in ball (0 : Space m) ρ, (φ y - a) ^ 2 := by
    rw [← integral_const_mul]
    congr 1
    funext y
    rw [normalizedHeight, div_eq_inv_mul, mul_pow]
  have h2 : ∫ y in ball (0 : Space m) ρ, ‖fderiv ℝ (normalizedHeight φ a δ) y‖ ^ 2 =
      δ⁻¹ ^ 2 * ∫ y in ball (0 : Space m) ρ, ‖fderiv ℝ φ y‖ ^ 2 := by
    rw [← integral_const_mul]
    congr 1
    funext y
    exact norm_fderiv_normalizedHeight_sq φ a hδ y
  rw [h1, h2]
  have hδ2 : 0 ≤ δ⁻¹ ^ 2 := sq_nonneg _
  calc
    δ⁻¹ ^ 2 * ∫ y in ball (0 : Space m) ρ, (φ y - a) ^ 2 ≤
        δ⁻¹ ^ 2 * (2 ^ (m + 1) * ρ ^ 2 * ∫ y in ball (0 : Space m) ρ, ‖fderiv ℝ φ y‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hP hδ2
    _ = _ := by ring

namespace LevelGraphFamily

variable {v : Space (m + 1) → ℝ} {D : Set (Space m)} {τ s₁ s₂ T c : ℝ} {L : ℝ≥0}
  {h : ℝ → Space m → ℝ}

/-- HA2 under the smallness `∫_{level region} ε |∇_y v|² ≤ Θ δ²` and `|B \ D| ≤ M δ²`: some
reference level has normalized extended height with Dirichlet energy at most
`(c⁻¹ Θ + (s₂ - s₁) L² M) / (s₂ - s₁)` on `B`, for every center `a`. -/
theorem exists_reference_level_normalized_of_le (hG : LevelGraphFamily v D τ s₁ s₂ T c L h)
    (hT : 0 < T) (hc : 0 < c) (hs : s₁ < s₂) (hDo : IsOpen D) (hDne : D.Nonempty)
    (B : Set (Space m)) {δ M Θ : ℝ} (hδ : 0 < δ) (hM : 0 ≤ M) (hΘ : 0 ≤ Θ)
    (htilt : ∫⁻ x in levelRegion v D τ s₁ s₂,
      ENNReal.ofReal (diffuseTiltDensity T v (verticalDirection m) x) ≤
        ENNReal.ofReal (Θ * δ ^ 2))
    (hbad : volume (B \ D) ≤ ENNReal.ofReal (M * δ ^ 2)) :
    ∃ s₀ ∈ Icc s₁ s₂, ∀ a : ℝ, ∫⁻ y in B, ENNReal.ofReal
        (‖gradient (normalizedHeight (extendedHeight D L τ s₁ s₂ h s₀) a δ) y‖ ^ 2) ≤
      ENNReal.ofReal ((c⁻¹ * Θ + (s₂ - s₁) * (L : ℝ) ^ 2 * M) / (s₂ - s₁)) := by
  obtain ⟨s₀, hs₀, hle⟩ := hG.exists_reference_level hT hc hs hDo hDne B
  refine ⟨s₀, hs₀, fun a ↦ ?_⟩
  have hI : 0 < s₂ - s₁ := sub_pos.mpr hs
  have hci : 0 ≤ c⁻¹ := inv_nonneg.mpr hc.le
  have hnum : ENNReal.ofReal c⁻¹ * (∫⁻ x in levelRegion v D τ s₁ s₂,
        ENNReal.ofReal (diffuseTiltDensity T v (verticalDirection m) x)) +
      ENNReal.ofReal ((s₂ - s₁) * (L : ℝ) ^ 2) * volume (B \ D) ≤
      ENNReal.ofReal (c⁻¹ * (Θ * δ ^ 2) + (s₂ - s₁) * (L : ℝ) ^ 2 * (M * δ ^ 2)) := by
    have e1 : ENNReal.ofReal (c⁻¹ * (Θ * δ ^ 2) + (s₂ - s₁) * (L : ℝ) ^ 2 * (M * δ ^ 2)) =
        ENNReal.ofReal c⁻¹ * ENNReal.ofReal (Θ * δ ^ 2) +
          ENNReal.ofReal ((s₂ - s₁) * (L : ℝ) ^ 2) * ENNReal.ofReal (M * δ ^ 2) := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul hci,
        ENNReal.ofReal_mul (show 0 ≤ (s₂ - s₁) * (L : ℝ) ^ 2 by positivity)]
    rw [e1]
    gcongr
  rw [lintegral_gradient_normalizedHeight]
  calc
    ENNReal.ofReal (δ⁻¹ ^ 2) * ∫⁻ y in B,
        ENNReal.ofReal (‖gradient (extendedHeight D L τ s₁ s₂ h s₀) y‖ ^ 2) ≤
        ENNReal.ofReal (δ⁻¹ ^ 2) *
          (ENNReal.ofReal (c⁻¹ * (Θ * δ ^ 2) + (s₂ - s₁) * (L : ℝ) ^ 2 * (M * δ ^ 2)) /
            ENNReal.ofReal (s₂ - s₁)) := by
      gcongr
      exact hle.trans (by gcongr)
    _ = ENNReal.ofReal ((c⁻¹ * Θ + (s₂ - s₁) * (L : ℝ) ^ 2 * M) / (s₂ - s₁)) := by
      rw [← ENNReal.ofReal_div_of_pos hI, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp

/-- Pointwise HA3 between two levels in `[s₁, s₂]` for normalized extended heights. -/
theorem abs_normalizedHeight_sub_le_of_mem (hG : LevelGraphFamily v D τ s₁ s₂ T c L h)
    (hT : 0 < T) (hc : 0 < c) (hs : s₁ ≤ s₂) (hD : D.Nonempty) {δ : ℝ} (hδ : 0 < δ) (a : ℝ)
    {s s' : ℝ} (hσ : s ∈ Icc s₁ s₂) (hσ' : s' ∈ Icc s₁ s₂) (y : Space m) :
    |normalizedHeight (extendedHeight D L τ s₁ s₂ h s) a δ y -
        normalizedHeight (extendedHeight D L τ s₁ s₂ h s') a δ y| ≤
      (s₂ - s₁) / (c * T * δ) := by
  have hh := hG.abs_normalizedHeight_sub_le hT hc hs hD hδ a s s' y
  have hss : |s - s'| ≤ s₂ - s₁ := abs_sub_le_of_le_of_le hσ.1 hσ.2 hσ'.1 hσ'.2
  exact hh.trans (div_le_div_of_nonneg_right hss (mul_pos (mul_pos hc hT) hδ).le)

end LevelGraphFamily

/-- **HA2–HA3 along a sequence.** Suppose that for each `j` the level heights form a level graph
family over an open good set `D_j` at scale `T_j` (so `ε_j = T_j⁻¹`), the tangential energy of the
level region is at most `Θ δ_j²`, and `|B_ρ \ D_j| ≤ M δ_j²`. Choose the reference level `σ_j` by
the mean-value principle and center `a_j` the `B_ρ`-average of its extended height. Then the
normalized reference heights `H_j = (h̃_{σ_j} - a_j) / δ_j` are uniformly bounded in `W^{1,2}(B_ρ)`;
a subsequence converges in `L²(B_r)` for all `r < ρ` to some `H`; and if `T_j δ_j → ∞`
(i.e. `ε_j / δ_j → 0`), the normalized heights of *every* choice of levels `s_j ∈ [s₁, s₂]`, with
the same centers `a_j`, converge to the same `H` (HA3.1). -/
theorem exists_normalizedHeight_limit {v : ℕ → Space (m + 1) → ℝ} {D : ℕ → Set (Space m)}
    {h : ℕ → ℝ → Space m → ℝ} {T δ : ℕ → ℝ} {τ s₁ s₂ c ρ M Θ : ℝ} {L : ℝ≥0}
    (hG : ∀ j, LevelGraphFamily (v j) (D j) τ s₁ s₂ (T j) c L (h j))
    (hT : ∀ j, 0 < T j) (hc : 0 < c) (hs : s₁ < s₂) (hDo : ∀ j, IsOpen (D j))
    (hDne : ∀ j, (D j).Nonempty) (hδ : ∀ j, 0 < δ j) (hρ : 0 < ρ) (hM : 0 ≤ M) (hΘ : 0 ≤ Θ)
    (htilt : ∀ j, ∫⁻ x in levelRegion (v j) (D j) τ s₁ s₂,
      ENNReal.ofReal (diffuseTiltDensity (T j) (v j) (verticalDirection m) x) ≤
        ENNReal.ofReal (Θ * δ j ^ 2))
    (hbad : ∀ j, volume (ball (0 : Space m) ρ \ D j) ≤ ENNReal.ofReal (M * δ j ^ 2))
    (hratio : Tendsto (fun j ↦ T j * δ j) atTop atTop) :
    ∃ σ a : ℕ → ℝ, (∀ j, σ j ∈ Icc s₁ s₂) ∧
      (∀ j, a j = ⨍ z in ball (0 : Space m) ρ, extendedHeight (D j) L τ s₁ s₂ (h j) (σ j) z) ∧
      (∀ j, ∫ y in ball (0 : Space m) ρ,
        (normalizedHeight (extendedHeight (D j) L τ s₁ s₂ (h j) (σ j)) (a j) (δ j) y ^ 2 +
          ‖fderiv ℝ (normalizedHeight (extendedHeight (D j) L τ s₁ s₂ (h j) (σ j)) (a j)
            (δ j)) y‖ ^ 2) ≤
        (2 ^ (m + 1) * ρ ^ 2 + 1) * ((c⁻¹ * Θ + (s₂ - s₁) * (L : ℝ) ^ 2 * M) / (s₂ - s₁))) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ H : Space m → ℝ, Measurable H ∧
        (∀ r < ρ, MemLp H 2 (volume.restrict (ball (0 : Space m) r))) ∧
        ∀ s : ℕ → ℝ, (∀ j, s j ∈ Icc s₁ s₂) → ∀ r < ρ,
          Tendsto (fun j ↦ ∫ y in ball (0 : Space m) r,
            (normalizedHeight (extendedHeight (D (φ j)) L τ s₁ s₂ (h (φ j)) (s j))
              (a (φ j)) (δ (φ j)) y - H y) ^ 2) atTop (𝓝 0) := by
  set C₁ := (c⁻¹ * Θ + (s₂ - s₁) * (L : ℝ) ^ 2 * M) / (s₂ - s₁) with hC₁
  have hI : 0 < s₂ - s₁ := sub_pos.mpr hs
  have hC₁0 : 0 ≤ C₁ := by
    have hci : 0 ≤ c⁻¹ := inv_nonneg.mpr hc.le
    positivity
  have hex : ∀ j, ∃ s₀ ∈ Icc s₁ s₂, ∀ a : ℝ, ∫⁻ y in ball (0 : Space m) ρ, ENNReal.ofReal
      (‖gradient (normalizedHeight (extendedHeight (D j) L τ s₁ s₂ (h j) s₀) a (δ j)) y‖ ^ 2) ≤
        ENNReal.ofReal C₁ := fun j ↦
    (hG j).exists_reference_level_normalized_of_le (hT j) hc hs (hDo j) (hDne j) _ (hδ j) hM hΘ
      (htilt j) (hbad j)
  choose σ hσ hσgrad using hex
  set a : ℕ → ℝ := fun j ↦
    ⨍ z in ball (0 : Space m) ρ, extendedHeight (D j) L τ s₁ s₂ (h j) (σ j) z with ha
  set Φ : ℕ → Space m → ℝ := fun j ↦ extendedHeight (D j) L τ s₁ s₂ (h j) (σ j) with hΦ
  set Hn : ℕ → Space m → ℝ := fun j ↦ normalizedHeight (Φ j) (a j) (δ j) with hHn
  have hΦLip : ∀ j, LipschitzWith L (Φ j) := fun j ↦
    (hG j).extendedHeight_lipschitzWith hs.le (hDne j) (σ j)
  have hHLip : ∀ j, LipschitzWith (L * Real.toNNReal (δ j)⁻¹) (Hn j) := fun j ↦
    normalizedHeight_lipschitzWith (hΦLip j) (a j) (hδ j)
  have hgrad : ∀ j, ∫ y in ball (0 : Space m) ρ, ‖fderiv ℝ (Hn j) y‖ ^ 2 ≤ C₁ := by
    intro j
    have hh := LevelGraphFamily.integral_gradient_normalizedHeight_le hC₁0 (hσgrad j (a j))
    simpa only [norm_gradient_eq_norm_fderiv] using hh
  have hL2 : ∀ j, ∫ y in ball (0 : Space m) ρ, Hn j y ^ 2 ≤ 2 ^ (m + 1) * ρ ^ 2 * C₁ := by
    intro j
    have hP := integral_sq_normalizedHeight_le_poincare (hΦLip j) hρ (hδ j)
    calc
      ∫ y in ball (0 : Space m) ρ, Hn j y ^ 2 ≤
          2 ^ (m + 1) * ρ ^ 2 * ∫ y in ball (0 : Space m) ρ, ‖fderiv ℝ (Hn j) y‖ ^ 2 := hP
      _ ≤ 2 ^ (m + 1) * ρ ^ 2 * C₁ := by gcongr; exact hgrad j
  have hW : ∀ j, ∫ y in ball (0 : Space m) ρ, (Hn j y ^ 2 + ‖fderiv ℝ (Hn j) y‖ ^ 2) ≤
      (2 ^ (m + 1) * ρ ^ 2 + 1) * C₁ := by
    intro j
    have hc1 : IntegrableOn (fun y ↦ Hn j y ^ 2) (ball (0 : Space m) ρ) :=
      integrableOn_ball_of_continuous' ((hHLip j).continuous.pow 2) _ _
    have hc2 : IntegrableOn (fun y ↦ ‖fderiv ℝ (Hn j) y‖ ^ 2) (ball (0 : Space m) ρ) :=
      integrableOn_norm_fderiv_sq_of_lipschitzWith (hHLip j) _ _
    rw [integral_add hc1 hc2]
    have h1 := hL2 j
    have h2 := hgrad j
    nlinarith
  obtain ⟨φ, hφ, H, hHm, hHL2, hlim⟩ := exists_subseq_tendsto_sq_integral_ball (0 : Space m) ρ
    ((2 ^ (m + 1) * ρ ^ 2 + 1) * C₁) Hn (fun j ↦ ⟨_, hHLip j⟩) hW
  refine ⟨σ, a, hσ, fun j ↦ rfl, hW, φ, hφ, H, hHm, hHL2, ?_⟩
  intro s hsj r hr
  -- the HA3 error at the `j`-th term of the subsequence
  set κ : ℕ → ℝ := fun j ↦ (s₂ - s₁) / (c * T (φ j) * δ (φ j)) with hκ
  have hκ0 : Tendsto κ atTop (𝓝 0) := by
    have hTδ : Tendsto (fun j ↦ T (φ j) * δ (φ j)) atTop atTop :=
      hratio.comp hφ.tendsto_atTop
    have h1 : Tendsto (fun j ↦ c * (T (φ j) * δ (φ j))) atTop atTop :=
      hTδ.const_mul_atTop hc
    have h2 := h1.inv_tendsto_atTop
    have h3 := h2.const_mul (s₂ - s₁)
    rw [mul_zero] at h3
    refine h3.congr fun j ↦ ?_
    simp only [κ, Pi.inv_apply, div_eq_mul_inv, mul_assoc]
  have hκnn : ∀ j, 0 ≤ κ j := fun j ↦
    div_nonneg hI.le (mul_pos (mul_pos hc (hT (φ j))) (hδ (φ j))).le
  have hpt : ∀ j y, |normalizedHeight (extendedHeight (D (φ j)) L τ s₁ s₂ (h (φ j)) (s j))
      (a (φ j)) (δ (φ j)) y - Hn (φ j) y| ≤ κ j := fun j y ↦
    (hG (φ j)).abs_normalizedHeight_sub_le_of_mem (hT (φ j)) hc hs.le (hDne (φ j)) (hδ (φ j))
      (a (φ j)) (hsj j) (hσ (φ j)) y
  have hfin : IsFiniteMeasure (volume.restrict (ball (0 : Space m) r)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hint : ∀ j, Integrable (fun y ↦ (Hn (φ j) y - H y) ^ 2)
      (volume.restrict (ball (0 : Space m) r)) := fun j ↦
    ((memLp_two_ball_of_continuous' (hHLip (φ j)).continuous 0 r).sub (hHL2 r hr)).integrable_sq
  have hbound : ∀ j, ∫ y in ball (0 : Space m) r,
      (normalizedHeight (extendedHeight (D (φ j)) L τ s₁ s₂ (h (φ j)) (s j))
        (a (φ j)) (δ (φ j)) y - H y) ^ 2 ≤
      2 * (∫ y in ball (0 : Space m) r, (Hn (φ j) y - H y) ^ 2) +
        2 * κ j ^ 2 * volume.real (ball (0 : Space m) r) := by
    intro j
    have hmono := integral_mono_of_nonneg (μ := volume.restrict (ball (0 : Space m) r))
      (f := fun y ↦ (normalizedHeight (extendedHeight (D (φ j)) L τ s₁ s₂ (h (φ j)) (s j))
        (a (φ j)) (δ (φ j)) y - H y) ^ 2)
      (g := fun y ↦ 2 * (Hn (φ j) y - H y) ^ 2 + 2 * κ j ^ 2)
      (Eventually.of_forall fun y ↦ sq_nonneg _)
      (((hint j).const_mul 2).add (integrable_const _))
      (Eventually.of_forall fun y ↦ by
        have h1 := hpt j y
        have h2 : (normalizedHeight (extendedHeight (D (φ j)) L τ s₁ s₂ (h (φ j)) (s j))
            (a (φ j)) (δ (φ j)) y - Hn (φ j) y) ^ 2 ≤ κ j ^ 2 := by
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) h1 2
        dsimp only
        nlinarith [sq_nonneg (normalizedHeight (extendedHeight (D (φ j)) L τ s₁ s₂ (h (φ j))
          (s j)) (a (φ j)) (δ (φ j)) y - Hn (φ j) y + (Hn (φ j) y - H y)),
          sq_nonneg (normalizedHeight (extendedHeight (D (φ j)) L τ s₁ s₂ (h (φ j))
          (s j)) (a (φ j)) (δ (φ j)) y - Hn (φ j) y - (Hn (φ j) y - H y))])
    refine hmono.trans_eq ?_
    rw [integral_add ((hint j).const_mul 2) (integrable_const _), integral_const_mul,
      integral_const, smul_eq_mul, measureReal_restrict_apply_univ]
    ring
  have hlimr := hlim r hr
  have hupper : Tendsto (fun j ↦ 2 * (∫ y in ball (0 : Space m) r, (Hn (φ j) y - H y) ^ 2) +
      2 * κ j ^ 2 * volume.real (ball (0 : Space m) r)) atTop (𝓝 0) := by
    have h1 := hlimr.const_mul 2
    have h2 := ((hκ0.pow 2).const_mul 2).mul_const (volume.real (ball (0 : Space m) r))
    simpa using h1.add h2
  exact squeeze_zero (fun j ↦ integral_nonneg fun y ↦ sq_nonneg _) hbound hupper

/-! ### HA9.2 along a sequence: different good sets give the same normalized limit -/

/-- **HA9.2 along a sequence.** Two `L`-Lipschitz height sequences which differ by at most `κ_j`
on good sets `D_j`, whose complements in the larger ball `B_{ρ'}(y₀)` have volume at most
`M δ_j²`, have the same normalized `L²(B_ρ(y₀))` limit when `δ_j → 0` and `κ_j / δ_j → 0`. On the
good set the thickness bound is used; off it, every point is within any fixed `r` of the good set
for large `j`, and the Lipschitz bounds give `|f - g| ≤ κ + 2 L r` on a set of volume `M δ²`. -/
theorem tendsto_integral_sq_sub_div_of_near_good {f g : ℕ → Space m → ℝ} {L : ℝ≥0}
    (hf : ∀ j, LipschitzWith L (f j)) (hg : ∀ j, LipschitzWith L (g j))
    {D : ℕ → Set (Space m)} (hD : ∀ j, MeasurableSet (D j)) {κ δ : ℕ → ℝ}
    (hfg : ∀ j, ∀ z ∈ D j, |f j z - g j z| ≤ κ j) {y₀ : Space m} {ρ ρ' M : ℝ} (hM : 0 ≤ M)
    (hρ : ρ < ρ') (hbad : ∀ j, volume (ball y₀ ρ' \ D j) ≤ ENNReal.ofReal (M * δ j ^ 2))
    (hδ : ∀ j, 0 < δ j) (hδ0 : Tendsto δ atTop (𝓝 0))
    (hκ : Tendsto (fun j ↦ κ j / δ j) atTop (𝓝 0)) :
    Tendsto (fun j ↦ ∫ y in ball y₀ ρ, ((f j y - g j y) / δ j) ^ 2) atTop (𝓝 0) := by
  set V := volume.real (ball y₀ ρ) with hVdef
  have hV : 0 ≤ V := measureReal_nonneg
  rw [tendsto_order]
  refine ⟨fun a ha ↦ Eventually.of_forall fun j ↦
    ha.trans_le (integral_nonneg fun y ↦ sq_nonneg _), fun ε hε ↦ ?_⟩
  set A := (L : ℝ) ^ 2 * M with hA
  have hA0 : 0 ≤ A := by positivity
  set r := min ((ρ' - ρ) / 2) (min 1 (ε / (16 * (A + 1)))) with hr
  have hr0 : 0 < r := lt_min (by linarith) (lt_min one_pos (by positivity))
  have hrρ : r < ρ' - ρ := (min_le_left _ _).trans_lt (by linarith)
  have hr1 : r ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hrε : r ≤ ε / (16 * (A + 1)) := (min_le_right _ _).trans (min_le_right _ _)
  have hrsmall : 8 * A * r ^ 2 < ε / 2 := by
    have h1 : r ^ 2 ≤ r := by nlinarith
    have h2 : 8 * A * r ≤ 8 * A * (ε / (16 * (A + 1))) := by gcongr
    have h3 : 8 * A * (ε / (16 * (A + 1))) < ε / 2 := by
      rw [mul_div_assoc', div_lt_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    nlinarith
  have hvolr : 0 < volume (ball y₀ r) := measure_ball_pos _ _ hr0
  have hev1 : ∀ᶠ j in atTop, ENNReal.ofReal (M * δ j ^ 2) < volume (ball y₀ r) := by
    have ht : Tendsto (fun j ↦ ENNReal.ofReal (M * δ j ^ 2)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun j ↦ M * δ j ^ 2) atTop (𝓝 (M * 0 ^ 2)) :=
        (hδ0.pow 2).const_mul M
      rw [show M * (0 : ℝ) ^ 2 = 0 by ring] at h1
      simpa using ENNReal.tendsto_ofReal h1
    exact ht.eventually (gt_mem_nhds hvolr)
  have hev2 : ∀ᶠ j in atTop, (κ j / δ j) ^ 2 * (V + 2 * M * δ j ^ 2) < ε / 2 := by
    have ht : Tendsto (fun j ↦ (κ j / δ j) ^ 2 * (V + 2 * M * δ j ^ 2)) atTop
        (𝓝 (0 ^ 2 * (V + 2 * M * 0 ^ 2))) :=
      (hκ.pow 2).mul (tendsto_const_nhds.add ((hδ0.pow 2).const_mul (2 * M)))
    rw [show (0 : ℝ) ^ 2 * (V + 2 * M * 0 ^ 2) = 0 by ring] at ht
    exact ht.eventually (gt_mem_nhds (by positivity))
  filter_upwards [hev1, hev2] with j h1 h2
  have hδj := hδ j
  have hnear : ∀ y ∈ ball y₀ ρ, ∃ z ∈ D j, dist y z < r := by
    intro y hy
    rw [mem_ball] at hy
    apply exists_mem_ball_of_volume_lt (B := ball y₀ ρ')
    · exact ball_subset_ball' (by linarith)
    · calc
        volume (ball y₀ ρ' \ D j) ≤ ENNReal.ofReal (M * δ j ^ 2) := hbad j
        _ < volume (ball y₀ r) := h1
        _ = volume (ball y r) := by
          rw [Measure.addHaar_ball_center, Measure.addHaar_ball_center volume y]
  have hcont : Continuous (fun y ↦ ((f j y - g j y) / δ j) ^ 2) :=
    (((hf j).continuous.sub (hg j).continuous).div_const _).pow 2
  have hint := integrableOn_ball_of_continuous' hcont y₀ ρ
  have hfinB : volume (ball y₀ ρ) ≠ ⊤ := measure_ball_lt_top.ne
  rw [← integral_inter_add_sdiff (hD j) hint]
  have hgood : ∫ y in ball y₀ ρ ∩ D j, ((f j y - g j y) / δ j) ^ 2 ≤ (κ j / δ j) ^ 2 * V := by
    calc
      ∫ y in ball y₀ ρ ∩ D j, ((f j y - g j y) / δ j) ^ 2 ≤
          ∫ _ in ball y₀ ρ ∩ D j, (κ j / δ j) ^ 2 := by
        refine setIntegral_mono_on (hint.mono_set inter_subset_left)
          (integrableOn_const ((measure_mono inter_subset_left).trans_lt
            measure_ball_lt_top).ne) (measurableSet_ball.inter (hD j)) fun y hy ↦ ?_
        rw [div_pow, div_pow]
        apply div_le_div_of_nonneg_right _ (sq_nonneg _)
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hfg j y hy.2) 2
      _ = (κ j / δ j) ^ 2 * volume.real (ball y₀ ρ ∩ D j) := by
        rw [setIntegral_const, smul_eq_mul, mul_comm]
      _ ≤ (κ j / δ j) ^ 2 * V := by
        gcongr
        exact measureReal_mono inter_subset_left hfinB
  have hvolbad : volume.real (ball y₀ ρ \ D j) ≤ M * δ j ^ 2 :=
    ENNReal.toReal_le_of_le_ofReal (by positivity)
      ((measure_mono (sdiff_subset_sdiff_left (ball_subset_ball hρ.le))).trans (hbad j))
  have hbadI : ∫ y in ball y₀ ρ \ D j, ((f j y - g j y) / δ j) ^ 2 ≤
      (2 * (κ j / δ j) ^ 2 + 8 * (L : ℝ) ^ 2 * r ^ 2 / δ j ^ 2) * (M * δ j ^ 2) := by
    calc
      ∫ y in ball y₀ ρ \ D j, ((f j y - g j y) / δ j) ^ 2 ≤
          ∫ _ in ball y₀ ρ \ D j, (2 * (κ j / δ j) ^ 2 + 8 * (L : ℝ) ^ 2 * r ^ 2 / δ j ^ 2) := by
        refine setIntegral_mono_on (hint.mono_set sdiff_subset)
          (integrableOn_const ((measure_mono sdiff_subset).trans_lt
            measure_ball_lt_top).ne) (measurableSet_ball.diff (hD j)) fun y hy ↦ ?_
        obtain ⟨z, hz, hyz⟩ := hnear y hy.1
        have hb := abs_sub_le_of_lipschitzWith_of_near (hf j) (hg j) (hfg j) hz hyz.le
        have hsq : (f j y - g j y) ^ 2 ≤ (κ j + 2 * L * r) ^ 2 := by
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) hb 2
        have hsq2 : (κ j + 2 * L * r) ^ 2 ≤ 2 * κ j ^ 2 + 8 * (L : ℝ) ^ 2 * r ^ 2 := by
          nlinarith [sq_nonneg (κ j - 2 * L * r)]
        rw [div_pow, div_pow]
        have hδ2 : 0 < δ j ^ 2 := by positivity
        rw [div_le_iff₀ hδ2]
        have he : (2 * (κ j ^ 2 / δ j ^ 2) + 8 * (L : ℝ) ^ 2 * r ^ 2 / δ j ^ 2) * δ j ^ 2 =
            2 * κ j ^ 2 + 8 * (L : ℝ) ^ 2 * r ^ 2 := by
          field_simp
        rw [he]
        linarith
      _ = (2 * (κ j / δ j) ^ 2 + 8 * (L : ℝ) ^ 2 * r ^ 2 / δ j ^ 2) *
          volume.real (ball y₀ ρ \ D j) := by
        rw [setIntegral_const, smul_eq_mul, mul_comm]
      _ ≤ (2 * (κ j / δ j) ^ 2 + 8 * (L : ℝ) ^ 2 * r ^ 2 / δ j ^ 2) * (M * δ j ^ 2) := by
        gcongr
  have hfinal : (κ j / δ j) ^ 2 * V +
      (2 * (κ j / δ j) ^ 2 + 8 * (L : ℝ) ^ 2 * r ^ 2 / δ j ^ 2) * (M * δ j ^ 2) =
      (κ j / δ j) ^ 2 * (V + 2 * M * δ j ^ 2) + 8 * A * r ^ 2 := by
    rw [hA]
    field_simp
    ring
  linarith

/-! ### HA9.e: transfer of the tilt bound to nearby points -/

/-- **HA9.e radius transfer.** If the ball integrals of a bounded nonnegative density at `x` are
below `ℓ r^m` for all `0 < r ≤ r₀`, then at a point `x'` with `|x' - x| ≤ d` they are below
`ℓ (1 + d / ρ)^m r^m` for all radii `ρ ≤ r ≤ r₀ - d`: the ball `B_r(x')` lies in `B_{r+d}(x)`. -/
theorem setIntegral_ball_lt_of_near {F : Space (m + 1) → ℝ} {C : ℝ} (hFm : Measurable F)
    (hF0 : ∀ x, 0 ≤ F x) (hFC : ∀ x, F x ≤ C) {x x' : Space (m + 1)} {ℓ r₀ d ρ : ℝ}
    (hρ : 0 < ρ) (hd : 0 ≤ d)
    (hgood : ∀ r ∈ Ioc 0 r₀, ∫ y in ball x r, F y < ℓ * r ^ m) (hxx' : dist x' x ≤ d)
    {r : ℝ} (hr : ρ ≤ r) (hr' : r + d ≤ r₀) :
    ∫ y in ball x' r, F y < ℓ * (1 + d / ρ) ^ m * r ^ m := by
  have hr0 : 0 < r := hρ.trans_le hr
  have hrd : r + d ∈ Ioc 0 r₀ := ⟨by linarith, hr'⟩
  have h1 : ∫ y in ball x' r, F y ≤ ∫ y in ball x (r + d), F y :=
    setIntegral_ball_mono hFm hF0 hFC (by linarith)
  have h2 := hgood (r + d) hrd
  have hℓ : 0 < ℓ := by
    have h3 : 0 ≤ ∫ y in ball x (r + d), F y :=
      setIntegral_nonneg measurableSet_ball fun y _ ↦ hF0 y
    have h4 : 0 < (r + d) ^ m := pow_pos (by linarith) m
    by_contra hn
    push Not at hn
    nlinarith
  have h5 : r + d ≤ (1 + d / ρ) * r := by
    have : d ≤ d / ρ * r := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hρ]
      nlinarith
    nlinarith
  have h6 : (r + d) ^ m ≤ ((1 + d / ρ) * r) ^ m := pow_le_pow_left₀ (by linarith) h5 m
  calc
    ∫ y in ball x' r, F y < ℓ * (r + d) ^ m := h1.trans_lt h2
    _ ≤ ℓ * ((1 + d / ρ) * r) ^ m := by gcongr
    _ = ℓ * (1 + d / ρ) ^ m * r ^ m := by rw [mul_pow]; ring

/-! ### Microscopic one-dimensional limits at actual good points (HA9) -/

/-- The diffuse tilt of a rotated, translated rescaling is the physical tilt in the rotated
direction, times the scale. -/
theorem diffuseTiltDensity_translate_dilation_isometry (U : Space (m + 1) → ℝ)
    (c : Space (m + 1)) {R : ℝ} (hR : 0 < R) (Q : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1))
    (e x : Space (m + 1)) :
    diffuseTiltDensity R (fun y ↦ U (c + R • Q y)) e x =
      R * diffuseTiltDensity 1 U (Q e) (c + R • Q x) := by
  unfold diffuseTiltDensity
  rw [gradient_comp_translate_dilation_isometry, norm_smul, LinearIsometryEquiv.norm_map,
    real_inner_smul_left]
  have hin : inner ℝ (Q.symm (gradient U (c + R • Q x))) e =
      inner ℝ (gradient U (c + R • Q x)) (Q e) := by
    rw [← Q.inner_map_map, LinearIsometryEquiv.apply_symm_apply]
  rw [hin, Real.norm_eq_abs, abs_of_pos hR]
  field_simp

/-- Change of variables for ball integrals under `y ↦ c + R • Q y`. -/
theorem setIntegral_ball_comp_translate_dilation_isometry (G : Space (m + 1) → ℝ)
    (c : Space (m + 1)) {R : ℝ} (hR : 0 < R) (Q : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1))
    (x : Space (m + 1)) (r : ℝ) :
    ∫ y in ball x r, G (c + R • Q y) =
      (R ^ (m + 1))⁻¹ * ∫ z in ball (c + R • Q x) (R * r), G z := by
  have h1 : ∫ y in ball x r, G (c + R • Q y) = ∫ z in ball (Q x) r, G (c + R • z) := by
    rw [← LinearIsometryEquiv.image_ball,
      (Q.measurePreserving).setIntegral_image_emb Q.toHomeomorph.measurableEmbedding]
  have h2 : ∫ z in ball (Q x) r, G (c + R • z) =
      (R ^ (m + 1))⁻¹ * ∫ w in ball (R • Q x) (R * r), G (c + w) := by
    rw [Measure.setIntegral_comp_smul_of_pos volume (fun w ↦ G (c + w)) _ hR,
      _root_.smul_ball hR.ne', Real.norm_eq_abs, abs_of_pos hR, finrank_euclideanSpace,
      Fintype.card_fin, smul_eq_mul]
  have h3 : ∫ w in ball (R • Q x) (R * r), G (c + w) =
      ∫ z in ball (c + R • Q x) (R * r), G z := by
    have hp : (fun w : Space (m + 1) ↦ c + w) ⁻¹' ball (c + R • Q x) (R * r) =
        ball (R • Q x) (R * r) := by
      ext w
      simp only [mem_preimage, mem_ball, dist_add_left]
    have ht := ((measurePreserving_add_left volume c).restrict_preimage
      (s := ball (c + R • Q x) (R * r)) measurableSet_ball).integral_comp
        (Homeomorph.addLeft c).measurableEmbedding G
    simpa only [hp] using ht
  rw [h1, h2, h3]

/-- **Scale invariance of the normalized tilt.** For `v y = U (c + R • Q y)` and `R > 0`,
`∫_{B_r(x)} R⁻¹-diffuse tilt of v in direction e = R⁻ᵐ ∫_{B_{Rr}(c + R Q x)}` physical tilt of `U`
in direction `Q e`. -/
theorem setIntegral_ball_diffuseTiltDensity_rescaled (U : Space (m + 1) → ℝ)
    (c : Space (m + 1)) {R : ℝ} (hR : 0 < R) (Q : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1))
    (e x : Space (m + 1)) (r : ℝ) :
    ∫ y in ball x r, diffuseTiltDensity R (fun y ↦ U (c + R • Q y)) e y =
      (R ^ m)⁻¹ * ∫ z in ball (c + R • Q x) (R * r), diffuseTiltDensity 1 U (Q e) z := by
  simp_rw [diffuseTiltDensity_translate_dilation_isometry U c hR Q e]
  rw [integral_const_mul, setIntegral_ball_comp_translate_dilation_isometry _ c hR Q x r,
    pow_succ]
  field_simp


/-- At an actual good point of the rescaling at scale `R`, the physical tilt on a ball of physical
radius `ρ ≤ R r₀` around the physical center is below `ℓ ρ^m`. -/
theorem physical_tilt_lt_of_isLayerGoodPoint {U : Space (m + 1) → ℝ} {c : Space (m + 1)}
    {R : ℝ} (hR : 0 < R) {e : Space (m + 1)} {ℓ r₀ b : ℝ} {x : Space (m + 1)}
    (hgood : IsLayerGoodPoint R (fun y ↦ U (c + R • y)) e ℓ r₀ b x) {ρ : ℝ} (hρ : 0 < ρ)
    (hρR : ρ ≤ R * r₀) :
    ∫ z in ball (c + R • x) ρ, diffuseTiltDensity 1 U e z < ℓ * ρ ^ m := by
  have hr : ρ / R ∈ Ioc 0 r₀ := ⟨div_pos hρ hR, by rw [div_le_iff₀ hR]; linarith⟩
  have h1 := hgood.2 (ρ / R) hr
  have h2 := setIntegral_ball_diffuseTiltDensity_rescaled U c hR
    (LinearIsometryEquiv.refl ℝ (Space (m + 1))) e x (ρ / R)
  simp only [LinearIsometryEquiv.coe_refl, id_eq] at h2
  rw [h2, mul_div_cancel₀ _ hR.ne'] at h1
  have hRm : 0 < R ^ m := pow_pos hR m
  rw [inv_mul_lt_iff₀ hRm, div_pow] at h1
  have he : R ^ m * (ℓ * (ρ ^ m / R ^ m)) = ℓ * ρ ^ m := by field_simp
  rwa [he] at h1

/-- **Microscopic one-dimensional limits at actual good points (HA9).** Let `x_j` be actual good
points of the rescalings `y ↦ zeroExtension g u (c_j + R_j • y)` with thresholds `ℓ_j → 0`, fixed
`r₀ > 0` and `R_j → ∞`. Then, along a subsequence, the physical translates about the physical
centers `c_j + R_j • x_j` converge locally uniformly to a `κ`-Lipschitz profile `V` depending only
on the coordinate along `e`, inheriting all translation orders of the solution, with
`V 0 ∈ [0, 1 - b]`. -/
theorem RigidityHypotheses.exists_oneDimensional_limit_at_good_points
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (c : ℕ → Space (m + 1))
    {R : ℕ → ℝ} (hR : ∀ j, 0 < R j) (hRt : Tendsto R atTop atTop) {e : Space (m + 1)}
    (he : ‖e‖ = 1) {ℓ : ℕ → ℝ} (hℓ : Tendsto ℓ atTop (𝓝 0)) {r₀ b : ℝ} (hr₀ : 0 < r₀)
    (x : ℕ → Space (m + 1))
    (hgood : ∀ j, IsLayerGoodPoint (R j) (fun y ↦ zeroExtension g u (c j + R j • y)) e (ℓ j) r₀ b
      (x j)) :
    ∃ (φ : ℕ → ℕ) (V : Space (m + 1) → ℝ), StrictMono φ ∧
      LipschitzWith ⟨κ, h.kappa_pos.le⟩ V ∧ (∀ y, V y ∈ Icc 0 1) ∧
      (∀ K : Set (Space (m + 1)), IsCompact K →
        TendstoUniformlyOn (fun j y ↦ zeroExtension g u (c (φ j) + R (φ j) • x (φ j) + y)) V
          atTop K) ∧
      translationOrderSet (zeroExtension g u) ⊆ translationOrderSet V ∧
      (∀ y, V y = V ((inner ℝ e y) • e)) ∧ V 0 ∈ Icc 0 (1 - b) := by
  set X : ℕ → Space (m + 1) := fun j ↦ c j + R j • x j with hX
  have hLip : ∀ j, LipschitzWith ⟨κ, h.kappa_pos.le⟩ (fun y ↦ zeroExtension g u (X j + y)) := by
    intro j
    apply LipschitzWith.of_dist_le_mul
    intro y z
    simpa only [dist_add_left] using (hr.zeroExtension_lipschitzWith h).dist_le_mul
      (X j + y) (X j + z)
  have hball : ∀ ρ : ℝ, 0 < ρ → Tendsto (fun j ↦ ∫ z in ball (X j) ρ,
      diffuseTiltDensity 1 (zeroExtension g u) e z) atTop (𝓝 0) := by
    intro ρ hρ
    have hlarge : ∀ᶠ j in atTop, ρ ≤ R j * r₀ := by
      have ht : Tendsto (fun j ↦ R j * r₀) atTop atTop := hRt.atTop_mul_const hr₀
      exact ht.eventually (eventually_ge_atTop ρ)
    have hup : Tendsto (fun j ↦ ℓ j * ρ ^ m) atTop (𝓝 0) := by
      simpa using hℓ.mul_const (ρ ^ m)
    refine squeeze_zero' (Eventually.of_forall fun j ↦ setIntegral_nonneg measurableSet_ball
      fun z _ ↦ diffuseTiltDensity_nonneg one_pos _ he z) ?_ hup
    filter_upwards [hlarge] with j hj
    exact (physical_tilt_lt_of_isLayerGoodPoint (hR j) (hgood j) hρ hj).le
  have ht : ∀ K : Set (Space (m + 1)), IsCompact K →
      Tendsto (fun j ↦ ∫ y in K,
        diffuseTiltDensity 1 (fun z ↦ zeroExtension g u (X j + z)) e y) atTop (𝓝 0) := by
    intro K hK
    obtain ⟨ρ, hKρ⟩ := hK.isBounded.subset_ball (0 : Space (m + 1))
    set ρ' := max ρ 1
    have hKρ' : K ⊆ ball 0 ρ' := hKρ.trans (ball_subset_ball (le_max_left _ _))
    have hρ' : 0 < ρ' := lt_max_of_lt_right one_pos
    refine squeeze_zero (fun j ↦ setIntegral_nonneg hK.measurableSet
      fun z _ ↦ diffuseTiltDensity_nonneg one_pos _ he z) (fun j ↦ ?_) (hball ρ' hρ')
    have hT : ∀ y, diffuseTiltDensity 1 (fun z ↦ zeroExtension g u (X j + z)) e y =
        diffuseTiltDensity 1 (zeroExtension g u) e (X j + y) := by
      intro y
      have hh := diffuseTiltDensity_translate_dilation_isometry (zeroExtension g u) (X j)
        one_pos (LinearIsometryEquiv.refl ℝ (Space (m + 1))) e y
      simpa using hh
    simp_rw [hT]
    have hint : IntegrableOn (fun y ↦ diffuseTiltDensity 1 (zeroExtension g u) e (X j + y))
        (ball 0 ρ') := by
      have hc : Continuous (fun y : Space (m + 1) ↦ X j + y) := by fun_prop
      have hi := integrableOn_diffuseTiltDensity (hLip j).locallyLipschitz
        (isCompact_closedBall (0 : Space (m + 1)) ρ') 1 he
      refine (hi.congr_fun (fun y _ ↦ hT y) measurableSet_closedBall).mono_set
        ball_subset_closedBall
    calc
      ∫ y in K, diffuseTiltDensity 1 (zeroExtension g u) e (X j + y) ≤
          ∫ y in ball 0 ρ', diffuseTiltDensity 1 (zeroExtension g u) e (X j + y) :=
        setIntegral_mono_set hint (Eventually.of_forall fun y ↦
          diffuseTiltDensity_nonneg one_pos _ he _) (Eventually.of_forall hKρ')
      _ = ∫ z in ball (X j) ρ', diffuseTiltDensity 1 (zeroExtension g u) e z := by
        have hh := setIntegral_ball_comp_translate_dilation_isometry
          (diffuseTiltDensity 1 (zeroExtension g u) e) (X j) one_pos
          (LinearIsometryEquiv.refl ℝ (Space (m + 1))) 0 ρ'
        simpa using hh
  obtain ⟨φ, V, hφ, hV, hVval, hlim, horder, hprofile⟩ :=
    hr.exists_oneDimensional_physical_translation_limit h X he ht
  refine ⟨φ, V, hφ, hV, hVval, hlim, horder, hprofile, ?_⟩
  have h0 : Tendsto (fun j ↦ zeroExtension g u (X (φ j) + 0)) atTop (𝓝 (V 0)) :=
    (hlim {0} isCompact_singleton).tendsto_at (mem_singleton 0)
  have hmem : ∀ j, zeroExtension g u (X (φ j) + 0) ∈ Icc (0 : ℝ) (1 - b) := by
    intro j
    rw [add_zero]
    exact Ioo_subset_Icc_self (hgood (φ j)).1
  exact isClosed_Icc.mem_of_tendsto h0 (Eventually.of_forall hmem)

/-! ### HA2–HA3 with eventual hypotheses, and for sequences with planar layers -/

/-- `exists_normalizedHeight_limit` when the HA2 inputs hold only for large `j`; all conclusions
are stated along the extracted subsequence `φ`. -/
theorem exists_normalizedHeight_limit_of_eventually {v : ℕ → Space (m + 1) → ℝ}
    {D : ℕ → Set (Space m)} {h : ℕ → ℝ → Space m → ℝ} {T δ : ℕ → ℝ} {τ s₁ s₂ c ρ M Θ : ℝ}
    {L : ℝ≥0} (hG : ∀ᶠ j in atTop, LevelGraphFamily (v j) (D j) τ s₁ s₂ (T j) c L (h j))
    (hT : ∀ j, 0 < T j) (hc : 0 < c) (hs : s₁ < s₂) (hDo : ∀ j, IsOpen (D j))
    (hDne : ∀ᶠ j in atTop, (D j).Nonempty) (hδ : ∀ j, 0 < δ j) (hρ : 0 < ρ) (hM : 0 ≤ M)
    (hΘ : 0 ≤ Θ)
    (htilt : ∀ᶠ j in atTop, ∫⁻ x in levelRegion (v j) (D j) τ s₁ s₂,
      ENNReal.ofReal (diffuseTiltDensity (T j) (v j) (verticalDirection m) x) ≤
        ENNReal.ofReal (Θ * δ j ^ 2))
    (hbad : ∀ᶠ j in atTop, volume (ball (0 : Space m) ρ \ D j) ≤ ENNReal.ofReal (M * δ j ^ 2))
    (hratio : Tendsto (fun j ↦ T j * δ j) atTop atTop) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ σ a : ℕ → ℝ, (∀ j, σ j ∈ Icc s₁ s₂) ∧
      (∀ j, a j =
        ⨍ z in ball (0 : Space m) ρ, extendedHeight (D (φ j)) L τ s₁ s₂ (h (φ j)) (σ j) z) ∧
      (∀ j, ∫ y in ball (0 : Space m) ρ,
        (normalizedHeight (extendedHeight (D (φ j)) L τ s₁ s₂ (h (φ j)) (σ j)) (a j)
            (δ (φ j)) y ^ 2 +
          ‖fderiv ℝ (normalizedHeight (extendedHeight (D (φ j)) L τ s₁ s₂ (h (φ j)) (σ j)) (a j)
            (δ (φ j))) y‖ ^ 2) ≤
        (2 ^ (m + 1) * ρ ^ 2 + 1) * ((c⁻¹ * Θ + (s₂ - s₁) * (L : ℝ) ^ 2 * M) / (s₂ - s₁))) ∧
      ∃ H : Space m → ℝ, Measurable H ∧
        (∀ r < ρ, MemLp H 2 (volume.restrict (ball (0 : Space m) r))) ∧
        ∀ s : ℕ → ℝ, (∀ j, s j ∈ Icc s₁ s₂) → ∀ r < ρ,
          Tendsto (fun j ↦ ∫ y in ball (0 : Space m) r,
            (normalizedHeight (extendedHeight (D (φ j)) L τ s₁ s₂ (h (φ j)) (s j))
              (a j) (δ (φ j)) y - H y) ^ 2) atTop (𝓝 0) := by
  obtain ⟨N, hN⟩ := (hG.and (hDne.and (htilt.and hbad))).exists_forall_of_atTop
  have hle : ∀ j, N ≤ j + N := fun j ↦ Nat.le_add_left N j
  obtain ⟨σ', a', hσ', ha', hW', φ', hφ', H, hHm, hHL2, hlim'⟩ :=
    exists_normalizedHeight_limit (v := fun j ↦ v (j + N)) (D := fun j ↦ D (j + N))
      (h := fun j ↦ h (j + N)) (T := fun j ↦ T (j + N)) (δ := fun j ↦ δ (j + N))
      (fun j ↦ (hN _ (hle j)).1) (fun j ↦ hT _) hc hs (fun j ↦ hDo _)
      (fun j ↦ (hN _ (hle j)).2.1) (fun j ↦ hδ _) hρ hM hΘ (fun j ↦ (hN _ (hle j)).2.2.1)
      (fun j ↦ (hN _ (hle j)).2.2.2) (hratio.comp (tendsto_add_atTop_nat N))
  refine ⟨fun j ↦ φ' j + N, fun i k hik ↦ Nat.add_lt_add_right (hφ' hik) N,
    fun j ↦ σ' (φ' j), fun j ↦ a' (φ' j), fun j ↦ hσ' _, fun j ↦ ha' _, fun j ↦ hW' _,
    H, hHm, hHL2, fun s hsj r hr ↦ hlim' s hsj r hr⟩

/-- The good projection inside the horizontal ball `B_ρ`, in vertical coordinates. -/
def verticalGoodSet (T : ℝ) (v : Space (m + 1) → ℝ) (ℓ r₀ b ρ : ℝ) : Set (Space m) :=
  goodProjection T v (verticalDirection m) ℓ r₀ b ∩ ball 0 ρ

theorem norm_le_norm_horizontal_add_abs_vertical (x : Space (m + 1)) :
    ‖x‖ ≤ ‖horizontal x‖ + |x (Fin.last m)| := by
  have h := norm_point_le (horizontal x) (x (Fin.last m))
  rwa [point_horizontal_last] at h

theorem levelRegion_subset_closedBall {v : Space (m + 1) → ℝ} {D : Set (Space m)} {ρ τ s₁ s₂ : ℝ}
    (hD : D ⊆ ball 0 ρ) : levelRegion v D τ s₁ s₂ ⊆ closedBall 0 (ρ + τ) := by
  intro x hx
  rw [mem_closedBall, dist_zero_right]
  have h1 := norm_le_norm_horizontal_add_abs_vertical x
  have h2 : ‖horizontal x‖ < ρ := by
    have := hD hx.1
    rwa [mem_ball, dist_zero_right] at this
  have h3 : |x (Fin.last m)| < τ := abs_lt.mpr hx.2.1
  linarith

/-- **HA2–HA3 for a sequence with planar layers, modulo the HA9 graph conditions.** Let `v_j` be
Lipschitz, differentiable at positive values, with vertical planar layers (HA8), at scales
`T_j > 0` with `δ_j → 0` and `T_j δ_j → ∞`, and with total vertical tilt at most `Θ δ_j²` on a
fixed ball. On the good projections `D_j = verticalGoodSet (T j) (v j) ℓ r₀ b ρ` assume the cone
condition and the unsigned slope bound (HA9.d, HA11). Then the bad volume is `O(δ_j²)` (HA1.2),
the slope bound is signed (`eventually_hasLevelSlope_of_cone`), the chosen
level heights form level graph families (HA2.1), and along a subsequence the normalized
reference heights converge in `L²` with a uniform `W^{1,2}` bound, every choice of levels in
`[s₁, s₂]` having the same limit (HA2.3, HA3.1). -/
theorem VerticalPlanarLayers.exists_normalizedHeight_limit {v : ℕ → Space (m + 1) → ℝ}
    (hV : VerticalPlanarLayers v) {K : ℕ → ℝ≥0} (hvL : ∀ j, LipschitzWith (K j) (v j))
    (hdiff : ∀ j x, 0 < v j x → DifferentiableAt ℝ (v j) x) {T δ : ℕ → ℝ}
    (hT : ∀ j, 0 < T j) (hδ : ∀ j, 0 < δ j) (hδ0 : Tendsto δ atTop (𝓝 0))
    (hratio : Tendsto (fun j ↦ T j * δ j) atTop atTop) {ℓ r₀ b ρ τ s₁ s₂ c Θ : ℝ} {L : ℝ≥0}
    (hℓ : 0 < ℓ) (hb0 : 0 ≤ b) (hb1 : b < 1) (hρ : 0 < ρ) (hτ : 0 < τ) (hs₁ : 0 < s₁)
    (hs : s₁ < s₂) (hs₂ : s₂ < 1) (hc : 0 < c) (hΘ : 0 ≤ Θ)
    (htot : ∀ᶠ j in atTop, ∫ x in closedBall (0 : Space (m + 1)) (ρ + τ + |r₀|),
      diffuseTiltDensity (T j) (v j) (verticalDirection m) x ≤ Θ * δ j ^ 2)
    {D : ℕ → Set (Space m)} (hDdef : ∀ j, D j = verticalGoodSet (T j) (v j) ℓ r₀ b ρ)
    (hcone : ∀ᶠ j in atTop, HasLevelCone (v j) (D j) τ s₁ s₂ L)
    (hslope : ∀ᶠ j in atTop, HasLevelSlopeAbs (v j) (D j) τ s₁ s₂ (T j) c) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ σ a : ℕ → ℝ, (∀ j, σ j ∈ Icc s₁ s₂) ∧
      (∀ j, a j = ⨍ z in ball (0 : Space m) ρ, extendedHeight (D (φ j)) L τ s₁ s₂
        (fun s y ↦ slabLevelHeight (v (φ j)) τ s y) (σ j) z) ∧
      (∀ j, ∫ y in ball (0 : Space m) ρ,
        (normalizedHeight (extendedHeight (D (φ j)) L τ s₁ s₂
            (fun s y ↦ slabLevelHeight (v (φ j)) τ s y) (σ j)) (a j) (δ (φ j)) y ^ 2 +
          ‖fderiv ℝ (normalizedHeight (extendedHeight (D (φ j)) L τ s₁ s₂
            (fun s y ↦ slabLevelHeight (v (φ j)) τ s y) (σ j)) (a j) (δ (φ j))) y‖ ^ 2) ≤
        (2 ^ (m + 1) * ρ ^ 2 + 1) * ((c⁻¹ * Θ + (s₂ - s₁) * (L : ℝ) ^ 2 *
          ((5 : ℝ) ^ m * volume.real (ball (0 : Space m) 1) * Θ / ℓ)) / (s₂ - s₁))) ∧
      ∃ H : Space m → ℝ, Measurable H ∧
        (∀ r < ρ, MemLp H 2 (volume.restrict (ball (0 : Space m) r))) ∧
        ∀ s : ℕ → ℝ, (∀ j, s j ∈ Icc s₁ s₂) → ∀ r < ρ,
          Tendsto (fun j ↦ ∫ y in ball (0 : Space m) r,
            (normalizedHeight (extendedHeight (D (φ j)) L τ s₁ s₂
              (fun s y ↦ slabLevelHeight (v (φ j)) τ s y) (s j)) (a j) (δ (φ j)) y - H y) ^ 2)
            atTop (𝓝 0) := by
  have hvert : ‖verticalDirection m‖ = 1 := by simp [verticalDirection]
  set ω := volume.real (ball (0 : Space m) 1) with hω
  have hω0 : 0 ≤ ω := measureReal_nonneg
  set M := (5 : ℝ) ^ m * ω * Θ / ℓ with hMdef
  have hM : 0 ≤ M := by positivity
  set Λ := ρ + τ + |r₀| with hΛ
  have hF0 : ∀ j x, 0 ≤ diffuseTiltDensity (T j) (v j) (verticalDirection m) x := fun j x ↦
    diffuseTiltDensity_nonneg (hT j) (v j) hvert x
  have hFint : ∀ j, IntegrableOn (diffuseTiltDensity (T j) (v j) (verticalDirection m))
      (closedBall (0 : Space (m + 1)) Λ) := fun j ↦
    integrableOn_diffuseTiltDensity (hvL j).locallyLipschitz (isCompact_closedBall _ _) _ hvert
  have hDo : ∀ j, IsOpen (D j) := by
    intro j
    rw [hDdef j]
    exact (isOpen_goodProjection (hT j) (hvL j) hvert ℓ r₀ b).inter isOpen_ball
  have hDball : ∀ j, D j ⊆ ball 0 ρ := by
    intro j
    rw [hDdef j]
    exact inter_subset_right
  -- HA1.2 on the good projection
  have hbad : ∀ᶠ j in atTop, volume (ball (0 : Space m) ρ \ D j) ≤
      ENNReal.ofReal (M * δ j ^ 2) := by
    filter_upwards [hV.eventually_volume_sdiff_goodProjection_le hT
      (fun j ↦ (hvL j).locallyLipschitz) hvert hℓ r₀ hb0 hb1 ρ hτ, htot] with j hj hjt
    have hsub : ball (0 : Space m) ρ \ D j ⊆
        closedBall 0 ρ \ goodProjection (T j) (v j) (verticalDirection m) ℓ r₀ b := by
      rintro y ⟨hy, hyD⟩
      refine ⟨ball_subset_closedBall hy, fun hyG ↦ hyD ?_⟩
      rw [hDdef j]
      exact ⟨hyG, hy⟩
    have hint : ∫ x in closedBall (0 : Space (m + 1)) (|ρ| + τ + |r₀|),
        diffuseTiltDensity (T j) (v j) (verticalDirection m) x ≤ Θ * δ j ^ 2 := by
      refine le_trans (setIntegral_mono_set (hFint j) (Eventually.of_forall (hF0 j))
        (Eventually.of_forall (closedBall_subset_closedBall ?_))) hjt
      rw [abs_of_pos hρ]
    have hω' : volume (ball (0 : Space m) 1) = ENNReal.ofReal ω :=
      (ofReal_measureReal measure_ball_lt_top.ne).symm
    calc
      volume (ball (0 : Space m) ρ \ D j) ≤
          volume (closedBall 0 ρ \ goodProjection (T j) (v j) (verticalDirection m) ℓ r₀ b) :=
        measure_mono hsub
      _ ≤ _ := hj
      _ ≤ (ENNReal.ofReal ((5 : ℝ) ^ m) * volume (ball (0 : Space m) 1) / ENNReal.ofReal ℓ) *
          ENNReal.ofReal (Θ * δ j ^ 2) := by gcongr
      _ = ENNReal.ofReal (M * δ j ^ 2) := by
        rw [hω', ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_div_of_pos hℓ,
          ← ENNReal.ofReal_mul (by positivity), hMdef]
        congr 1
        ring
  -- nonemptiness of the good sets
  have hDne : ∀ᶠ j in atTop, (D j).Nonempty := by
    have hvol : 0 < volume (ball (0 : Space m) ρ) := measure_ball_pos _ _ hρ
    have ht : Tendsto (fun j ↦ ENNReal.ofReal (M * δ j ^ 2)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun j ↦ M * δ j ^ 2) atTop (𝓝 (M * 0 ^ 2)) := (hδ0.pow 2).const_mul M
      rw [show M * (0 : ℝ) ^ 2 = 0 by ring] at h1
      simpa using ENNReal.tendsto_ofReal h1
    filter_upwards [hbad, ht.eventually (gt_mem_nhds hvol)] with j hj hjlt
    by_contra hne
    rw [not_nonempty_iff_eq_empty] at hne
    rw [hne, sdiff_empty] at hj
    exact absurd (hj.trans_lt hjlt) (lt_irrefl _)
  -- the level graph families
  have hG : ∀ᶠ j in atTop, LevelGraphFamily (v j) (D j) τ s₁ s₂ (T j) c L
      (fun s y ↦ slabLevelHeight (v j) τ s y) := by
    filter_upwards [hV.eventually_levelGraphFamily hdiff ρ hτ hs₁ hs₂ T L,
      hV.eventually_hasLevelSlope_of_cone hdiff hτ hs₁ hs₂ hT L, hcone, hslope]
      with j hj hjsign hjc hjs
    have hDsub : D j ⊆ closedBall 0 ρ := (hDball j).trans ball_subset_closedBall
    exact hj (D j) hDsub hjc (hjsign (D j) hDsub hjc hjs)
  -- the tilt of the level regions
  have htilt : ∀ᶠ j in atTop, ∫⁻ x in levelRegion (v j) (D j) τ s₁ s₂,
      ENNReal.ofReal (diffuseTiltDensity (T j) (v j) (verticalDirection m) x) ≤
        ENNReal.ofReal (Θ * δ j ^ 2) := by
    filter_upwards [htot] with j hj
    have hsub : levelRegion (v j) (D j) τ s₁ s₂ ⊆ closedBall (0 : Space (m + 1)) Λ :=
      (levelRegion_subset_closedBall (hDball j)).trans
        (closedBall_subset_closedBall (by rw [hΛ]; linarith [abs_nonneg r₀]))
    calc
      ∫⁻ x in levelRegion (v j) (D j) τ s₁ s₂,
          ENNReal.ofReal (diffuseTiltDensity (T j) (v j) (verticalDirection m) x) ≤
          ∫⁻ x in closedBall (0 : Space (m + 1)) Λ,
            ENNReal.ofReal (diffuseTiltDensity (T j) (v j) (verticalDirection m) x) :=
        lintegral_mono_set hsub
      _ = ENNReal.ofReal (∫ x in closedBall (0 : Space (m + 1)) Λ,
            diffuseTiltDensity (T j) (v j) (verticalDirection m) x) :=
        (ofReal_integral_eq_lintegral_ofReal (hFint j)
          (Eventually.of_forall (hF0 j))).symm
      _ ≤ ENNReal.ofReal (Θ * δ j ^ 2) := ENNReal.ofReal_le_ofReal hj
  exact exists_normalizedHeight_limit_of_eventually hG hT hc hs hDo hDne hδ hρ hM hΘ htilt hbad
    hratio

/-- Rotated rescalings of the zero extension are Lipschitz with constant `κ R`. -/
theorem RigidityHypotheses.lipschitzWith_rescaled (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) (c : Space (m + 1)) {R : ℝ} (hR : 0 ≤ R)
    (Q : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1)) :
    LipschitzWith (⟨κ, h.kappa_pos.le⟩ * Real.toNNReal R)
      (fun x ↦ zeroExtension g u (c + R • Q x)) := by
  have hA : LipschitzWith (Real.toNNReal R) (fun x : Space (m + 1) ↦ c + R • Q x) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_add_left, dist_eq_norm, dist_eq_norm, ← smul_sub, ← map_sub, norm_smul,
      LinearIsometryEquiv.norm_map, Real.norm_eq_abs, abs_of_nonneg hR, Real.coe_toNNReal _ hR]
  exact (hr.zeroExtension_lipschitzWith h).comp hA

/-- **HA2–HA3 for the actual rotated rescalings, modulo the HA9 graph conditions.** For
`v_j x = zeroExtension g u (c_j + R_j • Q_j x)`, where the unrotated rescalings converge locally in
`L¹` to the half-space `{⟪e, y⟫ > 0}` and `Q_j` carries the vertical direction to `e_j → e`, the
conclusions of `VerticalPlanarLayers.exists_normalizedHeight_limit` hold with `T_j = R_j`
(`ε_j = R_j⁻¹`) as soon as the total vertical tilt is `O(δ_j²)`, `δ_j → 0`, `R_j δ_j → ∞`, and
the cone condition and the unsigned slope bound hold on the good projections. -/
theorem RigidityHypotheses.exists_normalizedHeight_limit_of_cone
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hsharp : ∀ z : Space (m + 1), ∀ r : ℝ, 0 < r →
      (∫ x in closedBall z r, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤
        phasePrimitive f 1 * volume.real (closedBall (0 : Space m) 1) * r ^ m)
    (c₀ : ℕ → Space (m + 1)) {R : ℕ → ℝ} (hR : ∀ j, 0 < R j) (hRt : Tendsto R atTop atTop)
    {e : Space (m + 1)} (he : ‖e‖ = 1)
    (hlocal : ∀ K : Set (Space (m + 1)), IsCompact K →
      Tendsto (fun j ↦ ∫ x in K, ‖zeroExtension g u (c₀ j + R j • x) -
        {y : Space (m + 1) | 0 < inner ℝ e y}.indicator (fun _ ↦ (1 : ℝ)) x‖)
          atTop (𝓝 0))
    {Q : ℕ → Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1)}
    (hQ : Tendsto (fun j ↦ Q j (verticalDirection m)) atTop (𝓝 e))
    {v : ℕ → Space (m + 1) → ℝ}
    (hvdef : ∀ j, v j = fun x ↦ zeroExtension g u (c₀ j + R j • Q j x))
    {δ : ℕ → ℝ} (hδ : ∀ j, 0 < δ j) (hδ0 : Tendsto δ atTop (𝓝 0))
    (hratio : Tendsto (fun j ↦ R j * δ j) atTop atTop) {ℓ r₀ b ρ τ s₁ s₂ c Θ : ℝ} {L : ℝ≥0}
    (hℓ : 0 < ℓ) (hb0 : 0 ≤ b) (hb1 : b < 1) (hρ : 0 < ρ) (hτ : 0 < τ) (hs₁ : 0 < s₁)
    (hs : s₁ < s₂) (hs₂ : s₂ < 1) (hc : 0 < c) (hΘ : 0 ≤ Θ)
    (htot : ∀ᶠ j in atTop, ∫ x in closedBall (0 : Space (m + 1)) (ρ + τ + |r₀|),
      diffuseTiltDensity (R j) (v j) (verticalDirection m) x ≤ Θ * δ j ^ 2)
    {D : ℕ → Set (Space m)} (hDdef : ∀ j, D j = verticalGoodSet (R j) (v j) ℓ r₀ b ρ)
    (hcone : ∀ᶠ j in atTop, HasLevelCone (v j) (D j) τ s₁ s₂ L)
    (hslope : ∀ᶠ j in atTop, HasLevelSlopeAbs (v j) (D j) τ s₁ s₂ (R j) c) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ σ a : ℕ → ℝ, (∀ j, σ j ∈ Icc s₁ s₂) ∧
      (∀ j, a j = ⨍ z in ball (0 : Space m) ρ, extendedHeight (D (φ j)) L τ s₁ s₂
        (fun s y ↦ slabLevelHeight (v (φ j)) τ s y) (σ j) z) ∧
      (∀ j, ∫ y in ball (0 : Space m) ρ,
        (normalizedHeight (extendedHeight (D (φ j)) L τ s₁ s₂
            (fun s y ↦ slabLevelHeight (v (φ j)) τ s y) (σ j)) (a j) (δ (φ j)) y ^ 2 +
          ‖fderiv ℝ (normalizedHeight (extendedHeight (D (φ j)) L τ s₁ s₂
            (fun s y ↦ slabLevelHeight (v (φ j)) τ s y) (σ j)) (a j) (δ (φ j))) y‖ ^ 2) ≤
        (2 ^ (m + 1) * ρ ^ 2 + 1) * ((c⁻¹ * Θ + (s₂ - s₁) * (L : ℝ) ^ 2 *
          ((5 : ℝ) ^ m * volume.real (ball (0 : Space m) 1) * Θ / ℓ)) / (s₂ - s₁))) ∧
      ∃ H : Space m → ℝ, Measurable H ∧
        (∀ r < ρ, MemLp H 2 (volume.restrict (ball (0 : Space m) r))) ∧
        ∀ s : ℕ → ℝ, (∀ j, s j ∈ Icc s₁ s₂) → ∀ r < ρ,
          Tendsto (fun j ↦ ∫ y in ball (0 : Space m) r,
            (normalizedHeight (extendedHeight (D (φ j)) L τ s₁ s₂
              (fun s y ↦ slabLevelHeight (v (φ j)) τ s y) (s j)) (a j) (δ (φ j)) y - H y) ^ 2)
            atTop (𝓝 0) := by
  have hv : v = fun j x ↦ zeroExtension g u (c₀ j + R j • Q j x) := funext hvdef
  have hV : VerticalPlanarLayers v := by
    rw [hv]
    exact hr.verticalPlanarLayers_of_rotated h hsharp c₀ hR hRt he hlocal hQ
  have hvL : ∀ j, LipschitzWith (⟨κ, h.kappa_pos.le⟩ * Real.toNNReal (R j)) (v j) := by
    intro j
    rw [hvdef j]
    exact hr.lipschitzWith_rescaled h (c₀ j) (hR j).le (Q j)
  have hdiff : ∀ j x, 0 < v j x → DifferentiableAt ℝ (v j) x := by
    intro j x hx
    rw [hvdef j] at hx ⊢
    exact h.differentiableAt_rescaled_of_pos (c₀ j) (R j) (Q j) hx
  exact hV.exists_normalizedHeight_limit hvL hdiff hR hδ hδ0 hratio hℓ hb0 hb1 hρ hτ hs₁ hs hs₂
    hc hΘ htot hDdef hcone hslope

end SerrinEpigraph
