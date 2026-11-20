module

public import SerrinEpigraph.MicroscopicProfileLimit
public import SerrinEpigraph.HarmonicOneDimensionalLimit
public import SerrinEpigraph.PhysicalTranslationClearing
public import SerrinEpigraph.DiffuseGoodLayers
public import SerrinEpigraph.LowLevelHeightMoments

/-!
# Microscopic profile approximation at low positive points (HA10.a, HA10.b)

This file discharges the profile-approximation hypothesis of
`RigidityHypotheses.exists_low_level_bounds_of_profile_approximation` (blueprint
`harmonic-approximation.md`, HA10.a, HA10.b, with the classification HA9.a of
`SerrinEpigraph.MicroscopicProfileLimit`).

* `RigidityHypotheses.exists_microscopic_profile_dichotomy` (HA10.a, compactness): at a positive
  point `X` with `U(X) < 1 - b₀` whose physical tilt along a unit vector `e` is small on all balls
  of radius at most `ρ₀`, either `U` crosses the level `s` downward along the line `X + τ e` inside
  a fixed window, or every crossing of `s` on that line in a fixed window is a center of
  `α`-approximation of `U` by the translated layer profile on a ball of radius `K'`.
* `RigidityHypotheses.exists_low_profile_approximation` (HA10.a + HA10.b, rescaled): for the
  rotated rescaled translates, every low positive point over a good horizontal set `D` in the
  slab is either bad at a degraded threshold `ℓ'`, or `v` is `α`-close on `B_{Kα/R}(p)` to
  `q(R (t - H(y)))` with `H(y) = h_s(y) - T(s)/R`. The downward crossings are excluded by the cone
  condition at the level `s`, and the microscopic window by the nondegeneracy (CO3).
* `RigidityHypotheses.exists_low_level_bounds_on_good_slab` (HA10.c assembled): the low-level mass
  and height moments over the low points of the slab that are not bad, via
  `RigidityHypotheses.exists_low_level_bounds_of_approximation_on`.

The cone condition at the level `s` (HA9.d), the slab facts (HA8) and the treatment of the bad
low points (HA1.1, thin layer) are hypotheses or left to the consumer.
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory Filter InnerProductSpace
open scoped Topology ContDiff NNReal

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}

/-! ### Tilt along a limit direction -/

private theorem norm_gradient_le_of_lipschitzWith {d : ℕ} {U : Space d → ℝ} {K : ℝ≥0}
    (hU : LipschitzWith K U) (x : Space d) : ‖gradient U x‖ ≤ K := by
  simp only [gradient, LinearIsometryEquiv.norm_map]
  exact norm_fderiv_le_of_lipschitz ℝ hU

/-- Small tilt along directions `e_j → e` on balls of radius up to `ρ₀_j → ∞` gives vanishing tilt
along `e` on every compact set. -/
theorem tilt_tendsto_zero_of_small_tilt {U : Space (m + 1) → ℝ} {K₀ : ℝ≥0}
    (hU : LipschitzWith K₀ U) (X : ℕ → Space (m + 1)) (ev : ℕ → Space (m + 1))
    (hev : ∀ j, ‖ev j‖ = 1) {e : Space (m + 1)} (he : ‖e‖ = 1)
    (hconv : Tendsto ev atTop (𝓝 e)) {ℓ ρ₀ : ℕ → ℝ} (hℓ : Tendsto ℓ atTop (𝓝 0))
    (hρ₀ : Tendsto ρ₀ atTop atTop)
    (htilt : ∀ j, ∀ ρ ∈ Ioc 0 (ρ₀ j),
      ∫ z in ball (X j) ρ, diffuseTiltDensity 1 U (ev j) z < ℓ j * ρ ^ m)
    (K : Set (Space (m + 1))) (hK : IsCompact K) :
    Tendsto (fun j ↦ ∫ y in K, diffuseTiltDensity 1 (fun z ↦ U (X j + z)) e y) atTop (𝓝 0) := by
  obtain ⟨ρ', hKρ'⟩ := hK.isBounded.subset_ball (0 : Space (m + 1))
  set ρ := max ρ' 1 with hρdef
  have hρ : 0 < ρ := lt_max_of_lt_right one_pos
  have hKρ : K ⊆ ball 0 ρ := hKρ'.trans (ball_subset_ball (le_max_left _ _))
  have hgradT : ∀ j y, gradient (fun z ↦ U (X j + z)) y = gradient U (X j + y) := by
    intro j y
    simp only [gradient, fderiv_comp_add_left]
  have hLipT : ∀ j, LipschitzWith K₀ (fun z ↦ U (X j + z)) := by
    intro j
    apply LipschitzWith.of_dist_le_mul
    intro y z
    simpa only [dist_add_left] using hU.dist_le_mul (X j + y) (X j + z)
  -- pointwise comparison of the tilts along `e` and `e_j`
  have hpt : ∀ j y, diffuseTiltDensity 1 (fun z ↦ U (X j + z)) e y ≤
      diffuseTiltDensity 1 (fun z ↦ U (X j + z)) (ev j) y + 2 * (K₀ : ℝ) ^ 2 * ‖ev j - e‖ := by
    intro j y
    set G := gradient (fun z ↦ U (X j + z)) y with hG
    have hGn : ‖G‖ ≤ K₀ := norm_gradient_le_of_lipschitzWith (hLipT j) y
    have h1 : |inner ℝ G (ev j) - inner ℝ G e| ≤ ‖G‖ * ‖ev j - e‖ := by
      rw [← inner_sub_right]
      exact abs_real_inner_le_norm _ _
    have h2 : |inner ℝ G (ev j) + inner ℝ G e| ≤ 2 * ‖G‖ := by
      rw [← inner_add_right]
      calc |inner ℝ G (ev j + e)| ≤ ‖G‖ * ‖ev j + e‖ := abs_real_inner_le_norm _ _
        _ ≤ ‖G‖ * 2 := by
            apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
            calc ‖ev j + e‖ ≤ ‖ev j‖ + ‖e‖ := norm_add_le _ _
              _ = 2 := by rw [hev j, he]; norm_num
        _ = 2 * ‖G‖ := by ring
    have h3 : inner ℝ G (ev j) ^ 2 - inner ℝ G e ^ 2 ≤ 2 * (K₀ : ℝ) ^ 2 * ‖ev j - e‖ := by
      have hfac : inner ℝ G (ev j) ^ 2 - inner ℝ G e ^ 2 =
          (inner ℝ G (ev j) - inner ℝ G e) * (inner ℝ G (ev j) + inner ℝ G e) := by ring
      rw [hfac]
      calc _ ≤ |(inner ℝ G (ev j) - inner ℝ G e) * (inner ℝ G (ev j) + inner ℝ G e)| :=
            le_abs_self _
        _ = |inner ℝ G (ev j) - inner ℝ G e| * |inner ℝ G (ev j) + inner ℝ G e| := abs_mul _ _
        _ ≤ (‖G‖ * ‖ev j - e‖) * (2 * ‖G‖) :=
            mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
        _ = 2 * ‖G‖ ^ 2 * ‖ev j - e‖ := by ring
        _ ≤ 2 * (K₀ : ℝ) ^ 2 * ‖ev j - e‖ := by
            have := pow_le_pow_left₀ (norm_nonneg G) hGn 2
            have := norm_nonneg (ev j - e)
            nlinarith
    simp only [diffuseTiltDensity, div_one]
    linarith
  -- the integral bound
  have hbound : ∀ᶠ j in atTop, ∫ y in K, diffuseTiltDensity 1 (fun z ↦ U (X j + z)) e y ≤
      ℓ j * ρ ^ m + 2 * (K₀ : ℝ) ^ 2 * ‖ev j - e‖ * volume.real K := by
    filter_upwards [hρ₀.eventually_ge_atTop ρ] with j hj
    have hint_e := integrableOn_diffuseTiltDensity (hLipT j).locallyLipschitz hK 1 he
    have hint_j := integrableOn_diffuseTiltDensity (hLipT j).locallyLipschitz hK 1 (hev j)
    have hint_ball := integrableOn_diffuseTiltDensity (hLipT j).locallyLipschitz
      (isCompact_closedBall (0 : Space (m + 1)) ρ) 1 (hev j)
    have hconst : IntegrableOn (fun _ : Space (m + 1) ↦ 2 * (K₀ : ℝ) ^ 2 * ‖ev j - e‖) K :=
      integrableOn_const hK.measure_lt_top.ne
    have hstep1 : ∫ y in K, diffuseTiltDensity 1 (fun z ↦ U (X j + z)) e y ≤
        ∫ y in K, (diffuseTiltDensity 1 (fun z ↦ U (X j + z)) (ev j) y +
          2 * (K₀ : ℝ) ^ 2 * ‖ev j - e‖) :=
      setIntegral_mono hint_e (hint_j.add hconst) (hpt j)
    rw [integral_add hint_j hconst, setIntegral_const, smul_eq_mul] at hstep1
    have hstep2 : ∫ y in K, diffuseTiltDensity 1 (fun z ↦ U (X j + z)) (ev j) y ≤
        ∫ y in ball (0 : Space (m + 1)) ρ, diffuseTiltDensity 1 (fun z ↦ U (X j + z)) (ev j) y :=
      setIntegral_mono_set (hint_ball.mono_set ball_subset_closedBall)
        (Eventually.of_forall fun y ↦ diffuseTiltDensity_nonneg one_pos _ (hev j) y)
        (Eventually.of_forall hKρ)
    have hstep3 : ∫ y in ball (0 : Space (m + 1)) ρ,
        diffuseTiltDensity 1 (fun z ↦ U (X j + z)) (ev j) y =
        ∫ z in ball (X j) ρ, diffuseTiltDensity 1 U (ev j) z := by
      have hfun : ∀ y, diffuseTiltDensity 1 (fun z ↦ U (X j + z)) (ev j) y =
          diffuseTiltDensity 1 U (ev j) (X j + y) := by
        intro y
        simp only [diffuseTiltDensity, hgradT]
      simp_rw [hfun]
      have hh := setIntegral_ball_comp_translate_dilation_isometry
        (diffuseTiltDensity 1 U (ev j)) (X j) one_pos
        (LinearIsometryEquiv.refl ℝ (Space (m + 1))) 0 ρ
      simpa using hh
    have hstep4 := htilt j ρ ⟨hρ, hj⟩
    nlinarith [hstep1, hstep2, hstep3, hstep4]
  have hlim : Tendsto (fun j ↦ ℓ j * ρ ^ m + 2 * (K₀ : ℝ) ^ 2 * ‖ev j - e‖ * volume.real K)
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun j ↦ ‖ev j - e‖) atTop (𝓝 0) := by
      have := (hconv.sub (tendsto_const_nhds (x := e))).norm
      simpa using this
    have := (hℓ.mul_const (ρ ^ m)).add ((h1.const_mul (2 * (K₀ : ℝ) ^ 2)).mul_const
      (volume.real K))
    simpa using this
  refine squeeze_zero' (Eventually.of_forall fun j ↦ ?_) hbound hlim
  exact setIntegral_nonneg hK.measurableSet fun y _ ↦ diffuseTiltDensity_nonneg one_pos _ he y

/-! ### Limits at anchors -/

/-- **Limits at anchors.** Physical translates about positive anchors `X_j` with small tilt along
`e_j` on growing balls converge, along a subsequence, to a one-dimensional `κ`-Lipschitz limit `V`
along a limit direction `e`, with `0` in the closure of the positive phase of `V` and
`V 0 ≤ 1 - b₀`; bounded auxiliary sequences converge along the same subsequence. -/
theorem RigidityHypotheses.exists_anchor_limit (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) (X : ℕ → Space (m + 1)) (ev : ℕ → Space (m + 1))
    (hev : ∀ j, ‖ev j‖ = 1) {ℓ ρ₀ : ℕ → ℝ} (hℓ : Tendsto ℓ atTop (𝓝 0))
    (hρ₀ : Tendsto ρ₀ atTop atTop)
    (htilt : ∀ j, ∀ ρ ∈ Ioc 0 (ρ₀ j),
      ∫ z in ball (X j) ρ, diffuseTiltDensity 1 (zeroExtension g u) (ev j) z < ℓ j * ρ ^ m)
    (hpos : ∀ j, 0 < zeroExtension g u (X j)) {b₀ : ℝ}
    (hb : ∀ j, zeroExtension g u (X j) ≤ 1 - b₀) {M K' : ℝ} (τ : ℕ → ℝ)
    (hτ : ∀ j, τ j ∈ Icc (-M) M) (Z : ℕ → Space (m + 1)) (hZ : ∀ j, Z j ∈ closedBall 0 K') :
    ∃ (φ : ℕ → ℕ) (e : Space (m + 1)) (V : Space (m + 1) → ℝ) (τlim : ℝ) (Zlim : Space (m + 1)),
      StrictMono φ ∧ ‖e‖ = 1 ∧ Tendsto (fun j ↦ ev (φ j)) atTop (𝓝 e) ∧
      Tendsto (fun j ↦ τ (φ j)) atTop (𝓝 τlim) ∧ Tendsto (fun j ↦ Z (φ j)) atTop (𝓝 Zlim) ∧
      τlim ∈ Icc (-M) M ∧ Zlim ∈ closedBall 0 K' ∧
      LipschitzWith ⟨κ, h.kappa_pos.le⟩ V ∧ (∀ x, V x ∈ Icc 0 1) ∧
      (∀ K : Set (Space (m + 1)), IsCompact K →
        TendstoUniformlyOn (fun j x ↦ zeroExtension g u (X (φ j) + x)) V atTop K) ∧
      (∀ x, V x = V ((inner ℝ e x) • e)) ∧ V 0 ≤ 1 - b₀ ∧
      (0 : Space (m + 1)) ∈ closure {x | 0 < V x} := by
  -- compactness of the direction and the auxiliary data
  have hcpt : IsCompact (sphere (0 : Space (m + 1)) 1 ×ˢ (Icc (-M) M ×ˢ closedBall
      (0 : Space (m + 1)) K')) :=
    (isCompact_sphere 0 1).prod (isCompact_Icc.prod (isCompact_closedBall 0 K'))
  obtain ⟨⟨e, τlim, Zlim⟩, ⟨he, hτlim, hZlim⟩, φ₁, hφ₁, hconv⟩ := hcpt.tendsto_subseq
    (x := fun j ↦ (ev j, τ j, Z j)) (fun j ↦ ⟨by simp [hev j], hτ j, hZ j⟩)
  have he' : ‖e‖ = 1 := by simpa using he
  have hconv_e : Tendsto (fun j ↦ ev (φ₁ j)) atTop (𝓝 e) := by
    have := (continuous_fst.tendsto _).comp hconv
    simpa [Function.comp_def] using this
  have hconv_τ : Tendsto (fun j ↦ τ (φ₁ j)) atTop (𝓝 τlim) := by
    have := (continuous_fst.comp continuous_snd |>.tendsto _).comp hconv
    simpa [Function.comp_def] using this
  have hconv_Z : Tendsto (fun j ↦ Z (φ₁ j)) atTop (𝓝 Zlim) := by
    have := (continuous_snd.comp continuous_snd |>.tendsto _).comp hconv
    simpa [Function.comp_def] using this
  -- vanishing tilt along `e` and the one-dimensional limit
  have ht : ∀ K : Set (Space (m + 1)), IsCompact K →
      Tendsto (fun j ↦ ∫ y in K,
        diffuseTiltDensity 1 (fun z ↦ zeroExtension g u (X (φ₁ j) + z)) e y) atTop (𝓝 0) :=
    fun K hK ↦ tilt_tendsto_zero_of_small_tilt (hr.zeroExtension_lipschitzWith h)
      (X ∘ φ₁) (ev ∘ φ₁) (fun j ↦ hev _) he' hconv_e (hℓ.comp hφ₁.tendsto_atTop)
      (hρ₀.comp hφ₁.tendsto_atTop) (fun j ↦ htilt (φ₁ j)) K hK
  obtain ⟨φ₂, V, hφ₂, hV, hVval, hlim, -, hprofile⟩ :=
    hr.exists_oneDimensional_physical_translation_limit h (X ∘ φ₁) he' ht
  refine ⟨φ₁ ∘ φ₂, e, V, τlim, Zlim, hφ₁.comp hφ₂, he', hconv_e.comp hφ₂.tendsto_atTop,
    hconv_τ.comp hφ₂.tendsto_atTop, hconv_Z.comp hφ₂.tendsto_atTop, hτlim, hZlim, hV, hVval,
    hlim, hprofile, ?_, ?_⟩
  · have h0 : Tendsto (fun j ↦ zeroExtension g u (X (φ₁ (φ₂ j)) + 0)) atTop (𝓝 (V 0)) :=
      (hlim {0} isCompact_singleton).tendsto_at (mem_singleton 0)
    exact le_of_tendsto' h0 fun j ↦ by rw [add_zero]; exact hb _
  · exact hr.physical_translation_limit_mem_closure_positive h (fun x ↦ (hVval x).1)
      (fun j ↦ hpos _) hlim

/-- Values of the translates at convergent points converge to the limit. -/
theorem tendsto_translate_of_tendsto {X : ℕ → Space (m + 1)} {V : Space (m + 1) → ℝ}
    (hVc : Continuous V)
    (hlim : ∀ K : Set (Space (m + 1)), IsCompact K →
      TendstoUniformlyOn (fun j x ↦ zeroExtension g u (X j + x)) V atTop K)
    {Y : ℕ → Space (m + 1)} {y : Space (m + 1)} (hY : Tendsto Y atTop (𝓝 y)) :
    Tendsto (fun j ↦ zeroExtension g u (X j + Y j)) atTop (𝓝 (V y)) := by
  have hK := isCompact_closedBall y 1
  exact (hlim _ hK).tendsto_comp hVc.continuousWithinAt
    (tendsto_nhdsWithin_iff.mpr ⟨hY, hY (closedBall_mem_nhds y one_pos)⟩)

/-- The anchor of a one-dimensional limit lies in the closure of the positive set of its profile. -/
private theorem mem_closure_profile_of_mem_closure {d : ℕ} {V : Space d → ℝ} {e : Space d}
    (he : ‖e‖ = 1) (h1D : ∀ x, V x = V ((inner ℝ e x) • e))
    (hcl : (0 : Space d) ∈ closure {x | 0 < V x}) :
    (0 : ℝ) ∈ closure {τ : ℝ | 0 < V (τ • e)} := by
  rw [Metric.mem_closure_iff] at hcl ⊢
  intro ε hε
  obtain ⟨x, hx, hdist⟩ := hcl ε hε
  refine ⟨inner ℝ e x, ?_, ?_⟩
  · change 0 < V (inner ℝ e x • e)
    rw [← h1D x]
    exact hx
  · rw [Real.dist_eq, zero_sub, abs_neg]
    calc |inner ℝ e x| ≤ ‖e‖ * ‖x‖ := abs_real_inner_le_norm _ _
      _ = dist 0 x := by rw [he, one_mul, dist_comm, dist_zero_right]
      _ < ε := hdist

/-- The layer profile hits a positive level only at its travel time. -/
private theorem RigidityHypotheses.eq_travelTime_of_layerProfile_eq
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) {s x : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1)
    (hx : layerProfile f x = s) : x = layerTravelTime f s := by
  have hxpos : 0 < x := by
    by_contra hn
    rw [layerProfile_of_nonpos f (not_lt.mp hn)] at hx
    linarith [hs.1]
  have := (hr.layerProfile_spec h hxpos.le).2
  rw [hx] at this
  exact this.symm

/-- **HA10.a, crossing part.** -/
theorem RigidityHypotheses.exists_microscopic_crossing (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) {L : ℝ}
    (hbound : ∀ z : Space (m + 1), ∀ r : ℝ, 0 < r →
      (∫ x in closedBall z r, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤ L * r ^ m)
    {b₀ s M₀ : ℝ} (hb₀ : b₀ ∈ Ioo (0 : ℝ) 1) (hs : s ∈ Ioo (0 : ℝ) 1)
    (hM₀ : layerTravelTime f (1 - b₀) + 1 ≤ M₀) :
    ∃ ℓ ρ₀ : ℝ, 0 < ℓ ∧ 0 < ρ₀ ∧ ∀ (X e : Space (m + 1)), ‖e‖ = 1 →
      zeroExtension g u X ∈ Ioo 0 (1 - b₀) →
      (∀ ρ ∈ Ioc 0 ρ₀, ∫ z in ball X ρ, diffuseTiltDensity 1 (zeroExtension g u) e z <
        ℓ * ρ ^ m) →
      (∃ τ₁ τ₂ : ℝ, -(M₀ + layerTravelTime f s + 2) ≤ τ₁ ∧ τ₁ < τ₂ ∧
        τ₂ ≤ layerTravelTime f (1 - b₀) ∧ s < zeroExtension g u (X + τ₁ • e) ∧
        zeroExtension g u (X + τ₂ • e) < s) ∨
      ∃ τ ∈ Icc (-(layerTravelTime f (1 - b₀) + 1)) (layerTravelTime f s + 1),
        zeroExtension g u (X + τ • e) = s := by
  by_contra hcon
  simp only [not_exists, not_and, not_or, not_forall] at hcon
  have hseq : ∀ j : ℕ, ∃ X e : Space (m + 1), ‖e‖ = 1 ∧ zeroExtension g u X ∈ Ioo 0 (1 - b₀) ∧
      (∀ ρ ∈ Ioc 0 ((j : ℝ) + 1), ∫ z in ball X ρ, diffuseTiltDensity 1 (zeroExtension g u) e z <
        1 / ((j : ℝ) + 1) * ρ ^ m) ∧
      (¬∃ τ₁ τ₂ : ℝ, -(M₀ + layerTravelTime f s + 2) ≤ τ₁ ∧ τ₁ < τ₂ ∧
        τ₂ ≤ layerTravelTime f (1 - b₀) ∧ s < zeroExtension g u (X + τ₁ • e) ∧
        zeroExtension g u (X + τ₂ • e) < s) ∧
      ¬∃ τ ∈ Icc (-(layerTravelTime f (1 - b₀) + 1)) (layerTravelTime f s + 1),
        zeroExtension g u (X + τ • e) = s := by
    intro j
    obtain ⟨X, e, he, hX, htilt, hA, hB⟩ := hcon (1 / ((j : ℝ) + 1)) ((j : ℝ) + 1)
      (by positivity) (by positivity)
    refine ⟨X, e, he, hX, htilt, ?_, ?_⟩
    · rintro ⟨τ₁, τ₂, h1, h2, h3, h4, h5⟩
      exact hA τ₁ τ₂ h1 h2 h3 h4 h5
    · rintro ⟨τ, hτ, hτs⟩
      exact hB τ hτ hτs
  choose X ev hev hX htilt hA hB using hseq
  have hℓ : Tendsto (fun j : ℕ ↦ 1 / ((j : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hρ₀ : Tendsto (fun j : ℕ ↦ (j : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  obtain ⟨φ, e, V, -, -, hφ, he, hconv, -, -, -, -, hV, hVval, hlim, h1D, hV0, hcl⟩ :=
    hr.exists_anchor_limit h X ev hev hℓ hρ₀ htilt (fun j ↦ (hX j).1) (fun j ↦ (hX j).2.le)
      (M := 0) (K' := 0) (fun _ ↦ 0) (fun _ ↦ ⟨by norm_num, le_rfl⟩) (fun _ ↦ 0)
      (fun _ ↦ mem_closedBall_self le_rfl)
  have hP := hr.isHamiltonianProfile_of_oneDimensional_limit h hbound hV hVval hlim he h1D
  have hcl' := mem_closure_profile_of_mem_closure he h1D hcl
  have hP0 : V ((0 : ℝ) • e) ≤ 1 - b₀ := by rwa [zero_smul]
  have hTb : 0 ≤ layerTravelTime f (1 - b₀) :=
    hr.layerTravelTime_nonneg h ⟨by linarith [hb₀.2], by linarith [hb₀.1]⟩
  have hTs : 0 < layerTravelTime f s := hr.layerTravelTime_pos h hs
  have hline : ∀ σ : ℝ, Tendsto (fun j ↦ zeroExtension g u (X (φ j) + σ • ev (φ j))) atTop
      (𝓝 (V (σ • e))) := fun σ ↦
    tendsto_translate_of_tendsto hV.continuous hlim (tendsto_const_nhds.smul hconv)
  rcases hP.anchored_dichotomy hr h (M₀ := M₀) hb₀ hs (by linarith) hP0 hcl' with hinc | hdown
  · -- an increasing profile crosses `s` near `T(s) - T(P 0)`
    set s₀ := V ((0 : ℝ) • e)
    have hs₀ : s₀ ∈ Ico (0 : ℝ) 1 := ⟨(hVval _).1, by linarith [hb₀.1]⟩
    have hTs₀ : layerTravelTime f s₀ ≤ layerTravelTime f (1 - b₀) :=
      (hr.layerTravelTime_strictMonoOn h).monotoneOn hs₀
        ⟨by linarith [hb₀.2], by linarith [hb₀.1]⟩ hP0
    have hTs₀0 := hr.layerTravelTime_nonneg h hs₀
    set σ := layerTravelTime f s - layerTravelTime f s₀ with hσ
    set γ := min (layerTravelTime f s) 1 / 2 with hγ
    have hγpos : 0 < γ := by positivity
    have hγ1 : γ ≤ 1 / 2 := by
      have := min_le_right (layerTravelTime f s) 1
      rw [hγ]; linarith
    have hγs : γ < layerTravelTime f s := by
      have := min_le_left (layerTravelTime f s) 1
      rw [hγ]; linarith
    have hlow : V ((σ - γ) • e) < s := by
      have heq := hinc (σ - γ) (by linarith)
      change V ((σ - γ) • e) = layerProfile f (σ - γ + layerTravelTime f s₀) at heq
      rw [heq, show σ - γ + layerTravelTime f s₀ = layerTravelTime f s - γ by rw [hσ]; ring]
      exact hr.layerProfile_lt_of_lt_travelTime h hs (by linarith)
    have hhigh : s < V ((σ + γ) • e) := by
      have heq := hinc (σ + γ) (by linarith)
      change V ((σ + γ) • e) = layerProfile f (σ + γ + layerTravelTime f s₀) at heq
      rw [heq, show σ + γ + layerTravelTime f s₀ = layerTravelTime f s + γ by rw [hσ]; ring]
      exact hr.lt_layerProfile_of_travelTime_lt h ⟨hs.1.le, hs.2⟩ (by linarith)
    obtain ⟨j, hj1, hj2⟩ := ((hline (σ - γ)).eventually (gt_mem_nhds hlow)).and
      ((hline (σ + γ)).eventually (lt_mem_nhds hhigh)) |>.exists
    have hcont : ContinuousOn (fun τ : ℝ ↦ zeroExtension g u (X (φ j) + τ • ev (φ j)))
        (Icc (σ - γ) (σ + γ)) :=
      (h.zeroExtension_continuous.comp (continuous_const.add
        (continuous_id.smul continuous_const))).continuousOn
    obtain ⟨τ, hτ, hτs⟩ := intermediate_value_Icc (by linarith) hcont ⟨hj1.le, hj2.le⟩
    exact hB (φ j) ⟨τ, ⟨by linarith [hτ.1], by linarith [hτ.2]⟩, hτs⟩
  · obtain ⟨σ₁, σ₂, h1, h2, h3, h4, h5⟩ := hdown
    obtain ⟨j, hj1, hj2⟩ := ((hline σ₁).eventually (lt_mem_nhds h4)).and
      ((hline σ₂).eventually (gt_mem_nhds h5)) |>.exists
    exact hA (φ j) ⟨σ₁, σ₂, by linarith, h2, h3, hj1, hj2⟩

/-- **HA10.a, approximation part.** -/
theorem RigidityHypotheses.exists_microscopic_approximation (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) {L : ℝ}
    (hbound : ∀ z : Space (m + 1), ∀ r : ℝ, 0 < r →
      (∫ x in closedBall z r, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤ L * r ^ m)
    {α K' b₀ s M₀ : ℝ} (hα : 0 < α) (hK' : 0 ≤ K') (hb₀ : b₀ ∈ Ioo (0 : ℝ) 1)
    (hs : s ∈ Ioo (0 : ℝ) 1) (hM₀ : K' + layerTravelTime f (1 - b₀) + 1 ≤ M₀) :
    ∃ ℓ ρ₀ : ℝ, 0 < ℓ ∧ 0 < ρ₀ ∧ ∀ (X e : Space (m + 1)), ‖e‖ = 1 →
      zeroExtension g u X ∈ Ioo 0 (1 - b₀) →
      (∀ ρ ∈ Ioc 0 ρ₀, ∫ z in ball X ρ, diffuseTiltDensity 1 (zeroExtension g u) e z <
        ℓ * ρ ^ m) →
      (∃ τ₁ τ₂ : ℝ, -(M₀ + layerTravelTime f s + 2) ≤ τ₁ ∧ τ₁ < τ₂ ∧
        τ₂ ≤ layerTravelTime f (1 - b₀) ∧ s < zeroExtension g u (X + τ₁ • e) ∧
        zeroExtension g u (X + τ₂ • e) < s) ∨
      ∀ τ ∈ Icc (-(layerTravelTime f (1 - b₀) + 1)) (layerTravelTime f s + 1),
        zeroExtension g u (X + τ • e) = s → ∀ Z ∈ closedBall (0 : Space (m + 1)) K',
          |zeroExtension g u (X + Z) - layerProfile f (inner ℝ e Z - τ + layerTravelTime f s)|
            ≤ α := by
  by_contra hcon
  simp only [not_exists, not_and, not_or, not_forall, not_le] at hcon
  set W := Icc (-(layerTravelTime f (1 - b₀) + 1)) (layerTravelTime f s + 1) with hW
  have hseq : ∀ j : ℕ, ∃ (X e : Space (m + 1)) (τ : ℝ) (Z : Space (m + 1)), ‖e‖ = 1 ∧
      zeroExtension g u X ∈ Ioo 0 (1 - b₀) ∧
      (∀ ρ ∈ Ioc 0 ((j : ℝ) + 1), ∫ z in ball X ρ, diffuseTiltDensity 1 (zeroExtension g u) e z <
        1 / ((j : ℝ) + 1) * ρ ^ m) ∧
      (¬∃ τ₁ τ₂ : ℝ, -(M₀ + layerTravelTime f s + 2) ≤ τ₁ ∧ τ₁ < τ₂ ∧
        τ₂ ≤ layerTravelTime f (1 - b₀) ∧ s < zeroExtension g u (X + τ₁ • e) ∧
        zeroExtension g u (X + τ₂ • e) < s) ∧
      τ ∈ W ∧ zeroExtension g u (X + τ • e) = s ∧ Z ∈ closedBall (0 : Space (m + 1)) K' ∧
      α < |zeroExtension g u (X + Z) - layerProfile f (inner ℝ e Z - τ + layerTravelTime f s)| := by
    intro j
    obtain ⟨X, e, he, hX, htilt, hA, τ, hτ, hτs, Z, hZ, hbad⟩ :=
      hcon (1 / ((j : ℝ) + 1)) ((j : ℝ) + 1) (by positivity) (by positivity)
    refine ⟨X, e, τ, Z, he, hX, htilt, ?_, hτ, hτs, hZ, hbad⟩
    rintro ⟨τ₁, τ₂, h1, h2, h3, h4, h5⟩
    exact hA τ₁ τ₂ h1 h2 h3 h4 h5
  choose X ev τ Z hev hX htilt hA hτ hτs hZ hbad using hseq
  have hℓ : Tendsto (fun j : ℕ ↦ 1 / ((j : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hρ₀ : Tendsto (fun j : ℕ ↦ (j : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have hTb : 0 ≤ layerTravelTime f (1 - b₀) :=
    hr.layerTravelTime_nonneg h ⟨by linarith [hb₀.2], by linarith [hb₀.1]⟩
  have hTs : 0 < layerTravelTime f s := hr.layerTravelTime_pos h hs
  have hτM : ∀ j, τ j ∈ Icc (-(layerTravelTime f (1 - b₀) + layerTravelTime f s + 1))
      (layerTravelTime f (1 - b₀) + layerTravelTime f s + 1) := fun j ↦
    ⟨by linarith [(hτ j).1], by linarith [(hτ j).2]⟩
  obtain ⟨φ, e, V, τlim, Zlim, hφ, he, hconv, hconvτ, hconvZ, -, hZlim, hV, hVval, hlim, h1D,
    hV0, hcl⟩ := hr.exists_anchor_limit h X ev hev hℓ hρ₀ htilt (fun j ↦ (hX j).1)
      (fun j ↦ (hX j).2.le) τ hτM Z hZ
  have hP := hr.isHamiltonianProfile_of_oneDimensional_limit h hbound hV hVval hlim he h1D
  have hcl' := mem_closure_profile_of_mem_closure he h1D hcl
  have hP0 : V ((0 : ℝ) • e) ≤ 1 - b₀ := by rwa [zero_smul]
  have hline : ∀ σ : ℝ, Tendsto (fun j ↦ zeroExtension g u (X (φ j) + σ • ev (φ j))) atTop
      (𝓝 (V (σ • e))) := fun σ ↦
    tendsto_translate_of_tendsto hV.continuous hlim (tendsto_const_nhds.smul hconv)
  rcases hP.anchored_dichotomy hr h (M₀ := M₀) hb₀ hs (by linarith) hP0 hcl' with hinc | hdown
  · set s₀ := V ((0 : ℝ) • e)
    -- the limit crossing
    have hτW : τlim ∈ W := isClosed_Icc.mem_of_tendsto hconvτ
      (Eventually.of_forall fun j ↦ hτ (φ j))
    have hVτ : V (τlim • e) = s := by
      have h1 := tendsto_translate_of_tendsto hV.continuous hlim (hconvτ.smul hconv)
      have h2 : (fun j ↦ zeroExtension g u (X (φ j) + τ (φ j) • ev (φ j))) = fun _ ↦ s :=
        funext fun j ↦ hτs (φ j)
      rw [h2] at h1
      exact tendsto_nhds_unique h1 tendsto_const_nhds
    have hτcross : τlim + layerTravelTime f s₀ = layerTravelTime f s := by
      have heq := hinc τlim (by linarith [hτW.1])
      change V (τlim • e) = layerProfile f (τlim + layerTravelTime f s₀) at heq
      rw [hVτ] at heq
      exact hr.eq_travelTime_of_layerProfile_eq h hs heq.symm
    -- the limit approximation
    have hZe : -M₀ ≤ inner ℝ e Zlim := by
      have h1 : |inner ℝ e Zlim| ≤ K' := by
        calc |inner ℝ e Zlim| ≤ ‖e‖ * ‖Zlim‖ := abs_real_inner_le_norm _ _
          _ ≤ K' := by rw [he, one_mul]; simpa using hZlim
      linarith [neg_abs_le (inner ℝ e Zlim)]
    have hVZ : V Zlim = layerProfile f (inner ℝ e Zlim - τlim + layerTravelTime f s) := by
      rw [h1D Zlim, hinc _ hZe, show inner ℝ e Zlim + layerTravelTime f s₀ =
        inner ℝ e Zlim - τlim + layerTravelTime f s by linarith]
    have hU : Tendsto (fun j ↦ zeroExtension g u (X (φ j) + Z (φ j))) atTop (𝓝 (V Zlim)) :=
      tendsto_translate_of_tendsto hV.continuous hlim hconvZ
    have hq : Tendsto (fun j ↦ layerProfile f (inner ℝ (ev (φ j)) (Z (φ j)) - τ (φ j) +
        layerTravelTime f s)) atTop
        (𝓝 (layerProfile f (inner ℝ e Zlim - τlim + layerTravelTime f s))) := by
      apply ((hr.continuous_layerProfile h).tendsto _).comp
      exact ((hconv.inner hconvZ).sub hconvτ).add tendsto_const_nhds
    have hdiff := (hU.sub hq)
    rw [hVZ, sub_self] at hdiff
    obtain ⟨j, hj⟩ := (hdiff.abs.eventually (gt_mem_nhds (by rw [abs_zero]; exact hα))).exists
    exact absurd (hbad (φ j)) (not_lt.mpr hj.le)
  · obtain ⟨σ₁, σ₂, h1, h2, h3, h4, h5⟩ := hdown
    obtain ⟨j, hj1, hj2⟩ := ((hline σ₁).eventually (lt_mem_nhds h4)).and
      ((hline σ₂).eventually (gt_mem_nhds h5)) |>.exists
    exact hA (φ j) ⟨σ₁, σ₂, by linarith, h2, h3, hj1, hj2⟩

/-- **HA10.a (microscopic profile dichotomy).** For `α > 0`, `K' ≥ 0`, `b₀, s ∈ (0, 1)` there are
`ℓ, ρ₀ > 0` such that, at every positive point `X` with `U(X) < 1 - b₀` and physical tilt along a
unit vector `e` below `ℓ ρ^m` on all balls `B_ρ(X)`, `0 < ρ ≤ ρ₀`: either `U` crosses `s` downward
along `X + τ e` in a fixed window, or `U` crosses `s` along that line in the window
`[-(T(1-b₀) + 1), T(s) + 1]` and every such crossing `τ` is a center of `α`-approximation:
`|U(X + Z) - q(⟪e, Z⟫ - τ + T(s))| ≤ α` for `‖Z‖ ≤ K'`. -/
theorem RigidityHypotheses.exists_microscopic_profile_dichotomy (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) {L : ℝ}
    (hbound : ∀ z : Space (m + 1), ∀ r : ℝ, 0 < r →
      (∫ x in closedBall z r, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤ L * r ^ m)
    {α K' b₀ s : ℝ} (hα : 0 < α) (hK' : 0 ≤ K') (hb₀ : b₀ ∈ Ioo (0 : ℝ) 1)
    (hs : s ∈ Ioo (0 : ℝ) 1) :
    ∃ ℓ ρ₀ : ℝ, 0 < ℓ ∧ 0 < ρ₀ ∧ ∀ (X e : Space (m + 1)), ‖e‖ = 1 →
      zeroExtension g u X ∈ Ioo 0 (1 - b₀) →
      (∀ ρ ∈ Ioc 0 ρ₀, ∫ z in ball X ρ, diffuseTiltDensity 1 (zeroExtension g u) e z <
        ℓ * ρ ^ m) →
      (∃ τ₁ τ₂ : ℝ, -(K' + layerTravelTime f (1 - b₀) + layerTravelTime f s + 3) ≤ τ₁ ∧
        τ₁ < τ₂ ∧ τ₂ ≤ layerTravelTime f (1 - b₀) ∧ s < zeroExtension g u (X + τ₁ • e) ∧
        zeroExtension g u (X + τ₂ • e) < s) ∨
      ((∃ τ ∈ Icc (-(layerTravelTime f (1 - b₀) + 1)) (layerTravelTime f s + 1),
          zeroExtension g u (X + τ • e) = s) ∧
        ∀ τ ∈ Icc (-(layerTravelTime f (1 - b₀) + 1)) (layerTravelTime f s + 1),
          zeroExtension g u (X + τ • e) = s → ∀ Z ∈ closedBall (0 : Space (m + 1)) K',
            |zeroExtension g u (X + Z) - layerProfile f (inner ℝ e Z - τ + layerTravelTime f s)|
              ≤ α) := by
  set M₀ := K' + layerTravelTime f (1 - b₀) + 1 with hM₀
  have hTb : 0 ≤ layerTravelTime f (1 - b₀) :=
    hr.layerTravelTime_nonneg h ⟨by linarith [hb₀.2], by linarith [hb₀.1]⟩
  obtain ⟨ℓ₁, ρ₁, hℓ₁, hρ₁, h1⟩ := hr.exists_microscopic_crossing h hbound (M₀ := M₀) hb₀ hs
    (by linarith)
  obtain ⟨ℓ₂, ρ₂, hℓ₂, hρ₂, h2⟩ := hr.exists_microscopic_approximation h hbound (M₀ := M₀) hα
    hK' hb₀ hs le_rfl
  refine ⟨min ℓ₁ ℓ₂, max ρ₁ ρ₂, lt_min hℓ₁ hℓ₂, lt_max_of_lt_left hρ₁, ?_⟩
  intro X e he hX htilt
  have ht₁ : ∀ ρ ∈ Ioc 0 ρ₁, ∫ z in ball X ρ, diffuseTiltDensity 1 (zeroExtension g u) e z <
      ℓ₁ * ρ ^ m := fun ρ hρ ↦ (htilt ρ ⟨hρ.1, hρ.2.trans (le_max_left _ _)⟩).trans_le
    (mul_le_mul_of_nonneg_right (min_le_left _ _) (pow_nonneg hρ.1.le m))
  have ht₂ : ∀ ρ ∈ Ioc 0 ρ₂, ∫ z in ball X ρ, diffuseTiltDensity 1 (zeroExtension g u) e z <
      ℓ₂ * ρ ^ m := fun ρ hρ ↦ (htilt ρ ⟨hρ.1, hρ.2.trans (le_max_right _ _)⟩).trans_le
    (mul_le_mul_of_nonneg_right (min_le_right _ _) (pow_nonneg hρ.1.le m))
  have hwin : -(M₀ + layerTravelTime f s + 2) =
      -(K' + layerTravelTime f (1 - b₀) + layerTravelTime f s + 3) := by rw [hM₀]; ring
  rcases h1 X e he hX ht₁ with hd | hc
  · left
    rwa [hwin] at hd
  · rcases h2 X e he hX ht₂ with hd | ha
    · left
      rwa [hwin] at hd
    · exact Or.inr ⟨hc, ha⟩

/-! ### HA10.b: orientation, the microscopic window, and the rescaled statement -/

private theorem norm_point_sub_point (y : Space m) (t t' : ℝ) :
    ‖point y t - point y t'‖ = |t - t'| := by
  have h := point_add_vertical y t' (t - t')
  rw [show t' + (t - t') = t by ring] at h
  rw [← h, add_sub_cancel_left, norm_smul, norm_verticalDirection, mul_one, Real.norm_eq_abs]

private theorem abs_last_sub_le_norm (z w : Space (m + 1)) :
    |z (Fin.last m) - w (Fin.last m)| ≤ ‖z - w‖ := by
  have h := abs_real_inner_le_norm (EuclideanSpace.single (Fin.last m) (1 : ℝ)) (z - w)
  simpa [EuclideanSpace.inner_single_left] using h

/-- **No downward crossing on lines over `D`.** If the cone condition holds at the level `s` and
the line over `y ∈ D` vanishes below the slab, then `v` cannot cross `s` downward inside the slab:
a downward crossing would produce two crossings of `s` on the same line. -/
theorem no_downward_crossing_of_cone {v : Space (m + 1) → ℝ} (hv : Continuous v)
    {D : Set (Space m)} {τs η s : ℝ} {Lc : ℝ≥0} (hcone : HasLevelCone v D τs s s Lc)
    (hη : 0 < η) (hητ : η < τs) (hs0 : 0 < s)
    (hlow : ∀ y ∈ D, ∀ t ∈ Ioo (-τs) τs, t ≤ -η → v (point y t) = 0)
    {y : Space m} (hy : y ∈ D) {t₁ t₂ : ℝ} (ht₁ : t₁ ∈ Ioo (-τs) τs) (ht₂ : t₂ ∈ Ioo (-τs) τs)
    (h12 : t₁ < t₂) (hv1 : s < v (point y t₁)) (hv2 : v (point y t₂) < s) : False := by
  have hc : Continuous (fun σ ↦ v (point y σ)) := hv.comp (continuous_point y)
  have ht₁η : -η < t₁ := by
    by_contra hn
    have := hlow y hy t₁ ht₁ (not_lt.mp hn)
    linarith
  have hηmem : -η ∈ Ioo (-τs) τs := ⟨by linarith, by linarith⟩
  have hv0 : v (point y (-η)) = 0 := hlow y hy (-η) hηmem le_rfl
  obtain ⟨c₁, hc₁, hvc₁⟩ := intermediate_value_Icc ht₁η.le hc.continuousOn
    (show s ∈ Icc (v (point y (-η))) (v (point y t₁)) from ⟨by rw [hv0]; exact hs0.le, hv1.le⟩)
  obtain ⟨c₂, hc₂, hvc₂⟩ := intermediate_value_Icc' h12.le hc.continuousOn
    (show s ∈ Icc (v (point y t₂)) (v (point y t₁)) from ⟨hv2.le, hv1.le⟩)
  have hc₁t : c₁ < t₁ := lt_of_le_of_ne hc₁.2 (fun heq ↦ by rw [heq] at hvc₁; linarith)
  have hc₂t : t₁ < c₂ := lt_of_le_of_ne hc₂.1 (fun heq ↦ by rw [← heq] at hvc₂; linarith)
  have hc₁m : c₁ ∈ Ioo (-τs) τs := ⟨by linarith [hc₁.1], by linarith [ht₁.2]⟩
  have hc₂m : c₂ ∈ Ioo (-τs) τs := ⟨by linarith [ht₁.1], by linarith [hc₂.2, ht₂.2]⟩
  have hh := hcone s ⟨le_rfl, le_rfl⟩ y hy y hy c₁ hc₁m c₂ hc₂m hvc₁ hvc₂
  rw [dist_self, mul_zero] at hh
  have := abs_nonpos_iff.mp hh
  linarith

/-- The physical tilt bound at a good point of a rotated rescaling. -/
theorem physical_tilt_lt_of_isLayerGoodPoint_rotated {U : Space (m + 1) → ℝ}
    {c : Space (m + 1)} {R : ℝ} (hR : 0 < R) (Q : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1))
    {ℓ r₀ b : ℝ} {A : Space (m + 1)}
    (hgood : IsLayerGoodPoint R (fun y ↦ U (c + R • Q y)) (verticalDirection m) ℓ r₀ b A)
    {ρ : ℝ} (hρ : 0 < ρ) (hρR : ρ ≤ R * r₀) :
    ∫ z in ball (c + R • Q A) ρ, diffuseTiltDensity 1 U (Q (verticalDirection m)) z <
      ℓ * ρ ^ m := by
  have hr : ρ / R ∈ Ioc 0 r₀ := ⟨div_pos hρ hR, by rw [div_le_iff₀ hR]; linarith⟩
  have h1 := hgood.2 (ρ / R) hr
  have h2 := setIntegral_ball_diffuseTiltDensity_rescaled U c hR Q (verticalDirection m) A (ρ / R)
  rw [h2, mul_div_cancel₀ _ hR.ne'] at h1
  have hRm : 0 < R ^ m := pow_pos hR m
  rw [inv_mul_lt_iff₀ hRm, div_pow] at h1
  have he : R ^ m * (ℓ * (ρ ^ m / R ^ m)) = ℓ * ρ ^ m := by field_simp
  rwa [he] at h1

/-- A good point of height less than `1` at horizontal distance less than `ρ` lies over the
vertical good set; hence `D = verticalGoodSet R v ℓ r₀ b ρD` contains every line of `B_{ρD}`
carrying a good point of height less than `1`. -/
theorem horizontal_mem_verticalGoodSet {T : ℝ} {v : Space (m + 1) → ℝ} {ℓ r₀ b ρ : ℝ}
    {A : Space (m + 1)} (hA : IsLayerGoodPoint T v (verticalDirection m) ℓ r₀ b A)
    (h1 : |A (Fin.last m)| < 1) (hρ : ‖horizontal A‖ < ρ) :
    horizontal A ∈ verticalGoodSet T v ℓ r₀ b ρ :=
  ⟨⟨A, ⟨hA, h1⟩, rfl⟩, by rwa [mem_ball, dist_zero_right]⟩

/-- The cone condition on a range of levels restricts to each single level of the range. -/
theorem HasLevelCone.of_mem_Icc {v : Space (m + 1) → ℝ} {D : Set (Space m)} {τ s₁ s₂ : ℝ}
    {L : ℝ≥0} (hc : HasLevelCone v D τ s₁ s₂ L) {s : ℝ} (hs : s ∈ Icc s₁ s₂) :
    HasLevelCone v D τ s s L := by
  intro s' hs'
  obtain rfl : s' = s := le_antisymm hs'.2 hs'.1
  exact hc s' hs

/-- **HA10.a + HA10.b for the rescaled translates.** There is `α₁ > 0` such that for every
`K, α > 0`, `b₀ ∈ (0, 1)`, level `s ∈ (0, α₁)` with `s < 1 - b₀` and cone constant `Lc` there are
`ℓ, ρ₀, C_w, ℓ' > 0`, independent of the center `x`, the scale `R` and the rotation `Q`, with the
following property. Let `v = U(x + R • Q ·)`; let `D` be a horizontal set on which the cone
condition holds at the level `s` in the slab `|t| < τs` and which contains every line in the
horizontal ball `B_{ρD}` carrying a good point (threshold `ℓ`, radii up to `r₀`) in the slab, e.g.
`D = verticalGoodSet R v ℓ r₀ b₀ ρD` if `τs ≤ 1` (`horizontal_mem_verticalGoodSet`); let `v`
vanish below `-η` and exceed `1 - β` above `η` on lines over `D`. Then every low positive point `p`
(`0 < v p < b ≤ s`) over `D` in the slab, at horizontal distance at least `C_w / R` from the
boundary of `B_{ρD}`, is either a bad point at the threshold `ℓ'` (radii up to `2 r₀`), or `v` is
`α`-close on `B_{Kα/R}(p)` to the layer profile translated to the height `H(y) = h_s(y) - T(s)/R`,
where `h_s = slabLevelHeight v τs s` is the `s`-level height. A point that is not bad is its own
anchor for the microscopic dichotomy. -/
theorem RigidityHypotheses.exists_low_profile_approximation (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) {L : ℝ}
    (hbound : ∀ z : Space (m + 1), ∀ r : ℝ, 0 < r →
      (∫ x in closedBall z r, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤ L * r ^ m) :
    ∃ α₁ : ℝ, 0 < α₁ ∧ ∀ (K α : ℝ), 0 < K → 0 < α → ∀ b₀ ∈ Ioo (0 : ℝ) 1,
      ∀ s ∈ Ioo (0 : ℝ) α₁, s < 1 - b₀ → ∀ Lc : ℝ≥0,
      ∃ ℓ ρ₀ Cw ℓ' : ℝ, 0 < ℓ ∧ 0 < ρ₀ ∧ 0 < Cw ∧ 0 < ℓ' ∧
      ∀ (x : Space (m + 1)) (R : ℝ), 0 < R → ∀ Q : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1),
      ∀ (D : Set (Space m)) (r₀ τs η β ρD b : ℝ),
        ρ₀ ≤ R * r₀ → Cw ≤ R * r₀ → 0 < η → η + Cw / R < τs → β ≤ b₀ → s < 1 - β → b ≤ s →
        HasLevelCone (fun z ↦ zeroExtension g u (x + R • Q z)) D τs s s Lc →
        (∀ A, IsLayerGoodPoint R (fun z ↦ zeroExtension g u (x + R • Q z))
          (verticalDirection m) ℓ r₀ b₀ A → |A (Fin.last m)| < τs → ‖horizontal A‖ < ρD →
            horizontal A ∈ D) →
        (∀ y ∈ D, ∀ t ∈ Ioo (-τs) τs, t ≤ -η →
          zeroExtension g u (x + R • Q (point y t)) = 0) →
        (∀ y ∈ D, ∀ t ∈ Ioo (-τs) τs, η ≤ t →
          1 - β < zeroExtension g u (x + R • Q (point y t))) →
        ∀ y ∈ D, ‖y‖ + Cw / R < ρD → ∀ t ∈ Ioo (-τs) τs,
          0 < zeroExtension g u (x + R • Q (point y t)) →
          zeroExtension g u (x + R • Q (point y t)) < b →
          (∃ r ∈ Ioc 0 (2 * r₀), ℓ' * r ^ m ≤ ∫ z in ball (point y t) r,
            diffuseTiltDensity R (fun z ↦ zeroExtension g u (x + R • Q z))
              (verticalDirection m) z) ∨
          ∀ z ∈ ball (point y t) (K * α / R),
            |zeroExtension g u (x + R • Q z) - layerProfile f (R * (z (Fin.last m) -
              (slabLevelHeight (fun z ↦ zeroExtension g u (x + R • Q z)) τs s y -
                layerTravelTime f s / R)))| ≤ α := by
  obtain ⟨a₀, α₁, ha₀, hα₁, hnd⟩ := hr.exists_microscopic_nondegeneracy h
  refine ⟨α₁, hα₁, ?_⟩
  intro K α hK hα b₀ hb₀ s hs hsb Lc
  have hs01 : s ∈ Ioo (0 : ℝ) 1 := ⟨hs.1, by linarith [hb₀.1]⟩
  set T1 := layerTravelTime f (1 - b₀) with hT1
  set Ts := layerTravelTime f s with hTs
  have hT1 : 0 ≤ T1 := hr.layerTravelTime_nonneg h ⟨by linarith [hb₀.2], by linarith [hb₀.1]⟩
  have hTs0 : 0 < Ts := hr.layerTravelTime_pos h hs01
  set Cn := s / a₀ with hCn
  have hCn0 : 0 < Cn := div_pos hs.1 ha₀
  set K' := K * α + (1 + (Lc : ℝ)) * Cn + T1 + Ts + 1 with hK'
  have hK'0 : 0 ≤ K' := by positivity
  obtain ⟨ℓ, ρ₀, hℓ, hρ₀, hdich⟩ := hr.exists_microscopic_profile_dichotomy h hbound
    (α := α) (K' := K') hα hK'0 hb₀ hs01
  set Wd := K' + T1 + Ts + 3 with hWd
  set Cw := Wd + Cn + 1 with hCw
  have hm1 : Module.finrank ℝ (Space (m + 1)) = m + 1 := finrank_euclideanSpace_fin
  set vol₁ := volume.real (ball (0 : Space (m + 1)) 1) with hvol₁
  have hvol₁pos : 0 < vol₁ := by
    rw [hvol₁, Measure.real]
    exact ENNReal.toReal_pos (measure_ball_pos volume 0 one_pos).ne'
      (measure_ball_lt_top (μ := volume)).ne
  have hκ := h.kappa_pos
  set cℓ := ℓ / (κ ^ 2 * vol₁) with hcℓ
  have hcℓ0 : 0 < cℓ := by positivity
  set ℓ' := ℓ * min ((1 / 2 : ℝ) ^ m) ((cℓ / (2 * Cn)) ^ m) with hℓ'
  have hℓ'0 : 0 < ℓ' := mul_pos hℓ (lt_min (by positivity) (by positivity))
  refine ⟨ℓ, ρ₀, Cw, ℓ', hℓ, hρ₀, by positivity, hℓ'0, ?_⟩
  intro x R hR Q D r₀ τs η β ρD b hρR hCwR hη hητ hβ hsβ hbs hcone hfull hlow hhigh
    y hy hyρ t ht hpos hlowb
  set v : Space (m + 1) → ℝ := fun z ↦ zeroExtension g u (x + R • Q z) with hvdef
  have hvc : Continuous v :=
    h.zeroExtension_continuous.comp (continuous_const.add (Q.continuous.const_smul R))
  have hCwR' : Cw / R ≤ r₀ := by rw [div_le_iff₀ hR]; linarith
  have hητ' : η < τs := by
    have : 0 < Cw / R := by positivity
    linarith
  have hlowb' : v (point y t) < b := hlowb
  -- the low point lies in the slab
  have htη : t ∈ Ioo (-η) η := by
    constructor
    · by_contra hn
      have := hlow y hy t ht (not_lt.mp hn)
      linarith
    · by_contra hn
      have := hhigh y hy t ht (not_lt.mp hn)
      linarith
  -- either `p` is bad at the threshold `ℓ'`, or it is a good anchor at the threshold `ℓ ≥ ℓ'`
  by_cases hbad : ∃ r ∈ Ioc 0 (2 * r₀), ℓ' * r ^ m ≤ ∫ z in ball (point y t) r,
      diffuseTiltDensity R v (verticalDirection m) z
  · exact Or.inl hbad
  push Not at hbad
  have hℓ'ℓ : ℓ' ≤ ℓ := by
    have h1 : min ((1 / 2 : ℝ) ^ m) ((cℓ / (2 * Cn)) ^ m) ≤ 1 :=
      (min_le_left _ _).trans (pow_le_one₀ (by norm_num) (by norm_num))
    calc ℓ' = ℓ * min ((1 / 2 : ℝ) ^ m) ((cℓ / (2 * Cn)) ^ m) := hℓ'
      _ ≤ ℓ * 1 := mul_le_mul_of_nonneg_left h1 hℓ.le
      _ = ℓ := mul_one ℓ
  have hpos' : 0 < v (point y t) := hpos
  obtain ⟨tA, htA, hA⟩ : ∃ tA, |tA| < τs ∧
      IsLayerGoodPoint R v (verticalDirection m) ℓ r₀ b₀ (point y tA) := by
    refine ⟨t, abs_lt.mpr ht, ⟨hpos', by linarith⟩, fun r hr ↦ ?_⟩
    exact (hbad r ⟨hr.1, by linarith [hr.1, hr.2]⟩).trans_le
      (mul_le_mul_of_nonneg_right hℓ'ℓ (pow_nonneg hr.1.le m))
  set A := point y tA with hAdef
  set e := Q (verticalDirection m) with hedef
  have he : ‖e‖ = 1 := by rw [hedef, LinearIsometryEquiv.norm_map]; exact norm_verticalDirection m
  set X := x + R • Q A with hXdef
  have hline : ∀ τ : ℝ, zeroExtension g u (X + τ • e) = v (point y (tA + τ / R)) := by
    intro τ
    simp only [hvdef, hXdef, hAdef, hedef]
    rw [← point_add_vertical, map_add, map_smul, smul_add, smul_smul, mul_div_cancel₀ _ hR.ne',
      add_assoc]
  have hpt : ∀ z : Space (m + 1), zeroExtension g u (X + R • Q (z - A)) = v z := by
    intro z
    simp only [hvdef, hXdef]
    rw [map_sub, smul_sub, add_add_sub_cancel]
  have hinner : ∀ z : Space (m + 1), inner ℝ e (R • Q (z - A)) = R * (z (Fin.last m) - tA) := by
    intro z
    rw [hedef, real_inner_smul_right, LinearIsometryEquiv.inner_map_map, real_inner_comm,
      inner_verticalDirection_right, hAdef]
    simp [last_point]
  have hUX : zeroExtension g u X ∈ Ioo 0 (1 - b₀) := hA.1
  have htilt : ∀ ρ ∈ Ioc 0 ρ₀, ∫ z in ball X ρ, diffuseTiltDensity 1 (zeroExtension g u) e z <
      ℓ * ρ ^ m := fun ρ hρ ↦
    physical_tilt_lt_of_isLayerGoodPoint_rotated hR Q hA hρ.1 (hρ.2.trans hρR)
  have htAη : tA ∈ Ioo (-η) η := by
    have hvA : v A ∈ Ioo 0 (1 - b₀) := hA.1
    have htA' : tA ∈ Ioo (-τs) τs := abs_lt.mp htA
    constructor
    · by_contra hn
      have := hlow y hy tA htA' (not_lt.mp hn)
      rw [← hAdef] at this
      linarith [hvA.1]
    · by_contra hn
      have := hhigh y hy tA htA' (not_lt.mp hn)
      rw [← hAdef] at this
      linarith [hvA.2]
  have hwin : ∀ τ : ℝ, |τ| ≤ Wd → tA + τ / R ∈ Ioo (-τs) τs := by
    intro τ hτ
    have h1 : |τ / R| ≤ Wd / R := by
      rw [abs_div, abs_of_pos hR]
      exact div_le_div_of_nonneg_right hτ hR.le
    have h2 : Wd / R ≤ Cw / R := div_le_div_of_nonneg_right (by linarith) hR.le
    rw [abs_le] at h1
    constructor <;> linarith [htAη.1, htAη.2]
  rcases hdich X e he hUX htilt with hdown | ⟨⟨τc, hτc, hτcs⟩, happrox⟩
  · -- a downward crossing contradicts the cone condition
    exfalso
    obtain ⟨τ₁, τ₂, h1, h2, h3, h4, h5⟩ := hdown
    have hτ₁ : |τ₁| ≤ Wd := abs_le.mpr ⟨by linarith, by linarith⟩
    have hτ₂ : |τ₂| ≤ Wd := abs_le.mpr ⟨by linarith, by linarith⟩
    rw [hline] at h4 h5
    exact no_downward_crossing_of_cone hvc hcone hη hητ' hs.1 hlow hy
      (hwin τ₁ hτ₁) (hwin τ₂ hτ₂) (by
        have : τ₁ / R < τ₂ / R := div_lt_div_of_pos_right h2 hR
        linarith) h4 h5
  · -- the crossing is the slab level height
    have hτcW : |τc| ≤ Wd := abs_le.mpr ⟨by linarith [hτc.1], by linarith [hτc.2]⟩
    have hcross : ∃ t' ∈ Ioo (-τs) τs, v (point y t') = s :=
      ⟨tA + τc / R, hwin τc hτcW, by rw [← hline]; exact hτcs⟩
    obtain ⟨hHmem, hHval⟩ := slabLevelHeight_spec hcross
    set ts := slabLevelHeight v τs s y with htsdef
    have htseq : ts = tA + τc / R := by
      have hh := hcone s ⟨le_rfl, le_rfl⟩ y hy y hy ts hHmem (tA + τc / R) (hwin τc hτcW)
        hHval (by rw [← hline]; exact hτcs)
      rw [dist_self, mul_zero] at hh
      have := abs_nonpos_iff.mp hh
      linarith
    have hτceq : τc = R * (ts - tA) := by rw [htseq]; field_simp; ring
    -- the CO3 point near `p`
    set p := point y t with hpdef
    obtain ⟨z₀, hz₀, hz₀s⟩ := hnd x R hR Q p s hs.1 hs.2.le hpos
    have hseg : ContinuousOn (fun lam : ℝ ↦ v (p + lam • (z₀ - p))) (Icc 0 1) :=
      (hvc.comp (continuous_const.add (continuous_id.smul continuous_const))).continuousOn
    obtain ⟨lam, hlam, hlams⟩ := intermediate_value_Icc zero_le_one hseg
      (show s ∈ Icc (v (p + (0 : ℝ) • (z₀ - p))) (v (p + (1 : ℝ) • (z₀ - p))) by
        rw [zero_smul, add_zero, one_smul, add_sub_cancel]
        exact ⟨(hlowb'.trans_le hbs).le, hz₀s.le⟩)
    set p' := p + lam • (z₀ - p) with hp'def
    have hpp' : ‖p' - p‖ < Cn / R := by
      have h1 : ‖p' - p‖ = lam * ‖z₀ - p‖ := by
        rw [hp'def, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hlam.1]
      have h2 : ‖z₀ - p‖ < s / (a₀ * R) := by rwa [mem_ball, dist_eq_norm] at hz₀
      have h3 : s / (a₀ * R) = Cn / R := by rw [hCn]; field_simp
      rw [h1, ← h3]
      calc lam * ‖z₀ - p‖ ≤ 1 * ‖z₀ - p‖ := mul_le_mul_of_nonneg_right hlam.2 (norm_nonneg _)
        _ < s / (a₀ * R) := by rw [one_mul]; exact h2
    set y' := horizontal p' with hy'def
    set t' := p' (Fin.last m) with ht'def
    have hp'pt : point y' t' = p' := point_horizontal_last p'
    have hvp' : v (point y' t') = s := by rw [hp'pt]; exact hlams
    have htt' : |t' - t| < Cn / R := by
      have := abs_last_sub_le_norm p' p
      rw [hpdef, last_point] at this
      exact this.trans_lt hpp'
    have hCnCw : Cn / R ≤ Cw / R := div_le_div_of_nonneg_right (by linarith) hR.le
    have ht'm : t' ∈ Ioo (-τs) τs := by
      rw [abs_lt] at htt'
      constructor <;> linarith [htη.1, htη.2]
    have hyy' : dist y' y < Cn / R := by
      have := lipschitzWith_one_horizontal.dist_le_mul p' p
      rw [NNReal.coe_one, one_mul, hpdef, horizontal_point, dist_eq_norm] at this
      rw [hy'def]
      exact this.trans_lt hpp'
    have hy'ρ : ‖y'‖ < ρD := by
      have := norm_le_norm_add_norm_sub' y' y
      rw [← dist_eq_norm] at this
      linarith
    by_cases hy'D : y' ∈ D
    · -- the window: `|t - ts| ≤ (1 + Lc) Cn / R`
      right
      have hh := hcone s ⟨le_rfl, le_rfl⟩ y' hy'D y hy t' ht'm ts hHmem hvp' hHval
      have hwin' : |t - ts| < (1 + (Lc : ℝ)) * Cn / R := by
        have h1 : |t' - ts| ≤ (Lc : ℝ) * (Cn / R) :=
          hh.trans (mul_le_mul_of_nonneg_left hyy'.le Lc.coe_nonneg)
        calc |t - ts| ≤ |t - t'| + |t' - ts| := abs_sub_le _ _ _
          _ < Cn / R + (Lc : ℝ) * (Cn / R) := by rw [abs_sub_comm]; linarith
          _ = (1 + (Lc : ℝ)) * Cn / R := by ring
      intro z hz
      have hZ : R • Q (z - A) ∈ closedBall (0 : Space (m + 1)) K' := by
        rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg hR.le,
          LinearIsometryEquiv.norm_map]
        have hzA : ‖z - A‖ ≤ ‖z - p‖ + |t - ts| + |ts - tA| := by
          have h1 : z - A = (z - p) + (point y t - point y ts) + (point y ts - A) := by
            rw [hpdef]; abel
          rw [h1]
          calc ‖(z - p) + (point y t - point y ts) + (point y ts - A)‖
              ≤ ‖z - p‖ + ‖point y t - point y ts‖ + ‖point y ts - A‖ := norm_add₃_le
            _ = _ := by rw [norm_point_sub_point, hAdef, norm_point_sub_point]
        have hzp : ‖z - p‖ < K * α / R := by rwa [mem_ball, dist_eq_norm] at hz
        have hts : |ts - tA| = |τc| / R := by
          rw [htseq, show tA + τc / R - tA = τc / R by ring, abs_div, abs_of_pos hR]
        have hτcb : |τc| ≤ T1 + Ts + 1 := abs_le.mpr ⟨by linarith [hτc.1], by linarith [hτc.2]⟩
        have hRzp : R * ‖z - p‖ < K * α := by
          have := (lt_div_iff₀ hR).mp hzp
          linarith [mul_comm R ‖z - p‖]
        have hRtts : R * |t - ts| < (1 + (Lc : ℝ)) * Cn := by
          have := (lt_div_iff₀ hR).mp hwin'
          linarith [mul_comm R |t - ts|]
        have hRtsA : R * |ts - tA| = |τc| := by
          rw [hts]
          field_simp
        have key : R * ‖z - A‖ ≤ K * α + (1 + (Lc : ℝ)) * Cn + (T1 + Ts + 1) := by
          have h1 : R * ‖z - A‖ ≤ R * ‖z - p‖ + R * |t - ts| + R * |ts - tA| := by
            have := mul_le_mul_of_nonneg_left hzA hR.le
            linarith
          linarith
        rw [hK']
        linarith
      have happ := happrox (R * (ts - tA)) (by rw [← hτceq]; exact hτc)
        (by rw [← hτceq]; exact hτcs) _ hZ
      rw [hpt, hinner] at happ
      have harg : R * (z (Fin.last m) - tA) - R * (ts - tA) + Ts =
          R * (z (Fin.last m) - (ts - Ts / R)) := by field_simp; ring
      rw [harg] at happ
      exact happ
    · -- the CO3 point is bad, and so is `p` at the degraded threshold
      left
      have hp'good : ¬IsLayerGoodPoint R v (verticalDirection m) ℓ r₀ b₀ p' := by
        intro hg
        apply hy'D
        have := hfull p' hg (by rw [← ht'def]; exact abs_lt.mpr ⟨ht'm.1, ht'm.2⟩)
          (by rw [← hy'def]; exact hy'ρ)
        rwa [← hy'def] at this
      have hval' : v p' ∈ Ioo 0 (1 - b₀) := by
        rw [show v p' = s from hlams]
        exact ⟨hs.1, hsb⟩
      have hbadr : ∃ r ∈ Ioc 0 r₀, ℓ * r ^ m ≤
          ∫ z in ball p' r, diffuseTiltDensity R v (verticalDirection m) z := by
        by_contra hn
        push Not at hn
        exact hp'good ⟨hval', hn⟩
      obtain ⟨r, hr0, hrbad⟩ := hbadr
      -- microscopic radii cannot be bad
      have hLipv : LipschitzWith ⟨κ * R, by positivity⟩ v := by
        apply LipschitzWith.of_dist_le_mul
        intro a c
        have := (hr.zeroExtension_lipschitzWith h).dist_le_mul (x + R • Q a) (x + R • Q c)
        rw [dist_add_left, dist_smul₀, Real.norm_of_nonneg hR.le, Q.dist_map] at this
        calc dist (v a) (v c) ≤ κ * (R * dist a c) := this
          _ = κ * R * dist a c := by ring
      have hRr : cℓ ≤ R * r := by
        have hint := integrableOn_diffuseTiltDensity hLipv.locallyLipschitz
          (isCompact_closedBall p' r) R (norm_verticalDirection m)
        have hle : ∫ z in ball p' r, diffuseTiltDensity R v (verticalDirection m) z ≤
            (κ * R) ^ 2 / R * volume.real (ball p' r) := by
          have hconst : IntegrableOn (fun _ : Space (m + 1) ↦ (κ * R) ^ 2 / R) (ball p' r) :=
            integrableOn_const (measure_ball_lt_top (μ := volume)).ne
          have := setIntegral_mono (hint.mono_set ball_subset_closedBall) hconst
            (fun z ↦ diffuseTiltDensity_le_of_lipschitzWith hR hLipv (verticalDirection m) z)
          rwa [setIntegral_const, smul_eq_mul, mul_comm] at this
        have hvolr : volume.real (ball p' r) = r ^ (m + 1) * vol₁ := by
          rw [Measure.real, Measure.addHaar_ball volume p' hr0.1.le, hm1, ENNReal.toReal_mul,
            ENNReal.toReal_ofReal (pow_nonneg hr0.1.le _), hvol₁, Measure.real]
        rw [hvolr] at hle
        have h1 : ℓ * r ^ m ≤ (κ * R) ^ 2 / R * (r ^ (m + 1) * vol₁) := hrbad.trans hle
        have h2 : (κ * R) ^ 2 / R * (r ^ (m + 1) * vol₁) = (κ ^ 2 * vol₁ * (R * r)) * r ^ m := by
          field_simp
          ring
        rw [h2] at h1
        have h3 : ℓ ≤ κ ^ 2 * vol₁ * (R * r) := le_of_mul_le_mul_right h1 (pow_pos hr0.1 m)
        rw [hcℓ, div_le_iff₀ (by positivity)]
        linarith
      rcases le_or_gt (Cn / R) r with hrbig | hrsmall
      · refine ⟨2 * r, ⟨by linarith [hr0.1], by linarith [hr0.2]⟩, ?_⟩
        have hsub : ball p' r ⊆ ball p (2 * r) := by
          intro z hz
          rw [mem_ball] at hz ⊢
          have := dist_triangle z p' p
          rw [dist_eq_norm p' p] at this
          linarith
        have hint := integrableOn_diffuseTiltDensity hLipv.locallyLipschitz
          (isCompact_closedBall p (2 * r)) R (norm_verticalDirection m)
        have hmono : ∫ z in ball p' r, diffuseTiltDensity R v (verticalDirection m) z ≤
            ∫ z in ball p (2 * r), diffuseTiltDensity R v (verticalDirection m) z :=
          setIntegral_mono_set (hint.mono_set ball_subset_closedBall)
            (Eventually.of_forall fun z ↦ diffuseTiltDensity_nonneg hR _
              (norm_verticalDirection m) z) (Eventually.of_forall hsub)
        have hmin2 : min ((1 / 2 : ℝ) ^ m) ((cℓ / (2 * Cn)) ^ m) * 2 ^ m ≤ 1 := by
          calc min ((1 / 2 : ℝ) ^ m) ((cℓ / (2 * Cn)) ^ m) * 2 ^ m
              ≤ (1 / 2 : ℝ) ^ m * 2 ^ m :=
                mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)
            _ = 1 := by rw [← mul_pow]; norm_num
        have hrm : 0 ≤ r ^ m := pow_nonneg hr0.1.le m
        have hℓ'le : ℓ' * (2 * r) ^ m ≤ ℓ * r ^ m := by
          calc ℓ' * (2 * r) ^ m
              = ℓ * (min ((1 / 2 : ℝ) ^ m) ((cℓ / (2 * Cn)) ^ m) * 2 ^ m) * r ^ m := by
                rw [hℓ', mul_pow]
                ring
            _ ≤ ℓ * 1 * r ^ m :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmin2 hℓ.le) hrm
            _ = ℓ * r ^ m := by ring
        linarith
      · refine ⟨2 * Cn / R, ⟨by positivity, by
          have : Cn / R ≤ r₀ := hCnCw.trans hCwR'
          rw [mul_div_assoc]; linarith⟩, ?_⟩
        have hsub : ball p' r ⊆ ball p (2 * Cn / R) := by
          intro z hz
          rw [mem_ball] at hz ⊢
          have := dist_triangle z p' p
          rw [dist_eq_norm p' p] at this
          have : 2 * Cn / R = Cn / R + Cn / R := by ring
          linarith
        have hint := integrableOn_diffuseTiltDensity hLipv.locallyLipschitz
          (isCompact_closedBall p (2 * Cn / R)) R (norm_verticalDirection m)
        have hmono : ∫ z in ball p' r, diffuseTiltDensity R v (verticalDirection m) z ≤
            ∫ z in ball p (2 * Cn / R), diffuseTiltDensity R v (verticalDirection m) z :=
          setIntegral_mono_set (hint.mono_set ball_subset_closedBall)
            (Eventually.of_forall fun z ↦ diffuseTiltDensity_nonneg hR _
              (norm_verticalDirection m) z) (Eventually.of_forall hsub)
        have hrlow : cℓ / R ≤ r := by rw [div_le_iff₀ hR]; linarith
        have hℓ'le : ℓ' * (2 * Cn / R) ^ m ≤ ℓ * r ^ m := by
          have h1 : ℓ' ≤ ℓ * (cℓ / (2 * Cn)) ^ m := by
            rw [hℓ']
            exact mul_le_mul_of_nonneg_left (min_le_right _ _) hℓ.le
          have h2 : (cℓ / (2 * Cn)) ^ m * (2 * Cn / R) ^ m = (cℓ / R) ^ m := by
            rw [← mul_pow]
            congr 1
            field_simp
          have h3 : (cℓ / R) ^ m ≤ r ^ m := pow_le_pow_left₀ (by positivity) hrlow m
          calc ℓ' * (2 * Cn / R) ^ m ≤ ℓ * (cℓ / (2 * Cn)) ^ m * (2 * Cn / R) ^ m :=
                mul_le_mul_of_nonneg_right h1 (by positivity)
            _ = ℓ * (cℓ / R) ^ m := by rw [mul_assoc, h2]
            _ ≤ ℓ * r ^ m := mul_le_mul_of_nonneg_left h3 hℓ.le
        linarith

/-! ### HA10.c on the good low points of the slab -/

/-- **HA10.c on a measurable set of approximated low points.** Variant of
`RigidityHypotheses.exists_low_level_bounds_of_profile_approximation` in which only the points of
a measurable set `S` of low positive points over `D` are assumed to be centers of approximation:
with `Λ = K α + (b + α) / c_q` and `ρ = |∇v|² / R`, `∫_S ρ ≤ M Λ |D|` and
`∫_S (t - a)² ρ ≤ 2 M Λ ∫_D ((H - a)² + (Λ / R)²)`. -/
theorem RigidityHypotheses.exists_low_level_bounds_of_approximation_on
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) :
    ∃ K α₀ M : ℝ, 0 < K ∧ 0 < α₀ ∧ 0 ≤ M ∧
      ∀ (x : Space (m + 1)) (R : ℝ), 0 < R → ∀ Q : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1),
        ∀ q : ℝ → ℝ, (∀ s ≤ 0, q s = 0) → ∀ cq s₁ : ℝ, 0 < cq →
          (∀ s, 0 ≤ s → cq * min s s₁ ≤ q s) →
          ∀ α b : ℝ, 0 < α → α ≤ α₀ → 0 < b → b + α < cq * s₁ →
          ∀ D : Set (Space m), MeasurableSet D → volume D ≠ ⊤ →
          ∀ (H : Space m → ℝ) (a : ℝ), IntegrableOn (fun y ↦ (H y - a) ^ 2) D →
          ∀ S : Set (Space (m + 1)), MeasurableSet S →
            (∀ p ∈ S, horizontal p ∈ D ∧ 0 < zeroExtension g u (x + R • Q p) ∧
              zeroExtension g u (x + R • Q p) < b ∧ ∀ z ∈ ball p (K * α / R),
                |zeroExtension g u (x + R • Q z) - q (R * (z (Fin.last m) - H (horizontal p)))|
                  ≤ α) →
            (∫ p in S, ‖gradient (fun z ↦ zeroExtension g u (x + R • Q z)) p‖ ^ 2 / R) ≤
              M * (K * α + (b + α) / cq) * volume.real D ∧
            (∫ p in S, (p (Fin.last m) - a) ^ 2 *
                (‖gradient (fun z ↦ zeroExtension g u (x + R • Q z)) p‖ ^ 2 / R)) ≤
              2 * M * (K * α + (b + α) / cq) *
                ∫ y in D, ((H y - a) ^ 2 + ((K * α + (b + α) / cq) / R) ^ 2) := by
  obtain ⟨K, α₀, hK, hα₀, hloc⟩ := hr.exists_low_band_localization h
  obtain ⟨M, hM0, hdens⟩ := hr.exists_rotated_rescaled_density_bound h
  refine ⟨K, α₀, M, hK, hα₀, hM0, ?_⟩
  intro x R hR Q q hq0 cq s₁ hcq hqlin α b hα hαle hb hbα D hD hDfin H a hHint S hS hSprop
  set B := (b + α) / cq with hBdef
  have hB : 0 < B := div_pos (by linarith) hcq
  have hKα : 0 < K * α := mul_pos hK hα
  set Λ := K * α + B with hΛdef
  have hΛ : 0 < Λ := by linarith
  set v : Space (m + 1) → ℝ := fun z ↦ zeroExtension g u (x + R • Q z) with hvdef
  have hρm : Measurable (fun p ↦ ‖gradient v p‖ ^ 2 / R) :=
    ((measurable_gradient v).norm.pow_const 2).div_const R
  have hρ0 : ∀ p, 0 ≤ ‖gradient v p‖ ^ 2 / R := fun p ↦ div_nonneg (sq_nonneg _) hR.le
  have hρM : ∀ p ∈ S, ‖gradient v p‖ ^ 2 / R ≤ M * R := fun p hp ↦
    hdens x R hR Q p (hSprop p hp).2.1
  have hSD : ∀ p ∈ S, horizontal p ∈ D := fun p hp ↦ (hSprop p hp).1
  -- band localization on the lines over `D`
  have hloc' : ∀ y ∈ D, ∀ t, point y t ∈ S →
      -(K * α) < R * (t - H y) ∧ R * (t - H y) < B := by
    intro y _ t ht
    obtain ⟨_, h1, h2, happ⟩ := hSprop _ ht
    rw [horizontal_point] at happ
    have hl := hloc x R hR Q q hq0 cq s₁ hcq hqlin (H y) α b hα hαle hbα (point y t) happ h1 h2
    simpa only [last_point] using hl
  set c : Space m → ℝ := fun y ↦ H y + (B - K * α) / (2 * R) with hcdef
  have hℓ : 0 ≤ Λ / (2 * R) := (div_pos hΛ (mul_pos two_pos hR)).le
  have hcen : ∀ y ∈ D, ∀ t, point y t ∈ S → |t - c y| ≤ Λ / (2 * R) := by
    intro y hy t ht
    obtain ⟨hl, hu⟩ := hloc' y hy t ht
    have e1 : t - c y = (R * (t - H y) - (B - K * α) / 2) / R := by
      simp only [hcdef]
      field_simp
      ring
    have e2 : Λ / (2 * R) = Λ / 2 / R := by
      field_simp
    rw [e1, e2, abs_le]
    constructor
    · rw [← neg_div]
      exact div_le_div_of_nonneg_right (by linarith) hR.le
    · exact div_le_div_of_nonneg_right (by linarith) hR.le
  have habs : ∀ y ∈ D, ∀ t, point y t ∈ S → |t - H y| ≤ Λ / R := by
    intro y hy t ht
    obtain ⟨hl, hu⟩ := hloc' y hy t ht
    have h1 : |R * (t - H y)| ≤ Λ := abs_le.mpr ⟨by linarith, by linarith⟩
    rw [abs_mul, abs_of_pos hR] at h1
    rw [le_div_iff₀ hR]
    linarith [mul_comm R |t - H y|]
  refine ⟨?_, ?_⟩
  · -- the low-level mass
    have hKi : IntegrableOn (fun _ : Space m ↦ M * R) D := integrableOn_const hDfin
    have hmain := setIntegral_le_of_vertical_band (c := c) (K := fun _ ↦ M * R) hS hρm hρ0 hD
      hSD hℓ (fun _ _ ↦ mul_nonneg hM0 hR.le) hKi
      (fun y hy t ht ↦ ⟨hcen y hy t ht, hρM _ ht⟩)
    rw [setIntegral_const, smul_eq_mul] at hmain
    calc _ ≤ 2 * (Λ / (2 * R)) * (volume.real D * (M * R)) := hmain
      _ = M * Λ * volume.real D := by field_simp
  · -- the low-level height moment
    have hFm : Measurable (fun p : Space (m + 1) ↦
        (p (Fin.last m) - a) ^ 2 * (‖gradient v p‖ ^ 2 / R)) :=
      ((((EuclideanSpace.proj (𝕜 := ℝ) (Fin.last m)).continuous.measurable).sub_const
        a).pow_const 2).mul hρm
    have hKi : IntegrableOn (fun y ↦ 2 * (M * R) * ((H y - a) ^ 2 + (Λ / R) ^ 2)) D :=
      (hHint.add (integrableOn_const hDfin)).const_mul (2 * (M * R))
    have hmain := setIntegral_le_of_vertical_band (c := c)
      (K := fun y ↦ 2 * (M * R) * ((H y - a) ^ 2 + (Λ / R) ^ 2)) hS hFm
      (fun p ↦ mul_nonneg (sq_nonneg _) (hρ0 p)) hD hSD hℓ
      (fun _ _ ↦ mul_nonneg (mul_nonneg two_pos.le (mul_nonneg hM0 hR.le)) (by positivity))
      hKi (by
        intro y hy t ht
        refine ⟨hcen y hy t ht, ?_⟩
        rw [last_point]
        have hb' := habs y hy t ht
        have hsq : (t - H y) ^ 2 ≤ (Λ / R) ^ 2 := by
          have := pow_le_pow_left₀ (abs_nonneg _) hb' 2
          rwa [sq_abs] at this
        have hta : (t - a) ^ 2 ≤ 2 * ((H y - a) ^ 2 + (Λ / R) ^ 2) := by
          nlinarith [sq_nonneg (t - H y - (H y - a))]
        calc (t - a) ^ 2 * (‖gradient v (point y t)‖ ^ 2 / R)
            ≤ 2 * ((H y - a) ^ 2 + (Λ / R) ^ 2) * (M * R) :=
              mul_le_mul hta (hρM _ ht) (hρ0 _) (by positivity)
          _ = 2 * (M * R) * ((H y - a) ^ 2 + (Λ / R) ^ 2) := by ring)
    rw [integral_const_mul] at hmain
    calc _ ≤ 2 * (Λ / (2 * R)) * (2 * (M * R) * ∫ y in D, ((H y - a) ^ 2 + (Λ / R) ^ 2)) :=
          hmain
      _ = 2 * M * Λ * ∫ y in D, ((H y - a) ^ 2 + (Λ / R) ^ 2) := by field_simp

/-- **HA10 assembled: low-level mass and height moments on the good slab.** There are
`K, α₀, c_q > 0` and `M ≥ 0`, independent of the center, the scale and the rotation, such that for
`0 < α ≤ α₀`, `b₀ ∈ (0, 1)`, a level `s ∈ (0, α₀)` with `s < 1 - b₀` and a cone constant `Lc`
there are `ℓ, ρ₀, C_w, ℓ' > 0` with the following property. In the setting of
`RigidityHypotheses.exists_low_profile_approximation` (with `0 < b ≤ s` and `D` measurable), let
`D'` be the set of `y ∈ D` with `‖y‖ + C_w / R < ρD`, and `S` the set of low positive points
(`0 < v < b`) over `D'` in the slab `|t| < τs` that are not bad at the threshold `ℓ'` (radii up to
`2 r₀`). With `Λ = K α + (b + α) / c_q`, `ρ = |∇v|² / R` and the heights
`H(y) = h_s(y) - T(s) / R` (`h_s = slabLevelHeight v τs s`):
`∫_S ρ ≤ M Λ |D'|` and `∫_S (t - a)² ρ ≤ 2 M Λ ∫_{D'} ((H - a)² + (Λ / R)²)`. -/
theorem RigidityHypotheses.exists_low_level_bounds_on_good_slab (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) {L : ℝ}
    (hbound : ∀ z : Space (m + 1), ∀ r : ℝ, 0 < r →
      (∫ x in closedBall z r, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤ L * r ^ m) :
    ∃ K α₀ cq M : ℝ, 0 < K ∧ 0 < α₀ ∧ 0 < cq ∧ 0 ≤ M ∧
      ∀ α : ℝ, 0 < α → α ≤ α₀ → ∀ b₀ ∈ Ioo (0 : ℝ) 1,
      ∀ s ∈ Ioo (0 : ℝ) α₀, s < 1 - b₀ → ∀ Lc : ℝ≥0,
      ∃ ℓ ρ₀ Cw ℓ' : ℝ, 0 < ℓ ∧ 0 < ρ₀ ∧ 0 < Cw ∧ 0 < ℓ' ∧
      ∀ (x : Space (m + 1)) (R : ℝ), 0 < R → ∀ Q : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1),
      ∀ (D : Set (Space m)) (r₀ τs η β ρD b a : ℝ), MeasurableSet D → 0 < b →
        ρ₀ ≤ R * r₀ → Cw ≤ R * r₀ → 0 < η → η + Cw / R < τs → β ≤ b₀ → s < 1 - β → b ≤ s →
        HasLevelCone (fun z ↦ zeroExtension g u (x + R • Q z)) D τs s s Lc →
        (∀ A, IsLayerGoodPoint R (fun z ↦ zeroExtension g u (x + R • Q z))
          (verticalDirection m) ℓ r₀ b₀ A → |A (Fin.last m)| < τs → ‖horizontal A‖ < ρD →
            horizontal A ∈ D) →
        (∀ y ∈ D, ∀ t ∈ Ioo (-τs) τs, t ≤ -η →
          zeroExtension g u (x + R • Q (point y t)) = 0) →
        (∀ y ∈ D, ∀ t ∈ Ioo (-τs) τs, η ≤ t →
          1 - β < zeroExtension g u (x + R • Q (point y t))) →
        (∫ p in {p | horizontal p ∈ D ∧ ‖horizontal p‖ + Cw / R < ρD ∧
            p (Fin.last m) ∈ Ioo (-τs) τs ∧ 0 < zeroExtension g u (x + R • Q p) ∧
            zeroExtension g u (x + R • Q p) < b ∧ ∀ r ∈ Ioc 0 (2 * r₀),
              ∫ z in ball p r, diffuseTiltDensity R (fun z ↦ zeroExtension g u (x + R • Q z))
                (verticalDirection m) z < ℓ' * r ^ m},
            ‖gradient (fun z ↦ zeroExtension g u (x + R • Q z)) p‖ ^ 2 / R) ≤
          M * (K * α + (b + α) / cq) * volume.real {y ∈ D | ‖y‖ + Cw / R < ρD} ∧
        (∫ p in {p | horizontal p ∈ D ∧ ‖horizontal p‖ + Cw / R < ρD ∧
            p (Fin.last m) ∈ Ioo (-τs) τs ∧ 0 < zeroExtension g u (x + R • Q p) ∧
            zeroExtension g u (x + R • Q p) < b ∧ ∀ r ∈ Ioc 0 (2 * r₀),
              ∫ z in ball p r, diffuseTiltDensity R (fun z ↦ zeroExtension g u (x + R • Q z))
                (verticalDirection m) z < ℓ' * r ^ m},
            (p (Fin.last m) - a) ^ 2 *
              (‖gradient (fun z ↦ zeroExtension g u (x + R • Q z)) p‖ ^ 2 / R)) ≤
          2 * M * (K * α + (b + α) / cq) * ∫ y in {y ∈ D | ‖y‖ + Cw / R < ρD},
            ((slabLevelHeight (fun z ↦ zeroExtension g u (x + R • Q z)) τs s y -
              layerTravelTime f s / R - a) ^ 2 + ((K * α + (b + α) / cq) / R) ^ 2) := by
  obtain ⟨K, α₀l, M, hK, hα₀l, hM0, hbands⟩ := hr.exists_low_level_bounds_of_approximation_on h
  obtain ⟨α₁, hα₁, happrox⟩ := hr.exists_low_profile_approximation h hbound
  obtain ⟨cq, s₁, hcq, hs₁, hqlin⟩ := hr.exists_layerProfile_linear_lower h
  set α₀ := min (min α₀l α₁) (cq * s₁ / 2) with hα₀def
  have hα₀ : 0 < α₀ := lt_min (lt_min hα₀l hα₁) (by positivity)
  refine ⟨K, α₀, cq, M, hK, hα₀, hcq, hM0, ?_⟩
  intro α hα hαle b₀ hb₀ s hs hsb Lc
  have hα₀1 : α₀ ≤ α₀l := (min_le_left _ _).trans (min_le_left _ _)
  have hα₀2 : α₀ ≤ α₁ := (min_le_left _ _).trans (min_le_right _ _)
  have hα₀3 : α₀ ≤ cq * s₁ / 2 := min_le_right _ _
  obtain ⟨ℓ, ρ₀, Cw, ℓ', hℓ, hρ₀, hCw, hℓ', happ⟩ :=
    happrox K α hK hα b₀ hb₀ s ⟨hs.1, hs.2.trans_le hα₀2⟩ hsb Lc
  refine ⟨ℓ, ρ₀, Cw, ℓ', hℓ, hρ₀, hCw, hℓ', ?_⟩
  intro x R hR Q D r₀ τs η β ρD b a hD hb hρR hCwR hη hητ hβ hsβ hbs hcone hfull hlow hhigh
  have hvc : Continuous (fun z ↦ zeroExtension g u (x + R • Q z)) :=
    h.zeroExtension_continuous.comp (continuous_const.add (Q.continuous.const_smul R))
  have hLipv : LipschitzWith ⟨κ * R, mul_nonneg h.kappa_pos.le hR.le⟩
      (fun z ↦ zeroExtension g u (x + R • Q z)) := by
    apply LipschitzWith.of_dist_le_mul
    intro a c
    have := (hr.zeroExtension_lipschitzWith h).dist_le_mul (x + R • Q a) (x + R • Q c)
    rw [dist_add_left, dist_smul₀, Real.norm_of_nonneg hR.le, Q.dist_map] at this
    calc _ ≤ κ * (R * dist a c) := this
      _ = κ * R * dist a c := by ring
  have hCwR0 : 0 < Cw / R := div_pos hCw hR
  have hbα : b + α < cq * s₁ := by linarith [hs.2]
  -- the horizontal set `D'`
  have hD' : MeasurableSet {y ∈ D | ‖y‖ + Cw / R < ρD} :=
    hD.inter (measurableSet_lt (continuous_norm.add continuous_const).measurable
      measurable_const)
  have hD'fin : volume {y ∈ D | ‖y‖ + Cw / R < ρD} ≠ ⊤ := by
    refine ((measure_mono (fun y hy ↦ ?_)).trans_lt
      (measure_ball_lt_top (x := (0 : Space m)) (r := ρD))).ne
    rw [mem_ball, dist_zero_right]
    linarith [hy.2]
  -- the `s`-level heights are bounded and Lipschitz on `D`
  have hcross : ∀ y ∈ D, ∃ t ∈ Ioo (-τs) τs, zeroExtension g u (x + R • Q (point y t)) = s := by
    intro y hy
    have hm : -η ∈ Ioo (-τs) τs := ⟨by linarith, by linarith⟩
    have hp : η ∈ Ioo (-τs) τs := ⟨by linarith, by linarith⟩
    have h0 := hlow y hy (-η) hm le_rfl
    have h1 := hhigh y hy η hp le_rfl
    obtain ⟨c, hc, hvc'⟩ := intermediate_value_Icc (show -η ≤ η by linarith)
      (hvc.comp (continuous_point y)).continuousOn
      (show s ∈ Icc (zeroExtension g u (x + R • Q (point y (-η))))
          (zeroExtension g u (x + R • Q (point y η))) from
        ⟨by rw [h0]; exact hs.1.le, by linarith⟩)
    exact ⟨c, ⟨by linarith [hc.1], by linarith [hc.2]⟩, hvc'⟩
  have hLipH : LipschitzOnWith Lc
      (slabLevelHeight (fun z ↦ zeroExtension g u (x + R • Q z)) τs s) D := by
    apply LipschitzOnWith.of_dist_le_mul
    intro y hy y' hy'
    obtain ⟨h1, h2⟩ := slabLevelHeight_spec
      (v := fun z ↦ zeroExtension g u (x + R • Q z)) (hcross y hy)
    obtain ⟨h1', h2'⟩ := slabLevelHeight_spec
      (v := fun z ↦ zeroExtension g u (x + R • Q z)) (hcross y' hy')
    rw [Real.dist_eq]
    exact hcone s ⟨le_rfl, le_rfl⟩ y hy y' hy' _ h1 _ h1' h2 h2'
  have hHint : IntegrableOn (fun y ↦ (slabLevelHeight (fun z ↦ zeroExtension g u (x + R • Q z))
      τs s y - layerTravelTime f s / R - a) ^ 2) {y ∈ D | ‖y‖ + Cw / R < ρD} := by
    have hcont : ContinuousOn (fun y ↦ (slabLevelHeight
        (fun z ↦ zeroExtension g u (x + R • Q z)) τs s y - layerTravelTime f s / R - a) ^ 2)
        {y ∈ D | ‖y‖ + Cw / R < ρD} :=
      (((hLipH.continuousOn.mono (fun y hy ↦ hy.1)).sub continuousOn_const).sub
        continuousOn_const).pow 2
    refine IntegrableOn.of_bound hD'fin.lt_top (hcont.aestronglyMeasurable hD')
      ((τs + |layerTravelTime f s / R| + |a|) ^ 2) (ae_restrict_of_forall_mem hD' ?_)
    intro y hy
    obtain ⟨h1, _⟩ := slabLevelHeight_spec
      (v := fun z ↦ zeroExtension g u (x + R • Q z)) (hcross y hy.1)
    have habs : |slabLevelHeight (fun z ↦ zeroExtension g u (x + R • Q z)) τs s y -
        layerTravelTime f s / R - a| ≤ τs + |layerTravelTime f s / R| + |a| := by
      rw [abs_le]
      constructor <;> linarith [h1.1, h1.2, neg_abs_le (layerTravelTime f s / R),
        le_abs_self (layerTravelTime f s / R), neg_abs_le a, le_abs_self a]
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) habs 2
  -- the good low points of the slab
  have hG : IsOpen {p : Space (m + 1) | ∀ r ∈ Ioc 0 (2 * r₀), ∫ z in ball p r,
      diffuseTiltDensity R (fun z ↦ zeroExtension g u (x + R • Q z)) (verticalDirection m) z <
        ℓ' * r ^ m} :=
    isOpen_setOf_forall_setIntegral_ball_lt (measurable_diffuseTiltDensity R _ _)
      (diffuseTiltDensity_nonneg hR _ (norm_verticalDirection m))
      (diffuseTiltDensity_le_of_lipschitzWith hR hLipv _) ℓ' (2 * r₀)
  have hS : MeasurableSet {p | horizontal p ∈ D ∧ ‖horizontal p‖ + Cw / R < ρD ∧
      p (Fin.last m) ∈ Ioo (-τs) τs ∧ 0 < zeroExtension g u (x + R • Q p) ∧
      zeroExtension g u (x + R • Q p) < b ∧ ∀ r ∈ Ioc 0 (2 * r₀),
        ∫ z in ball p r, diffuseTiltDensity R (fun z ↦ zeroExtension g u (x + R • Q z))
          (verticalDirection m) z < ℓ' * r ^ m} :=
    (continuous_horizontal.measurable hD).inter
      ((measurableSet_lt ((continuous_norm.comp continuous_horizontal).add
          continuous_const).measurable measurable_const).inter
        ((isOpen_Ioo.preimage (EuclideanSpace.proj (𝕜 := ℝ) (Fin.last m)).continuous
            |>.measurableSet).inter
          ((measurableSet_lt measurable_const hvc.measurable).inter
            ((measurableSet_lt hvc.measurable measurable_const).inter hG.measurableSet))))
  refine hbands x R hR Q (layerProfile f) (fun σ hσ ↦ layerProfile_of_nonpos f hσ) cq s₁ hcq
    hqlin α b hα (hαle.trans hα₀1) hb hbα _ hD' hD'fin _ a hHint _ hS ?_
  rintro p ⟨hpD, hpρ, hpt, hp0, hpb, hpgood⟩
  refine ⟨⟨hpD, hpρ⟩, hp0, hpb, ?_⟩
  have hpp : point (horizontal p) (p (Fin.last m)) = p := point_horizontal_last p
  have hres := happ x R hR Q D r₀ τs η β ρD b hρR hCwR hη hητ hβ hsβ hbs hcone hfull hlow hhigh
    (horizontal p) hpD hpρ (p (Fin.last m)) hpt (by rw [hpp]; exact hp0) (by rw [hpp]; exact hpb)
  rw [hpp] at hres
  rcases hres with ⟨r, hr, hrbad⟩ | happrox'
  · exact absurd (hpgood r hr) (not_lt.mpr hrbad)
  · exact happrox'

end SerrinEpigraph
