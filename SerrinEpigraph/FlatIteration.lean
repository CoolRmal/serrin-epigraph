module

public import SerrinEpigraph.FlatBand

/-!
# Iterating the tilt-excess decay (`GR13`, flatness at one point)

* `TiltDecayProp m b η₀`: the conclusion of `exists_tilt_decay` for the threshold `η₀`.
* `IsFlatConfig.exists_frames`: iterating the decay gives frames `R k` such that
  `{x | θ^k R_k x ∈ E}` is flat with excess at most `η / 2^k`, and
  `‖R_{k+1} e_n - R_k e_n‖ ≤ tiltConst m √(η/2^k)`.
* `IsFlatConfig.exists_normal` (**`GR13.1`**): there is a unit normal `n` with
  `‖n - e_n‖ ≤ tiltConst m √η / (1 - √(1/2))` such that every boundary point `x` with
  `‖x‖ ≤ θ^k/4` satisfies `|⟪x, n⟫| ≤ flatModulus m η k · θ^k`, where
  `flatModulus m η k → 0` as `k → ∞`.
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory InnerProductSpace Filter
open scoped Topology ENNReal NNReal

namespace SerrinEpigraph

theorem similarity_comp_zero {d : ℕ} (Q R : Space d ≃ₗᵢ[ℝ] Space d) (θ₁ θ₂ : ℝ) (x : Space d) :
    similarity R 0 θ₁ (similarity Q 0 θ₂ x) = similarity (Q.trans R) 0 (θ₁ * θ₂) x := by
  simp only [similarity, zero_add, LinearIsometryEquiv.trans_apply, map_smul, smul_smul]

theorem similarity_refl_zero_one {d : ℕ} (x : Space d) :
    similarity (LinearIsometryEquiv.refl ℝ (Space d)) 0 1 x = x := by
  simp [similarity]

/-- The conclusion of `exists_tilt_decay` for the threshold `η₀`. -/
def TiltDecayProp (m : ℕ) (b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))) (η₀ : ℝ) :
    Prop :=
  ∀ (E Ω : Set (Space (m + 1))) (μ : Measure (Space (m + 1)))
    (ν : Space (m + 1) → Space (m + 1)), IsFlatConfig b E Ω μ ν →
    (projectedExcessMeasure μ ν).real (ball 0 2) ≤ η₀ →
    ∃ Q : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1),
      ‖Q (verticalDirection m) - verticalDirection m‖ ≤
        tiltConst m * Real.sqrt ((projectedExcessMeasure μ ν).real (ball 0 2)) ∧
      ∃ μ' ν', IsFlatConfig b (similarity Q 0 (decayTheta m) ⁻¹' E)
          (similarity Q 0 (decayTheta m) ⁻¹' Ω) μ' ν' ∧
        (projectedExcessMeasure μ' ν').real (ball 0 2) ≤
          (projectedExcessMeasure μ ν).real (ball 0 2) / 2

theorem exists_tiltDecayProp (m : ℕ) (b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ TiltDecayProp m b η₀ :=
  exists_tilt_decay m b

/-- The flatness modulus of `GR13.1`. -/
def flatModulus (m : ℕ) (η : ℝ) (k : ℕ) : ℝ :=
  2 * flatBand m (η / 2 ^ k) +
    tiltConst m * Real.sqrt η * Real.sqrt (1 / 2) ^ k / (1 - Real.sqrt (1 / 2))

theorem sqrt_half_lt_one : Real.sqrt (1 / 2) < 1 := by
  rw [Real.sqrt_lt' one_pos]
  norm_num

theorem flatModulus_nonneg (m : ℕ) {η : ℝ} (hη : 0 ≤ η) (k : ℕ) : 0 ≤ flatModulus m η k := by
  unfold flatModulus
  have h1 := flatBand_nonneg m (show 0 ≤ η / 2 ^ k by positivity)
  have h2 := tiltConst_nonneg m
  have h3 : 0 < 1 - Real.sqrt (1 / 2) := by linarith [sqrt_half_lt_one]
  positivity

theorem flatModulus_anti (m : ℕ) {η : ℝ} (hη : 0 ≤ η) {k l : ℕ} (hkl : k ≤ l) :
    flatModulus m η l ≤ flatModulus m η k := by
  unfold flatModulus
  have h3 : 0 < 1 - Real.sqrt (1 / 2) := by linarith [sqrt_half_lt_one]
  have hb : flatBand m (η / 2 ^ l) ≤ flatBand m (η / 2 ^ k) :=
    flatBand_mono m (by positivity)
      (div_le_div_of_nonneg_left hη (by positivity) (pow_le_pow_right₀ (by norm_num) hkl))
  have hr : Real.sqrt (1 / 2) ^ l ≤ Real.sqrt (1 / 2) ^ k :=
    pow_le_pow_of_le_one (Real.sqrt_nonneg _) sqrt_half_lt_one.le hkl
  have h2 := tiltConst_nonneg m
  have h4 : 0 ≤ tiltConst m * Real.sqrt η := mul_nonneg h2 (Real.sqrt_nonneg _)
  gcongr

theorem tendsto_flatModulus (m : ℕ) (η : ℝ) : Tendsto (flatModulus m η) atTop (𝓝 0) := by
  have h1 : Tendsto (fun k : ℕ ↦ η / 2 ^ k) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).const_mul η
    rw [mul_zero] at this
    refine this.congr fun k ↦ ?_
    rw [one_div_pow, mul_one_div]
  have h2 : Tendsto (fun k : ℕ ↦ Real.sqrt (1 / 2) ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (Real.sqrt_nonneg _) sqrt_half_lt_one
  have h3 := ((tendsto_flatBand m).comp h1).const_mul 2
  have h4 := (h2.const_mul (tiltConst m * Real.sqrt η)).div_const (1 - Real.sqrt (1 / 2))
  have := h3.add h4
  simp only [mul_zero, zero_div, add_zero] at this
  refine this.congr fun k ↦ ?_
  simp only [flatModulus, Function.comp_apply]

namespace IsFlatConfig

variable {m : ℕ} {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))}
  {E Ω : Set (Space (m + 1))} {μ : Measure (Space (m + 1))} {ν : Space (m + 1) → Space (m + 1)}

/-- **Iterating the tilt-excess decay.** -/
theorem exists_frames {η₀ : ℝ} (hdec : TiltDecayProp m b η₀) (hF : IsFlatConfig b E Ω μ ν)
    {η : ℝ} (he : (projectedExcessMeasure μ ν).real (ball 0 2) ≤ η) (hη : η ≤ η₀) :
    ∃ R : ℕ → (Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1)),
      R 0 = LinearIsometryEquiv.refl ℝ (Space (m + 1)) ∧
      (∀ k, ∃ μ' ν', IsFlatConfig b (similarity (R k) 0 (decayTheta m ^ k) ⁻¹' E)
          (similarity (R k) 0 (decayTheta m ^ k) ⁻¹' Ω) μ' ν' ∧
        (projectedExcessMeasure μ' ν').real (ball 0 2) ≤ η / 2 ^ k) ∧
      ∀ k, ‖R (k + 1) (verticalDirection m) - R k (verticalDirection m)‖ ≤
        tiltConst m * Real.sqrt (η / 2 ^ k) := by
  set θ := decayTheta m with hθ_def
  have hη0 : 0 ≤ η := measureReal_nonneg.trans he
  set P : ℕ → (Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1)) → Prop := fun k R ↦
    ∃ μ' ν', IsFlatConfig b (similarity R 0 (θ ^ k) ⁻¹' E) (similarity R 0 (θ ^ k) ⁻¹' Ω) μ' ν' ∧
      (projectedExcessMeasure μ' ν').real (ball 0 2) ≤ η / 2 ^ k with hP_def
  have hset : ∀ (Q R : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1)) (k : ℕ) (A : Set (Space (m + 1))),
      similarity Q 0 θ ⁻¹' (similarity R 0 (θ ^ k) ⁻¹' A) =
        similarity (Q.trans R) 0 (θ ^ (k + 1)) ⁻¹' A := by
    intro Q R k A
    ext x
    simp only [mem_preimage, similarity_comp_zero, pow_succ]
  have step : ∀ k R, P k R → ∃ Q : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1),
      ‖Q (verticalDirection m) - verticalDirection m‖ ≤ tiltConst m * Real.sqrt (η / 2 ^ k) ∧
        P (k + 1) (Q.trans R) := by
    rintro k R ⟨μ', ν', hF', he'⟩
    have hη2 : η / 2 ^ k ≤ η₀ := (div_le_self hη0 (one_le_pow₀ (by norm_num))).trans hη
    obtain ⟨Q, hQ, μ'', ν'', hF'', he''⟩ := hdec _ _ μ' ν' hF' (he'.trans hη2)
    refine ⟨Q, hQ.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt he') (tiltConst_nonneg m)),
      μ'', ν'', ?_, ?_⟩
    · rw [← hset, ← hset]
      exact hF''
    · calc (projectedExcessMeasure μ'' ν'').real (ball 0 2)
          ≤ (projectedExcessMeasure μ' ν').real (ball 0 2) / 2 := he''
        _ ≤ (η / 2 ^ k) / 2 := by linarith
        _ = η / 2 ^ (k + 1) := by rw [pow_succ]; ring
  choose! Qf hQf using step
  let R : ℕ → (Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1)) := fun k ↦
    Nat.rec (LinearIsometryEquiv.refl ℝ (Space (m + 1))) (fun k Rk ↦ (Qf k Rk).trans Rk) k
  have hR0 : R 0 = LinearIsometryEquiv.refl ℝ (Space (m + 1)) := rfl
  have hRs : ∀ k, R (k + 1) = (Qf k (R k)).trans (R k) := fun k ↦ rfl
  have hPR : ∀ k, P k (R k) := by
    intro k
    induction k with
    | zero =>
      have hset0 : ∀ A : Set (Space (m + 1)),
          similarity (R 0) 0 (θ ^ 0) ⁻¹' A = A := by
        intro A
        ext x
        simp only [mem_preimage, hR0, pow_zero, similarity_refl_zero_one]
      refine ⟨μ, ν, ?_, by simpa using he⟩
      rw [hset0, hset0]
      exact hF
    | succ k ih =>
      rw [hRs]
      exact (hQf k (R k) ih).2
  refine ⟨R, hR0, hPR, fun k ↦ ?_⟩
  rw [hRs, LinearIsometryEquiv.trans_apply, ← map_sub, LinearIsometryEquiv.norm_map]
  exact (hQf k (R k) (hPR k)).1

/-- **`GR13.1`: flatness at the centre.** -/
theorem exists_normal {η₀ : ℝ} (hdec : TiltDecayProp m b η₀) (hF : IsFlatConfig b E Ω μ ν)
    {η : ℝ} (he : (projectedExcessMeasure μ ν).real (ball 0 2) ≤ η) (hη : η ≤ η₀)
    (hη1 : η ≤ 1)
    (hsmall : bandOscConst m * Real.sqrt η + 2 * 1 * η <
      minimizerVolumeDensityConst m * (1 / 4) ^ (m + 1)) :
    ∃ n : Space (m + 1), ‖n‖ = 1 ∧
      ‖n - verticalDirection m‖ ≤ tiltConst m * Real.sqrt η / (1 - Real.sqrt (1 / 2)) ∧
      ∀ k : ℕ, ∀ x ∈ measureTheoreticBoundary E, ‖x‖ ≤ decayTheta m ^ k / 4 →
        |inner ℝ x n| ≤ flatModulus m η k * decayTheta m ^ k := by
  set θ := decayTheta m with hθ_def
  have hθ0 : 0 < θ := decayTheta_pos m
  have hθ1 : θ ≤ 1 / 10 := decayTheta_le m
  have hη0 : 0 ≤ η := measureReal_nonneg.trans he
  obtain ⟨R, hR0, hRF, hRn⟩ := hF.exists_frames hdec he hη
  set r := Real.sqrt (1 / 2) with hr_def
  have hr1 : r < 1 := sqrt_half_lt_one
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  set C := tiltConst m * Real.sqrt η with hC_def
  set u : ℕ → Space (m + 1) := fun k ↦ R k (verticalDirection m) with hu_def
  have hsq : ∀ k : ℕ, Real.sqrt (η / 2 ^ k) = Real.sqrt η * r ^ k := by
    intro k
    have h1 : η / 2 ^ k = η * (r ^ k) ^ 2 := by
      rw [← pow_mul, mul_comm k 2, pow_mul, hr_def, Real.sq_sqrt (by norm_num), one_div_pow,
        div_eq_mul_one_div]
    rw [h1, Real.sqrt_mul hη0, Real.sqrt_sq (by positivity)]
  have hu : ∀ k, dist (u k) (u (k + 1)) ≤ C * r ^ k := by
    intro k
    rw [dist_comm, dist_eq_norm, hC_def, mul_assoc, ← hsq]
    exact hRn k
  obtain ⟨n, hn⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric r C hr1 hu)
  have hdist : ∀ k, dist (u k) n ≤ C * r ^ k / (1 - r) :=
    dist_le_of_le_geometric_of_tendsto r C hr1 hu hn
  have hunorm : ∀ k, ‖u k‖ = 1 := fun k ↦ by
    simp only [hu_def, LinearIsometryEquiv.norm_map, norm_verticalDirection]
  have hnorm : ‖n‖ = 1 := by
    have h1 : Tendsto (fun k ↦ ‖u k‖) atTop (𝓝 ‖n‖) := hn.norm
    simp only [hunorm] at h1
    exact (tendsto_nhds_unique tendsto_const_nhds h1).symm
  refine ⟨n, hnorm, ?_, ?_⟩
  · have h0 : dist (verticalDirection m) n ≤ C / (1 - r) := by
      have := hdist 0
      simpa [hu_def, hR0] using this
    rw [dist_eq_norm, norm_sub_rev] at h0
    exact h0
  intro k x hx hxk
  obtain ⟨μ', ν', hFk, hek⟩ := hRF k
  set S := similarity (R k) 0 (θ ^ k) with hS_def
  have hθk : 0 < θ ^ k := pow_pos hθ0 k
  have hek0 : 0 ≤ (projectedExcessMeasure μ' ν').real (ball 0 2) := measureReal_nonneg
  have hekη : (projectedExcessMeasure μ' ν').real (ball 0 2) ≤ η :=
    hek.trans (div_le_self hη0 (one_le_pow₀ (by norm_num)))
  have hsmallk : bandOscConst m * Real.sqrt ((projectedExcessMeasure μ' ν').real (ball 0 2)) +
      2 * 1 * (projectedExcessMeasure μ' ν').real (ball 0 2) <
        minimizerVolumeDensityConst m * (1 / 4) ^ (m + 1) := by
    have h1 := Real.sqrt_le_sqrt hekη
    have h2 := bandOscConst_nonneg m
    nlinarith
  have hgr10 := hFk.min.gr10_band_width hFk.slab subset_rfl hFk.cyl (hekη.trans hη1)
    (r₀ := 1 / 4) (by norm_num) le_rfl (by norm_num) hsmallk
  set ak := ⨍ z in ball (0 : Space m) 1, columnSignedHeight (S ⁻¹' E) (1 / 2) z with hak
  have hband := hgr10.2
  have hfb : ((bandOscConst m * Real.sqrt ((projectedExcessMeasure μ' ν').real (ball 0 2)) +
      2 * 1 * (projectedExcessMeasure μ' ν').real (ball 0 2)) /
        minimizerVolumeDensityConst m) ^ ((1 : ℝ) / (m + 1)) ≤ flatBand m (η / 2 ^ k) :=
    flatBand_mono m hek0 hek
  have hak0 : |ak| ≤ flatBand m (η / 2 ^ k) := by
    have h := hband 0 hFk.zero_mem
      (by rw [horizontal_zero]; exact mem_ball_self (by norm_num)) (by simp)
    simp only [PiLp.zero_apply, zero_sub, abs_neg] at h
    exact h.trans hfb
  -- the preimage of `x`
  set y := θ⁻¹ ^ k • (R k).symm x with hy_def
  have hSy : S y = x := by
    rw [hS_def, similarity, zero_add, hy_def, map_smul, LinearIsometryEquiv.apply_symm_apply,
      smul_smul, ← mul_pow, mul_inv_cancel₀ hθ0.ne', one_pow, one_smul]
  have hyb : y ∈ measureTheoreticBoundary (S ⁻¹' E) := by
    rw [measureTheoreticBoundary_preimage_similarity E (R k) 0 hθk]
    show S y ∈ measureTheoreticBoundary E
    rw [hSy]
    exact hx
  have hynorm : ‖y‖ ≤ 1 / 4 := by
    rw [hy_def, norm_smul, LinearIsometryEquiv.norm_map, Real.norm_eq_abs,
      abs_of_pos (pow_pos (inv_pos.mpr hθ0) k), inv_pow]
    rw [inv_mul_le_iff₀ hθk]
    linarith
  have hyπ : horizontal y ∈ ball (0 : Space m) (1 / 2) :=
    mem_ball_zero_iff.mpr ((norm_horizontal_le_norm_of_space y).trans_lt (by linarith))
  have hyn : |y (Fin.last m)| < 1 := (abs_apply_last_le_norm y).trans_lt (by linarith)
  have hyband := (hband y hyb hyπ hyn).trans hfb
  have hylast : |y (Fin.last m)| ≤ 2 * flatBand m (η / 2 ^ k) := by
    have := abs_sub_abs_le_abs_sub (y (Fin.last m)) ak
    linarith
  -- the inner product with the approximate normal
  have hxuk : inner ℝ x (u k) = θ ^ k * y (Fin.last m) := by
    rw [← hSy, hS_def, similarity, zero_add, real_inner_smul_left, hu_def,
      LinearIsometryEquiv.inner_map_map, inner_verticalDirection_right]
  have hx_un : |inner ℝ x (n - u k)| ≤ θ ^ k / 4 * (C * r ^ k / (1 - r)) := by
    refine (abs_real_inner_le_norm _ _).trans ?_
    have := hdist k
    rw [dist_eq_norm, norm_sub_rev] at this
    exact mul_le_mul hxk this (norm_nonneg _) (by positivity)
  have hsplit : inner ℝ x n = inner ℝ x (u k) + inner ℝ x (n - u k) := by
    rw [inner_sub_right]
    ring
  rw [hsplit]
  have hC0 : 0 ≤ C := mul_nonneg (tiltConst_nonneg m) (Real.sqrt_nonneg _)
  have h1r : 0 < 1 - r := by linarith
  calc |inner ℝ x (u k) + inner ℝ x (n - u k)|
      ≤ |inner ℝ x (u k)| + |inner ℝ x (n - u k)| := abs_add_le _ _
    _ ≤ θ ^ k * (2 * flatBand m (η / 2 ^ k)) + θ ^ k / 4 * (C * r ^ k / (1 - r)) := by
        rw [hxuk, abs_mul, abs_of_pos hθk]
        exact add_le_add (mul_le_mul_of_nonneg_left hylast hθk.le) hx_un
    _ ≤ flatModulus m η k * θ ^ k := by
        unfold flatModulus
        rw [← hC_def, ← hr_def]
        have h2 : 0 ≤ C * r ^ k / (1 - r) := by positivity
        nlinarith

end IsFlatConfig

end SerrinEpigraph
