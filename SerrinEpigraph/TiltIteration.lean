module

public import SerrinEpigraph.DiffuseTiltEstimate
public import SerrinEpigraph.DiffuseTiltTranslatedConvergence

/-!
# Backward tilt iteration, optimal ball directions, and limiting line projections

This module formalizes sections I1–I7 of `docs/rigidity-proof/iteration-and-directions.md`:
1. Backward scale iterations with stopping thresholds (`stopped_tilt_iteration_I2` and
   `stopped_tilt_iteration`).
2. Ball tilt integrals, scale-normalized optimal ball tilt, and attainment on the unit sphere
   (`ballTiltIntegral`, `optimalBallTilt`, `exists_optimalBallTilt_direction`).
3. Rank-one line projections, operator-norm direction comparison without choosing normal signs,
   single-center scale convergence, and coincidence of limiting line projections across centers
   (`lineProjection`, `exists_limiting_lineProjection`,
   `limiting_lineProjection_eq_of_two_centers`).
-/

public section

noncomputable section

open Set Metric MeasureTheory Filter InnerProductSpace
open scoped Topology

namespace SerrinEpigraph

/-! ## I2–I2b. Numerical backward scale iterations -/

/-- Backward scale iteration with a stopping threshold (I2.1–I2.4): if `M` is bounded on
`[R₀, ∞)`, satisfies the coarse scaling inequality across factor `θ ∈ (0, 1)`, and improves by
`θ / 2` whenever `M R ≥ K ^ 2 / R ^ 2`, then
`M r ≤ max 1 (θ ^ ((2 : ℤ) - d)) * K ^ 2 / r ^ 2` for every `r ≥ R₀`. -/
theorem stopped_tilt_iteration_I2 {d : ℕ} {θ K δ₀ R₀ : ℝ} {M : ℝ → ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hK : 0 ≤ K) (hδ : 0 ≤ δ₀) (hR₀ : 0 < R₀)
    (hM : ∀ r, R₀ ≤ r → 0 ≤ M r ∧ M r ≤ δ₀)
    (hcoarse : ∀ R, R₀ ≤ θ * R → M (θ * R) ≤ θ ^ (-(d : ℤ)) * M R)
    (himprove : ∀ R, R₀ ≤ θ * R → K ^ 2 / R ^ 2 ≤ M R → M (θ * R) ≤ (θ / 2) * M R) :
    ∀ r, R₀ ≤ r → M r ≤ (max 1 (θ ^ ((2 : ℤ) - d)) * K ^ 2) / r ^ 2 := by
  intro r hr
  have hr0 : 0 < r := hR₀.trans_le hr
  let A : ℝ := max 1 (θ ^ ((2 : ℤ) - d))
  have hA1 : 1 ≤ A := le_max_left _ _
  have hA0 : 0 < A := zero_lt_one.trans_le hA1
  have hAθ : θ ^ ((2 : ℤ) - d) ≤ A := le_max_right _ _
  have hAK : 0 ≤ A * K ^ 2 := mul_nonneg hA0.le (pow_nonneg hK 2)
  by_contra hn
  have hlt : (A * K ^ 2) / r ^ 2 < M r := lt_of_not_ge hn
  let F : ℝ → ℝ := fun s ↦ s ^ 2 * M s
  have hFr : A * K ^ 2 < F r := by
    have hh := (div_lt_iff₀ (sq_pos_of_pos hr0)).mp hlt
    simpa only [F, mul_comm] using hh
  let q : ℝ := θ ^ 3 / 2
  have hq0 : 0 < q := by positivity
  have hq1 : q < 1 := by
    have hθ3 : θ ^ 3 < 1 := pow_lt_one₀ hθ0.le hθ1 (by norm_num)
    dsimp only [q]
    linarith
  let s : ℕ → ℝ := fun j ↦ r / θ ^ j
  have hs_pos (j : ℕ) : 0 < s j := div_pos hr0 (pow_pos hθ0 j)
  have hsR (j : ℕ) : R₀ ≤ s j := by
    refine hr.trans ?_
    dsimp only [s]
    rw [le_div_iff₀ (pow_pos hθ0 j)]
    exact mul_le_of_le_one_right hr0.le (pow_le_one₀ hθ0.le hθ1.le)
  have hθs (j : ℕ) : θ * s (j + 1) = s j := by
    dsimp only [s]
    rw [pow_succ']
    field_simp [hθ0.ne']
  have hθpow : θ ^ 2 * θ ^ (-(d : ℤ)) = θ ^ ((2 : ℤ) - d) := by
    have hh := (zpow_add₀ hθ0.ne' (2 : ℤ) (-(d : ℤ))).symm
    simpa only [sub_eq_add_neg, zpow_ofNat] using hh
  have hind (j : ℕ) : A * K ^ 2 < F (s j) ∧ F r ≤ q ^ j * F (s j) := by
    induction j with
    | zero =>
      simp only [s, pow_zero, div_one, one_mul]
      exact ⟨hFr, le_rfl⟩
    | succ j ih =>
      obtain ⟨h1, h2⟩ := ih
      have hMs1 : 0 ≤ M (s (j + 1)) := (hM (s (j + 1)) (hsR (j + 1))).1
      have hFs1 : 0 ≤ F (s (j + 1)) := mul_nonneg (sq_nonneg _) hMs1
      have hs_sq : (s j) ^ 2 = θ ^ 2 * (s (j + 1)) ^ 2 := by
        rw [← hθs j, mul_pow]
      have hc := hcoarse (s (j + 1)) (by rw [hθs j]; exact hsR j)
      rw [hθs j] at hc
      have hFc : F (s j) ≤ A * F (s (j + 1)) := by
        calc
          F (s j) = θ ^ 2 * (s (j + 1)) ^ 2 * M (s j) := by
            dsimp only [F]; rw [hs_sq]
          _ ≤ θ ^ 2 * (s (j + 1)) ^ 2 * (θ ^ (-(d : ℤ)) * M (s (j + 1))) :=
            mul_le_mul_of_nonneg_left hc (by positivity)
          _ = (θ ^ 2 * θ ^ (-(d : ℤ))) * F (s (j + 1)) := by
            dsimp only [F]; ring
          _ = θ ^ ((2 : ℤ) - d) * F (s (j + 1)) := by rw [hθpow]
          _ ≤ A * F (s (j + 1)) := mul_le_mul_of_nonneg_right hAθ hFs1
      have hthresh : K ^ 2 / (s (j + 1)) ^ 2 ≤ M (s (j + 1)) := by
        rw [div_le_iff₀ (sq_pos_of_pos (hs_pos (j + 1)))]
        have hAKF : A * K ^ 2 < A * F (s (j + 1)) := h1.trans_le hFc
        have hKF : K ^ 2 < F (s (j + 1)) := lt_of_mul_lt_mul_left hAKF hA0.le
        dsimp only [F] at hKF
        linarith
      have himp := himprove (s (j + 1)) (by rw [hθs j]; exact hsR j) hthresh
      rw [hθs j] at himp
      have hFi : F (s j) ≤ q * F (s (j + 1)) := by
        calc
          F (s j) = θ ^ 2 * (s (j + 1)) ^ 2 * M (s j) := by
            dsimp only [F]; rw [hs_sq]
          _ ≤ θ ^ 2 * (s (j + 1)) ^ 2 * ((θ / 2) * M (s (j + 1))) :=
            mul_le_mul_of_nonneg_left himp (by positivity)
          _ = q * F (s (j + 1)) := by
            dsimp only [F, q]; ring
      refine ⟨?_, ?_⟩
      · exact h1.trans_le (hFi.trans (mul_le_of_le_one_left hFs1 hq1.le))
      · calc
          F r ≤ q ^ j * F (s j) := h2
          _ ≤ q ^ j * (q * F (s (j + 1))) :=
            mul_le_mul_of_nonneg_left hFi (pow_nonneg hq0.le j)
          _ = q ^ (j + 1) * F (s (j + 1)) := by rw [pow_succ']; ring
  have hub (j : ℕ) : F r ≤ r ^ 2 * δ₀ * (θ / 2) ^ j := by
    have hMs : M (s j) ≤ δ₀ := (hM (s j) (hsR j)).2
    have hθj : θ ^ j ≠ 0 := pow_ne_zero j hθ0.ne'
    calc
      F r ≤ q ^ j * F (s j) := (hind j).2
      _ ≤ q ^ j * ((s j) ^ 2 * δ₀) := by
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg hq0.le j)
        exact mul_le_mul_of_nonneg_left hMs (sq_nonneg _)
      _ = r ^ 2 * δ₀ * (θ / 2) ^ j := by
        dsimp only [q, s]
        have hqpow : (θ ^ 3 / 2) ^ j = (θ ^ j) ^ 2 * (θ / 2) ^ j := by
          rw [show θ ^ 3 / 2 = θ ^ 2 * (θ / 2) by ring, mul_pow, ← pow_mul, mul_comm 2 j, pow_mul]
        rw [hqpow, div_pow]
        field_simp [hθj]
  have hlim : Tendsto (fun j : ℕ ↦ r ^ 2 * δ₀ * (θ / 2) ^ j) atTop (𝓝 0) := by
    have h0 : 0 ≤ r ^ 2 * δ₀ := mul_nonneg (sq_nonneg r) hδ
    have _ := h0
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by linarith : θ / 2 < 1)).const_mul
        (r ^ 2 * δ₀)
  have hle0 : F r ≤ 0 := ge_of_tendsto' hlim hub
  linarith

/-- Backward scale iteration with additive stopping error (I2b.1–I2b.2): if `M` is bounded on
`[R₀, ∞)` and satisfies `M (ρ * R) ≤ q * M R + C_star / (ρ * R) ^ 2` whenever `R₀ ≤ ρ * R`,
then `M r ≤ (C_star / (1 - q * ρ ^ 2)) / r ^ 2` for every `r ≥ R₀`. -/
theorem stopped_tilt_iteration {ρ q C_star δ₀ R₀ : ℝ} {M : ℝ → ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hC : 0 ≤ C_star) (hδ : 0 ≤ δ₀) (hR₀ : 0 < R₀)
    (hM : ∀ r, R₀ ≤ r → 0 ≤ M r ∧ M r ≤ δ₀)
    (hstep : ∀ R, R₀ ≤ ρ * R → M (ρ * R) ≤ q * M R + C_star / (ρ * R) ^ 2) :
    ∀ r, R₀ ≤ r → M r ≤ (C_star / (1 - q * ρ ^ 2)) / r ^ 2 := by
  intro r hr
  have hr0 : 0 < r := hR₀.trans_le hr
  have hρ2 : ρ ^ 2 ≤ 1 := pow_le_one₀ hρ0.le hρ1.le
  have hqρ : q * ρ ^ 2 < 1 := by nlinarith
  have hden : 0 < 1 - q * ρ ^ 2 := sub_pos.mpr hqρ
  let B : ℝ := C_star / (1 - q * ρ ^ 2)
  have hB0 : 0 ≤ B := div_nonneg hC hden.le
  have hCB : C_star - B = -(q * ρ ^ 2 * B) := by
    dsimp only [B]
    field_simp [hden.ne']
    ring
  let s : ℕ → ℝ := fun j ↦ r / ρ ^ j
  have hs_pos (j : ℕ) : 0 < s j := div_pos hr0 (pow_pos hρ0 j)
  have hsR (j : ℕ) : R₀ ≤ s j := by
    refine hr.trans ?_
    dsimp only [s]
    rw [le_div_iff₀ (pow_pos hρ0 j)]
    exact mul_le_of_le_one_right hr0.le (pow_le_one₀ hρ0.le hρ1.le)
  have hρs (j : ℕ) : ρ * s (j + 1) = s j := by
    dsimp only [s]
    rw [pow_succ']
    field_simp [hρ0.ne']
  have hind (j : ℕ) : M r - B / r ^ 2 ≤ q ^ j * (M (s j) - B / (s j) ^ 2) := by
    induction j with
    | zero =>
      simp [s]
    | succ j ih =>
      have hst := hstep (s (j + 1)) (by rw [hρs j]; exact hsR j)
      have hone : M (s j) - B / (s j) ^ 2 ≤ q * (M (s (j + 1)) - B / (s (j + 1)) ^ 2) := by
        rw [← hρs j]
        calc
          M (ρ * s (j + 1)) - B / (ρ * s (j + 1)) ^ 2
            ≤ q * M (s (j + 1)) + C_star / (ρ * s (j + 1)) ^ 2 - B / (ρ * s (j + 1)) ^ 2 :=
              sub_le_sub_right hst _
          _ = q * M (s (j + 1)) + (C_star - B) / (ρ * s (j + 1)) ^ 2 := by ring
          _ = q * (M (s (j + 1)) - B / (s (j + 1)) ^ 2) := by
              rw [hCB]
              have hsne : s (j + 1) ≠ 0 := (hs_pos (j + 1)).ne'
              field_simp [hρ0.ne', hsne]
              ring
      calc
        M r - B / r ^ 2 ≤ q ^ j * (M (s j) - B / (s j) ^ 2) := ih
        _ ≤ q ^ j * (q * (M (s (j + 1)) - B / (s (j + 1)) ^ 2)) :=
          mul_le_mul_of_nonneg_left hone (pow_nonneg hq0 j)
        _ = q ^ (j + 1) * (M (s (j + 1)) - B / (s (j + 1)) ^ 2) := by rw [pow_succ']; ring
  have hub (j : ℕ) : M r - B / r ^ 2 ≤ q ^ j * δ₀ := by
    refine (hind j).trans (mul_le_mul_of_nonneg_left ?_ (pow_nonneg hq0 j))
    have hBs : 0 ≤ B / (s j) ^ 2 := div_nonneg hB0 (sq_nonneg _)
    linarith [(hM (s j) (hsR j)).2]
  have hlim : Tendsto (fun j : ℕ ↦ q ^ j * δ₀) atTop (𝓝 0) := by
    have _ : 0 ≤ δ₀ := hδ
    simpa only [zero_mul] using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const δ₀
  have hle0 : M r - B / r ^ 2 ≤ 0 := ge_of_tendsto' hlim hub
  linarith

/-! ## I1 & I3. Ball tilt integrals and optimal ball tilt -/

/-- Non-normalized tangential Dirichlet energy on `closedBall x r` with respect to direction `e`
(I1). -/
@[expose] def ballTiltIntegral {d : ℕ} (v : Space d → ℝ) (x e : Space d) (r : ℝ) : ℝ :=
  ∫ y in closedBall x r, ‖gradient v y‖ ^ 2 - inner ℝ (gradient v y) e ^ 2

/-- Scale-normalized optimal ball tilt minimized over unit directions `e ∈ sphere 0 1` (I1). -/
@[expose] def optimalBallTilt {m : ℕ} (v : Space (m + 1) → ℝ) (x : Space (m + 1)) (r : ℝ) : ℝ :=
  sInf ((fun e ↦ r ^ (-(m : ℤ)) * ballTiltIntegral v x e r) '' sphere 0 1)

/-- Reversing the normal direction leaves the ball tilt integral unchanged. -/
@[simp] theorem ballTiltIntegral_neg {d : ℕ} (v : Space d → ℝ) (x e : Space d) (r : ℝ) :
    ballTiltIntegral v x (-e) r = ballTiltIntegral v x e r := by
  simp only [ballTiltIntegral, inner_neg_right, neg_sq]

/-- Pointwise rescaling identity relating `diffuseTiltDensity` of a translated dilation to the
physical tilt integrand (I1). -/
theorem diffuseTiltDensity_translate_dilation {d : ℕ} (v : Space d → ℝ)
    (x e : Space d) {R : ℝ} (hR : 0 < R) (z : Space d) :
    diffuseTiltDensity R (fun y ↦ v (x + R • y)) e z =
      R * (‖gradient v (x + R • z)‖ ^ 2 - inner ℝ (gradient v (x + R • z)) e ^ 2) := by
  simp only [diffuseTiltDensity, gradient_comp_translate_dilation, norm_smul,
    Real.norm_of_nonneg hR.le, real_inner_smul_left]
  field_simp [hR.ne']

/-- Change of variables between unit-scale `diffuseTiltDensity` and physical `ballTiltIntegral`
(I1). -/
theorem integral_diffuseTiltDensity_translate_dilation {m : ℕ} (v : Space (m + 1) → ℝ)
    (x e : Space (m + 1)) {R : ℝ} (hR : 0 < R) (ρ : ℝ) :
    (∫ z in closedBall 0 ρ, diffuseTiltDensity R (fun y ↦ v (x + R • y)) e z) =
      (R ^ m)⁻¹ * ballTiltIntegral v x e (R * ρ) := by
  simp_rw [diffuseTiltDensity_translate_dilation v x e hR]
  exact setIntegral_closedBall_translate_dilation_weighted
    (fun y ↦ ‖gradient v y‖ ^ 2 - inner ℝ (gradient v y) e ^ 2) x hR ρ

/-- Exact scale invariance between rescaled diffuse tilt on `closedBall 0 ρ` and normalized
physical tilt on `closedBall x (R * ρ)` (I1). -/
theorem scaled_integral_diffuseTiltDensity_eq {m : ℕ} (v : Space (m + 1) → ℝ)
    (x e : Space (m + 1)) {R ρ : ℝ} (hR : 0 < R) :
    ρ ^ (-(m : ℤ)) * (∫ z in closedBall 0 ρ, diffuseTiltDensity R (fun y ↦ v (x + R • y)) e z) =
      (R * ρ) ^ (-(m : ℤ)) * ballTiltIntegral v x e (R * ρ) := by
  rw [integral_diffuseTiltDensity_translate_dilation v x e hR ρ, mul_zpow R ρ (-(m : ℤ)),
    zpow_neg R, zpow_natCast]
  ring

/-- For nonzero `r`, `r ^ m / r ^ 2` agrees with the integer power `r ^ ((m : ℤ) - 2)`. -/
theorem pow_div_sq_eq_zpow_sub_two {r : ℝ} (hr : r ≠ 0) (m : ℕ) :
    r ^ m / r ^ 2 = r ^ ((m : ℤ) - 2) := by
  rw [zpow_sub₀ hr, zpow_natCast, zpow_ofNat]

/-- For a unit direction `e`, the ball tilt integral is nonnegative. -/
theorem ballTiltIntegral_nonneg {d : ℕ} (v : Space d → ℝ) (x : Space d)
    {e : Space d} (he : ‖e‖ = 1) (r : ℝ) :
    0 ≤ ballTiltIntegral v x e r :=
  integral_nonneg fun y ↦ sub_nonneg.mpr (inner_sq_le_norm_sq_of_unit (gradient v y) he)

/-- Local Lipschitz regularity makes the tilt integrand integrable on compact sets for any `e`. -/
theorem integrableOn_ballTiltIntegrand {d : ℕ} {v : Space d → ℝ}
    (hv : LocallyLipschitz v) {K : Set (Space d)} (hK : IsCompact K) (e : Space d) :
    IntegrableOn (fun y ↦ ‖gradient v y‖ ^ 2 - inner ℝ (gradient v y) e ^ 2) K := by
  have hi := integrableOn_gradient_sq_of_locallyLipschitz hv hK
  have hp : IntegrableOn (fun y ↦ inner ℝ (gradient v y) e ^ 2) K := by
    apply (hi.mul_const (‖e‖ ^ 2)).mono'
      (((measurable_gradient v).inner (𝕜 := ℝ) measurable_const).pow_const 2).aestronglyMeasurable
    filter_upwards with y
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    simpa only [sq_abs, mul_pow] using
      (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
        (abs_real_inner_le_norm (gradient v y) e)
  exact hi.sub hp

/-- Set inclusion between closed balls preserves the ball tilt inequality for unit directions. -/
theorem ballTiltIntegral_mono_closedBall {d : ℕ} {v : Space d → ℝ}
    (hv : LocallyLipschitz v) {x₁ x₂ e : Space d} (he : ‖e‖ = 1) {r₁ r₂ : ℝ}
    (hsub : closedBall x₁ r₁ ⊆ closedBall x₂ r₂) :
    ballTiltIntegral v x₁ e r₁ ≤ ballTiltIntegral v x₂ e r₂ :=
  setIntegral_mono_set
    (integrableOn_ballTiltIntegrand hv (isCompact_closedBall x₂ r₂) e)
    (Eventually.of_forall fun y ↦ sub_nonneg.mpr (inner_sq_le_norm_sq_of_unit (gradient v y) he))
    (Eventually.of_forall hsub)

/-- Larger concentric balls have at least as large ball tilt for any unit direction. -/
theorem ballTiltIntegral_mono_radius {d : ℕ} {v : Space d → ℝ}
    (hv : LocallyLipschitz v) (x : Space d) {e : Space d} (he : ‖e‖ = 1)
    {r₁ r₂ : ℝ} (hr : r₁ ≤ r₂) :
    ballTiltIntegral v x e r₁ ≤ ballTiltIntegral v x e r₂ :=
  ballTiltIntegral_mono_closedBall hv he (closedBall_subset_closedBall hr)

/-- For locally Lipschitz `v`, `e ↦ ballTiltIntegral v x e r` is continuous on `Space d`. -/
theorem continuous_ballTiltIntegral {d : ℕ} {v : Space d → ℝ}
    (hv : LocallyLipschitz v) (x : Space d) (r : ℝ) :
    Continuous (fun e ↦ ballTiltIntegral v x e r) := by
  rw [continuous_iff_continuousAt]
  intro e₀
  unfold ballTiltIntegral
  apply MeasureTheory.continuousAt_of_dominated (bound := fun y ↦
    (1 + (‖e₀‖ + 1) ^ 2) * ‖gradient v y‖ ^ 2)
  · exact Eventually.of_forall fun e ↦
      (((measurable_gradient v).norm.pow_const 2).sub
        (((measurable_gradient v).inner (𝕜 := ℝ) measurable_const).pow_const 2)).aestronglyMeasurable
  · filter_upwards [Metric.ball_mem_nhds e₀ zero_lt_one] with e he
    have he_norm : ‖e‖ ≤ ‖e₀‖ + 1 := by
      have hd : ‖e - e₀‖ < 1 := by simpa only [mem_ball, dist_eq_norm] using he
      linarith [norm_sub_norm_le e e₀]
    filter_upwards with y
    have hcs : inner ℝ (gradient v y) e ^ 2 ≤ (‖gradient v y‖ * ‖e‖) ^ 2 := by
      simpa only [sq_abs] using
        (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
          (abs_real_inner_le_norm (gradient v y) e)
    have he2 : ‖e‖ ^ 2 ≤ (‖e₀‖ + 1) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr he_norm
    have hprod : ‖gradient v y‖ ^ 2 * ‖e‖ ^ 2 ≤ ‖gradient v y‖ ^ 2 * (‖e₀‖ + 1) ^ 2 :=
      mul_le_mul_of_nonneg_left he2 (sq_nonneg _)
    rw [Real.norm_eq_abs]
    refine (abs_sub _ _).trans ?_
    rw [abs_of_nonneg (sq_nonneg _), abs_of_nonneg (sq_nonneg _)]
    nlinarith [mul_pow ‖gradient v y‖ ‖e‖ 2]
  · exact (integrableOn_gradient_sq_of_locallyLipschitz hv
      (isCompact_closedBall x r)).const_mul _
  · exact Eventually.of_forall fun y ↦ (by fun_prop : Continuous fun e ↦
      ‖gradient v y‖ ^ 2 - inner ℝ (gradient v y) e ^ 2).continuousAt

/-- Compactness of the unit sphere gives a unit direction attaining `optimalBallTilt v x r`,
together with nonnegativity and optimality over all unit directions (I1). -/
theorem exists_optimalBallTilt_direction {m : ℕ} {v : Space (m + 1) → ℝ}
    (hv : LocallyLipschitz v) (x : Space (m + 1)) {r : ℝ} (hr : 0 < r) :
    ∃ e : Space (m + 1), ‖e‖ = 1 ∧
      optimalBallTilt v x r = r ^ (-(m : ℤ)) * ballTiltIntegral v x e r ∧
      0 ≤ optimalBallTilt v x r ∧
      ∀ e' : Space (m + 1), ‖e'‖ = 1 →
        optimalBallTilt v x r ≤ r ^ (-(m : ℤ)) * ballTiltIntegral v x e' r := by
  let φ : Space (m + 1) → ℝ := fun e ↦ r ^ (-(m : ℤ)) * ballTiltIntegral v x e r
  have hcomp : IsCompact (sphere (0 : Space (m + 1)) 1) := isCompact_sphere 0 1
  have hne : (sphere (0 : Space (m + 1)) 1).Nonempty :=
    ⟨verticalDirection m, by simp [norm_verticalDirection]⟩
  have hcont : ContinuousOn φ (sphere 0 1) :=
    (continuous_const.mul (continuous_ballTiltIntegral hv x r)).continuousOn
  obtain ⟨e, heS, hmin⟩ := hcomp.exists_isMinOn hne hcont
  have he : ‖e‖ = 1 := by simpa only [mem_sphere_zero_iff_norm] using heS
  have hbdd : BddBelow (φ '' sphere 0 1) := by
    refine ⟨φ e, ?_⟩
    rintro _ ⟨e', he'S, rfl⟩
    exact hmin he'S
  have himg_ne : (φ '' sphere 0 1).Nonempty := ⟨φ e, e, heS, rfl⟩
  have hopt : optimalBallTilt v x r = φ e := by
    unfold optimalBallTilt
    apply le_antisymm
    · exact csInf_le hbdd ⟨e, heS, rfl⟩
    · refine le_csInf himg_ne ?_
      rintro _ ⟨e', he'S, rfl⟩
      exact hmin he'S
  have hrpow : 0 ≤ r ^ (-(m : ℤ)) := zpow_nonneg hr.le _
  have hnonneg : 0 ≤ optimalBallTilt v x r := by
    rw [hopt]
    exact mul_nonneg hrpow (ballTiltIntegral_nonneg v x he r)
  refine ⟨e, he, hopt, hnonneg, ?_⟩
  intro e' he'
  rw [hopt]
  exact hmin (by simpa only [mem_sphere_zero_iff_norm] using he')

/-- `optimalBallTilt` is nonnegative for positive radii. -/
theorem optimalBallTilt_nonneg {m : ℕ} {v : Space (m + 1) → ℝ}
    (hv : LocallyLipschitz v) (x : Space (m + 1)) {r : ℝ} (hr : 0 < r) :
    0 ≤ optimalBallTilt v x r := by
  obtain ⟨_, _, _, hnonneg, _⟩ := exists_optimalBallTilt_direction hv x hr
  exact hnonneg

/-- `optimalBallTilt` is bounded above by the normalized tilt in any unit direction. -/
theorem optimalBallTilt_le {m : ℕ} {v : Space (m + 1) → ℝ}
    (hv : LocallyLipschitz v) (x : Space (m + 1)) {r : ℝ} (hr : 0 < r)
    {e : Space (m + 1)} (he : ‖e‖ = 1) :
    optimalBallTilt v x r ≤ r ^ (-(m : ℤ)) * ballTiltIntegral v x e r := by
  obtain ⟨_, _, _, _, hle⟩ := exists_optimalBallTilt_direction hv x hr
  exact hle e he

/-- Coarse scaling inequality for `optimalBallTilt` across concentric balls (I3). -/
theorem optimalBallTilt_mul_le {m : ℕ} {v : Space (m + 1) → ℝ}
    (hv : LocallyLipschitz v) (x : Space (m + 1)) {θ r : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hr : 0 < r) :
    optimalBallTilt v x (θ * r) ≤ θ ^ (-(m : ℤ)) * optimalBallTilt v x r := by
  obtain ⟨e, he, hopt, _, _⟩ := exists_optimalBallTilt_direction hv x hr
  have hθr : 0 < θ * r := mul_pos hθ0 hr
  have hsub : θ * r ≤ r := mul_le_of_le_one_left hr.le hθ1
  calc
    optimalBallTilt v x (θ * r)
      ≤ (θ * r) ^ (-(m : ℤ)) * ballTiltIntegral v x e (θ * r) :=
        optimalBallTilt_le hv x hθr he
    _ = θ ^ (-(m : ℤ)) * (r ^ (-(m : ℤ)) * ballTiltIntegral v x e (θ * r)) := by
        rw [mul_zpow θ r (-(m : ℤ)), mul_assoc]
    _ ≤ θ ^ (-(m : ℤ)) * (r ^ (-(m : ℤ)) * ballTiltIntegral v x e r) := by
        apply mul_le_mul_of_nonneg_left _ (zpow_nonneg hθ0.le _)
        exact mul_le_mul_of_nonneg_left
          (ballTiltIntegral_mono_radius hv x he hsub) (zpow_nonneg hr.le _)
    _ = θ ^ (-(m : ℤ)) * optimalBallTilt v x r := by rw [← hopt]

/-- Application of `stopped_tilt_iteration_I2` to `optimalBallTilt` (I3.1). -/
theorem optimalBallTilt_le_div_sq_I2 {m : ℕ} {v : Space (m + 1) → ℝ}
    (hv : LocallyLipschitz v) (x : Space (m + 1))
    {θ K δ₀ R₀ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hK : 0 ≤ K) (hδ : 0 ≤ δ₀) (hR₀ : 0 < R₀)
    (hbound : ∀ r, R₀ ≤ r → optimalBallTilt v x r ≤ δ₀)
    (himprove : ∀ R, R₀ ≤ θ * R → K ^ 2 / R ^ 2 ≤ optimalBallTilt v x R →
      optimalBallTilt v x (θ * R) ≤ (θ / 2) * optimalBallTilt v x R) :
    ∀ r, R₀ ≤ r → optimalBallTilt v x r ≤ (max 1 (θ ^ ((2 : ℤ) - m)) * K ^ 2) / r ^ 2 :=
  stopped_tilt_iteration_I2 hθ0 hθ1 hK hδ hR₀
    (fun r hr ↦ ⟨optimalBallTilt_nonneg hv x (hR₀.trans_le hr), hbound r hr⟩)
    (fun _ hR ↦ optimalBallTilt_mul_le hv x hθ0 hθ1.le
      (pos_of_mul_pos_right (hR₀.trans_le hR) hθ0.le))
    himprove

/-- Application of `stopped_tilt_iteration` to `optimalBallTilt` (I3.2). -/
theorem optimalBallTilt_le_div_sq {m : ℕ} {v : Space (m + 1) → ℝ}
    (hv : LocallyLipschitz v) (x : Space (m + 1))
    {ρ q C_star δ₀ R₀ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hC : 0 ≤ C_star) (hδ : 0 ≤ δ₀) (hR₀ : 0 < R₀)
    (hbound : ∀ r, R₀ ≤ r → optimalBallTilt v x r ≤ δ₀)
    (hstep : ∀ R, R₀ ≤ ρ * R →
      optimalBallTilt v x (ρ * R) ≤ q * optimalBallTilt v x R + C_star / (ρ * R) ^ 2) :
    ∀ r, R₀ ≤ r → optimalBallTilt v x r ≤ (C_star / (1 - q * ρ ^ 2)) / r ^ 2 :=
  stopped_tilt_iteration hρ0 hρ1 hq0 hq1 hC hδ hR₀
    (fun r hr ↦ ⟨optimalBallTilt_nonneg hv x (hR₀.trans_le hr), hbound r hr⟩) hstep

/-! ## I4. Rank-one line projections and sign-free direction comparison -/

/-- Rank-one orthogonal projection `z ↦ ⟪e, z⟫ e` onto the line spanned by `e` (I1, I4). -/
@[expose] def lineProjection {d : ℕ} (e : Space d) : Space d →L[ℝ] Space d :=
  (innerSL ℝ e).smulRight e

@[simp] theorem lineProjection_apply {d : ℕ} (e x : Space d) :
    lineProjection e x = inner ℝ e x • e := rfl

@[simp] theorem lineProjection_neg {d : ℕ} (e : Space d) :
    lineProjection (-e) = lineProjection e := by
  ext x
  simp [lineProjection]

/-- Two unit vectors generate the same rank-one line projection iff they agree up to sign. -/
theorem lineProjection_eq_iff_of_unit {d : ℕ} {a b : Space d} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    lineProjection a = lineProjection b ↔ b = a ∨ b = -a := by
  constructor
  · intro h
    have happ := congrArg (fun L : Space d →L[ℝ] Space d ↦ L a) h
    simp only [lineProjection_apply, real_inner_self_eq_norm_sq, ha, one_pow, one_smul] at happ
    have hnorm : |inner ℝ b a| = 1 := by
      have hh := congrArg norm happ
      simpa only [ha, hb, norm_smul, Real.norm_eq_abs, mul_one] using hh.symm
    rcases abs_eq (by norm_num : (0 : ℝ) ≤ 1) |>.mp hnorm with h1 | hm1
    · left
      simpa only [h1, one_smul] using happ.symm
    · right
      rw [hm1, neg_one_smul] at happ
      exact neg_eq_iff_eq_neg.mp happ.symm
  · rintro (rfl | rfl)
    · rfl
    · exact (lineProjection_neg a).symm

/-- Exact operator-norm identity for the difference of two unit rank-one line projections:
`‖lineProjection a - lineProjection b‖ ^ 2 = 1 - inner ℝ a b ^ 2` (I4). -/
theorem norm_lineProjection_sub_sq {d : ℕ} {a b : Space d} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    ‖lineProjection a - lineProjection b‖ ^ 2 = 1 - inner ℝ a b ^ 2 := by
  let c : ℝ := inner ℝ a b
  have hc2 : c ^ 2 ≤ 1 := by
    simpa only [c, ha, one_pow] using inner_sq_le_norm_sq_of_unit a hb
  have h1c : 0 ≤ 1 - c ^ 2 := sub_nonneg.mpr hc2
  apply le_antisymm
  · have hop : ‖lineProjection a - lineProjection b‖ ≤ Real.sqrt (1 - c ^ 2) := by
      refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x ↦ ?_
      have hsq : ‖(lineProjection a - lineProjection b) x‖ ^ 2 ≤ (1 - c ^ 2) * ‖x‖ ^ 2 := by
        let u : Space d := b - c • a
        let α : ℝ := inner ℝ a x
        let w : Space d := x - α • a
        have hu_orth : inner ℝ u a = 0 := by
          simp only [u, c, inner_sub_left, real_inner_smul_left, real_inner_comm b a,
            real_inner_self_eq_norm_sq, ha]
          ring
        have hu_sq : ‖u‖ ^ 2 = 1 - c ^ 2 := by
          rw [← real_inner_self_eq_norm_sq]
          simp only [u, c, inner_sub_left, inner_sub_right, real_inner_smul_left,
            real_inner_smul_right, real_inner_comm b a]
          simp only [real_inner_self_eq_norm_sq, ha, hb]
          ring
        have hw_sq : ‖w‖ ^ 2 = ‖x‖ ^ 2 - α ^ 2 := by
          rw [← real_inner_self_eq_norm_sq]
          simp only [w, α, inner_sub_left, inner_sub_right, real_inner_smul_left,
            real_inner_smul_right, real_inner_comm x a]
          simp only [real_inner_self_eq_norm_sq, ha]
          ring
        have hbx : inner ℝ b x = c * α + inner ℝ u w := by
          have huw : inner ℝ u w = inner ℝ b x - c * α := by
            simp only [w, inner_sub_right, real_inner_smul_right, hu_orth, mul_zero, sub_zero]
            simp only [u, inner_sub_left, real_inner_smul_left, α]
          linarith
        have hTx : ‖(lineProjection a - lineProjection b) x‖ ^ 2 =
            (1 - c ^ 2) * α ^ 2 + inner ℝ u w ^ 2 := by
          rw [← real_inner_self_eq_norm_sq]
          simp only [sub_apply, lineProjection_apply, inner_sub_left, inner_sub_right,
            real_inner_smul_left, real_inner_smul_right, real_inner_comm a b]
          simp only [real_inner_self_eq_norm_sq, ha, hb]
          rw [show inner ℝ a x = α from rfl, show inner ℝ a b = c from rfl, hbx]
          ring
        have hcs : inner ℝ u w ^ 2 ≤ (1 - c ^ 2) * (‖x‖ ^ 2 - α ^ 2) := by
          have hh : inner ℝ u w ^ 2 ≤ (‖u‖ * ‖w‖) ^ 2 := by
            simpa only [sq_abs] using
              (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
                (abs_real_inner_le_norm u w)
          rw [mul_pow, hu_sq, hw_sq] at hh
          exact hh
        linarith
      have hrhs : (1 - c ^ 2) * ‖x‖ ^ 2 = (Real.sqrt (1 - c ^ 2) * ‖x‖) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt h1c]
      rw [hrhs] at hsq
      exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp hsq
    have hsq := (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mpr hop
    simpa only [Real.sq_sqrt h1c, c] using hsq
  · have happ : (lineProjection a - lineProjection b) a = a - c • b := by
      simp only [sub_apply, lineProjection_apply, real_inner_self_eq_norm_sq,
        ha, one_pow, one_smul, real_inner_comm a b, c]
    have hval : ‖a - c • b‖ ^ 2 = 1 - c ^ 2 := by
      rw [← real_inner_self_eq_norm_sq]
      simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
        real_inner_comm a b]
      simp only [real_inner_self_eq_norm_sq, ha, hb, c]
      ring
    have hle : ‖a - c • b‖ ≤ ‖lineProjection a - lineProjection b‖ := by
      rw [← happ]
      simpa only [ha, mul_one] using (lineProjection a - lineProjection b).le_opNorm a
    rw [← hval]
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hle

/-- Pointwise sign-free direction comparison (I4): for unit vectors `a, b` and any vector `g`,
`‖lineProjection a - lineProjection b‖ ^ 2 * ‖g‖ ^ 2` is controlled by twice the sum of the two
tangential energies of `g`. -/
theorem norm_lineProjection_sub_sq_mul_norm_sq_le {d : ℕ} {a b : Space d}
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (g : Space d) :
    ‖lineProjection a - lineProjection b‖ ^ 2 * ‖g‖ ^ 2 ≤
      2 * (‖g‖ ^ 2 - inner ℝ g a ^ 2) + 2 * (‖g‖ ^ 2 - inner ℝ g b ^ 2) := by
  by_cases hg : g = 0
  · simp [hg]
  · have hg0 : 0 < ‖g‖ := norm_pos_iff.mpr hg
    let ν : Space d := ‖g‖⁻¹ • g
    have hν : ‖ν‖ = 1 := by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hg0.le), inv_mul_cancel₀ hg0.ne']
    have htri : ‖lineProjection a - lineProjection b‖ ≤
        ‖lineProjection a - lineProjection ν‖ + ‖lineProjection ν - lineProjection b‖ := by
      simpa only [sub_add_sub_cancel] using
        norm_add_le (lineProjection a - lineProjection ν) (lineProjection ν - lineProjection b)
    have hsq : ‖lineProjection a - lineProjection b‖ ^ 2 ≤
        2 * ‖lineProjection a - lineProjection ν‖ ^ 2 +
          2 * ‖lineProjection ν - lineProjection b‖ ^ 2 := by
      nlinarith [norm_nonneg (lineProjection a - lineProjection b),
        norm_nonneg (lineProjection a - lineProjection ν),
        norm_nonneg (lineProjection ν - lineProjection b),
        sq_nonneg (‖lineProjection a - lineProjection ν‖ -
          ‖lineProjection ν - lineProjection b‖)]
    rw [norm_lineProjection_sub_sq ha hν, norm_lineProjection_sub_sq hν hb] at hsq
    have hmul := mul_le_mul_of_nonneg_right hsq (sq_nonneg ‖g‖)
    have haν : (1 - inner ℝ a ν ^ 2) * ‖g‖ ^ 2 = ‖g‖ ^ 2 - inner ℝ g a ^ 2 := by
      dsimp only [ν]
      rw [real_inner_smul_right, real_inner_comm a g]
      have hgne : ‖g‖ ≠ 0 := hg0.ne'
      field_simp [hgne]
    have hνb : (1 - inner ℝ ν b ^ 2) * ‖g‖ ^ 2 = ‖g‖ ^ 2 - inner ℝ g b ^ 2 := by
      dsimp only [ν]
      rw [real_inner_smul_left]
      have hgne : ‖g‖ ≠ 0 := hg0.ne'
      field_simp [hgne]
    nlinarith

/-- Integral form of the sign-free direction comparison on a closed ball (I4.1). -/
theorem norm_lineProjection_sub_sq_mul_kinetic_le {d : ℕ} {v : Space d → ℝ}
    (hv : LocallyLipschitz v) {a b : Space d} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (x : Space d) (r : ℝ) :
    ‖lineProjection a - lineProjection b‖ ^ 2 *
        (∫ y in closedBall x r, ‖gradient v y‖ ^ 2) ≤
      2 * ballTiltIntegral v x a r + 2 * ballTiltIntegral v x b r := by
  have hK := isCompact_closedBall x r
  have hg := integrableOn_gradient_sq_of_locallyLipschitz hv hK
  have ha_int := integrableOn_ballTiltIntegrand hv hK a
  have hb_int := integrableOn_ballTiltIntegrand hv hK b
  unfold ballTiltIntegral
  rw [← integral_const_mul, ← integral_const_mul 2, ← integral_const_mul 2,
    ← integral_add (ha_int.const_mul 2) (hb_int.const_mul 2)]
  exact integral_mono (hg.const_mul _) ((ha_int.const_mul 2).add (hb_int.const_mul 2))
    fun y ↦ norm_lineProjection_sub_sq_mul_norm_sq_le ha hb (gradient v y)

/-- Pointwise tangential energy transfer between two unit directions via line projections (I6). -/
theorem norm_sq_sub_inner_sq_le_two_mul {d : ℕ} {a b : Space d}
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (z : Space d) :
    ‖z‖ ^ 2 - inner ℝ z a ^ 2 ≤
      2 * (‖z‖ ^ 2 - inner ℝ z b ^ 2) +
        2 * ‖lineProjection b - lineProjection a‖ ^ 2 * ‖z‖ ^ 2 := by
  have hproj_norm (e : Space d) (he : ‖e‖ = 1) :
      ‖z - lineProjection e z‖ ^ 2 = ‖z‖ ^ 2 - inner ℝ z e ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, lineProjection_apply, inner_sub_left, inner_sub_right,
      inner_sub_right, real_inner_smul_left, real_inner_smul_right, real_inner_smul_left,
      real_inner_smul_right, real_inner_comm e z, real_inner_self_eq_norm_sq,
      real_inner_self_eq_norm_sq, he]
    ring
  have hdecomp : z - lineProjection a z =
      (z - lineProjection b z) + (lineProjection b - lineProjection a) z := by
    simp
  have htri : ‖z - lineProjection a z‖ ≤
      ‖z - lineProjection b z‖ + ‖(lineProjection b - lineProjection a) z‖ := by
    rw [hdecomp]
    exact norm_add_le _ _
  have hsq : ‖z - lineProjection a z‖ ^ 2 ≤
      2 * ‖z - lineProjection b z‖ ^ 2 + 2 * ‖(lineProjection b - lineProjection a) z‖ ^ 2 := by
    nlinarith [norm_nonneg (z - lineProjection a z), norm_nonneg (z - lineProjection b z),
      norm_nonneg ((lineProjection b - lineProjection a) z),
      sq_nonneg (‖z - lineProjection b z‖ - ‖(lineProjection b - lineProjection a) z‖)]
  have hop : ‖(lineProjection b - lineProjection a) z‖ ^ 2 ≤
      ‖lineProjection b - lineProjection a‖ ^ 2 * ‖z‖ ^ 2 := by
    rw [← mul_pow]
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
      ((lineProjection b - lineProjection a).le_opNorm z)
  rw [hproj_norm a ha, hproj_norm b hb] at hsq
  linarith

/-- Integral form of tangential energy transfer between two unit directions (I6). -/
theorem ballTiltIntegral_le_two_mul_add_proj_sq {d : ℕ} {v : Space d → ℝ}
    (hv : LocallyLipschitz v) {a b : Space d} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (x : Space d) (r : ℝ) :
    ballTiltIntegral v x a r ≤
      2 * ballTiltIntegral v x b r +
        2 * ‖lineProjection b - lineProjection a‖ ^ 2 *
          ∫ y in closedBall x r, ‖gradient v y‖ ^ 2 := by
  have hK := isCompact_closedBall x r
  have hg := integrableOn_gradient_sq_of_locallyLipschitz hv hK
  have ha_int := integrableOn_ballTiltIntegrand hv hK a
  have hb_int := integrableOn_ballTiltIntegrand hv hK b
  unfold ballTiltIntegral
  rw [← integral_const_mul 2, ← integral_const_mul (2 * ‖lineProjection b - lineProjection a‖ ^ 2),
    ← integral_add (hb_int.const_mul 2) (hg.const_mul _)]
  exact integral_mono ha_int ((hb_int.const_mul 2).add (hg.const_mul _))
    fun y ↦ norm_sq_sub_inner_sq_le_two_mul ha hb (gradient v y)

/-! ## I5–I7. Scale convergence of directions and coincidence across centers -/

/-- Explicit center-independent constant controlling `‖lineProjection e - lineProjection e_x‖`
in `exists_limiting_lineProjection` (I5.2). -/
@[expose] def limitingProjectionConst (m : ℕ) (c_kin B : ℝ) : ℝ :=
  6 * Real.sqrt (2 * (1 + (2 : ℝ) ^ m) * B / c_kin)

/-- Explicit center-independent constant controlling `ballTiltIntegral v x e_x r`
in `exists_limiting_lineProjection` (I6.1). -/
@[expose] def limitingTiltConst (m : ℕ) (c_kin C_kin B : ℝ) : ℝ :=
  2 * B + 2 * C_kin * limitingProjectionConst m c_kin B ^ 2

theorem limitingProjectionConst_nonneg (m : ℕ) (c_kin B : ℝ) :
    0 ≤ limitingProjectionConst m c_kin B := by
  unfold limitingProjectionConst
  positivity

theorem limitingTiltConst_nonneg (m : ℕ) {C_kin B : ℝ} (c_kin : ℝ)
    (hC : 0 ≤ C_kin) (hB : 0 ≤ B) :
    0 ≤ limitingTiltConst m c_kin C_kin B := by
  unfold limitingTiltConst
  positivity

/-- Adjacent-scale comparison of line projections when `R₀ ≤ s ≤ t ≤ 2 * s` (I5). -/
theorem norm_lineProjection_sub_le_of_adjacent_scales {m : ℕ} {v : Space (m + 1) → ℝ}
    (hv : LocallyLipschitz v) {x e₁ e₂ : Space (m + 1)}
    {c_kin B s t : ℝ} (hc : 0 < c_kin) (hB : 0 ≤ B)
    (hs : 0 < s) (hst : s ≤ t) (ht2 : t ≤ 2 * s)
    (he₁ : ‖e₁‖ = 1) (he₂ : ‖e₂‖ = 1)
    (hkin : c_kin * s ^ m ≤ ∫ y in closedBall x s, ‖gradient v y‖ ^ 2)
    (ht₁ : ballTiltIntegral v x e₁ s ≤ B * (s ^ m / s ^ 2))
    (ht₂ : ballTiltIntegral v x e₂ t ≤ B * (t ^ m / t ^ 2)) :
    ‖lineProjection e₁ - lineProjection e₂‖ ≤
      Real.sqrt (2 * (1 + (2 : ℝ) ^ m) * B / c_kin) / s := by
  have ht0 : 0 < t := hs.trans_le hst
  have htm : t ^ m ≤ (2 : ℝ) ^ m * s ^ m := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ ht0.le ht2 m
  have hs2t2 : s ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ hs.le hst 2
  have hratio : t ^ m / t ^ 2 ≤ (2 : ℝ) ^ m * (s ^ m / s ^ 2) := by
    calc
      t ^ m / t ^ 2 ≤ t ^ m / s ^ 2 :=
        div_le_div_of_nonneg_left (pow_nonneg ht0.le m) (sq_pos_of_pos hs) hs2t2
      _ ≤ ((2 : ℝ) ^ m * s ^ m) / s ^ 2 :=
        div_le_div_of_nonneg_right htm (sq_nonneg s)
      _ = (2 : ℝ) ^ m * (s ^ m / s ^ 2) := mul_div_assoc _ _ _
  have ht₂s : ballTiltIntegral v x e₂ s ≤ B * ((2 : ℝ) ^ m * (s ^ m / s ^ 2)) :=
    (ballTiltIntegral_mono_radius hv x he₂ hst).trans (ht₂.trans (mul_le_mul_of_nonneg_left hratio hB))
  have hcomp := norm_lineProjection_sub_sq_mul_kinetic_le hv he₁ he₂ x s
  have hmul : ‖lineProjection e₁ - lineProjection e₂‖ ^ 2 * (c_kin * s ^ m) ≤
      2 * (1 + (2 : ℝ) ^ m) * B * (s ^ m / s ^ 2) := by
    calc
      ‖lineProjection e₁ - lineProjection e₂‖ ^ 2 * (c_kin * s ^ m)
        ≤ ‖lineProjection e₁ - lineProjection e₂‖ ^ 2 *
            (∫ y in closedBall x s, ‖gradient v y‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hkin (sq_nonneg _)
      _ ≤ 2 * ballTiltIntegral v x e₁ s + 2 * ballTiltIntegral v x e₂ s := hcomp
      _ ≤ 2 * (B * (s ^ m / s ^ 2)) + 2 * (B * ((2 : ℝ) ^ m * (s ^ m / s ^ 2))) := by
          linarith
      _ = 2 * (1 + (2 : ℝ) ^ m) * B * (s ^ m / s ^ 2) := by ring
  have hsm_pos : 0 < s ^ m := pow_pos hs m
  have hcs_pos : 0 < c_kin * s ^ m := mul_pos hc hsm_pos
  have hsq : ‖lineProjection e₁ - lineProjection e₂‖ ^ 2 ≤
      (Real.sqrt (2 * (1 + (2 : ℝ) ^ m) * B / c_kin) / s) ^ 2 := by
    have hdiv : ‖lineProjection e₁ - lineProjection e₂‖ ^ 2 ≤
        (2 * (1 + (2 : ℝ) ^ m) * B * (s ^ m / s ^ 2)) / (c_kin * s ^ m) :=
      (le_div_iff₀ hcs_pos).mpr hmul
    have hnonneg : 0 ≤ 2 * (1 + (2 : ℝ) ^ m) * B / c_kin := by positivity
    refine hdiv.trans_eq ?_
    rw [div_pow, Real.sq_sqrt hnonneg]
    field_simp [hc.ne', hs.ne', hsm_pos.ne']
  exact (sq_le_sq₀ (norm_nonneg _) (div_nonneg (Real.sqrt_nonneg _) hs.le)).mp hsq

/-- Fixed-center asymptotic line projection and limiting-direction tilt bound (I5–I6):
under two-sided kinetic bounds `c_kin * r ^ m ≤ ∫_{B_r(x)} ‖∇v‖ ^ 2 ≤ C_kin * r ^ m` and
`optimalBallTilt v x r ≤ B / r ^ 2` for `r ≥ R₀`, there exists a unit vector `e_x` such that for
all `r ≥ R₀`, `ballTiltIntegral v x e_x r ≤ limitingTiltConst m c_kin C_kin B * (r ^ m / r ^ 2)`
and every near-optimal unit direction `e` at scale `r` (in particular every direction attaining
`optimalBallTilt v x r`) satisfies
`‖lineProjection e - lineProjection e_x‖ ≤ limitingProjectionConst m c_kin B / r`. -/
theorem exists_limiting_lineProjection {m : ℕ} {v : Space (m + 1) → ℝ}
    (hv : LocallyLipschitz v) (x : Space (m + 1))
    {R₀ c_kin C_kin B : ℝ} (hR₀ : 0 < R₀) (hc : 0 < c_kin) (hC : 0 < C_kin) (hB : 0 ≤ B)
    (hkin : ∀ r, R₀ ≤ r →
      c_kin * r ^ m ≤ (∫ y in closedBall x r, ‖gradient v y‖ ^ 2) ∧
        (∫ y in closedBall x r, ‖gradient v y‖ ^ 2) ≤ C_kin * r ^ m)
    (htilt : ∀ r, R₀ ≤ r → optimalBallTilt v x r ≤ B / r ^ 2) :
    ∃ e_x : Space (m + 1), ‖e_x‖ = 1 ∧
      (∀ r, R₀ ≤ r →
        ballTiltIntegral v x e_x r ≤ limitingTiltConst m c_kin C_kin B * (r ^ m / r ^ 2)) ∧
      (∀ r, R₀ ≤ r → ∀ e : Space (m + 1), ‖e‖ = 1 →
        r ^ (-(m : ℤ)) * ballTiltIntegral v x e r ≤ B / r ^ 2 →
        ‖lineProjection e - lineProjection e_x‖ ≤ limitingProjectionConst m c_kin B / r) := by
  let C_step : ℝ := Real.sqrt (2 * (1 + (2 : ℝ) ^ m) * B / c_kin)
  have hC_step : 0 ≤ C_step := Real.sqrt_nonneg _
  have hunnorm {s : ℝ} (hs : 0 < s) {e : Space (m + 1)}
      (he : s ^ (-(m : ℤ)) * ballTiltIntegral v x e s ≤ B / s ^ 2) :
      ballTiltIntegral v x e s ≤ B * (s ^ m / s ^ 2) := by
    have hsm : 0 < s ^ m := pow_pos hs m
    have hz : s ^ (-(m : ℤ)) = (s ^ m)⁻¹ := by rw [zpow_neg, zpow_natCast]
    rw [hz] at he
    have hh := mul_le_mul_of_nonneg_left he hsm.le
    rw [← mul_assoc, mul_inv_cancel₀ hsm.ne', one_mul] at hh
    linarith [show s ^ m * (B / s ^ 2) = B * (s ^ m / s ^ 2) by ring]
  let rad : ℕ → ℝ := fun k ↦ (2 : ℝ) ^ k * R₀
  have hrad_ge (k : ℕ) : R₀ ≤ rad k := by
    dsimp only [rad]
    exact le_mul_of_one_le_left hR₀.le (one_le_pow₀ (by norm_num))
  have hrad_pos (k : ℕ) : 0 < rad k := hR₀.trans_le (hrad_ge k)
  have hex_k (k : ℕ) := exists_optimalBallTilt_direction hv x (hrad_pos k)
  choose dir hdir_unit hdir_opt _ _ using hex_k
  have hdir_tilt (k : ℕ) : ballTiltIntegral v x (dir k) (rad k) ≤
      B * ((rad k) ^ m / (rad k) ^ 2) := by
    apply hunnorm (hrad_pos k)
    rw [← hdir_opt k]
    exact htilt (rad k) (hrad_ge k)
  let Q : ℕ → Space (m + 1) →L[ℝ] Space (m + 1) := fun k ↦ lineProjection (dir k)
  have hQ_step (k : ℕ) : ‖Q (k + 1) - Q k‖ ≤ C_step / rad k := by
    rw [norm_sub_rev]
    have hr2 : rad (k + 1) = 2 * rad k := by dsimp only [rad]; rw [pow_succ']; ring
    exact norm_lineProjection_sub_le_of_adjacent_scales hv hc hB (hrad_pos k)
      (by linarith [hrad_pos k]) (by linarith) (hdir_unit k) (hdir_unit (k + 1))
      (hkin (rad k) (hrad_ge k)).1 (hdir_tilt k) (hdir_tilt (k + 1))
  have hQ_span (k N : ℕ) :
      ‖Q (k + N) - Q k‖ ≤ (2 - 2 * (1 / 2 : ℝ) ^ N) * (C_step / rad k) := by
    induction N with
    | zero =>
      simp
    | succ N ih =>
      have hstepN : ‖Q (k + N + 1) - Q (k + N)‖ ≤ (1 / 2 : ℝ) ^ N * (C_step / rad k) := by
        refine (hQ_step (k + N)).trans_eq ?_
        dsimp only [rad]
        rw [pow_add, one_div_pow]
        field_simp [hR₀.ne']
      calc
        ‖Q (k + N + 1) - Q k‖
          ≤ ‖Q (k + N + 1) - Q (k + N)‖ + ‖Q (k + N) - Q k‖ := by
            simpa only [sub_add_sub_cancel] using
              norm_add_le (Q (k + N + 1) - Q (k + N)) (Q (k + N) - Q k)
        _ ≤ (1 / 2 : ℝ) ^ N * (C_step / rad k) +
            (2 - 2 * (1 / 2 : ℝ) ^ N) * (C_step / rad k) := add_le_add hstepN ih
        _ = (2 - 2 * (1 / 2 : ℝ) ^ (N + 1)) * (C_step / rad k) := by
            rw [pow_succ']; ring
  have hQ_tail_fin (k N : ℕ) : ‖Q (k + N) - Q k‖ ≤ 2 * (C_step / rad k) := by
    refine (hQ_span k N).trans ?_
    apply mul_le_mul_of_nonneg_right _ (div_nonneg hC_step (hrad_pos k).le)
    have hp : 0 ≤ (1 / 2 : ℝ) ^ N := by positivity
    linarith
  have hQ_cauchy : CauchySeq Q := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    have hlim0 : Tendsto (fun k : ℕ ↦ 2 * (C_step / ((2 : ℝ) ^ k * R₀))) atTop (𝓝 0) := by
      have heq : (fun k : ℕ ↦ 2 * (C_step / ((2 : ℝ) ^ k * R₀))) =
          fun k : ℕ ↦ (2 * C_step / R₀) * (1 / 2 : ℝ) ^ k := by
        funext k
        rw [one_div_pow]
        field_simp [hR₀.ne']
      rw [heq]
      simpa only [mul_zero] using
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by norm_num : (1 / 2 : ℝ) < 1)).const_mul
          (2 * C_step / R₀)
    obtain ⟨K, hK⟩ := (hlim0.eventually_lt_const (half_pos hε)).exists
    refine ⟨K, fun i hi j hj ↦ ?_⟩
    have hiK : ‖Q i - Q K‖ < ε / 2 := by
      obtain ⟨N, rfl⟩ := Nat.exists_eq_add_of_le hi
      exact (hQ_tail_fin K N).trans_lt hK
    have hjK : ‖Q j - Q K‖ < ε / 2 := by
      obtain ⟨N, rfl⟩ := Nat.exists_eq_add_of_le hj
      exact (hQ_tail_fin K N).trans_lt hK
    rw [dist_eq_norm]
    have htri : ‖Q i - Q j‖ ≤ ‖Q i - Q K‖ + ‖Q j - Q K‖ := by
      rw [norm_sub_rev (Q j) (Q K)]
      simpa only [sub_add_sub_cancel] using norm_add_le (Q i - Q K) (Q K - Q j)
    linarith
  obtain ⟨e_x, he_xS, φ, hφ_mono, hφ_lim⟩ :=
    (isCompact_sphere (0 : Space (m + 1)) 1).tendsto_subseq
      fun k ↦ by simpa only [mem_sphere_zero_iff_norm] using hdir_unit k
  have he_x : ‖e_x‖ = 1 := by simpa only [mem_sphere_zero_iff_norm] using he_xS
  have hQ_subseq : Tendsto (Q ∘ φ) atTop (𝓝 (lineProjection e_x)) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hinner : Tendsto (fun j ↦ 1 - inner ℝ (dir (φ j)) e_x ^ 2) atTop (𝓝 0) := by
      have ht := (hφ_lim.inner (𝕜 := ℝ) (tendsto_const_nhds (x := e_x))).pow 2
      simp only [real_inner_self_eq_norm_sq, he_x, one_pow] at ht
      simpa only [sub_self, Function.comp_apply] using (tendsto_const_nhds (x := (1 : ℝ))).sub ht
    filter_upwards [hinner.eventually_lt_const (sq_pos_of_pos hε)] with j hj
    rw [dist_eq_norm, Function.comp_apply]
    have hsq : ‖lineProjection (dir (φ j)) - lineProjection e_x‖ ^ 2 < ε ^ 2 := by
      rw [norm_lineProjection_sub_sq (hdir_unit (φ j)) he_x]
      exact hj
    exact (sq_lt_sq₀ (norm_nonneg _) hε.le).mp hsq
  obtain ⟨Q_lim, hQ_tendsto⟩ := cauchySeq_tendsto_of_complete hQ_cauchy
  have hQ_eq : Q_lim = lineProjection e_x :=
    tendsto_nhds_unique (hQ_tendsto.comp hφ_mono.tendsto_atTop) hQ_subseq
  rw [hQ_eq] at hQ_tendsto
  have hQ_tail (k : ℕ) : ‖lineProjection e_x - Q k‖ ≤ 2 * (C_step / rad k) := by
    have hshift : Tendsto (fun N : ℕ ↦ ‖Q (N + k) - Q k‖) atTop
        (𝓝 ‖lineProjection e_x - Q k‖) := by
      have hk_tend : Tendsto (fun N : ℕ ↦ Q (N + k)) atTop (𝓝 (lineProjection e_x)) :=
        hQ_tendsto.comp (tendsto_add_atTop_nat k)
      exact (hk_tend.sub_const (Q k)).norm
    exact le_of_tendsto' hshift fun N ↦ by simpa only [Nat.add_comm N k] using hQ_tail_fin k N
  have hproj_bound : ∀ r, R₀ ≤ r → ∀ e : Space (m + 1), ‖e‖ = 1 →
      r ^ (-(m : ℤ)) * ballTiltIntegral v x e r ≤ B / r ^ 2 →
      ‖lineProjection e - lineProjection e_x‖ ≤ limitingProjectionConst m c_kin B / r := by
    intro r hr e he het
    have hr0 : 0 < r := hR₀.trans_le hr
    have hex_n : ∃ n : ℕ, r < rad (n + 1) := by
      refine ⟨⌊r / R₀⌋₊, ?_⟩
      dsimp only [rad]
      rw [← div_lt_iff₀ hR₀]
      have h1 : r / R₀ < (⌊r / R₀⌋₊ + 1 : ℕ) := by
        simpa only [Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one (r / R₀)
      have h2 : ((⌊r / R₀⌋₊ + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (⌊r / R₀⌋₊ + 1) := by
        exact_mod_cast (Nat.lt_pow_self (by norm_num : 1 < 2)).le
      exact h1.trans_le h2
    classical
    let k : ℕ := Nat.find hex_n
    have hk_up : r ≤ 2 * rad k := by
      have hh := (Nat.find_spec hex_n).le
      dsimp only [rad] at hh ⊢
      linarith [show (2 : ℝ) ^ (k + 1) * R₀ = 2 * ((2 : ℝ) ^ k * R₀) by rw [pow_succ']; ring]
    have hk_low : rad k ≤ r := by
      cases hk_eq : k with
      | zero =>
        simpa only [rad, pow_zero, one_mul] using hr
      | succ k' =>
        have hlt : k' < k := by omega
        have hnot := Nat.find_min hex_n hlt
        exact not_lt.mp hnot
    have hadj : ‖Q k - lineProjection e‖ ≤ C_step / rad k :=
      norm_lineProjection_sub_le_of_adjacent_scales hv hc hB (hrad_pos k) hk_low hk_up
        (hdir_unit k) he (hkin (rad k) (hrad_ge k)).1 (hdir_tilt k) (hunnorm hr0 het)
    have hrad_inv : C_step / rad k ≤ 2 * C_step / r := by
      rw [div_le_div_iff₀ (hrad_pos k) hr0]
      nlinarith
    calc
      ‖lineProjection e - lineProjection e_x‖
        ≤ ‖lineProjection e - Q k‖ + ‖Q k - lineProjection e_x‖ := by
          simpa only [sub_add_sub_cancel] using
            norm_add_le (lineProjection e - Q k) (Q k - lineProjection e_x)
      _ = ‖Q k - lineProjection e‖ + ‖lineProjection e_x - Q k‖ := by
          rw [norm_sub_rev (lineProjection e) (Q k), norm_sub_rev (Q k) (lineProjection e_x)]
      _ ≤ C_step / rad k + 2 * (C_step / rad k) := add_le_add hadj (hQ_tail k)
      _ = 3 * (C_step / rad k) := by ring
      _ ≤ 3 * (2 * C_step / r) := mul_le_mul_of_nonneg_left hrad_inv (by norm_num)
      _ = limitingProjectionConst m c_kin B / r := by
          unfold limitingProjectionConst
          dsimp only [C_step]
          ring
  refine ⟨e_x, he_x, ?_, hproj_bound⟩
  intro r hr
  have hr0 : 0 < r := hR₀.trans_le hr
  obtain ⟨e_r, he_r, hopt_r, _, _⟩ := exists_optimalBallTilt_direction hv x hr0
  have het_r : r ^ (-(m : ℤ)) * ballTiltIntegral v x e_r r ≤ B / r ^ 2 := by
    rw [← hopt_r]
    exact htilt r hr
  have htr : ballTiltIntegral v x e_r r ≤ B * (r ^ m / r ^ 2) := hunnorm hr0 het_r
  have hpr : ‖lineProjection e_r - lineProjection e_x‖ ≤
      limitingProjectionConst m c_kin B / r := hproj_bound r hr e_r he_r het_r
  have hpr_sq : ‖lineProjection e_r - lineProjection e_x‖ ^ 2 ≤
      limitingProjectionConst m c_kin B ^ 2 / r ^ 2 := by
    rw [← div_pow]
    exact (sq_le_sq₀ (norm_nonneg _)
      (div_nonneg (limitingProjectionConst_nonneg m c_kin B) hr0.le)).mpr hpr
  have hkin_up : (∫ y in closedBall x r, ‖gradient v y‖ ^ 2) ≤ C_kin * r ^ m :=
    (hkin r hr).2
  have _ := hC
  calc
    ballTiltIntegral v x e_x r
      ≤ 2 * ballTiltIntegral v x e_r r +
          2 * ‖lineProjection e_r - lineProjection e_x‖ ^ 2 *
            ∫ y in closedBall x r, ‖gradient v y‖ ^ 2 :=
        ballTiltIntegral_le_two_mul_add_proj_sq hv he_x he_r x r
    _ ≤ 2 * (B * (r ^ m / r ^ 2)) +
          2 * (limitingProjectionConst m c_kin B ^ 2 / r ^ 2) * (C_kin * r ^ m) := by
        refine add_le_add (mul_le_mul_of_nonneg_left htr (by norm_num)) ?_
        exact mul_le_mul (mul_le_mul_of_nonneg_left hpr_sq (by norm_num)) hkin_up
          (integral_nonneg fun _ ↦ sq_nonneg _) (by positivity)
    _ = limitingTiltConst m c_kin C_kin B * (r ^ m / r ^ 2) := by
        unfold limitingTiltConst
        ring

/-- Coincidence of limiting line projections across two centers (I7): if `e_x` and `e_y` are unit
directions satisfying the `r ^ m / r ^ 2` tilt bounds at centers `x` and `y` respectively, and `x`
satisfies the `r ^ m` kinetic lower bound, then `lineProjection e_x = lineProjection e_y` (hence
`e_y = e_x ∨ e_y = -e_x`). The constants and starting radii at `x` and `y` may differ. -/
theorem limiting_lineProjection_eq_of_two_centers {m : ℕ} {v : Space (m + 1) → ℝ}
    (hv : LocallyLipschitz v) {x y e_x e_y : Space (m + 1)}
    {R_x R_y c_x D_x D_y : ℝ}
    (hR_x : 0 < R_x) (hR_y : 0 < R_y) (hc_x : 0 < c_x)
    (he_x : ‖e_x‖ = 1) (he_y : ‖e_y‖ = 1)
    (hx_kin : ∀ r, R_x ≤ r → c_x * r ^ m ≤ ∫ z in closedBall x r, ‖gradient v z‖ ^ 2)
    (hx_tilt : ∀ r, R_x ≤ r → ballTiltIntegral v x e_x r ≤ D_x * (r ^ m / r ^ 2))
    (hy_tilt : ∀ r, R_y ≤ r → ballTiltIntegral v y e_y r ≤ D_y * (r ^ m / r ^ 2)) :
    lineProjection e_x = lineProjection e_y ∧ (e_y = e_x ∨ e_y = -e_x) := by
  let R_base : ℝ := max (max R_x R_y) (dist x y)
  let D₁ : ℝ := max D_x 0
  let D₂ : ℝ := max D_y 0
  let C_xy : ℝ := (2 * D₁ + 2 * (2 : ℝ) ^ m * D₂) / c_x
  have hbound (k : ℕ) : ‖lineProjection e_x - lineProjection e_y‖ ^ 2 ≤
      C_xy / (R_base + (k + 1 : ℝ)) ^ 2 := by
    let r : ℝ := R_base + (k + 1 : ℝ)
    have hr_base : R_base ≤ r := le_add_of_nonneg_right (by positivity)
    have hr_x : R_x ≤ r := ((le_max_left R_x R_y).trans (le_max_left _ _)).trans hr_base
    have hr_y : R_y ≤ r := ((le_max_right R_x R_y).trans (le_max_left _ _)).trans hr_base
    have hdist : dist x y ≤ r := (le_max_right _ _).trans hr_base
    have hr0 : 0 < r := hR_x.trans_le hr_x
    have h2r_y : R_y ≤ 2 * r := by
      have _ := hR_y
      linarith
    have hsub : closedBall x r ⊆ closedBall y (2 * r) := by
      intro z hz
      rw [mem_closedBall] at hz ⊢
      linarith [dist_triangle z x y]
    have htx : ballTiltIntegral v x e_x r ≤ D₁ * (r ^ m / r ^ 2) :=
      (hx_tilt r hr_x).trans
        (mul_le_mul_of_nonneg_right (le_max_left D_x 0) (by positivity))
    have h2r_ratio : (2 * r) ^ m / (2 * r) ^ 2 ≤ (2 : ℝ) ^ m * (r ^ m / r ^ 2) := by
      rw [mul_pow 2 r m]
      have hsq_le : r ^ 2 ≤ (2 * r) ^ 2 := by nlinarith
      calc
        ((2 : ℝ) ^ m * r ^ m) / (2 * r) ^ 2
          ≤ ((2 : ℝ) ^ m * r ^ m) / r ^ 2 :=
            div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hr0) hsq_le
        _ = (2 : ℝ) ^ m * (r ^ m / r ^ 2) := mul_div_assoc _ _ _
    have hty : ballTiltIntegral v x e_y r ≤ D₂ * ((2 : ℝ) ^ m * (r ^ m / r ^ 2)) := by
      calc
        ballTiltIntegral v x e_y r
          ≤ ballTiltIntegral v y e_y (2 * r) :=
            ballTiltIntegral_mono_closedBall hv he_y hsub
        _ ≤ D_y * ((2 * r) ^ m / (2 * r) ^ 2) := hy_tilt (2 * r) h2r_y
        _ ≤ D₂ * ((2 * r) ^ m / (2 * r) ^ 2) :=
            mul_le_mul_of_nonneg_right (le_max_left D_y 0) (by positivity)
        _ ≤ D₂ * ((2 : ℝ) ^ m * (r ^ m / r ^ 2)) :=
            mul_le_mul_of_nonneg_left h2r_ratio (le_max_right D_y 0)
    have hcomp := norm_lineProjection_sub_sq_mul_kinetic_le hv he_x he_y x r
    have hrm_pos : 0 < r ^ m := pow_pos hr0 m
    have hcr_pos : 0 < c_x * r ^ m := mul_pos hc_x hrm_pos
    have hmul : ‖lineProjection e_x - lineProjection e_y‖ ^ 2 * (c_x * r ^ m) ≤
        (2 * D₁ + 2 * (2 : ℝ) ^ m * D₂) * (r ^ m / r ^ 2) := by
      calc
        ‖lineProjection e_x - lineProjection e_y‖ ^ 2 * (c_x * r ^ m)
          ≤ ‖lineProjection e_x - lineProjection e_y‖ ^ 2 *
              (∫ z in closedBall x r, ‖gradient v z‖ ^ 2) :=
            mul_le_mul_of_nonneg_left (hx_kin r hr_x) (sq_nonneg _)
        _ ≤ 2 * ballTiltIntegral v x e_x r + 2 * ballTiltIntegral v x e_y r := hcomp
        _ ≤ 2 * (D₁ * (r ^ m / r ^ 2)) + 2 * (D₂ * ((2 : ℝ) ^ m * (r ^ m / r ^ 2))) := by
            linarith
        _ = (2 * D₁ + 2 * (2 : ℝ) ^ m * D₂) * (r ^ m / r ^ 2) := by ring
    refine ((le_div_iff₀ hcr_pos).mpr hmul).trans_eq ?_
    change ((2 * D₁ + 2 * (2 : ℝ) ^ m * D₂) * (r ^ m / r ^ 2)) / (c_x * r ^ m) = C_xy / r ^ 2
    dsimp only [C_xy]
    field_simp [hc_x.ne', hr0.ne', hrm_pos.ne']
  have hlim : Tendsto (fun k : ℕ ↦ C_xy / (R_base + (k + 1 : ℝ)) ^ 2) atTop (𝓝 0) := by
    have hbase0 : 0 ≤ R_base := (hR_x.le.trans (le_max_left R_x R_y)).trans (le_max_left _ _)
    have hmaj : Tendsto (fun k : ℕ ↦ C_xy * (1 / (k + 1 : ℝ)) ^ 2) atTop (𝓝 0) := by
      simpa only [zero_pow (by norm_num : 2 ≠ 0), mul_zero] using
        (tendsto_one_div_add_atTop_nhds_zero_nat.pow 2).const_mul C_xy
    apply squeeze_zero (fun k ↦ by dsimp only [C_xy, D₁, D₂]; positivity) _ hmaj
    intro k
    have hk_le : (k + 1 : ℝ) ^ 2 ≤ (R_base + (k + 1 : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (le_add_of_nonneg_left hbase0) 2
    calc
      C_xy / (R_base + (k + 1 : ℝ)) ^ 2
        ≤ C_xy / (k + 1 : ℝ) ^ 2 :=
          div_le_div_of_nonneg_left (by dsimp only [C_xy, D₁, D₂]; positivity)
            (by positivity) hk_le
      _ = C_xy * (1 / (k + 1 : ℝ)) ^ 2 := by
          have hk0 : (k + 1 : ℝ) ≠ 0 := by positivity
          field_simp [hk0]
  have hsq0 : ‖lineProjection e_x - lineProjection e_y‖ ^ 2 ≤ 0 := ge_of_tendsto' hlim hbound
  have hnorm0 : ‖lineProjection e_x - lineProjection e_y‖ = 0 :=
    sq_eq_zero_iff.mp (le_antisymm hsq0 (sq_nonneg _))
  have heq : lineProjection e_x = lineProjection e_y := sub_eq_zero.mp (norm_eq_zero.mp hnorm0)
  exact ⟨heq, (lineProjection_eq_iff_of_unit he_x he_y).mp heq⟩

/-- Common unoriented direction across an arbitrary family of centers `S` (combining I5–I7):
if all `x ∈ S` satisfy the kinetic and tilt hypotheses with `(R₀, c_kin, C_kin, B)`, there exists
a single unit vector `e₀` satisfying the explicit limiting-direction tilt and projection bounds
simultaneously at every center `x ∈ S`. -/
theorem exists_common_limiting_lineProjection {m : ℕ} {v : Space (m + 1) → ℝ}
    (hv : LocallyLipschitz v) (S : Set (Space (m + 1)))
    {R₀ c_kin C_kin B : ℝ} (hR₀ : 0 < R₀) (hc : 0 < c_kin) (hC : 0 < C_kin) (hB : 0 ≤ B)
    (hkin : ∀ x ∈ S, ∀ r, R₀ ≤ r →
      c_kin * r ^ m ≤ (∫ y in closedBall x r, ‖gradient v y‖ ^ 2) ∧
        (∫ y in closedBall x r, ‖gradient v y‖ ^ 2) ≤ C_kin * r ^ m)
    (htilt : ∀ x ∈ S, ∀ r, R₀ ≤ r → optimalBallTilt v x r ≤ B / r ^ 2) :
    ∃ e₀ : Space (m + 1), ‖e₀‖ = 1 ∧
      ∀ x ∈ S,
        (∀ r, R₀ ≤ r →
          ballTiltIntegral v x e₀ r ≤ limitingTiltConst m c_kin C_kin B * (r ^ m / r ^ 2)) ∧
        (∀ r, R₀ ≤ r → ∀ e : Space (m + 1), ‖e‖ = 1 →
          r ^ (-(m : ℤ)) * ballTiltIntegral v x e r ≤ B / r ^ 2 →
          ‖lineProjection e - lineProjection e₀‖ ≤ limitingProjectionConst m c_kin B / r) := by
  by_cases hS : S.Nonempty
  · obtain ⟨x₀, hx₀⟩ := hS
    obtain ⟨e₀, he₀, hx₀_tilt, _⟩ :=
      exists_limiting_lineProjection hv x₀ hR₀ hc hC hB (hkin x₀ hx₀) (htilt x₀ hx₀)
    refine ⟨e₀, he₀, fun x hx ↦ ?_⟩
    obtain ⟨e_x, he_x, hx_tilt, hx_proj⟩ :=
      exists_limiting_lineProjection hv x hR₀ hc hC hB (hkin x hx) (htilt x hx)
    obtain ⟨hQ_eq, hsign⟩ := limiting_lineProjection_eq_of_two_centers hv hR₀ hR₀ hc
      he₀ he_x (fun r hr ↦ (hkin x₀ hx₀ r hr).1) hx₀_tilt hx_tilt
    refine ⟨fun r hr ↦ ?_, fun r hr e he het ↦ ?_⟩
    · rcases hsign with rfl | rfl
      · exact hx_tilt r hr
      · simpa only [ballTiltIntegral_neg] using hx_tilt r hr
    · rw [hQ_eq]
      exact hx_proj r hr e he het
  · refine ⟨verticalDirection m, norm_verticalDirection m, fun x hx ↦ ?_⟩
    exact False.elim (hS ⟨x, hx⟩)

end SerrinEpigraph
