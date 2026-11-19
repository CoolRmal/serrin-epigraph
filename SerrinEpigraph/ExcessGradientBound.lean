module

public import SerrinEpigraph.ExcessLipschitzApprox

/-!
# The Dirichlet energy of the Lipschitz approximation (`GR9.3`)

Let `f` be a Lipschitz approximation of the signed height that agrees with it at every good
Lebesgue point (`exists_lipschitz_approx`). At almost every good point `y`, where `f` is
differentiable, the good set has density one and the excess measure has density `θ(y)`
(Besicovitch differentiation), the oscillation estimates of `ExcessOscillation` at the scales
`ρ → 0` give

`(1/2) 4^(-m) |∇f(y)| ≤ 2^(3m+3) √(2 θ(y) (1 + θ(y)))`

(`norm_fderiv_le_of_density`). Integrating over the good set (`∫_G θ ≤ ε(G)`) and using the
Lipschitz bound on the bad set (`|B \ G| ≤ 4^m e/κ`) yields `GR9.3`:
`∫_{B_{3/2}} |∇f|² ≤ C e` (`SlabTrappedRepresentation.integral_norm_fderiv_sq_le`).
No area formula for the graph of `f` is used.
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory InnerProductSpace Filter
open scoped Topology ENNReal CompactlySupported NNReal

namespace SerrinEpigraph

/-! ### 1. Linear forms on balls -/

/-- A linear form is large on a definite fraction of every ball:
`∫_{B_ρ(y)} |L(z - y)| ≥ (|L| ρ / 2) 4^(-d) |B_ρ(y)|`. -/
theorem integral_abs_apply_sub_ge {d : ℕ} (L : Space d →L[ℝ] ℝ) (y : Space d) {ρ : ℝ}
    (hρ : 0 < ρ) :
    ‖L‖ * ρ / 2 * ((1 / 4) ^ d * volume.real (ball y ρ)) ≤ ∫ z in ball y ρ, |L (z - y)| := by
  have hcont : Continuous fun z ↦ |L (z - y)| :=
    (L.continuous.comp (continuous_id.sub continuous_const)).abs
  have hint : IntegrableOn (fun z ↦ |L (z - y)|) (ball y ρ) :=
    (hcont.continuousOn.integrableOn_compact (isCompact_closedBall y ρ)).mono_set
      ball_subset_closedBall
  have hint0 : 0 ≤ ∫ z in ball y ρ, |L (z - y)| := integral_nonneg fun _ ↦ abs_nonneg _
  by_cases hL : ‖L‖ = 0
  · rw [hL, zero_mul, zero_div, zero_mul]
    exact hint0
  set w : Space d := (InnerProductSpace.toDual ℝ (Space d)).symm L with hw_def
  have hw : ‖w‖ = ‖L‖ := LinearIsometryEquiv.norm_map _ _
  have hLw : ∀ v, L v = inner ℝ w v := fun v ↦ InnerProductSpace.toDual_symm_apply.symm
  have hwpos : 0 < ‖w‖ := by rw [hw]; exact lt_of_le_of_ne (norm_nonneg _) (Ne.symm hL)
  set u : Space d := ‖w‖⁻¹ • w with hu_def
  have hLu : L u = ‖L‖ := by
    rw [hLw, hu_def, inner_smul_right, real_inner_self_eq_norm_sq, ← hw]
    field_simp
  have hu : ‖u‖ = 1 := by
    rw [hu_def, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hwpos.ne']
  set c : Space d := y + (3 * ρ / 4) • u with hc_def
  have hsub : ball c (ρ / 4) ⊆ ball y ρ := by
    intro z hz
    rw [mem_ball] at hz ⊢
    have hcy : dist c y = 3 * ρ / 4 := by
      rw [hc_def, dist_eq_norm, add_sub_cancel_left, norm_smul, hu, mul_one,
        Real.norm_of_nonneg (by positivity)]
    calc
      dist z y ≤ dist z c + dist c y := dist_triangle _ _ _
      _ < ρ := by linarith
  have hlow : ∀ z ∈ ball c (ρ / 4), ‖L‖ * ρ / 2 ≤ |L (z - y)| := by
    intro z hz
    have hzc : ‖z - c‖ < ρ / 4 := by rw [← dist_eq_norm]; exact hz
    have hsplit : z - y = (z - c) + (3 * ρ / 4) • u := by
      rw [hc_def]
      abel
    have h1 : |L (z - c)| ≤ ‖L‖ * ‖z - c‖ := by
      rw [← Real.norm_eq_abs]
      exact L.le_opNorm _
    have h2 : ‖L‖ * ‖z - c‖ ≤ ‖L‖ * (ρ / 4) :=
      mul_le_mul_of_nonneg_left hzc.le (norm_nonneg _)
    have h3 := (abs_le.mp (h1.trans h2)).1
    rw [hsplit, map_add, map_smul, hLu, smul_eq_mul]
    have hpos : 0 ≤ L (z - c) + 3 * ρ / 4 * ‖L‖ := by nlinarith [norm_nonneg L]
    rw [abs_of_nonneg hpos]
    nlinarith [norm_nonneg L]
  have hvol : volume.real (ball c (ρ / 4)) = (1 / 4) ^ d * volume.real (ball y ρ) := by
    rw [show ρ / 4 = 1 / 4 * ρ by ring]
    exact volume_real_ball_mul c y hρ (by norm_num)
  calc
    ‖L‖ * ρ / 2 * ((1 / 4) ^ d * volume.real (ball y ρ)) = ∫ z in ball c (ρ / 4), ‖L‖ * ρ / 2 := by
      rw [setIntegral_const, smul_eq_mul, hvol]
      ring
    _ ≤ ∫ z in ball c (ρ / 4), |L (z - y)| :=
      setIntegral_mono_on (integrableOn_const measure_ball_ne_top) (hint.mono_set hsub)
        measurableSet_ball hlow
    _ ≤ ∫ z in ball y ρ, |L (z - y)| :=
      setIntegral_mono_set hint (Eventually.of_forall fun _ ↦ abs_nonneg _) hsub.eventuallyLE

/-! ### 2. The pointwise gradient bound -/

namespace SlabTrappedRepresentation

variable {m : ℕ} {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))}
  {E : Set (Space (m + 1))} {U : Set (Space m)} {H H' : ℝ} {μ : Measure (Space (m + 1))}
  {ν : Space (m + 1) → Space (m + 1)}

/-- **Pointwise gradient bound** (`GR9.3`): at a good Lebesgue point `y` where the Lipschitz
approximation is differentiable, the good set has density one, and the excess measure has
density `θ`, one has `(1/2) 4^(-m) |∇f(y)| ≤ 2^(3m+3) √(2θ(1+θ))`. -/
theorem norm_fderiv_le_of_density
    (hS : SlabTrappedRepresentation b E U H H' μ ν) (hU2 : ball (0 : Space m) 2 ⊆ U)
    {κ : ℝ} {f : Space m → ℝ}
    (hfg : ∀ z ∈ goodLebesgueSet E H (projectedExcessMeasure μ ν) κ,
      f z = columnSignedHeight E H z)
    {y : Space m} (hy : y ∈ goodLebesgueSet E H (projectedExcessMeasure μ ν) κ)
    (hdiff : DifferentiableAt ℝ f y)
    (hdens : Tendsto (fun r ↦ volume (normalizedGoodSet (projectedExcessMeasure μ ν) κ ∩
      closedBall y r) / volume (closedBall y r)) (𝓝[>] 0) (𝓝 1))
    {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hrn : Tendsto (fun r ↦ projectedExcessMeasure μ ν (closedBall y r) /
      volume (closedBall y r)) (𝓝[>] 0) (𝓝 (ENNReal.ofReal θ))) :
    1 / 2 * (1 / 4) ^ m * ‖fderiv ℝ f y‖ ≤ 2 ^ (3 * m + 3) * Real.sqrt (2 * θ * (1 + θ)) := by
  set g := columnSignedHeight E H with hg_def
  set ε := projectedExcessMeasure μ ν with hε_def
  set G := normalizedGoodSet ε κ with hG_def
  set L := fderiv ℝ f y with hL_def
  set ℓ := ‖L‖ with hℓ_def
  have hℓ0 : 0 ≤ ℓ := norm_nonneg _
  have := hS.isFiniteMeasure_excess
  have hGm : MeasurableSet G := measurableSet_excessGoodSet ε measurableSet_ball _ _
  have hy0 : dist y 0 < 3 / 2 := hy.1.1
  have hfy : f y = g y := hfg y hy
  have hint : ∀ r, IntegrableOn g (ball y r) := fun r ↦
    integrableOn_columnSignedHeight_ball hS.measurableSet hS.pos.le y r
  -- Step A: the estimate up to `κ' > θ` and an error `2η`.
  have hA : ∀ κ' : ℝ, θ < κ' → ∀ η : ℝ, 0 < η →
      1 / 2 * (1 / 4) ^ m * ℓ ≤ 2 ^ (3 * m + 3) * Real.sqrt (2 * κ' * (1 + κ')) + 2 * η := by
    intro κ' hκ' η hη
    have hκ'0 : 0 < κ' := lt_of_le_of_lt hθ0 hκ'
    set A := Real.sqrt (2 * κ' * (1 + κ')) with hA_def
    have hA0 : 0 ≤ A := Real.sqrt_nonneg _
    -- (a) excess density at small scales
    obtain ⟨r₁, hr₁, hr₁s⟩ : ∃ r₁ > 0, ∀ r ∈ Ioo (0 : ℝ) r₁,
        ε (ball y r) ≤ ENNReal.ofReal κ' * volume (ball y r) := by
      have hlt : ENNReal.ofReal θ < ENNReal.ofReal κ' :=
        (ENNReal.ofReal_lt_ofReal_iff hκ'0).mpr hκ'
      obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp
        (hrn.eventually (gt_mem_nhds hlt))
      refine ⟨u, hu, fun r hr ↦ ?_⟩
      have hratio : ε (closedBall y r) / volume (closedBall y r) < ENNReal.ofReal κ' := hsub hr
      have hvpos : volume (closedBall y r) ≠ 0 := (measure_closedBall_pos volume y hr.1).ne'
      have hvfin : volume (closedBall y r) ≠ ⊤ := measure_closedBall_lt_top.ne
      have h1 : ε (closedBall y r) < ENNReal.ofReal κ' * volume (closedBall y r) :=
        (ENNReal.div_lt_iff (Or.inl hvpos) (Or.inl hvfin)).mp hratio
      calc
        ε (ball y r) ≤ ε (closedBall y r) := measure_mono ball_subset_closedBall
        _ ≤ ENNReal.ofReal κ' * volume (closedBall y r) := h1.le
        _ = ENNReal.ofReal κ' * volume (ball y r) := by rw [volume_closedBall_eq_ball y hr.1]
    -- (b) differentiability
    obtain ⟨δ, hδ, hδs⟩ : ∃ δ > 0, ∀ z ∈ ball y δ, |f z - f y - L (z - y)| ≤ η * ‖z - y‖ := by
      have hev := hdiff.hasFDerivAt.isLittleO.def hη
      obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
      exact ⟨δ, hδ, fun z hz ↦ by simpa [Real.norm_eq_abs] using hball z hz⟩
    -- (c) density of the good set
    set η' := η / (ℓ + 1) with hη'_def
    have hη' : 0 < η' := by positivity
    obtain ⟨r₂, hr₂, hr₂s⟩ : ∃ r₂ > 0, ∀ r ∈ Ioo (0 : ℝ) r₂,
        volume.real (ball y r \ G) ≤ η' * volume.real (ball y r) := by
      have hlt : ENNReal.ofReal (1 - η') < 1 := by
        rw [← ENNReal.ofReal_one]
        exact (ENNReal.ofReal_lt_ofReal_iff one_pos).mpr (by linarith)
      obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp
        (hdens.eventually (lt_mem_nhds hlt))
      refine ⟨u, hu, fun r hr ↦ ?_⟩
      have hratio : ENNReal.ofReal (1 - η') < volume (G ∩ closedBall y r) /
          volume (closedBall y r) := hsub hr
      have h1 : ENNReal.ofReal (1 - η') * volume (closedBall y r) <
          volume (G ∩ closedBall y r) := ENNReal.mul_lt_of_lt_div hratio
      have h2 : max (1 - η') 0 * volume.real (closedBall y r) ≤
          volume.real (G ∩ closedBall y r) := by
        have h3 := ENNReal.toReal_mono (measure_ne_top_of_subset inter_subset_right
          measure_closedBall_lt_top.ne) h1.le
        rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal', ← Measure.real] at h3
      have hsplit := measureReal_inter_add_sdiff (μ := volume) (s := closedBall y r) hGm
        measure_closedBall_lt_top.ne
      have hcomm : volume.real (closedBall y r ∩ G) = volume.real (G ∩ closedBall y r) := by
        rw [inter_comm]
      have hcb : volume.real (closedBall y r) = volume.real (ball y r) := by
        rw [Measure.real, Measure.real, volume_closedBall_eq_ball y hr.1]
      have hmono : volume.real (ball y r \ G) ≤ volume.real (closedBall y r \ G) :=
        measureReal_mono (sdiff_subset_sdiff ball_subset_closedBall subset_rfl)
          (measure_ne_top_of_subset sdiff_subset measure_closedBall_lt_top.ne)
      have hmax : (1 - η') * volume.real (closedBall y r) ≤
          max (1 - η') 0 * volume.real (closedBall y r) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) measureReal_nonneg
      rw [← hcb]
      linarith
    -- (d) the scale
    set M := min (min (r₁ / 2) δ) (min r₂ (1 / 16)) with hM_def
    have hM0 : 0 < M := by positivity
    have hM1 : M ≤ r₁ / 2 := (min_le_left _ _).trans (min_le_left _ _)
    have hM2 : M ≤ δ := (min_le_left _ _).trans (min_le_right _ _)
    have hM3 : M ≤ r₂ := (min_le_right _ _).trans (min_le_left _ _)
    have hM4 : M ≤ 1 / 16 := (min_le_right _ _).trans (min_le_right _ _)
    set ρ := M / 2 with hρ_def
    have hρ : 0 < ρ := by positivity
    have hρ1 : 2 * ρ < r₁ := by linarith
    have hρδ : ρ < δ := by linarith
    have hρ2 : ρ < r₂ := by linarith
    have hρ16 : ρ < 1 / 16 := by linarith
    -- (e) excess hypotheses
    have hexc' : ∀ s, 0 < s → s ≤ ρ → ε (ball y (2 * s)) ≤
        ENNReal.ofReal κ' * volume (ball y (2 * s)) := fun s hs hsρ ↦
      hr₁s (2 * s) ⟨by positivity, by linarith⟩
    have hball2 : ball y (2 * ρ) ⊆ U :=
      ((ball_subset_of_mem_normalizedGoodSet hy.1 (by linarith)).trans
        (ball_subset_ball (by norm_num))).trans hU2
    have hpt := hS.abs_sub_average_le_of_excess hρ hκ'0.le hball2 hexc' hy.2
    have hosc := hS.integral_abs_sub_average_le_of_excess hρ hκ'0.le hball2
      (hexc' ρ hρ le_rfl)
    set B := ball y ρ with hB_def
    set gB := ⨍ z in B, g z with hgB_def
    have hBpos : 0 < volume.real B := volume_real_ball_pos y hρ
    -- (h) oscillation around `g y`
    have hgy_int : IntegrableOn (fun z ↦ |g z - g y|) B :=
      ((hint ρ).sub (integrableOn_const measure_ball_ne_top)).abs
    have hgB_int : IntegrableOn (fun z ↦ |g z - gB|) B :=
      ((hint ρ).sub (integrableOn_const measure_ball_ne_top)).abs
    have hosc_y : ∫ z in B, |g z - g y| ≤ 2 ^ (3 * m + 3) * A * ρ * volume.real B := by
      calc
        ∫ z in B, |g z - g y| ≤ ∫ z in B, (|g z - gB| + |gB - g y|) :=
          integral_mono hgy_int (hgB_int.add (integrableOn_const measure_ball_ne_top))
            (fun z ↦ abs_sub_le _ _ _)
        _ = (∫ z in B, |g z - gB|) + |gB - g y| * volume.real B := by
          rw [integral_add hgB_int (integrableOn_const measure_ball_ne_top), setIntegral_const,
            smul_eq_mul, mul_comm]
        _ ≤ 2 ^ (2 * m + 1) * A * ρ * volume.real B +
            2 ^ (3 * m + 2) * A * ρ * volume.real B := by
          rw [abs_sub_comm]
          exact add_le_add hosc (mul_le_mul_of_nonneg_right hpt hBpos.le)
        _ ≤ 2 ^ (3 * m + 3) * A * ρ * volume.real B := by
          have h1 : (2 : ℝ) ^ (2 * m + 1) ≤ 2 ^ (3 * m + 2) :=
            pow_le_pow_right₀ (by norm_num) (by omega)
          have h2 : (2 : ℝ) ^ (3 * m + 3) = 2 ^ (3 * m + 2) * 2 := pow_succ _ _
          have h3 : 0 ≤ A * ρ * volume.real B := by positivity
          nlinarith
    -- (i) the pointwise bound
    have hpoint : ∀ᵐ z ∂(volume.restrict B),
        |L (z - y)| ≤ |g z - g y| + η * ρ + ℓ * ρ * Gᶜ.indicator (fun _ ↦ (1 : ℝ)) z := by
      have hae := ae_restrict_of_ae (s := B) (ae_mem_goodLebesgueSet hS.measurableSet hS.pos.le
        ε κ)
      filter_upwards [hae, ae_restrict_mem measurableSet_ball] with z hzL hzB
      have hzy : ‖z - y‖ ≤ ρ := by
        rw [← dist_eq_norm]
        exact (mem_ball.mp hzB).le
      by_cases hzG : z ∈ G
      · have hfz : f z = g z := hfg z (hzL hzG)
        have hzδ : z ∈ ball y δ := ball_subset_ball hρδ.le hzB
        have h1 := hδs z hzδ
        rw [indicator_of_notMem (show z ∉ Gᶜ from fun h ↦ h hzG), mul_zero, add_zero]
        calc
          |L (z - y)| = |(f z - f y) - (f z - f y - L (z - y))| := by ring_nf
          _ ≤ |f z - f y| + |f z - f y - L (z - y)| := abs_sub _ _
          _ ≤ |g z - g y| + η * ρ := by
            have hA1 : |f z - f y| = |g z - g y| := by rw [hfz, hfy]
            have hA2 : |f z - f y - L (z - y)| ≤ η * ρ :=
              h1.trans (mul_le_mul_of_nonneg_left hzy hη.le)
            linarith
      · rw [indicator_of_mem (show z ∈ Gᶜ from hzG), mul_one]
        have h1 : |L (z - y)| ≤ ℓ * ρ := by
          rw [← Real.norm_eq_abs]
          exact (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left hzy hℓ0)
        have h2 : 0 ≤ |g z - g y| + η * ρ := by positivity
        linarith
    -- (j) integrate
    have hind_int : IntegrableOn (fun z ↦ Gᶜ.indicator (fun _ ↦ (1 : ℝ)) z) B :=
      (integrableOn_const measure_ball_ne_top).indicator hGm.compl
    have hL_int : IntegrableOn (fun z ↦ |L (z - y)|) B :=
      ((L.continuous.comp (continuous_id.sub continuous_const)).abs.continuousOn.integrableOn_compact
        (isCompact_closedBall y ρ)).mono_set ball_subset_closedBall
    have hupper : ∫ z in B, |L (z - y)| ≤
        2 ^ (3 * m + 3) * A * ρ * volume.real B + η * ρ * volume.real B +
          ℓ * ρ * (η' * volume.real B) := by
      have hrhs_int : IntegrableOn (fun z ↦ |g z - g y| + η * ρ +
          ℓ * ρ * Gᶜ.indicator (fun _ ↦ (1 : ℝ)) z) B :=
        (hgy_int.add (integrableOn_const measure_ball_ne_top)).add (hind_int.const_mul _)
      calc
        ∫ z in B, |L (z - y)| ≤ ∫ z in B, (|g z - g y| + η * ρ +
            ℓ * ρ * Gᶜ.indicator (fun _ ↦ (1 : ℝ)) z) :=
          integral_mono_ae hL_int hrhs_int hpoint
        _ = (∫ z in B, |g z - g y|) + η * ρ * volume.real B +
            ℓ * ρ * volume.real (B \ G) := by
          have e1 : ∫ z in B, (|g z - g y| + η * ρ + ℓ * ρ * Gᶜ.indicator (fun _ ↦ (1 : ℝ)) z) =
              (∫ z in B, (|g z - g y| + η * ρ)) +
                ∫ z in B, ℓ * ρ * Gᶜ.indicator (fun _ ↦ (1 : ℝ)) z :=
            integral_add (by exact hgy_int.add (integrableOn_const measure_ball_ne_top))
              (hind_int.const_mul _)
          have e2 : ∫ z in B, (|g z - g y| + η * ρ) =
              (∫ z in B, |g z - g y|) + ∫ z in B, η * ρ :=
            integral_add hgy_int (integrableOn_const measure_ball_ne_top)
          have e3 : ∫ z in B, η * ρ = η * ρ * volume.real B := by
            rw [setIntegral_const, smul_eq_mul, mul_comm]
          have e4 : ∫ z in B, ℓ * ρ * Gᶜ.indicator (fun _ ↦ (1 : ℝ)) z =
              ℓ * ρ * volume.real (B \ G) := by
            rw [integral_const_mul, setIntegral_indicator hGm.compl, setIntegral_const,
              smul_eq_mul, mul_one, ← sdiff_eq]
          rw [e1, e2, e3, e4]
        _ ≤ _ := by
          have hd := hr₂s ρ ⟨hρ, hρ2⟩
          have h1 := mul_le_mul_of_nonneg_left hd (by positivity : 0 ≤ ℓ * ρ)
          linarith [hosc_y]
    -- (k) the lower bound and conclusion
    have hlower := integral_abs_apply_sub_ge L y hρ
    have hineq : 1 / 2 * (1 / 4) ^ m * ℓ * (ρ * volume.real B) ≤
        (2 ^ (3 * m + 3) * A + η + ℓ * η') * (ρ * volume.real B) := by
      have : ‖L‖ * ρ / 2 * ((1 / 4) ^ m * volume.real B) =
          1 / 2 * (1 / 4) ^ m * ℓ * (ρ * volume.real B) := by ring
      linarith
    have hpos : 0 < ρ * volume.real B := mul_pos hρ hBpos
    have hmain := le_of_mul_le_mul_right hineq hpos
    have hℓη : ℓ * η' ≤ η := by
      rw [hη'_def, mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  -- Step B: remove the error `2η`.
  have hB : ∀ κ' : ℝ, θ < κ' →
      1 / 2 * (1 / 4) ^ m * ℓ ≤ 2 ^ (3 * m + 3) * Real.sqrt (2 * κ' * (1 + κ')) := by
    intro κ' hκ'
    refine le_of_forall_pos_le_add fun η hη ↦ ?_
    have h := hA κ' hκ' (η / 2) (by positivity)
    linarith
  -- Step C: let `κ' ↓ θ`.
  have hlim : Tendsto (fun n : ℕ ↦ 2 ^ (3 * m + 3) *
      Real.sqrt (2 * (θ + 1 / ((n : ℝ) + 1)) * (1 + (θ + 1 / ((n : ℝ) + 1))))) atTop
      (𝓝 (2 ^ (3 * m + 3) * Real.sqrt (2 * θ * (1 + θ)))) := by
    have hκn : Tendsto (fun n : ℕ ↦ θ + 1 / ((n : ℝ) + 1)) atTop (𝓝 θ) := by
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add θ
    have hc : Continuous fun t : ℝ ↦ 2 ^ (3 * m + 3) * Real.sqrt (2 * t * (1 + t)) := by
      fun_prop
    exact (hc.tendsto θ).comp hκn
  refine ge_of_tendsto' hlim fun n ↦ hB _ ?_
  have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  linarith

/-! ### 3. The Dirichlet energy (`GR9.3`) -/

/-- The dimensional constant of `GR9.3`. -/
def gradApproxConst (m : ℕ) : ℝ :=
  (2 * 4 ^ m * 2 ^ (3 * m + 3) * 2) ^ 2 + lipschitzApproxConst m ^ 2 * 4 ^ m

/-- **The Dirichlet energy of the Lipschitz approximation** (`GR9.3`): if `e = ε(B_2) ≤ κ ≤ 1`
and `f` is a `C √κ`-Lipschitz function agreeing with the signed height at every good Lebesgue
point, then `∫_{B_{3/2}} |∇f|² ≤ C e` with `C = gradApproxConst m`. -/
theorem integral_norm_fderiv_sq_le
    (hS : SlabTrappedRepresentation b E U H H' μ ν) (hU2 : ball (0 : Space m) 2 ⊆ U)
    {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) {f : Space m → ℝ}
    (hf : LipschitzWith (Real.toNNReal (lipschitzApproxConst m * Real.sqrt κ)) f)
    (hfg : ∀ z ∈ goodLebesgueSet E H (projectedExcessMeasure μ ν) κ,
      f z = columnSignedHeight E H z) :
    ∫ y in ball (0 : Space m) (3 / 2), ‖fderiv ℝ f y‖ ^ 2 ≤
      gradApproxConst m * (projectedExcessMeasure μ ν).real (ball 0 2) := by
  set ε := projectedExcessMeasure μ ν with hε_def
  have := hS.isFiniteMeasure_excess
  set G := normalizedGoodSet ε κ with hG_def
  set B : Set (Space m) := ball 0 (3 / 2) with hB_def
  set e := ε.real (ball (0 : Space m) 2) with he_def
  have hGm : MeasurableSet G := measurableSet_excessGoodSet ε measurableSet_ball _ _
  have hGB : G ⊆ B := excessGoodSet_subset _ _ _ _
  set K := lipschitzApproxConst m * Real.sqrt κ with hK_def
  have hK0 : 0 ≤ K := mul_nonneg (lipschitzApproxConst_nonneg m) (Real.sqrt_nonneg _)
  have hKcoe : ((Real.toNNReal K : ℝ≥0) : ℝ) = K := Real.coe_toNNReal _ hK0
  have hDf : ∀ y, ‖fderiv ℝ f y‖ ≤ K := fun y ↦ by
    rw [← hKcoe]; exact norm_fderiv_le_of_lipschitz ℝ hf
  have hmeasD : Measurable fun y ↦ ‖fderiv ℝ f y‖ ^ 2 :=
    ((measurable_fderiv ℝ f).norm).pow_const 2
  have hintB : IntegrableOn (fun y ↦ ‖fderiv ℝ f y‖ ^ 2) B := by
    refine IntegrableOn.of_bound measure_ball_lt_top hmeasD.aestronglyMeasurable (K ^ 2)
      (Eventually.of_forall fun y ↦ ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hDf y) 2
  set C₁ : ℝ := (2 * 4 ^ m * 2 ^ (3 * m + 3) * 2) ^ 2 with hC₁_def
  set θ : Space m → ℝ := fun y ↦ (ε.rnDeriv volume y).toReal with hθ_def
  -- (1) the pointwise bound on the good set
  have hpt : ∀ᵐ y ∂volume, y ∈ G → ‖fderiv ℝ f y‖ ^ 2 ≤ C₁ * θ y := by
    filter_upwards [hf.ae_differentiableAt,
      ae_mem_goodLebesgueSet hS.measurableSet hS.pos.le ε κ,
      Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet volume hGm,
      Besicovitch.ae_tendsto_rnDeriv ε volume, Measure.rnDeriv_lt_top ε volume]
      with y hdiff hyL hdens hrn hfin hyG
    have hyL' := hyL hyG
    have hθy : ENNReal.ofReal (θ y) = ε.rnDeriv volume y := ENNReal.ofReal_toReal hfin.ne
    have hθ0 : 0 ≤ θ y := ENNReal.toReal_nonneg
    have hdens' : Tendsto (fun r ↦ volume (G ∩ closedBall y r) / volume (closedBall y r))
        (𝓝[>] 0) (𝓝 1) := by
      simpa [indicator_of_mem hyG] using hdens
    have hrn' : Tendsto (fun r ↦ ε (closedBall y r) / volume (closedBall y r)) (𝓝[>] 0)
        (𝓝 (ENNReal.ofReal (θ y))) := by rw [hθy]; exact hrn
    -- `θ ≤ κ` at good points
    have hθκ : θ y ≤ κ := by
      have hle : ε.rnDeriv volume y ≤ ENNReal.ofReal κ := by
        refine le_of_tendsto hrn ?_
        filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 4)] with r hr
        have hvpos : volume (closedBall y r) ≠ 0 := (measure_closedBall_pos volume y hr.1).ne'
        have hvfin : volume (closedBall y r) ≠ ⊤ := measure_closedBall_lt_top.ne
        rw [ENNReal.div_le_iff hvpos hvfin]
        exact hyG.2 r hr.1 hr.2
      rw [← hθy] at hle
      exact (ENNReal.ofReal_le_ofReal_iff hκ0.le).mp hle
    have hmain := hS.norm_fderiv_le_of_density hU2 hfg hyL' hdiff hdens' hθ0 hrn'
    have hsq := sqrt_two_mul_one_add_le hθ0 (hθκ.trans hκ1)
    have hℓ : ‖fderiv ℝ f y‖ ≤ 2 * 4 ^ m * 2 ^ (3 * m + 3) * 2 * Real.sqrt (θ y) := by
      have h4 : (0 : ℝ) < (1 / 4) ^ m := by positivity
      have h1 : 1 / 2 * (1 / 4) ^ m * ‖fderiv ℝ f y‖ ≤
          2 ^ (3 * m + 3) * (2 * Real.sqrt (θ y)) :=
        hmain.trans (mul_le_mul_of_nonneg_left hsq (by positivity))
      have hone : (2 : ℝ) * 4 ^ m * (1 / 2 * (1 / 4) ^ m) = 1 := by
        rw [show (2 : ℝ) * 4 ^ m * (1 / 2 * (1 / 4) ^ m) = (4 * (1 / 4)) ^ m by
          rw [mul_pow]; ring]
        norm_num
      calc
        ‖fderiv ℝ f y‖ = (2 * 4 ^ m * (1 / 2 * (1 / 4) ^ m)) * ‖fderiv ℝ f y‖ := by
          rw [hone, one_mul]
        _ = 2 * 4 ^ m * (1 / 2 * (1 / 4) ^ m * ‖fderiv ℝ f y‖) := by ring
        _ ≤ 2 * 4 ^ m * (2 ^ (3 * m + 3) * (2 * Real.sqrt (θ y))) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = 2 * 4 ^ m * 2 ^ (3 * m + 3) * 2 * Real.sqrt (θ y) := by ring
    calc
      ‖fderiv ℝ f y‖ ^ 2 ≤ (2 * 4 ^ m * 2 ^ (3 * m + 3) * 2 * Real.sqrt (θ y)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hℓ 2
      _ = C₁ * θ y := by
        rw [mul_pow, Real.sq_sqrt hθ0, hC₁_def]
  -- (2) the good part
  have hθ_int : Integrable θ volume := by
    refine integrable_toReal_of_lintegral_ne_top
      (Measure.measurable_rnDeriv ε volume).aemeasurable ?_
    have hle : ∫⁻ y, ε.rnDeriv volume y ≤ ε univ := by
      rw [← setLIntegral_univ, ← withDensity_apply _ MeasurableSet.univ]
      exact Measure.withDensity_rnDeriv_le ε volume univ
    exact ne_top_of_le_ne_top (measure_ne_top _ _) hle
  have hθG : ∫ y in G, θ y ≤ ε.real G := by
    rw [integral_toReal (Measure.measurable_rnDeriv ε volume).aemeasurable
      (ae_restrict_of_ae (Measure.rnDeriv_lt_top ε volume))]
    have hle : ∫⁻ y in G, ε.rnDeriv volume y ≤ ε G := by
      rw [← withDensity_apply _ hGm]
      exact Measure.withDensity_rnDeriv_le ε volume G
    exact ENNReal.toReal_mono (measure_ne_top _ _) hle
  have hGe : ε.real G ≤ e :=
    measureReal_mono (hGB.trans (ball_subset_ball (by norm_num))) (measure_ne_top _ _)
  have hgood : ∫ y in G, ‖fderiv ℝ f y‖ ^ 2 ≤ C₁ * e := by
    have hC₁ : 0 ≤ C₁ := by positivity
    calc
      ∫ y in G, ‖fderiv ℝ f y‖ ^ 2 ≤ ∫ y in G, C₁ * θ y :=
        setIntegral_mono_ae_restrict (hintB.mono_set hGB) (hθ_int.integrableOn.const_mul C₁)
          ((ae_restrict_iff' hGm).mpr hpt)
      _ = C₁ * ∫ y in G, θ y := integral_const_mul _ _
      _ ≤ C₁ * ε.real G := mul_le_mul_of_nonneg_left hθG hC₁
      _ ≤ C₁ * e := mul_le_mul_of_nonneg_left hGe hC₁
  -- (3) the bad part
  have hbad : ∫ y in B \ G, ‖fderiv ℝ f y‖ ^ 2 ≤ lipschitzApproxConst m ^ 2 * 4 ^ m * e := by
    have hvol := volume_ball_diff_excessGoodSet_le ε (0 : Space m) (R := 3 / 2) (s₀ := 1 / 4) hκ0
    have hball : ε (ball (0 : Space m) (3 / 2 + 1 / 4)) ≤ ε (ball (0 : Space m) 2) :=
      measure_mono (ball_subset_ball (by norm_num))
    have hvol' : volume (B \ G) ≤ ENNReal.ofReal (4 ^ m / κ) * ε (ball (0 : Space m) 2) :=
      hvol.trans (by gcongr)
    have hvolr : volume.real (B \ G) ≤ 4 ^ m / κ * e := by
      have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (measure_ne_top _ _)) hvol'
      rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at h
    calc
      ∫ y in B \ G, ‖fderiv ℝ f y‖ ^ 2 ≤ ∫ y in B \ G, K ^ 2 :=
        setIntegral_mono_on (hintB.mono_set sdiff_subset)
          (integrableOn_const (measure_ne_top_of_subset sdiff_subset measure_ball_lt_top.ne))
          (measurableSet_ball.diff hGm) (fun y _ ↦ pow_le_pow_left₀ (norm_nonneg _) (hDf y) 2)
      _ = K ^ 2 * volume.real (B \ G) := by rw [setIntegral_const, smul_eq_mul, mul_comm]
      _ ≤ K ^ 2 * (4 ^ m / κ * e) := mul_le_mul_of_nonneg_left hvolr (sq_nonneg _)
      _ = lipschitzApproxConst m ^ 2 * 4 ^ m * e := by
        rw [hK_def, mul_pow, Real.sq_sqrt hκ0.le]
        field_simp
  calc
    ∫ y in B, ‖fderiv ℝ f y‖ ^ 2 = (∫ y in B ∩ G, ‖fderiv ℝ f y‖ ^ 2) +
        ∫ y in B \ G, ‖fderiv ℝ f y‖ ^ 2 := (integral_inter_add_sdiff hGm hintB).symm
    _ = (∫ y in G, ‖fderiv ℝ f y‖ ^ 2) + ∫ y in B \ G, ‖fderiv ℝ f y‖ ^ 2 := by
      rw [inter_eq_right.mpr hGB]
    _ ≤ C₁ * e + lipschitzApproxConst m ^ 2 * 4 ^ m * e := add_le_add hgood hbad
    _ = gradApproxConst m * e := by rw [gradApproxConst, hC₁_def]; ring

end SlabTrappedRepresentation

/-! ### 4. The packaged `GR9` statement -/

/-- Horizontal almost-everywhere statements lift to the cylinder. -/
theorem ae_horizontal_of_ae {m : ℕ} {P : Space m → Prop} (hP : ∀ᵐ y ∂volume, P y) :
    ∀ᵐ x ∂(volume : Measure (Space (m + 1))), P (horizontal x) := by
  have h1 := (measurePreserving_horizontal_last m).quasiMeasurePreserving
  have h2 := Measure.quasiMeasurePreserving_fst (μ := (volume : Measure (Space m)))
    (ν := (volume : Measure ℝ))
  exact (h2.comp h1).ae hP

namespace SlabTrappedRepresentation

variable {m : ℕ} {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))}
  {E : Set (Space (m + 1))} {U : Set (Space m)} {H H' : ℝ} {μ : Measure (Space (m + 1))}
  {ν : Space (m + 1) → Space (m + 1)}

/-- **`GR9` (Lipschitz approximation on the good set).** In the normalized setting
(`B_2 ⊆ U`, `e = ε(B_2) ≤ κ ≤ 1`, `κ > 0`) let `G = normalizedGoodSet ε κ ⊆ B_{3/2}`. Then:
1. `G` is measurable and `|B_{3/2} \ G| ≤ 4^m e / κ`;
2. the columns over `B_{3/2} \ G` carry perimeter `μ(π⁻¹(B_{3/2} \ G)) ≤ |B_{3/2} \ G| + e`
   (`GR9.2`);
3. there is a `C √κ`-Lipschitz `f` with `|f| ≤ H`, equal a.e. on `G` to the signed height,
   such that `E` coincides a.e. over `G` (inside the cylinder) with the epigraph of `f`
   (single layer, provided `κ < 1`), and `∫_{B_{3/2}} |∇f|² ≤ C e` (`GR9.3`). -/
theorem gr9_lipschitz_approximation
    (hS : SlabTrappedRepresentation b E U H H' μ ν) (hU2 : ball (0 : Space m) 2 ⊆ U)
    {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1)
    (he : (projectedExcessMeasure μ ν).real (ball 0 2) ≤ κ) :
    MeasurableSet (normalizedGoodSet (projectedExcessMeasure μ ν) κ) ∧
    normalizedGoodSet (projectedExcessMeasure μ ν) κ ⊆ ball 0 (3 / 2) ∧
    volume.real (ball (0 : Space m) (3 / 2) \ normalizedGoodSet (projectedExcessMeasure μ ν) κ) ≤
      4 ^ m / κ * (projectedExcessMeasure μ ν).real (ball 0 2) ∧
    μ.real (horizontal ⁻¹' (ball (0 : Space m) (3 / 2) \
        normalizedGoodSet (projectedExcessMeasure μ ν) κ)) ≤
      volume.real (ball (0 : Space m) (3 / 2) \
        normalizedGoodSet (projectedExcessMeasure μ ν) κ) +
      (projectedExcessMeasure μ ν).real (ball 0 2) ∧
    ∃ f : Space m → ℝ,
      LipschitzWith (Real.toNNReal (lipschitzApproxConst m * Real.sqrt κ)) f ∧
      (∀ y, |f y| ≤ H) ∧
      (∀ᵐ y ∂volume, y ∈ normalizedGoodSet (projectedExcessMeasure μ ν) κ →
        f y = columnSignedHeight E H y) ∧
      (∀ᵐ x ∂volume, x ∈ cylinderSet U H' →
        horizontal x ∈ normalizedGoodSet (projectedExcessMeasure μ ν) κ →
        (x ∈ E ↔ f (horizontal x) < x (Fin.last m))) ∧
      ∫ y in ball (0 : Space m) (3 / 2), ‖fderiv ℝ f y‖ ^ 2 ≤
        gradApproxConst m * (projectedExcessMeasure μ ν).real (ball 0 2) := by
  set ε := projectedExcessMeasure μ ν with hε_def
  have := hS.isFiniteMeasure
  have := hS.isFiniteMeasure_excess
  set G := normalizedGoodSet ε κ with hG_def
  have hGm : MeasurableSet G := measurableSet_excessGoodSet ε measurableSet_ball _ _
  have hGB : G ⊆ ball 0 (3 / 2) := excessGoodSet_subset _ _ _ _
  have hBU : ball (0 : Space m) (3 / 2) ⊆ U := (ball_subset_ball (by norm_num)).trans hU2
  -- the bad set
  have hvol : volume.real (ball (0 : Space m) (3 / 2) \ G) ≤ 4 ^ m / κ * ε.real (ball 0 2) := by
    have h1 := volume_ball_diff_excessGoodSet_le ε (0 : Space m) (R := 3 / 2) (s₀ := 1 / 4) hκ0
    have hball : ε (ball (0 : Space m) (3 / 2 + 1 / 4)) ≤ ε (ball (0 : Space m) 2) :=
      measure_mono (ball_subset_ball (by norm_num))
    have h2 : volume (ball (0 : Space m) (3 / 2) \ G) ≤
        ENNReal.ofReal (4 ^ m / κ) * ε (ball (0 : Space m) 2) := h1.trans (by gcongr)
    have h3 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (measure_ne_top _ _)) h2
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at h3
  have hbadμ : μ.real (horizontal ⁻¹' (ball (0 : Space m) (3 / 2) \ G)) ≤
      volume.real (ball (0 : Space m) (3 / 2) \ G) + ε.real (ball 0 2) := by
    have h1 := measure_preimage_diff_excessGoodSet_le hS.measurableSet hS.isOpen hS.pos hS.lt
      hS.rep hS.bot hS.top measurableSet_ball hBU (1 / 4) κ
    have hfin : volume (ball (0 : Space m) (3 / 2) \ G) ≠ ⊤ :=
      measure_ne_top_of_subset sdiff_subset measure_ball_lt_top.ne
    have h2 := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfin, measure_ne_top _ _⟩) h1
    rw [ENNReal.toReal_add hfin (measure_ne_top _ _)] at h2
    have h3 : ε.real (ball (0 : Space m) (3 / 2)) ≤ ε.real (ball 0 2) :=
      measureReal_mono (ball_subset_ball (by norm_num)) (measure_ne_top _ _)
    exact h2.trans (by rw [← Measure.real, ← Measure.real]; linarith)
  obtain ⟨f, hf, hfH, hfgL, hfgG⟩ := hS.exists_lipschitz_approx hU2 hκ0.le hκ1.le he
  refine ⟨hGm, hGB, hvol, hbadμ, f, hf, hfH, hfgG, ?_, ?_⟩
  · have hsl := ae_mem_iff_columnSignedHeight_lt_of_excessGoodSet hS.measurableSet hS.isOpen
      hS.pos hS.lt hS.rep hS.bot hS.top measurableSet_ball hBU (by norm_num : (0 : ℝ) < 1 / 4)
      hκ1
    filter_upwards [hsl, ae_horizontal_of_ae hfgG] with x hx hfx hxC hxG
    rw [hfx hxG]
    exact hx hxC hxG
  · exact hS.integral_norm_fderiv_sq_le hU2 hκ0 hκ1.le hf hfgL

end SlabTrappedRepresentation

end SerrinEpigraph
