module

public import SerrinEpigraph.PhysicalTranslationStress
public import SerrinEpigraph.ScalarStationarity
public import SerrinEpigraph.RadialDefectProfile
public import SerrinEpigraph.PhaseDilationInvariance
public import SerrinEpigraph.DilationStationarity
public import SerrinEpigraph.VectorIntegrationByParts

/-!
# Smooth radial Weiss monotonicity and homogeneity of microscopic blowups

At any free-boundary point of a physical translation limit `V`, rescalings
`x ↦ V (r • x) / r` admit nondegenerate locally uniform limits with strongly
convergent gradients in `L²_loc`. Differentiating a smooth radially weighted
Weiss functional avoids spherical trace and coarea formulas completely while
forcing every microscopic blowup limit to be positively homogeneous of degree one.
-/

public section

noncomputable section

open Set MeasureTheory Filter Metric InnerProductSpace
open scoped Topology NNReal Laplacian BoundedContinuousFunction

namespace SerrinEpigraph

/-- Cubic positive-part radial cutoff `(1 - s)₊³` for the smooth Weiss functional, chosen so that
both the profile and its negative derivative `3 (1 - s)₊²` are `C¹` on all of `ℝ`. -/
@[expose] def weissProfile (s : ℝ) : ℝ := max (1 - s) 0 ^ 3

/-- Negative derivative `3 (1 - s)₊²` of `weissProfile`, serving as the smooth radial boundary
weight in the Weiss functional. -/
@[expose] def weissBoundaryProfile (s : ℝ) : ℝ := 3 * radialDefectProfile s

theorem weissProfile_contDiff : ContDiff ℝ 1 weissProfile :=
  (contDiff_positivePart_pow (k := 3) (by norm_num)).comp (contDiff_const.sub contDiff_id)

theorem weissBoundaryProfile_contDiff : ContDiff ℝ 1 weissBoundaryProfile :=
  contDiff_const.mul radialDefectProfile_contDiff

theorem weissProfile_hasDerivAt (s : ℝ) :
    HasDerivAt weissProfile (-weissBoundaryProfile s) s := by
  have hd := (hasDerivAt_positivePart_pow (k := 3) (by norm_num) (1 - s)).comp s
    ((hasDerivAt_id s).const_sub 1)
  convert hd using 1
  · rfl
  · dsimp [weissBoundaryProfile, radialDefectProfile]
    ring

theorem weissProfile_deriv (s : ℝ) : deriv weissProfile s = -weissBoundaryProfile s :=
  (weissProfile_hasDerivAt s).deriv

theorem weissProfile_zero {s : ℝ} (hs : 1 ≤ s) : weissProfile s = 0 := by
  simp [weissProfile, max_eq_right (by linarith : 1 - s ≤ 0)]

theorem weissBoundaryProfile_zero {s : ℝ} (hs : 1 ≤ s) : weissBoundaryProfile s = 0 := by
  simp [weissBoundaryProfile, radialDefectProfile_zero hs]

theorem weissProfile_mem_Icc {s : ℝ} (hs : 0 ≤ s) : weissProfile s ∈ Icc (0 : ℝ) 1 := by
  have h0 : 0 ≤ max (1 - s) 0 := le_max_right _ _
  have h1 : max (1 - s) 0 ≤ 1 := max_le (by linarith) (by norm_num)
  refine ⟨pow_nonneg h0 3, ?_⟩
  simpa only [weissProfile, one_pow] using pow_le_pow_left₀ h0 h1 3

theorem weissBoundaryProfile_nonneg (s : ℝ) : 0 ≤ weissBoundaryProfile s := by
  unfold weissBoundaryProfile radialDefectProfile
  positivity

theorem weissBoundaryProfile_mem_Icc {s : ℝ} (hs : 0 ≤ s) :
    weissBoundaryProfile s ∈ Icc (0 : ℝ) 3 := by
  have hm := radialDefectProfile_mem_Icc hs
  exact ⟨weissBoundaryProfile_nonneg s, by dsimp [weissBoundaryProfile]; linarith [hm.2]⟩

theorem weissBoundaryProfile_lower {s : ℝ} (hs : s ≤ 1 / 4) :
    1 ≤ weissBoundaryProfile s := by
  unfold weissBoundaryProfile radialDefectProfile
  rw [max_eq_left (by linarith : 0 ≤ 1 - s)]
  nlinarith

/-- Smooth radially weighted bulk energy normalized at the microscopic blowup scale. -/
@[expose] def smoothWeissEnergy {m : ℕ} (f : ℝ → ℝ) (V : Space (m + 1) → ℝ) (r : ℝ) : ℝ :=
  r ^ (-(m + 1 : ℤ)) * ∫ x,
    (2 * phaseEnergyDensity f 0 V x) * radialWeight weissProfile 0 r x

/-- Smooth radially weighted boundary term for the microscopic Weiss functional. -/
@[expose] def smoothWeissBoundary {m : ℕ} (V : Space (m + 1) → ℝ) (r : ℝ) : ℝ :=
  2 * ∫ y, (V (r • y) / r) ^ 2 * weissBoundaryProfile (‖y‖ ^ 2)

/-- Smooth radial Weiss functional on ambient Euclidean space. -/
@[expose] def smoothWeissFunctional {m : ℕ} (f : ℝ → ℝ) (V : Space (m + 1) → ℝ) (r : ℝ) : ℝ :=
  smoothWeissEnergy f V r - smoothWeissBoundary V r

/-- Change of variables `x = r • y` writes the boundary term as a spatial radial weight. -/
theorem smoothWeissBoundary_eq_spatial_integral {m : ℕ} (V : Space (m + 1) → ℝ)
    {r : ℝ} (hr : 0 < r) :
    smoothWeissBoundary V r =
      2 * r ^ (-(m + 3 : ℤ)) *
        ∫ x, V x ^ 2 * radialWeight weissBoundaryProfile 0 r x := by
  let G : Space (m + 1) → ℝ := fun x ↦
    r ^ (-2 : ℤ) * (V x ^ 2 * radialWeight weissBoundaryProfile 0 r x)
  have hcomp (y : Space (m + 1)) :
      (V (r • y) / r) ^ 2 * weissBoundaryProfile (‖y‖ ^ 2) = G (r • y) := by
    have hnorm : ‖r • y - 0‖ ^ 2 / r ^ 2 = ‖y‖ ^ 2 := by
      rw [sub_zero, norm_smul, Real.norm_of_nonneg hr.le, mul_pow,
        mul_div_cancel_left₀ _ (sq_pos_of_pos hr).ne']
    dsimp only [G, radialWeight]
    rw [hnorm, zpow_neg, zpow_ofNat]
    field_simp
  simp_rw [smoothWeissBoundary, hcomp]
  rw [Measure.integral_comp_smul volume G r]
  simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul]
  rw [abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hr.le (m + 1)))]
  dsimp only [G]
  rw [integral_const_mul]
  have hrpow : (r ^ (m + 1))⁻¹ * r ^ (-2 : ℤ) = r ^ (-(m + 3 : ℤ)) := by
    have h1 : (r ^ (m + 1))⁻¹ = r ^ (-(m + 1 : ℤ)) := by
      rw [zpow_neg, show (m + 1 : ℤ) = ((m + 1 : ℕ) : ℤ) by push_cast; rfl, zpow_natCast]
    rw [h1, ← zpow_add₀ hr.ne']
    exact congrArg (r ^ ·) (by ring)
  calc
    2 * ((r ^ (m + 1))⁻¹ * (r ^ (-2 : ℤ) *
        ∫ x, V x ^ 2 * radialWeight weissBoundaryProfile 0 r x)) =
      2 * ((r ^ (m + 1))⁻¹ * r ^ (-2 : ℤ)) *
        ∫ x, V x ^ 2 * radialWeight weissBoundaryProfile 0 r x := by ring
    _ = _ := by rw [hrpow]

/-- Spatial rescaling scales the totalized gradient by the dilation factor everywhere. -/
theorem gradient_comp_smul {d : ℕ} (v : Space d → ℝ) {r : ℝ} (hr : r ≠ 0) (x : Space d) :
    gradient (fun y ↦ v (r • y)) x = r • gradient v (r • x) := by
  by_cases hd : DifferentiableAt ℝ v (r • x)
  · have hsmul : HasFDerivAt (fun y : Space d ↦ r • y)
        (r • ContinuousLinearMap.id ℝ (Space d)) x :=
      (r • ContinuousLinearMap.id ℝ (Space d)).hasFDerivAt
    have hcomp : HasFDerivAt (fun y ↦ v (r • y))
        ((fderiv ℝ v (r • x)).comp (r • ContinuousLinearMap.id ℝ (Space d))) x :=
      hd.hasFDerivAt.comp x hsmul
    have hf : fderiv ℝ (fun y ↦ v (r • y)) x = r • fderiv ℝ v (r • x) := by
      rw [hcomp.fderiv]
      ext w
      simp
    simp only [gradient, hf, map_smul]
  · have hnd : ¬DifferentiableAt ℝ (fun y ↦ v (r • y)) x := by
      intro hcomp
      apply hd
      have hinv : DifferentiableAt ℝ (fun z : Space d ↦ r⁻¹ • z) (r • x) :=
        (r⁻¹ • ContinuousLinearMap.id ℝ (Space d)).differentiableAt
      have hh : DifferentiableAt ℝ (fun z ↦ (fun y ↦ v (r • y)) (r⁻¹ • z)) (r • x) :=
        DifferentiableAt.comp (g := fun y ↦ v (r • y)) (f := fun z : Space d ↦ r⁻¹ • z)
          (r • x) (by simpa only [inv_smul_smul₀ hr] using hcomp) hinv
      have heq : (fun z ↦ (fun y ↦ v (r • y)) (r⁻¹ • z)) = v := by
        funext z
        simp [smul_inv_smul₀ hr]
      rwa [heq] at hh
    simp [gradient, fderiv_zero_of_not_differentiableAt hd,
      fderiv_zero_of_not_differentiableAt hnd]

/-- Microscopic rescaling `y ↦ v (r • y) / r` preserves the totalized gradient everywhere. -/
theorem gradient_rescale_div {d : ℕ} (v : Space d → ℝ) {r : ℝ} (hr : r ≠ 0) (x : Space d) :
    gradient (fun y ↦ v (r • y) / r) x = gradient v (r • x) := by
  let g : Space d → ℝ := fun y ↦ v (r • y)
  have hmul : fderiv ℝ (fun y ↦ r⁻¹ * g y) x = r⁻¹ • fderiv ℝ g x := by
    by_cases hd : DifferentiableAt ℝ g x
    · exact (hd.hasFDerivAt.const_mul r⁻¹).fderiv
    · have hnd : ¬DifferentiableAt ℝ (fun y ↦ r⁻¹ * g y) x := by
        intro hm
        apply hd
        have heq : (fun y ↦ r * (r⁻¹ * g y)) = g := by
          funext y
          field_simp
        rw [← heq]
        exact hm.const_mul r
      simp [fderiv_zero_of_not_differentiableAt hd, fderiv_zero_of_not_differentiableAt hnd]
  have heq : (fun y ↦ v (r • y) / r) = fun y ↦ r⁻¹ * g y := by
    funext y
    dsimp [g]
    ring
  rw [heq, gradient, hmul, map_smul]
  change r⁻¹ • gradient (fun y ↦ v (r • y)) x = gradient v (r • x)
  rw [gradient_comp_smul v hr x, inv_smul_smul₀ hr]

/-- Microscopic rescaling `y ↦ v (r • y) / r` preserves any global Lipschitz constant. -/
theorem lipschitzWith_rescale_div {d : ℕ} {v : Space d → ℝ} {L : ℝ≥0}
    (hv : LipschitzWith L v) {r : ℝ} (hr : 0 < r) :
    LipschitzWith L (fun x ↦ v (r • x) / r) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, ← sub_div, abs_div, abs_of_pos hr, ← Real.dist_eq]
  have hd := hv.dist_le_mul (r • x) (r • y)
  rw [dist_smul₀, Real.norm_of_nonneg hr.le] at hd
  exact (div_le_iff₀ hr).mpr (by linarith)

/-- Physical translates retain scalar stationarity across their free boundaries. -/
theorem RigidityHypotheses.translated_zeroExtension_scalar_stationarity
    {m : ℕ} {g : Space m → ℝ} {u φ : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (p : Space (m + 1))
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) :
    (∫ x, φ x * (‖gradient (zeroExtension g u) (p + x)‖ ^ 2 -
      zeroExtension g u (p + x) * f (zeroExtension g u (p + x))) +
      zeroExtension g u (p + x) *
        inner ℝ (gradient (zeroExtension g u) (p + x)) (gradient φ x)) = 0 := by
  let ψ : Space (m + 1) → ℝ := fun x ↦ φ (x + -p)
  have hψ : ContDiff ℝ 1 ψ := hφ.comp (contDiff_id.add contDiff_const)
  have hcψ : HasCompactSupport ψ :=
    hc.comp_isClosedEmbedding (isometry_add_right (-p)).isClosedEmbedding
  have hi := hr.integral_zeroExtension_scalar_stationarity h hψ hcψ
  have ht := integral_add_right_eq_self (μ := volume)
    (fun x ↦ ψ x * (‖gradient (zeroExtension g u) x‖ ^ 2 -
      zeroExtension g u x * f (zeroExtension g u x)) +
      zeroExtension g u x * inner ℝ (gradient (zeroExtension g u) x) (gradient ψ x)) p
  rw [← ht] at hi
  have hg (x : Space (m + 1)) : gradient ψ (x + p) = gradient φ x := by
    simp [ψ, gradient, fderiv_comp_add_right]
  simp only [ψ, hg, add_neg_cancel_right] at hi
  simpa only [add_comm] using hi

/-- Physical translation limits inherit the global scalar stationarity identity. -/
theorem RigidityHypotheses.physical_translation_limit_scalar_stationarity
    {m : ℕ} {g : Space m → ℝ} {u V φ : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {p : ℕ → Space (m + 1)} (hV : LipschitzWith ⟨κ, h.kappa_pos.le⟩ V)
    (hval : ∀ x, V x ∈ Icc 0 1)
    (hlim : ∀ K : Set (Space (m + 1)), IsCompact K →
      TendstoUniformlyOn (fun j x ↦ zeroExtension g u (p j + x)) V atTop K)
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) :
    (∫ x, φ x * (‖gradient V x‖ ^ 2 - V x * f (V x)) +
      V x * inner ℝ (gradient V x) (gradient φ x)) = 0 := by
  let K := tsupport φ
  let U := fun j x ↦ zeroExtension g u (p j + x)
  let q := fun j x ↦ gradient (zeroExtension g u) (p j + x)
  have hK : IsCompact K := hc
  have hpoint (x : Space (m + 1)) : Tendsto (fun j ↦ U j x) atTop (𝓝 (V x)) :=
    (hlim {x} isCompact_singleton).tendsto_at (mem_singleton x)
  obtain ⟨Cφ, hCφ⟩ := hc.exists_bound_of_continuous hφ.continuous
  have hgradφ : Continuous (gradient φ) :=
    (toDual ℝ (Space (m + 1))).symm.continuous.comp (hφ.continuous_fderiv one_ne_zero)
  have hsgrad : tsupport (gradient φ) ⊆ K := by
    apply closure_minimal _ (isClosed_tsupport φ)
    intro x hx
    by_contra hn
    exact hx (by simp [gradient, fderiv_of_notMem_tsupport ℝ hn])
  have hcgrad : HasCompactSupport (gradient φ) :=
    HasCompactSupport.of_support_subset_isCompact hK
      ((subset_tsupport _).trans hsgrad)
  obtain ⟨D, hD⟩ := hcgrad.exists_bound_of_continuous hgradφ
  have hq (j : ℕ) : Measurable (q j) :=
    (measurable_gradient _).comp (continuous_const.add continuous_id).measurable
  have hqbound (j : ℕ) (x : Space (m + 1)) : ‖q j x‖ ≤ κ :=
    hr.gradient_zeroExtension_norm_le_kappa h _
  have hVbound (x : Space (m + 1)) : ‖gradient V x‖ ≤ κ := by
    rw [gradient, LinearIsometryEquiv.norm_map]
    exact norm_fderiv_le_of_lipschitz ℝ hV
  have hiKj (j : ℕ) : IntegrableOn (fun x ↦ ‖q j x‖ ^ 2) K := by
    have hlip : LocallyLipschitz (U j) :=
      h.zeroExtension_locallyLipschitz.comp (isometry_add_left (p j)).lipschitzWith.locallyLipschitz
    simpa only [U, q, gradient, fderiv_comp_add_left] using
      integrableOn_gradient_sq_of_locallyLipschitz hlip hK
  have hiKV : IntegrableOn (fun x ↦ ‖gradient V x‖ ^ 2) K :=
    integrableOn_gradient_sq_of_locallyLipschitz hV.locallyLipschitz hK
  have ht1 := integral_mul_tendsto_of_integral_norm_sub_tendsto
    (volume.restrict K) (fun j x ↦ ‖q j x‖ ^ 2) (fun x ↦ ‖gradient V x‖ ^ 2) φ Cφ
    hiKj hiKV hφ.continuous.aestronglyMeasurable hCφ
    (hr.physical_translation_kinetic_tendsto h hV hval hlim hK)
  have hfcont : ContinuousOn (fun s : ℝ ↦ s * f s) (Icc 0 1) :=
    continuousOn_id.mul (h.reaction_contDiffOn.continuousOn.mono Icc_subset_Ici_self)
  have ht2 := hr.physical_translation_observable_tendsto h hval hpoint hK
    hφ.continuous.continuousOn hfcont
  have hUv (j : ℕ) (x : Space (m + 1)) : U j x ∈ Icc 0 1 :=
    ⟨h.zeroExtension_nonneg _, (hr.zeroExtension_lt_one _).le⟩
  have hUcont (j : ℕ) : Continuous (U j) :=
    h.zeroExtension_continuous.comp (continuous_const.add continuous_id)
  have htU : Tendsto (fun j ↦ ∫ x in K, ‖U j x - V x‖) atTop (𝓝 0) := by
    have ht0 : Tendsto (fun j ↦ ∫ x in K, ‖U j x - V x‖) atTop (𝓝 (∫ _x in K, (0 : ℝ))) := by
      apply tendsto_integral_of_dominated_convergence (fun _ ↦ (2 : ℝ))
      · exact fun j ↦ ((hUcont j).sub hV.continuous).norm.aestronglyMeasurable
      · exact continuousOn_const.integrableOn_compact hK
      · intro j
        filter_upwards with x
        rw [norm_norm, Real.norm_eq_abs]
        exact abs_le.mpr ⟨by linarith [(hUv j x).1, (hUv j x).2, (hval x).1, (hval x).2],
          by linarith [(hUv j x).1, (hUv j x).2, (hval x).1, (hval x).2]⟩
      · filter_upwards with x
        simpa using ((hpoint x).sub (tendsto_const_nhds (x := V x))).norm
    simpa using ht0
  have htG := hr.physical_translation_gradient_integral_norm_tendsto h hV hval hlim hK
  have hi3j (j : ℕ) : IntegrableOn (fun x ↦ U j x * inner ℝ (q j x) (gradient φ x)) K := by
    apply (continuousOn_const.integrableOn_compact hK (f := fun _ ↦ κ * D)).mono'
      ((hUcont j).measurable.mul ((hq j).inner (𝕜 := ℝ) hgradφ.measurable)).aestronglyMeasurable
    filter_upwards with x
    simp only [Pi.mul_apply]
    rw [norm_mul, Real.norm_of_nonneg (hUv j x).1]
    have hin : ‖inner ℝ (q j x) (gradient φ x)‖ ≤ κ * D :=
      (norm_inner_le_norm (𝕜 := ℝ) _ _).trans
        (mul_le_mul (hqbound j x) (hD x) (norm_nonneg _) h.kappa_pos.le)
    exact (mul_le_of_le_one_left (norm_nonneg _) (hUv j x).2).trans hin
  have hi3V : IntegrableOn (fun x ↦ V x * inner ℝ (gradient V x) (gradient φ x)) K := by
    apply (continuousOn_const.integrableOn_compact hK (f := fun _ ↦ κ * D)).mono'
      (hV.continuous.measurable.mul
        ((measurable_gradient V).inner (𝕜 := ℝ) hgradφ.measurable)).aestronglyMeasurable
    filter_upwards with x
    simp only [Pi.mul_apply]
    rw [norm_mul, Real.norm_of_nonneg (hval x).1]
    have hin : ‖inner ℝ (gradient V x) (gradient φ x)‖ ≤ κ * D :=
      (norm_inner_le_norm (𝕜 := ℝ) _ _).trans
        (mul_le_mul (hVbound x) (hD x) (norm_nonneg _) h.kappa_pos.le)
    exact (mul_le_of_le_one_left (norm_nonneg _) (hval x).2).trans hin
  have ht3 : Tendsto (fun j ↦ ∫ x in K, U j x * inner ℝ (q j x) (gradient φ x)) atTop
      (𝓝 (∫ x in K, V x * inner ℝ (gradient V x) (gradient φ x))) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have hmaj := (htU.const_mul (κ * D)).add (htG.const_mul D)
    simp only [mul_zero, add_zero] at hmaj
    apply squeeze_zero (fun _ ↦ norm_nonneg _) _ hmaj
    intro j
    rw [← integral_sub (hi3j j) hi3V]
    have hiU : IntegrableOn (fun x ↦ ‖U j x - V x‖) K :=
      ((hUcont j).sub hV.continuous).norm.continuousOn.integrableOn_compact hK
    have hiG : IntegrableOn (fun x ↦ ‖q j x - gradient V x‖) K := by
      apply (continuousOn_const.integrableOn_compact hK (f := fun _ ↦ 2 * κ)).mono'
        ((hq j).sub (measurable_gradient V)).norm.aestronglyMeasurable
      filter_upwards with x
      rw [norm_norm]
      exact (norm_sub_le _ _).trans (by linarith [hqbound j x, hVbound x])
    calc
      ‖∫ x in K, U j x * inner ℝ (q j x) (gradient φ x) -
          V x * inner ℝ (gradient V x) (gradient φ x)‖ ≤
        ∫ x in K, ‖U j x * inner ℝ (q j x) (gradient φ x) -
          V x * inner ℝ (gradient V x) (gradient φ x)‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ x in K, κ * D * ‖U j x - V x‖ + D * ‖q j x - gradient V x‖ := by
        apply integral_mono ((hi3j j).sub hi3V).norm
          ((hiU.const_mul (κ * D)).add (hiG.const_mul D))
        intro x
        simp only [Pi.sub_apply, Pi.add_apply]
        have hsplit : U j x * inner ℝ (q j x) (gradient φ x) -
            V x * inner ℝ (gradient V x) (gradient φ x) =
            (U j x - V x) * inner ℝ (q j x) (gradient φ x) +
            V x * inner ℝ (q j x - gradient V x) (gradient φ x) := by
          rw [inner_sub_left]
          ring
        rw [hsplit]
        apply (norm_add_le _ _).trans
        apply add_le_add
        · rw [norm_mul]
          have hin : ‖inner ℝ (q j x) (gradient φ x)‖ ≤ κ * D :=
            (norm_inner_le_norm (𝕜 := ℝ) _ _).trans
              (mul_le_mul (hqbound j x) (hD x) (norm_nonneg _) h.kappa_pos.le)
          exact (mul_le_mul_of_nonneg_left hin (norm_nonneg _)).trans_eq (mul_comm _ _)
        · rw [norm_mul, Real.norm_of_nonneg (hval x).1]
          have hin : ‖inner ℝ (q j x - gradient V x) (gradient φ x)‖ ≤
              ‖q j x - gradient V x‖ * D :=
            (norm_inner_le_norm (𝕜 := ℝ) _ _).trans
              (mul_le_mul_of_nonneg_left (hD x) (norm_nonneg _))
          exact ((mul_le_of_le_one_left (norm_nonneg _) (hval x).2).trans hin).trans_eq
            (mul_comm _ _)
      _ = κ * D * (∫ x in K, ‖U j x - V x‖) + D * ∫ x in K, ‖q j x - gradient V x‖ := by
        rw [integral_add (hiU.const_mul _) (hiG.const_mul _), integral_const_mul,
          integral_const_mul]
  have hi1j (j : ℕ) : IntegrableOn (fun x ↦ ‖q j x‖ ^ 2 * φ x) K :=
    (hiKj j).mul_continuousOn hφ.continuous.continuousOn hK
  have hi1V : IntegrableOn (fun x ↦ ‖gradient V x‖ ^ 2 * φ x) K :=
    hiKV.mul_continuousOn hφ.continuous.continuousOn hK
  have hi2j (j : ℕ) : IntegrableOn (fun x ↦ U j x * f (U j x) * φ x) K :=
    ((hfcont.comp_continuous (hUcont j) (hUv j)).mul
      hφ.continuous).continuousOn.integrableOn_compact hK
  have hi2V : IntegrableOn (fun x ↦ V x * f (V x) * φ x) K :=
    ((hfcont.comp_continuous hV.continuous hval).mul
      hφ.continuous).continuousOn.integrableOn_compact hK
  have hcut (v : Space (m + 1) → ℝ) (r : Space (m + 1) → Space (m + 1)) :
      (∫ x in K, φ x * (‖r x‖ ^ 2 - v x * f (v x)) + v x * inner ℝ (r x) (gradient φ x)) =
        ∫ x, φ x * (‖r x‖ ^ 2 - v x * f (v x)) + v x * inner ℝ (r x) (gradient φ x) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    simp [image_eq_zero_of_notMem_tsupport hx, gradient, fderiv_of_notMem_tsupport ℝ hx]
  have hz (j : ℕ) :
      (∫ x in K, ‖q j x‖ ^ 2 * φ x) - (∫ x in K, U j x * f (U j x) * φ x) +
        (∫ x in K, U j x * inner ℝ (q j x) (gradient φ x)) = 0 := by
    have hsub := integral_sub (hi1j j) (hi2j j)
    have hadd := integral_add ((hi1j j).sub (hi2j j)) (hi3j j)
    simp only [Pi.sub_apply] at hsub hadd
    have heq : (∫ x in K, ‖q j x‖ ^ 2 * φ x - U j x * f (U j x) * φ x +
          U j x * inner ℝ (q j x) (gradient φ x)) =
        ∫ x in K, φ x * (‖q j x‖ ^ 2 - U j x * f (U j x)) +
          U j x * inner ℝ (q j x) (gradient φ x) :=
      setIntegral_congr_fun hK.measurableSet (fun x _ ↦ by ring)
    have hst : (∫ x in K, φ x * (‖q j x‖ ^ 2 - U j x * f (U j x)) +
        U j x * inner ℝ (q j x) (gradient φ x)) = 0 := by
      rw [hcut]
      exact hr.translated_zeroExtension_scalar_stationarity h (p j) hφ hc
    linarith
  have hlim_all := (ht1.sub ht2).add ht3
  have hzero := tendsto_nhds_unique
    (tendsto_const_nhds.congr' (Eventually.of_forall (fun j ↦ (hz j).symm))) hlim_all
  rw [← hcut V (gradient V)]
  have hsubV := integral_sub hi1V hi2V
  have haddV := integral_add (hi1V.sub hi2V) hi3V
  simp only [Pi.sub_apply] at hsubV haddV
  have heqV : (∫ x in K, φ x * (‖gradient V x‖ ^ 2 - V x * f (V x)) +
        V x * inner ℝ (gradient V x) (gradient φ x)) =
      ∫ x in K, ‖gradient V x‖ ^ 2 * φ x - V x * f (V x) * φ x +
        V x * inner ℝ (gradient V x) (gradient φ x) :=
    setIntegral_congr_fun hK.measurableSet (fun x _ ↦ by ring)
  linarith

/-- A translated zero extension satisfies the first-order weak equation on its positive phase. -/
theorem Hypotheses.translated_zeroExtension_weak_equation
    {m : ℕ} {g : Space m → ℝ} {u η : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (h : Hypotheses g u f κ) (p : Space (m + 1)) (hη : ContDiff ℝ 1 η)
    (hc : HasCompactSupport η)
    (hs : ∀ x ∈ tsupport η, 0 < zeroExtension g u (p + x)) :
    (∫ x, inner ℝ (gradient (zeroExtension g u) (p + x)) (gradient η x)) =
      ∫ x, f (zeroExtension g u (p + x)) * η x := by
  let ψ : Space (m + 1) → ℝ := fun z ↦ η (z + -p)
  have hψ : ContDiff ℝ 1 ψ := hη.comp (contDiff_id.add contDiff_const)
  have hcψ : HasCompactSupport ψ :=
    hc.comp_isClosedEmbedding (isometry_add_right (-p)).isClosedEmbedding
  have hsub : tsupport ψ ⊆ epigraph g := by
    intro z hz
    have hmem : z + -p ∈ tsupport η :=
      tsupport_comp_subset_preimage η (continuous_id.add continuous_const) hz
    have hpos := hs (z + -p) hmem
    have he : p + (z + -p) = z := by abel
    rw [he] at hpos
    exact (h.zeroExtension_pos_iff z).mp hpos
  have hw := h.weak_equation hψ hcψ hsub
  have hL : (∫ z, inner ℝ (gradient (zeroExtension g u) z) (gradient ψ z)) =
      ∫ z, inner ℝ (gradient u z) (gradient ψ z) := by
    apply integral_congr_ae
    refine Eventually.of_forall (fun z ↦ ?_)
    by_cases hz : z ∈ epigraph g
    · simp [h.gradient_zeroExtension hz]
    · have hn : z ∉ tsupport ψ := fun hm ↦ hz (hsub hm)
      simp [gradient, fderiv_of_notMem_tsupport ℝ hn]
  have hR : (∫ z, f (zeroExtension g u z) * ψ z) = ∫ z, f (u z) * ψ z := by
    apply integral_congr_ae
    refine Eventually.of_forall (fun z ↦ ?_)
    by_cases hz : z ∈ epigraph g
    · simp [zeroExtension_of_mem hz]
    · have hn : z ∉ tsupport ψ := fun hm ↦ hz (hsub hm)
      simp [image_eq_zero_of_notMem_tsupport hn]
  rw [← hL, ← hR] at hw
  have htL := integral_add_right_eq_self (μ := volume)
    (fun z ↦ inner ℝ (gradient (zeroExtension g u) z) (gradient ψ z)) p
  have htR := integral_add_right_eq_self (μ := volume)
    (fun z ↦ f (zeroExtension g u z) * ψ z) p
  rw [← htL, ← htR] at hw
  have hg (x : Space (m + 1)) : gradient ψ (x + p) = gradient η x := by
    simp [ψ, gradient, fderiv_comp_add_right]
  simp only [ψ, hg, add_neg_cancel_right] at hw
  simpa only [add_comm] using hw

/-- Physical translation limits satisfy the first-order weak PDE on their positive phase. -/
theorem RigidityHypotheses.physical_translation_limit_weak_equation
    {m : ℕ} {g : Space m → ℝ} {u V η : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {p : ℕ → Space (m + 1)} (hV : LipschitzWith ⟨κ, h.kappa_pos.le⟩ V)
    (hval : ∀ x, V x ∈ Icc 0 1)
    (hlim : ∀ K : Set (Space (m + 1)), IsCompact K →
      TendstoUniformlyOn (fun j x ↦ zeroExtension g u (p j + x)) V atTop K)
    (hη : ContDiff ℝ 1 η) (hc : HasCompactSupport η)
    (hs : tsupport η ⊆ {x | 0 < V x}) :
    (∫ x, inner ℝ (gradient V x) (gradient η x)) = ∫ x, f (V x) * η x := by
  let K := tsupport η
  have hK : IsCompact K := hc
  have hpoint (x : Space (m + 1)) :
      Tendsto (fun j ↦ zeroExtension g u (p j + x)) atTop (𝓝 (V x)) :=
    (hlim {x} isCompact_singleton).tendsto_at (mem_singleton x)
  have hgradη : Continuous (gradient η) :=
    (toDual ℝ (Space (m + 1))).symm.continuous.comp (hη.continuous_fderiv one_ne_zero)
  have hsgrad : tsupport (gradient η) ⊆ K := by
    apply closure_minimal _ (isClosed_tsupport η)
    intro x hx
    by_contra hn
    exact hx (by simp [gradient, fderiv_of_notMem_tsupport ℝ hn])
  obtain ⟨D, hD⟩ := (HasCompactSupport.of_support_subset_isCompact hK
    ((subset_tsupport _).trans hsgrad)).exists_bound_of_continuous hgradη
  have hq (j : ℕ) : Measurable (fun x ↦ gradient (zeroExtension g u) (p j + x)) :=
    (measurable_gradient _).comp (continuous_const.add continuous_id).measurable
  have hqbound (j : ℕ) (x : Space (m + 1)) :
      ‖gradient (zeroExtension g u) (p j + x)‖ ≤ κ :=
    hr.gradient_zeroExtension_norm_le_kappa h _
  have hVbound (x : Space (m + 1)) : ‖gradient V x‖ ≤ κ := by
    rw [gradient, LinearIsometryEquiv.norm_map]
    exact norm_fderiv_le_of_lipschitz ℝ hV
  have hij (j : ℕ) : IntegrableOn
      (fun x ↦ inner ℝ (gradient (zeroExtension g u) (p j + x)) (gradient η x)) K := by
    apply (continuousOn_const.integrableOn_compact hK (f := fun _ ↦ κ * D)).mono'
      ((hq j).inner (𝕜 := ℝ) hgradη.measurable).aestronglyMeasurable
    filter_upwards with x
    exact (norm_inner_le_norm (𝕜 := ℝ) _ _).trans
      (mul_le_mul (hqbound j x) (hD x) (norm_nonneg _) h.kappa_pos.le)
  have hiV : IntegrableOn (fun x ↦ inner ℝ (gradient V x) (gradient η x)) K := by
    apply (continuousOn_const.integrableOn_compact hK (f := fun _ ↦ κ * D)).mono'
      ((measurable_gradient V).inner (𝕜 := ℝ) hgradη.measurable).aestronglyMeasurable
    filter_upwards with x
    exact (norm_inner_le_norm (𝕜 := ℝ) _ _).trans
      (mul_le_mul (hVbound x) (hD x) (norm_nonneg _) h.kappa_pos.le)
  have htL : Tendsto (fun j ↦ ∫ x,
      inner ℝ (gradient (zeroExtension g u) (p j + x)) (gradient η x)) atTop
      (𝓝 (∫ x, inner ℝ (gradient V x) (gradient η x))) := by
    have hcut (r : Space (m + 1) → Space (m + 1)) :
        (∫ x in K, inner ℝ (r x) (gradient η x)) = ∫ x, inner ℝ (r x) (gradient η x) := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      simp [gradient, fderiv_of_notMem_tsupport ℝ hx]
    simp_rw [← hcut]
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have hmaj := (hr.physical_translation_gradient_integral_norm_tendsto h hV hval hlim
      hK).const_mul D
    simp only [mul_zero] at hmaj
    apply squeeze_zero (fun _ ↦ norm_nonneg _) _ hmaj
    intro j
    have hiG : IntegrableOn
        (fun x ↦ ‖gradient (zeroExtension g u) (p j + x) - gradient V x‖) K := by
      apply (continuousOn_const.integrableOn_compact hK (f := fun _ ↦ 2 * κ)).mono'
        ((hq j).sub (measurable_gradient V)).norm.aestronglyMeasurable
      filter_upwards with x
      rw [norm_norm]
      exact (norm_sub_le _ _).trans (by linarith [hqbound j x, hVbound x])
    rw [← integral_sub (hij j) hiV]
    calc
      ‖∫ x in K, inner ℝ (gradient (zeroExtension g u) (p j + x)) (gradient η x) -
          inner ℝ (gradient V x) (gradient η x)‖ ≤
        ∫ x in K, ‖inner ℝ (gradient (zeroExtension g u) (p j + x) - gradient V x)
          (gradient η x)‖ := by
        simpa only [inner_sub_left] using norm_integral_le_integral_norm _
      _ ≤ ∫ x in K, D * ‖gradient (zeroExtension g u) (p j + x) - gradient V x‖ := by
        apply integral_mono ((hij j).sub hiV |>.congr
          (Eventually.of_forall (fun _ ↦ (inner_sub_left _ _ _).symm))).norm (hiG.const_mul D)
        intro x
        exact ((norm_inner_le_norm (𝕜 := ℝ) _ _).trans
          (mul_le_mul_of_nonneg_left (hD x) (norm_nonneg _))).trans_eq (mul_comm _ _)
      _ = D * ∫ x in K, ‖gradient (zeroExtension g u) (p j + x) - gradient V x‖ :=
        integral_const_mul _ _
  have htR := hr.physical_translation_observable_tendsto h hval hpoint hK
    hη.continuous.continuousOn (h.reaction_contDiffOn.continuousOn.mono Icc_subset_Ici_self)
  simp only [K, setIntegral_mul_test] at htR
  have hpos := eventually_positive_on_compact_of_tendstoUniformlyOn hK hV.continuous.continuousOn
    hs (hlim K hK)
  apply tendsto_nhds_unique htL
  apply htR.congr'
  filter_upwards [hpos] with j hj
  exact (h.translated_zeroExtension_weak_equation (p j) hη hc hj).symm

/-- Nonnegative globally Lipschitz functions integrate by parts against compact Laplacians
without assuming a global upper bound. -/
theorem integral_mul_laplacian_eq_neg_inner_gradient_of_nonneg_lipschitz
    {d : ℕ} {v φ : Space d → ℝ} {L : ℝ≥0} (hv : LipschitzWith L v)
    (hv0 : ∀ x, 0 ≤ v x) (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) :
    (∫ x, v x * (Δ φ) x) = -∫ x, inner ℝ (gradient v x) (gradient φ x) := by
  obtain ⟨R, hR, hsupp⟩ := hc.isBounded.subset_ball_lt 0 (0 : Space d)
  let B : ℝ := v 0 + (L : ℝ) * (R + 1)
  have hB0 : 0 ≤ B := by
    dsimp [B]
    linarith [hv0 0, mul_nonneg L.coe_nonneg (show (0 : ℝ) ≤ R + 1 by linarith)]
  let w : Space d → ℝ := fun x ↦ min (v x) B
  have hw : LocallyLipschitz w := hv.locallyLipschitz.min (LocallyLipschitz.const B)
  have hwval (x : Space d) : w x ∈ Icc 0 B := ⟨le_min (hv0 x) hB0, min_le_right _ _⟩
  have heq_ball : EqOn w v (ball 0 (R + 1)) := by
    intro x hx
    have hnorm : ‖x‖ < R + 1 := by simpa only [mem_ball, dist_zero_right] using hx
    have hd := hv.dist_le_mul x 0
    rw [Real.dist_eq, dist_zero_right] at hd
    have hle : v x ≤ B := by
      dsimp [B]
      linarith [(abs_le.mp hd).2, mul_le_mul_of_nonneg_left hnorm.le L.coe_nonneg]
    exact min_eq_left hle
  have hL : (∫ x, v x * (Δ φ) x) = ∫ x, w x * (Δ φ) x := by
    apply integral_congr_ae
    refine Eventually.of_forall (fun x ↦ ?_)
    by_cases hx : x ∈ tsupport φ
    · have hxb : x ∈ ball 0 (R + 1) := (ball_subset_ball (by linarith)) (hsupp hx)
      dsimp only
      rw [heq_ball hxb]
    · simp [laplacian_zero_off_tsupport φ hx]
  have hR' : (∫ x, inner ℝ (gradient v x) (gradient φ x)) =
      ∫ x, inner ℝ (gradient w x) (gradient φ x) := by
    apply integral_congr_ae
    refine Eventually.of_forall (fun x ↦ ?_)
    by_cases hx : x ∈ tsupport φ
    · have hxb : x ∈ ball 0 (R + 1) := (ball_subset_ball (by linarith)) (hsupp hx)
      have hev : w =ᶠ[𝓝 x] v := heq_ball.eventuallyEq_of_mem (isOpen_ball.mem_nhds hxb)
      simp [gradient, hev.fderiv_eq]
    · simp [gradient, fderiv_of_notMem_tsupport ℝ hx]
  rw [hL, hR']
  exact integral_mul_laplacian_eq_neg_inner_gradient_of_locallyLipschitz hw hwval hφ hc

/-- Compactly supported dilation preserves compact support. -/
private theorem hasCompactSupport_comp_smul {d : ℕ} {ψ : Space d → ℝ}
    (hc : HasCompactSupport ψ) {s : ℝ} (hs : 0 < s) :
    HasCompactSupport (fun z ↦ ψ (s • z)) := by
  obtain ⟨R, hR⟩ := hc.isBounded.subset_closedBall (0 : Space d)
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Space d) (R / s))
  intro z hz
  have hmem : s • z ∈ tsupport ψ := subset_tsupport ψ hz
  have hn : ‖s • z‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hR hmem
  rw [norm_smul, Real.norm_of_nonneg hs.le] at hn
  simpa only [mem_closedBall, dist_zero_right] using (le_div_iff₀ hs).mpr (by linarith)

/-- Microscopic rescalings of a physical translation limit retain the weak subsolution
inequality with scaled reaction `r * f (V (r • x))`. -/
theorem RigidityHypotheses.rescaled_limit_lipschitz_test
    {m : ℕ} {g : Space m → ℝ} {u V ψ : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ r : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {p : ℕ → Space (m + 1)} (hV : LipschitzWith ⟨κ, h.kappa_pos.le⟩ V)
    (hval : ∀ x, V x ∈ Icc 0 1)
    (hlim : ∀ x, Tendsto (fun j ↦ zeroExtension g u (p j + x)) atTop (𝓝 (V x)))
    (hr0 : 0 < r) (hψ : LocallyLipschitz ψ) (hc : HasCompactSupport ψ)
    (hψ0 : ∀ x, 0 ≤ ψ x) :
    (∫ x, inner ℝ (gradient (fun y ↦ V (r • y) / r) x) (gradient ψ x) -
      (r * f (V (r • x))) * ψ x) ≤ 0 := by
  let ψ_r : Space (m + 1) → ℝ := fun z ↦ ψ (r⁻¹ • z)
  have hψ_r : LocallyLipschitz ψ_r := hψ.comp (lipschitzWith_smul r⁻¹).locallyLipschitz
  have hc_r : HasCompactSupport ψ_r := hasCompactSupport_comp_smul hc (inv_pos.mpr hr0)
  have htest := hr.physical_translation_limit_lipschitz_test h hV hval hlim hψ_r hc_r
    (fun z ↦ hψ0 _)
  let F : Space (m + 1) → ℝ := fun z ↦ inner ℝ (gradient V z) (gradient ψ_r z) - f (V z) * ψ_r z
  have hchg := Measure.integral_comp_smul volume F r
  simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul] at hchg
  rw [abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hr0.le (m + 1)))] at hchg
  have hle : (∫ x, F (r • x)) ≤ 0 := by
    rw [hchg]
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (pow_nonneg hr0.le _)) htest
  have hmul := mul_nonpos_of_nonneg_of_nonpos hr0.le hle
  rw [← integral_const_mul] at hmul
  apply le_trans _ hmul
  apply le_of_eq
  apply integral_congr_ae
  refine Eventually.of_forall (fun x ↦ ?_)
  dsimp only [F, ψ_r]
  rw [gradient_rescale_div V hr0.ne' x, gradient_comp_smul ψ (inv_ne_zero hr0.ne') (r • x),
    inv_smul_smul₀ hr0.ne', real_inner_smul_right]
  field_simp

/-- Uniform convergence on a compact set implies local `L¹` convergence. -/
theorem integral_norm_sub_tendsto_of_tendstoUniformlyOn
    {d : ℕ} {v : ℕ → Space d → ℝ} {w : Space d → ℝ} {K : Set (Space d)}
    (hK : IsCompact K) (hv : ∀ j, ContinuousOn (v j) K) (hw : ContinuousOn w K)
    (ht : TendstoUniformlyOn v w atTop K) :
    Tendsto (fun j ↦ ∫ x in K, ‖v j x - w x‖) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ := ε / (volume.real K + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp ht δ hδ] with j hj
  have hi : IntegrableOn (fun x ↦ ‖v j x - w x‖) K :=
    ((hv j).sub hw).norm.integrableOn_compact hK
  have hle : (∫ x in K, ‖v j x - w x‖) ≤ ∫ _x in K, δ := by
    apply setIntegral_mono_on hi (continuousOn_const.integrableOn_compact hK) hK.measurableSet
    intro x hx
    simpa only [dist_eq_norm, norm_sub_rev] using (hj x hx).le
  rw [setIntegral_const, smul_eq_mul] at hle
  have hnonneg : 0 ≤ ∫ x in K, ‖v j x - w x‖ := integral_nonneg (fun _ ↦ norm_nonneg _)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
  have hmul : δ * (volume.real K + 1) = ε := div_mul_cancel₀ ε (by positivity)
  nlinarith

/-- Microscopic blowup sequences have strongly convergent gradients in `L²_loc` on every
compact subset, including across the limiting free boundary. -/
theorem RigidityHypotheses.microscopic_blowup_gradient_tendsto
    {m : ℕ} {g : Space m → ℝ} {u V W_lim : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {p_seq : ℕ → Space (m + 1)} {r_seq : ℕ → ℝ}
    (hV : LipschitzWith ⟨κ, h.kappa_pos.le⟩ V) (hval : ∀ x, V x ∈ Icc 0 1)
    (hlim : ∀ K : Set (Space (m + 1)), IsCompact K →
      TendstoUniformlyOn (fun j x ↦ zeroExtension g u (p_seq j + x)) V atTop K)
    (hr_pos : ∀ j, 0 < r_seq j) (hr_lim : Tendsto r_seq atTop (𝓝 0))
    (hW : LipschitzWith ⟨κ, h.kappa_pos.le⟩ W_lim) (hW0 : ∀ x, 0 ≤ W_lim x)
    (hWlim : ∀ K : Set (Space (m + 1)), IsCompact K →
      TendstoUniformlyOn (fun j x ↦ V (r_seq j • x) / r_seq j) W_lim atTop K)
    {K : Set (Space (m + 1))} (hK : IsCompact K) :
    Tendsto (fun j ↦ ∫ x in K,
      ‖gradient (fun y ↦ V (r_seq j • y) / r_seq j) x - gradient W_lim x‖ ^ 2)
      atTop (𝓝 0) := by
  let v := fun j x ↦ V (r_seq j • x) / r_seq j
  let a := fun j x ↦ r_seq j * f (V (r_seq j • x))
  have hpointV (x : Space (m + 1)) :
      Tendsto (fun j ↦ zeroExtension g u (p_seq j + x)) atTop (𝓝 (V x)) :=
    (hlim {x} isCompact_singleton).tendsto_at (mem_singleton x)
  have hv_lip (j : ℕ) : LipschitzWith ⟨κ, h.kappa_pos.le⟩ (v j) :=
    lipschitzWith_rescale_div hV (hr_pos j)
  have hv0 (j : ℕ) (x : Space (m + 1)) : 0 ≤ v j x :=
    div_nonneg (hval _).1 (hr_pos j).le
  obtain ⟨R_max, hR_max⟩ := isBounded_iff_forall_norm_le.mp
    (isBounded_range_of_tendsto r_seq hr_lim)
  obtain ⟨M_f, hM_f⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (h.reaction_contDiffOn.continuousOn.mono Icc_subset_Ici_self)
  have hR0 : 0 ≤ R_max := (norm_nonneg _).trans (hR_max _ (mem_range_self 0))
  have hM0 : 0 ≤ M_f := (norm_nonneg _).trans (hM_f 0 ⟨le_rfl, zero_le_one⟩)
  let A : ℝ := R_max * M_f
  have ha_cont (j : ℕ) : Continuous (a j) :=
    continuous_const.mul (h.reaction_contDiffOn.continuousOn.comp_continuous
      (hV.continuous.comp (continuous_id.const_smul (r_seq j))) (fun x ↦ (hval _).1))
  have ha_meas (j : ℕ) : Measurable (a j) := (ha_cont j).measurable
  have ha_bound (j : ℕ) (x : Space (m + 1)) : ‖a j x‖ ≤ A := by
    dsimp only [a, A]
    rw [norm_mul]
    exact mul_le_mul (hR_max _ (mem_range_self j)) (hM_f _ (hval _)) (norm_nonneg _) hR0
  have hweak_v (j : ℕ) (ψ : Space (m + 1) → ℝ) (hψ : LocallyLipschitz ψ)
      (hcψ : HasCompactSupport ψ) (hψ0 : ∀ x, 0 ≤ ψ x) :
      (∫ x, inner ℝ (gradient (v j) x) (gradient ψ x) - a j x * ψ x) ≤ 0 :=
    hr.rescaled_limit_lipschitz_test h hV hval hpointV (hr_pos j) hψ hcψ hψ0
  have hweak_W (ψ : Space (m + 1) → ℝ) (hψ : LocallyLipschitz ψ)
      (hcψ : HasCompactSupport ψ) (hψ0 : ∀ x, 0 ≤ ψ x) :
      (∫ x, inner ℝ (gradient W_lim x) (gradient ψ x) - (0 : ℝ) * ψ x) ≤ 0 := by
    have hgradW (x : Space (m + 1)) : ‖gradient W_lim x‖ ≤ κ := by
      rw [gradient, LinearIsometryEquiv.norm_map]
      exact norm_fderiv_le_of_lipschitz ℝ hW
    apply integral_weak_residual_nonpos_of_locallyLipschitz_test (measurable_gradient W_lim)
      measurable_const hgradW (fun _ ↦ show ‖(0 : ℝ)‖ ≤ A by simp [A]; positivity) ?_ hψ hcψ hψ0
    intro φ hφ hcφ hφ0
    simp only [zero_mul, sub_zero]
    rw [← neg_neg (∫ x, inner ℝ (gradient W_lim x) (gradient φ x)),
      ← integral_mul_laplacian_eq_neg_inner_gradient_of_nonneg_lipschitz hW hW0 hφ hcφ,
      neg_nonpos]
    have hlap : Continuous (Δ φ) := continuous_laplacian_of_contDiff hφ
    have hcΔ : HasCompactSupport (Δ φ) := by
      apply hcφ.of_isClosed_subset (isClosed_tsupport _)
      apply closure_minimal _ (isClosed_tsupport φ)
      intro x hx
      by_contra hn
      exact hx (laplacian_zero_off_tsupport φ hn)
    obtain ⟨CΔ, hCΔ⟩ := hcΔ.exists_bound_of_continuous hlap
    obtain ⟨Cφ, hCφ⟩ := hcφ.exists_bound_of_continuous hφ.continuous
    have htU := integral_norm_sub_tendsto_of_tendstoUniformlyOn hcφ
      (fun j ↦ (hv_lip j).continuous.continuousOn) hW.continuous.continuousOn (hWlim _ hcφ)
    have htL := integral_mul_tendsto_of_integral_norm_sub_tendsto (volume.restrict (tsupport φ))
      v W_lim (Δ φ) CΔ
      (fun j ↦ (hv_lip j).continuous.continuousOn.integrableOn_compact hcφ)
      (hW.continuous.continuousOn.integrableOn_compact hcφ)
      hlap.aestronglyMeasurable hCΔ htU
    simp only [setIntegral_mul_laplacian_test] at htL
    have htR : Tendsto (fun j ↦ -(∫ x, a j x * φ x)) atTop (𝓝 0) := by
      have ht0 : Tendsto (fun j ↦ ∫ x in tsupport φ, a j x * φ x) atTop
          (𝓝 (∫ _x in tsupport φ, (0 : ℝ))) := by
        apply tendsto_integral_of_dominated_convergence (fun _ ↦ A * Cφ)
        · exact fun j ↦ ((ha_cont j).mul hφ.continuous).aestronglyMeasurable
        · exact continuousOn_const.integrableOn_compact hcφ
        · intro j
          filter_upwards with x
          rw [norm_mul]
          exact mul_le_mul (ha_bound j x) (hCφ x) (norm_nonneg _) (by dsimp [A]; positivity)
        · filter_upwards with x
          exact squeeze_zero_norm (a := fun j ↦ ‖r_seq j‖ * (M_f * Cφ))
            (fun j ↦ by
              dsimp only [a]
              rw [mul_assoc, norm_mul, norm_mul]
              exact mul_le_mul_of_nonneg_left
                (mul_le_mul (hM_f _ (hval _)) (hCφ x) (norm_nonneg _) hM0) (norm_nonneg _))
            (by simpa using hr_lim.norm.mul_const (M_f * Cφ))
      simp only [setIntegral_mul_test, integral_zero] at ht0
      simpa using ht0.neg
    have hineq (j : ℕ) : -(∫ x, a j x * φ x) ≤ ∫ x, v j x * (Δ φ) x := by
      have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
      have hv_grad (x : Space (m + 1)) : ‖gradient (v j) x‖ ≤ κ := by
        rw [gradient, LinearIsometryEquiv.norm_map]
        exact norm_fderiv_le_of_lipschitz ℝ (hv_lip j)
      have hi_res := integrable_weak_residual_of_locallyLipschitz_test
        (measurable_gradient (v j)) (ha_meas j) hv_grad (ha_bound j)
        hφ1.locallyLipschitz hcφ
      have hi_src : Integrable (fun x ↦ a j x * φ x) :=
        ((ha_cont j).mul hφ.continuous).integrable_of_hasCompactSupport hcφ.mul_left
      have hi_grad : Integrable (fun x ↦ inner ℝ (gradient (v j) x) (gradient φ x)) := by
        apply (hi_res.add hi_src).congr
        exact Eventually.of_forall (fun x ↦ by simp only [Pi.add_apply]; ring)
      have hw := hweak_v j φ hφ1.locallyLipschitz hcφ hφ0
      rw [integral_sub hi_grad hi_src] at hw
      rw [integral_mul_laplacian_eq_neg_inner_gradient_of_nonneg_lipschitz
        (hv_lip j) (hv0 j) hφ hcφ]
      linarith
    exact le_of_tendsto_of_tendsto' htR htL hineq
  obtain ⟨R, hR, hKR⟩ := hK.isBounded.subset_ball_lt 0 (0 : Space (m + 1))
  let φ : ContDiffBump (0 : Space (m + 1)) :=
    { rIn := R, rOut := R + 1, rIn_pos := hR, rIn_lt_rOut := by linarith }
  have hone (x : Space (m + 1)) (hx : x ∈ K) : φ x = 1 :=
    φ.one_of_mem_closedBall (ball_subset_closedBall (hKR hx))
  have hKφ : K ⊆ tsupport (φ : Space (m + 1) → ℝ) := by
    intro x hx
    exact subset_tsupport _ (by change φ x ≠ 0; rw [hone x hx]; norm_num)
  have ht := integral_cutoff_gradient_sub_sq_tendsto hv_lip hW ha_meas measurable_const
    ha_bound (fun _ ↦ show ‖(0 : ℝ)‖ ≤ A by simp [A]; positivity)
    hweak_v hweak_W φ.contDiff φ.hasCompactSupport (fun _ ↦ ⟨φ.nonneg, φ.le_one⟩)
    (hWlim _ φ.hasCompactSupport)
  apply squeeze_zero (fun _ ↦ integral_nonneg (fun _ ↦ sq_nonneg _)) _ ht
  intro j
  have hi := (integrableOn_gradient_sub_sq_of_lipschitz (hv_lip j) hW φ.hasCompactSupport).bdd_mul
    φ.continuous.aestronglyMeasurable
    (Eventually.of_forall (fun x ↦ show ‖(φ : Space (m + 1) → ℝ) x‖ ≤ 1 by
      rw [Real.norm_of_nonneg φ.nonneg]; exact φ.le_one))
  have he : (∫ x in K, ‖gradient (v j) x - gradient W_lim x‖ ^ 2) =
      ∫ x in K, φ x * ‖gradient (v j) x - gradient W_lim x‖ ^ 2 := by
    apply setIntegral_congr_fun hK.measurableSet
    intro x hx
    simp only [hone x hx, one_mul]
  rw [he]
  exact setIntegral_mono_set hi
    (Eventually.of_forall (fun _ ↦ mul_nonneg φ.nonneg (sq_nonneg _)))
    (Eventually.of_forall hKφ)

/-- Microscopic rescalings satisfy the rescaled scalar stationarity identity. -/
theorem RigidityHypotheses.rescaled_limit_scalar_stationarity
    {m : ℕ} {g : Space m → ℝ} {u V η : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ r : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {p : ℕ → Space (m + 1)} (hV : LipschitzWith ⟨κ, h.kappa_pos.le⟩ V)
    (hval : ∀ x, V x ∈ Icc 0 1)
    (hlim : ∀ K : Set (Space (m + 1)), IsCompact K →
      TendstoUniformlyOn (fun j x ↦ zeroExtension g u (p j + x)) V atTop K)
    (hr0 : 0 < r) (hη : ContDiff ℝ 1 η) (hc : HasCompactSupport η) :
    (∫ x, η x * (‖gradient (fun y ↦ V (r • y) / r) x‖ ^ 2 -
      (V (r • x) / r) * (r * f (V (r • x)))) +
      (V (r • x) / r) * inner ℝ (gradient (fun y ↦ V (r • y) / r) x) (gradient η x)) = 0 := by
  let η_r : Space (m + 1) → ℝ := fun z ↦ η (r⁻¹ • z)
  have hη_r : ContDiff ℝ 1 η_r := hη.comp (contDiff_id.const_smul r⁻¹)
  have hc_r : HasCompactSupport η_r := hasCompactSupport_comp_smul hc (inv_pos.mpr hr0)
  have hst := hr.physical_translation_limit_scalar_stationarity h hV hval hlim hη_r hc_r
  let F : Space (m + 1) → ℝ := fun z ↦
    η_r z * (‖gradient V z‖ ^ 2 - V z * f (V z)) + V z * inner ℝ (gradient V z) (gradient η_r z)
  have hchg := Measure.integral_comp_smul volume F r
  simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul] at hchg
  rw [abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hr0.le (m + 1)))] at hchg
  have hz : (∫ x, F (r • x)) = 0 := by
    rw [hchg, hst, mul_zero]
  rw [← hz]
  apply integral_congr_ae
  refine Eventually.of_forall (fun x ↦ ?_)
  dsimp only [F, η_r]
  rw [gradient_rescale_div V hr0.ne' x, gradient_comp_smul η (inv_ne_zero hr0.ne') (r • x),
    inv_smul_smul₀ hr0.ne', real_inner_smul_right]
  field_simp

/-- Microscopic rescalings satisfy the first-order weak PDE on their positive phase. -/
theorem RigidityHypotheses.rescaled_limit_weak_equation
    {m : ℕ} {g : Space m → ℝ} {u V η : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ r : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {p : ℕ → Space (m + 1)} (hV : LipschitzWith ⟨κ, h.kappa_pos.le⟩ V)
    (hval : ∀ x, V x ∈ Icc 0 1)
    (hlim : ∀ K : Set (Space (m + 1)), IsCompact K →
      TendstoUniformlyOn (fun j x ↦ zeroExtension g u (p j + x)) V atTop K)
    (hr0 : 0 < r) (hη : ContDiff ℝ 1 η) (hc : HasCompactSupport η)
    (hs : ∀ x ∈ tsupport η, 0 < V (r • x) / r) :
    (∫ x, inner ℝ (gradient (fun y ↦ V (r • y) / r) x) (gradient η x)) =
      ∫ x, (r * f (V (r • x))) * η x := by
  let η_r : Space (m + 1) → ℝ := fun z ↦ η (r⁻¹ • z)
  have hη_r : ContDiff ℝ 1 η_r := hη.comp (contDiff_id.const_smul r⁻¹)
  have hc_r : HasCompactSupport η_r := hasCompactSupport_comp_smul hc (inv_pos.mpr hr0)
  have hs_r : tsupport η_r ⊆ {z | 0 < V z} := by
    intro z hz
    have hmem : r⁻¹ • z ∈ tsupport η :=
      tsupport_comp_subset_preimage η (continuous_id.const_smul r⁻¹) hz
    have hpos := hs (r⁻¹ • z) hmem
    rw [smul_inv_smul₀ hr0.ne', div_pos_iff_of_pos_right hr0] at hpos
    exact hpos
  have heq := hr.physical_translation_limit_weak_equation h hV hval hlim hη_r hc_r hs_r
  let FL : Space (m + 1) → ℝ := fun z ↦ inner ℝ (gradient V z) (gradient η_r z)
  let FR : Space (m + 1) → ℝ := fun z ↦ f (V z) * η_r z
  have hchgL := Measure.integral_comp_smul volume FL r
  have hchgR := Measure.integral_comp_smul volume FR r
  simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul] at hchgL hchgR
  rw [abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hr0.le (m + 1)))] at hchgL hchgR
  have heq' : (∫ x, FL (r • x)) = ∫ x, FR (r • x) := by
    rw [hchgL, hchgR, heq]
  have hmul := congrArg (fun t ↦ r * t) heq'
  change r * (∫ x, FL (r • x)) = r * ∫ x, FR (r • x) at hmul
  rw [← integral_const_mul, ← integral_const_mul] at hmul
  convert hmul using 1
  · apply integral_congr_ae
    refine Eventually.of_forall (fun x ↦ ?_)
    dsimp only [FL, η_r]
    rw [gradient_rescale_div V hr0.ne' x, gradient_comp_smul η (inv_ne_zero hr0.ne') (r • x),
      inv_smul_smul₀ hr0.ne', real_inner_smul_right]
    field_simp
  · apply integral_congr_ae
    refine Eventually.of_forall (fun x ↦ ?_)
    dsimp only [FR, η_r]
    rw [inv_smul_smul₀ hr0.ne']
    ring

/-- Every microscopic blowup limit satisfies the global truncated harmonic identity. -/
theorem RigidityHypotheses.microscopic_blowup_truncated_harmonic
    {m : ℕ} {g : Space m → ℝ} {u V W_lim η : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {p_seq : ℕ → Space (m + 1)} {r_seq : ℕ → ℝ}
    (hV : LipschitzWith ⟨κ, h.kappa_pos.le⟩ V) (hval : ∀ x, V x ∈ Icc 0 1)
    (hlim : ∀ K : Set (Space (m + 1)), IsCompact K →
      TendstoUniformlyOn (fun j x ↦ zeroExtension g u (p_seq j + x)) V atTop K)
    (hr_pos : ∀ j, 0 < r_seq j) (hr_lim : Tendsto r_seq atTop (𝓝 0))
    (hW : LipschitzWith ⟨κ, h.kappa_pos.le⟩ W_lim) (hW0 : ∀ x, 0 ≤ W_lim x)
    (hWlim : ∀ K : Set (Space (m + 1)), IsCompact K →
      TendstoUniformlyOn (fun j x ↦ V (r_seq j • x) / r_seq j) W_lim atTop K)
    (hη : ContDiff ℝ 1 η) (hc : HasCompactSupport η) :
    (∫ x, η x * ‖gradient W_lim x‖ ^ 2 +
      W_lim x * inner ℝ (gradient W_lim x) (gradient η x)) = 0 := by
  let K := tsupport η
  let v := fun j x ↦ V (r_seq j • x) / r_seq j
  have hK : IsCompact K := hc
  have hv_lip (j : ℕ) : LipschitzWith ⟨κ, h.kappa_pos.le⟩ (v j) :=
    lipschitzWith_rescale_div hV (hr_pos j)
  have hgrad_sq := hr.microscopic_blowup_gradient_tendsto h hV hval hlim hr_pos hr_lim
    hW hW0 hWlim hK
  have hgrad_L1 : Tendsto (fun j ↦ ∫ x in K, ‖gradient (v j) x - gradient W_lim x‖)
      atTop (𝓝 0) :=
    integral_norm_tendsto_zero_of_square_tendsto_zero hK
      (fun j ↦ integrableOn_gradient_sub_sq_of_lipschitz (hv_lip j) hW hK) hgrad_sq
  have hv_gbound (j : ℕ) (x : Space (m + 1)) : ‖gradient (v j) x‖ ≤ κ := by
    rw [gradient, LinearIsometryEquiv.norm_map]
    exact norm_fderiv_le_of_lipschitz ℝ (hv_lip j)
  have hW_gbound (x : Space (m + 1)) : ‖gradient W_lim x‖ ≤ κ := by
    rw [gradient, LinearIsometryEquiv.norm_map]
    exact norm_fderiv_le_of_lipschitz ℝ hW
  have hkin_tendsto : Tendsto (fun j ↦ ∫ x in K,
      ‖‖gradient (v j) x‖ ^ 2 - ‖gradient W_lim x‖ ^ 2‖) atTop (𝓝 0) := by
    have ht := integral_norm_quadratic_sub_tendsto
      (fun j ↦ measurable_gradient (v j)) (measurable_gradient W_lim)
      (B := fun _ ↦ ContinuousLinearMap.id ℝ (Space (m + 1))) continuous_const
      hv_gbound hW_gbound (fun _ ↦ ContinuousLinearMap.norm_id_le) hK hgrad_L1
    simpa only [ContinuousLinearMap.id_apply, real_inner_self_eq_norm_sq] using ht
  obtain ⟨Cη, hCη⟩ := hc.exists_bound_of_continuous hη.continuous
  have ht1 := integral_mul_tendsto_of_integral_norm_sub_tendsto (volume.restrict K)
    (fun j x ↦ ‖gradient (v j) x‖ ^ 2) (fun x ↦ ‖gradient W_lim x‖ ^ 2) η Cη
    (fun j ↦ integrableOn_gradient_sq_of_locallyLipschitz (hv_lip j).locallyLipschitz hK)
    (integrableOn_gradient_sq_of_locallyLipschitz hW.locallyLipschitz hK)
    hη.continuous.aestronglyMeasurable hCη hkin_tendsto
  obtain ⟨M_f, hM_f⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (h.reaction_contDiffOn.continuousOn.mono Icc_subset_Ici_self)
  have hM0 : 0 ≤ M_f := (norm_nonneg _).trans (hM_f 0 ⟨le_rfl, zero_le_one⟩)
  obtain ⟨R_max, hR_max⟩ := isBounded_iff_forall_norm_le.mp
    (isBounded_range_of_tendsto r_seq hr_lim)
  have hR0 : 0 ≤ R_max := (norm_nonneg _).trans (hR_max _ (mem_range_self 0))
  obtain ⟨BW, hBW⟩ := hK.exists_bound_of_continuousOn hW.continuous.continuousOn
  have ht2 : Tendsto (fun j ↦ ∫ x in K,
      η x * (v j x * (r_seq j * f (V (r_seq j • x))))) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hclose := Metric.tendstoUniformlyOn_iff.mp (hWlim K hK) 1 zero_lt_one
    have hsmall : ∀ᶠ j in atTop,
        ‖r_seq j‖ * ((|BW| + 1) * M_f * |Cη| * volume.real K) < ε := by
      have ht := hr_lim.norm.mul_const ((|BW| + 1) * M_f * |Cη| * volume.real K)
      simp only [norm_zero, zero_mul] at ht
      exact ht.eventually (Iio_mem_nhds hε)
    filter_upwards [hclose, hsmall] with j hj hjs
    have hfcont : Continuous (fun x ↦ f (V (r_seq j • x))) :=
      h.reaction_contDiffOn.continuousOn.comp_continuous
        (hV.continuous.comp (continuous_id.const_smul (r_seq j))) (fun x ↦ (hval _).1)
    have hi : IntegrableOn (fun x ↦ η x * (v j x * (r_seq j * f (V (r_seq j • x))))) K :=
      (hη.continuous.mul ((hv_lip j).continuous.mul
        (continuous_const.mul hfcont))).continuousOn.integrableOn_compact hK
    have hpt (x : Space (m + 1)) (hx : x ∈ K) :
        ‖η x * (v j x * (r_seq j * f (V (r_seq j • x))))‖ ≤
          ‖r_seq j‖ * ((|BW| + 1) * M_f * |Cη|) := by
      have hvx : ‖v j x‖ ≤ |BW| + 1 := by
        have hd := hj x hx
        rw [dist_comm, dist_eq_norm] at hd
        have hw := (hBW x hx).trans (le_abs_self BW)
        linarith [norm_sub_norm_le (v j x) (W_lim x)]
      rw [norm_mul, norm_mul, norm_mul]
      have h1 : ‖η x‖ ≤ |Cη| := (hCη x).trans (le_abs_self Cη)
      have h2 : ‖f (V (r_seq j • x))‖ ≤ M_f := hM_f _ (hval _)
      have hprod := mul_le_mul h1 (mul_le_mul hvx
        (mul_le_mul_of_nonneg_left h2 (norm_nonneg (r_seq j)))
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by positivity))
        (mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))) (abs_nonneg Cη)
      calc
        ‖η x‖ * (‖v j x‖ * (‖r_seq j‖ * ‖f (V (r_seq j • x))‖)) ≤
          |Cη| * ((|BW| + 1) * (‖r_seq j‖ * M_f)) := hprod
        _ = ‖r_seq j‖ * ((|BW| + 1) * M_f * |Cη|) := by ring
    have hle : ‖∫ x in K, η x * (v j x * (r_seq j * f (V (r_seq j • x))))‖ ≤
        ‖r_seq j‖ * ((|BW| + 1) * M_f * |Cη| * volume.real K) := by
      calc
        _ ≤ ∫ x in K, ‖η x * (v j x * (r_seq j * f (V (r_seq j • x))))‖ :=
          norm_integral_le_integral_norm _
        _ ≤ ∫ _x in K, ‖r_seq j‖ * ((|BW| + 1) * M_f * |Cη|) :=
          setIntegral_mono_on hi.norm (continuousOn_const.integrableOn_compact hK)
            hK.measurableSet hpt
        _ = ‖r_seq j‖ * ((|BW| + 1) * M_f * |Cη| * volume.real K) := by
          rw [setIntegral_const, smul_eq_mul]
          ring
    simpa only [dist_zero_right] using hle.trans_lt hjs
  have hgradη : Continuous (gradient η) :=
    (toDual ℝ (Space (m + 1))).symm.continuous.comp (hη.continuous_fderiv one_ne_zero)
  have hsgrad : tsupport (gradient η) ⊆ K := by
    apply closure_minimal _ (isClosed_tsupport η)
    intro x hx
    by_contra hn
    exact hx (by simp [gradient, fderiv_of_notMem_tsupport ℝ hn])
  obtain ⟨D, hD⟩ := (HasCompactSupport.of_support_subset_isCompact hK
    ((subset_tsupport _).trans hsgrad)).exists_bound_of_continuous hgradη
  have htU := integral_norm_sub_tendsto_of_tendstoUniformlyOn hK
    (fun j ↦ (hv_lip j).continuous.continuousOn) hW.continuous.continuousOn (hWlim K hK)
  have hi3j (j : ℕ) : IntegrableOn
      (fun x ↦ v j x * inner ℝ (gradient (v j) x) (gradient η x)) K := by
    obtain ⟨Bv, hBv⟩ := hK.exists_bound_of_continuousOn (hv_lip j).continuous.continuousOn
    apply (continuousOn_const.integrableOn_compact hK (f := fun _ ↦ |Bv| * (κ * |D|))).mono'
      ((hv_lip j).continuous.measurable.mul
        ((measurable_gradient (v j)).inner (𝕜 := ℝ) hgradη.measurable)).aestronglyMeasurable
    filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
    simp only [Pi.mul_apply]
    rw [norm_mul]
    exact mul_le_mul ((hBv x hx).trans (le_abs_self Bv))
      ((norm_inner_le_norm (𝕜 := ℝ) _ _).trans
        (mul_le_mul (hv_gbound j x) ((hD x).trans (le_abs_self D)) (norm_nonneg _) h.kappa_pos.le))
      (norm_nonneg _) (abs_nonneg Bv)
  have hi3W : IntegrableOn
      (fun x ↦ W_lim x * inner ℝ (gradient W_lim x) (gradient η x)) K := by
    apply (continuousOn_const.integrableOn_compact hK (f := fun _ ↦ |BW| * (κ * |D|))).mono'
      (hW.continuous.measurable.mul
        ((measurable_gradient W_lim).inner (𝕜 := ℝ) hgradη.measurable)).aestronglyMeasurable
    filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
    simp only [Pi.mul_apply]
    rw [norm_mul]
    exact mul_le_mul ((hBW x hx).trans (le_abs_self BW))
      ((norm_inner_le_norm (𝕜 := ℝ) _ _).trans
        (mul_le_mul (hW_gbound x) ((hD x).trans (le_abs_self D)) (norm_nonneg _) h.kappa_pos.le))
      (norm_nonneg _) (abs_nonneg BW)
  have ht3 : Tendsto (fun j ↦ ∫ x in K,
      v j x * inner ℝ (gradient (v j) x) (gradient η x)) atTop
      (𝓝 (∫ x in K, W_lim x * inner ℝ (gradient W_lim x) (gradient η x))) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have hmaj := (htU.const_mul (κ * |D|)).add (hgrad_L1.const_mul (|BW| * |D|))
    simp only [mul_zero, add_zero] at hmaj
    apply squeeze_zero (fun _ ↦ norm_nonneg _) _ hmaj
    intro j
    rw [← integral_sub (hi3j j) hi3W]
    have hiU : IntegrableOn (fun x ↦ ‖v j x - W_lim x‖) K :=
      ((hv_lip j).continuous.sub hW.continuous).norm.continuousOn.integrableOn_compact hK
    have hiG : IntegrableOn (fun x ↦ ‖gradient (v j) x - gradient W_lim x‖) K := by
      apply (continuousOn_const.integrableOn_compact hK (f := fun _ ↦ 2 * κ)).mono'
        ((measurable_gradient (v j)).sub (measurable_gradient W_lim)).norm.aestronglyMeasurable
      filter_upwards with x
      rw [norm_norm]
      exact (norm_sub_le _ _).trans (by linarith [hv_gbound j x, hW_gbound x])
    calc
      ‖∫ x in K, v j x * inner ℝ (gradient (v j) x) (gradient η x) -
          W_lim x * inner ℝ (gradient W_lim x) (gradient η x)‖ ≤
        ∫ x in K, ‖v j x * inner ℝ (gradient (v j) x) (gradient η x) -
          W_lim x * inner ℝ (gradient W_lim x) (gradient η x)‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ x in K, (κ * |D|) * ‖v j x - W_lim x‖ +
          (|BW| * |D|) * ‖gradient (v j) x - gradient W_lim x‖ := by
        apply setIntegral_mono_on ((hi3j j).sub hi3W).norm
          ((hiU.const_mul _).add (hiG.const_mul _)) hK.measurableSet
        intro x hx
        simp only [Pi.sub_apply, Pi.add_apply]
        have hsplit : v j x * inner ℝ (gradient (v j) x) (gradient η x) -
            W_lim x * inner ℝ (gradient W_lim x) (gradient η x) =
            (v j x - W_lim x) * inner ℝ (gradient (v j) x) (gradient η x) +
            W_lim x * inner ℝ (gradient (v j) x - gradient W_lim x) (gradient η x) := by
          rw [inner_sub_left]
          ring
        rw [hsplit]
        apply (norm_add_le _ _).trans
        apply add_le_add
        · rw [norm_mul]
          have hin : ‖inner ℝ (gradient (v j) x) (gradient η x)‖ ≤ κ * |D| :=
            (norm_inner_le_norm (𝕜 := ℝ) _ _).trans
              (mul_le_mul (hv_gbound j x) ((hD x).trans (le_abs_self D))
                (norm_nonneg _) h.kappa_pos.le)
          exact (mul_le_mul_of_nonneg_left hin (norm_nonneg _)).trans_eq (mul_comm _ _)
        · rw [norm_mul]
          have hin : ‖inner ℝ (gradient (v j) x - gradient W_lim x) (gradient η x)‖ ≤
              ‖gradient (v j) x - gradient W_lim x‖ * |D| :=
            (norm_inner_le_norm (𝕜 := ℝ) _ _).trans
              (mul_le_mul_of_nonneg_left ((hD x).trans (le_abs_self D)) (norm_nonneg _))
          have hw := (hBW x hx).trans (le_abs_self BW)
          calc
            ‖W_lim x‖ * ‖inner ℝ (gradient (v j) x - gradient W_lim x) (gradient η x)‖ ≤
              |BW| * (‖gradient (v j) x - gradient W_lim x‖ * |D|) :=
                mul_le_mul hw hin (norm_nonneg _) (abs_nonneg BW)
            _ = (|BW| * |D|) * ‖gradient (v j) x - gradient W_lim x‖ := by ring
      _ = (κ * |D|) * (∫ x in K, ‖v j x - W_lim x‖) +
          (|BW| * |D|) * ∫ x in K, ‖gradient (v j) x - gradient W_lim x‖ := by
        rw [integral_add (hiU.const_mul _) (hiG.const_mul _), integral_const_mul,
          integral_const_mul]
  have ht_all := (ht1.sub ht2).add ht3
  simp only [sub_zero] at ht_all
  have hz (j : ℕ) :
      (∫ x in K, ‖gradient (v j) x‖ ^ 2 * η x) -
        (∫ x in K, η x * (v j x * (r_seq j * f (V (r_seq j • x))))) +
        (∫ x in K, v j x * inner ℝ (gradient (v j) x) (gradient η x)) = 0 := by
    have hi1 : IntegrableOn (fun x ↦ ‖gradient (v j) x‖ ^ 2 * η x) K :=
      (integrableOn_gradient_sq_of_locallyLipschitz (hv_lip j).locallyLipschitz
        hK).mul_continuousOn hη.continuous.continuousOn hK
    have hfcont : Continuous (fun x ↦ f (V (r_seq j • x))) :=
      h.reaction_contDiffOn.continuousOn.comp_continuous
        (hV.continuous.comp (continuous_id.const_smul (r_seq j))) (fun x ↦ (hval _).1)
    have hi2 : IntegrableOn (fun x ↦ η x * (v j x * (r_seq j * f (V (r_seq j • x))))) K :=
      (hη.continuous.mul ((hv_lip j).continuous.mul
        (continuous_const.mul hfcont))).continuousOn.integrableOn_compact hK
    have hsub := integral_sub hi1 hi2
    have hadd := integral_add (hi1.sub hi2) (hi3j j)
    simp only [Pi.sub_apply] at hsub hadd
    have heq : (∫ x in K, ‖gradient (v j) x‖ ^ 2 * η x -
          η x * (v j x * (r_seq j * f (V (r_seq j • x)))) +
          v j x * inner ℝ (gradient (v j) x) (gradient η x)) =
        ∫ x, η x * (‖gradient (v j) x‖ ^ 2 -
          v j x * (r_seq j * f (V (r_seq j • x)))) +
          v j x * inner ℝ (gradient (v j) x) (gradient η x) := by
      trans (∫ x in K, η x * (‖gradient (v j) x‖ ^ 2 -
          v j x * (r_seq j * f (V (r_seq j • x)))) +
          v j x * inner ℝ (gradient (v j) x) (gradient η x))
      · exact setIntegral_congr_fun hK.measurableSet (fun x _ ↦ by ring)
      · exact setIntegral_eq_integral_of_forall_compl_eq_zero (s := K) (fun x hx ↦ by
          simp [image_eq_zero_of_notMem_tsupport hx, gradient,
            fderiv_of_notMem_tsupport ℝ hx])
    have hst : (∫ x, η x * (‖gradient (v j) x‖ ^ 2 -
        v j x * (r_seq j * f (V (r_seq j • x)))) +
        v j x * inner ℝ (gradient (v j) x) (gradient η x)) = 0 :=
      hr.rescaled_limit_scalar_stationarity h hV hval hlim (hr_pos j) hη hc
    linarith
  have hzero := tendsto_nhds_unique
    (tendsto_const_nhds.congr' (Eventually.of_forall (fun j ↦ (hz j).symm))) ht_all
  have hi1W : IntegrableOn (fun x ↦ ‖gradient W_lim x‖ ^ 2 * η x) K :=
    (integrableOn_gradient_sq_of_locallyLipschitz hW.locallyLipschitz hK).mul_continuousOn
      hη.continuous.continuousOn hK
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := K) (fun x hx ↦ by
    simp [image_eq_zero_of_notMem_tsupport hx, gradient, fderiv_of_notMem_tsupport ℝ hx])]
  have haddW := integral_add hi1W hi3W
  have heqW : (∫ x in K, η x * ‖gradient W_lim x‖ ^ 2 +
        W_lim x * inner ℝ (gradient W_lim x) (gradient η x)) =
      ∫ x in K, ‖gradient W_lim x‖ ^ 2 * η x +
        W_lim x * inner ℝ (gradient W_lim x) (gradient η x) :=
    setIntegral_congr_fun hK.measurableSet (fun x _ ↦ by ring)
  linarith

/-- Every microscopic blowup limit is weakly harmonic on its open positive phase. -/
theorem RigidityHypotheses.microscopic_blowup_weak_harmonic
    {m : ℕ} {g : Space m → ℝ} {u V W_lim η : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {p_seq : ℕ → Space (m + 1)} {r_seq : ℕ → ℝ}
    (hV : LipschitzWith ⟨κ, h.kappa_pos.le⟩ V) (hval : ∀ x, V x ∈ Icc 0 1)
    (hlim : ∀ K : Set (Space (m + 1)), IsCompact K →
      TendstoUniformlyOn (fun j x ↦ zeroExtension g u (p_seq j + x)) V atTop K)
    (hr_pos : ∀ j, 0 < r_seq j) (hr_lim : Tendsto r_seq atTop (𝓝 0))
    (hW : LipschitzWith ⟨κ, h.kappa_pos.le⟩ W_lim) (hW0 : ∀ x, 0 ≤ W_lim x)
    (hWlim : ∀ K : Set (Space (m + 1)), IsCompact K →
      TendstoUniformlyOn (fun j x ↦ V (r_seq j • x) / r_seq j) W_lim atTop K)
    (hη : ContDiff ℝ 1 η) (hc : HasCompactSupport η)
    (hs : tsupport η ⊆ {x | 0 < W_lim x}) :
    (∫ x, inner ℝ (gradient W_lim x) (gradient η x)) = 0 := by
  let K := tsupport η
  let v := fun j x ↦ V (r_seq j • x) / r_seq j
  have hK : IsCompact K := hc
  have hv_lip (j : ℕ) : LipschitzWith ⟨κ, h.kappa_pos.le⟩ (v j) :=
    lipschitzWith_rescale_div hV (hr_pos j)
  have hgrad_sq := hr.microscopic_blowup_gradient_tendsto h hV hval hlim hr_pos hr_lim
    hW hW0 hWlim hK
  have hgrad_L1 : Tendsto (fun j ↦ ∫ x in K, ‖gradient (v j) x - gradient W_lim x‖)
      atTop (𝓝 0) :=
    integral_norm_tendsto_zero_of_square_tendsto_zero hK
      (fun j ↦ integrableOn_gradient_sub_sq_of_lipschitz (hv_lip j) hW hK) hgrad_sq
  have hgradη : Continuous (gradient η) :=
    (toDual ℝ (Space (m + 1))).symm.continuous.comp (hη.continuous_fderiv one_ne_zero)
  have hsgrad : tsupport (gradient η) ⊆ K := by
    apply closure_minimal _ (isClosed_tsupport η)
    intro x hx
    by_contra hn
    exact hx (by simp [gradient, fderiv_of_notMem_tsupport ℝ hn])
  obtain ⟨D, hD⟩ := (HasCompactSupport.of_support_subset_isCompact hK
    ((subset_tsupport _).trans hsgrad)).exists_bound_of_continuous hgradη
  have hv_gbound (j : ℕ) (x : Space (m + 1)) : ‖gradient (v j) x‖ ≤ κ := by
    rw [gradient, LinearIsometryEquiv.norm_map]
    exact norm_fderiv_le_of_lipschitz ℝ (hv_lip j)
  have hW_gbound (x : Space (m + 1)) : ‖gradient W_lim x‖ ≤ κ := by
    rw [gradient, LinearIsometryEquiv.norm_map]
    exact norm_fderiv_le_of_lipschitz ℝ hW
  have hij (j : ℕ) : IntegrableOn (fun x ↦ inner ℝ (gradient (v j) x) (gradient η x)) K := by
    apply (continuousOn_const.integrableOn_compact hK (f := fun _ ↦ κ * |D|)).mono'
      ((measurable_gradient (v j)).inner (𝕜 := ℝ) hgradη.measurable).aestronglyMeasurable
    filter_upwards with x
    exact (norm_inner_le_norm (𝕜 := ℝ) _ _).trans
      (mul_le_mul (hv_gbound j x) ((hD x).trans (le_abs_self D)) (norm_nonneg _) h.kappa_pos.le)
  have hiW : IntegrableOn (fun x ↦ inner ℝ (gradient W_lim x) (gradient η x)) K := by
    apply (continuousOn_const.integrableOn_compact hK (f := fun _ ↦ κ * |D|)).mono'
      ((measurable_gradient W_lim).inner (𝕜 := ℝ) hgradη.measurable).aestronglyMeasurable
    filter_upwards with x
    exact (norm_inner_le_norm (𝕜 := ℝ) _ _).trans
      (mul_le_mul (hW_gbound x) ((hD x).trans (le_abs_self D)) (norm_nonneg _) h.kappa_pos.le)
  have htL : Tendsto (fun j ↦ ∫ x, inner ℝ (gradient (v j) x) (gradient η x)) atTop
      (𝓝 (∫ x, inner ℝ (gradient W_lim x) (gradient η x))) := by
    have hcut (r : Space (m + 1) → Space (m + 1)) :
        (∫ x in K, inner ℝ (r x) (gradient η x)) = ∫ x, inner ℝ (r x) (gradient η x) := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      simp [gradient, fderiv_of_notMem_tsupport ℝ hx]
    simp_rw [← hcut]
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have hmaj := hgrad_L1.const_mul |D|
    simp only [mul_zero] at hmaj
    apply squeeze_zero (fun _ ↦ norm_nonneg _) _ hmaj
    intro j
    have hiG : IntegrableOn (fun x ↦ ‖gradient (v j) x - gradient W_lim x‖) K := by
      apply (continuousOn_const.integrableOn_compact hK (f := fun _ ↦ 2 * κ)).mono'
        ((measurable_gradient (v j)).sub (measurable_gradient W_lim)).norm.aestronglyMeasurable
      filter_upwards with x
      rw [norm_norm]
      exact (norm_sub_le _ _).trans (by linarith [hv_gbound j x, hW_gbound x])
    rw [← integral_sub (hij j) hiW]
    calc
      ‖∫ x in K, inner ℝ (gradient (v j) x) (gradient η x) -
          inner ℝ (gradient W_lim x) (gradient η x)‖ ≤
        ∫ x in K, ‖inner ℝ (gradient (v j) x - gradient W_lim x) (gradient η x)‖ := by
        simpa only [inner_sub_left] using norm_integral_le_integral_norm _
      _ ≤ ∫ x in K, |D| * ‖gradient (v j) x - gradient W_lim x‖ := by
        apply integral_mono (((hij j).sub hiW).congr
          (Eventually.of_forall (fun _ ↦ (inner_sub_left _ _ _).symm))).norm (hiG.const_mul |D|)
        intro x
        exact ((norm_inner_le_norm (𝕜 := ℝ) _ _).trans
          (mul_le_mul_of_nonneg_left ((hD x).trans (le_abs_self D)) (norm_nonneg _))).trans_eq
          (mul_comm _ _)
      _ = |D| * ∫ x in K, ‖gradient (v j) x - gradient W_lim x‖ := integral_const_mul _ _
  obtain ⟨M_f, hM_f⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (h.reaction_contDiffOn.continuousOn.mono Icc_subset_Ici_self)
  have hM0 : 0 ≤ M_f := (norm_nonneg _).trans (hM_f 0 ⟨le_rfl, zero_le_one⟩)
  obtain ⟨Cη, hCη⟩ := hc.exists_bound_of_continuous hη.continuous
  obtain ⟨R_max, hR_max⟩ := isBounded_iff_forall_norm_le.mp
    (isBounded_range_of_tendsto r_seq hr_lim)
  have hR0 : 0 ≤ R_max := (norm_nonneg _).trans (hR_max _ (mem_range_self 0))
  have htR : Tendsto (fun j ↦ ∫ x, (r_seq j * f (V (r_seq j • x))) * η x) atTop (𝓝 0) := by
    have ht0 : Tendsto (fun j ↦ ∫ x in K, (r_seq j * f (V (r_seq j • x))) * η x) atTop
        (𝓝 (∫ _x in K, (0 : ℝ))) := by
      apply tendsto_integral_of_dominated_convergence (fun _ ↦ R_max * M_f * |Cη|)
      · intro j
        have hfcont : Continuous (fun x ↦ f (V (r_seq j • x))) :=
          h.reaction_contDiffOn.continuousOn.comp_continuous
            (hV.continuous.comp (continuous_id.const_smul (r_seq j))) (fun x ↦ (hval _).1)
        exact ((continuous_const.mul hfcont).mul hη.continuous).aestronglyMeasurable
      · exact continuousOn_const.integrableOn_compact hK
      · intro j
        filter_upwards with x
        rw [norm_mul, norm_mul]
        exact mul_le_mul (mul_le_mul (hR_max _ (mem_range_self j)) (hM_f _ (hval _))
          (norm_nonneg _) hR0) ((hCη x).trans (le_abs_self Cη)) (norm_nonneg _)
          (mul_nonneg hR0 hM0)
      · filter_upwards with x
        exact squeeze_zero_norm (a := fun j ↦ ‖r_seq j‖ * (M_f * |Cη|))
          (fun j ↦ by
            rw [mul_assoc, norm_mul, norm_mul]
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul (hM_f _ (hval _)) ((hCη x).trans (le_abs_self Cη))
                (norm_nonneg _) hM0) (norm_nonneg _))
          (by simpa using hr_lim.norm.mul_const (M_f * |Cη|))
    simpa only [K, setIntegral_mul_test, integral_zero] using ht0
  have hpos := eventually_positive_on_compact_of_tendstoUniformlyOn hK
    hW.continuous.continuousOn hs (hWlim K hK)
  apply tendsto_nhds_unique htL
  apply htR.congr'
  filter_upwards [hpos] with j hj
  exact (hr.rescaled_limit_weak_equation h hV hval hlim (hr_pos j) hη hc hj).symm

/-- Nonnegative Lipschitz functions vanishing at the origin admit a locally uniformly
convergent subsequence on all of Euclidean space. -/
theorem exists_locally_uniform_subsequence_of_lipschitz_zero {d : ℕ}
    (F : ℕ → Space d → ℝ) {L : ℝ≥0}
    (hL : ∀ j, LipschitzWith L (F j)) (h0 : ∀ j, F j 0 = 0)
    (hnonneg : ∀ j x, 0 ≤ F j x) :
    ∃ (φ : ℕ → ℕ) (W : Space d → ℝ), StrictMono φ ∧ LipschitzWith L W ∧
      W 0 = 0 ∧ (∀ x, 0 ≤ W x) ∧
      ∀ K : Set (Space d), IsCompact K →
        TendstoUniformlyOn (fun j ↦ F (φ j)) W atTop K := by
  let X (k : ℕ) := closedBall (0 : Space d) (k + 1 : ℝ)
  let : ∀ k, CompactSpace (X k) := fun k ↦
    isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : Space d) (k + 1 : ℝ))
  let G : ∀ k, ℕ → X k →ᵇ ℝ := fun k j ↦ BoundedContinuousFunction.mkOfCompact
    ⟨fun x ↦ F j x, (hL j).continuous.comp continuous_subtype_val⟩
  have hM (k j : ℕ) (x : X k) : G k j x ∈ Icc 0 ((L : ℝ) * (k + 1 : ℝ)) := by
    refine ⟨hnonneg j x, ?_⟩
    have hd := (hL j).dist_le_mul x.1 0
    rw [h0 j, dist_zero_right, dist_zero_right, Real.norm_of_nonneg (hnonneg j x)] at hd
    have hx : ‖x.1‖ ≤ k + 1 := by simpa only [X, mem_closedBall, dist_zero_right] using x.2
    exact hd.trans (mul_le_mul_of_nonneg_left hx L.coe_nonneg)
  obtain ⟨φ, hφ, hv⟩ := exists_simultaneous_uniform_subsequence G (fun _ ↦ L)
    (fun k ↦ (L : ℝ) * (k + 1 : ℝ)) (fun k j ↦ (hL j).restrict (X k)) hM
  choose v hv using hv
  let W (x : Space d) := limUnder atTop (fun j ↦ F (φ j) x)
  have hpoint (x : Space d) : Tendsto (fun j ↦ F (φ j) x) atTop (𝓝 (W x)) := by
    obtain ⟨k, hk⟩ := exists_nat_gt ‖x‖
    have hx : x ∈ X k := by simp only [X, mem_closedBall, dist_zero_right]; linarith
    have ht := (hv k).tendsto_at (⟨x, hx⟩ : X k)
    have he : W x = v k ⟨x, hx⟩ := ht.limUnder_eq
    rw [he]
    exact ht
  refine ⟨φ, W, hφ, ?_, ?_, ?_, ?_⟩
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    exact le_of_tendsto ((hpoint x).dist (hpoint y))
      (Eventually.of_forall (fun j ↦ (hL (φ j)).dist_le_mul x y))
  · exact tendsto_nhds_unique (hpoint 0)
      (tendsto_const_nhds.congr' (Eventually.of_forall (fun j ↦ (h0 (φ j)).symm)))
  · exact fun x ↦ ge_of_tendsto (hpoint x) (Eventually.of_forall (fun j ↦ hnonneg (φ j) x))
  · intro K hK
    obtain ⟨r, hr⟩ := hK.isBounded.subset_ball (0 : Space d)
    obtain ⟨k, hk⟩ := exists_nat_gt r
    have hsub : K ⊆ X k := by
      intro x hx
      have hxr : ‖x‖ < r := by simpa using hr hx
      simp only [X, mem_closedBall, dist_zero_right]
      linarith
    apply TendstoUniformlyOn.mono _ hsub
    apply tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mpr
    have he : (fun x : X k ↦ W x) = v k := by
      funext x
      exact ((hv k).tendsto_at x).limUnder_eq
    change TendstoUniformly (fun j (x : X k) ↦ F (φ j) x) (fun x : X k ↦ W x) atTop
    rw [he]
    exact hv k

/-- Microscopic blowups at a free-boundary point of a physical translation limit admit a
locally uniformly convergent subsequence whose limit is nondegenerate, `κ`-Lipschitz,
weakly harmonic on its positive phase, globally truncated-harmonic, and strongly approximated
in `L²_loc` by the rescaled gradients (TB2 and TB6.2). -/
theorem RigidityHypotheses.exists_microscopic_blowup_limit
    {m : ℕ} {g : Space m → ℝ} {u V : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {p_seq : ℕ → Space (m + 1)} {r_seq : ℕ → ℝ}
    (hlim : ∀ K : Set (Space (m + 1)), IsCompact K →
      TendstoUniformlyOn (fun j x ↦ zeroExtension g u (p_seq j + x)) V atTop K)
    (hV0 : V 0 = 0) (hcl : (0 : Space (m + 1)) ∈ closure {x | 0 < V x})
    (hr_pos : ∀ j, 0 < r_seq j) (hr_lim : Tendsto r_seq atTop (𝓝 0)) :
    ∃ (φ : ℕ → ℕ) (W_lim : Space (m + 1) → ℝ),
      StrictMono φ ∧
      LipschitzWith ⟨κ, h.kappa_pos.le⟩ W_lim ∧
      W_lim 0 = 0 ∧
      (∀ x, 0 ≤ W_lim x) ∧
      (∀ K : Set (Space (m + 1)), IsCompact K →
        TendstoUniformlyOn (fun j x ↦ V (r_seq (φ j) • x) / r_seq (φ j)) W_lim atTop K) ∧
      (∃ x ∈ closedBall 0 1, 0 < W_lim x) ∧
      (∀ η : Space (m + 1) → ℝ, ContDiff ℝ 1 η → HasCompactSupport η →
        tsupport η ⊆ {x | 0 < W_lim x} →
        (∫ x, inner ℝ (gradient W_lim x) (gradient η x)) = 0) ∧
      (∀ η : Space (m + 1) → ℝ, ContDiff ℝ 1 η → HasCompactSupport η →
        (∫ x, η x * ‖gradient W_lim x‖ ^ 2 +
          W_lim x * inner ℝ (gradient W_lim x) (gradient η x)) = 0) ∧
      (∀ K : Set (Space (m + 1)), IsCompact K →
        Tendsto (fun j ↦ ∫ x in K,
          ‖gradient (fun y ↦ V (r_seq (φ j) • y) / r_seq (φ j)) x - gradient W_lim x‖ ^ 2)
          atTop (𝓝 0)) := by
  have hpointV (x : Space (m + 1)) :
      Tendsto (fun j ↦ zeroExtension g u (p_seq j + x)) atTop (𝓝 (V x)) :=
    (hlim {x} isCompact_singleton).tendsto_at (mem_singleton x)
  have hV : LipschitzWith ⟨κ, h.kappa_pos.le⟩ V := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    exact le_of_tendsto ((hpointV x).dist (hpointV y))
      (Eventually.of_forall (fun j ↦ by
        simpa only [dist_add_left] using
          (hr.zeroExtension_lipschitzWith h).dist_le_mul (p_seq j + x) (p_seq j + y)))
  have hval (x : Space (m + 1)) : V x ∈ Icc 0 1 :=
    ⟨ge_of_tendsto (hpointV x) (Eventually.of_forall (fun _ ↦ h.zeroExtension_nonneg _)),
      le_of_tendsto (hpointV x) (Eventually.of_forall (fun _ ↦ (hr.zeroExtension_lt_one _).le))⟩
  let F : ℕ → Space (m + 1) → ℝ := fun j x ↦ V (r_seq j • x) / r_seq j
  obtain ⟨φ, W_lim, hφ, hW, hW_zero, hW0, hWlim⟩ :=
    exists_locally_uniform_subsequence_of_lipschitz_zero F
      (fun j ↦ lipschitzWith_rescale_div hV (hr_pos j))
      (fun j ↦ by simp [F, hV0])
      (fun j x ↦ div_nonneg (hval _).1 (hr_pos j).le)
  have hrφ_pos (j : ℕ) : 0 < r_seq (φ j) := hr_pos (φ j)
  have hrφ_lim : Tendsto (fun j ↦ r_seq (φ j)) atTop (𝓝 0) := hr_lim.comp hφ.tendsto_atTop
  have hnondeg : ∃ x ∈ closedBall (0 : Space (m + 1)) 1, 0 < W_lim x := by
    obtain ⟨a_star, R₀, ha_pos, hR₀_pos, hclear⟩ := hr.exists_physical_limit_clearing_constants h
    obtain ⟨x₀, hx₀, hmax⟩ := (isCompact_closedBall (0 : Space (m + 1)) 1).exists_isMaxOn
      (nonempty_closedBall.mpr zero_le_one) hW.continuous.continuousOn
    have hevR : ∀ᶠ j in atTop, r_seq (φ j) ≤ R₀ :=
      (hrφ_lim.eventually (Iio_mem_nhds hR₀_pos)).mono (fun _ hj ↦ hj.le)
    have hevU := Metric.tendstoUniformlyOn_iff.mp
      (hWlim (closedBall 0 1) (isCompact_closedBall 0 1)) (a_star / 2) (half_pos ha_pos)
    obtain ⟨j, hjR, hjU⟩ := (hevR.and hevU).exists
    obtain ⟨y, hy_ball, hy_val⟩ := exists_positive_value_of_clearing
      (hclear p_seq V hlim) hcl (hrφ_pos j) hjR
    let x := (r_seq (φ j))⁻¹ • y
    have hx_mem : x ∈ closedBall (0 : Space (m + 1)) 1 := by
      have hy_norm : ‖y‖ < r_seq (φ j) := by simpa only [mem_ball, dist_zero_right] using hy_ball
      rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr
        (hrφ_pos j).le)]
      exact (inv_mul_le_iff₀ (hrφ_pos j)).mpr (by linarith)
    have hFx : a_star < V (r_seq (φ j) • x) / r_seq (φ j) := by
      dsimp only [x]
      rw [smul_inv_smul₀ (hrφ_pos j).ne']
      exact (lt_div_iff₀ (hrφ_pos j)).mpr hy_val
    have hclose := hjU x hx_mem
    rw [Real.dist_eq] at hclose
    have hmaxx : W_lim x ≤ W_lim x₀ := hmax hx_mem
    refine ⟨x₀, hx₀, ?_⟩
    linarith [(abs_lt.mp hclose).1]
  refine ⟨φ, W_lim, hφ, hW, hW_zero, hW0, hWlim, hnondeg,
    fun η hη hc hs ↦ hr.microscopic_blowup_weak_harmonic h hV hval hlim
      hrφ_pos hrφ_lim hW hW0 hWlim hη hc hs,
    fun η hη hc ↦ hr.microscopic_blowup_truncated_harmonic h hV hval hlim
      hrφ_pos hrφ_lim hW hW0 hWlim hη hc,
    fun K hK ↦ hr.microscopic_blowup_gradient_tendsto h hV hval hlim
      hrφ_pos hrφ_lim hW hW0 hWlim hK⟩

/-! ### Smooth radial Weiss monotonicity and degree-one homogeneity (TB3 and TB4) -/

/-- Global divergence integration by parts for a bounded nonnegative locally Lipschitz scalar
multiplied against a compactly supported `C¹` vector field. -/
theorem integral_fieldDivergence_mul_eq_neg_inner_gradient_of_locallyLipschitz
    {d : ℕ} (b : OrthonormalBasis (Fin d) ℝ (Space d))
    {w : Space d → ℝ} {X : Space d → Space d} {B : ℝ}
    (hw : LocallyLipschitz w) (hval : ∀ x, w x ∈ Icc 0 B)
    (hX : ContDiff ℝ 1 X) (hc : HasCompactSupport X) :
    (∫ x, w x * fieldDivergence b X x) = -∫ x, inner ℝ (gradient w x) (X x) := by
  obtain ⟨R, hR, hsupp⟩ := hc.isBounded.subset_ball_lt 0 (0 : Space d)
  let K := tsupport X
  have hK : IsCompact K := hc
  have hB0 : 0 ≤ B := (hval 0).1.trans (hval 0).2
  let χ : ContDiffBump (0 : Space d) :=
    { rIn := R + 1, rOut := R + 2, rIn_pos := by linarith, rIn_lt_rOut := by linarith }
  have hdiv_cont : Continuous (fieldDivergence b X) := fieldDivergence_continuous b hX
  have hcdiv : HasCompactSupport (fieldDivergence b X) := by
    apply hc.of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal _ (isClosed_tsupport X)
    intro x hx
    by_contra hn
    exact hx (fieldDivergence_zero_of_notMem_tsupport b X hn)
  obtain ⟨Cdiv, hCdiv⟩ := hcdiv.exists_bound_of_continuous hdiv_cont
  obtain ⟨CX, hCX⟩ := hc.exists_bound_of_continuous hX.continuous
  obtain ⟨Cg, hCg⟩ := normalizedMollify_gradient_bound_of_locallyLipschitz hw hK
  have hmoll (n : ℕ) :
      (∫ x in K, normalizedMollify w n x * fieldDivergence b X x) =
        -∫ x in K, inner ℝ (gradient (normalizedMollify w n) x) (X x) := by
    let gn := normalizedMollify w n
    let φn : Space d → ℝ := fun x ↦ χ x * gn x
    have hgn : ContDiff ℝ 1 gn := (normalizedMollify_contDiff hw.continuous n).of_le (by simp)
    have hχ1 : ContDiff ℝ 1 (χ : Space d → ℝ) := χ.contDiff
    have hφn : ContDiff ℝ 1 φn := hχ1.mul hgn
    have hcφn : HasCompactSupport φn := χ.hasCompactSupport.mul_right
    have hibp := integral_inner_field_gradient (μ := volume) isOpen_univ hX.contDiffOn
      hφn hcφn (subset_univ _) b
    have htrace (x : Space d) :
        (∑ i, inner ℝ (fderiv ℝ X x (b i)) (b i)) = fieldDivergence b X x := by
      unfold fieldDivergence
      exact Finset.sum_congr rfl (fun i _ ↦ real_inner_comm _ _)
    simp_rw [htrace] at hibp
    have hL : (∫ x in K, gn x * fieldDivergence b X x) =
        ∫ x, fieldDivergence b X x * φn x := by
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ by
        simp [fieldDivergence_zero_of_notMem_tsupport b X hx])]
      apply integral_congr_ae
      refine Eventually.of_forall (fun x ↦ ?_)
      by_cases hx : x ∈ K
      · have hxb : x ∈ closedBall 0 (R + 1) :=
          ball_subset_closedBall ((ball_subset_ball (by linarith)) (hsupp hx))
        dsimp only [φn]
        rw [χ.one_of_mem_closedBall hxb, one_mul, mul_comm]
      · simp [fieldDivergence_zero_of_notMem_tsupport b X hx]
    have hR' : (∫ x in K, inner ℝ (gradient gn x) (X x)) =
        ∫ x, inner ℝ (X x) (gradient φn x) := by
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ by
        simp [image_eq_zero_of_notMem_tsupport hx])]
      apply integral_congr_ae
      refine Eventually.of_forall (fun x ↦ ?_)
      by_cases hx : x ∈ K
      · have hxb : x ∈ ball 0 (R + 1) := (ball_subset_ball (by linarith)) (hsupp hx)
        have hev : φn =ᶠ[𝓝 x] gn := by
          filter_upwards [isOpen_ball.mem_nhds hxb] with y hy
          dsimp only [φn]
          rw [χ.one_of_mem_closedBall (ball_subset_closedBall hy), one_mul]
        have hgrad : gradient φn x = gradient gn x := by
          simp [gradient, hev.fderiv_eq]
        dsimp only
        rw [hgrad, real_inner_comm]
      · simp [image_eq_zero_of_notMem_tsupport hx]
    rw [hL, hR', hibp, neg_neg]
  have htL : Tendsto (fun n ↦ ∫ x in K, normalizedMollify w n x * fieldDivergence b X x)
      atTop (𝓝 (∫ x in K, w x * fieldDivergence b X x)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ ↦ B * |Cdiv|)
    · exact fun n ↦ ((normalizedMollify_contDiff hw.continuous n).continuous.mul
        hdiv_cont).aestronglyMeasurable
    · exact continuousOn_const.integrableOn_compact hK
    · intro n
      filter_upwards with x
      have hm := normalizedMollify_mem_Icc_of_bounds hw.continuous hval n x
      rw [norm_mul, Real.norm_of_nonneg hm.1]
      exact mul_le_mul hm.2 ((hCdiv x).trans (le_abs_self Cdiv)) (norm_nonneg _) hB0
    · filter_upwards with x
      exact (normalizedMollify_tendsto hw.continuous x).mul tendsto_const_nhds
  have htR : Tendsto (fun n ↦ -∫ x in K, inner ℝ (gradient (normalizedMollify w n) x) (X x))
      atTop (𝓝 (-∫ x in K, inner ℝ (gradient w x) (X x))) := by
    apply Tendsto.neg
    apply tendsto_integral_of_dominated_convergence (fun _ ↦ (Cg : ℝ) * |CX|)
    · exact fun n ↦ ((measurable_gradient _).inner (𝕜 := ℝ)
        hX.continuous.measurable).aestronglyMeasurable
    · exact continuousOn_const.integrableOn_compact hK
    · intro n
      filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
      exact (norm_inner_le_norm (𝕜 := ℝ) _ _).trans
        (mul_le_mul (hCg n x hx) ((hCX x).trans (le_abs_self CX)) (norm_nonneg _) Cg.coe_nonneg)
    · filter_upwards [ae_restrict_of_ae
        (normalizedMollify_gradient_tendsto_ae_of_locallyLipschitz hw)] with x hx
      exact hx.inner tendsto_const_nhds
  have heqK := tendsto_nhds_unique htL (htR.congr' (Eventually.of_forall (fun n ↦ (hmoll n).symm)))
  have hcutL : (∫ x in K, w x * fieldDivergence b X x) = ∫ x, w x * fieldDivergence b X x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ by
      simp [fieldDivergence_zero_of_notMem_tsupport b X hx])
  have hcutR : (∫ x in K, inner ℝ (gradient w x) (X x)) = ∫ x, inner ℝ (gradient w x) (X x) :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ by
      simp [image_eq_zero_of_notMem_tsupport hx])
  rw [← hcutL, ← hcutR, heqK]

/-- Almost-everywhere differentiability of a globally Lipschitz scalar function. -/
private theorem ae_differentiableAt_of_lipschitz {d : ℕ} {v : Space d → ℝ} {L : ℝ≥0}
    (hv : LipschitzWith L v) : ∀ᵐ x, DifferentiableAt ℝ v x := by
  have he (n : ℕ) : ∀ᵐ x, x ∈ closedBall (0 : Space d) (n + 1) →
      DifferentiableWithinAt ℝ v (closedBall 0 (n + 1)) x :=
    (hv.lipschitzOnWith (s := closedBall 0 (n + 1))).ae_differentiableWithinAt_of_mem
  filter_upwards [ae_all_iff.mpr he] with x hx
  obtain ⟨n, hn⟩ := exists_nat_gt ‖x‖
  have hb : x ∈ ball (0 : Space d) (n + 1) := by
    simp only [mem_ball, dist_zero_right]; linarith
  exact (hx n (ball_subset_closedBall hb)).differentiableAt (closedBall_mem_nhds_of_mem hb)

/-- Integration by parts for `V²` against a compactly supported `C¹` vector field when `V` is
globally Lipschitz with values in `[0, 1]`. -/
theorem integral_sq_fieldDivergence_eq_neg_two_mul_inner_gradient
    {d : ℕ} (b : OrthonormalBasis (Fin d) ℝ (Space d))
    {V : Space d → ℝ} {X : Space d → Space d} {L : ℝ≥0}
    (hV : LipschitzWith L V) (hval : ∀ x, V x ∈ Icc 0 1)
    (hX : ContDiff ℝ 1 X) (hc : HasCompactSupport X) :
    (∫ x, V x ^ 2 * fieldDivergence b X x) =
      -2 * ∫ x, V x * inner ℝ (gradient V x) (X x) := by
  have hw_lip : LipschitzWith (2 * L) (fun x ↦ V x ^ 2) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq]
    have hfac : |V x ^ 2 - V y ^ 2| = |V x + V y| * |V x - V y| := by
      rw [← abs_mul]; congr 1; ring
    have hsum : |V x + V y| ≤ 2 :=
      abs_le.mpr ⟨by linarith [(hval x).1, (hval y).1], by linarith [(hval x).2, (hval y).2]⟩
    have hd := hV.dist_le_mul x y
    rw [Real.dist_eq] at hd
    rw [hfac, NNReal.coe_mul, NNReal.coe_ofNat, mul_assoc]
    exact mul_le_mul hsum hd (abs_nonneg _) (by positivity)
  have hw_val (x : Space d) : V x ^ 2 ∈ Icc (0 : ℝ) 1 :=
    ⟨sq_nonneg _, by nlinarith [(hval x).1, (hval x).2]⟩
  rw [integral_fieldDivergence_mul_eq_neg_inner_gradient_of_locallyLipschitz b
    hw_lip.locallyLipschitz hw_val hX hc]
  have hcongr : (∫ x, inner ℝ (gradient (fun y ↦ V y ^ 2) x) (X x)) =
      ∫ x, 2 * (V x * inner ℝ (gradient V x) (X x)) := by
    apply integral_congr_ae
    filter_upwards [ae_differentiableAt_of_lipschitz hV] with x hd
    have hsq : gradient (fun y ↦ V y ^ 2) x = (2 * V x) • gradient V x := by
      apply ext_inner_right ℝ
      intro u
      rw [inner_gradient_left, (hd.hasFDerivAt.pow 2).fderiv, smul_apply,
        real_inner_smul_left, inner_gradient_left]
      simp only [Nat.add_one_sub_one, pow_one, smul_eq_mul]
      ring
    rw [hsq, real_inner_smul_left]
    ring
  rw [hcongr, integral_const_mul]
  ring

/-- Scale derivative of the smooth Weiss bulk energy for a physical translation limit. -/
theorem RigidityHypotheses.smoothWeissEnergy_hasDerivAt
    {m : ℕ} {g : Space m → ℝ} {u V : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ r : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {p : ℕ → Space (m + 1)} (hV : LipschitzWith ⟨κ, h.kappa_pos.le⟩ V)
    (hval : ∀ x, V x ∈ Icc 0 1)
    (hlim : ∀ K : Set (Space (m + 1)), IsCompact K →
      TendstoUniformlyOn (fun j x ↦ zeroExtension g u (p j + x)) V atTop K)
    (hr0 : 0 < r) :
    HasDerivAt (smoothWeissEnergy f V)
      (4 * r ^ (-(m + 4 : ℤ)) *
          (∫ x, radialWeight weissBoundaryProfile 0 r x *
            (inner ℝ (gradient V x) x ^ 2 - V x * inner ℝ (gradient V x) x)) -
        2 * r ^ (-(m + 2 : ℤ)) *
          (∫ x, radialWeight weissProfile 0 r x * (V x * f (V x)))) r := by
  let E := phaseEnergyDensity f 0 V
  let ψ := radialWeight weissProfile (0 : Space (m + 1)) r
  let pr := radialWeight weissBoundaryProfile (0 : Space (m + 1)) r
  let basis := EuclideanSpace.basisFun (Fin (m + 1)) ℝ
  have hzero_w : ∀ s : ℝ, 2 ≤ s → weissProfile s = 0 :=
    fun _ hs ↦ weissProfile_zero (by linarith)
  have hzero_p : ∀ s : ℝ, 2 ≤ s → weissBoundaryProfile s = 0 :=
    fun _ hs ↦ weissBoundaryProfile_zero (by linarith)
  have hiE (K : Set (Space (m + 1))) (hK : IsCompact K) :
      IntegrableOn (fun x ↦ 2 * E x) K :=
    (h.integrableOn_lipschitz_phaseEnergy hV.locallyLipschitz hval 0 hK).const_mul 2
  have hdI := hasDerivAt_integral_mul_radialWeight weissProfile_contDiff hzero_w 0 hr0 hiE
  have hpow := hasDerivAt_zpow (-(m + 1 : ℤ)) r (Or.inl hr0.ne')
  have hd_prod := hpow.mul hdI
  change HasDerivAt (smoothWeissEnergy f V) _ r at hd_prod
  have hψ_cont : ContDiff ℝ 1 ψ := contDiff_radialWeight weissProfile_contDiff 0 r
  have hψ_comp : HasCompactSupport ψ :=
    (isCompact_closedBall 0 (2 * r)).of_isClosed_subset (isClosed_tsupport _)
      (tsupport_radialWeight_subset hzero_w 0 hr0)
  have hpr_cont : ContDiff ℝ 1 pr := contDiff_radialWeight weissBoundaryProfile_contDiff 0 r
  have hpr_comp : HasCompactSupport pr :=
    (isCompact_closedBall 0 (2 * r)).of_isClosed_subset (isClosed_tsupport _)
      (tsupport_radialWeight_subset hzero_p 0 hr0)
  let X : Space (m + 1) → Space (m + 1) := fun x ↦ ψ x • x
  have hX : ContDiff ℝ 1 X := hψ_cont.smul contDiff_id
  have hcX : HasCompactSupport X := hψ_comp.smul_right
  have hstress := hr.physical_translation_limit_stress_stationarity h hV hval hlim basis hX hcX
  have hscalar := hr.physical_translation_limit_scalar_stationarity h hV hval hlim hψ_cont hψ_comp
  have hfderiv_ψ (x v : Space (m + 1)) :
      fderiv ℝ ψ x v = -2 / r ^ 2 * pr x * inner ℝ x v := by
    have hf := fderiv_radialWeight weissProfile_contDiff.differentiable_one 0 r x v
    simp only [sub_zero, weissProfile_deriv] at hf
    dsimp only [ψ, pr, radialWeight] at hf ⊢
    simp only [sub_zero] at hf ⊢
    rw [hf]
    ring
  have hgrad_ψ (x : Space (m + 1)) : gradient ψ x = (-2 / r ^ 2 * pr x) • x := by
    apply ext_inner_right ℝ
    intro v
    rw [inner_gradient_left, hfderiv_ψ, real_inner_smul_left]
  have hdiv_X (x : Space (m + 1)) :
      fieldDivergence basis X x = (m + 1 : ℝ) * ψ x - 2 / r ^ 2 * ‖x‖ ^ 2 * pr x := by
    have hd := divergence_localized_dilation basis (hψ_cont.differentiable_one x) 0
    simp only [sub_zero, Nat.cast_add, Nat.cast_one] at hd
    dsimp only [X]
    rw [hd, hfderiv_ψ, real_inner_self_eq_norm_sq]
    ring
  have hfderiv_X (x v : Space (m + 1)) :
      fderiv ℝ X x v = ψ x • v + (-2 / r ^ 2 * pr x * inner ℝ x v) • x := by
    have hd := fderiv_localized_dilation (hψ_cont.differentiable_one x) 0 v
    simp only [sub_zero] at hd
    dsimp only [X]
    rw [hd, hfderiv_ψ]
  have hscale_deriv (x : Space (m + 1)) :
      radialWeightScaleDerivative weissProfile 0 r x = 2 * ‖x‖ ^ 2 / r ^ 3 * pr x := by
    dsimp only [radialWeightScaleDerivative, pr, radialWeight]
    simp only [sub_zero, weissProfile_deriv]
    ring
  have hVbound (x : Space (m + 1)) : ‖gradient V x‖ ≤ κ := by
    rw [gradient, LinearIsometryEquiv.norm_map]
    exact norm_fderiv_le_of_lipschitz ℝ hV
  have hf_cont : Continuous (fun x ↦ f (V x)) :=
    h.reaction_contDiffOn.continuousOn.comp_continuous hV.continuous (fun x ↦ (hval x).1)
  have hi_Eψ : Integrable (fun x ↦ (2 * E x) * ψ x) := by
    have hiK := (hiE (tsupport ψ) hψ_comp).mul_continuousOn hψ_cont.continuous.continuousOn hψ_comp
    exact hiK.integrable_of_forall_notMem_eq_zero (fun x hx ↦ by
      simp [image_eq_zero_of_notMem_tsupport hx])
  have hi_Ed : Integrable (fun x ↦ (2 * E x) * radialWeightScaleDerivative weissProfile 0 r x) := by
    let K := closedBall (0 : Space (m + 1)) (2 * r)
    have hK : IsCompact K := isCompact_closedBall _ _
    have hcont_d : Continuous (radialWeightScaleDerivative weissProfile (0 : Space (m + 1)) r) := by
      have h1 : Continuous (fun x : Space (m + 1) ↦ 2 * ‖x‖ ^ 2 / r ^ 3 * pr x) :=
        ((continuous_const.mul (continuous_norm.pow 2)).div_const _).mul hpr_cont.continuous
      exact h1.congr (fun x ↦ (hscale_deriv x).symm)
    have hiK := (hiE K hK).mul_continuousOn hcont_d.continuousOn hK
    exact hiK.integrable_of_forall_notMem_eq_zero (fun x hx ↦ by
      have hn : x ∉ tsupport (radialWeightScaleDerivative weissProfile 0 r) :=
        fun hh ↦ hx (tsupport_radialWeightScaleDerivative_subset hzero_w 0 hr0 hh)
      simp [image_eq_zero_of_notMem_tsupport hn])
  have hi_stress : Integrable (fun x ↦ E x * fieldDivergence basis X x -
      inner ℝ (gradient V x) (fderiv ℝ X x (gradient V x))) := by
    have hDX := hX.continuous_fderiv one_ne_zero
    obtain ⟨D, hD⟩ := (hcX.fderiv ℝ).exists_bound_of_continuous hDX
    have hdiv := fieldDivergence_continuous basis hX
    have hcdiv : HasCompactSupport (fieldDivergence basis X) := by
      apply hcX.of_isClosed_subset (isClosed_tsupport _)
      apply closure_minimal _ (isClosed_tsupport X)
      intro x hx; by_contra hn
      exact hx (fieldDivergence_zero_of_notMem_tsupport basis X hn)
    obtain ⟨C, hC⟩ := hcdiv.exists_bound_of_continuous hdiv
    have hi1 : IntegrableOn (fun x ↦ E x * fieldDivergence basis X x) (tsupport X) :=
      (h.integrableOn_lipschitz_phaseEnergy hV.locallyLipschitz hval 0 hcX).mul_bdd
        hdiv.aestronglyMeasurable (Eventually.of_forall hC)
    have hi2 : IntegrableOn
        (fun x ↦ inner ℝ (gradient V x) (fderiv ℝ X x (gradient V x))) (tsupport X) :=
      integrableOn_inner_linear_of_bounds (measurable_gradient V) hDX hVbound hD hcX
    have hi12 : IntegrableOn
        (fun x ↦ E x * fieldDivergence basis X x -
          inner ℝ (gradient V x) (fderiv ℝ X x (gradient V x))) (tsupport X) := hi1.sub hi2
    exact hi12.integrable_of_forall_notMem_eq_zero (fun x hx ↦ by
      simp [fieldDivergence_zero_of_notMem_tsupport basis X hx, fderiv_of_notMem_tsupport ℝ hx])
  have hi_scalar : Integrable (fun x ↦ ψ x * (‖gradient V x‖ ^ 2 - V x * f (V x)) +
      V x * inner ℝ (gradient V x) (gradient ψ x)) := by
    have hgradψ_cont : Continuous (gradient ψ) :=
      (toDual ℝ (Space (m + 1))).symm.continuous.comp (hψ_cont.continuous_fderiv one_ne_zero)
    have hi1 : IntegrableOn (fun x ↦ ψ x * (‖gradient V x‖ ^ 2 - V x * f (V x))) (tsupport ψ) := by
      have hg2 := integrableOn_gradient_sq_of_locallyLipschitz hV.locallyLipschitz hψ_comp
      have hvf : IntegrableOn (fun x ↦ V x * f (V x)) (tsupport ψ) :=
        (hV.continuous.mul hf_cont).continuousOn.integrableOn_compact hψ_comp
      exact ((hg2.sub hvf).mul_continuousOn hψ_cont.continuous.continuousOn hψ_comp).congr_fun
        (fun x _ ↦ by simp only [Pi.sub_apply]; ring) hψ_comp.measurableSet
    have hi2 : IntegrableOn (fun x ↦ V x * inner ℝ (gradient V x) (gradient ψ x)) (tsupport ψ) := by
      obtain ⟨D, hD⟩ := hψ_comp.exists_bound_of_continuousOn hgradψ_cont.continuousOn
      apply (continuousOn_const.integrableOn_compact hψ_comp (f := fun _ ↦ κ * |D|)).mono'
        (hV.continuous.measurable.mul
          ((measurable_gradient V).inner (𝕜 := ℝ) hgradψ_cont.measurable)).aestronglyMeasurable
      filter_upwards [ae_restrict_mem hψ_comp.measurableSet] with x hx
      simp only [Pi.mul_apply]
      rw [norm_mul, Real.norm_of_nonneg (hval x).1]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hval x).2).trans
        ((norm_inner_le_norm (𝕜 := ℝ) _ _).trans
          (mul_le_mul (hVbound x) ((hD x hx).trans (le_abs_self D)) (norm_nonneg _) h.kappa_pos.le))
    have hi12 : IntegrableOn
        (fun x ↦ ψ x * (‖gradient V x‖ ^ 2 - V x * f (V x)) +
          V x * inner ℝ (gradient V x) (gradient ψ x)) (tsupport ψ) := hi1.add hi2
    exact hi12.integrable_of_forall_notMem_eq_zero (fun x hx ↦ by
      simp [image_eq_zero_of_notMem_tsupport hx, gradient, fderiv_of_notMem_tsupport ℝ hx])
  have hi_quad : Integrable (fun x ↦ pr x *
      (inner ℝ (gradient V x) x ^ 2 - V x * inner ℝ (gradient V x) x)) := by
    let K := tsupport pr
    have hK : IsCompact K := hpr_comp
    obtain ⟨Rx, hRx⟩ := hK.isBounded.subset_closedBall (0 : Space (m + 1))
    obtain ⟨Cp, hCp⟩ := hpr_comp.exists_bound_of_continuous hpr_cont.continuous
    have hiK : IntegrableOn (fun x ↦ pr x *
        (inner ℝ (gradient V x) x ^ 2 - V x * inner ℝ (gradient V x) x)) K := by
      apply (continuousOn_const.integrableOn_compact hK
        (f := fun _ ↦ |Cp| * ((κ * |Rx|) ^ 2 + κ * |Rx|))).mono'
        (hpr_cont.continuous.measurable.mul
          ((((measurable_gradient V).inner (𝕜 := ℝ) measurable_id).pow_const 2).sub
            (hV.continuous.measurable.mul
              ((measurable_gradient V).inner (𝕜 := ℝ) measurable_id)))).aestronglyMeasurable
      filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
      simp only [Pi.mul_apply, Pi.sub_apply, id_eq]
      rw [norm_mul]
      have hnx0 : ‖x‖ ≤ Rx := by simpa only [mem_closedBall, dist_zero_right] using hRx hx
      have hnx : ‖x‖ ≤ |Rx| := hnx0.trans (le_abs_self Rx)
      have hin : ‖inner ℝ (gradient V x) x‖ ≤ κ * |Rx| :=
        (norm_inner_le_norm (𝕜 := ℝ) _ _).trans
          (mul_le_mul (hVbound x) hnx (norm_nonneg _) h.kappa_pos.le)
      have hsub_b : ‖inner ℝ (gradient V x) x ^ 2 - V x * inner ℝ (gradient V x) x‖ ≤
          (κ * |Rx|) ^ 2 + κ * |Rx| := by
        apply (norm_sub_le _ _).trans
        apply add_le_add
        · rw [norm_pow]
          exact pow_le_pow_left₀ (norm_nonneg _) hin 2
        · rw [norm_mul, Real.norm_of_nonneg (hval x).1]
          exact (mul_le_of_le_one_left (norm_nonneg _) (hval x).2).trans hin
      exact mul_le_mul ((hCp x).trans (le_abs_self Cp)) hsub_b (norm_nonneg _) (abs_nonneg Cp)
    exact hiK.integrable_of_forall_notMem_eq_zero (fun x hx ↦ by
      simp [image_eq_zero_of_notMem_tsupport hx])
  have hi_react : Integrable (fun x ↦ ψ x * (V x * f (V x))) :=
    (hψ_cont.continuous.mul (hV.continuous.mul hf_cont)).integrable_of_hasCompactSupport
      hψ_comp.mul_right
  convert hd_prod using 1
  have hr2 : r ^ (-(m + 1 : ℤ) - 1) = r ^ (-(m + 2 : ℤ)) :=
    congrArg (r ^ ·) (by ring)
  have hr4 : r ^ (-(m + 2 : ℤ)) * (1 / r ^ 2) = r ^ (-(m + 4 : ℤ)) := by
    have h1 : 1 / r ^ 2 = r ^ (-2 : ℤ) := by rw [one_div, zpow_neg, zpow_ofNat]
    rw [h1, ← zpow_add₀ hr0.ne']
    exact congrArg (r ^ ·) (by ring)
  have hr3 : r ^ (-(m + 1 : ℤ)) * (1 / r ^ 3) = r ^ (-(m + 4 : ℤ)) := by
    have h1 : 1 / r ^ 3 = r ^ (-3 : ℤ) := by rw [one_div, zpow_neg, zpow_ofNat]
    rw [h1, ← zpow_add₀ hr0.ne']
    exact congrArg (r ^ ·) (by ring)
  have hr1 : r ^ (-(m + 1 : ℤ)) * (1 / r) = r ^ (-(m + 2 : ℤ)) := by
    have h1 : 1 / r = r ^ (-1 : ℤ) := by rw [one_div, zpow_neg_one]
    rw [h1, ← zpow_add₀ hr0.ne']
    exact congrArg (r ^ ·) (by ring)
  have hpt (x : Space (m + 1)) :
      ((-(m + 1 : ℤ) : ℝ) * r ^ (-(m + 1 : ℤ) - 1)) * ((2 * E x) * ψ x) +
        r ^ (-(m + 1 : ℤ)) * ((2 * E x) * radialWeightScaleDerivative weissProfile 0 r x) +
        2 * r ^ (-(m + 2 : ℤ)) * (E x * fieldDivergence basis X x -
          inner ℝ (gradient V x) (fderiv ℝ X x (gradient V x))) +
        2 * r ^ (-(m + 2 : ℤ)) * (ψ x * (‖gradient V x‖ ^ 2 - V x * f (V x)) +
          V x * inner ℝ (gradient V x) (gradient ψ x)) =
      4 * r ^ (-(m + 4 : ℤ)) * (pr x *
        (inner ℝ (gradient V x) x ^ 2 - V x * inner ℝ (gradient V x) x)) -
        2 * r ^ (-(m + 2 : ℤ)) * (ψ x * (V x * f (V x))) := by
    rw [hr2, hscale_deriv x, hdiv_X x, hfderiv_X x, hgrad_ψ x]
    simp only [inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
      Int.cast_add, Int.cast_natCast, Int.cast_one]
    have hcomm : inner ℝ x (gradient V x) = inner ℝ (gradient V x) x := real_inner_comm _ _
    rw [hcomm]
    have ha1 : r ^ (-(m + 1 : ℤ)) * ((2 * E x) * (2 * ‖x‖ ^ 2 / r ^ 3 * pr x)) =
        (r ^ (-(m + 1 : ℤ)) * (1 / r ^ 3)) * (4 * E x * ‖x‖ ^ 2 * pr x) := by ring
    rw [ha1, hr3]
    have ha2 : 2 * r ^ (-(m + 2 : ℤ)) *
        (E x * ((m + 1 : ℝ) * ψ x - 2 / r ^ 2 * ‖x‖ ^ 2 * pr x) -
          (ψ x * ‖gradient V x‖ ^ 2 +
            -2 / r ^ 2 * pr x * inner ℝ (gradient V x) x * inner ℝ (gradient V x) x)) =
        2 * (m + 1 : ℝ) * r ^ (-(m + 2 : ℤ)) * E x * ψ x -
          2 * r ^ (-(m + 2 : ℤ)) * ψ x * ‖gradient V x‖ ^ 2 +
          (r ^ (-(m + 2 : ℤ)) * (1 / r ^ 2)) *
            (-4 * E x * ‖x‖ ^ 2 * pr x + 4 * pr x * inner ℝ (gradient V x) x ^ 2) := by ring
    rw [ha2, hr4]
    have ha3 : 2 * r ^ (-(m + 2 : ℤ)) * (ψ x * (‖gradient V x‖ ^ 2 - V x * f (V x)) +
        V x * (-2 / r ^ 2 * pr x * inner ℝ (gradient V x) x)) =
        2 * r ^ (-(m + 2 : ℤ)) * ψ x * ‖gradient V x‖ ^ 2 -
          2 * r ^ (-(m + 2 : ℤ)) * (ψ x * (V x * f (V x))) -
          (r ^ (-(m + 2 : ℤ)) * (1 / r ^ 2)) *
            (4 * pr x * (V x * inner ℝ (gradient V x) x)) := by ring
    rw [ha3, hr4]
    ring
  have hint_eq := integral_congr_ae (μ := volume) (Eventually.of_forall hpt)
  have hiL1 := hi_Eψ.const_mul ((-(m + 1 : ℤ) : ℝ) * r ^ (-(m + 1 : ℤ) - 1))
  have hiL2 := hi_Ed.const_mul (r ^ (-(m + 1 : ℤ)))
  have hiL3 := hi_stress.const_mul (2 * r ^ (-(m + 2 : ℤ)))
  have hiL4 := hi_scalar.const_mul (2 * r ^ (-(m + 2 : ℤ)))
  have hiR1 := hi_quad.const_mul (4 * r ^ (-(m + 4 : ℤ)))
  have hiR2 := hi_react.const_mul (2 * r ^ (-(m + 2 : ℤ)))
  have hsplitL : (∫ x, ((-(m + 1 : ℤ) : ℝ) * r ^ (-(m + 1 : ℤ) - 1)) * ((2 * E x) * ψ x) +
      r ^ (-(m + 1 : ℤ)) * ((2 * E x) * radialWeightScaleDerivative weissProfile 0 r x) +
      2 * r ^ (-(m + 2 : ℤ)) * (E x * fieldDivergence basis X x -
        inner ℝ (gradient V x) (fderiv ℝ X x (gradient V x))) +
      2 * r ^ (-(m + 2 : ℤ)) * (ψ x * (‖gradient V x‖ ^ 2 - V x * f (V x)) +
        V x * inner ℝ (gradient V x) (gradient ψ x))) =
      ((-(m + 1 : ℤ) : ℝ) * r ^ (-(m + 1 : ℤ) - 1)) * (∫ x, (2 * E x) * ψ x) +
      r ^ (-(m + 1 : ℤ)) * (∫ x, (2 * E x) * radialWeightScaleDerivative weissProfile 0 r x) +
      2 * r ^ (-(m + 2 : ℤ)) * (∫ x, E x * fieldDivergence basis X x -
        inner ℝ (gradient V x) (fderiv ℝ X x (gradient V x))) +
      2 * r ^ (-(m + 2 : ℤ)) * (∫ x, ψ x * (‖gradient V x‖ ^ 2 - V x * f (V x)) +
        V x * inner ℝ (gradient V x) (gradient ψ x)) := by
    have h1 := integral_add ((hiL1.add hiL2).add hiL3) hiL4
    have h2 := integral_add (hiL1.add hiL2) hiL3
    have h3 := integral_add hiL1 hiL2
    simp only [Pi.add_apply] at h1 h2 h3
    rw [h1, h2, h3, integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul]
  have hsplitR : (∫ x, 4 * r ^ (-(m + 4 : ℤ)) * (pr x *
      (inner ℝ (gradient V x) x ^ 2 - V x * inner ℝ (gradient V x) x)) -
      2 * r ^ (-(m + 2 : ℤ)) * (ψ x * (V x * f (V x)))) =
      4 * r ^ (-(m + 4 : ℤ)) * (∫ x, pr x *
        (inner ℝ (gradient V x) x ^ 2 - V x * inner ℝ (gradient V x) x)) -
      2 * r ^ (-(m + 2 : ℤ)) * (∫ x, ψ x * (V x * f (V x))) := by
    have hs := integral_sub hiR1 hiR2
    rw [hs, integral_const_mul, integral_const_mul]
  rw [hsplitL, hsplitR, hstress, hscalar] at hint_eq
  dsimp only [ψ, pr] at hint_eq ⊢
  push_cast at hint_eq ⊢
  linarith

/-- Scale derivative of the smooth Weiss boundary term for any globally Lipschitz `V : Space (m+1) → [0, 1]`. -/
theorem smoothWeissBoundary_hasDerivAt {m : ℕ} {V : Space (m + 1) → ℝ} {L : ℝ≥0}
    (hV : LipschitzWith L V) (hval : ∀ x, V x ∈ Icc 0 1) {r : ℝ} (hr0 : 0 < r) :
    HasDerivAt (smoothWeissBoundary V)
      (4 * r ^ (-(m + 4 : ℤ)) *
        ∫ x, radialWeight weissBoundaryProfile 0 r x *
          (V x * inner ℝ (gradient V x) x - V x ^ 2)) r := by
  let pr := radialWeight weissBoundaryProfile (0 : Space (m + 1)) r
  let basis := EuclideanSpace.basisFun (Fin (m + 1)) ℝ
  have hzero_p : ∀ s : ℝ, 2 ≤ s → weissBoundaryProfile s = 0 :=
    fun _ hs ↦ weissBoundaryProfile_zero (by linarith)
  have hiV2 (K : Set (Space (m + 1))) (hK : IsCompact K) :
      IntegrableOn (fun x ↦ V x ^ 2) K :=
    (hV.continuous.pow 2).continuousOn.integrableOn_compact hK
  have hdI := hasDerivAt_integral_mul_radialWeight weissBoundaryProfile_contDiff hzero_p 0 hr0 hiV2
  have hpow := (hasDerivAt_zpow (-(m + 3 : ℤ)) r (Or.inl hr0.ne')).const_mul 2
  have hd_prod : HasDerivAt (smoothWeissBoundary V) _ r :=
    (hpow.mul hdI).congr_of_eventuallyEq (by
      filter_upwards [Ioi_mem_nhds hr0] with s hs
      simp only [Pi.mul_apply]
      exact smoothWeissBoundary_eq_spatial_integral V hs)
  have hpr_cont : ContDiff ℝ 1 pr := contDiff_radialWeight weissBoundaryProfile_contDiff 0 r
  have hpr_comp : HasCompactSupport pr :=
    (isCompact_closedBall 0 (2 * r)).of_isClosed_subset (isClosed_tsupport _)
      (tsupport_radialWeight_subset hzero_p 0 hr0)
  let X : Space (m + 1) → Space (m + 1) := fun x ↦ pr x • x
  have hX : ContDiff ℝ 1 X := hpr_cont.smul contDiff_id
  have hcX : HasCompactSupport X := hpr_comp.smul_right
  have hibp := integral_sq_fieldDivergence_eq_neg_two_mul_inner_gradient basis hV hval hX hcX
  have hdiv_X (x : Space (m + 1)) :
      fieldDivergence basis X x =
        (m + 1 : ℝ) * pr x - r * radialWeightScaleDerivative weissBoundaryProfile 0 r x := by
    have hd := divergence_localized_dilation basis (hpr_cont.differentiable_one x) 0
    simp only [sub_zero, Nat.cast_add, Nat.cast_one] at hd
    have hf := fderiv_radialWeight weissBoundaryProfile_contDiff.differentiable_one 0 r x x
    simp only [sub_zero, real_inner_self_eq_norm_sq] at hf
    dsimp only [X, pr] at hd ⊢
    rw [hd, hf]
    dsimp only [radialWeightScaleDerivative]
    simp only [sub_zero]
    field_simp
    ring
  have hi_V2p : Integrable (fun x ↦ V x ^ 2 * pr x) :=
    ((hV.continuous.pow 2).mul hpr_cont.continuous).integrable_of_hasCompactSupport
      hpr_comp.mul_left
  have hi_V2div : Integrable (fun x ↦ V x ^ 2 * fieldDivergence basis X x) := by
    have hcdiv : HasCompactSupport (fieldDivergence basis X) := by
      apply hcX.of_isClosed_subset (isClosed_tsupport _)
      apply closure_minimal _ (isClosed_tsupport X)
      intro x hx; by_contra hn
      exact hx (fieldDivergence_zero_of_notMem_tsupport basis X hn)
    exact ((hV.continuous.pow 2).mul (fieldDivergence_continuous basis hX)).integrable_of_hasCompactSupport
      hcdiv.mul_left
  have hi_V2d : Integrable
      (fun x ↦ V x ^ 2 * radialWeightScaleDerivative weissBoundaryProfile 0 r x) := by
    have heq : (fun x ↦ V x ^ 2 * radialWeightScaleDerivative weissBoundaryProfile 0 r x) =
        fun x ↦ r⁻¹ * ((m + 1 : ℝ) * (V x ^ 2 * pr x) - V x ^ 2 * fieldDivergence basis X x) := by
      funext x
      rw [hdiv_X x]
      field_simp
      ring
    rw [heq]
    exact ((hi_V2p.const_mul (m + 1 : ℝ)).sub hi_V2div).const_mul r⁻¹
  have hi_Vin : Integrable (fun x ↦ V x * inner ℝ (gradient V x) (X x)) := by
    obtain ⟨CX, hCX⟩ := hcX.exists_bound_of_continuous hX.continuous
    have hVbound (x : Space (m + 1)) : ‖gradient V x‖ ≤ L := by
      rw [gradient, LinearIsometryEquiv.norm_map]
      exact norm_fderiv_le_of_lipschitz ℝ hV
    have hiK : IntegrableOn (fun x ↦ V x * inner ℝ (gradient V x) (X x)) (tsupport X) := by
      apply (continuousOn_const.integrableOn_compact hcX (f := fun _ ↦ (L : ℝ) * |CX|)).mono'
        (hV.continuous.measurable.mul
          ((measurable_gradient V).inner (𝕜 := ℝ) hX.continuous.measurable)).aestronglyMeasurable
      filter_upwards with x
      simp only [Pi.mul_apply]
      rw [norm_mul, Real.norm_of_nonneg (hval x).1]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hval x).2).trans
        ((norm_inner_le_norm (𝕜 := ℝ) _ _).trans
          (mul_le_mul (hVbound x) ((hCX x).trans (le_abs_self CX)) (norm_nonneg _) L.coe_nonneg))
    exact hiK.integrable_of_forall_notMem_eq_zero (fun x hx ↦ by
      simp [image_eq_zero_of_notMem_tsupport hx])
  convert hd_prod using 1
  have hr4 : r ^ (-(m + 3 : ℤ) - 1) = r ^ (-(m + 4 : ℤ)) := congrArg (r ^ ·) (by ring)
  have hr34 : r ^ (-(m + 3 : ℤ)) = r ^ (-(m + 4 : ℤ)) * r := by
    have h1 : r ^ (-(m + 3 : ℤ)) = r ^ (-(m + 4 : ℤ) + 1) := congrArg (r ^ ·) (by ring)
    rw [h1, zpow_add₀ hr0.ne', zpow_one]
  have hdiv_split : (∫ x, V x ^ 2 * fieldDivergence basis X x) =
      (m + 1 : ℝ) * (∫ x, V x ^ 2 * pr x) -
        r * ∫ x, V x ^ 2 * radialWeightScaleDerivative weissBoundaryProfile 0 r x := by
    have hcongr : (∫ x, V x ^ 2 * fieldDivergence basis X x) =
        ∫ x, (m + 1 : ℝ) * (V x ^ 2 * pr x) -
          r * (V x ^ 2 * radialWeightScaleDerivative weissBoundaryProfile 0 r x) :=
      integral_congr_ae (Eventually.of_forall (fun x ↦ by dsimp only; rw [hdiv_X x]; ring))
    have hs := integral_sub (hi_V2p.const_mul (m + 1 : ℝ)) (hi_V2d.const_mul r)
    rw [hcongr, hs, integral_const_mul, integral_const_mul]
  have hVin_eq : (∫ x, V x * inner ℝ (gradient V x) (X x)) =
      ∫ x, pr x * (V x * inner ℝ (gradient V x) x) :=
    integral_congr_ae (Eventually.of_forall (fun x ↦ by
      dsimp only [X]; rw [real_inner_smul_right]; ring))
  have hi_prVin : Integrable (fun x ↦ pr x * (V x * inner ℝ (gradient V x) x)) :=
    hi_Vin.congr (Eventually.of_forall (fun x ↦ by
      dsimp only [X]; rw [real_inner_smul_right]; ring))
  have hi_prV2 : Integrable (fun x ↦ pr x * V x ^ 2) :=
    hi_V2p.congr (Eventually.of_forall (fun x ↦ mul_comm _ _))
  have hsubR := integral_sub hi_prVin hi_prV2
  have hcongrR : (∫ x, pr x * (V x * inner ℝ (gradient V x) x - V x ^ 2)) =
      (∫ x, pr x * (V x * inner ℝ (gradient V x) x)) - ∫ x, V x ^ 2 * pr x := by
    have hc1 : (∫ x, pr x * (V x * inner ℝ (gradient V x) x - V x ^ 2)) =
        ∫ x, pr x * (V x * inner ℝ (gradient V x) x) - pr x * V x ^ 2 :=
      integral_congr_ae (Eventually.of_forall (fun x ↦ by ring))
    have hc2 : (∫ x, pr x * V x ^ 2) = ∫ x, V x ^ 2 * pr x :=
      integral_congr_ae (Eventually.of_forall (fun x ↦ mul_comm _ _))
    rw [hc1, hsubR, hc2]
  rw [hcongrR, hr4, hr34]
  rw [hdiv_split, hVin_eq] at hibp
  dsimp only [pr] at hcongrR hibp ⊢
  push_cast
  linear_combination 2 * r ^ (-(m + 4 : ℤ)) * hibp

/-- Smooth radial Weiss derivative identity (TB3): differentiating `smoothWeissFunctional` yields
a nonnegative squared homogeneity defect minus a reaction error of order `O(1)`. -/
theorem RigidityHypotheses.smoothWeissFunctional_hasDerivAt
    {m : ℕ} {g : Space m → ℝ} {u V : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ r : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {p : ℕ → Space (m + 1)} (hV : LipschitzWith ⟨κ, h.kappa_pos.le⟩ V)
    (hval : ∀ x, V x ∈ Icc 0 1)
    (hlim : ∀ K : Set (Space (m + 1)), IsCompact K →
      TendstoUniformlyOn (fun j x ↦ zeroExtension g u (p j + x)) V atTop K)
    (hr0 : 0 < r) :
    HasDerivAt (smoothWeissFunctional f V)
      (4 * r ^ (-(m + 4 : ℤ)) *
          (∫ x, radialWeight weissBoundaryProfile 0 r x *
            (inner ℝ (gradient V x) x - V x) ^ 2) -
        2 * r ^ (-(m + 2 : ℤ)) *
          (∫ x, radialWeight weissProfile 0 r x * (V x * f (V x)))) r := by
  have hdE := hr.smoothWeissEnergy_hasDerivAt h hV hval hlim hr0
  have hdB := smoothWeissBoundary_hasDerivAt hV hval hr0
  have hd := hdE.sub hdB
  change HasDerivAt (smoothWeissFunctional f V) _ r at hd
  convert hd using 1
  let pr := radialWeight weissBoundaryProfile (0 : Space (m + 1)) r
  have hzero_p : ∀ s : ℝ, 2 ≤ s → weissBoundaryProfile s = 0 :=
    fun _ hs ↦ weissBoundaryProfile_zero (by linarith)
  have hpr_cont : ContDiff ℝ 1 pr := contDiff_radialWeight weissBoundaryProfile_contDiff 0 r
  have hpr_comp : HasCompactSupport pr :=
    (isCompact_closedBall 0 (2 * r)).of_isClosed_subset (isClosed_tsupport _)
      (tsupport_radialWeight_subset hzero_p 0 hr0)
  have hVbound (x : Space (m + 1)) : ‖gradient V x‖ ≤ κ := by
    rw [gradient, LinearIsometryEquiv.norm_map]
    exact norm_fderiv_le_of_lipschitz ℝ hV
  have hi_Vin : Integrable (fun x ↦ pr x * (V x * inner ℝ (gradient V x) x)) := by
    let K := tsupport pr
    have hK : IsCompact K := hpr_comp
    obtain ⟨Rx, hRx⟩ := hK.isBounded.subset_closedBall (0 : Space (m + 1))
    obtain ⟨Cp, hCp⟩ := hpr_comp.exists_bound_of_continuous hpr_cont.continuous
    have hiK : IntegrableOn (fun x ↦ pr x * (V x * inner ℝ (gradient V x) x)) K := by
      apply (continuousOn_const.integrableOn_compact hK
        (f := fun _ ↦ |Cp| * (κ * |Rx|))).mono'
        (hpr_cont.continuous.measurable.mul (hV.continuous.measurable.mul
          ((measurable_gradient V).inner (𝕜 := ℝ) measurable_id))).aestronglyMeasurable
      filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
      simp only [Pi.mul_apply, id_eq]
      rw [norm_mul, norm_mul, Real.norm_of_nonneg (hval x).1]
      have hnx0 : ‖x‖ ≤ Rx := by simpa only [mem_closedBall, dist_zero_right] using hRx hx
      have hnx : ‖x‖ ≤ |Rx| := hnx0.trans (le_abs_self Rx)
      have hin : ‖inner ℝ (gradient V x) x‖ ≤ κ * |Rx| :=
        (norm_inner_le_norm (𝕜 := ℝ) _ _).trans
          (mul_le_mul (hVbound x) hnx (norm_nonneg _) h.kappa_pos.le)
      exact mul_le_mul ((hCp x).trans (le_abs_self Cp))
        ((mul_le_of_le_one_left (norm_nonneg _) (hval x).2).trans hin)
        (mul_nonneg (hval x).1 (norm_nonneg _)) (abs_nonneg Cp)
    exact hiK.integrable_of_forall_notMem_eq_zero (fun x hx ↦ by
      simp [image_eq_zero_of_notMem_tsupport hx])
  have hi_V2 : Integrable (fun x ↦ pr x * V x ^ 2) :=
    (hpr_cont.continuous.mul (hV.continuous.pow 2)).integrable_of_hasCompactSupport
      hpr_comp.mul_right
  have hi_g2 : Integrable (fun x ↦ pr x * inner ℝ (gradient V x) x ^ 2) := by
    let K := tsupport pr
    have hK : IsCompact K := hpr_comp
    obtain ⟨Rx, hRx⟩ := hK.isBounded.subset_closedBall (0 : Space (m + 1))
    obtain ⟨Cp, hCp⟩ := hpr_comp.exists_bound_of_continuous hpr_cont.continuous
    have hiK : IntegrableOn (fun x ↦ pr x * inner ℝ (gradient V x) x ^ 2) K := by
      apply (continuousOn_const.integrableOn_compact hK
        (f := fun _ ↦ |Cp| * (κ * |Rx|) ^ 2)).mono'
        (hpr_cont.continuous.measurable.mul
          (((measurable_gradient V).inner (𝕜 := ℝ) measurable_id).pow_const 2)).aestronglyMeasurable
      filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
      simp only [Pi.mul_apply, id_eq]
      rw [norm_mul, norm_pow]
      have hnx0 : ‖x‖ ≤ Rx := by simpa only [mem_closedBall, dist_zero_right] using hRx hx
      have hnx : ‖x‖ ≤ |Rx| := hnx0.trans (le_abs_self Rx)
      have hin : ‖inner ℝ (gradient V x) x‖ ≤ κ * |Rx| :=
        (norm_inner_le_norm (𝕜 := ℝ) _ _).trans
          (mul_le_mul (hVbound x) hnx (norm_nonneg _) h.kappa_pos.le)
      exact mul_le_mul ((hCp x).trans (le_abs_self Cp))
        (pow_le_pow_left₀ (norm_nonneg _) hin 2) (pow_nonneg (norm_nonneg _) 2) (abs_nonneg Cp)
    exact hiK.integrable_of_forall_notMem_eq_zero (fun x hx ↦ by
      simp [image_eq_zero_of_notMem_tsupport hx])
  have hiA : Integrable (fun x ↦ pr x *
      (inner ℝ (gradient V x) x ^ 2 - V x * inner ℝ (gradient V x) x)) :=
    (hi_g2.sub hi_Vin).congr (Eventually.of_forall (fun x ↦ by simp only [Pi.sub_apply]; ring))
  have hiB : Integrable (fun x ↦ pr x *
      (V x * inner ℝ (gradient V x) x - V x ^ 2)) :=
    (hi_Vin.sub hi_V2).congr (Eventually.of_forall (fun x ↦ by simp only [Pi.sub_apply]; ring))
  have hsub := integral_sub hiA hiB
  have hcongr : (∫ x, pr x * (inner ℝ (gradient V x) x - V x) ^ 2) =
      ∫ x, (pr x * (inner ℝ (gradient V x) x ^ 2 - V x * inner ℝ (gradient V x) x) -
        pr x * (V x * inner ℝ (gradient V x) x - V x ^ 2)) :=
    integral_congr_ae (Eventually.of_forall (fun x ↦ by ring))
  rw [show radialWeight weissBoundaryProfile 0 r = pr from rfl, hcongr, hsub]
  ring

/-- Along a `C¹` ray, `v (a • x) / a - v x` is controlled by the integral of
`‖⟨∇v (t • x), t • x⟩ - v (t • x)‖` for `1 ≤ a`. -/
theorem norm_homogeneity_sub_le_integral {d : ℕ} {v : Space d → ℝ}
    (hv : ContDiff ℝ 1 v) (x : Space d) {a : ℝ} (ha : 1 ≤ a) :
    ‖v (a • x) / a - v x‖ ≤
      ∫ t in Icc (1 : ℝ) a, ‖inner ℝ (gradient v (t • x)) (t • x) - v (t • x)‖ := by
  have hg : Continuous (gradient v) :=
    (toDual ℝ (Space d)).symm.continuous.comp (hv.continuous_fderiv one_ne_zero)
  have hc : Continuous (fun t : ℝ ↦ t • x) := continuous_id.smul continuous_const
  let D : ℝ → ℝ := fun t ↦ (inner ℝ (gradient v (t • x)) (t • x) - v (t • x)) / t ^ 2
  have hD_cont : ContinuousOn D (Icc 1 a) :=
    (((hg.comp hc).inner hc).sub (hv.continuous.comp hc)).continuousOn.div
      (continuous_id.pow 2).continuousOn (fun t ht ↦ pow_ne_zero 2 (by linarith [ht.1]))
  have hd (t : ℝ) (ht : t ∈ Icc (1 : ℝ) a) :
      HasDerivAt (fun s : ℝ ↦ v (s • x) / s) (D t) t := by
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hl : HasDerivAt (fun s : ℝ ↦ s • x) x t := by
      simpa only [one_smul, id_eq] using (hasDerivAt_id t).smul_const x
    have hnum := (hv.differentiable one_ne_zero (t • x)).hasFDerivAt.comp_hasDerivAt t hl
    have hq := hnum.div (hasDerivAt_id t) ht0
    convert hq using 1
    · rfl
    · change (inner ℝ (gradient v (t • x)) (t • x) - v (t • x)) / t ^ 2 = _
      rw [← inner_gradient_left, real_inner_smul_right]
      simp only [id_eq, Function.comp_apply]
      ring
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (f := fun s : ℝ ↦ v (s • x) / s)
    ha ((hv.continuous.comp hc).continuousOn.div continuousOn_id
      (fun t ht ↦ by linarith [ht.1]))
    (fun t ht ↦ hd t ⟨ht.1.le, ht.2.le⟩)
    (intervalIntegrable_iff_integrableOn_Icc_of_le ha |>.mpr
      (hD_cont.integrableOn_compact isCompact_Icc))
  simp only [one_smul, div_one] at hftc
  rw [← hftc, intervalIntegral.integral_of_le ha, ← integral_Icc_eq_integral_Ioc]
  apply (norm_integral_le_integral_norm _).trans
  apply setIntegral_mono_on (hD_cont.norm.integrableOn_compact isCompact_Icc)
    ((((hg.comp hc).inner hc).sub (hv.continuous.comp hc)).norm.continuousOn.integrableOn_compact
      isCompact_Icc) measurableSet_Icc
  intro t ht
  dsimp only [D]
  rw [norm_div, Real.norm_of_nonneg (sq_nonneg t)]
  exact div_le_self (norm_nonneg _) (by nlinarith [ht.1])

/-- Smooth ball estimate for `v (a • x) / a - v x` in terms of `‖⟨∇v x, x⟩ - v x‖`. -/
theorem integral_norm_homogeneity_sub_le {d : ℕ} {v : Space d → ℝ}
    (hv : ContDiff ℝ 1 v) {r a : ℝ} (hr : 0 ≤ r) (ha : 1 ≤ a) :
    (∫ x in closedBall 0 r, ‖v (a • x) / a - v x‖) ≤
      (a - 1) * ∫ x in closedBall 0 (a * r), ‖inner ℝ (gradient v x) x - v x‖ := by
  have hg : Continuous (gradient v) :=
    (toDual ℝ (Space d)).symm.continuous.comp (hv.continuous_fderiv one_ne_zero)
  let A : Space d → ℝ := fun x ↦ ‖inner ℝ (gradient v x) x - v x‖
  have hA : Continuous A := ((hg.inner continuous_id).sub hv.continuous).norm
  let F : Space d → ℝ → ℝ := fun x t ↦ A (t • x)
  have hF : Continuous F.uncurry := hA.comp (continuous_snd.smul continuous_fst)
  have hfi : Integrable (Function.uncurry F)
      ((volume.restrict (closedBall 0 r)).prod (volume.restrict (Icc (1 : ℝ) a))) := by
    rw [Measure.prod_restrict]
    exact hF.continuousOn.integrableOn_compact ((isCompact_closedBall 0 r).prod isCompact_Icc)
  have hparam := continuous_parametric_integral_of_continuous (μ := volume) hF
    (isCompact_Icc (a := (1 : ℝ)) (b := a))
  have hi : IntegrableOn (fun x : Space d ↦ ‖v (a • x) / a - v x‖) (closedBall 0 r) :=
    ((((hv.continuous.comp (continuous_id.const_smul a)).div_const a).sub hv.continuous).norm)
      |>.continuousOn.integrableOn_compact (isCompact_closedBall 0 r)
  have hle : (∫ x in closedBall 0 r, ‖v (a • x) / a - v x‖) ≤
      ∫ x in closedBall 0 r, ∫ t in Icc (1 : ℝ) a, F x t :=
    integral_mono hi (hparam.continuousOn.integrableOn_compact (isCompact_closedBall 0 r))
      (fun x ↦ norm_homogeneity_sub_le_integral hv x ha)
  rw [integral_integral_swap hfi] at hle
  apply hle.trans
  have ht : ∀ t ∈ Icc (1 : ℝ) a,
      (∫ x in closedBall 0 r, F x t) ≤ ∫ x in closedBall 0 (a * r), A x :=
    fun t ht ↦ integral_dilate_closedBall_le hA (fun _ ↦ norm_nonneg _) hr ht.1 ht.2
  have he := setIntegral_mono_on hfi.integral_prod_right
    (continuousOn_const.integrableOn_compact (μ := volume) isCompact_Icc) measurableSet_Icc ht
  simpa only [setIntegral_const, Real.volume_real_Icc, max_eq_left (sub_nonneg.mpr ha),
    smul_eq_mul, Function.uncurry_apply_pair] using he

/-- Every nonnegative Lipschitz function vanishing at `0` whose homogeneity defect
`⟨∇W x, x⟩ - W x` has zero `L²` norm on all closed balls is positively homogeneous of degree `1`. -/
theorem one_homogeneous_of_radial_defect_zero {d : ℕ} {W : Space d → ℝ} {L : ℝ≥0}
    (hW : LipschitzWith L W) (hW0 : ∀ x, 0 ≤ W x) (hzero : W 0 = 0)
    (hdef : ∀ R : ℝ, 0 < R →
      (∫ x in closedBall 0 R, (inner ℝ (gradient W x) x - W x) ^ 2) = 0) :
    ∀ t : ℝ, 0 ≤ t → ∀ x : Space d, W (t • x) = t * W x := by
  have hL1 (R : ℝ) (hR : 0 < R) :
      (∫ x in closedBall 0 R, ‖inner ℝ (gradient W x) x - W x‖) = 0 := by
    let K := closedBall (0 : Space d) R
    have hK : IsCompact K := isCompact_closedBall _ _
    have hWbound (x : Space d) : ‖gradient W x‖ ≤ L := by
      rw [gradient, LinearIsometryEquiv.norm_map]
      exact norm_fderiv_le_of_lipschitz ℝ hW
    have hi2 : IntegrableOn (fun x ↦ (inner ℝ (gradient W x) x - W x) ^ 2) K := by
      apply (continuousOn_const.integrableOn_compact hK
        (f := fun _ ↦ (2 * (L : ℝ) * R) ^ 2)).mono'
        ((((measurable_gradient W).inner (𝕜 := ℝ) measurable_id).sub
          hW.continuous.measurable).pow_const 2).aestronglyMeasurable
      filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
      have hnx : ‖x‖ ≤ R := by simpa only [K, mem_closedBall, dist_zero_right] using hx
      have hWx : ‖W x‖ ≤ L * R := by
        have hd := hW.dist_le_mul x 0
        rw [hzero, dist_zero_right, dist_zero_right] at hd
        exact hd.trans (mul_le_mul_of_nonneg_left hnx L.coe_nonneg)
      have hin : ‖inner ℝ (gradient W x) x‖ ≤ L * R :=
        (norm_inner_le_norm (𝕜 := ℝ) _ _).trans
          (mul_le_mul (hWbound x) hnx (norm_nonneg _) L.coe_nonneg)
      simp only [Pi.sub_apply, id_eq]
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) ((norm_sub_le _ _).trans (by linarith)) 2
    have hae := (integral_eq_zero_iff_of_nonneg_ae
      (Eventually.of_forall (fun _ ↦ sq_nonneg _)) hi2).mp (hdef R hR)
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hae] with x hx
    simp only [Pi.zero_apply] at hx ⊢
    rw [sq_eq_zero_iff.mp hx, norm_zero]
  have hout {a : ℝ} (ha : 1 ≤ a) (x₀ : Space d) : W (a • x₀) / a = W x₀ := by
    have ha0 : 0 < a := zero_lt_one.trans_le ha
    let r : ℝ := ‖x₀‖ + 1
    have hr : 0 < r := by dsimp [r]; positivity
    let B : ℝ := (L : ℝ) * (a * r + 2)
    have hB0 : 0 ≤ B := by dsimp [B]; positivity
    let w : Space d → ℝ := fun x ↦ min (W x) B
    have hw : LocallyLipschitz w := hW.locallyLipschitz.min (LocallyLipschitz.const B)
    have hwval (x : Space d) : w x ∈ Icc 0 B := ⟨le_min (hW0 x) hB0, min_le_right _ _⟩
    have heq_ball : EqOn w W (ball 0 (a * r + 1)) := by
      intro x hx
      have hnx : ‖x‖ < a * r + 1 := by simpa only [mem_ball, dist_zero_right] using hx
      have hd := hW.dist_le_mul x 0
      rw [hzero, dist_zero_right, dist_zero_right, Real.norm_of_nonneg (hW0 x)] at hd
      have hle : W x ≤ B := by
        dsimp [B]
        exact hd.trans (mul_le_mul_of_nonneg_left (by linarith) L.coe_nonneg)
      exact min_eq_left hle
    let K1 := closedBall (0 : Space d) r
    let K2 := closedBall (0 : Space d) (a * r)
    have hK1 : IsCompact K1 := isCompact_closedBall _ _
    have hK2 : IsCompact K2 := isCompact_closedBall _ _
    obtain ⟨Cg, hCg⟩ := normalizedMollify_gradient_bound_of_locallyLipschitz hw hK2
    have htL : Tendsto (fun n ↦ ∫ x in K1,
        ‖normalizedMollify w n (a • x) / a - normalizedMollify w n x‖) atTop
        (𝓝 (∫ x in K1, ‖w (a • x) / a - w x‖)) := by
      apply tendsto_integral_of_dominated_convergence (fun _ ↦ 2 * B)
      · intro n
        have hc := (normalizedMollify_contDiff hw.continuous n).continuous
        exact ((((hc.comp (continuous_id.const_smul a)).div_const a).sub hc).norm.aestronglyMeasurable).restrict
      · exact continuousOn_const.integrableOn_compact hK1
      · intro n
        filter_upwards with x
        have hma := normalizedMollify_mem_Icc_of_bounds hw.continuous hwval n (a • x)
        have hmx := normalizedMollify_mem_Icc_of_bounds hw.continuous hwval n x
        rw [norm_norm]
        apply (norm_sub_le _ _).trans
        rw [norm_div, Real.norm_of_nonneg hma.1, Real.norm_of_nonneg ha0.le,
          Real.norm_of_nonneg hmx.1]
        have hdiv : normalizedMollify w n (a • x) / a ≤ B :=
          (div_le_self hma.1 ha).trans hma.2
        linarith [hmx.2]
      · filter_upwards with x
        exact (((normalizedMollify_tendsto hw.continuous (a • x)).div_const a).sub
          (normalizedMollify_tendsto hw.continuous x)).norm
    have htR : Tendsto (fun n ↦ (a - 1) * ∫ x in K2,
        ‖inner ℝ (gradient (normalizedMollify w n) x) x - normalizedMollify w n x‖) atTop
        (𝓝 ((a - 1) * ∫ x in K2, ‖inner ℝ (gradient w x) x - w x‖)) := by
      apply Tendsto.const_mul
      apply tendsto_integral_of_dominated_convergence (fun _ ↦ (Cg : ℝ) * (a * r) + B)
      · intro n
        have hc := (normalizedMollify_contDiff hw.continuous n).continuous
        exact (((measurable_gradient _).inner (𝕜 := ℝ) measurable_id |>.sub hc.measurable).norm.aestronglyMeasurable).restrict
      · exact continuousOn_const.integrableOn_compact hK2
      · intro n
        filter_upwards [ae_restrict_mem hK2.measurableSet] with x hx
        have hmx := normalizedMollify_mem_Icc_of_bounds hw.continuous hwval n x
        have hnx : ‖x‖ ≤ a * r := by simpa only [K2, mem_closedBall, dist_zero_right] using hx
        rw [norm_norm]
        apply (norm_sub_le _ _).trans
        apply add_le_add
        · exact (norm_inner_le_norm (𝕜 := ℝ) _ _).trans
            (mul_le_mul (hCg n x hx) hnx (norm_nonneg _) Cg.coe_nonneg)
        · rw [Real.norm_of_nonneg hmx.1]
          exact hmx.2
      · filter_upwards [ae_restrict_of_ae
          (normalizedMollify_gradient_tendsto_ae_of_locallyLipschitz hw)] with x hx
        exact ((hx.inner tendsto_const_nhds).sub (normalizedMollify_tendsto hw.continuous x)).norm
    have hle := le_of_tendsto_of_tendsto htL htR (Eventually.of_forall (fun n ↦
      integral_norm_homogeneity_sub_le
        ((normalizedMollify_contDiff hw.continuous n).of_le (by simp)) hr.le ha))
    have hK2_eq : (∫ x in K2, ‖inner ℝ (gradient w x) x - w x‖) =
        ∫ x in K2, ‖inner ℝ (gradient W x) x - W x‖ := by
      apply setIntegral_congr_fun hK2.measurableSet
      intro x hx
      have hnx : ‖x‖ ≤ a * r := by simpa only [K2, mem_closedBall, dist_zero_right] using hx
      have hxb : x ∈ ball 0 (a * r + 1) := by
        simp only [mem_ball, dist_zero_right]; linarith
      have hev : w =ᶠ[𝓝 x] W := heq_ball.eventuallyEq_of_mem (isOpen_ball.mem_nhds hxb)
      dsimp only
      rw [heq_ball hxb, show gradient w x = gradient W x by simp [gradient, hev.fderiv_eq]]
    have hK1_eq : (∫ x in K1, ‖w (a • x) / a - w x‖) = ∫ x in K1, ‖W (a • x) / a - W x‖ := by
      apply setIntegral_congr_fun hK1.measurableSet
      intro x hx
      have hnx : ‖x‖ ≤ r := by simpa only [K1, mem_closedBall, dist_zero_right] using hx
      have hxb1 : x ∈ ball 0 (a * r + 1) := by
        simp only [mem_ball, dist_zero_right]; nlinarith
      have hxb2 : a • x ∈ ball 0 (a * r + 1) := by
        simp only [mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg ha0.le]
        nlinarith
      dsimp only
      rw [heq_ball hxb1, heq_ball hxb2]
    rw [hK1_eq, hK2_eq, hL1 (a * r) (mul_pos ha0 hr), mul_zero] at hle
    have hint0 : (∫ x in K1, ‖W (a • x) / a - W x‖) = 0 :=
      le_antisymm hle (integral_nonneg (fun _ ↦ norm_nonneg _))
    by_contra hne
    let δ : ℝ := ‖W (a • x₀) / a - W x₀‖ / 2
    have hδ : 0 < δ := half_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne))
    have hcont : Continuous (fun x ↦ ‖W (a • x) / a - W x‖) :=
      (((hW.continuous.comp (continuous_id.const_smul a)).div_const a).sub hW.continuous).norm
    obtain ⟨ρ₀, hρ₀, hball⟩ := Metric.continuousAt_iff.mp hcont.continuousAt δ hδ
    let ρ : ℝ := min ρ₀ 1
    have hρ : 0 < ρ := lt_min hρ₀ zero_lt_one
    have hsub_K1 : ball x₀ ρ ⊆ K1 := by
      intro x hx
      have hdx : ‖x - x₀‖ < ρ := by simpa only [mem_ball, dist_eq_norm] using hx
      have hρ1 : ρ ≤ 1 := min_le_right _ _
      simp only [K1, r, mem_closedBall, dist_zero_right]
      calc
        ‖x‖ = ‖(x - x₀) + x₀‖ := by abel_nf
        _ ≤ ‖x - x₀‖ + ‖x₀‖ := norm_add_le _ _
        _ ≤ ‖x₀‖ + 1 := by linarith
    have hlow : (∫ _x in ball x₀ ρ, δ) ≤ ∫ x in K1, ‖W (a • x) / a - W x‖ := by
      calc
        (∫ _x in ball x₀ ρ, δ) ≤ ∫ x in ball x₀ ρ, ‖W (a • x) / a - W x‖ := by
          apply setIntegral_mono_on (continuousOn_const.integrableOn_compact
            (isCompact_closedBall x₀ ρ) |>.mono_set ball_subset_closedBall)
            ((hcont.continuousOn.integrableOn_compact hK1).mono_set hsub_K1) isOpen_ball.measurableSet
          intro x hx
          have hx' : dist x x₀ < ρ₀ := lt_of_lt_of_le (mem_ball.mp hx) (min_le_left _ _)
          have hd := hball hx'
          rw [Real.dist_eq] at hd
          dsimp [δ] at hd ⊢
          linarith [(abs_lt.mp hd).1]
        _ ≤ ∫ x in K1, ‖W (a • x) / a - W x‖ :=
          setIntegral_mono_set (hcont.continuousOn.integrableOn_compact hK1)
            (Eventually.of_forall (fun _ ↦ norm_nonneg _)) (Eventually.of_forall hsub_K1)
    rw [setIntegral_const, smul_eq_mul, hint0] at hlow
    have hvol : 0 < volume.real (ball x₀ ρ) :=
      ENNReal.toReal_pos (measure_ball_pos volume x₀ hρ).ne' measure_ball_lt_top.ne
    linarith [mul_pos hvol hδ]
  intro t ht x
  rcases eq_or_lt_of_le ht with rfl | ht0
  · simp [hzero]
  · by_cases ht1 : 1 ≤ t
    · rw [mul_comm]
      exact (div_eq_iff ht0.ne').mp (hout ht1 x)
    · push Not at ht1
      have hinv : 1 ≤ t⁻¹ := by
        rw [inv_eq_one_div]
        exact (le_div_iff₀ ht0).mpr (by linarith)
      have he := hout hinv (t • x)
      rw [inv_smul_smul₀ ht0.ne', div_inv_eq_mul, mul_comm] at he
      exact he.symm

/-- Every microscopic blowup limit at a free-boundary point `V 0 = 0` of a physical translation
limit is positively homogeneous of degree `1` (TB4). -/
theorem RigidityHypotheses.microscopic_blowup_one_homogeneous
    {m : ℕ} {g : Space m → ℝ} {u V W_lim : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {p_seq : ℕ → Space (m + 1)} {r_seq : ℕ → ℝ}
    (hV : LipschitzWith ⟨κ, h.kappa_pos.le⟩ V) (hval : ∀ x, V x ∈ Icc 0 1)
    (hV0 : V 0 = 0)
    (hlim : ∀ K : Set (Space (m + 1)), IsCompact K →
      TendstoUniformlyOn (fun j x ↦ zeroExtension g u (p_seq j + x)) V atTop K)
    (hr_pos : ∀ j, 0 < r_seq j) (hr_lim : Tendsto r_seq atTop (𝓝 0))
    (hW : LipschitzWith ⟨κ, h.kappa_pos.le⟩ W_lim) (hW0 : ∀ x, 0 ≤ W_lim x)
    (hW_zero : W_lim 0 = 0)
    (hWlim : ∀ K : Set (Space (m + 1)), IsCompact K →
      TendstoUniformlyOn (fun j x ↦ V (r_seq j • x) / r_seq j) W_lim atTop K) :
    ∀ t : ℝ, 0 ≤ t → ∀ x : Space (m + 1), W_lim (t • x) = t * W_lim x := by
  obtain ⟨M_f, hM_f⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (h.reaction_contDiffOn.continuousOn.mono Icc_subset_Ici_self)
  have hM0 : 0 ≤ M_f := (norm_nonneg _).trans (hM_f 0 ⟨le_rfl, zero_le_one⟩)
  let B1 := closedBall (0 : Space (m + 1)) 1
  have hB1 : IsCompact B1 := isCompact_closedBall _ _
  let C₀ : ℝ := 2 * κ * M_f * volume.real B1
  have hC₀ : 0 ≤ C₀ := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) h.kappa_pos.le) hM0)
    measureReal_nonneg
  let G : ℝ → ℝ := fun s ↦ smoothWeissFunctional f V s + C₀ * s
  have hreact_bound {s : ℝ} (hs : 0 < s) :
      |2 * s ^ (-(m + 2 : ℤ)) * ∫ x, radialWeight weissProfile 0 s x * (V x * f (V x))| ≤ C₀ := by
    let H : Space (m + 1) → ℝ := fun x ↦ radialWeight weissProfile 0 s x * (V x * f (V x))
    have hchg := Measure.integral_comp_smul volume H s
    simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul] at hchg
    rw [abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hs.le (m + 1)))] at hchg
    have hs_pow : s ^ (-(m + 2 : ℤ)) * s ^ (m + 1) = s⁻¹ := by
      have h1 : (s ^ (m + 1) : ℝ) = s ^ ((m + 1 : ℕ) : ℤ) := (zpow_natCast s (m + 1)).symm
      rw [h1, ← zpow_add₀ hs.ne', ← zpow_neg_one]
      exact congrArg (s ^ ·) (by push_cast; ring)
    have hint : ∫ x, H x = s ^ (m + 1) * ∫ y, H (s • y) := by
      rw [hchg, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hs.ne'), one_mul]
    have hrew : 2 * s ^ (-(m + 2 : ℤ)) * (∫ x, H x) =
        2 * ∫ y in B1, weissProfile (‖y‖ ^ 2) * ((V (s • y) / s) * f (V (s • y))) := by
      have hpre : 2 * s ^ (-(m + 2 : ℤ)) * (∫ x, H x) = 2 * ∫ y, s⁻¹ * H (s • y) := by
        calc
          2 * s ^ (-(m + 2 : ℤ)) * (∫ x, H x) =
              2 * s ^ (-(m + 2 : ℤ)) * (s ^ (m + 1) * ∫ y, H (s • y)) := by rw [hint]
          _ = 2 * ((s ^ (-(m + 2 : ℤ)) * s ^ (m + 1)) * ∫ y, H (s • y)) := by ring
          _ = 2 * (s⁻¹ * ∫ y, H (s • y)) := by rw [hs_pow]
          _ = 2 * ∫ y, s⁻¹ * H (s • y) := by rw [integral_const_mul]
      rw [hpre]
      congr 1
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := B1) (fun y hy ↦ by
        have hny : 1 < ‖y‖ := by simpa only [B1, mem_closedBall, dist_zero_right, not_le] using hy
        have h1 : 1 ≤ ‖s • y - 0‖ ^ 2 / s ^ 2 := by
          rw [sub_zero, norm_smul, Real.norm_of_nonneg hs.le, mul_pow,
            mul_div_cancel_left₀ _ (sq_pos_of_pos hs).ne']
          nlinarith
        dsimp only [H, radialWeight]
        rw [weissProfile_zero h1, zero_mul, mul_zero])]
      apply setIntegral_congr_fun hB1.measurableSet
      intro y _
      dsimp only [H, radialWeight]
      rw [sub_zero, norm_smul, Real.norm_of_nonneg hs.le, mul_pow,
        mul_div_cancel_left₀ _ (sq_pos_of_pos hs).ne']
      field_simp
    change |2 * s ^ (-(m + 2 : ℤ)) * ∫ x, H x| ≤ C₀
    rw [hrew, ← Real.norm_eq_abs, norm_mul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have hf_cont : Continuous (fun y ↦ f (V (s • y))) :=
      h.reaction_contDiffOn.continuousOn.comp_continuous
        (hV.continuous.comp (continuous_id.const_smul s)) (fun y ↦ (hval _).1)
    have hi : IntegrableOn
        (fun y ↦ weissProfile (‖y‖ ^ 2) * ((V (s • y) / s) * f (V (s • y)))) B1 :=
      ((weissProfile_contDiff.continuous.comp (continuous_norm.pow 2)).mul
        (((lipschitzWith_rescale_div hV hs).continuous).mul
          hf_cont)).continuousOn.integrableOn_compact hB1
    have hle : ‖∫ y in B1, weissProfile (‖y‖ ^ 2) * ((V (s • y) / s) * f (V (s • y)))‖ ≤
        κ * M_f * volume.real B1 := by
      calc
        _ ≤ ∫ y in B1, ‖weissProfile (‖y‖ ^ 2) * ((V (s • y) / s) * f (V (s • y)))‖ :=
          norm_integral_le_integral_norm _
        _ ≤ ∫ _y in B1, κ * M_f := by
          apply setIntegral_mono_on hi.norm (continuousOn_const.integrableOn_compact hB1)
            hB1.measurableSet
          intro y hy
          have hny : ‖y‖ ≤ 1 := by simpa only [B1, mem_closedBall, dist_zero_right] using hy
          have hw := weissProfile_mem_Icc (sq_nonneg ‖y‖)
          have hvy : ‖V (s • y) / s‖ ≤ κ := by
            have hd := (lipschitzWith_rescale_div hV hs).dist_le_mul y 0
            simp only [smul_zero, hV0, zero_div, dist_zero_right] at hd
            exact hd.trans (mul_le_of_le_one_right h.kappa_pos.le hny)
          rw [norm_mul, norm_mul, Real.norm_of_nonneg hw.1]
          exact (mul_le_of_le_one_left (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hw.2).trans
            (mul_le_mul hvy (hM_f _ (hval _)) (norm_nonneg _) h.kappa_pos.le)
        _ = κ * M_f * volume.real B1 := by rw [setIntegral_const, smul_eq_mul]; ring
    dsimp only [C₀]
    linarith
  have hdG {s : ℝ} (hs : 0 < s) :
      HasDerivAt G
        ((4 * s ^ (-(m + 4 : ℤ)) *
            ∫ x, radialWeight weissBoundaryProfile 0 s x *
              (inner ℝ (gradient V x) x - V x) ^ 2) -
          (2 * s ^ (-(m + 2 : ℤ)) *
            ∫ x, radialWeight weissProfile 0 s x * (V x * f (V x))) + C₀) s := by
    convert (hr.smoothWeissFunctional_hasDerivAt h hV hval hlim hs).add
      ((hasDerivAt_id s).const_mul C₀) using 1
    · ext y; rfl
    · simp
  have hdG_lower {s : ℝ} (hs : 0 < s) :
      4 * s ^ (-(m + 4 : ℤ)) *
          (∫ x, radialWeight weissBoundaryProfile 0 s x *
            (inner ℝ (gradient V x) x - V x) ^ 2) ≤ deriv G s := by
    rw [(hdG hs).deriv]
    linarith [(abs_le.mp (hreact_bound hs)).2]
  have hG_mono : MonotoneOn G (Ioi 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioi (0 : ℝ))
    · exact fun s hs ↦ (hdG hs).continuousAt.continuousWithinAt
    · exact fun s hs ↦ (hdG (interior_subset hs)).differentiableAt.differentiableWithinAt
    · intro s hs
      have hs0 : 0 < s := interior_subset hs
      apply le_trans _ (hdG_lower hs0)
      exact mul_nonneg (mul_nonneg (by norm_num) (zpow_nonneg hs0.le _))
        (integral_nonneg (fun x ↦ mul_nonneg (weissBoundaryProfile_nonneg _) (sq_nonneg _)))
  have hG_bdd : BddBelow (G '' Ioi 0) := by
    refine ⟨-6 * κ ^ 2 * volume.real B1, ?_⟩
    rintro _ ⟨s, hs : 0 < s, rfl⟩
    have hE0 : 0 ≤ smoothWeissEnergy f V s := by
      apply mul_nonneg (zpow_nonneg hs.le _)
      apply integral_nonneg
      intro x
      have hpe : 0 ≤ phaseEnergyDensity f 0 V x := by
        by_cases hx : 0 < V x
        · simp only [phaseEnergyDensity, indicator_of_mem (s := {y | 0 < V y}) hx, add_zero]
          exact add_nonneg (by positivity) (hr.normalizedPotential_nonneg h (hval x))
        · simp [phaseEnergyDensity, indicator_of_notMem (s := {y | 0 < V y}) hx]
      exact mul_nonneg (by linarith) (weissProfile_mem_Icc (by positivity)).1
    have hB_le : smoothWeissBoundary V s ≤ 6 * κ ^ 2 * volume.real B1 := by
      have hcut : smoothWeissBoundary V s =
          2 * ∫ y in B1, (V (s • y) / s) ^ 2 * weissBoundaryProfile (‖y‖ ^ 2) := by
        unfold smoothWeissBoundary
        congr 1
        symm
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro y hy
        have hny : 1 < ‖y‖ := by simpa only [B1, mem_closedBall, dist_zero_right, not_le] using hy
        simp [weissBoundaryProfile_zero (by nlinarith : 1 ≤ ‖y‖ ^ 2)]
      rw [hcut]
      have hi : IntegrableOn
          (fun y ↦ (V (s • y) / s) ^ 2 * weissBoundaryProfile (‖y‖ ^ 2)) B1 :=
        ((((lipschitzWith_rescale_div hV hs).continuous).pow 2).mul
          (weissBoundaryProfile_contDiff.continuous.comp
            (continuous_norm.pow 2))).continuousOn.integrableOn_compact hB1
      have hle : (∫ y in B1, (V (s • y) / s) ^ 2 * weissBoundaryProfile (‖y‖ ^ 2)) ≤
          ∫ _y in B1, 3 * κ ^ 2 := by
        apply setIntegral_mono_on hi (continuousOn_const.integrableOn_compact hB1) hB1.measurableSet
        intro y hy
        have hny : ‖y‖ ≤ 1 := by simpa only [B1, mem_closedBall, dist_zero_right] using hy
        have hvy : ‖V (s • y) / s‖ ≤ κ := by
          have hd := (lipschitzWith_rescale_div hV hs).dist_le_mul y 0
          simp only [smul_zero, hV0, zero_div, dist_zero_right] at hd
          exact hd.trans (mul_le_of_le_one_right h.kappa_pos.le hny)
        have hvy2 : (V (s • y) / s) ^ 2 ≤ κ ^ 2 := by
          rw [← sq_abs, ← Real.norm_eq_abs]
          exact pow_le_pow_left₀ (norm_nonneg _) hvy 2
        have hwb := (weissBoundaryProfile_mem_Icc (sq_nonneg ‖y‖)).2
        calc
          (V (s • y) / s) ^ 2 * weissBoundaryProfile (‖y‖ ^ 2) ≤ κ ^ 2 * 3 :=
            mul_le_mul hvy2 hwb (weissBoundaryProfile_nonneg _) (sq_nonneg κ)
          _ = 3 * κ ^ 2 := by ring
      rw [setIntegral_const, smul_eq_mul] at hle
      linarith
    dsimp only [G, smoothWeissFunctional]
    have hCs : 0 ≤ C₀ * s := mul_nonneg hC₀ hs.le
    linarith
  let Θ₀ : ℝ := sInf (G '' Ioi 0)
  have hG_lim : Tendsto G (𝓝[>] 0) (𝓝 Θ₀) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hne : (G '' Ioi 0).Nonempty := ⟨G 1, 1, zero_lt_one, rfl⟩
    obtain ⟨_, ⟨r_ε, hr_ε : 0 < r_ε, rfl⟩, hlt⟩ := Real.lt_sInf_add_pos hne hε
    filter_upwards [Ioo_mem_nhdsGT hr_ε] with s hs
    have hlo : Θ₀ ≤ G s := csInf_le hG_bdd ⟨s, hs.1, rfl⟩
    have hhi : G s ≤ G r_ε := hG_mono hs.1 hr_ε hs.2.le
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hlo)]
    linarith
  apply one_homogeneous_of_radial_defect_zero hW hW0 hW_zero
  intro R hR
  let K := closedBall (0 : Space (m + 1)) R
  have hK : IsCompact K := isCompact_closedBall _ _
  let v := fun j x ↦ V (r_seq j • x) / r_seq j
  have hv_lip (j : ℕ) : LipschitzWith ⟨κ, h.kappa_pos.le⟩ (v j) :=
    lipschitzWith_rescale_div hV (hr_pos j)
  have ht_a : Tendsto (fun j ↦ 2 * R * r_seq j) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨by simpa using hr_lim.const_mul (2 * R),
      Eventually.of_forall (fun j ↦ mul_pos (by positivity) (hr_pos j))⟩
  have ht_b : Tendsto (fun j ↦ 4 * R * r_seq j) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨by simpa using hr_lim.const_mul (4 * R),
      Eventually.of_forall (fun j ↦ mul_pos (by positivity) (hr_pos j))⟩
  have ht_diff : Tendsto (fun j ↦ G (4 * R * r_seq j) - G (2 * R * r_seq j)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, sub_self] using (hG_lim.comp ht_b).sub (hG_lim.comp ht_a)
  have ht_vj_def : Tendsto
      (fun j ↦ ∫ z in K, (inner ℝ (gradient (v j) z) z - v j z) ^ 2) atTop (𝓝 0) := by
    let cR : ℝ := 4 * (2 * R) * (4 * R) ^ (-(m + 4 : ℤ))
    have hcR : 0 < cR := mul_pos (by positivity) (zpow_pos (by positivity) _)
    have hmaj := ht_diff.const_mul cR⁻¹
    simp only [mul_zero] at hmaj
    apply squeeze_zero (fun _ ↦ integral_nonneg (fun _ ↦ sq_nonneg _)) _ hmaj
    intro j
    let aj := 2 * R * r_seq j
    let bj := 4 * R * r_seq j
    have haj : 0 < aj := mul_pos (by positivity) (hr_pos j)
    have hab : aj < bj := by dsimp [aj, bj]; nlinarith [hr_pos j]
    have hcontG : ContinuousOn G (Icc aj bj) :=
      fun s hs ↦ (hdG (haj.trans_le hs.1)).continuousAt.continuousWithinAt
    have hdiffG : ∀ s ∈ Ioo aj bj, HasDerivAt G (deriv G s) s :=
      fun s hs ↦ (hdG (haj.trans hs.1)).differentiableAt.hasDerivAt
    obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope G (deriv G) hab hcontG hdiffG
    have hξ0 : 0 < ξ := haj.trans hξ.1
    have hbj_sub : bj - aj = 2 * R * r_seq j := by dsimp [aj, bj]; ring
    have hmvt : (2 * R * r_seq j) * deriv G ξ = G bj - G aj := by
      rw [← hbj_sub, hslope, mul_div_cancel₀ _ (sub_pos.mpr hab).ne']
    have hlow_ξ := mul_le_mul_of_nonneg_left (hdG_lower hξ0)
      (mul_nonneg (show 0 ≤ 2 * R by positivity) (hr_pos j).le)
    rw [hmvt] at hlow_ξ
    let Fξ : Space (m + 1) → ℝ := fun x ↦
      radialWeight weissBoundaryProfile 0 ξ x * (inner ℝ (gradient V x) x - V x) ^ 2
    have hchg := Measure.integral_comp_smul volume Fξ (r_seq j)
    simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul] at hchg
    rw [abs_of_nonneg (inv_nonneg.mpr (pow_nonneg (hr_pos j).le (m + 1)))] at hchg
    have hFξ_int : (∫ x, Fξ x) = (r_seq j) ^ (m + 1) * ∫ z, Fξ (r_seq j • z) := by
      rw [hchg, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ (hr_pos j).ne'), one_mul]
    have hiFξ : Integrable (fun z ↦ Fξ (r_seq j • z)) := by
      have hzero_p : ∀ s : ℝ, 2 ≤ s → weissBoundaryProfile s = 0 :=
        fun _ hs ↦ weissBoundaryProfile_zero (by linarith)
      have hpr_cont : ContDiff ℝ 1 (radialWeight weissBoundaryProfile (0 : Space (m + 1)) ξ) :=
        contDiff_radialWeight weissBoundaryProfile_contDiff 0 ξ
      have hpr_comp : HasCompactSupport (radialWeight weissBoundaryProfile (0 : Space (m + 1)) ξ) :=
        (isCompact_closedBall 0 (2 * ξ)).of_isClosed_subset (isClosed_tsupport _)
          (tsupport_radialWeight_subset hzero_p 0 hξ0)
      have hc_z : HasCompactSupport (fun z ↦ radialWeight weissBoundaryProfile 0 ξ (r_seq j • z)) :=
        hasCompactSupport_comp_smul hpr_comp (hr_pos j)
      obtain ⟨Rz, hRz⟩ := hc_z.isBounded.subset_closedBall (0 : Space (m + 1))
      have hKz : IsCompact (closedBall (0 : Space (m + 1)) Rz) := isCompact_closedBall _ _
      have hVbound (x : Space (m + 1)) : ‖gradient V x‖ ≤ κ := by
        rw [gradient, LinearIsometryEquiv.norm_map]
        exact norm_fderiv_le_of_lipschitz ℝ hV
      have hiKz : IntegrableOn (fun z ↦ Fξ (r_seq j • z)) (closedBall 0 Rz) := by
        apply (continuousOn_const.integrableOn_compact hKz
          (f := fun _ ↦ 3 * (κ * (r_seq j * |Rz|) + 1) ^ 2)).mono'
          ((hpr_cont.continuous.comp (continuous_id.const_smul (r_seq j))).measurable.mul
            (((((measurable_gradient V).comp (continuous_id.const_smul (r_seq j)).measurable).inner
              (𝕜 := ℝ) (continuous_id.const_smul (r_seq j)).measurable).sub
              (hV.continuous.comp (continuous_id.const_smul (r_seq j))).measurable).pow_const
                2)).aestronglyMeasurable
        filter_upwards [ae_restrict_mem hKz.measurableSet] with z hz
        have hnz0 : ‖z‖ ≤ Rz := by simpa only [mem_closedBall, dist_zero_right] using hz
        have hnz : ‖z‖ ≤ |Rz| := hnz0.trans (le_abs_self Rz)
        have hwb := weissBoundaryProfile_mem_Icc
          (show 0 ≤ ‖r_seq j • z - 0‖ ^ 2 / ξ ^ 2 by positivity)
        simp only [Pi.mul_apply, Pi.sub_apply, Function.comp_apply, Pi.smul_apply, id_eq]
        dsimp only [radialWeight]
        rw [norm_mul, Real.norm_of_nonneg hwb.1, norm_pow]
        apply mul_le_mul hwb.2 (pow_le_pow_left₀ (norm_nonneg _) _ 2) (by positivity) (by norm_num)
        apply (norm_sub_le _ _).trans
        apply add_le_add
        · exact (norm_inner_le_norm (𝕜 := ℝ) _ _).trans
            (mul_le_mul (hVbound _) (by
              rw [norm_smul, Real.norm_of_nonneg (hr_pos j).le]
              exact mul_le_mul_of_nonneg_left hnz (hr_pos j).le) (norm_nonneg _) h.kappa_pos.le)
        · rw [Real.norm_of_nonneg (hval _).1]
          exact (hval _).2
      exact hiKz.integrable_of_forall_notMem_eq_zero (fun z hz ↦ by
        have hn : z ∉ tsupport (fun w ↦ radialWeight weissBoundaryProfile 0 ξ (r_seq j • w)) :=
          fun hh ↦ hz (hRz hh)
        simp [Fξ, image_eq_zero_of_notMem_tsupport hn])
    have hK_le : (r_seq j) ^ 2 * (∫ z in K, (inner ℝ (gradient (v j) z) z - v j z) ^ 2) ≤
        ∫ z, Fξ (r_seq j • z) := by
      have hi_lhs : IntegrableOn
          (fun z ↦ (r_seq j) ^ 2 * (inner ℝ (gradient (v j) z) z - v j z) ^ 2) K := by
        have hv_gb (z : Space (m + 1)) : ‖gradient (v j) z‖ ≤ κ := by
          rw [gradient, LinearIsometryEquiv.norm_map]
          exact norm_fderiv_le_of_lipschitz ℝ (hv_lip j)
        apply (continuousOn_const.integrableOn_compact hK
          (f := fun _ ↦ (r_seq j) ^ 2 * (2 * κ * R) ^ 2)).mono'
          (measurable_const.mul ((((measurable_gradient (v j)).inner (𝕜 := ℝ) measurable_id).sub
            (hv_lip j).continuous.measurable).pow_const 2)).aestronglyMeasurable
        filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
        have hnz : ‖z‖ ≤ R := by simpa only [K, mem_closedBall, dist_zero_right] using hz
        have hvz : ‖v j z‖ ≤ κ * R := by
          have hd := (hv_lip j).dist_le_mul z 0
          simp only [v, smul_zero, hV0, zero_div, dist_zero_right] at hd
          exact hd.trans (mul_le_mul_of_nonneg_left hnz h.kappa_pos.le)
        have hin : ‖inner ℝ (gradient (v j) z) z‖ ≤ κ * R :=
          (norm_inner_le_norm (𝕜 := ℝ) _ _).trans
            (mul_le_mul (hv_gb z) hnz (norm_nonneg _) h.kappa_pos.le)
        simp only [Pi.mul_apply, Pi.sub_apply, id_eq]
        rw [norm_mul, Real.norm_of_nonneg (sq_nonneg _), norm_pow]
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg _) ((norm_sub_le _ _).trans (by linarith)) 2)
          (sq_nonneg _)
      rw [← integral_const_mul]
      calc
        (∫ z in K, (r_seq j) ^ 2 * (inner ℝ (gradient (v j) z) z - v j z) ^ 2) ≤
            ∫ z in K, Fξ (r_seq j • z) := by
          apply setIntegral_mono_on hi_lhs hiFξ.integrableOn hK.measurableSet
          intro z hz
          have hnz : ‖z‖ ≤ R := by simpa only [K, mem_closedBall, dist_zero_right] using hz
          have hratio : ‖r_seq j • z - 0‖ ^ 2 / ξ ^ 2 ≤ 1 / 4 := by
            rw [sub_zero, norm_smul, Real.norm_of_nonneg (hr_pos j).le]
            apply (div_le_iff₀ (sq_pos_of_pos hξ0)).mpr
            have hξ_lo : 2 * R * r_seq j < ξ := hξ.1
            have h1 : (r_seq j * ‖z‖) ^ 2 ≤ (R * r_seq j) ^ 2 :=
              (sq_le_sq₀ (mul_nonneg (hr_pos j).le (norm_nonneg z))
                (mul_nonneg hR.le (hr_pos j).le)).mpr
                (by simpa only [mul_comm] using mul_le_mul_of_nonneg_left hnz (hr_pos j).le)
            have h2 : (2 * R * r_seq j) ^ 2 ≤ ξ ^ 2 := by nlinarith
            nlinarith
          have hwb := weissBoundaryProfile_lower hratio
          have hlin : inner ℝ (gradient V (r_seq j • z)) (r_seq j • z) - V (r_seq j • z) =
              r_seq j * (inner ℝ (gradient (v j) z) z - v j z) := by
            have hrj_ne : r_seq j ≠ 0 := (hr_pos j).ne'
            dsimp only [v]
            rw [gradient_rescale_div V hrj_ne z, real_inner_smul_right]
            field_simp [hrj_ne]
          have hsq_id : (inner ℝ (gradient V (r_seq j • z)) (r_seq j • z) - V (r_seq j • z)) ^ 2 =
              (r_seq j) ^ 2 * (inner ℝ (gradient (v j) z) z - v j z) ^ 2 := by
            rw [hlin, mul_pow]
          dsimp only [Fξ, radialWeight]
          rw [hsq_id]
          exact le_mul_of_one_le_left (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hwb
        _ ≤ ∫ z, Fξ (r_seq j • z) :=
          setIntegral_le_integral hiFξ
            (Eventually.of_forall (fun z ↦ mul_nonneg (weissBoundaryProfile_nonneg _) (sq_nonneg _)))
    have hpow_lo : cR ≤
        (2 * R * r_seq j) * (4 * ξ ^ (-(m + 4 : ℤ)) *
          ((r_seq j) ^ (m + 1) * (r_seq j) ^ 2)) := by
      have hξ_hi : ξ ≤ 4 * R * r_seq j := hξ.2.le
      have hξ_zpow : (4 * R * r_seq j) ^ (-(m + 4 : ℤ)) ≤ ξ ^ (-(m + 4 : ℤ)) := by
        rw [zpow_neg, zpow_neg, show (m + 4 : ℤ) = ((m + 4 : ℕ) : ℤ) by push_cast; rfl,
          zpow_natCast, zpow_natCast]
        exact inv_anti₀ (pow_pos hξ0 _) (pow_le_pow_left₀ hξ0.le hξ_hi _)
      have hprod_eq : (2 * R * r_seq j) *
          (4 * (4 * R * r_seq j) ^ (-(m + 4 : ℤ)) *
            ((r_seq j) ^ (m + 1) * (r_seq j) ^ 2)) = cR := by
        have hr_tot : r_seq j * ((r_seq j) ^ (m + 1) * (r_seq j) ^ 2) =
            (r_seq j) ^ (m + 4) := by ring
        rw [mul_zpow, zpow_neg, zpow_neg,
          show (m + 4 : ℤ) = ((m + 4 : ℕ) : ℤ) by push_cast; rfl, zpow_natCast, zpow_natCast]
        dsimp only [cR]
        rw [zpow_neg, show (m + 4 : ℤ) = ((m + 4 : ℕ) : ℤ) by push_cast; rfl, zpow_natCast]
        have hne : (r_seq j) ^ (m + 4) ≠ 0 := pow_ne_zero _ (hr_pos j).ne'
        calc
          2 * R * r_seq j * (4 * (((4 * R) ^ (m + 4))⁻¹ * ((r_seq j) ^ (m + 4))⁻¹) *
              ((r_seq j) ^ (m + 1) * (r_seq j) ^ 2)) =
            4 * (2 * R) * ((4 * R) ^ (m + 4))⁻¹ *
              ((r_seq j * ((r_seq j) ^ (m + 1) * (r_seq j) ^ 2)) *
                ((r_seq j) ^ (m + 4))⁻¹) := by ring
          _ = 4 * (2 * R) * ((4 * R) ^ (m + 4))⁻¹ := by
            rw [hr_tot, mul_inv_cancel₀ hne, mul_one]
      rw [← hprod_eq]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hξ_zpow (by norm_num))
          (mul_nonneg (pow_nonneg (hr_pos j).le _) (sq_nonneg _)))
        (mul_nonneg (by positivity) (hr_pos j).le)
    have hcomb : cR * (∫ z in K, (inner ℝ (gradient (v j) z) z - v j z) ^ 2) ≤ G bj - G aj := by
      calc
        cR * (∫ z in K, (inner ℝ (gradient (v j) z) z - v j z) ^ 2) ≤
          (2 * R * r_seq j) * (4 * ξ ^ (-(m + 4 : ℤ)) *
            ((r_seq j) ^ (m + 1) * ((r_seq j) ^ 2 *
              ∫ z in K, (inner ℝ (gradient (v j) z) z - v j z) ^ 2))) := by
          have hint_nn : 0 ≤ ∫ z in K, (inner ℝ (gradient (v j) z) z - v j z) ^ 2 :=
            integral_nonneg (fun _ ↦ sq_nonneg _)
          have hmul := mul_le_mul_of_nonneg_right hpow_lo hint_nn
          linarith
        _ ≤ (2 * R * r_seq j) * (4 * ξ ^ (-(m + 4 : ℤ)) *
            ((r_seq j) ^ (m + 1) * ∫ z, Fξ (r_seq j • z))) := by
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by positivity) (hr_pos j).le)
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) (zpow_nonneg hξ0.le _))
          exact mul_le_mul_of_nonneg_left hK_le (pow_nonneg (hr_pos j).le _)
        _ = (2 * R * r_seq j) * (4 * ξ ^ (-(m + 4 : ℤ)) * ∫ x, Fξ x) := by rw [← hFξ_int]
        _ ≤ G bj - G aj := hlow_ξ
    have hdiv := mul_le_mul_of_nonneg_left hcomb (inv_nonneg.mpr hcR.le)
    rwa [inv_mul_cancel_left₀ hcR.ne'] at hdiv
  have hgrad_sq := hr.microscopic_blowup_gradient_tendsto h hV hval hlim hr_pos hr_lim
    hW hW0 hWlim hK
  have ht_v_sq : Tendsto (fun j ↦ ∫ z in K, (v j z - W_lim z) ^ 2) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hvK0 : 0 ≤ volume.real K := measureReal_nonneg
    let δ : ℝ := Real.sqrt (ε / (volume.real K + 1))
    have hδ : 0 < δ := Real.sqrt_pos.mpr (div_pos hε (by linarith))
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp (hWlim K hK) δ hδ] with j hj
    have hi : IntegrableOn (fun z ↦ (v j z - W_lim z) ^ 2) K :=
      (((hv_lip j).continuous.sub hW.continuous).pow 2).continuousOn.integrableOn_compact hK
    have hle : (∫ z in K, (v j z - W_lim z) ^ 2) ≤ ∫ _z in K, δ ^ 2 := by
      apply setIntegral_mono_on hi (continuousOn_const.integrableOn_compact hK) hK.measurableSet
      intro z hz
      have hd := hj z hz
      rw [dist_comm, Real.dist_eq] at hd
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hd.le 2
    rw [setIntegral_const, smul_eq_mul, Real.sq_sqrt (div_nonneg hε.le (by linarith))] at hle
    have hnn : 0 ≤ ∫ z in K, (v j z - W_lim z) ^ 2 := integral_nonneg (fun _ ↦ sq_nonneg _)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
    have hpos_div : 0 < ε / (volume.real K + 1) := div_pos hε (by linarith)
    have hmul : (volume.real K + 1) * (ε / (volume.real K + 1)) = ε :=
      mul_div_cancel₀ ε (by linarith)
    nlinarith
  have ht_W_def : Tendsto
      (fun _ : ℕ ↦ ∫ z in K, (inner ℝ (gradient W_lim z) z - W_lim z) ^ 2) atTop (𝓝 0) := by
    have hmaj := ((ht_vj_def.const_mul 2).add
      ((hgrad_sq.const_mul (4 * R ^ 2)).add (ht_v_sq.const_mul 4)))
    simp only [mul_zero, add_zero] at hmaj
    apply squeeze_zero (fun _ ↦ integral_nonneg (fun _ ↦ sq_nonneg _)) _ hmaj
    intro j
    have hv_gb (z : Space (m + 1)) : ‖gradient (v j) z‖ ≤ κ := by
      rw [gradient, LinearIsometryEquiv.norm_map]
      exact norm_fderiv_le_of_lipschitz ℝ (hv_lip j)
    have hW_gb (z : Space (m + 1)) : ‖gradient W_lim z‖ ≤ κ := by
      rw [gradient, LinearIsometryEquiv.norm_map]
      exact norm_fderiv_le_of_lipschitz ℝ hW
    have hiW : IntegrableOn (fun z ↦ (inner ℝ (gradient W_lim z) z - W_lim z) ^ 2) K := by
      apply (continuousOn_const.integrableOn_compact hK (f := fun _ ↦ (2 * κ * R) ^ 2)).mono'
        ((((measurable_gradient W_lim).inner (𝕜 := ℝ) measurable_id).sub
          hW.continuous.measurable).pow_const 2).aestronglyMeasurable
      filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
      have hnz : ‖z‖ ≤ R := by simpa only [K, mem_closedBall, dist_zero_right] using hz
      have hWz : ‖W_lim z‖ ≤ κ * R := by
        have hd := hW.dist_le_mul z 0
        rw [hW_zero, dist_zero_right, dist_zero_right] at hd
        exact hd.trans (mul_le_mul_of_nonneg_left hnz h.kappa_pos.le)
      have hin : ‖inner ℝ (gradient W_lim z) z‖ ≤ κ * R :=
        (norm_inner_le_norm (𝕜 := ℝ) _ _).trans
          (mul_le_mul (hW_gb z) hnz (norm_nonneg _) h.kappa_pos.le)
      simp only [Pi.sub_apply, id_eq]
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) ((norm_sub_le _ _).trans (by linarith)) 2
    have hivj : IntegrableOn (fun z ↦ (inner ℝ (gradient (v j) z) z - v j z) ^ 2) K := by
      apply (continuousOn_const.integrableOn_compact hK (f := fun _ ↦ (2 * κ * R) ^ 2)).mono'
        ((((measurable_gradient (v j)).inner (𝕜 := ℝ) measurable_id).sub
          (hv_lip j).continuous.measurable).pow_const 2).aestronglyMeasurable
      filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
      have hnz : ‖z‖ ≤ R := by simpa only [K, mem_closedBall, dist_zero_right] using hz
      have hvz : ‖v j z‖ ≤ κ * R := by
        have hd := (hv_lip j).dist_le_mul z 0
        simp only [v, smul_zero, hV0, zero_div, dist_zero_right] at hd
        exact hd.trans (mul_le_mul_of_nonneg_left hnz h.kappa_pos.le)
      have hin : ‖inner ℝ (gradient (v j) z) z‖ ≤ κ * R :=
        (norm_inner_le_norm (𝕜 := ℝ) _ _).trans
          (mul_le_mul (hv_gb z) hnz (norm_nonneg _) h.kappa_pos.le)
      simp only [Pi.sub_apply, id_eq]
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) ((norm_sub_le _ _).trans (by linarith)) 2
    have hig : IntegrableOn (fun z ↦ ‖gradient (v j) z - gradient W_lim z‖ ^ 2) K :=
      integrableOn_gradient_sub_sq_of_lipschitz (hv_lip j) hW hK
    have hiv : IntegrableOn (fun z ↦ (v j z - W_lim z) ^ 2) K :=
      (((hv_lip j).continuous.sub hW.continuous).pow 2).continuousOn.integrableOn_compact hK
    have hsum_int : IntegrableOn
        (fun z ↦ 2 * (inner ℝ (gradient (v j) z) z - v j z) ^ 2 +
          (4 * R ^ 2 * ‖gradient (v j) z - gradient W_lim z‖ ^ 2 +
            4 * (v j z - W_lim z) ^ 2)) K :=
      Integrable.congr
        ((hivj.const_mul 2).add ((hig.const_mul (4 * R ^ 2)).add (hiv.const_mul 4)))
        (Eventually.of_forall (fun z ↦ by simp only [Pi.add_apply]))
    have hrhs_eq : 2 * (∫ z in K, (inner ℝ (gradient (v j) z) z - v j z) ^ 2) +
        (4 * R ^ 2 * (∫ z in K, ‖gradient (v j) z - gradient W_lim z‖ ^ 2) +
          4 * ∫ z in K, (v j z - W_lim z) ^ 2) =
        ∫ z in K, (2 * (inner ℝ (gradient (v j) z) z - v j z) ^ 2 +
          (4 * R ^ 2 * ‖gradient (v j) z - gradient W_lim z‖ ^ 2 +
            4 * (v j z - W_lim z) ^ 2)) := by
      have ha1 := integral_add (hivj.const_mul 2) ((hig.const_mul (4 * R ^ 2)).add (hiv.const_mul 4))
      have ha2 := integral_add (hig.const_mul (4 * R ^ 2)) (hiv.const_mul 4)
      simp only [Pi.add_apply] at ha1
      rw [← integral_const_mul, ← integral_const_mul, ← integral_const_mul, ← ha2, ← ha1]
    rw [hrhs_eq]
    apply setIntegral_mono_on hiW hsum_int hK.measurableSet
    intro z hz
    have hnz : ‖z‖ ≤ R := by simpa only [K, mem_closedBall, dist_zero_right] using hz
    let A := inner ℝ (gradient (v j) z) z - v j z
    let B := inner ℝ (gradient W_lim z - gradient (v j) z) z
    let C := v j z - W_lim z
    have hid : inner ℝ (gradient W_lim z) z - W_lim z = A + (B + C) := by
      dsimp only [A, B, C]
      rw [inner_sub_left]
      ring
    have hB_sq : B ^ 2 ≤ R ^ 2 * ‖gradient (v j) z - gradient W_lim z‖ ^ 2 := by
      dsimp only [B]
      rw [← sq_abs, ← Real.norm_eq_abs, norm_sub_rev (gradient (v j) z), mul_comm (R ^ 2),
        ← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _)
        ((norm_inner_le_norm (𝕜 := ℝ) _ _).trans
          (mul_le_mul_of_nonneg_left hnz (norm_nonneg _))) 2
    rw [hid]
    nlinarith [sq_nonneg (A - (B + C)), sq_nonneg (B - C), hB_sq]
  exact tendsto_nhds_unique tendsto_const_nhds ht_W_def

/-- Full microscopic blowup extraction packaging subconvergence, nondegeneracy, weak and truncated
harmonicity, strong `L²_loc` gradient convergence, and degree-one positive homogeneity (TB2–TB4,
TB6.2). -/
theorem RigidityHypotheses.exists_oneHomogeneous_microscopic_blowup_limit
    {m : ℕ} {g : Space m → ℝ} {u V : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {p_seq : ℕ → Space (m + 1)} {r_seq : ℕ → ℝ}
    (hlim : ∀ K : Set (Space (m + 1)), IsCompact K →
      TendstoUniformlyOn (fun j x ↦ zeroExtension g u (p_seq j + x)) V atTop K)
    (hV0 : V 0 = 0) (hcl : (0 : Space (m + 1)) ∈ closure {x | 0 < V x})
    (hr_pos : ∀ j, 0 < r_seq j) (hr_lim : Tendsto r_seq atTop (𝓝 0)) :
    ∃ (φ : ℕ → ℕ) (W_lim : Space (m + 1) → ℝ),
      StrictMono φ ∧
      LipschitzWith ⟨κ, h.kappa_pos.le⟩ W_lim ∧
      W_lim 0 = 0 ∧
      (∀ x, 0 ≤ W_lim x) ∧
      (∀ t : ℝ, 0 ≤ t → ∀ x, W_lim (t • x) = t * W_lim x) ∧
      (∀ K : Set (Space (m + 1)), IsCompact K →
        TendstoUniformlyOn (fun j x ↦ V (r_seq (φ j) • x) / r_seq (φ j)) W_lim atTop K) ∧
      (∃ x ∈ closedBall 0 1, 0 < W_lim x) ∧
      (∀ η : Space (m + 1) → ℝ, ContDiff ℝ 1 η → HasCompactSupport η →
        tsupport η ⊆ {x | 0 < W_lim x} →
        (∫ x, inner ℝ (gradient W_lim x) (gradient η x)) = 0) ∧
      (∀ η : Space (m + 1) → ℝ, ContDiff ℝ 1 η → HasCompactSupport η →
        (∫ x, η x * ‖gradient W_lim x‖ ^ 2 +
          W_lim x * inner ℝ (gradient W_lim x) (gradient η x)) = 0) ∧
      (∀ K : Set (Space (m + 1)), IsCompact K →
        Tendsto (fun j ↦ ∫ x in K,
          ‖gradient (fun y ↦ V (r_seq (φ j) • y) / r_seq (φ j)) x - gradient W_lim x‖ ^ 2)
          atTop (𝓝 0)) := by
  have hpointV (x : Space (m + 1)) :
      Tendsto (fun j ↦ zeroExtension g u (p_seq j + x)) atTop (𝓝 (V x)) :=
    (hlim {x} isCompact_singleton).tendsto_at (mem_singleton x)
  have hV : LipschitzWith ⟨κ, h.kappa_pos.le⟩ V := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    exact le_of_tendsto ((hpointV x).dist (hpointV y))
      (Eventually.of_forall (fun j ↦ by
        simpa only [dist_add_left] using
          (hr.zeroExtension_lipschitzWith h).dist_le_mul (p_seq j + x) (p_seq j + y)))
  have hval (x : Space (m + 1)) : V x ∈ Icc 0 1 :=
    ⟨ge_of_tendsto (hpointV x) (Eventually.of_forall (fun _ ↦ h.zeroExtension_nonneg _)),
      le_of_tendsto (hpointV x) (Eventually.of_forall (fun _ ↦ (hr.zeroExtension_lt_one _).le))⟩
  obtain ⟨φ, W_lim, hφ, hW, hW_zero, hW0, hWlim, hnondeg, hweak, htrunc, hgrad⟩ :=
    hr.exists_microscopic_blowup_limit h hlim hV0 hcl hr_pos hr_lim
  refine ⟨φ, W_lim, hφ, hW, hW_zero, hW0,
    hr.microscopic_blowup_one_homogeneous h hV hval hV0 hlim
      (fun j ↦ hr_pos (φ j)) (hr_lim.comp hφ.tendsto_atTop) hW hW0 hW_zero hWlim,
    hWlim, hnondeg, hweak, htrunc, hgrad⟩

end SerrinEpigraph
