module

public import SerrinEpigraph.LipschitzMollificationDerivative
public import SerrinEpigraph.PlaneTiltIntegral
public import SerrinEpigraph.CauchyEnergy
public import SerrinEpigraph.DiffuseTiltEstimate
public import SerrinEpigraph.PhysicalTranslationCompactness
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# One-dimensionality of zero-tangential-energy limits

The conclusions below concern genuine Euclidean derivatives and Lebesgue measure.
Almost-everywhere directional information is converted to pointwise translation
invariance by smooth averaging, so exceptional affine lines cause no difficulty.
-/

public section
noncomputable section

open Set Metric MeasureTheory Filter InnerProductSpace ContinuousLinearMap
open scoped Topology Convolution

namespace SerrinEpigraph

/-- An almost-everywhere vanishing directional derivative vanishes everywhere
after smooth averaging. -/
theorem mollify_fderiv_apply_eq_zero_of_ae {d : ℕ} {v : Space d → ℝ} {C : NNReal}
    (hv : LipschitzWith C v) {ξ : Space d}
    (hξ : ∀ᵐ x, fderiv ℝ v x ξ = 0) (n : ℕ) (x : Space d) :
    fderiv ℝ (mollify v n) x ξ = 0 := by
  rw [(mollify_hasFDerivAt_of_lipschitz hv n x).fderiv]
  have hi := ((averagingBump d n).hasCompactSupport_normed (μ := volume)).convolutionExists_left
    (lsmul ℝ ℝ) (averagingBump d n).continuous_normed
    (locallyIntegrable_fderiv_of_lipschitz hv) x
  have hi' : Integrable
      (fun t ↦ (averagingBump d n).normed volume t • fderiv ℝ v (x - t)) :=
    hi.integrable
  change (∫ t, (averagingBump d n).normed volume t • fderiv ℝ v (x - t)) ξ = 0
  rw [ContinuousLinearMap.integral_apply hi']
  have ha := (volume.measurePreserving_sub_left x).quasiMeasurePreserving.ae hξ
  apply integral_eq_zero_of_ae
  filter_upwards [ha] with t ht
  simp only [smul_apply, ht, smul_zero, Pi.zero_apply]

/-- A globally Lipschitz function is invariant under any direction in which its
derivative vanishes almost everywhere. No exceptional line is discarded. -/
theorem add_eq_of_ae_fderiv_apply_eq_zero {d : ℕ} {v : Space d → ℝ} {C : NNReal}
    (hv : LipschitzWith C v) {ξ : Space d}
    (hξ : ∀ᵐ x, fderiv ℝ v x ξ = 0) (x : Space d) :
    v (x + ξ) = v x := by
  have he (n : ℕ) : mollify v n (x + ξ) = mollify v n x := by
    have hd (t : ℝ) :
        HasDerivAt (fun s : ℝ ↦ mollify v n (x + s • ξ)) 0 t := by
      have hh := ((mollify_contDiff hv.continuous n).differentiable (by simp)
        (x + t • ξ)).hasFDerivAt.comp_hasDerivAt t
          ((hasDerivAt_id t).smul_const ξ |>.const_add x)
      convert hh using 1
      · rfl
      · simpa only [one_smul] using (mollify_fderiv_apply_eq_zero_of_ae hv hξ n
          (x + t • ξ)).symm
    have hh := is_const_of_deriv_eq_zero (fun t ↦ (hd t).differentiableAt)
      (fun t ↦ (hd t).deriv) (1 : ℝ) 0
    simpa only [one_smul, zero_smul, add_zero] using hh
  exact tendsto_nhds_unique (mollify_tendsto hv.continuous (x + ξ))
    ((mollify_tendsto hv.continuous x).congr (fun n ↦ (he n).symm))

/-- Vanishing tangential derivatives force dependence on the single normal
coordinate, with the profile given by restriction to the normal line. -/
theorem eq_normal_profile_of_ae_tangential_fderiv_eq_zero
    {d : ℕ} {v : Space d → ℝ} {C : NNReal} (hv : LipschitzWith C v)
    {e : Space d} (he : ‖e‖ = 1)
    (ht : ∀ ξ : Space d, inner ℝ e ξ = 0 → ∀ᵐ x, fderiv ℝ v x ξ = 0)
    (x : Space d) :
    v x = v ((inner ℝ e x) • e) := by
  have hz : inner ℝ e (x - (inner ℝ e x) • e) = 0 := by
    simp [inner_sub_right, inner_smul_right, he]
  have hh := add_eq_of_ae_fderiv_apply_eq_zero hv
    (ht (x - (inner ℝ e x) • e) hz) ((inner ℝ e x) • e)
  simpa only [add_sub_cancel] using hh

/-- Directional derivatives of a globally Lipschitz function are locally integrable. -/
theorem locallyIntegrable_fderiv_apply_of_lipschitz
    {d : ℕ} {v : Space d → ℝ} {C : NNReal} (hv : LipschitzWith C v) (ξ : Space d) :
    LocallyIntegrable (fun x ↦ fderiv ℝ v x ξ) volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  exact (ContinuousLinearMap.apply ℝ ℝ ξ).integrable_comp
    ((locallyIntegrable_fderiv_of_lipschitz hv).integrableOn_isCompact hK)

/-- Weak vanishing against every smooth compact test identifies the actual
almost-everywhere directional derivative. -/
theorem ae_fderiv_apply_eq_zero_of_weak_directional_eq_zero
    {d : ℕ} {v : Space d → ℝ} {C : NNReal} (hv : LipschitzWith C v)
    {B : ℝ} (hval : ∀ x, v x ∈ Icc 0 B) (ξ : Space d)
    (hw : ∀ ψ : Space d → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      (∫ x in tsupport ψ, v x * fderiv ℝ ψ x ξ) = 0) :
    ∀ᵐ x, fderiv ℝ v x ξ = 0 := by
  apply ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (locallyIntegrable_fderiv_apply_of_lipschitz hv ξ)
  intro ψ hψ hc
  have hi := setIntegral_inner_gradient_mul_eq_neg_of_locallyLipschitz
    hv.locallyLipschitz hval (hψ.of_le (by simp)) hc hc (Subset.refl _) ξ
  rw [hw ψ hψ hc, neg_zero] at hi
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun x hx ↦ by simp [image_eq_zero_of_notMem_tsupport hx])] at hi
  simpa only [smul_eq_mul, inner_gradient_left, mul_comm] using hi

/-- The square of each directional derivative is integrable on compact sets. -/
theorem integrableOn_fderiv_apply_sq_of_lipschitz
    {d : ℕ} {v : Space d → ℝ} {C : NNReal} (hv : LipschitzWith C v)
    (ξ : Space d) {K : Set (Space d)} (hK : IsCompact K) :
    IntegrableOn (fun x ↦ fderiv ℝ v x ξ ^ 2) K := by
  have hi : IntegrableOn (fun _ : Space d ↦ ((C : ℝ) * ‖ξ‖) ^ 2) K :=
    continuousOn_const.integrableOn_compact hK
  apply hi.mono'
    (((measurable_fderiv ℝ v).apply_continuousLinearMap ξ).pow_const 2).aestronglyMeasurable
  filter_upwards with x
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have hb : |fderiv ℝ v x ξ| ≤ C * ‖ξ‖ :=
    (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hv) (norm_nonneg ξ))
  simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr hb

/-- Vanishing directional Dirichlet energy makes every compact directional
gradient flux tend to zero. -/
theorem integral_cutoff_fderiv_tendsto_zero_of_square_tendsto_zero
    {d : ℕ} {v : ℕ → Space d → ℝ} {C : ℕ → NNReal}
    (hv : ∀ j, LipschitzWith (C j) (v j)) (ξ : Space d)
    {K : Set (Space d)} (hK : IsCompact K) {ψ : Space d → ℝ} (hψ : Continuous ψ)
    (ht : Tendsto (fun j ↦ ∫ x in K, fderiv ℝ (v j) x ξ ^ 2) atTop (𝓝 0)) :
    Tendsto (fun j ↦ ∫ x in K, fderiv ℝ (v j) x ξ * ψ x) atTop (𝓝 0) := by
  have hb : IntegrableOn (fun x ↦ ψ x ^ 2) K :=
    (hψ.pow 2).continuousOn.integrableOn_compact hK
  have hbound := (Real.continuous_sqrt.tendsto 0 |>.comp ht).mul_const
    (Real.sqrt (∫ x in K, ψ x ^ 2))
  simp only [Real.sqrt_zero, zero_mul] at hbound
  apply squeeze_zero_norm (fun j ↦ ?_) hbound
  exact abs_integral_mul_le_sqrt
    (integrableOn_fderiv_apply_sq_of_lipschitz (hv j) ξ hK) hb

/-- Local integral convergence and vanishing directional energy force translation
invariance of the limiting Lipschitz function. -/
theorem add_eq_of_local_limit_and_directional_energy_tendsto_zero
    {d : ℕ} {v : ℕ → Space d → ℝ} {p : Space d → ℝ}
    {C : ℕ → NNReal} (hv : ∀ j, LipschitzWith (C j) (v j))
    {D : NNReal} (hp : LipschitzWith D p)
    {B : ℕ → ℝ} (hval : ∀ j x, v j x ∈ Icc 0 (B j))
    {B₀ : ℝ} (hpval : ∀ x, p x ∈ Icc 0 B₀) (ξ : Space d)
    (hlocal : ∀ K, IsCompact K →
      Tendsto (fun j ↦ ∫ x in K, ‖v j x - p x‖) atTop (𝓝 0))
    (ht : ∀ K, IsCompact K →
      Tendsto (fun j ↦ ∫ x in K, fderiv ℝ (v j) x ξ ^ 2) atTop (𝓝 0))
    (x : Space d) :
    p (x + ξ) = p x := by
  apply add_eq_of_ae_fderiv_apply_eq_zero hp
  apply ae_fderiv_apply_eq_zero_of_weak_directional_eq_zero hp hpval ξ
  intro ψ hψ hc
  have hflux := integral_cutoff_gradient_tendsto_of_integral_norm_sub_tendsto
    (fun j ↦ (hv j).locallyLipschitz) hval (hψ.of_le (by simp)) hc hc
    (Subset.refl _) (hp.continuous.continuousOn.integrableOn_compact hc) ξ
    (hlocal _ hc)
  simp only [inner_gradient_left] at hflux
  have hzero := integral_cutoff_fderiv_tendsto_zero_of_square_tendsto_zero hv ξ hc
    hψ.continuous (ht _ hc)
  have he := tendsto_nhds_unique hflux hzero
  exact neg_eq_zero.mp he

/-- Every tangential component is controlled by the full tangential Dirichlet density. -/
theorem inner_sq_le_tangential_norm_sq {d : ℕ} (q : Space d) {e ξ : Space d}
    (he : ‖e‖ = 1) (hξ : inner ℝ e ξ = 0) :
    inner ℝ q ξ ^ 2 ≤ (‖q‖ ^ 2 - inner ℝ q e ^ 2) * ‖ξ‖ ^ 2 := by
  let z := q - inner ℝ q e • e
  have hz : ‖z‖ ^ 2 = ‖q‖ ^ 2 - inner ℝ q e ^ 2 := by
    dsimp only [z]
    rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      inner_smul_right, he]
    ring
  have hi : inner ℝ z ξ = inner ℝ q ξ := by
    simp [z, inner_sub_left, real_inner_smul_left, hξ]
  have hb := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (norm_nonneg z)
    (norm_nonneg ξ))).mpr (abs_real_inner_le_norm z ξ)
  simpa only [sq_abs, mul_pow, hz, hi] using hb

/-- A locally convergent Lipschitz family whose full tangential energy vanishes
has a one-dimensional limit. -/
theorem eq_normal_profile_of_local_limit_and_tilt_tendsto_zero
    {d : ℕ} {v : ℕ → Space d → ℝ} {p : Space d → ℝ}
    {C : ℕ → NNReal} (hv : ∀ j, LipschitzWith (C j) (v j))
    {D : NNReal} (hp : LipschitzWith D p)
    {B : ℕ → ℝ} (hval : ∀ j x, v j x ∈ Icc 0 (B j))
    {B₀ : ℝ} (hpval : ∀ x, p x ∈ Icc 0 B₀)
    {e : Space d} (he : ‖e‖ = 1)
    (hlocal : ∀ K, IsCompact K →
      Tendsto (fun j ↦ ∫ x in K, ‖v j x - p x‖) atTop (𝓝 0))
    (ht : ∀ K, IsCompact K →
      Tendsto (fun j ↦ ∫ x in K, diffuseTiltDensity 1 (v j) e x) atTop (𝓝 0))
    (x : Space d) :
    p x = p ((inner ℝ e x) • e) := by
  let ξ := x - inner ℝ e x • e
  have hξ : inner ℝ e ξ = 0 := by
    simp [ξ, inner_sub_right, inner_smul_right, he]
  have hsq (K : Set (Space d)) (hK : IsCompact K) :
      Tendsto (fun j ↦ ∫ z in K, fderiv ℝ (v j) z ξ ^ 2) atTop (𝓝 0) := by
    have hbound := (ht K hK).mul_const (‖ξ‖ ^ 2)
    simp only [zero_mul] at hbound
    apply squeeze_zero (fun j ↦ integral_nonneg (fun z ↦ sq_nonneg _)) _ hbound
    intro j
    have hi := integrableOn_diffuseTiltDensity (hv j).locallyLipschitz hK 1 he
    calc
      _ ≤ ∫ z in K, diffuseTiltDensity 1 (v j) e z * ‖ξ‖ ^ 2 := by
        apply integral_mono (integrableOn_fderiv_apply_sq_of_lipschitz (hv j) ξ hK)
          (hi.mul_const _)
        intro z
        simpa only [diffuseTiltDensity, div_one, inner_gradient_left] using
          inner_sq_le_tangential_norm_sq (gradient (v j) z) he hξ
      _ = _ := integral_mul_const _ _
  have hh := add_eq_of_local_limit_and_directional_energy_tendsto_zero
    hv hp hval hpval ξ hlocal hsq ((inner ℝ e x) • e)
  simpa only [ξ, add_sub_cancel] using hh

/-- Pointwise convergence of continuous functions in the unit interval gives
local integral convergence on every compact set. -/
theorem integral_norm_sub_tendsto_zero_of_unit_interval_pointwise
    {d : ℕ} {v : ℕ → Space d → ℝ} {p : Space d → ℝ}
    (hv : ∀ j, Continuous (v j)) (hp : Continuous p)
    (hval : ∀ j x, v j x ∈ Icc 0 1) (hpval : ∀ x, p x ∈ Icc 0 1)
    (ht : ∀ x, Tendsto (fun j ↦ v j x) atTop (𝓝 (p x)))
    {K : Set (Space d)} (hK : IsCompact K) :
    Tendsto (fun j ↦ ∫ x in K, ‖v j x - p x‖) atTop (𝓝 0) := by
  have hh : Tendsto (fun j ↦ ∫ x in K, ‖v j x - p x‖) atTop
      (𝓝 (∫ x in K, ‖p x - p x‖)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ ↦ (1 : ℝ))
    · intro j
      exact ((hv j).sub hp).norm.aestronglyMeasurable
    · exact continuousOn_const.integrableOn_compact hK
    · intro j
      filter_upwards with x
      rw [norm_norm, Real.norm_eq_abs, abs_le]
      constructor <;> linarith [(hval j x).1, (hval j x).2, (hpval x).1, (hpval x).2]
    · filter_upwards with x
      exact ((ht x).sub tendsto_const_nhds).norm
  simpa only [sub_self, norm_zero, integral_zero] using hh

/-- Physical translates whose tangential energy vanishes have a subsequential
one-dimensional limit, retaining the actual sharp Lipschitz bound and all orders. -/
theorem RigidityHypotheses.exists_oneDimensional_physical_translation_limit
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (c : ℕ → Space (m + 1)) {e : Space (m + 1)} (he : ‖e‖ = 1)
    (ht : ∀ K : Set (Space (m + 1)), IsCompact K →
      Tendsto (fun j ↦ ∫ x in K,
        diffuseTiltDensity 1 (fun y ↦ zeroExtension g u (c j + y)) e x) atTop (𝓝 0)) :
    ∃ (φ : ℕ → ℕ) (V : Space (m + 1) → ℝ), StrictMono φ ∧
      LipschitzWith ⟨κ, h.kappa_pos.le⟩ V ∧ (∀ x, V x ∈ Icc 0 1) ∧
      (∀ K : Set (Space (m + 1)), IsCompact K →
        TendstoUniformlyOn (fun j x ↦ zeroExtension g u (c (φ j) + x)) V atTop K) ∧
      translationOrderSet (zeroExtension g u) ⊆ translationOrderSet V ∧
      ∀ x, V x = V ((inner ℝ e x) • e) := by
  obtain ⟨φ, V, hφ, hV, hVval, hlim, horder⟩ := hr.exists_physical_translation_limit h c
  refine ⟨φ, V, hφ, hV, hVval, hlim, horder, ?_⟩
  have hv (j : ℕ) : LipschitzWith ⟨κ, h.kappa_pos.le⟩
      (fun x ↦ zeroExtension g u (c (φ j) + x)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_add_left] using (hr.zeroExtension_lipschitzWith h).dist_le_mul
      (c (φ j) + x) (c (φ j) + y)
  have hval (j : ℕ) (x : Space (m + 1)) :
      zeroExtension g u (c (φ j) + x) ∈ Icc 0 1 :=
    ⟨h.zeroExtension_nonneg _, (hr.zeroExtension_lt_one _).le⟩
  apply eq_normal_profile_of_local_limit_and_tilt_tendsto_zero hv hV hval hVval he
  · intro K hK
    apply integral_norm_sub_tendsto_zero_of_unit_interval_pointwise
      (fun j ↦ (hv j).continuous) hV.continuous hval hVval _ hK
    intro x
    exact (hlim {x} isCompact_singleton).tendsto_at (mem_singleton x)
  · intro K hK
    exact (ht K hK).comp hφ.tendsto_atTop

end SerrinEpigraph
