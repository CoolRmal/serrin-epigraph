module

public import SerrinEpigraph.MollificationDerivative
public import SerrinEpigraph.MollificationSupport

/-!
# Calibration limits for smooth perturbations of the zero extension
-/

public section
noncomputable section

open MeasureTheory Filter Metric InnerProductSpace
open scoped Topology

namespace SerrinEpigraph

/-- Gradients of normalized averages respect addition of continuous functions. -/
theorem normalizedMollify_gradient_add {d : ℕ} {v φ : Space d → ℝ}
    (hv : Continuous v) (hφ : Continuous φ) (n : ℕ) (x : Space d) :
    gradient (normalizedMollify (fun y ↦ v y + φ y) n) x =
      gradient (normalizedMollify v n) x + gradient (normalizedMollify φ n) x := by
  rw [normalizedMollify_add hv hφ]
  simp only [gradient, fderiv_fun_add
    ((normalizedMollify_contDiff hv n).differentiable (by simp) x)
    ((normalizedMollify_contDiff hφ n).differentiable (by simp) x), map_add]

/-- Smooth functions have uniformly bounded averaged gradients on compact sets. -/
theorem normalizedMollify_gradient_bound_contDiff {d : ℕ} {v : Space d → ℝ}
    (hv : ContDiff ℝ 1 v) {K : Set (Space d)} (hK : IsCompact K) :
    ∃ C : NNReal, ∀ n x, x ∈ K → ‖gradient (normalizedMollify v n) x‖ ≤ C := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_ball (0 : Space d)
  obtain ⟨C, hC⟩ := hv.locallyLipschitz.locallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (isCompact_closedBall (0 : Space d) (R + 1))
  refine ⟨C, fun n x hx ↦ ?_⟩
  have hm := normalizedMollify_lipschitzOn_closedBall hv.continuous hC n
  have hd := norm_fderiv_le_of_lipschitzOn ℝ (closedBall_mem_nhds_of_mem (hR hx)) hm
  simpa only [gradient, LinearIsometryEquiv.norm_map] using hd

/-- A continuous function valued below one has a common compact level bound for its averages. -/
theorem normalizedMollify_level_bound_of_continuous {d : ℕ} {v : Space d → ℝ}
    (hv : Continuous v) (hval : ∀ x, v x ∈ Set.Ico (0 : ℝ) 1)
    {K : Set (Space d)} (hK : IsCompact K) :
    ∃ b < (1 : ℝ), ∀ n x, x ∈ K → normalizedMollify v n x ∈ Set.Icc (0 : ℝ) b := by
  obtain ⟨R, hR0, hR⟩ := hK.isBounded.subset_ball_lt 0 (0 : Space d)
  have hne : (closedBall (0 : Space d) (R + 1)).Nonempty :=
    ⟨0, by simp only [mem_closedBall, dist_self]; linarith⟩
  obtain ⟨z, hz, hmax⟩ := (isCompact_closedBall (0 : Space d) (R + 1)).exists_isMaxOn
    hne hv.continuousOn
  refine ⟨v z, (hval z).2, fun n x hx ↦ ?_⟩
  have h0 := mollify_nonneg (fun x ↦ (hval x).1) n x
  have hc := mollify_contraction_mem_Ioo n
  have hb : mollify v n x ≤ v z := by
    apply mollify_le_of_local hv
    intro t ht
    apply hmax
    have hxR : ‖x‖ ≤ R := (by simpa only [mem_ball, dist_zero_right] using hR hx : ‖x‖ < R).le
    have ht1 : ‖t‖ ≤ 1 :=
      (by simpa only [mem_ball, dist_zero_right] using ht :
        ‖t‖ < (averagingBump d n).rOut).le.trans (averagingBump_rOut_le_one _ _)
    simp only [mem_closedBall, dist_zero_right]
    exact (norm_sub_le x t).trans (add_le_add hxR ht1)
  exact ⟨mul_nonneg hc.1.le h0, (mul_le_of_le_one_left h0 hc.2.le).trans hb⟩

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ : ℝ}

/-- Averaged gradients converge almost everywhere for smooth perturbations of the zero extension. -/
theorem Hypotheses.perturbed_normalizedMollify_gradient_tendsto_ae
    (h : Hypotheses g u f κ) {φ : Space (m + 1) → ℝ} (hφ : ContDiff ℝ 1 φ) :
    ∀ᵐ x, Tendsto (fun n ↦
      gradient (normalizedMollify (fun y ↦ zeroExtension g u y + φ y) n) x) atTop
      (𝓝 (gradient (fun y ↦ zeroExtension g u y + φ y) x)) := by
  filter_upwards [h.normalizedMollify_gradient_tendsto_ae,
    h.zeroExtension_ae_differentiableAt] with x hx hd
  have hφt := normalizedMollify_gradient_tendsto_on_open isOpen_univ hφ.contDiffOn (Set.mem_univ x)
  have ht := hx.add hφt
  have hg := gradient_affine_variation hd (hφ.differentiable_one x) 1
  simp only [one_mul, one_smul] at hg
  rw [hg]
  simp_rw [normalizedMollify_gradient_add h.zeroExtension_continuous hφ.continuous]
  exact ht

/-- Smooth compact perturbations have uniformly bounded averaged gradients locally. -/
theorem Hypotheses.perturbed_normalizedMollify_gradient_bound
    (h : Hypotheses g u f κ) {φ : Space (m + 1) → ℝ} (hφ : ContDiff ℝ 1 φ)
    {K : Set (Space (m + 1))} (hK : IsCompact K) :
    ∃ C : NNReal, ∀ n x, x ∈ K →
      ‖gradient (normalizedMollify (fun y ↦ zeroExtension g u y + φ y) n) x‖ ≤ C := by
  obtain ⟨C₀, hC₀⟩ := h.normalizedMollify_gradient_bound hK
  obtain ⟨C₁, hC₁⟩ := normalizedMollify_gradient_bound_contDiff hφ hK
  refine ⟨C₀ + C₁, fun n x hx ↦ ?_⟩
  rw [normalizedMollify_gradient_add h.zeroExtension_continuous hφ.continuous]
  exact (norm_add_le _ _).trans (add_le_add (hC₀ n x hx) (hC₁ n x hx))

/-- The calibration integral of a perturbed zero extension is the limit of its smooth approximations. -/
theorem RigidityHypotheses.perturbed_calibration_tendsto
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {φ : Space (m + 1) → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hval : ∀ x, zeroExtension g u x + φ x ∈ Set.Ico (0 : ℝ) 1)
    {K : Set (Space (m + 1))} (hK : IsCompact K) :
    Tendsto (fun n ↦ ∫ x in K, hr.boundaryCalibratedDensity h (horizontal x)
      (normalizedMollify (fun y ↦ zeroExtension g u y + φ y) n x)
      (gradient (normalizedMollify (fun y ↦ zeroExtension g u y + φ y) n) x)) atTop
      (𝓝 (∫ x in K, hr.boundaryCalibratedDensity h (horizontal x)
        (zeroExtension g u x + φ x) (gradient (fun y ↦ zeroExtension g u y + φ y) x))) := by
  have hv := h.zeroExtension_continuous.add hφ.continuous
  obtain ⟨b, hb, hval'⟩ := normalizedMollify_level_bound_of_continuous hv hval hK
  obtain ⟨C, hC⟩ := h.perturbed_normalizedMollify_gradient_bound hφ hK
  apply hr.tendsto_integral_boundaryCalibration h hK hb
    (fun n ↦ (normalizedMollify_contDiff hv n).continuous.continuousOn)
    (fun n ↦ ((toDual ℝ (Space (m + 1))).symm.continuous.comp
      ((normalizedMollify_contDiff hv n).continuous_fderiv (by simp))).continuousOn)
    hval' hC
  · exact Eventually.of_forall (normalizedMollify_tendsto hv)
  · exact ae_restrict_of_ae (h.perturbed_normalizedMollify_gradient_tendsto_ae hφ)

/-- Compact smooth perturbations preserve the zero extension's calibration integral across the
free boundary, on a fixed ball containing the perturbation. -/
theorem RigidityHypotheses.perturbed_calibration_eq_energy
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {φ : Space (m + 1) → ℝ} (hφ : ContDiff ℝ 1 φ) (hsupp : HasCompactSupport φ)
    (hval : ∀ x, zeroExtension g u x + φ x ∈ Set.Ico (0 : ℝ) 1) :
    ∃ R : ℝ, tsupport φ ⊆ closedBall 0 R ∧
      (∫ x in closedBall 0 R, hr.boundaryCalibratedDensity h (horizontal x)
        (zeroExtension g u x + φ x) (gradient (fun y ↦ zeroExtension g u y + φ y) x)) =
      ∫ x in closedBall 0 R,
        phaseEnergyDensity f (κ ^ 2 / 2 - normalizedPotential f 0) (zeroExtension g u) x := by
  obtain ⟨R₁, hR₁⟩ := normalizedMollify_uniform_support hsupp
  obtain ⟨R₀, hR₀⟩ := hsupp.isBounded.subset_closedBall (0 : Space (m + 1))
  let R := max R₀ R₁
  have hsub : tsupport φ ⊆ closedBall 0 R :=
    hR₀.trans (closedBall_subset_closedBall (le_max_left _ _))
  have hsubn (n) : tsupport (normalizedMollify φ n) ⊆ closedBall 0 R :=
    (hR₁ n).trans (closedBall_subset_closedBall (le_max_right _ _))
  have hR (n) :
      (∫ x in closedBall 0 R, hr.boundaryCalibratedDensity h (horizontal x)
        (normalizedMollify (fun y ↦ zeroExtension g u y + φ y) n x)
        (gradient (normalizedMollify (fun y ↦ zeroExtension g u y + φ y) n) x)) =
      ∫ x in closedBall 0 R, hr.boundaryCalibratedDensity h (horizontal x)
        (normalizedMollify (zeroExtension g u) n x)
        (gradient (normalizedMollify (zeroExtension g u) n) x) := by
    have hV : ContDiff ℝ 1 (normalizedMollify (zeroExtension g u) n) :=
      (normalizedMollify_contDiff h.zeroExtension_continuous n).of_le (by simp)
    have hΦ : ContDiff ℝ 1 (normalizedMollify φ n) :=
      (normalizedMollify_contDiff hφ.continuous n).of_le (by simp)
    have he := hr.boundaryCalibratedPath_endpoints h hV hΦ (isCompact_closedBall 0 R) (hsubn n)
      (normalizedMollify_mem_Ico h.zeroExtension_continuous
        (fun x ↦ ⟨h.zeroExtension_nonneg x, (hr.zeroExtension_lt_one x).le⟩) n)
      (fun x ↦ by
        rw [← congrFun (normalizedMollify_add h.zeroExtension_continuous hφ.continuous n) x]
        exact normalizedMollify_mem_Ico (h.zeroExtension_continuous.add hφ.continuous)
          (fun x ↦ ⟨(hval x).1, (hval x).2.le⟩) n x)
    simpa only [normalizedMollify_add h.zeroExtension_continuous hφ.continuous n] using he
  refine ⟨R, hsub, ?_⟩
  have ht := hr.perturbed_calibration_tendsto h hφ hval (isCompact_closedBall 0 R)
  have he := ht.congr' (Eventually.of_forall hR)
  exact tendsto_nhds_unique he (hr.normalizedMollify_calibration_tendsto_energy h
    (isCompact_closedBall 0 R))

end SerrinEpigraph
