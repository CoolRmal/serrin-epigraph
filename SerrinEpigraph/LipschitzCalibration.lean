module

public import SerrinEpigraph.LipschitzMollificationDerivative
public import SerrinEpigraph.UnshiftedMinimality

/-!
# Calibration limits for locally Lipschitz competitors
-/

public section
noncomputable section

open MeasureTheory Filter Metric InnerProductSpace
open scoped Topology

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ : ℝ}

/-- Normalized averaging recovers the calibration integral of any locally Lipschitz
competitor valued below one. -/
theorem RigidityHypotheses.lipschitz_calibration_tendsto
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {v : Space (m + 1) → ℝ} (hv : LocallyLipschitz v)
    (hval : ∀ x, v x ∈ Set.Ico (0 : ℝ) 1)
    {K : Set (Space (m + 1))} (hK : IsCompact K) :
    Tendsto (fun n ↦ ∫ x in K, hr.boundaryCalibratedDensity h (horizontal x)
      (normalizedMollify v n x) (gradient (normalizedMollify v n) x)) atTop
      (𝓝 (∫ x in K, hr.boundaryCalibratedDensity h (horizontal x) (v x) (gradient v x))) := by
  obtain ⟨b, hb, hval'⟩ := normalizedMollify_level_bound_of_continuous hv.continuous hval hK
  obtain ⟨C, hC⟩ := normalizedMollify_gradient_bound_of_locallyLipschitz hv hK
  apply hr.tendsto_integral_boundaryCalibration h hK hb
    (fun n ↦ (normalizedMollify_contDiff hv.continuous n).continuous.continuousOn)
    (fun n ↦ ((toDual ℝ (Space (m + 1))).symm.continuous.comp
      ((normalizedMollify_contDiff hv.continuous n).continuous_fderiv (by simp))).continuousOn)
    hval' hC
  · exact Eventually.of_forall (normalizedMollify_tendsto hv.continuous)
  · exact ae_restrict_of_ae (normalizedMollify_gradient_tendsto_ae_of_locallyLipschitz hv)

/-- Compact locally Lipschitz perturbations preserve the zero extension's calibration integral across the
free boundary, on a fixed ball containing the perturbation. -/
theorem RigidityHypotheses.lipschitz_perturbed_calibration_eq_energy
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {φ : Space (m + 1) → ℝ} (hφ : LocallyLipschitz φ) (hsupp : HasCompactSupport φ)
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
  have ht := hr.lipschitz_calibration_tendsto h (h.zeroExtension_locallyLipschitz.add hφ) hval (isCompact_closedBall 0 R)
  have he := ht.congr' (Eventually.of_forall hR)
  exact tendsto_nhds_unique he (hr.normalizedMollify_calibration_tendsto_energy h
    (isCompact_closedBall 0 R))

/-- Locally Lipschitz competitors have integrable calibration density on compact sets. -/
theorem RigidityHypotheses.integrableOn_lipschitz_calibration
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {v : Space (m + 1) → ℝ} (hv : LocallyLipschitz v)
    (hval : ∀ x, v x ∈ Set.Ico (0 : ℝ) 1)
    {K : Set (Space (m + 1))} (hK : IsCompact K) :
    IntegrableOn (fun x ↦ hr.boundaryCalibratedDensity h (horizontal x)
      (v x) (gradient v x)) K := by
  let B := fun x ↦ hr.closedLevelGradient h (horizontal x, v x)
  have hB : Continuous B := (hr.closedLevelGradient_continuousOn h).comp_continuous
    (continuous_horizontal.prodMk hv.continuous) hval
  obtain ⟨C, hC⟩ := gradient_bound_of_locallyLipschitz hv hK
  have hiC : IntegrableOn (fun _ : Space (m + 1) ↦ (C : ℝ)) K :=
    continuousOn_const.integrableOn_compact hK
  have hG : IntegrableOn (gradient v) K := by
    apply hiC.mono' (measurable_gradient v).aestronglyMeasurable
    filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
    exact hC x hx
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hB.continuousOn
  have hi : IntegrableOn (fun x ↦ inner ℝ (B x) (gradient v x)) K := by
    apply (hG.norm.const_mul M).mono'
      (hB.measurable.inner (measurable_gradient v)).aestronglyMeasurable
    filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
    exact (norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (hM x hx) (norm_nonneg _))
  have hW : Continuous (fun x ↦ normalizedPotential f (v x)) :=
    h.normalizedPotential_continuousOn.comp_continuous hv.continuous
      (fun x ↦ ⟨(hval x).1, (hval x).2.le⟩)
  exact ((hi.sub (((hB.norm.pow 2).div_const 2).continuousOn.integrableOn_compact hK)).add
    (hW.continuousOn.integrableOn_compact hK)).add
      (continuousOn_const.integrableOn_compact (μ := volume) hK)

end SerrinEpigraph
