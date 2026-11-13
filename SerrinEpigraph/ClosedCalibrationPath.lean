module

public import SerrinEpigraph.BoundaryCalibrationIntegral
public import SerrinEpigraph.ClosedRangeMinimality

/-!
# Continuity of closed calibration integrals along regularization paths
-/

public section
noncomputable section

open InnerProductSpace MeasureTheory Filter
open scoped Topology

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ : ℝ}

/-- Continuous level and vector fields give a continuous closed calibration up to level zero. -/
theorem RigidityHypotheses.boundaryCalibratedDensity_continuousOn_comp
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {α : Type*} [TopologicalSpace α] {S : Set α}
    {Y : α → Space m} {V : α → ℝ} {Z : α → Space (m + 1)}
    (hY : ContinuousOn Y S) (hV : ContinuousOn V S) (hZ : ContinuousOn Z S)
    (hval : ∀ a ∈ S, V a ∈ Set.Ico (0 : ℝ) 1) :
    ContinuousOn (fun a ↦ hr.boundaryCalibratedDensity h (Y a) (V a) (Z a)) S := by
  have hB := (hr.closedLevelGradient_continuousOn h).comp (hY.prodMk hV) hval
  have hW := h.normalizedPotential_continuousOn.comp hV
    (fun a ha ↦ ⟨(hval a ha).1, (hval a ha).2.le⟩)
  exact (((hB.inner hZ).sub ((hB.norm.pow 2).div_const 2)).add hW).add continuousOn_const

/-- Moving a nonnegative competitor slightly toward one half regularizes its levels. -/
theorem regularized_level_mem_Ioo {s ε : ℝ} (hs : s ∈ Set.Ico (0 : ℝ) 1)
    (hε : ε ∈ Set.Ioc (0 : ℝ) 1) :
    (1 - ε) * s + ε / 2 ∈ Set.Ioo (0 : ℝ) 1 := by
  have hε0 := hε.1
  have hε1 := hε.2
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.mpr hε.2) hs.1]
  · nlinarith [mul_nonneg (sub_nonneg.mpr hε.2) (sub_nonneg.mpr hs.2.le)]

/-- Closed calibration integrals vary continuously as a smooth competitor is lifted off zero. -/
theorem RigidityHypotheses.regularizedCalibration_continuousOn
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {v : Space (m + 1) → ℝ} (hv : ContDiff ℝ 1 v)
    (hval : ∀ x, v x ∈ Set.Ico (0 : ℝ) 1)
    {K : Set (Space (m + 1))} (hK : IsCompact K) :
    ContinuousOn (fun ε ↦ ∫ x in K,
      hr.boundaryCalibratedDensity h (horizontal x) ((1 - ε) * v x + ε / 2)
        ((1 - ε) • gradient v x)) (Set.Icc (0 : ℝ) 1) := by
  apply continuousOn_setIntegral_compact hK isCompact_Icc
    (F := fun p ↦ hr.boundaryCalibratedDensity h (horizontal p.2)
      ((1 - p.1) * v p.2 + p.1 / 2) ((1 - p.1) • gradient v p.2))
  have hg : Continuous (gradient v) :=
    (toDual ℝ (Space (m + 1))).symm.continuous.comp
      (hv.continuous_fderiv one_ne_zero)
  apply hr.boundaryCalibratedDensity_continuousOn_comp h
    (continuous_horizontal.comp continuous_snd).continuousOn
    (((continuous_const.sub continuous_fst).mul (hv.continuous.comp continuous_snd)).add
      (continuous_fst.div_const 2)).continuousOn
    ((continuous_const.sub continuous_fst).smul (hg.comp continuous_snd)).continuousOn
  intro p hp
  change (1 - p.1) * v p.2 + p.1 / 2 ∈ Set.Ico (0 : ℝ) 1
  by_cases he : p.1 = 0
  · simpa only [he, sub_zero, one_mul, zero_div, add_zero] using hval p.2
  · have hepos : 0 < p.1 := lt_of_le_of_ne hp.1.1 (Ne.symm he)
    have hs := regularized_level_mem_Ioo (hval p.2) ⟨hepos, hp.1.2⟩
    exact ⟨hs.1.le, hs.2⟩

/-- At strictly positive levels, the closed calibration integral is invariant under compact changes. -/
theorem RigidityHypotheses.boundaryCalibratedPath_endpoints_positive
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {v φ : Space (m + 1) → ℝ} (hv : ContDiff ℝ 1 v) (hφ : ContDiff ℝ 1 φ)
    {K : Set (Space (m + 1))} (hK : IsCompact K) (hsupp : tsupport φ ⊆ K)
    (hval : ∀ x, v x ∈ Set.Ioo (0 : ℝ) 1)
    (hend : ∀ x, v x + φ x ∈ Set.Ioo (0 : ℝ) 1) :
    (∫ x in K, hr.boundaryCalibratedDensity h (horizontal x) (v x + φ x)
      (gradient (fun y ↦ v y + φ y) x)) =
      ∫ x in K, hr.boundaryCalibratedDensity h (horizontal x) (v x) (gradient v x) := by
  have he := hr.calibratedPath_endpoints h isOpen_univ hv.contDiffOn hφ hK
    (Set.subset_univ K) hsupp (fun x _ ↦ hval x) (fun x _ ↦ hend x)
  have hg (x : Space (m + 1)) :
      gradient (fun y ↦ v y + φ y) x = gradient v x + gradient φ x := by
    simpa only [one_mul, one_smul] using
      gradient_affine_variation (hv.differentiable_one x) (hφ.differentiable_one x) 1
  have hi0 := hr.integrableOn_boundaryCalibratedDensity h hv
    (fun x ↦ ⟨(hval x).1.le, (hval x).2⟩) hK
  have hi1 := hr.integrableOn_boundaryCalibratedDensity h (hv.add hφ)
    (fun x ↦ ⟨(hend x).1.le, (hend x).2⟩) hK
  have hic : IntegrableOn (fun _ : Space (m + 1) ↦
      κ ^ 2 / 2 - normalizedPotential f 0) K :=
    continuousOn_const.integrableOn_compact hK
  have h0 (x : Space (m + 1)) :
      hr.calibratedDensity h (horizontal x) (v x) (gradient v x) =
        hr.boundaryCalibratedDensity h (horizontal x) (v x) (gradient v x) -
          (κ ^ 2 / 2 - normalizedPotential f 0) := by
    unfold boundaryCalibratedDensity calibratedDensity
    rw [hr.closedLevelGradient_eq h (hval x)]
    ring
  have h1 (x : Space (m + 1)) :
      hr.calibratedDensity h (horizontal x) (v x + φ x) (gradient v x + gradient φ x) =
        hr.boundaryCalibratedDensity h (horizontal x) (v x + φ x)
          (gradient (fun y ↦ v y + φ y) x) -
            (κ ^ 2 / 2 - normalizedPotential f 0) := by
    unfold boundaryCalibratedDensity calibratedDensity
    rw [hr.closedLevelGradient_eq h (hend x), hg x]
    ring
  simp_rw [h0, h1] at he
  rw [integral_sub hi1 hic, integral_sub hi0 hic] at he
  linarith

/-- Compact smooth changes preserve the closed calibration integral even when levels vanish. -/
theorem RigidityHypotheses.boundaryCalibratedPath_endpoints
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {v φ : Space (m + 1) → ℝ} (hv : ContDiff ℝ 1 v) (hφ : ContDiff ℝ 1 φ)
    {K : Set (Space (m + 1))} (hK : IsCompact K) (hsupp : tsupport φ ⊆ K)
    (hval : ∀ x, v x ∈ Set.Ico (0 : ℝ) 1)
    (hend : ∀ x, v x + φ x ∈ Set.Ico (0 : ℝ) 1) :
    (∫ x in K, hr.boundaryCalibratedDensity h (horizontal x) (v x + φ x)
      (gradient (fun y ↦ v y + φ y) x)) =
      ∫ x in K, hr.boundaryCalibratedDensity h (horizontal x) (v x) (gradient v x) := by
  let A := fun ε ↦ ∫ x in K, hr.boundaryCalibratedDensity h (horizontal x)
    ((1 - ε) * (v x + φ x) + ε / 2) ((1 - ε) • gradient (fun y ↦ v y + φ y) x)
  let B := fun ε ↦ ∫ x in K, hr.boundaryCalibratedDensity h (horizontal x)
    ((1 - ε) * v x + ε / 2) ((1 - ε) • gradient v x)
  have hA : ContinuousOn A (Set.Icc (0 : ℝ) 1) :=
    hr.regularizedCalibration_continuousOn h (hv.add hφ) hend hK
  have hB : ContinuousOn B (Set.Icc (0 : ℝ) 1) :=
    hr.regularizedCalibration_continuousOn h hv hval hK
  have he : ∀ ε ∈ Set.Ioc (0 : ℝ) 1, A ε = B ε := by
    intro ε hε
    let V := fun x ↦ (1 - ε) * v x + ε / 2
    let Φ := fun x ↦ (1 - ε) * φ x
    have hV : ContDiff ℝ 1 V := (contDiff_const.mul hv).add contDiff_const
    have hΦ : ContDiff ℝ 1 Φ := contDiff_const.mul hφ
    have hend' (x) : V x + Φ x = (1 - ε) * (v x + φ x) + ε / 2 := by
      dsimp [V, Φ]; ring
    have he' := hr.boundaryCalibratedPath_endpoints_positive h hV hΦ hK
      ((tsupport_mul_subset_right (f := fun _ ↦ 1 - ε) (g := φ)).trans hsupp)
      (fun x ↦ regularized_level_mem_Ioo (hval x) hε)
      (fun x ↦ by rw [hend' x]; exact regularized_level_mem_Ioo (hend x) hε)
    have hg (w : Space (m + 1) → ℝ) (hw : ContDiff ℝ 1 w) (x) :
        gradient (fun y ↦ (1 - ε) * w y + ε / 2) x = (1 - ε) • gradient w x := by
      simp only [gradient, fderiv_add_const, fderiv_const_mul (hw.differentiable_one x),
        map_smul]
    have hfun : (fun y ↦ V y + Φ y) = (fun y ↦ (1 - ε) * (v y + φ y) + ε / 2) :=
      funext hend'
    rw [hfun] at he'
    simp_rw [hend'] at he'
    dsimp only [V] at he'
    simp_rw [hg _ (hv.add hφ), hg _ hv] at he'
    exact he'
  have hcl : (0 : ℝ) ∈ closure (Set.Ioc (0 : ℝ) 1) := by
    rw [closure_Ioc (by norm_num : (0 : ℝ) ≠ 1)]
    simp
  have hA0 := (hA 0 (by simp)).mono Set.Ioc_subset_Icc_self
  have hB0 := (hB 0 (by simp)).mono Set.Ioc_subset_Icc_self
  have he0 : A 0 = B 0 := le_antisymm
    (ContinuousWithinAt.closure_le hcl hA0 hB0 (fun ε hε ↦ (he ε hε).le))
    (ContinuousWithinAt.closure_le hcl hB0 hA0 (fun ε hε ↦ (he ε hε).ge))
  simpa only [A, B, sub_zero, one_mul, zero_div, add_zero, one_smul] using he0

end SerrinEpigraph
