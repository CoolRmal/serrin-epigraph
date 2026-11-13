module

public import SerrinEpigraph.AnnularSpatial
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Continuous second derivatives of annular solutions
-/

public section

open Set

namespace SerrinEpigraph

variable {m : ℕ} {f : ℝ → ℝ} {a b : ℝ}

/-- The radial slope is continuously differentiable on the open radial interval. -/
theorem IncreasingRadialSegment.slope_contDiffOn_one
    (v : IncreasingRadialSegment f m a b) (hf : ContDiffOn ℝ 1 f (Ici 0)) :
    ContDiffOn ℝ 1 v.slope (Ioo a b) := by
  rw [show (1 : WithTop ℕ∞) = 0 + 1 by rfl, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
  refine ⟨fun r hr ↦ (v.slope_derivative r hr).differentiableAt.differentiableWithinAt,
    by simp, contDiffOn_zero.mpr ?_⟩
  have hQ := v.value_continuous.mono Ioo_subset_Icc_self
  have hP := v.slope_continuous.mono Ioo_subset_Icc_self
  have hF := hf.continuousOn.comp hQ (fun r hr ↦ (v.value_pos r hr).le)
  have hc : ContinuousOn (fun r ↦ -f (v.value r) - (m : ℝ) / r * v.slope r) (Ioo a b) :=
    hF.neg.sub ((continuousOn_const.div continuousOn_id
      (fun r hr ↦ (v.inner_pos.trans hr.1).ne')).mul hP)
  apply hc.congr
  intro r hr
  exact (v.slope_derivative r hr).deriv

/-- The radial value is twice continuously differentiable on the open radial interval. -/
theorem IncreasingRadialSegment.value_contDiffOn_two
    (v : IncreasingRadialSegment f m a b) (hf : ContDiffOn ℝ 1 f (Ici 0)) :
    ContDiffOn ℝ 2 v.value (Ioo a b) := by
  rw [show (2 : WithTop ℕ∞) = 1 + 1 by norm_num,
    contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
  refine ⟨fun r hr ↦ (v.value_derivative r hr).differentiableAt.differentiableWithinAt,
    by simp, ?_⟩
  apply (v.slope_contDiffOn_one hf).congr
  intro r hr
  exact (v.value_derivative r hr).deriv

/-- The spatial annular solution is twice continuously differentiable throughout the annulus. -/
theorem IncreasingRadialSegment.spatial_contDiffOn_two
    (v : IncreasingRadialSegment f m a b) (hf : ContDiffOn ℝ 1 f (Ici 0))
    (c : Space (m + 1)) : ContDiffOn ℝ 2 (v.spatial c) (radialAnnulus c a b) := by
  change ContDiffOn ℝ 2 (v.value ∘ (fun x : Space (m + 1) ↦ ‖x - c‖)) _
  apply (v.value_contDiffOn_two hf).comp
    (f := fun x : Space (m + 1) ↦ ‖x - c‖) ?_ ?_
  · intro x hx
    have hne : x - c ≠ 0 := norm_pos_iff.mp (v.inner_pos.trans hx.1)
    exact ((contDiffAt_norm ℝ hne).comp x (contDiffAt_id.sub contDiffAt_const)).contDiffWithinAt
  · exact fun _ hx ↦ hx

/-- The radial value has its prescribed slope as a right derivative at the inner endpoint. -/
theorem IncreasingRadialSegment.value_hasDerivWithinAt_inner
    (v : IncreasingRadialSegment f m a b) :
    HasDerivWithinAt v.value (v.slope a) (Ici a) a := by
  apply hasDerivWithinAt_Ici_of_tendsto_deriv (s := Ioo a b)
    (fun r hr ↦ (v.value_derivative r hr).differentiableAt.differentiableWithinAt)
  · exact (v.value_continuous a ⟨le_rfl, v.radii_lt.le⟩).mono Ioo_subset_Icc_self
  · exact Ioo_mem_nhdsGT v.radii_lt
  · have hp := v.slope_continuous a ⟨le_rfl, v.radii_lt.le⟩
    rw [ContinuousWithinAt, nhdsWithin_Icc_eq_nhdsGE v.radii_lt] at hp
    apply (hp.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)).congr'
    filter_upwards [Ioo_mem_nhdsGT v.radii_lt] with r hr
    exact (v.value_derivative r hr).deriv.symm

/-- The inner sphere derivative within the closed annulus has the prescribed radial slope. -/
theorem IncreasingRadialSegment.spatial_hasFDerivWithinAt_inner
    (v : IncreasingRadialSegment f m a b) {c x : Space (m + 1)}
    (hx : x ∈ Metric.sphere c a) :
    HasFDerivWithinAt (v.spatial c) ((v.slope a / a) • innerSL ℝ (x - c))
      (closedRadialAnnulus c a b) x := by
  have hnorm : ‖x - c‖ = a := by simpa only [Metric.mem_sphere, dist_eq_norm] using hx
  have hne : x - c ≠ 0 := norm_ne_zero_iff.mp (hnorm ▸ v.inner_pos.ne')
  have hn := (hasFDerivAt_euclidean_norm hne).comp x ((hasFDerivAt_id x).sub_const c)
  have hmap : MapsTo (fun y : Space (m + 1) ↦ ‖y - c‖)
      (closedRadialAnnulus c a b) (Ici a) := fun _ hy ↦ hy.1
  have he := v.value_hasDerivWithinAt_inner.comp_hasFDerivWithinAt_of_eq x
    hn.hasFDerivWithinAt hmap hnorm.symm
  convert he using 1
  · rfl
  · simp only [hnorm, ContinuousLinearMap.comp_id, smul_smul, div_eq_mul_inv]

end SerrinEpigraph
