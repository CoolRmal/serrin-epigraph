module

public import SerrinEpigraph.PlaneTiltRotation
public import SerrinEpigraph.PerimeterInvariance
public import SerrinEpigraph.GraphPerimeter

/-!
# Exact perimeter of arbitrary planar halfspaces
-/

public section

noncomputable section

open Set Metric MeasureTheory Filter InnerProductSpace
open scoped Topology ENNReal

namespace SerrinEpigraph

/-- Conjugation of a vector field by an isometry preserves its intrinsic divergence. -/
theorem fieldDivergence_isometry_conjugate {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) (Q : Space d ≃ₗᵢ[ℝ] Space d)
    (F : Space d → Space d) (x : Space d) :
    fieldDivergence b (fun y ↦ Q.symm (F (Q y))) x = fieldDivergence b F (Q x) := by
  rw [fieldDivergence_basis_independent b (b.map Q) F]
  have hd : fderiv ℝ (fun y ↦ Q.symm (F (Q y))) x =
      (Q.symm : Space d →L[ℝ] Space d).comp
        ((fderiv ℝ F (Q x)).comp (Q : Space d →L[ℝ] Space d)) := by
    change fderiv ℝ (Q.symm ∘ (F ∘ Q)) x = _
    rw [Q.symm.comp_fderiv]
    congr 1
    exact Q.toContinuousLinearEquiv.comp_right_fderiv
  unfold fieldDivergence
  apply Finset.sum_congr rfl
  intro i hi
  rw [hd]
  simp only [ContinuousLinearMap.comp_apply, OrthonormalBasis.map_apply]
  change inner ℝ (b i) (Q.symm (fderiv ℝ F (Q x) (Q (b i)))) = _
  rw [← Q.inner_map_map, Q.apply_symm_apply]

/-- Pulling back the phase and its test domain by an isometry cannot increase perimeter. -/
theorem variationalPerimeter_preimage_isometry_le {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) (Q : Space d ≃ₗᵢ[ℝ] Space d)
    (E Ω : Set (Space d)) :
    variationalPerimeter b (Q ⁻¹' E) (Q ⁻¹' Ω) ≤ variationalPerimeter b E Ω := by
  unfold variationalPerimeter
  refine iSup_le (fun F ↦ iSup_le (fun hF ↦ iSup_le (fun hc ↦
    iSup_le (fun hs ↦ iSup_le (fun hunit ↦ ?_)))))
  let G : Space d → Space d := fun x ↦ Q (F (Q.symm x))
  have hG : ContDiff ℝ 1 G := Q.contDiff.comp (hF.comp Q.symm.contDiff)
  have hcG : HasCompactSupport G :=
    (hc.comp_homeomorph Q.symm.toHomeomorph).comp_left Q.map_zero
  have hsG : tsupport G ⊆ Ω := by
    have h₁ : tsupport G ⊆ tsupport (F ∘ Q.symm) := tsupport_comp_subset Q.map_zero _
    have h₂ : tsupport (F ∘ Q.symm) ⊆ Q.symm ⁻¹' tsupport F :=
      tsupport_comp_subset_preimage F Q.symm.continuous
    intro x hx
    have hh := hs (h₂ (h₁ hx))
    simpa only [mem_preimage, Q.apply_symm_apply] using hh
  have huG (x : Space d) : ‖G x‖ ≤ 1 := by simpa only [G, Q.norm_map] using hunit (Q.symm x)
  have hp : (∫ x, (Q ⁻¹' E).indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b F x) =
      ∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b G x := by
    rw [← Q.measurePreserving.integral_comp Q.toHomeomorph.measurableEmbedding
      (fun x ↦ E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b G x)]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro x
    have hd := fieldDivergence_isometry_conjugate b Q.symm F (Q x)
    simp only [Q.symm_symm, Q.symm_apply_apply] at hd
    simp only [G, hd]
    congr 1
  rw [hp]
  exact le_iSup_of_le G (le_iSup_of_le hG (le_iSup_of_le hcG
    (le_iSup_of_le hsG (le_iSup_of_le huG le_rfl))))

/-- Euclidean coordinate changes preserve variational perimeter exactly. -/
theorem variationalPerimeter_preimage_isometry {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Space d)) (Q : Space d ≃ₗᵢ[ℝ] Space d)
    (E Ω : Set (Space d)) :
    variationalPerimeter b (Q ⁻¹' E) (Q ⁻¹' Ω) = variationalPerimeter b E Ω := by
  apply le_antisymm (variationalPerimeter_preimage_isometry_le b Q E Ω)
  have hh := variationalPerimeter_preimage_isometry_le b Q.symm (Q ⁻¹' E) (Q ⁻¹' Ω)
  have hE : Q.symm ⁻¹' (Q ⁻¹' E) = E := by ext x; simp
  have hΩ : Q.symm ⁻¹' (Q ⁻¹' Ω) = Ω := by ext x; simp
  simpa only [hE, hΩ] using hh

/-- The horizontal halfspace has exactly the horizontal ball's volume as perimeter. -/
theorem horizontal_halfspace_perimeter_closedBall_volume {m : ℕ}
    (b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))) {r : ℝ} (hr : 0 < r) :
    variationalPerimeter b (epigraph (fun _ : Space m ↦ (0 : ℝ))) (ball 0 r) =
      volume (closedBall (0 : Space m) r) := by
  have htrace : {y : Space m | point y 0 ∈ ball (0 : Space (m + 1)) r} = ball 0 r := by
    ext y
    simp only [mem_ofPred_eq, mem_ball, dist_zero_right, norm_point_zero]
  rw [graph_perimeter_eq_area b contDiff_const isOpen_ball, htrace]
  have harea (y : Space m) : graphAreaDensity (fun _ : Space m ↦ (0 : ℝ)) y = 1 := by
    simp [graphAreaDensity, gradient_fun_const]
  simp_rw [harea]
  simp only [ENNReal.ofReal_one, lintegral_const, Measure.restrict_apply_univ, one_mul]
  rw [Measure.addHaar_ball_of_pos volume _ hr, Measure.addHaar_closedBall volume _ hr.le]

/-- The exact perimeter formula for a halfspace in any unit-normal direction. -/
theorem positive_halfspace_perimeter_closedBall_volume {m : ℕ}
    (b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1)))
    {e : Space (m + 1)} (he : ‖e‖ = 1) {r : ℝ} (hr : 0 < r) :
    variationalPerimeter b {x : Space (m + 1) | 0 < inner ℝ e x} (ball 0 r) =
      volume (closedBall (0 : Space m) r) := by
  obtain ⟨Q, hQ⟩ := exists_linearIsometryEquiv_vertical he
  have hphase : Q ⁻¹' {x : Space (m + 1) | 0 < inner ℝ e x} =
      epigraph (fun _ : Space m ↦ (0 : ℝ)) := by
    ext x
    change (0 < inner ℝ e (Q x)) ↔ 0 < x (Fin.last m)
    rw [← hQ, Q.inner_map_map]
    simp [verticalDirection, EuclideanSpace.inner_single_left]
  rw [← variationalPerimeter_preimage_isometry b Q,
    hphase, Q.preimage_ball, map_zero]
  exact horizontal_halfspace_perimeter_closedBall_volume b hr

/-- The real-valued planar perimeter is the unit-ball constant times the surface power. -/
theorem positive_halfspace_perimeter_toReal {m : ℕ}
    (b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1)))
    {e : Space (m + 1)} (he : ‖e‖ = 1) {r : ℝ} (hr : 0 < r) :
    (variationalPerimeter b {x : Space (m + 1) | 0 < inner ℝ e x} (ball 0 r)).toReal =
      r ^ m * volume.real (closedBall (0 : Space m) 1) := by
  rw [positive_halfspace_perimeter_closedBall_volume b he hr]
  exact (Measure.addHaar_real_closedBall' volume (0 : Space m) hr.le).trans
    (by rw [finrank_euclideanSpace_fin])

end SerrinEpigraph
