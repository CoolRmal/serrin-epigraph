module

public import SerrinEpigraph.LocalizedGraphRecovery

/-!
# Localized quantitative energy bound for graph partitions
-/

public section

open Set MeasureTheory Filter
open scoped Topology NNReal

namespace SerrinEpigraph

/-- Fixed compatible partitions have a localized area-action bound for every
Lipschitz ambient cutoff equal to one on the integration set. -/
theorem RigidityHypotheses.exists_localized_graphRecovery_energy_error
    {ι : Type*} [Fintype ι] {m d : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
    {f : ℝ → ℝ} {κ δ : ℝ} (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hδ : 0 < δ) {C : ℝ≥0} (hW : LipschitzOnWith C (normalizedPotential f) (Icc 0 1))
    {b : Space d → ℝ} (hb : ContDiff ℝ 1 b) {w : ι → Space d → ℝ}
    (hw : ∀ i, ContDiff ℝ 1 (w i)) (hwc : ∀ i, HasCompactSupport (w i))
    (hpos : ∀ i y, 0 ≤ w i y) (hsum : ∀ y, ∑ i, w i y ≤ 1)
    {A : Set (Space d)} (hA : IsCompact A) (hsupp : ∀ i y, y ∉ A → w i y = 0)
    {L : ι → ℝ} {H ε τ : ℝ} (hL : ∀ i, 0 < L i) (hLH : ∀ i, L i ≤ H)
    (hH : 0 ≤ H) (hε : 0 ≤ ε) (hτ : 0 < τ)
    (hscale : ∀ i y, 0 < w i y → graphAreaDensity b y ≤ L i ∧ L i ≤ graphAreaDensity b y + ε)
    {χ : Space (d + 1) → ℝ} {M : ℝ≥0} (hχ : LipschitzWith M χ)
    (hχpos : ∀ x, 0 ≤ χ x)
    {K : Set (Space (d + 1))} (hK : IsCompact K) (hproj : ∀ x ∈ K, horizontal x ∈ A)
    (hone : ∀ x ∈ K, ∑ i, w i (horizontal x) = 1)
    (hχone : ∀ x ∈ K, 1 ≤ χ x)
    {R : ℕ → ℝ} (hR : ∀ j, 0 < R j) (hRtop : Tendsto R atTop atTop) :
    let η := fun i x ↦ w i (horizontal x)
    let v := fun j i x ↦ recoveryProfile f δ (R j * graphHeight b x / L i)
    ∃ e : ℕ → ℝ, (∀ j, 0 ≤ e j) ∧ Tendsto e atTop (𝓝 0) ∧
      ∀ j, (∫ x in K, rescaledPhaseEnergyDensity f (R j) (partitionRecovery η (v j)) x) ≤
        (1 + τ) * ((∫ y in A, (χ (point y (b y)) +
          M * (recoveryTravelTime f δ 1 * H / R j)) * (graphAreaDensity b y + ε)) *
          recoveryActionPrimitive f δ 1) + e j +
        (volume A).toReal * (C * Real.sqrt (2 * (normalizedPotential f 0 + δ)) *
          (recoveryTravelTime f δ 1 * H) ^ 2 * ε) := by
  classical
  dsimp only
  let η := fun i x ↦ w i (horizontal x)
  let v := fun j i x ↦ recoveryProfile f δ (R j * graphHeight b x / L i)
  have hη (i : ι) : ContDiff ℝ 1 (η i) :=
    (hw i).comp (horizontalContinuousLinearMap (m := d)).contDiff
  have hηpos (i : ι) (x : Space (d + 1)) : 0 ≤ η i x := hpos i _
  have hηsum (x : Space (d + 1)) : ∑ i, η i x ≤ 1 := hsum _
  have hheight : ContDiff ℝ 1 (graphHeight b) := by
    unfold graphHeight
    exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (d + 1) ↦ ℝ) (Fin.last d)).contDiff.sub
      (hb.comp (horizontalContinuousLinearMap (m := d)).contDiff)
  have hv (j : ℕ) (i : ι) : LocallyLipschitz (v j i) :=
    (hr.recoveryProfile_lipschitz h hδ).locallyLipschitz.comp
      ((contDiff_const.mul hheight).div_const (L i)).locallyLipschitz
  have hval (j : ℕ) (i : ι) (x : Space (d + 1)) : v j i x ∈ Icc (0 : ℝ) 1 :=
    hr.recoveryProfile_mem_Icc h hδ _
  obtain ⟨e, hepos, het, he⟩ := exists_partitionRecovery_kinetic_error hη hv hval
    hηpos hηsum hτ hR hRtop hK
  refine ⟨e, hepos, het, ?_⟩
  intro j
  have hphase (x : Space (d + 1)) (_ : x ∈ K) (i : ι) : 0 < v j i x ↔ x ∈ epigraph b := by
    rw [hr.recoveryProfile_pos_iff h hδ, div_pos_iff_of_pos_right (hL i),
      mul_pos_iff_of_pos_left (hR j)]
    exact sub_pos
  have hclose (x : Space (d + 1)) (_ : x ∈ K) (i k : ι) (hi : 0 < η i x) (hk : 0 < η k x) :
      |(L k)⁻¹ - (L i)⁻¹| ≤ ε := graphScales_inverse_close
    (hscale k _ hk).1 (hscale i _ hi).1 (hscale k _ hk).2 (hscale i _ hi).2
  have hpot := hr.integral_partitionRecovery_potential_defect_le h hδ (hR j) hW hb.continuous
    (fun i ↦ (hη i).continuous) hηpos hηsum hL hLH hH hε hA.measurableSet
    hA.measure_ne_top hK hproj hone hclose
  have htotal := hr.integral_partitionRecovery_energy_le h (fun i ↦ (hη i).locallyLipschitz)
    (hv j) hηpos hηsum (hval j) (hR j).le hτ.le hK hone hphase (he j) hpot
  have hprincipal := hr.sum_graphRecovery_energy_le_cutoff_area h hδ (hR j) hb
    (fun i ↦ (hw i).continuous) hwc hpos hsum hA hsupp hL hLH hH hε
    (fun i y hy ↦ (hscale i y hy).2)
    (fun i y hy ↦ graphScale_controls_slope (hscale i y hy).1) hχ hχpos hK hχone
  have hv_eq (i : ι) : geometricRecoveryProfile f δ (R j)
      (fun z ↦ graphHeight b z / L i) = v j i := by
    funext x
    exact congrArg (recoveryProfile f δ) (mul_div_assoc _ _ _).symm
  simp only [hv_eq] at hprincipal
  exact htotal.trans (add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left hprincipal (by linarith)) le_rfl) le_rfl)

end SerrinEpigraph
