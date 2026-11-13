module

public import SerrinEpigraph.RecoveryDiagonalScale

/-!+# Integral convergence for varying graph recovery partitions
-/

public section

open Set MeasureTheory Filter
open scoped Topology

namespace SerrinEpigraph

/-- Recovery mixtures converge in local L1 even when their finite partitions
vary, provided their graph scales are uniformly bounded and layers vanish. -/
theorem RigidityHypotheses.varying_graphRecovery_integral_limit
    {ι : ℕ → Type*} [∀ j, Fintype (ι j)] {m d : ℕ}
    {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {δ R : ℕ → ℝ} (hδ : ∀ j, 0 < δ j) (hR : ∀ j, 0 < R j)
    {H : ℝ} {L : (j : ℕ) → ι j → ℝ}
    (hL : ∀ j i, 0 < L j i) (hLH : ∀ j i, L j i ≤ H)
    (hwidth : Tendsto (fun j ↦ recoveryTravelTime f (δ j) 1 * H / R j) atTop (𝓝 0))
    {b : Space d → ℝ} (hb : Continuous b)
    {η : (j : ℕ) → ι j → Space (d + 1) → ℝ}
    (hη : ∀ j i, Continuous (η j i)) (hpos : ∀ j i x, 0 ≤ η j i x)
    (hsum : ∀ j x, ∑ i, η j i x ≤ 1) {K : Set (Space (d + 1))}
    (hK : IsCompact K) (hone : ∀ j x, x ∈ K → ∑ i, η j i x = 1) :
    Tendsto (fun j ↦ ∫ x in K,
      ‖partitionRecovery (η j)
        (fun i z ↦ recoveryProfile f (δ j) (R j * graphHeight b z / L j i)) x -
        (epigraph b).indicator (fun _ ↦ (1 : ℝ)) x‖) atTop (𝓝 0) := by
  classical
  let z := (epigraph b).indicator (fun _ ↦ (1 : ℝ))
  let v := fun j (i : ι j) x ↦ recoveryProfile f (δ j) (R j * graphHeight b x / L j i)
  have hz : Measurable z := measurable_const.indicator (isOpen_epigraph hb).measurableSet
  have hheight : Continuous (graphHeight b) := by
    exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (d + 1) ↦ ℝ) (Fin.last d)).continuous.sub
      (hb.comp (horizontalContinuousLinearMap (m := d)).continuous)
  have hv (j : ℕ) (i : ι j) : Continuous (v j i) :=
    (hr.recoveryProfile_lipschitz h (hδ j)).continuous.comp
      ((continuous_const.mul hheight).div_const (L j i))
  have hp (j : ℕ) : Continuous (partitionRecovery (η j) (v j)) :=
    continuous_finsetSum _ (fun i _ ↦ (hη j i).mul (hv j i))
  have hval (j : ℕ) (x : Space (d + 1)) :
      partitionRecovery (η j) (v j) x ∈ Icc (0 : ℝ) 1 :=
    partitionRecovery_mem_Icc (hpos j) (hsum j)
      (fun i x ↦ hr.recoveryProfile_mem_Icc h (hδ j) _) x
  have he := tendsto_integral_of_dominated_convergence (μ := volume.restrict K)
    (F := fun j x ↦ ‖partitionRecovery (η j) (v j) x - z x‖)
    (f := fun _ ↦ (0 : ℝ)) (fun _ ↦ (1 : ℝ))
    (fun j ↦ ((hp j).measurable.sub hz).norm.aestronglyMeasurable)
    (continuous_const.continuousOn.integrableOn_compact hK)
    (fun j ↦ Eventually.of_forall (fun x ↦ by
      have hx := hval j x
      simp only [Real.norm_eq_abs, abs_abs]
      apply abs_le.mpr
      by_cases hxE : x ∈ epigraph b <;> simp [z, hxE] <;>
        constructor <;> linarith [hx.1, hx.2]))
    (ae_restrict_of_forall_mem hK.measurableSet (fun x hx ↦ by
      apply tendsto_const_nhds.congr'
      filter_upwards [hr.varying_graphRecovery_eventually_eq h hδ hR hL hLH hwidth (b := b)
        (fun j ↦ hone j x hx)] with j hj
      simp only [v, z, hj, sub_self, norm_zero]))
  simpa only [integral_zero] using he

end SerrinEpigraph
