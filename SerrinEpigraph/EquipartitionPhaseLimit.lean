module

public import SerrinEpigraph.EnergyEquipartition

/-!
# A common nontrivial conical phase with asymptotic energy equipartition
-/

public section

open Set MeasureTheory Metric Filter
open scoped Topology ENNReal

namespace SerrinEpigraph

/-- One sequence realizes the geometric phase limit and both local energy identities.
The comparison conclusion remains restricted to graph competitors. -/
theorem RigidityHypotheses.exists_phase_with_equipartition
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) :
    ∃ R : ℕ → ℝ, (∀ j, 1 ≤ R j) ∧ Tendsto R atTop atTop ∧
      ∃ E : Set (Space (m + 1)), MeasurableSet E ∧
        (∀ K : Set (Space (m + 1)), IsCompact K →
          Tendsto (fun j ↦ ∫ x in K, ‖zeroExtension g u (R j • x) -
            E.indicator (fun _ ↦ (1 : ℝ)) x‖) atTop (𝓝 0)) ∧
        (volume E ≠ 0 ∧ volume Eᶜ ≠ 0) ∧
        (∀ a : ℝ, 0 < a → ∀ᵐ x ∂volume, x ∈ E ↔ a • x ∈ E) ∧
        (∃ C : ℝ, 0 < C ∧ ∀ (k : ℕ)
          (basis : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))),
          variationalPerimeter basis E (ball 0 (k + 1 : ℝ)) ≤
            ENNReal.ofReal (C * (k + 1 : ℝ) ^ m)) ∧
        (∀ t : ℝ, 0 ≤ t → ∀ᵐ x ∂volume, x ∈ E → x + t • verticalDirection m ∈ E) ∧
        (∀ (basis : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1)))
          (s r₀ : ℝ), 0 < s → r₀ < s →
          ∀ b : Space m → ℝ, ContDiff ℝ 1 b →
          (∀ᵐ x ∂volume.restrict (ball 0 s \ closedBall 0 r₀), x ∈ E ↔ x ∈ epigraph b) →
          variationalPerimeter basis E (ball 0 s) ≤
            variationalPerimeter basis (epigraph b) (ball 0 s)) ∧
        (HasOneSidedLinearBound g →
          (∃ C : ℝ, 0 < C ∧ ∀ᵐ x ∂volume,
            x ∈ E → -C * ‖horizontal x‖ ≤ x (Fin.last m)) ∨
          (∃ C : ℝ, 0 < C ∧ ∀ᵐ x ∂volume,
            C * ‖horizontal x‖ < x (Fin.last m) → x ∈ E)) ∧
        (∀ K : Set (Space (m + 1)), IsCompact K →
          Tendsto (fun j ↦ ∫ x in K,
            rescaledDiscrepancyDensity f (R j) (fun y ↦ zeroExtension g u (R j • y)) x)
              atTop (𝓝 0)) ∧
        (∀ K : Set (Space (m + 1)), IsCompact K →
          Tendsto (fun j ↦
            (∫ x in K, rescaledPhaseEnergyDensity f (R j)
              (fun y ↦ zeroExtension g u (R j • y)) x) -
            (∫ x in K, ‖gradient (fun y ↦ phasePrimitive f (zeroExtension g u (R j • y))) x‖))
              atTop (𝓝 0)) := by
  obtain ⟨R, hR, hRt, hdef⟩ := hr.exists_scales_energy_defects_tendsto_zero h
    radialDefectProfile_contDiff (fun _ hs ↦ radialDefectProfile_zero (by linarith))
    (fun _ hs ↦ radialDefectProfile_mem_Icc hs) radialDefectProfile_antitone
  obtain ⟨φ, hφ, E, hE, hlocal, hperim, hvertical, hminimal, hside⟩ :=
    hr.exists_phase_with_geometric_properties h R hR hRt
  have hRφ (j : ℕ) : 1 ≤ R (φ j) := hR _
  have hRφ0 (j : ℕ) : 0 < R (φ j) := zero_lt_one.trans_le (hRφ j)
  have hRtφ := hRt.comp hφ.tendsto_atTop
  have hD (k : ℕ) := ((hdef k).1).comp hφ.tendsto_atTop
  have hB (k : ℕ) := ((hdef k).2).comp hφ.tendsto_atTop
  refine ⟨fun j ↦ R (φ j), hRφ, hRtφ, E, hE, hlocal,
    hr.phase_limit_nontrivial h hRφ hRtφ hlocal,
    fun _ ha ↦ hr.phase_limit_dilation_invariant h hRφ hD hE hlocal ha,
    hperim, hvertical, hminimal, hside, ?_, ?_⟩
  · exact fun _ hK ↦ hr.rescaledDiscrepancy_tendsto_zero_compact h hRφ0 hB hK
  · exact fun _ hK ↦ hr.rescaled_energy_primitive_gap_tendsto_zero h hRφ0 hB hK

end SerrinEpigraph
