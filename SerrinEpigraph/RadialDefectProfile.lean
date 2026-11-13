module

public import SerrinEpigraph.RadialEnergyDefect
public import SerrinEpigraph.LimitingPhaseGeometry
public import SerrinEpigraph.Truncation

/-!
# A fixed cutoff detecting radial variation and one common limiting phase
-/

public section

noncomputable section

open Set Metric MeasureTheory Filter
open scoped Topology

namespace SerrinEpigraph

/-- A C1 cutoff with strictly negative derivative at squared radii below one. -/
@[expose] def radialDefectProfile (s : ℝ) : ℝ := max (1 - s) 0 ^ 2

/-- The squared positive-part cutoff has the regularity required by the energy identity. -/
theorem radialDefectProfile_contDiff : ContDiff ℝ 1 radialDefectProfile :=
  (contDiff_positivePart_pow (k := 2) le_rfl).comp (contDiff_const.sub contDiff_id)

/-- The exact cutoff derivative, including its junction at one. -/
theorem radialDefectProfile_deriv (s : ℝ) : deriv radialDefectProfile s = -2 * max (1 - s) 0 := by
  have hd := (hasDerivAt_positivePart_pow (k := 2) le_rfl (1 - s)).comp s
    ((hasDerivAt_id s).const_sub 1)
  change HasDerivAt radialDefectProfile _ s at hd
  rw [hd.deriv]
  norm_num

/-- The cutoff vanishes at all squared radii at least one. -/
theorem radialDefectProfile_zero {s : ℝ} (hs : 1 ≤ s) : radialDefectProfile s = 0 := by
  simp [radialDefectProfile, max_eq_right (by linarith : 1 - s ≤ 0)]

/-- The radial cutoff has values between zero and one on nonnegative squared radii. -/
theorem radialDefectProfile_mem_Icc {s : ℝ} (hs : 0 ≤ s) :
    radialDefectProfile s ∈ Icc (0 : ℝ) 1 := by
  have h0 : 0 ≤ max (1 - s) 0 := le_max_right _ _
  have h1 : max (1 - s) 0 ≤ 1 := max_le (by linarith) (by norm_num)
  exact ⟨sq_nonneg _, by dsimp only [radialDefectProfile]; nlinarith⟩

/-- The radial cutoff decreases. -/
theorem radialDefectProfile_antitone : Antitone radialDefectProfile := by
  intro s t hst
  have hh : max (1 - t) 0 ≤ max (1 - s) 0 := max_le_max (by linarith) le_rfl
  exact (sq_le_sq₀ (le_max_right _ _) (le_max_right _ _)).mpr hh

/-- Its negative derivative is uniformly positive on the inner half-ball. -/
theorem radialDefectProfile_neg_deriv_lower {s : ℝ} (hs : s ≤ 1 / 4) :
    3 / 2 ≤ -deriv radialDefectProfile s := by
  rw [radialDefectProfile_deriv, max_eq_left (by linarith)]
  linarith

/-- One phase limit can be chosen together with radial-defect decay at every fixed multiple
of its scales. This does not yet assert that the limiting phase is invariant under dilation. -/
theorem RigidityHypotheses.exists_phase_with_vanishing_radial_defect
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) :
    ∃ R : ℕ → ℝ, (∀ j, 1 ≤ R j) ∧ Tendsto R atTop atTop ∧
      ∃ E : Set (Space (m + 1)), MeasurableSet E ∧
        (∀ K : Set (Space (m + 1)), IsCompact K →
          Tendsto (fun j ↦ ∫ x in K, ‖zeroExtension g u (R j • x) -
            E.indicator (fun _ ↦ (1 : ℝ)) x‖) atTop (𝓝 0)) ∧
        (∀ k : ℕ, Tendsto (fun j ↦
          radialEnergyDefect g u radialDefectProfile 0 ((k + 1 : ℝ) * R j)) atTop (𝓝 0)) ∧
        (∀ t : ℝ, 0 ≤ t → ∀ᵐ x ∂volume, x ∈ E → x + t • verticalDirection m ∈ E) ∧
        (∀ (basis : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1)))
          (s r₀ : ℝ), 0 < s → r₀ < s →
          ∀ b : Space m → ℝ, ContDiff ℝ 1 b →
          (∀ᵐ x ∂volume.restrict (ball 0 s \ closedBall 0 r₀), x ∈ E ↔ x ∈ epigraph b) →
          variationalPerimeter basis E (ball 0 s) ≤
            variationalPerimeter basis (epigraph b) (ball 0 s)) := by
  obtain ⟨R, hR, hRt, hD⟩ := hr.exists_scales_radialEnergyDefect_tendsto_zero h
    radialDefectProfile_contDiff (fun _ hs ↦ radialDefectProfile_zero (by linarith))
    (fun _ hs ↦ radialDefectProfile_mem_Icc hs) radialDefectProfile_antitone
  obtain ⟨φ, hφ, E, hE, hlocal, _, hvertical, hminimal, _⟩ :=
    hr.exists_phase_with_geometric_properties h R hR hRt
  exact ⟨fun j ↦ R (φ j), fun j ↦ hR (φ j), hRt.comp hφ.tendsto_atTop,
    E, hE, hlocal, fun k ↦ (hD k).comp hφ.tendsto_atTop, hvertical, hminimal⟩

end SerrinEpigraph
