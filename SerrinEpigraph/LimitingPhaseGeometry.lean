module

public import SerrinEpigraph.PhaseVerticalMonotonicity

/-!
# Geometric properties of one common limiting phase
-/

public section

open Set MeasureTheory Metric Filter
open scoped Topology ENNReal

namespace SerrinEpigraph

/-- The positive-phase indicators converge to the same local limit as the
rescaled solutions, so geometric information is not lost when selecting that limit. -/
theorem RigidityHypotheses.phaseIndicator_limit_of_solution_limit
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (R : ℕ → ℝ) (hR : Tendsto R atTop atTop) {r : ℝ} (hradius : 0 < r)
    {E : Set (Space (m + 1))} (hE : MeasurableSet E)
    (ht : Tendsto (fun j ↦ ∫ x in closedBall 0 r,
      ‖zeroExtension g u (R j • x) - E.indicator (fun _ ↦ (1 : ℝ)) x‖) atTop (𝓝 0)) :
    Tendsto (fun j ↦ ∫ x in closedBall 0 r,
      ‖positivePhaseIndicator (zeroExtension g u) (R j • x) -
        E.indicator (fun _ ↦ (1 : ℝ)) x‖) atTop (𝓝 0) := by
  let F := fun j x ↦ zeroExtension g u (R j • x)
  let P := fun j x ↦ positivePhaseIndicator (zeroExtension g u) (R j • x)
  let V := E.indicator (fun _ : Space (m + 1) ↦ (1 : ℝ))
  have hcont (j : ℕ) : Continuous (F j) :=
    h.zeroExtension_continuous.comp (continuous_id.const_smul (R j))
  have hF (j : ℕ) : IntegrableOn (F j) (closedBall 0 r) :=
    (hcont j).continuousOn.integrableOn_compact (isCompact_closedBall 0 r)
  have hP (j : ℕ) : IntegrableOn (P j) (closedBall 0 r) :=
    (continuousOn_const.integrableOn_compact (isCompact_closedBall 0 r)).indicator
      (isOpen_lt (continuous_const (y := (0 : ℝ))) (hcont j)).measurableSet
  have hV : IntegrableOn V (closedBall 0 r) :=
    (continuousOn_const.integrableOn_compact (isCompact_closedBall 0 r)).indicator hE
  have herr : Tendsto (fun j ↦ ∫ x in closedBall 0 r, ‖P j x - F j x‖)
      atTop (𝓝 0) := by
    simpa only [F, P, Real.norm_eq_abs, phaseIndicatorError, Function.comp_def] using
      (hr.phaseIndicatorError_tendsto_zero h hradius).comp hR
  have hsum := herr.add ht
  simp only [zero_add] at hsum
  apply squeeze_zero (fun j ↦ integral_nonneg (fun x ↦ norm_nonneg _)) _ hsum
  intro j
  exact integral_norm_sub_triangle (hP j) (hF j) hV

/-- Every fixed local phase limit, not just a separately extracted subsequence,
has a surface-order perimeter bound on integer-radius balls. -/
theorem RigidityHypotheses.phase_limit_perimeter_bound
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {R : ℕ → ℝ} (hR : ∀ j, 1 ≤ R j)
    {E : Set (Space (m + 1))} (hE : MeasurableSet E)
    (hlim : ∀ k : ℕ, Tendsto (fun j ↦ ∫ x in closedBall 0 (k + 1 : ℝ),
      ‖zeroExtension g u (R j • x) - E.indicator (fun _ ↦ (1 : ℝ)) x‖) atTop (𝓝 0)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (k : ℕ)
      (basis : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))),
      variationalPerimeter basis E (ball 0 (k + 1 : ℝ)) ≤
        ENNReal.ofReal (C * (k + 1 : ℝ) ^ m) := by
  obtain ⟨C, hC, hbound⟩ := hr.rescaledPhaseEnergy_bound h
  have hc : 0 < phasePrimitive f 1 := hr.phasePrimitive_one_pos h
  refine ⟨C / phasePrimitive f 1, div_pos hC hc, fun k basis ↦ ?_⟩
  have hval (j : ℕ) (x : Space (m + 1)) : zeroExtension g u (R j • x) ∈ Icc (0 : ℝ) 1 :=
    ⟨h.zeroExtension_nonneg _, (hr.zeroExtension_lt_one _).le⟩
  have hv (j : ℕ) : LocallyLipschitz (fun x ↦ zeroExtension g u (R j • x)) :=
    h.zeroExtension_locallyLipschitz.comp (lipschitzWith_smul (R j)).locallyLipschitz
  apply hr.perimeter_le_of_recovery_sequence h basis
    (fun j ↦ zero_lt_one.trans_le (hR j)) hv hval hE (isCompact_closedBall _ _)
    ball_subset_closedBall (hlim k) (B := fun _ ↦ C * (k + 1 : ℝ) ^ m)
  · intro j
    apply hbound (R j) (k + 1 : ℝ) (zero_lt_one.trans_le (hR j))
    nlinarith [hR j, Nat.cast_nonneg (α := ℝ) k]
  · have he : (C / phasePrimitive f 1 * (k + 1 : ℝ) ^ m) * phasePrimitive f 1 =
        C * (k + 1 : ℝ) ^ m := by field_simp
    rw [he]
    exact tendsto_const_nhds

/-- A single phase limit simultaneously has local L1 convergence, surface-order
perimeter, upward translation monotonicity, graph-competitor minimality under
almost-everywhere annular agreement, and the cone constraint whenever the original
graph has a one-sided linear bound. -/
theorem RigidityHypotheses.exists_phase_with_geometric_properties
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (R : ℕ → ℝ) (hR : ∀ j, 1 ≤ R j) (hRt : Tendsto R atTop atTop) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ E : Set (Space (m + 1)), MeasurableSet E ∧
      (∀ K : Set (Space (m + 1)), IsCompact K →
        Tendsto (fun j ↦ ∫ x in K, ‖zeroExtension g u (R (φ j) • x) -
          E.indicator (fun _ ↦ (1 : ℝ)) x‖) atTop (𝓝 0)) ∧
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
          C * ‖horizontal x‖ < x (Fin.last m) → x ∈ E)) := by
  obtain ⟨φ, hφ, E, hE, hlocal, _⟩ :=
    hr.exists_limiting_phase_with_graph_minimality h R hR hRt
  have hRφ (j : ℕ) : 1 ≤ R (φ j) := hR _
  have hRtφ := hRt.comp hφ.tendsto_atTop
  refine ⟨φ, hφ, E, hE, hlocal,
    hr.phase_limit_perimeter_bound h hRφ hE
      (fun k ↦ hlocal _ (isCompact_closedBall _ _)),
    fun t ht ↦ h.phase_limit_vertical_translation
      (fun j ↦ zero_le_one.trans (hRφ j)) hE hlocal ht, ?_, ?_⟩
  · intro basis s r₀ hs hr₀ b hb hagree
    exact hr.limiting_phase_graph_minimality_ae h basis hs hr₀ hRφ hRtφ hE
      (hlocal _ (isCompact_closedBall _ _)) hb hagree
  · intro hg
    apply h.phase_limit_oneSided_cone hg (fun j ↦ zero_lt_one.trans_le (hRφ j)) hRtφ hE
    intro k
    exact hr.phaseIndicator_limit_of_solution_limit h _ hRtφ (by positivity) hE
      (hlocal _ (isCompact_closedBall _ _))

end SerrinEpigraph
