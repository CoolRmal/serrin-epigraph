module

public import SerrinEpigraph.RescaledPotential
public import SerrinEpigraph.RadialSlopeBound

/-!
# Vanishing volume of the intermediate positive phase
-/

public section

open MeasureTheory Metric Filter
open scoped Topology

namespace SerrinEpigraph

noncomputable section

/-- The positive phase below a specified level after spatial dilation. -/
@[expose] def transitionRegion {d : ℕ} (U : Space d → ℝ) (R a : ℝ) : Set (Space d) :=
  {x | 0 < U (R • x) ∧ U (R • x) ≤ a}

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ : ℝ}

/-- Transition regions of the zero extension are measurable. -/
theorem Hypotheses.measurableSet_transitionRegion (h : Hypotheses g u f κ) (R a : ℝ) :
    MeasurableSet (transitionRegion (zeroExtension g u) R a) := by
  have hc : Continuous (fun x : Space (m + 1) ↦ zeroExtension g u (R • x)) :=
    h.zeroExtension_continuous.comp (continuous_id.const_smul R)
  exact (isOpen_lt (continuous_const (y := (0 : ℝ))) hc).measurableSet.inter
    (isClosed_le hc continuous_const).measurableSet

/-- Dilation preserves local integrability of the positive-phase potential. -/
theorem RigidityHypotheses.integrableOn_dilated_phasePotential
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (R : ℝ)
    {K : Set (Space (m + 1))} (hK : IsCompact K) :
    IntegrableOn (fun x ↦ phasePotentialDensity f (zeroExtension g u) (R • x)) K := by
  have hc : Continuous (fun x : Space (m + 1) ↦ zeroExtension g u (R • x)) :=
    h.zeroExtension_continuous.comp (continuous_id.const_smul R)
  have hW : Continuous (fun x ↦ normalizedPotential f (zeroExtension g u (R • x))) :=
    h.normalizedPotential_continuousOn.comp_continuous hc
      (fun x ↦ ⟨h.zeroExtension_nonneg _, (hr.zeroExtension_lt_one _).le⟩)
  have hi := (hW.continuousOn.integrableOn_compact (μ := volume) hK).indicator
    (isOpen_lt (continuous_const (y := (0 : ℝ))) hc).measurableSet
  exact hi

/-- The potential controls the volume of every intermediate positive-phase region. -/
theorem RigidityHypotheses.transitionVolume_le_potential
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {a : ℝ} (ha : a ∈ Set.Ico (0 : ℝ) 1) (R r : ℝ) :
    volume.real (transitionRegion (zeroExtension g u) R a ∩ closedBall 0 r) ≤
      (∫ x in closedBall 0 r, phasePotentialDensity f (zeroExtension g u) (R • x)) /
        normalizedPotential f a := by
  have hw : 0 < normalizedPotential f a := hr.normalizedPotential_pos h ha.1 ha.2
  have hm := h.measurableSet_transitionRegion R a
  have hi : IntegrableOn ((transitionRegion (zeroExtension g u) R a).indicator
      (fun _ ↦ normalizedPotential f a)) (closedBall 0 r) :=
    (continuousOn_const.integrableOn_compact (isCompact_closedBall 0 r)).indicator hm
  have hle := integral_mono hi
    (hr.integrableOn_dilated_phasePotential h R (isCompact_closedBall 0 r)) (fun x ↦ ?_)
  · rw [integral_indicator hm, Measure.restrict_restrict hm, setIntegral_const,
      smul_eq_mul] at hle
    exact (le_div_iff₀ hw).mpr hle
  · by_cases hx : x ∈ transitionRegion (zeroExtension g u) R a
    · rw [Set.indicator_of_mem hx]
      have hpos := hx.1
      simp only [phasePotentialDensity, Set.indicator_apply, Set.mem_ofPred_eq, hpos, ite_true]
      exact hr.normalizedPotential_antitoneOn h
        ⟨h.zeroExtension_nonneg _, (hr.zeroExtension_lt_one _).le⟩ ⟨ha.1, ha.2.le⟩ hx.2
    · rw [Set.indicator_of_notMem hx]
      exact (hr.phasePotential_bounds h _).1

/-- Every fixed sub-equilibrium portion of the positive phase has vanishing rescaled volume. -/
theorem RigidityHypotheses.transitionVolume_tendsto_zero
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {a r : ℝ} (ha : a ∈ Set.Ico (0 : ℝ) 1) (hradius : 0 < r) :
    Tendsto (fun R : ℝ ↦ volume.real
      (transitionRegion (zeroExtension g u) R a ∩ closedBall 0 r)) atTop (𝓝 0) := by
  have ht := (hr.rescaledPotential_tendsto_zero h hradius).div_const
    (normalizedPotential f a)
  simp only [zero_div] at ht
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (fun _ ↦ measureReal_nonneg) (fun R ↦ hr.transitionVolume_le_potential h ha R r)

end

end SerrinEpigraph
