module

public import SerrinEpigraph.TransitionVolume

/-!
# Local integral approximation by the positive-phase indicator
-/

public section

open MeasureTheory Metric Filter
open scoped Topology

namespace SerrinEpigraph

noncomputable section

/-- Indicator of the strictly positive phase, with real values. -/
@[expose] def positivePhaseIndicator {d : ℕ} (U : Space d → ℝ) : Space d → ℝ :=
  {x | 0 < U x}.indicator (fun _ ↦ 1)

/-- Absolute error from replacing a normalized function by its positive-phase indicator. -/
@[expose] def phaseIndicatorError {d : ℕ} (U : Space d → ℝ) (x : Space d) : ℝ :=
  |positivePhaseIndicator U x - U x|

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ : ℝ}

/-- The dilated indicator error is integrable on compact sets. -/
theorem Hypotheses.integrableOn_phaseIndicatorError (h : Hypotheses g u f κ) (R : ℝ)
    {K : Set (Space (m + 1))} (hK : IsCompact K) :
    IntegrableOn (fun x ↦ phaseIndicatorError (zeroExtension g u) (R • x)) K := by
  have hc : Continuous (fun x : Space (m + 1) ↦ zeroExtension g u (R • x)) :=
    h.zeroExtension_continuous.comp (continuous_id.const_smul R)
  have hi : IntegrableOn ({x | 0 < zeroExtension g u (R • x)}.indicator (fun _ ↦ (1 : ℝ))) K :=
    (continuousOn_const.integrableOn_compact hK).indicator
      (isOpen_lt (continuous_const (y := (0 : ℝ))) hc).measurableSet
  exact (hi.sub (hc.continuousOn.integrableOn_compact hK)).abs

/-- Splitting at a fixed level bounds the indicator error by transition volume and level deficit. -/
theorem RigidityHypotheses.integral_phaseIndicatorError_le
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {a : ℝ} (ha : a ∈ Set.Ico (0 : ℝ) 1) (R r : ℝ) :
    (∫ x in closedBall 0 r, phaseIndicatorError (zeroExtension g u) (R • x)) ≤
      volume.real (transitionRegion (zeroExtension g u) R a ∩ closedBall 0 r) +
        volume.real (closedBall (0 : Space (m + 1)) r) * (1 - a) := by
  have hi : IntegrableOn ((transitionRegion (zeroExtension g u) R a).indicator
      (fun _ ↦ (1 : ℝ))) (closedBall 0 r) :=
    (continuousOn_const.integrableOn_compact (isCompact_closedBall 0 r)).indicator
      (h.measurableSet_transitionRegion R a)
  have hj : IntegrableOn (fun _ : Space (m + 1) ↦ 1 - a) (closedBall 0 r) :=
    continuousOn_const.integrableOn_compact (isCompact_closedBall 0 r)
  have he := integral_mono (h.integrableOn_phaseIndicatorError R (isCompact_closedBall 0 r))
    (hi.add hj) (fun x ↦ ?_)
  · simp only [Pi.add_apply] at he
    rw [integral_add hi hj, integral_indicator (h.measurableSet_transitionRegion R a),
      Measure.restrict_restrict (h.measurableSet_transitionRegion R a), setIntegral_const,
      setIntegral_const, smul_eq_mul, smul_eq_mul, mul_one] at he
    exact he
  · simp only [Pi.add_apply]
    have h0 := h.zeroExtension_nonneg (R • x)
    have h1 := hr.zeroExtension_lt_one (R • x)
    by_cases hp : 0 < zeroExtension g u (R • x)
    · have heq : phaseIndicatorError (zeroExtension g u) (R • x) =
          1 - zeroExtension g u (R • x) := by
        simp [phaseIndicatorError, positivePhaseIndicator, hp, abs_of_pos (sub_pos.mpr h1)]
      rw [heq]
      by_cases hx : x ∈ transitionRegion (zeroExtension g u) R a
      · rw [Set.indicator_of_mem hx]
        linarith [ha.2]
      · rw [Set.indicator_of_notMem hx]
        have hh : a < zeroExtension g u (R • x) :=
          lt_of_not_ge (fun hh ↦ hx ⟨hp, hh⟩)
        linarith
    · have hz : zeroExtension g u (R • x) = 0 := le_antisymm (le_of_not_gt hp) h0
      have hx : x ∉ transitionRegion (zeroExtension g u) R a := fun hx ↦ hp hx.1
      rw [Set.indicator_of_notMem hx]
      simp only [phaseIndicatorError, positivePhaseIndicator, Set.indicator_apply,
        Set.mem_ofPred_eq, hz, lt_self_iff_false, ite_false, sub_zero, abs_zero, zero_add]
      exact sub_nonneg.mpr ha.2.le

/-- Dilated solutions approach their positive-phase indicators in local integral norm. -/
theorem RigidityHypotheses.phaseIndicatorError_tendsto_zero
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) {r : ℝ} (hradius : 0 < r) :
    Tendsto (fun R : ℝ ↦ ∫ x in closedBall 0 r,
      phaseIndicatorError (zeroExtension g u) (R • x)) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro b hb
    exact Eventually.of_forall (fun R ↦ hb.trans_le
      (integral_nonneg (fun x ↦ abs_nonneg _)))
  · intro ε hε
    let V := volume.real (closedBall (0 : Space (m + 1)) r)
    have hV : 0 ≤ V := measureReal_nonneg
    let δ := min (1 / 2 : ℝ) (ε / (2 * (V + 1)))
    have hδ : 0 < δ := lt_min (by norm_num) (div_pos hε (by positivity))
    have hδhalf : δ ≤ 1 / 2 := min_le_left _ _
    have hδsmall : δ * (2 * (V + 1)) ≤ ε :=
      (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
    have ha : 1 - δ ∈ Set.Ico (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    have ht := hr.transitionVolume_tendsto_zero h ha hradius
    have hev := ht.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 2 by positivity))
    filter_upwards [hev] with R hR
    have he := hr.integral_phaseIndicatorError_le h ha R r
    have hc : V * (1 - (1 - δ)) < ε / 2 := by
      nlinarith
    exact he.trans_lt (by change _ + V * (1 - (1 - δ)) < ε; linarith)

end

end SerrinEpigraph
