module

public import SerrinEpigraph.LimitingGraphComparison
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# One-sided cone constraints on the measurable phase limit
-/

public section

open Set MeasureTheory Filter Metric
open scoped Topology ENNReal

namespace SerrinEpigraph

/-- Pointwise eventual values on a region are inherited almost everywhere by an L1 limit. -/
theorem ae_eq_of_integral_limit_of_eventually_eq {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {F : ℕ → X → ℝ} {z : X → ℝ}
    (hF : ∀ j, Integrable (F j) μ) (hz : Integrable z μ)
    (ht : Tendsto (fun j ↦ ∫ x, ‖F j x - z x‖ ∂μ) atTop (𝓝 0))
    {P : X → Prop} {c : ℝ} (hc : ∀ x, P x → ∀ᶠ j in atTop, F j x = c) :
    ∀ᵐ x ∂μ, P x → z x = c := by
  have hLp : Tendsto (fun j ↦ eLpNorm (F j - z) 1 μ) atTop (𝓝 0) := by
    have he (j : ℕ) : eLpNorm (F j - z) 1 μ =
        ENNReal.ofReal (∫ x, ‖F j x - z x‖ ∂μ) := by
      rw [eLpNorm_one_eq_lintegral_enorm ((hF j).sub hz).aestronglyMeasurable,
        ← ofReal_integral_norm_eq_lintegral_enorm ((hF j).sub hz)]
      rfl
    simpa only [he, ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal ht
  have hmeasure := tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) hLp
  obtain ⟨φ, hφ, hpoint⟩ := hmeasure.exists_seq_tendsto_ae
  filter_upwards [hpoint] with x hx
  intro hPx
  have he : ∀ᶠ j in atTop, F (φ j) x = c := hφ.tendsto_atTop.eventually (hc x hPx)
  exact tendsto_nhds_unique hx (tendsto_const_nhds.congr' (Filter.EventuallyEq.symm he))

/-- Below the homogeneous lower cone, the limiting phase is absent almost everywhere. -/
theorem Hypotheses.phase_limit_lower_cone
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ C : ℝ}
    (h : Hypotheses g u f κ) (hg : ∀ y, -C * (1 + ‖y‖) ≤ g y)
    {R : ℕ → ℝ} (hR : ∀ j, 0 < R j) (hRt : Tendsto R atTop atTop)
    {E K : Set (Space (m + 1))} (hE : MeasurableSet E) (hK : IsCompact K)
    (ht : Tendsto (fun j ↦ ∫ x in K,
      ‖positivePhaseIndicator (zeroExtension g u) (R j • x) -
        E.indicator (fun _ ↦ (1 : ℝ)) x‖) atTop (𝓝 0)) :
    ∀ᵐ x ∂volume.restrict K, x (Fin.last m) < -C * ‖horizontal x‖ → x ∉ E := by
  let F := fun j x ↦ positivePhaseIndicator (zeroExtension g u) (R j • x)
  have hF (j : ℕ) : IntegrableOn (F j) K := by
    have hc := h.zeroExtension_continuous.comp (continuous_id.const_smul (R j))
    exact (continuousOn_const.integrableOn_compact hK).indicator
      (isOpen_lt (continuous_const (y := (0 : ℝ))) hc).measurableSet
  have hz : IntegrableOn (E.indicator (fun _ : Space (m + 1) ↦ (1 : ℝ))) K :=
    (continuousOn_const.integrableOn_compact hK).indicator hE
  have he := ae_eq_of_integral_limit_of_eventually_eq (volume.restrict K) hF hz ht
    (P := fun x ↦ x (Fin.last m) < -C * ‖horizontal x‖) (c := 0) (fun x hx ↦ by
      have hlim : Tendsto (fun j ↦ -C * (1 / R j + ‖horizontal x‖)) atTop
          (𝓝 (-C * ‖horizontal x‖)) := by
        simpa only [one_div, Function.comp_def, zero_add] using
          ((tendsto_inv_atTop_zero.comp hRt).add_const ‖horizontal x‖).const_mul (-C)
      filter_upwards [hlim.eventually (lt_mem_nhds hx)] with j hj
      have hout : R j • x ∉ epigraph g := by
        rw [← mem_epigraph_rescaledGraph_iff (hR j)]
        exact not_lt_of_ge ((rescaledGraph_lower_bound hg (hR j) (horizontal x)).trans'
          hj.le)
      have hn : ¬0 < zeroExtension g u (R j • x) := fun hp ↦ hout ((h.zeroExtension_pos_iff _).mp hp)
      exact indicator_of_notMem (s := {y | 0 < zeroExtension g u y}) hn _)
  filter_upwards [he] with x hx
  intro hbelow hmem
  have heq := hx hbelow
  simp only [indicator_of_mem hmem] at heq
  norm_num at heq

/-- Above the homogeneous upper cone, the limiting phase is present almost everywhere. -/
theorem Hypotheses.phase_limit_upper_cone
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ C : ℝ}
    (h : Hypotheses g u f κ) (hg : ∀ y, g y ≤ C * (1 + ‖y‖))
    {R : ℕ → ℝ} (hR : ∀ j, 0 < R j) (hRt : Tendsto R atTop atTop)
    {E K : Set (Space (m + 1))} (hE : MeasurableSet E) (hK : IsCompact K)
    (ht : Tendsto (fun j ↦ ∫ x in K,
      ‖positivePhaseIndicator (zeroExtension g u) (R j • x) -
        E.indicator (fun _ ↦ (1 : ℝ)) x‖) atTop (𝓝 0)) :
    ∀ᵐ x ∂volume.restrict K, C * ‖horizontal x‖ < x (Fin.last m) → x ∈ E := by
  let F := fun j x ↦ positivePhaseIndicator (zeroExtension g u) (R j • x)
  have hF (j : ℕ) : IntegrableOn (F j) K := by
    have hc := h.zeroExtension_continuous.comp (continuous_id.const_smul (R j))
    exact (continuousOn_const.integrableOn_compact hK).indicator
      (isOpen_lt (continuous_const (y := (0 : ℝ))) hc).measurableSet
  have hz : IntegrableOn (E.indicator (fun _ : Space (m + 1) ↦ (1 : ℝ))) K :=
    (continuousOn_const.integrableOn_compact hK).indicator hE
  have he := ae_eq_of_integral_limit_of_eventually_eq (volume.restrict K) hF hz ht
    (P := fun x ↦ C * ‖horizontal x‖ < x (Fin.last m)) (c := 1) (fun x hx ↦ by
      have hlim : Tendsto (fun j ↦ C * (1 / R j + ‖horizontal x‖)) atTop
          (𝓝 (C * ‖horizontal x‖)) := by
        simpa only [one_div, Function.comp_def, zero_add] using
          ((tendsto_inv_atTop_zero.comp hRt).add_const ‖horizontal x‖).const_mul C
      filter_upwards [hlim.eventually (gt_mem_nhds hx)] with j hj
      have hin : R j • x ∈ epigraph g := by
        rw [← mem_epigraph_rescaledGraph_iff (hR j)]
        exact (rescaledGraph_upper_bound hg (hR j) (horizontal x)).trans_lt hj
      have hp : 0 < zeroExtension g u (R j • x) := (h.zeroExtension_pos_iff _).mpr hin
      exact indicator_of_mem (s := {y | 0 < zeroExtension g u y}) hp _)
  filter_upwards [he] with x hx
  intro habove
  by_contra hnot
  have heq := hx habove
  simp only [indicator_of_notMem hnot] at heq
  norm_num at heq

/-- Either one-sided graph bound passes to the actual measurable phase limit as
a global almost-everywhere cone inclusion, without assuming a pointwise graph limit. -/
theorem Hypotheses.phase_limit_oneSided_cone
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (h : Hypotheses g u f κ) (hg : HasOneSidedLinearBound g)
    {R : ℕ → ℝ} (hR : ∀ j, 0 < R j) (hRt : Tendsto R atTop atTop)
    {E : Set (Space (m + 1))} (hE : MeasurableSet E)
    (ht : ∀ k : ℕ, Tendsto (fun j ↦ ∫ x in closedBall 0 (k + 1 : ℝ),
      ‖positivePhaseIndicator (zeroExtension g u) (R j • x) -
        E.indicator (fun _ ↦ (1 : ℝ)) x‖) atTop (𝓝 0)) :
    (∃ C : ℝ, 0 < C ∧ ∀ᵐ x ∂volume, x ∈ E → -C * ‖horizontal x‖ ≤ x (Fin.last m)) ∨
    (∃ C : ℝ, 0 < C ∧ ∀ᵐ x ∂volume, C * ‖horizontal x‖ < x (Fin.last m) → x ∈ E) := by
  have hcover (x : Space (m + 1)) : ∃ k : ℕ, x ∈ closedBall 0 (k + 1 : ℝ) := by
    obtain ⟨k, hk⟩ := exists_nat_gt ‖x‖
    refine ⟨k, ?_⟩
    rw [mem_closedBall, dist_zero_right]
    linarith
  rcases hg with ⟨C, hC, hg⟩ | ⟨C, hC, hg⟩
  · left
    refine ⟨C, hC, ?_⟩
    have ha (k : ℕ) : ∀ᵐ x ∂volume, x ∈ closedBall 0 (k + 1 : ℝ) →
        x (Fin.last m) < -C * ‖horizontal x‖ → x ∉ E :=
      (ae_restrict_iff' measurableSet_closedBall).mp
        (h.phase_limit_lower_cone hg hR hRt hE (isCompact_closedBall _ _) (ht k))
    filter_upwards [ae_all_iff.mpr ha] with x hx
    obtain ⟨k, hk⟩ := hcover x
    intro hxE
    exact le_of_not_gt (fun hh ↦ hx k hk hh hxE)
  · right
    refine ⟨C, hC, ?_⟩
    have ha (k : ℕ) : ∀ᵐ x ∂volume, x ∈ closedBall 0 (k + 1 : ℝ) →
        C * ‖horizontal x‖ < x (Fin.last m) → x ∈ E :=
      (ae_restrict_iff' measurableSet_closedBall).mp
        (h.phase_limit_upper_cone hg hR hRt hE (isCompact_closedBall _ _) (ht k))
    filter_upwards [ae_all_iff.mpr ha] with x hx
    obtain ⟨k, hk⟩ := hcover x
    exact hx k hk

/-- The third target's one-sided hypothesis yields a genuine measurable phase
subsequence with a cone inclusion and convergence of the rescaled solutions. -/
theorem RigidityHypotheses.exists_phase_with_oneSided_cone
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hg : HasOneSidedLinearBound g) (R : ℕ → ℝ)
    (hR : ∀ j, 1 ≤ R j) (hRt : Tendsto R atTop atTop) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ E : Set (Space (m + 1)), MeasurableSet E ∧
      (∀ k : ℕ, Tendsto (fun j ↦ ∫ x in closedBall 0 (k + 1 : ℝ),
        ‖zeroExtension g u (R (φ j) • x) - E.indicator (fun _ ↦ (1 : ℝ)) x‖)
        atTop (𝓝 0)) ∧
      ((∃ C : ℝ, 0 < C ∧ ∀ᵐ x ∂volume,
          x ∈ E → -C * ‖horizontal x‖ ≤ x (Fin.last m)) ∨
        (∃ C : ℝ, 0 < C ∧ ∀ᵐ x ∂volume,
          C * ‖horizontal x‖ < x (Fin.last m) → x ∈ E)) := by
  obtain ⟨φ, hφ, E, hE, hlim⟩ :=
    hr.solution_and_phaseIndicator_measurable_limit h R hR hRt
  exact ⟨φ, hφ, E, hE, fun k ↦ (hlim k).2,
    h.phase_limit_oneSided_cone hg (fun j ↦ zero_lt_one.trans_le (hR (φ j)))
      (hRt.comp hφ.tendsto_atTop) hE (fun k ↦ (hlim k).1)⟩

end SerrinEpigraph
