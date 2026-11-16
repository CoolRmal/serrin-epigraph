module

public import SerrinEpigraph.PhysicalTranslationPhase
public import SerrinEpigraph.CauchyEnergy

/-!
# Energy convergence for physical translation limits

Strong gradient convergence and almost-everywhere agreement of the phases
control the kinetic and potential parts separately.
-/

public section

noncomputable section

open Set MeasureTheory Filter Metric InnerProductSpace
open scoped Topology

namespace SerrinEpigraph

/-- On a compact set, vanishing squared norm implies vanishing integral norm. -/
theorem integral_norm_tendsto_zero_of_square_tendsto_zero
    {d k : ℕ} {F : ℕ → Space d → Space k} {K : Set (Space d)} (hK : IsCompact K)
    (hi : ∀ j, IntegrableOn (fun x ↦ ‖F j x‖ ^ 2) K)
    (ht : Tendsto (fun j ↦ ∫ x in K, ‖F j x‖ ^ 2) atTop (𝓝 0)) :
    Tendsto (fun j ↦ ∫ x in K, ‖F j x‖) atTop (𝓝 0) := by
  have hb : IntegrableOn (fun _ : Space d ↦ (1 : ℝ) ^ 2) K :=
    continuousOn_const.integrableOn_compact hK
  have hbound := ((Real.continuous_sqrt.tendsto 0).comp ht).mul_const
    (Real.sqrt (∫ _x in K, (1 : ℝ) ^ 2))
  simp only [Real.sqrt_zero, zero_mul] at hbound
  apply squeeze_zero_norm (fun j ↦ ?_) hbound
  simpa only [mul_one, Real.norm_eq_abs, Function.comp_def] using abs_integral_mul_le_sqrt (hi j) hb

/-- Physical translation gradients also converge in local integral norm. -/
theorem RigidityHypotheses.physical_translation_gradient_integral_norm_tendsto
    {m : ℕ} {g : Space m → ℝ} {u V : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {p : ℕ → Space (m + 1)} (hV : LipschitzWith ⟨κ, h.kappa_pos.le⟩ V)
    (hval : ∀ x, V x ∈ Icc 0 1)
    (hlim : ∀ K : Set (Space (m + 1)), IsCompact K →
      TendstoUniformlyOn (fun j x ↦ zeroExtension g u (p j + x)) V atTop K)
    {K : Set (Space (m + 1))} (hK : IsCompact K) :
    Tendsto (fun j ↦ ∫ x in K,
      ‖gradient (zeroExtension g u) (p j + x) - gradient V x‖) atTop (𝓝 0) := by
  apply integral_norm_tendsto_zero_of_square_tendsto_zero hK ?_
    (hr.physical_translation_gradient_tendsto h hV hval hlim hK)
  intro j
  have hlip : LipschitzWith ⟨κ, h.kappa_pos.le⟩
      (fun x ↦ zeroExtension g u (p j + x)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_add_left] using
      (hr.zeroExtension_lipschitzWith h).dist_le_mul (p j + x) (p j + y)
  simpa only [gradient, fderiv_comp_add_left] using
    integrableOn_gradient_sub_sq_of_lipschitz hlip hV hK

/-- Bounded continuous observables restricted to the actual positive phase
converge in local integral norm under physical translation. -/
theorem RigidityHypotheses.physical_translation_phase_observable_tendsto
    {m : ℕ} {g : Space m → ℝ} {u V : Space (m + 1) → ℝ} {f A : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {p : ℕ → Space (m + 1)} (hV : LipschitzWith ⟨κ, h.kappa_pos.le⟩ V)
    (hval : ∀ x, V x ∈ Icc 0 1)
    (hlim : ∀ K : Set (Space (m + 1)), IsCompact K →
      TendstoUniformlyOn (fun j x ↦ zeroExtension g u (p j + x)) V atTop K)
    (hA : ContinuousOn A (Icc 0 1)) {K : Set (Space (m + 1))} (hK : IsCompact K) :
    Tendsto (fun j ↦ ∫ x in K,
      ‖{y | 0 < zeroExtension g u (p j + y)}.indicator
          (fun y ↦ A (zeroExtension g u (p j + y))) x -
        {y | 0 < V y}.indicator (fun y ↦ A (V y)) x‖) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hA
  have hrange (j : ℕ) (x : Space (m + 1)) : zeroExtension g u (p j + x) ∈ Icc 0 1 :=
    ⟨h.zeroExtension_nonneg _, (hr.zeroExtension_lt_one _).le⟩
  have hU (j : ℕ) : Continuous (fun x ↦ zeroExtension g u (p j + x)) :=
    h.zeroExtension_continuous.comp (continuous_const.add continuous_id)
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC _ (hval 0))
  have hbound (w : Space (m + 1) → ℝ) (hw : ∀ x, w x ∈ Icc 0 1) (x : Space (m + 1)) :
      ‖{y | 0 < w y}.indicator (fun y ↦ A (w y)) x‖ ≤ C := by
    by_cases hx : 0 < w x
    · rw [indicator_of_mem (s := {y | 0 < w y}) hx]
      exact hC _ (hw x)
    · rw [indicator_of_notMem (s := {y | 0 < w y}) hx, norm_zero]
      exact hC0
  have ht : Tendsto (fun j ↦ ∫ x in K,
      ‖{y | 0 < zeroExtension g u (p j + y)}.indicator
          (fun y ↦ A (zeroExtension g u (p j + y))) x -
        {y | 0 < V y}.indicator (fun y ↦ A (V y)) x‖) atTop
      (𝓝 (∫ _x in K, (0 : ℝ))) := by
    apply tendsto_integral_of_dominated_convergence (fun _ ↦ 2 * C)
    · intro j
      exact (((hA.comp_continuous (hU j) (hrange j)).measurable.indicator
        (isOpen_lt continuous_const (hU j)).measurableSet).sub
        ((hA.comp_continuous hV.continuous hval).measurable.indicator
          (isOpen_lt continuous_const hV.continuous).measurableSet)).norm.aestronglyMeasurable
    · exact continuousOn_const.integrableOn_compact hK
    · intro j
      filter_upwards with x
      rw [norm_norm]
      exact (norm_sub_le _ _).trans (by linarith [hbound _ (hrange j) x, hbound V hval x])
    · filter_upwards [ae_restrict_of_ae
        (hr.physical_translation_phase_eventually_iff h hV hval hlim)] with x hx
      have hpoint := (hlim {x} isCompact_singleton).tendsto_at (mem_singleton x)
      have hp : Tendsto (fun j ↦ A (zeroExtension g u (p j + x))) atTop (𝓝 (A (V x))) :=
        ((hA _ (hval x)).tendsto).comp (tendsto_nhdsWithin_iff.mpr
          ⟨hpoint, Eventually.of_forall (fun j ↦ hrange j x)⟩)
      by_cases hpos : 0 < V x
      · apply (show Tendsto (fun j ↦ ‖A (zeroExtension g u (p j + x)) - A (V x)‖)
          atTop (𝓝 0) from by
            simpa only [sub_self, norm_zero] using
              (hp.sub (tendsto_const_nhds (x := A (V x)))).norm).congr'
        filter_upwards [hx] with j hj
        rw [indicator_of_mem (s := {y | 0 < V y}) hpos,
          indicator_of_mem (s := {y | 0 < zeroExtension g u (p j + y)}) (hj.mpr hpos)]
      · apply tendsto_const_nhds.congr'
        filter_upwards [hx] with j hj
        simp only [indicator_of_notMem (s := {y | 0 < V y}) hpos,
          indicator_of_notMem (s := {y | 0 < zeroExtension g u (p j + y)})
            (fun hp ↦ hpos (hj.mp hp)),
          sub_self, norm_zero]
  simpa only [integral_zero] using ht

end SerrinEpigraph
