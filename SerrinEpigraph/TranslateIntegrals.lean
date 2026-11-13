module

public import SerrinEpigraph.LimitProfile
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Compact weighted integrals of vertical translates

Continuous functions of the bounded translated solution converge under integration
on every compact set. This includes both the solution and its reaction.
-/

public section

noncomputable section

open Filter MeasureTheory
open scoped Topology

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ : ℝ}

/-- Dominated convergence for a continuous observable of the translated solution, with a
continuous weight on a compact set. -/
theorem RigidityHypotheses.tendsto_integral_vertical_translate
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {K : Set (Space (m + 1))} (hK : IsCompact K) {φ : Space (m + 1) → ℝ}
    (hφ : ContinuousOn φ K) {A : ℝ → ℝ} (hA : ContinuousOn A (Set.Icc (0 : ℝ) 1)) :
    Tendsto (fun t : ℝ ↦ ∫ x in K, A (u (x + t • verticalDirection m)) * φ x) atTop
      (𝓝 (∫ x in K, A (hr.verticalLimitProfile h (horizontal x)) * φ x)) := by
  obtain ⟨T, hT⟩ := compact_eventually_in_epigraph h.graph_contDiff.continuous hK
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hA
  obtain ⟨D, hD⟩ := hK.exists_bound_of_continuousOn hφ
  have hrange (t : ℝ) (ht : T ≤ t) (x : Space (m + 1)) (hx : x ∈ K) :
      u (x + t • verticalDirection m) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨(h.positive _ (hT t ht x hx)).le, (hr.solution_lt_one _ (hT t ht x hx)).le⟩
  apply tendsto_integral_filter_of_dominated_convergence (fun _ ↦ |C| * |D|)
  · filter_upwards [eventually_ge_atTop T] with t ht
    have hu : ContinuousOn (fun x ↦ u (x + t • verticalDirection m)) K :=
      h.solution_contDiffOn.continuousOn.comp
        (continuous_id.add continuous_const).continuousOn (hT t ht)
    exact ((hA.comp hu (hrange t ht)).mul hφ).aestronglyMeasurable hK.measurableSet
  · filter_upwards [eventually_ge_atTop T] with t ht
    filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
    rw [norm_mul]
    exact mul_le_mul ((hC _ (hrange t ht x hx)).trans (le_abs_self C))
      ((hD x hx).trans (le_abs_self D)) (norm_nonneg _) (abs_nonneg _)
  · exact continuousOn_const.integrableOn_compact hK
  · filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
    have hspec := hr.verticalLimitProfile_spec h (horizontal x)
    have hwithin : Tendsto (fun t : ℝ ↦ u (x + t • verticalDirection m)) atTop
        (𝓝[Set.Icc (0 : ℝ) 1] (hr.verticalLimitProfile h (horizontal x))) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨hr.vertical_translates_tendsto h x, ?_⟩
      filter_upwards [eventually_ge_atTop T] with t ht
      exact hrange t ht x hx
    exact ((hA _ ⟨hspec.1.le, hspec.2.1⟩).tendsto.comp hwithin).mul tendsto_const_nhds

/-- The solution term converges against a continuous compact-domain test weight. -/
theorem RigidityHypotheses.tendsto_integral_solution_translate
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {K : Set (Space (m + 1))} (hK : IsCompact K) {φ : Space (m + 1) → ℝ}
    (hφ : ContinuousOn φ K) :
    Tendsto (fun t : ℝ ↦ ∫ x in K, u (x + t • verticalDirection m) * φ x) atTop
      (𝓝 (∫ x in K, hr.verticalLimitProfile h (horizontal x) * φ x)) :=
  hr.tendsto_integral_vertical_translate h hK hφ continuousOn_id

/-- The reaction term converges against a continuous compact-domain test weight. -/
theorem RigidityHypotheses.tendsto_integral_reaction_translate
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {K : Set (Space (m + 1))} (hK : IsCompact K) {φ : Space (m + 1) → ℝ}
    (hφ : ContinuousOn φ K) :
    Tendsto (fun t : ℝ ↦ ∫ x in K, f (u (x + t • verticalDirection m)) * φ x) atTop
      (𝓝 (∫ x in K, f (hr.verticalLimitProfile h (horizontal x)) * φ x)) :=
  hr.tendsto_integral_vertical_translate h hK hφ
    (h.reaction_contDiffOn.continuousOn.mono (fun _ hx ↦ hx.1))

end SerrinEpigraph
