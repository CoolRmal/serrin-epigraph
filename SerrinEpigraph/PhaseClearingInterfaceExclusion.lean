module

public import SerrinEpigraph.PhaseClearingRescaled
public import SerrinEpigraph.GluingCostIntegral
public import Mathlib.Topology.MetricSpace.Thickening

/-!
# Vanishing local energy excludes levels and free boundaries
-/

public section
noncomputable section

open Set Metric Filter MeasureTheory InnerProductSpace
open scoped Topology

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ : ℝ}

/-- Local energy vanishing on an open set excludes every fixed compact interval
of interior phase values on its compact subsets. -/
theorem RigidityHypotheses.eventually_no_interior_levels_of_energy_vanishes
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {T : ℕ → ℝ} (hT : ∀ j, 0 < T j) (hTt : Tendsto T atTop atTop)
    {Ω : Set (Space (m + 1))} (hΩ : IsOpen Ω)
    (henergy : ∀ L : Set (Space (m + 1)), IsCompact L → L ⊆ Ω →
      Tendsto (fun j ↦ ∫ x in L, rescaledPhaseEnergyDensity f (T j)
        (fun y ↦ zeroExtension g u (T j • y)) x) atTop (𝓝 0))
    {K : Set (Space (m + 1))} (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    {a b : ℝ} (ha : 0 < a) (hb : b < 1) :
    ∀ᶠ j in atTop, ∀ x ∈ K, zeroExtension g u (T j • x) ∉ Icc a b := by
  obtain ⟨ρ, C, hρ, hC, hbound⟩ := hr.exists_rescaled_level_energy_lower_bound h ha hb
  obtain ⟨r, hradius, hthick⟩ := hK.exists_cthickening_subset_open hΩ hKΩ
  let L := cthickening r K
  have hL : IsCompact L := hK.cthickening
  have hc : 0 < C * r ^ m := mul_pos hC (pow_pos hradius _)
  have hevent := (henergy L hL hthick).eventually (gt_mem_nhds hc)
  have hlarge : ∀ᶠ j in atTop, ρ ≤ T j * r := by
    filter_upwards [hTt.eventually (eventually_ge_atTop (ρ / r))] with j hj
    exact (div_le_iff₀ hradius).mp hj
  filter_upwards [hevent, hlarge] with j hj hjlarge
  intro x hx hval
  have hlo := hbound (T j) (hT j) x hval r hjlarge
  have hU : LocallyLipschitz (fun y ↦ zeroExtension g u (T j • y)) :=
    h.zeroExtension_locallyLipschitz.comp (lipschitzWith_smul (T j)).locallyLipschitz
  have hUv (y : Space (m + 1)) : zeroExtension g u (T j • y) ∈ Icc (0 : ℝ) 1 :=
    ⟨h.zeroExtension_nonneg _, (hr.zeroExtension_lt_one _).le⟩
  have hmono := setIntegral_mono_set (h.integrableOn_rescaledPhaseEnergy hU hUv (T j) hL)
    (Eventually.of_forall (hr.rescaledPhaseEnergyDensity_nonneg h (hT j).le hUv))
    (Eventually.of_forall (closedBall_subset_cthickening hx r))
  exact (not_lt_of_ge (hlo.trans hmono)) hj

/-- Local energy vanishing excludes the entire rescaled free boundary on every
compact subset, without assuming any regularity of a limiting free boundary. -/
theorem RigidityHypotheses.eventually_no_freeBoundary_of_energy_vanishes
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {T : ℕ → ℝ} (hT : ∀ j, 0 < T j) (hTt : Tendsto T atTop atTop)
    {Ω : Set (Space (m + 1))} (hΩ : IsOpen Ω)
    (henergy : ∀ L : Set (Space (m + 1)), IsCompact L → L ⊆ Ω →
      Tendsto (fun j ↦ ∫ x in L, rescaledPhaseEnergyDensity f (T j)
        (fun y ↦ zeroExtension g u (T j • y)) x) atTop (𝓝 0))
    {K : Set (Space (m + 1))} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∀ᶠ j in atTop, ∀ x ∈ K, T j • x ∉ frontier (epigraph g) := by
  obtain ⟨ρ, C, hρ, hC, hbound⟩ := hr.exists_rescaled_freeBoundary_energy_lower_bound h
  obtain ⟨r, hradius, hthick⟩ := hK.exists_cthickening_subset_open hΩ hKΩ
  let L := cthickening r K
  have hL : IsCompact L := hK.cthickening
  have hc : 0 < C * r ^ m := mul_pos hC (pow_pos hradius _)
  have hevent := (henergy L hL hthick).eventually (gt_mem_nhds hc)
  have hlarge : ∀ᶠ j in atTop, ρ ≤ T j * r := by
    filter_upwards [hTt.eventually (eventually_ge_atTop (ρ / r))] with j hj
    exact (div_le_iff₀ hradius).mp hj
  filter_upwards [hevent, hlarge] with j hj hjlarge
  intro x hx hval
  have hlo := hbound (T j) (hT j) x hval r hjlarge
  have hU : LocallyLipschitz (fun y ↦ zeroExtension g u (T j • y)) :=
    h.zeroExtension_locallyLipschitz.comp (lipschitzWith_smul (T j)).locallyLipschitz
  have hUv (y : Space (m + 1)) : zeroExtension g u (T j • y) ∈ Icc (0 : ℝ) 1 :=
    ⟨h.zeroExtension_nonneg _, (hr.zeroExtension_lt_one _).le⟩
  have hmono := setIntegral_mono_set (h.integrableOn_rescaledPhaseEnergy hU hUv (T j) hL)
    (Eventually.of_forall (hr.rescaledPhaseEnergyDensity_nonneg h (hT j).le hUv))
    (Eventually.of_forall (closedBall_subset_cthickening hx r))
  exact (not_lt_of_ge (hlo.trans hmono)) hj

end SerrinEpigraph
