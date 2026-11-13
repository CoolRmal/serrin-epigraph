module

public import SerrinEpigraph.ZeroExtensionDifferentiability
public import SerrinEpigraph.QuadraticPotential

/-!
# Finite local energy of the whole-space positive phase

The additive energy constant remains an explicit parameter; no Bernoulli
normalization identity is assumed.
-/

public section

noncomputable section

open InnerProductSpace MeasureTheory

namespace SerrinEpigraph

/-- Energy density on the positive phase, with an explicit additive constant. -/
@[expose] def phaseEnergyDensity {d : ℕ} (f : ℝ → ℝ) (c : ℝ) (v : Space d → ℝ) :
    Space d → ℝ :=
  {x | 0 < v x}.indicator (fun x ↦ ‖gradient v x‖ ^ 2 / 2 + normalizedPotential f (v x) + c)

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ : ℝ}

/-- The solution takes values in the closed normalized range up to the boundary. -/
theorem RigidityHypotheses.solution_mem_Icc_closure (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) {x : Space (m + 1)} (hx : x ∈ closure (epigraph g)) :
    u x ∈ Set.Icc (0 : ℝ) 1 := by
  rw [← h.zeroExtension_eqOn_closure hx]
  exact ⟨h.zeroExtension_nonneg x, (hr.zeroExtension_lt_one x).le⟩

/-- The squared gradient of the extension can be written using the continuous closed-domain gradient. -/
theorem Hypotheses.norm_gradient_zeroExtension_sq_eq (h : Hypotheses g u f κ) :
    (fun x ↦ ‖gradient (zeroExtension g u) x‖ ^ 2) =
      (epigraph g).indicator
        (fun x ↦ ‖gradientWithin u (closure (epigraph g)) x‖ ^ 2) := by
  funext x
  by_cases hx : x ∈ epigraph g
  · rw [h.gradient_zeroExtension hx, Set.indicator_of_mem hx]
    simp only [gradientWithin, gradient,
      fderivWithin_closure_eq_fderiv h.graph_contDiff.continuous hx]
  · rw [h.gradient_zeroExtension_of_notMem hx, Set.indicator_of_notMem hx]
    simp

/-- The squared gradient of the zero extension is integrable on every compact set. -/
theorem Hypotheses.integrableOn_norm_gradient_zeroExtension_sq (h : Hypotheses g u f κ)
    {K : Set (Space (m + 1))} (hK : IsCompact K) :
    IntegrableOn (fun x ↦ ‖gradient (zeroExtension g u) x‖ ^ 2) K := by
  rw [h.norm_gradient_zeroExtension_sq_eq]
  apply (integrableOn_indicator_iff (isOpen_epigraph h.graph_contDiff.continuous).measurableSet).mpr
  have hc : ContinuousOn (gradientWithin u (closure (epigraph g))) (closure (epigraph g)) :=
    (toDual ℝ (Space (m + 1))).symm.continuous.comp_continuousOn
      (h.solution_contDiffOn_closure.continuousOn_fderivWithin
        (uniqueDiffOn_closure_epigraph h.graph_contDiff.differentiable_one) le_rfl)
  have hi := ((hc.mono (Set.inter_subset_right (s := K))).norm.pow 2).integrableOn_compact (μ := volume)
    (hK.inter_right isClosed_closure)
  exact hi.mono_set (fun x hx ↦ ⟨hx.2, subset_closure hx.1⟩)

/-- The phase energy of the zero extension agrees with the interior energy extended by zero. -/
theorem Hypotheses.phaseEnergyDensity_zeroExtension (h : Hypotheses g u f κ) (c : ℝ) :
    phaseEnergyDensity f c (zeroExtension g u) =
      (epigraph g).indicator (fun x ↦ ‖gradientWithin u (closure (epigraph g)) x‖ ^ 2 / 2 +
        normalizedPotential f (u x) + c) := by
  funext x
  by_cases hx : x ∈ epigraph g
  · have hp := (h.zeroExtension_pos_iff x).mpr hx
    unfold phaseEnergyDensity
    rw [Set.indicator_of_mem (s := {z | 0 < zeroExtension g u z}) hp, Set.indicator_of_mem hx,
      h.gradient_zeroExtension hx, zeroExtension_of_mem hx]
    simp only [gradientWithin, gradient,
      fderivWithin_closure_eq_fderiv h.graph_contDiff.continuous hx]
  · have hp : x ∉ {z | 0 < zeroExtension g u z} := fun hp ↦ hx ((h.zeroExtension_pos_iff x).mp hp)
    simp only [phaseEnergyDensity, Set.indicator_of_notMem (s := {z | 0 < zeroExtension g u z}) hp, Set.indicator_of_notMem hx]

/-- Every compact subset of the ambient space has finite phase energy. -/
theorem RigidityHypotheses.integrableOn_phaseEnergy_zeroExtension
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (c : ℝ)
    {K : Set (Space (m + 1))} (hK : IsCompact K) :
    IntegrableOn (phaseEnergyDensity f c (zeroExtension g u)) K := by
  rw [h.phaseEnergyDensity_zeroExtension c]
  apply (integrableOn_indicator_iff (isOpen_epigraph h.graph_contDiff.continuous).measurableSet).mpr
  have hc : ContinuousOn (gradientWithin u (closure (epigraph g))) (closure (epigraph g)) :=
    (toDual ℝ (Space (m + 1))).symm.continuous.comp_continuousOn
      (h.solution_contDiffOn_closure.continuousOn_fderivWithin
        (uniqueDiffOn_closure_epigraph h.graph_contDiff.differentiable_one) le_rfl)
  have hW := h.normalizedPotential_continuousOn.comp
    h.solution_contDiffOn_closure.continuousOn (fun x hx ↦ hr.solution_mem_Icc_closure h hx)
  have hE := ((hc.norm.pow 2 |>.div_const 2).add hW).add (continuousOn_const (c := c))
  have hi := (hE.mono (Set.inter_subset_right (s := K))).integrableOn_compact (μ := volume)
    (hK.inter_right isClosed_closure)
  exact hi.mono_set (fun x hx ↦ ⟨hx.2, subset_closure hx.1⟩)

/-- Nonnegative energy offsets give a nonnegative phase energy density. -/
theorem RigidityHypotheses.phaseEnergy_zeroExtension_nonneg
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) {c : ℝ} (hc : 0 ≤ c)
    (x : Space (m + 1)) : 0 ≤ phaseEnergyDensity f c (zeroExtension g u) x := by
  rw [h.phaseEnergyDensity_zeroExtension c]
  by_cases hx : x ∈ epigraph g
  · rw [Set.indicator_of_mem hx]
    have hW := hr.normalizedPotential_nonneg h
      ⟨(h.positive x hx).le, (hr.solution_lt_one x hx).le⟩
    positivity
  · rw [Set.indicator_of_notMem hx]

/-- Whole-space phase energy restricts exactly to the original interior energy. -/
theorem Hypotheses.integral_phaseEnergy_zeroExtension (h : Hypotheses g u f κ)
    (c : ℝ) {K : Set (Space (m + 1))} (hK : IsCompact K) :
    (∫ x in K, phaseEnergyDensity f c (zeroExtension g u) x) =
      ∫ x in epigraph g ∩ K, ‖gradient u x‖ ^ 2 / 2 + normalizedPotential f (u x) + c := by
  have hΩ := (isOpen_epigraph h.graph_contDiff.continuous).measurableSet
  rw [h.phaseEnergyDensity_zeroExtension c, integral_indicator hΩ,
    Measure.restrict_restrict hΩ]
  apply setIntegral_congr_fun (hΩ.inter hK.measurableSet)
  intro x hx
  simp only [gradientWithin, gradient,
    fderivWithin_closure_eq_fderiv h.graph_contDiff.continuous hx.1]

end SerrinEpigraph
