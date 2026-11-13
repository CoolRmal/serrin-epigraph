module

public import SerrinEpigraph.StressEnergy
public import SerrinEpigraph.GraphLocalDivergence

/-!
# Stress flux on epigraphs shifted into the solution domain
-/

public section

noncomputable section

open Set MeasureTheory InnerProductSpace
open scoped ContDiff

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ : ℝ}

/-- The potential is C1 on the positive solution range. -/
theorem Hypotheses.normalizedPotential_contDiffOn_positive (h : Hypotheses g u f κ) :
    ContDiffOn ℝ 1 (normalizedPotential f) (Ioi 0) := by
  rw [show (1 : ℕ∞ω) = 0 + 1 from rfl,
    contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
  refine ⟨fun s hs ↦ (h.normalizedPotential_hasDerivAt hs).differentiableAt.differentiableWithinAt,
    by simp, ?_⟩
  rw [contDiffOn_zero]
  apply (h.reaction_contDiffOn.continuousOn.mono Ioi_subset_Ici_self).neg.congr
  intro s hs
  exact h.normalizedPotential_deriv hs

/-- The stress flux is C1 in the interior under the original C2 solution hypothesis. -/
theorem Hypotheses.solutionStress_contDiffOn (h : Hypotheses g u f κ)
    {X : Space (m + 1) → Space (m + 1)} (hX : ContDiff ℝ 1 X) :
    ContDiffOn ℝ 1 (solutionStress u f X) (epigraph g) := by
  have hg : ContDiffOn ℝ 1 (gradient u) (epigraph g) :=
    (toDual ℝ (Space (m + 1))).symm.contDiff.comp_contDiffOn
      (h.solution_contDiffOn.fderiv_of_isOpen
        (isOpen_epigraph h.graph_contDiff.continuous) (m := 1) (by norm_num))
  have hW := h.normalizedPotential_contDiffOn_positive.comp
    (h.solution_contDiffOn.of_le (by norm_num : (1 : ℕ∞ω) ≤ 2)) h.positive
  exact ((((hg.norm_sq (𝕜 := ℝ)).div_const 2).add hW).smul hX.contDiffOn).sub
    ((hg.inner (𝕜 := ℝ) hX.contDiffOn).smul hg)

/-- Stress flux vanishes off the support of the spatial test. -/
theorem tsupport_solutionStress_subset {d : ℕ} (v : Space d → ℝ) (f : ℝ → ℝ)
    (X : Space d → Space d) : tsupport (solutionStress v f X) ⊆ tsupport X := by
  apply closure_minimal _ (isClosed_tsupport X)
  intro x hx
  by_contra hn
  exact hx (by simp [solutionStress, stressVector, image_eq_zero_of_notMem_tsupport hn])

/-- The closed epigraph shifted up by a positive amount lies in the original open epigraph. -/
theorem closure_shifted_epigraph_subset {g : Space m → ℝ} (hg : Continuous g)
    {ε : ℝ} (hε : 0 < ε) : closure (epigraph (fun y ↦ g y + ε)) ⊆ epigraph g := by
  have hb : Continuous (fun y ↦ g y + ε) := hg.add continuous_const
  rw [closure_epigraph hb]
  intro x hx
  change g (horizontal x) + ε ≤ x (Fin.last m) at hx
  change g (horizontal x) < x (Fin.last m)
  linarith

/-- Integration of the PDE stress identity over an upward shifted epigraph gives
the exact flux on that graph, with no C2 boundary assumption. -/
theorem Hypotheses.integral_shifted_stress_identity (h : Hypotheses g u f κ)
    (basis : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1)))
    {X : Space (m + 1) → Space (m + 1)} (hX : ContDiff ℝ 1 X)
    (hc : HasCompactSupport X) {ε : ℝ} (hε : 0 < ε) :
    (∫ x in epigraph (fun y ↦ g y + ε),
      (‖gradient u x‖ ^ 2 / 2 + normalizedPotential f (u x)) * fieldDivergence basis X x -
        inner ℝ (gradient u x) (fderiv ℝ X x (gradient u x))) =
      ∫ y, inner ℝ (point (gradient g y) (-1))
        (solutionStress u f X (point y (g y + ε))) := by
  have hs := closure_shifted_epigraph_subset h.graph_contDiff.continuous hε
  have hb := h.graph_contDiff.add (contDiff_const (c := ε))
  have hFc : HasCompactSupport (solutionStress u f X) :=
    hc.of_isClosed_subset (isClosed_tsupport _) (tsupport_solutionStress_subset u f X)
  have hGauss := integral_epigraph_divergence_of_contDiffOn basis hb
    (isOpen_epigraph h.graph_contDiff.continuous) (h.solutionStress_contDiffOn hX) hFc
    (fun _ hx ↦ hs hx.1)
  have hgrad : gradient (fun y ↦ g y + ε) = gradient g := by
    funext y
    simp only [gradient, fderiv_add_const]
  rw [hgrad] at hGauss
  rw [← hGauss]
  apply setIntegral_congr_fun (isOpen_epigraph hb.continuous).measurableSet
  intro x hx
  exact (h.solutionStress_divergence basis (hs (subset_closure hx))
    (hX.differentiable_one x)).symm

end SerrinEpigraph
