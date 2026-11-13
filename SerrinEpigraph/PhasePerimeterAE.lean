module

public import SerrinEpigraph.LocalizedPerimeterComparison

/-!
# Phase comparison independent of null-set representatives
-/

public section

open Set MeasureTheory Metric Filter
open scoped Topology ENNReal

namespace SerrinEpigraph

/-- Equal phases almost everywhere have identical unit indicators almost everywhere. -/
theorem phaseIndicator_congr_ae {d : ℕ} {E D : Set (Space d)} (hED : E =ᵐ[volume] D) :
    E.indicator (fun _ ↦ (1 : ℝ)) =ᵐ[volume] D.indicator (fun _ ↦ (1 : ℝ)) := by
  filter_upwards [hED] with x hx
  by_cases hxE : x ∈ E
  · have hxD : x ∈ D := (Iff.of_eq hx).mp hxE
    simp only [indicator_of_mem hxE, indicator_of_mem hxD]
  · have hxD : x ∉ D := fun hh ↦ hxE ((Iff.of_eq hx).mpr hh)
    simp only [indicator_of_notMem hxE, indicator_of_notMem hxD]

/-- Variational perimeter depends on the phase only up to equality almost everywhere. -/
theorem variationalPerimeter_congr_ae {d : ℕ}
    (basis : OrthonormalBasis (Fin d) ℝ (Space d)) {E D : Set (Space d)}
    (hED : E =ᵐ[volume] D) (Ω : Set (Space d)) :
    variationalPerimeter basis E Ω = variationalPerimeter basis D Ω := by
  have he (F : Space d → Space d) :
      (∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence basis F x) =
      ∫ x, D.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence basis F x := by
    apply integral_congr_ae
    filter_upwards [phaseIndicator_congr_ae hED] with x hx
    rw [hx]
  simp only [variationalPerimeter, he]

/-- Graph-competitor minimality requires only almost-everywhere agreement in the
outer annulus, so it does not depend on which representative of the phase is chosen. -/
theorem RigidityHypotheses.limiting_phase_graph_minimality_ae
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (basis : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1)))
    {s r₀ : ℝ} (hs : 0 < s) (hr₀ : r₀ < s)
    {R : ℕ → ℝ} (hR : ∀ j, 1 ≤ R j) (hRt : Tendsto R atTop atTop)
    {E : Set (Space (m + 1))} (hE : MeasurableSet E)
    (hUlim : Tendsto (fun j ↦ ∫ x in closedBall 0 s,
      ‖zeroExtension g u (R j • x) - E.indicator (fun _ ↦ (1 : ℝ)) x‖) atTop (𝓝 0))
    {b : Space m → ℝ} (hb : ContDiff ℝ 1 b)
    (hagree : ∀ᵐ x ∂volume.restrict (ball 0 s \ closedBall 0 r₀),
      x ∈ E ↔ x ∈ epigraph b) :
    variationalPerimeter basis E (ball 0 s) ≤
      variationalPerimeter basis (epigraph b) (ball 0 s) := by
  let A := ball (0 : Space (m + 1)) s \ closedBall 0 r₀
  have hA : MeasurableSet A := measurableSet_ball.diff measurableSet_closedBall
  let D := (E \ A) ∪ (epigraph b ∩ A)
  have hD : MeasurableSet D := (hE.diff hA).union
    ((isOpen_epigraph hb.continuous).measurableSet.inter hA)
  have hED : E =ᵐ[volume] D := by
    have ha : ∀ᵐ x ∂volume, x ∈ A → (x ∈ E ↔ x ∈ epigraph b) :=
      (ae_restrict_iff' hA).mp hagree
    filter_upwards [ha] with x hx
    apply propext
    by_cases hxA : x ∈ A
    · simpa only [D, mem_union, Set.mem_sdiff, mem_inter_iff, hxA, not_true_eq_false,
        and_false, and_true, false_or] using hx hxA
    · simp only [D, mem_union, Set.mem_sdiff, mem_inter_iff, hxA, not_false_eq_true,
        and_true, and_false, or_false]
  have hlimD : Tendsto (fun j ↦ ∫ x in closedBall 0 s,
      ‖zeroExtension g u (R j • x) - D.indicator (fun _ ↦ (1 : ℝ)) x‖) atTop (𝓝 0) := by
    convert hUlim using 1
    funext j
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (phaseIndicator_congr_ae hED)] with x hx
    rw [hx]
  rw [variationalPerimeter_congr_ae basis hED]
  apply hr.limiting_phase_graph_minimality h basis hs hr₀ hR hRt hD hlimD hb
  intro x hx
  have hxA : x ∈ A := hx
  simp only [D, mem_union, Set.mem_sdiff, mem_inter_iff, hxA, not_true_eq_false,
    and_false, and_true, false_or]

end SerrinEpigraph
