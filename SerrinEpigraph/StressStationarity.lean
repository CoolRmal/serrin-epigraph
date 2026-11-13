module

public import SerrinEpigraph.ShiftedStressFlux
public import SerrinEpigraph.PhaseEnergy
public import SerrinEpigraph.PerimeterLowerSemicontinuity

/-!
# Stationarity under compact spatial variations
-/

public section

noncomputable section

open Set MeasureTheory InnerProductSpace Filter
open scoped Topology

namespace SerrinEpigraph

/-- Integrable functions on an epigraph are recovered by raising its boundary
through heights tending down to zero. -/
theorem tendsto_integral_shifted_epigraph {d : ℕ} {g : Space d → ℝ}
    (hg : Continuous g) {v : Space (d + 1) → ℝ} (hi : IntegrableOn v (epigraph g)) :
    Tendsto (fun j : ℕ ↦ ∫ x in epigraph (fun y ↦ g y + 1 / (j + 1 : ℝ)), v x)
      atTop (𝓝 (∫ x in epigraph g, v x)) := by
  let E := fun j : ℕ ↦ epigraph (fun y ↦ g y + 1 / (j + 1 : ℝ))
  have hE (j : ℕ) : MeasurableSet (E j) :=
    (isOpen_epigraph (show Continuous (fun y ↦ g y + 1 / (j + 1 : ℝ)) from
      hg.add continuous_const)).measurableSet
  have hmono : Monotone E := by
    intro i j hij x hx
    have hdiv : 1 / (j + 1 : ℝ) ≤ 1 / (i + 1 : ℝ) := by
      apply one_div_le_one_div_of_le
      · positivity
      · exact_mod_cast Nat.add_le_add_right hij 1
    change g (horizontal x) + 1 / (i + 1 : ℝ) < x (Fin.last d) at hx
    change g (horizontal x) + 1 / (j + 1 : ℝ) < x (Fin.last d)
    linarith
  have hUnion : (⋃ j, E j) = epigraph g := by
    ext x
    constructor
    · intro hx
      obtain ⟨j, hj⟩ := mem_iUnion.mp hx
      exact closure_shifted_epigraph_subset hg (by positivity) (subset_closure hj)
    · intro hx
      change g (horizontal x) < x (Fin.last d) at hx
      have ht : Tendsto (fun j : ℕ ↦ 1 / (j + 1 : ℝ)) atTop (𝓝 (0 : ℝ)) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      obtain ⟨j, hj⟩ := (ht.eventually (eventually_lt_nhds (sub_pos.mpr hx))).exists
      exact mem_iUnion.mpr ⟨j, by change g (horizontal x) + _ < _; linarith⟩
  have hlim := tendsto_setIntegral_of_monotone hE hmono (hUnion ▸ hi)
  simpa only [hUnion, E] using hlim

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ : ℝ}

/-- The solution gradient interpreted within the closed epigraph is continuous there. -/
theorem Hypotheses.closed_gradient_continuousOn (h : Hypotheses g u f κ) :
    ContinuousOn (gradientWithin u (closure (epigraph g))) (closure (epigraph g)) :=
  (toDual ℝ (Space (m + 1))).symm.continuous.comp_continuousOn
    (h.solution_contDiffOn_closure.continuousOn_fderivWithin
      (uniqueDiffOn_closure_epigraph h.graph_contDiff.differentiable_one) le_rfl)

/-- Closed and ordinary gradients agree in the open epigraph. -/
theorem Hypotheses.closed_gradient_eq (h : Hypotheses g u f κ)
    {x : Space (m + 1)} (hx : x ∈ epigraph g) :
    gradientWithin u (closure (epigraph g)) x = gradient u x := by
  simp only [gradientWithin, gradient,
    fderivWithin_closure_eq_fderiv h.graph_contDiff.continuous hx]

/-- The stress flux with the derivative interpreted within the closed domain. -/
@[expose] def closedSolutionStress (g : Space m → ℝ) (u : Space (m + 1) → ℝ)
    (f : ℝ → ℝ) (X : Space (m + 1) → Space (m + 1)) (x : Space (m + 1)) :
    Space (m + 1) :=
  stressVector (normalizedPotential f (u x))
    (gradientWithin u (closure (epigraph g)) x) (X x)

/-- Stress has a continuous trace on the whole closed epigraph. -/
theorem RigidityHypotheses.closedSolutionStress_continuousOn
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {X : Space (m + 1) → Space (m + 1)} (hX : Continuous X) :
    ContinuousOn (closedSolutionStress g u f X) (closure (epigraph g)) := by
  have hp := h.closed_gradient_continuousOn
  have hW := h.normalizedPotential_continuousOn.comp
    h.solution_contDiffOn_closure.continuousOn (fun x hx ↦ hr.solution_mem_Icc_closure h hx)
  exact ((((hp.norm.pow 2).div_const 2).add hW).smul hX.continuousOn).sub
    ((hp.inner (𝕜 := ℝ) hX.continuousOn).smul hp)

/-- The normal stress flux through the zero boundary is zero, including its graph area factor. -/
theorem RigidityHypotheses.closedStress_graph_flux_zero
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (X : Space (m + 1) → Space (m + 1)) (y : Space m) :
    inner ℝ (point (gradient g y) (-1))
      (closedSolutionStress g u f X (point y (g y))) = 0 := by
  have hz := hr.solutionStress_boundary_flux_zero h y (X (point y (g y)))
  change inner ℝ
    ((Real.sqrt (1 + ‖gradient g y‖ ^ 2))⁻¹ • point (gradient g y) (-1))
    (closedSolutionStress g u f X (point y (g y))) = 0 at hz
  rw [real_inner_smul_left] at hz
  exact (mul_eq_zero.mp hz).resolve_left
    (inv_ne_zero ((Real.sqrt_pos.mpr (by positivity)).ne'))

/-- The graph stress integral depends continuously on its nonnegative vertical shift. -/
theorem RigidityHypotheses.closedStress_graph_flux_continuousOn
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {X : Space (m + 1) → Space (m + 1)} (hX : Continuous X) (hc : HasCompactSupport X) :
    ContinuousOn (fun t : ℝ ↦ ∫ y, inner ℝ (point (gradient g y) (-1))
      (closedSolutionStress g u f X (point y (g y + t)))) (Ici 0) := by
  let K := horizontal '' tsupport X
  have hK : IsCompact K := hc.image continuous_horizontal
  apply continuousOn_integral_of_compact_support (μ := volume) hK
  · have hnormal : Continuous (fun p : ℝ × Space m ↦ point (gradient g p.2) (-1)) :=
      pointContinuousLinearMap.continuous.comp
        (((toDual ℝ (Space m)).symm.continuous.comp
          (h.graph_contDiff.continuous_fderiv one_ne_zero)).comp continuous_snd |>.prodMk
          continuous_const)
    have hpoint : Continuous (fun p : ℝ × Space m ↦ point p.2 (g p.2 + p.1)) :=
      pointContinuousLinearMap.continuous.comp
        (continuous_snd.prodMk ((h.graph_contDiff.continuous.comp continuous_snd).add
          continuous_fst))
    exact hnormal.continuousOn.inner
      ((hr.closedSolutionStress_continuousOn h hX).comp hpoint.continuousOn
        (fun p hp ↦ point_mem_closure_epigraph (le_add_of_nonneg_right hp.1)))
  · intro t y _ hy
    have hx : point y (g y + t) ∉ tsupport X := fun hh ↦
      hy ⟨point y (g y + t), hh, horizontal_point _ _⟩
    simp [closedSolutionStress, stressVector, image_eq_zero_of_notMem_tsupport hx]

/-- Every compact C1 spatial variation satisfies the stress stationarity identity,
including variations that meet or move the free boundary. -/
theorem RigidityHypotheses.integral_stress_stationarity
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (basis : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1)))
    {X : Space (m + 1) → Space (m + 1)} (hX : ContDiff ℝ 1 X)
    (hc : HasCompactSupport X) :
    (∫ x in epigraph g,
      (‖gradient u x‖ ^ 2 / 2 + normalizedPotential f (u x)) * fieldDivergence basis X x -
        inner ℝ (gradient u x) (fderiv ℝ X x (gradient u x))) = 0 := by
  let p := gradientWithin u (closure (epigraph g))
  let v := fun x ↦ (‖p x‖ ^ 2 / 2 + normalizedPotential f (u x)) *
    fieldDivergence basis X x - inner ℝ (p x) (fderiv ℝ X x (p x))
  let w := fun x ↦ (‖gradient u x‖ ^ 2 / 2 + normalizedPotential f (u x)) *
    fieldDivergence basis X x - inner ℝ (gradient u x) (fderiv ℝ X x (gradient u x))
  have hEq : EqOn v w (epigraph g) := by
    intro x hx
    simp only [v, w, p, h.closed_gradient_eq hx]
  have hv : ContinuousOn v (closure (epigraph g)) := by
    have hp := h.closed_gradient_continuousOn
    have hW := h.normalizedPotential_continuousOn.comp
      h.solution_contDiffOn_closure.continuousOn (fun x hx ↦ hr.solution_mem_Icc_closure h hx)
    exact (((hp.norm.pow 2 |>.div_const 2).add hW).mul
      (fieldDivergence_continuous basis hX).continuousOn).sub
      (hp.inner (((hX.continuous_fderiv one_ne_zero).continuousOn).clm_apply hp))
  have hz (x : Space (m + 1)) (hx : x ∉ tsupport X) : v x = 0 := by
    simp [v, fieldDivergence_zero_of_notMem_tsupport basis X hx,
      fderiv_of_notMem_tsupport ℝ hx]
  have hi : IntegrableOn v (epigraph g) := by
    let K := tsupport X ∩ closure (epigraph g)
    have hK : IsCompact K := hc.inter_right isClosed_closure
    have hvi : IntegrableOn v K := (hv.mono inter_subset_right).integrableOn_compact hK
    have hiK : IntegrableOn ((epigraph g).indicator v) K :=
      hvi.indicator (isOpen_epigraph h.graph_contDiff.continuous).measurableSet
    apply (integrable_indicator_iff (isOpen_epigraph h.graph_contDiff.continuous).measurableSet).mp
    apply (integrableOn_iff_integrable_of_support_subset (s := K) ?_).mp hiK
    intro x hx
    have hxΩ : x ∈ epigraph g := by
      by_contra hn
      exact hx (indicator_of_notMem hn v)
    refine ⟨?_, subset_closure hxΩ⟩
    by_contra hn
    exact hx (by rw [indicator_of_mem hxΩ, hz x hn])
  have hiw : IntegrableOn w (epigraph g) := hi.congr_fun hEq
    (isOpen_epigraph h.graph_contDiff.continuous).measurableSet
  have hleft := tendsto_integral_shifted_epigraph h.graph_contDiff.continuous hiw
  have hright := (hr.closedStress_graph_flux_continuousOn h hX.continuous hc)
    0 (by simp : (0 : ℝ) ∈ Ici 0)
  have hε : Tendsto (fun j : ℕ ↦ 1 / (j + 1 : ℝ)) atTop (𝓝[Ici 0] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall (fun j ↦ by change 0 ≤ 1 / (j + 1 : ℝ); positivity)⟩
  have hright' := hright.tendsto.comp hε
  have hzero : (∫ y, inner ℝ (point (gradient g y) (-1))
      (closedSolutionStress g u f X (point y (g y + 0)))) = 0 := by
    simp only [add_zero, hr.closedStress_graph_flux_zero h X, integral_zero]
  rw [hzero] at hright'
  have hsame (j : ℕ) : (∫ x in epigraph (fun y ↦ g y + 1 / (j + 1 : ℝ)), w x) =
      ∫ y, inner ℝ (point (gradient g y) (-1))
        (closedSolutionStress g u f X (point y (g y + 1 / (j + 1 : ℝ)))) := by
    rw [show (∫ x in epigraph (fun y ↦ g y + 1 / (j + 1 : ℝ)), w x) =
      ∫ y, inner ℝ (point (gradient g y) (-1))
        (solutionStress u f X (point y (g y + 1 / (j + 1 : ℝ)))) from
          h.integral_shifted_stress_identity basis hX hc (by positivity)]
    apply integral_congr_ae
    exact Eventually.of_forall (fun y ↦ by
      have hx : point y (g y + 1 / (j + 1 : ℝ)) ∈ epigraph g := by
        simpa [epigraph] using (show (0 : ℝ) < 1 / (j + 1 : ℝ) by positivity)
      dsimp only
      simp only [closedSolutionStress, solutionStress, h.closed_gradient_eq hx])
  exact tendsto_nhds_unique hleft (hright'.congr' (Eventually.of_forall (fun j ↦ (hsame j).symm)))

end SerrinEpigraph
