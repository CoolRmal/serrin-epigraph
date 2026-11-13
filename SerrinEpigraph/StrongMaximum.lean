module

public import SerrinEpigraph.WeakBarrierComparison
public import SerrinEpigraph.Connectedness
public import SerrinEpigraph.StrongPositivity
public import SerrinEpigraph.WeakLinearization

/-!
# From local positivity to the strong maximum principle

The coefficient of the linearized equation is bounded only on compact interior balls. Local
positivity propagation then makes the positive set both relatively open and relatively closed.
-/

public section

open MeasureTheory InnerProductSpace Metric
open scoped Topology

namespace SerrinEpigraph

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

omit [MeasurableSpace E] [BorelSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Propagation on half-balls extends one positive value to a connected open domain. -/
theorem positive_of_halfBall_propagation {Ω : Set E} {v : E → ℝ}
    (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω) (hv : ContinuousOn v Ω)
    (hex : ∃ x ∈ Ω, 0 < v x)
    (hprop : ∀ (c : E) (R : ℝ), 0 < R → closedBall c R ⊆ Ω → 0 < v c →
      ∀ x ∈ ball c (R / 2), 0 < v x) : ∀ x ∈ Ω, 0 < v x := by
  let P := Ω ∩ v ⁻¹' Set.Ioi 0
  have hP : IsOpen P := hv.isOpen_inter_preimage hΩ isOpen_Ioi
  have hnonempty : (Ω ∩ P).Nonempty := by
    obtain ⟨x, hx, hpos⟩ := hex
    exact ⟨x, hx, hx, hpos⟩
  have hclosed : closure P ∩ Ω ⊆ P := by
    intro x hx
    obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.1 (hΩ.mem_nhds hx.2)
    obtain ⟨y, hy, hdist⟩ := Metric.mem_closure_iff.1 hx.1 (r / 4) (by positivity)
    have hball : closedBall y (r / 2) ⊆ Ω := by
      intro z hz
      apply hrsub
      rw [mem_ball]
      have hzdist : dist z y ≤ r / 2 := hz
      have hydist : dist y x < r / 4 := by simpa only [dist_comm] using hdist
      linarith [dist_triangle z y x]
    refine ⟨hx.2, hprop y (r / 2) (by positivity) hball hy.2 x ?_⟩
    change dist x y < r / 2 / 2
    convert hdist using 1
    ring
  exact fun x hx ↦ (hconn.subset_of_closure_inter_subset hP hnonempty hclosed hx).2

/-- A continuous potential is absorbed into a positive constant on compact interior balls. -/
theorem exists_weakSupersolution_on_ball {Ω : Set E} {v a : E → ℝ}
    (hv : ContDiffOn ℝ 1 v Ω) (ha : ContinuousOn a Ω) (hv0 : ∀ x ∈ Ω, 0 ≤ v x)
    (heq : ∀ φ : E → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ x, inner ℝ (gradient v x) (gradient φ x) ∂μ) = ∫ x, a x * v x * φ x ∂μ)
    {c : E} {R : ℝ} (hball : closedBall c R ⊆ Ω) :
    ∃ M : ℝ, 0 < M ∧ IsWeakSupersolution μ (ball c R) M v := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall c R).exists_bound_of_continuousOn (ha.mono hball)
  have hsub : ball c R ⊆ Ω := ball_subset_closedBall.trans hball
  refine ⟨|C| + 1, by positivity, isWeakSupersolution_of_weak_equation isOpen_ball
    (hv.mono hsub) (ha.mono hsub) (fun x hx ↦ hv0 x (hsub hx)) ?_ ?_⟩
  · intro x hx
    have hb := hC x (ball_subset_closedBall hx)
    simp only [Real.norm_eq_abs] at hb
    linarith [neg_abs_le (a x), le_abs_self C]
  · exact fun φ hφ hc hs ↦ heq φ hφ hc (hs.trans hsub)

/-- A nonnegative weak solution with continuous potential is positive on its connected domain
as soon as it has one positive value. -/
theorem positive_of_weak_equation {Ω : Set E} {v a : E → ℝ}
    (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω) (hv : ContDiffOn ℝ 1 v Ω)
    (ha : ContinuousOn a Ω) (hv0 : ∀ x ∈ Ω, 0 ≤ v x) (hex : ∃ x ∈ Ω, 0 < v x)
    (heq : ∀ φ : E → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ x, inner ℝ (gradient v x) (gradient φ x) ∂μ) = ∫ x, a x * v x * φ x ∂μ) :
    ∀ x ∈ Ω, 0 < v x := by
  apply positive_of_halfBall_propagation hΩ hconn hv.continuousOn hex
  intro c R hR hball hc
  obtain ⟨M, hM, hweak⟩ := exists_weakSupersolution_on_ball hv ha hv0 heq hball
  have hsub : ball c R ⊆ Ω := ball_subset_closedBall.trans hball
  exact hweak.pos_on_ball isOpen_ball (hv.mono hsub) (fun x hx ↦ hv0 x (hsub hx)) hM
    (half_pos hR) (closedBall_subset_ball (half_lt_self hR)) hc

/-- Nonnegativity upgrades to strict positivity for the vertical derivative in the epigraph. -/
theorem Hypotheses.verticalDerivative_pos_of_nonneg {m : ℕ} {g : Space m → ℝ}
    {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ} (h : Hypotheses g u f κ)
    (hv0 : ∀ x ∈ epigraph g, 0 ≤ verticalDerivative u x) :
    ∀ x ∈ epigraph g, 0 < verticalDerivative u x := by
  have hΩ := isOpen_epigraph h.graph_contDiff.continuous
  have hv : ContDiffOn ℝ 1 (verticalDerivative u) (epigraph g) :=
    (h.solution_contDiffOn.fderiv_of_isOpen hΩ (m := 1) (by norm_num)).clm_apply contDiffOn_const
  have ha : ContinuousOn (fun x ↦ deriv f (u x)) (epigraph g) :=
    ((h.reaction_contDiffOn.mono Set.Ioi_subset_Ici_self).continuousOn_deriv_of_isOpen
      isOpen_Ioi le_rfl).comp h.solution_contDiffOn.continuousOn (fun x hx ↦ h.positive x hx)
  exact positive_of_weak_equation hΩ
    (isConnected_epigraph h.graph_contDiff.continuous).isPreconnected hv ha hv0
    (exists_verticalDerivative_pos h) (fun φ hφ hc hs ↦ h.weak_vertical_equation hφ hc hs)

end SerrinEpigraph
