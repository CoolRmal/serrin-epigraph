module

public import SerrinEpigraph.TranslatedDomain
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Topology.Order.IntermediateValue

/-!
# Interior and exterior tangent balls in entire epigraphs

These geometric contact constructions are independent of the reaction term.
-/

public section
noncomputable section

open Metric Set

namespace SerrinEpigraph

/-- A continuous path from a closed set to the center of a disjoint ball meets a tangent ball. -/
theorem exists_tangent_ball_along_path {d : ℕ} {S : Set (Space d)} (hS : IsClosed S)
    {c : ℝ → Space d} (hc : Continuous c) {a b R : ℝ} (ha : c a ∈ S) (hR : 0 < R)
    (hb : ball (c b) R ⊆ Sᶜ) :
    ∃ t z, ball (c t) R ⊆ Sᶜ ∧ z ∈ frontier S ∧ dist z (c t) = R := by
  have hne : S.Nonempty := ⟨c a, ha⟩
  have hd : R ≤ infDist (c b) S := (le_infDist hne).mpr (by
    intro y hy
    by_contra hlt
    have hball : y ∈ ball (c b) R := by
      rw [mem_ball, dist_comm]
      exact lt_of_not_ge hlt
    exact hb hball hy)
  have hcont : Continuous (fun t ↦ infDist (c t) S) := (continuous_infDist_pt S).comp hc
  obtain ⟨t, ht⟩ := intermediate_value_univ a b hcont
    (show R ∈ Icc (infDist (c a) S) (infDist (c b) S) from
      ⟨by rw [infDist_zero_of_mem ha]; exact hR.le, hd⟩)
  change infDist (c t) S = R at ht
  obtain ⟨z, hz, hdist⟩ := hS.exists_infDist_eq_dist hne (c t)
  have hball : ball (c t) R ⊆ Sᶜ := by
    intro y hy
    apply notMem_of_dist_lt_infDist (x := c t)
    rw [ht, dist_comm]
    exact hy
  have he : dist z (c t) = R := by rw [dist_comm, ← hdist, ht]
  have hzc : z ∈ closure Sᶜ := by
    apply closure_mono hball
    rw [closure_ball _ hR.ne']
    exact (mem_closedBall.mpr he.le)
  refine ⟨t, z, hball, ?_, he⟩
  rw [frontier_eq_closure_inter_closure]
  exact ⟨subset_closure hz, hzc⟩

/-- The vertical axis in point coordinates agrees with scalar translation. -/
theorem vertical_axis_eq_point (m : ℕ) (t : ℝ) :
    t • verticalDirection m = point (0 : Space m) t := by
  ext i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i <;> simp [point, verticalDirection]

/-- Every positive radius admits an interior ball tangent to the epigraph boundary. -/
theorem epigraph_exists_interior_tangent_ball {m : ℕ} {g : Space m → ℝ}
    (hg : Continuous g) {R : ℝ} (hR : 0 < R) :
    ∃ t z, ball (point (0 : Space m) t) R ⊆ epigraph g ∧
      z ∈ frontier (epigraph g) ∧ dist z (point (0 : Space m) t) = R := by
  obtain ⟨T, hT⟩ := compact_eventually_in_epigraph hg (isCompact_closedBall (0 : Space (m + 1)) R)
  have hb : ball (T • verticalDirection m) R ⊆ epigraph g := by
    intro x hx
    have hy : x - T • verticalDirection m ∈ closedBall 0 R := by
      have hx' := (mem_ball.mp hx).le
      simpa only [mem_closedBall, dist_zero_right, dist_eq_norm, sub_zero] using hx'
    simpa only [sub_add_cancel] using hT T le_rfl _ hy
  have ha : g 0 • verticalDirection m ∈ (epigraph g)ᶜ := by
    rw [vertical_axis_eq_point]
    simp [epigraph]
  obtain ⟨t, z, hball, hz, he⟩ := exists_tangent_ball_along_path
    (c := fun t : ℝ ↦ t • verticalDirection m)
    (isOpen_epigraph hg).isClosed_compl (continuous_id.smul continuous_const) ha hR
    (by simpa only [compl_compl] using hb)
  refine ⟨t, z, ?_, ?_, ?_⟩
  · simpa only [compl_compl, vertical_axis_eq_point] using hball
  · simpa only [frontier_compl] using hz
  · simpa only [vertical_axis_eq_point] using he

/-- Compact sets translated sufficiently far downward lie strictly below the graph. -/
theorem compact_eventually_below_epigraph {m : ℕ} {g : Space m → ℝ}
    (hg : Continuous g) {K : Set (Space (m + 1))} (hK : IsCompact K) :
    ∃ T : ℝ, ∀ t : ℝ, T ≤ t → ∀ x ∈ K,
      x - t • verticalDirection m ∉ closure (epigraph g) := by
  have hc : Continuous (fun x : Space (m + 1) ↦ x (Fin.last m) - g (horizontal x)) := by
    apply Continuous.sub _ (hg.comp continuous_horizontal)
    fun_prop
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨C + 1, fun t ht x hx ↦ ?_⟩
  have hb := hC x hx
  rw [Real.norm_eq_abs] at hb
  rw [sub_eq_add_neg, ← neg_smul, add_vertical_eq_point, closure_epigraph hg]
  simp only [mem_ofPred_eq, horizontal_point, last_point, not_le]
  linarith [le_abs_self (x (Fin.last m) - g (horizontal x))]

/-- Every positive radius admits an exterior ball tangent to the epigraph boundary. -/
theorem epigraph_exists_exterior_tangent_ball {m : ℕ} {g : Space m → ℝ}
    (hg : Continuous g) {R : ℝ} (hR : 0 < R) :
    ∃ t z, ball (point (0 : Space m) t) R ⊆ (closure (epigraph g))ᶜ ∧
      z ∈ frontier (epigraph g) ∧ dist z (point (0 : Space m) t) = R := by
  obtain ⟨T, hT⟩ := compact_eventually_below_epigraph hg
    (isCompact_closedBall (0 : Space (m + 1)) R)
  have hb : ball ((-T) • verticalDirection m) R ⊆ (closure (epigraph g))ᶜ := by
    intro x hx
    have hy : x - (-T) • verticalDirection m ∈ closedBall 0 R := by
      have hx' := (mem_ball.mp hx).le
      simpa only [mem_closedBall, dist_zero_right, dist_eq_norm, sub_zero] using hx'
    have he := hT T le_rfl _ hy
    change x ∉ closure (epigraph g)
    simpa only [neg_smul, sub_neg_eq_add, add_sub_cancel_right] using he
  have ha : g 0 • verticalDirection m ∈ closure (epigraph g) := by
    rw [vertical_axis_eq_point]
    exact point_mem_closure_epigraph le_rfl
  obtain ⟨t, z, hball, hz, he⟩ := exists_tangent_ball_along_path
    (c := fun t : ℝ ↦ t • verticalDirection m) isClosed_closure
    (continuous_id.smul continuous_const) ha hR hb
  exact ⟨t, z, by simpa only [vertical_axis_eq_point] using hball,
    frontier_closure_subset hz, by simpa only [vertical_axis_eq_point] using he⟩

end SerrinEpigraph
