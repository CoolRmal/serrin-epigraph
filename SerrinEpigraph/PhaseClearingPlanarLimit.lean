module

public import SerrinEpigraph.PhaseClearingUniformLimit
public import SerrinEpigraph.PlaneTiltEnergyAway

/-!
# Planar integral limits give uniform phases and thin interface slabs

These conclusions use the original hypotheses and the actual halfspace phase
limit. Energy vanishing away from the plane is proved in PlaneTiltEnergyAway.
-/

public section
noncomputable section

open Set Metric Filter MeasureTheory InnerProductSpace
open scoped Topology

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ : ℝ}

theorem RigidityHypotheses.eventually_no_interior_levels_away_plane
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {R : ℕ → ℝ} (hR : ∀ j, 1 ≤ R j) (hRt : Tendsto R atTop atTop)
    {e : Space (m + 1)} (he : ‖e‖ = 1)
    (hlocal : ∀ K : Set (Space (m + 1)), IsCompact K →
      Tendsto (fun j ↦ ∫ x in K, ‖zeroExtension g u (R j • x) -
        {y : Space (m + 1) | 0 < inner ℝ e y}.indicator (fun _ ↦ (1 : ℝ)) x‖)
          atTop (𝓝 0))
    {K : Set (Space (m + 1))} (hK : IsCompact K)
    (havoid : ∀ x ∈ K, inner ℝ e x ≠ 0) {a b : ℝ} (ha : 0 < a) (hb : b < 1) :
    ∀ᶠ j in atTop, ∀ x ∈ K, zeroExtension g u (R j • x) ∉ Icc a b := by
  have hΩ : IsOpen {x : Space (m + 1) | inner ℝ e x ≠ 0} :=
    isOpen_ne.preimage (continuous_const.inner continuous_id)
  apply hr.eventually_no_interior_levels_of_energy_vanishes h
    (fun j ↦ zero_lt_one.trans_le (hR j)) hRt hΩ ?_ hK havoid ha hb
  intro L hL hLΩ
  exact hr.rescaled_energy_tendsto_zero_away_plane h hR hRt he hlocal hL hLΩ

theorem RigidityHypotheses.eventually_no_freeBoundary_away_plane
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {R : ℕ → ℝ} (hR : ∀ j, 1 ≤ R j) (hRt : Tendsto R atTop atTop)
    {e : Space (m + 1)} (he : ‖e‖ = 1)
    (hlocal : ∀ K : Set (Space (m + 1)), IsCompact K →
      Tendsto (fun j ↦ ∫ x in K, ‖zeroExtension g u (R j • x) -
        {y : Space (m + 1) | 0 < inner ℝ e y}.indicator (fun _ ↦ (1 : ℝ)) x‖)
          atTop (𝓝 0))
    {K : Set (Space (m + 1))} (hK : IsCompact K)
    (havoid : ∀ x ∈ K, inner ℝ e x ≠ 0) :
    ∀ᶠ j in atTop, ∀ x ∈ K, R j • x ∉ frontier (epigraph g) := by
  have hΩ : IsOpen {x : Space (m + 1) | inner ℝ e x ≠ 0} :=
    isOpen_ne.preimage (continuous_const.inner continuous_id)
  apply hr.eventually_no_freeBoundary_of_energy_vanishes h
    (fun j ↦ zero_lt_one.trans_le (hR j)) hRt hΩ ?_ hK havoid
  intro L hL hLΩ
  exact hr.rescaled_energy_tendsto_zero_away_plane h hR hRt he hlocal hL hLΩ

/-- On every compact subset of the positive limiting halfspace, the solutions
converge uniformly to the positive well. -/
theorem RigidityHypotheses.tendstoUniformlyOn_one_positive_halfspace
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {R : ℕ → ℝ} (hR : ∀ j, 1 ≤ R j) (hRt : Tendsto R atTop atTop)
    {e : Space (m + 1)} (he : ‖e‖ = 1)
    (hlocal : ∀ K : Set (Space (m + 1)), IsCompact K →
      Tendsto (fun j ↦ ∫ x in K, ‖zeroExtension g u (R j • x) -
        {y : Space (m + 1) | 0 < inner ℝ e y}.indicator (fun _ ↦ (1 : ℝ)) x‖)
          atTop (𝓝 0))
    {K : Set (Space (m + 1))} (hK : IsCompact K)
    (hpositive : ∀ x ∈ K, 0 < inner ℝ e x) :
    TendstoUniformlyOn (fun j x ↦ zeroExtension g u (R j • x)) (fun _ ↦ 1) atTop K := by
  have hΩ : IsOpen {x : Space (m + 1) | 0 < inner ℝ e x} :=
    isOpen_lt continuous_const (continuous_const.inner continuous_id)
  apply hr.tendstoUniformlyOn_one_of_energy_and_phase_converges h
    (fun j ↦ zero_lt_one.trans_le (hR j)) hRt hΩ ?_ ?_ hK hpositive
  · intro L hL hLΩ
    exact hr.rescaled_energy_tendsto_zero_away_plane h hR hRt he hlocal hL
      (fun x hx ↦ (hLΩ hx).ne')
  · intro L hL hLΩ
    convert hlocal L hL using 1
    funext j
    apply setIntegral_congr_fun hL.measurableSet
    intro x hx
    dsimp only
    rw [Set.indicator_of_mem (hLΩ hx)]

/-- On every compact subset of the negative limiting halfspace, the solutions
converge uniformly to zero. -/
theorem RigidityHypotheses.tendstoUniformlyOn_zero_negative_halfspace
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {R : ℕ → ℝ} (hR : ∀ j, 1 ≤ R j) (hRt : Tendsto R atTop atTop)
    {e : Space (m + 1)} (he : ‖e‖ = 1)
    (hlocal : ∀ K : Set (Space (m + 1)), IsCompact K →
      Tendsto (fun j ↦ ∫ x in K, ‖zeroExtension g u (R j • x) -
        {y : Space (m + 1) | 0 < inner ℝ e y}.indicator (fun _ ↦ (1 : ℝ)) x‖)
          atTop (𝓝 0))
    {K : Set (Space (m + 1))} (hK : IsCompact K)
    (hnegative : ∀ x ∈ K, inner ℝ e x < 0) :
    TendstoUniformlyOn (fun j x ↦ zeroExtension g u (R j • x)) 0 atTop K := by
  have hΩ : IsOpen {x : Space (m + 1) | inner ℝ e x < 0} :=
    isOpen_lt (continuous_const.inner continuous_id) continuous_const
  apply hr.tendstoUniformlyOn_zero_of_energy_and_phase_vanishes h
    (fun j ↦ zero_lt_one.trans_le (hR j)) hRt hΩ ?_ ?_ hK hnegative
  · intro L hL hLΩ
    exact hr.rescaled_energy_tendsto_zero_away_plane h hR hRt he hlocal hL
      (fun x hx ↦ (hLΩ hx).ne)
  · intro L hL hLΩ
    convert hlocal L hL using 1
    funext j
    apply setIntegral_congr_fun hL.measurableSet
    intro x hx
    dsimp only
    have hnx : x ∉ {y : Space (m + 1) | 0 < inner ℝ e y} := by
      have hh : inner ℝ e x < 0 := hLΩ hx
      change ¬0 < inner ℝ e x
      linarith
    rw [Set.indicator_of_notMem hnx, sub_zero]

/-- On compact subsets of the negative limiting halfspace, zero is attained
identically after a finite index, not merely as a uniform limit. -/
theorem RigidityHypotheses.eventually_eq_zero_negative_halfspace
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {R : ℕ → ℝ} (hR : ∀ j, 1 ≤ R j) (hRt : Tendsto R atTop atTop)
    {e : Space (m + 1)} (he : ‖e‖ = 1)
    (hlocal : ∀ K : Set (Space (m + 1)), IsCompact K →
      Tendsto (fun j ↦ ∫ x in K, ‖zeroExtension g u (R j • x) -
        {y : Space (m + 1) | 0 < inner ℝ e y}.indicator (fun _ ↦ (1 : ℝ)) x‖)
          atTop (𝓝 0))
    {K : Set (Space (m + 1))} (hK : IsCompact K)
    (hnegative : ∀ x ∈ K, inner ℝ e x < 0) :
    ∀ᶠ j in atTop, EqOn (fun x ↦ zeroExtension g u (R j • x)) 0 K := by
  have hΩ : IsOpen {x : Space (m + 1) | inner ℝ e x < 0} :=
    isOpen_lt (continuous_const.inner continuous_id) continuous_const
  apply hr.eventually_eq_zero_of_locally_uniform_zero h
    (fun j ↦ zero_lt_one.trans_le (hR j)) hRt hΩ ?_ hK hnegative
  intro L hL hLΩ
  exact hr.tendstoUniformlyOn_zero_negative_halfspace h hR hRt he hlocal hL hLΩ

/-- Every rescaled free boundary in a bounded ball eventually lies in an
arbitrarily thin slab about the limiting plane. -/
theorem RigidityHypotheses.eventually_freeBoundary_in_planar_slab
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {R : ℕ → ℝ} (hR : ∀ j, 1 ≤ R j) (hRt : Tendsto R atTop atTop)
    {e : Space (m + 1)} (he : ‖e‖ = 1)
    (hlocal : ∀ K : Set (Space (m + 1)), IsCompact K →
      Tendsto (fun j ↦ ∫ x in K, ‖zeroExtension g u (R j • x) -
        {y : Space (m + 1) | 0 < inner ℝ e y}.indicator (fun _ ↦ (1 : ℝ)) x‖)
          atTop (𝓝 0))
    (s : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ j in atTop, ∀ x ∈ closedBall (0 : Space (m + 1)) s,
      R j • x ∈ frontier (epigraph g) → |inner ℝ e x| < δ := by
  let K := closedBall (0 : Space (m + 1)) s ∩ {x | δ ≤ |inner ℝ e x|}
  have hK : IsCompact K := (isCompact_closedBall _ _).inter_right
    (isClosed_le continuous_const (continuous_const.inner continuous_id).abs)
  have havoid : ∀ x ∈ K, inner ℝ e x ≠ 0 := by
    intro x hx heq
    have hh := hx.2
    simp only [Set.mem_ofPred_eq, heq, abs_zero] at hh
    linarith
  filter_upwards [hr.eventually_no_freeBoundary_away_plane h hR hRt he hlocal hK havoid]
    with j hj
  intro x hx hfront
  by_contra hn
  exact hj x ⟨hx, le_of_not_gt hn⟩ hfront

/-- The two caps of a bounded ball have the correct actual phases, uniformly:
the upper cap has a fixed positive lower bound and the lower cap is identically zero. -/
theorem RigidityHypotheses.eventually_planar_caps
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {R : ℕ → ℝ} (hR : ∀ j, 1 ≤ R j) (hRt : Tendsto R atTop atTop)
    {e : Space (m + 1)} (he : ‖e‖ = 1)
    (hlocal : ∀ K : Set (Space (m + 1)), IsCompact K →
      Tendsto (fun j ↦ ∫ x in K, ‖zeroExtension g u (R j • x) -
        {y : Space (m + 1) | 0 < inner ℝ e y}.indicator (fun _ ↦ (1 : ℝ)) x‖)
          atTop (𝓝 0))
    (s : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ j in atTop, ∀ x ∈ closedBall (0 : Space (m + 1)) s,
      (δ ≤ inner ℝ e x → 1 / 2 < zeroExtension g u (R j • x)) ∧
      (inner ℝ e x ≤ -δ → zeroExtension g u (R j • x) = 0) := by
  let Kp := closedBall (0 : Space (m + 1)) s ∩ {x | δ ≤ inner ℝ e x}
  let Km := closedBall (0 : Space (m + 1)) s ∩ {x | inner ℝ e x ≤ -δ}
  have hKp : IsCompact Kp := (isCompact_closedBall _ _).inter_right
    (isClosed_le continuous_const (continuous_const.inner continuous_id))
  have hKm : IsCompact Km := (isCompact_closedBall _ _).inter_right
    (isClosed_le (continuous_const.inner continuous_id) continuous_const)
  have hpos : ∀ x ∈ Kp, 0 < inner ℝ e x := fun _ hx ↦ hδ.trans_le hx.2
  have hneg : ∀ x ∈ Km, inner ℝ e x < 0 := fun _ hx ↦ hx.2.trans_lt (by linarith)
  have hp := Metric.tendstoUniformlyOn_iff.mp
    (hr.tendstoUniformlyOn_one_positive_halfspace h hR hRt he hlocal hKp hpos)
    (1 / 2) (by norm_num)
  have hn := hr.eventually_eq_zero_negative_halfspace h hR hRt he hlocal hKm hneg
  filter_upwards [hp, hn] with j hjp hjn
  intro x hx
  constructor
  · intro heq
    have hh := hjp x ⟨hx, heq⟩
    rw [Real.dist_eq] at hh
    have habs := (abs_lt.mp hh).2
    linarith
  · intro heq
    exact hjn ⟨hx, heq⟩

/-- Each fixed compact interval of interior phase values is eventually trapped
in an arbitrarily thin slab on every bounded ball. -/
theorem RigidityHypotheses.eventually_interior_levels_in_planar_slab
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {R : ℕ → ℝ} (hR : ∀ j, 1 ≤ R j) (hRt : Tendsto R atTop atTop)
    {e : Space (m + 1)} (he : ‖e‖ = 1)
    (hlocal : ∀ K : Set (Space (m + 1)), IsCompact K →
      Tendsto (fun j ↦ ∫ x in K, ‖zeroExtension g u (R j • x) -
        {y : Space (m + 1) | 0 < inner ℝ e y}.indicator (fun _ ↦ (1 : ℝ)) x‖)
          atTop (𝓝 0))
    (s : ℝ) {δ a b : ℝ} (hδ : 0 < δ) (ha : 0 < a) (hb : b < 1) :
    ∀ᶠ j in atTop, ∀ x ∈ closedBall (0 : Space (m + 1)) s,
      zeroExtension g u (R j • x) ∈ Icc a b → |inner ℝ e x| < δ := by
  let K := closedBall (0 : Space (m + 1)) s ∩ {x | δ ≤ |inner ℝ e x|}
  have hK : IsCompact K := (isCompact_closedBall _ _).inter_right
    (isClosed_le continuous_const (continuous_const.inner continuous_id).abs)
  have havoid : ∀ x ∈ K, inner ℝ e x ≠ 0 := by
    intro x hx heq
    have hh := hx.2
    simp only [Set.mem_ofPred_eq, heq, abs_zero] at hh
    linarith
  filter_upwards [hr.eventually_no_interior_levels_away_plane
    h hR hRt he hlocal hK havoid ha hb] with j hj
  intro x hx hlevel
  by_contra hn
  exact hj x ⟨hx, le_of_not_gt hn⟩ hlevel

/-- Every point of the limiting plane in a bounded ball is eventually within
any prescribed positive distance of the actual rescaled free boundary. -/
theorem RigidityHypotheses.eventually_plane_near_freeBoundary
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {R : ℕ → ℝ} (hR : ∀ j, 1 ≤ R j) (hRt : Tendsto R atTop atTop)
    {e : Space (m + 1)} (he : ‖e‖ = 1)
    (hlocal : ∀ K : Set (Space (m + 1)), IsCompact K →
      Tendsto (fun j ↦ ∫ x in K, ‖zeroExtension g u (R j • x) -
        {y : Space (m + 1) | 0 < inner ℝ e y}.indicator (fun _ ↦ (1 : ℝ)) x‖)
          atTop (𝓝 0))
    (s : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ j in atTop, ∀ x ∈ closedBall (0 : Space (m + 1)) s,
      inner ℝ e x = 0 → ∃ y ∈ ball x δ, R j • y ∈ frontier (epigraph g) := by
  have hee : inner ℝ e e = 1 := by rw [real_inner_self_eq_norm_sq, he]; norm_num
  filter_upwards [hr.eventually_planar_caps h hR hRt he hlocal (s + δ) (half_pos hδ)]
    with j hj
  intro x hx hxplane
  let p := x + (δ / 2) • e
  let q := x - (δ / 2) • e
  have hnorm : ‖(δ / 2) • e‖ = δ / 2 := by
    rw [norm_smul, he, mul_one, Real.norm_eq_abs, abs_of_pos (half_pos hδ)]
  have hxp : p ∈ closedBall (0 : Space (m + 1)) (s + δ) := by
    have hnx : ‖x‖ ≤ s := by simpa only [mem_closedBall, dist_zero_right] using hx
    change ‖p - 0‖ ≤ s + δ
    rw [sub_zero]
    exact (norm_add_le x ((δ / 2) • e)).trans (by rw [hnorm]; linarith)
  have hxq : q ∈ closedBall (0 : Space (m + 1)) (s + δ) := by
    have hnx : ‖x‖ ≤ s := by simpa only [mem_closedBall, dist_zero_right] using hx
    change ‖q - 0‖ ≤ s + δ
    rw [sub_zero]
    exact (norm_sub_le x ((δ / 2) • e)).trans (by rw [hnorm]; linarith)
  have hpdir : inner ℝ e p = δ / 2 := by
    simp only [p, inner_add_right, inner_smul_right, hxplane, hee, mul_one, zero_add]
  have hqdir : inner ℝ e q = -(δ / 2) := by
    simp only [q, inner_sub_right, inner_smul_right, hxplane, hee, mul_one, zero_sub]
  have hppos : 0 < zeroExtension g u (R j • p) :=
    (by norm_num : (0 : ℝ) < 1 / 2).trans ((hj p hxp).1 hpdir.ge)
  have hqzero : zeroExtension g u (R j • q) = 0 := (hj q hxq).2 hqdir.le
  have hpball : p ∈ ball x δ := by
    change ‖x + (δ / 2) • e - x‖ < δ
    rw [add_sub_cancel_left, hnorm]
    linarith
  have hqball : q ∈ ball x δ := by
    change ‖x - (δ / 2) • e - x‖ < δ
    rw [sub_sub_cancel_left, norm_neg, hnorm]
    linarith
  let H : Space (m + 1) → ℝ := fun y ↦
    (R j • y) (Fin.last m) - g (horizontal (R j • y))
  have hH : Continuous H := by
    apply Continuous.sub
    · fun_prop
    · exact h.graph_contDiff.continuous.comp
        (continuous_horizontal.comp (continuous_const_smul (R j)))
  have hHp : 0 ≤ H p := by
    have hpi := (h.zeroExtension_pos_iff (R j • p)).mp hppos
    change g (horizontal (R j • p)) < (R j • p) (Fin.last m) at hpi
    change 0 ≤ (R j • p) (Fin.last m) - g (horizontal (R j • p))
    exact sub_nonneg.mpr hpi.le
  have hHq : H q ≤ 0 := by
    have hqi : R j • q ∉ epigraph g := by
      intro hqi
      have hh := (h.zeroExtension_pos_iff (R j • q)).mpr hqi
      rw [hqzero] at hh
      exact lt_irrefl _ hh
    change ¬g (horizontal (R j • q)) < (R j • q) (Fin.last m) at hqi
    dsimp [H]
    exact sub_nonpos.mpr (le_of_not_gt hqi)
  obtain ⟨y, hy, hyH⟩ := (convex_ball x δ).isPreconnected.intermediate_value hqball hpball
    hH.continuousOn (show (0 : ℝ) ∈ Icc (H q) (H p) from ⟨hHq, hHp⟩)
  refine ⟨y, hy, ?_⟩
  rw [frontier_epigraph h.graph_contDiff.continuous]
  change g (horizontal (R j • y)) = (R j • y) (Fin.last m)
  change (R j • y) (Fin.last m) - g (horizontal (R j • y)) = 0 at hyH
  exact (sub_eq_zero.mp hyH).symm

end SerrinEpigraph
