module

public import SerrinEpigraph.PhaseClearingInterfaceExclusion
public import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
# From local integral convergence and excluded levels to uniform phase limits
-/

public section
noncomputable section

open Set Metric Filter MeasureTheory InnerProductSpace
open scoped Topology

namespace SerrinEpigraph

/-- Excluding all fixed small positive levels upgrades local integral convergence
to zero to uniform convergence on compact subsets. -/
theorem tendstoUniformlyOn_zero_of_local_integral_and_level_exclusion
    {d : ℕ} {v : ℕ → Space d → ℝ}
    (hv : ∀ j, Continuous (v j)) (hvn : ∀ j x, 0 ≤ v j x)
    {Ω : Set (Space d)} (hΩ : IsOpen Ω)
    (hphase : ∀ L : Set (Space d), IsCompact L → L ⊆ Ω →
      Tendsto (fun j ↦ ∫ x in L, ‖v j x‖) atTop (𝓝 0))
    (hlevels : ∀ L : Set (Space d), IsCompact L → L ⊆ Ω →
      ∀ α : ℝ, α ∈ Ioo (0 : ℝ) 1 → ∀ᶠ j in atTop, ∀ x ∈ L, v j x ≠ α)
    {K : Set (Space d)} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    TendstoUniformlyOn v 0 atTop K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  let α := min (ε / 2) (1 / 2 : ℝ)
  have hα : 0 < α := lt_min (by positivity) (by norm_num)
  have hαone : α < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hαε : α < ε := (min_le_left _ _).trans_lt (by linarith)
  obtain ⟨r, hr, hthick⟩ := hK.exists_cthickening_subset_open hΩ hKΩ
  let L := cthickening r K
  have hL : IsCompact L := hK.cthickening
  have hvol : 0 < (volume (closedBall (0 : Space d) r)).toReal :=
    ENNReal.toReal_pos (measure_closedBall_pos volume 0 hr).ne' measure_closedBall_lt_top.ne
  have hevent := (hphase L hL hthick).eventually
    (gt_mem_nhds (mul_pos hα hvol))
  filter_upwards [hevent, hlevels L hL hthick α ⟨hα, hαone⟩] with j hj hjlevels
  intro x hx
  have hvsmall : v j x < α := by
    by_contra hn
    have hvx : α ≤ v j x := le_of_not_gt hn
    have hball : ∀ y ∈ closedBall x r, α ≤ v j y := by
      intro y hy
      by_contra hny
      have hvy : v j y < α := lt_of_not_ge hny
      have himg := (convex_closedBall x r).isPreconnected.intermediate_value hy
        (mem_closedBall_self hr.le) (hv j).continuousOn
      obtain ⟨z, hz, he⟩ := himg ⟨hvy.le, hvx⟩
      exact hjlevels z (closedBall_subset_cthickening hx r hz) he
    have hlo : α * (volume (closedBall (0 : Space d) r)).toReal ≤
        ∫ y in closedBall x r, ‖v j y‖ := by
      have hi := integral_mono_ae (continuousOn_const.integrableOn_compact
        (μ := volume) (isCompact_closedBall x r) (f := fun _ : Space d ↦ α))
        ((hv j).norm.continuousOn.integrableOn_compact (isCompact_closedBall x r))
        (by
          filter_upwards [ae_restrict_mem measurableSet_closedBall] with y hy
          exact (hball y hy).trans (le_abs_self _))
      simp only [integral_const, measureReal_def, Measure.restrict_apply_univ, smul_eq_mul] at hi
      have hvolEq : volume (closedBall x r) = volume (closedBall (0 : Space d) r) := by
        rw [Measure.addHaar_closedBall volume x hr.le,
          Measure.addHaar_closedBall volume (0 : Space d) hr.le]
      rw [hvolEq] at hi
      simpa only [mul_comm] using hi
    have hmono := setIntegral_mono_set
      ((hv j).norm.continuousOn.integrableOn_compact (μ := volume) hL)
      (Eventually.of_forall (fun y ↦ norm_nonneg (v j y)))
      (Eventually.of_forall (closedBall_subset_cthickening hx r))
    exact (not_lt_of_ge (hlo.trans hmono)) hj
  simpa only [Pi.zero_apply, dist_zero_left, Real.norm_eq_abs, abs_of_nonneg (hvn j x)]
    using hvsmall.trans hαε

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ : ℝ}

/-- Vanishing phase and energy integrals imply uniform convergence to zero locally. -/
theorem RigidityHypotheses.tendstoUniformlyOn_zero_of_energy_and_phase_vanishes
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {T : ℕ → ℝ} (hT : ∀ j, 0 < T j) (hTt : Tendsto T atTop atTop)
    {Ω : Set (Space (m + 1))} (hΩ : IsOpen Ω)
    (henergy : ∀ L : Set (Space (m + 1)), IsCompact L → L ⊆ Ω →
      Tendsto (fun j ↦ ∫ x in L, rescaledPhaseEnergyDensity f (T j)
        (fun y ↦ zeroExtension g u (T j • y)) x) atTop (𝓝 0))
    (hphase : ∀ L : Set (Space (m + 1)), IsCompact L → L ⊆ Ω →
      Tendsto (fun j ↦ ∫ x in L, ‖zeroExtension g u (T j • x)‖) atTop (𝓝 0))
    {K : Set (Space (m + 1))} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    TendstoUniformlyOn (fun j x ↦ zeroExtension g u (T j • x)) 0 atTop K := by
  apply tendstoUniformlyOn_zero_of_local_integral_and_level_exclusion
    (fun j ↦ h.zeroExtension_continuous.comp (continuous_const_smul (T j)))
    (fun _ _ ↦ h.zeroExtension_nonneg _) hΩ hphase ?_ hK hKΩ
  intro L hL hLΩ α hα
  filter_upwards [hr.eventually_no_interior_levels_of_energy_vanishes
    h hT hTt hΩ henergy hL hLΩ hα.1 hα.2] with j hj
  intro x hx he
  simp only [Function.comp_apply] at he
  exact hj x hx (by rw [he]; exact ⟨le_rfl, le_rfl⟩)

/-- Vanishing energy and local integral convergence to one imply locally uniform
convergence to the positive well. -/
theorem RigidityHypotheses.tendstoUniformlyOn_one_of_energy_and_phase_converges
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {T : ℕ → ℝ} (hT : ∀ j, 0 < T j) (hTt : Tendsto T atTop atTop)
    {Ω : Set (Space (m + 1))} (hΩ : IsOpen Ω)
    (henergy : ∀ L : Set (Space (m + 1)), IsCompact L → L ⊆ Ω →
      Tendsto (fun j ↦ ∫ x in L, rescaledPhaseEnergyDensity f (T j)
        (fun y ↦ zeroExtension g u (T j • y)) x) atTop (𝓝 0))
    (hphase : ∀ L : Set (Space (m + 1)), IsCompact L → L ⊆ Ω →
      Tendsto (fun j ↦ ∫ x in L, ‖zeroExtension g u (T j • x) - 1‖) atTop (𝓝 0))
    {K : Set (Space (m + 1))} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    TendstoUniformlyOn (fun j x ↦ zeroExtension g u (T j • x)) (fun _ ↦ 1) atTop K := by
  have hz : TendstoUniformlyOn (fun j x ↦ 1 - zeroExtension g u (T j • x)) 0 atTop K := by
    apply tendstoUniformlyOn_zero_of_local_integral_and_level_exclusion
      (fun j ↦ continuous_const.sub
        (h.zeroExtension_continuous.comp (continuous_const_smul (T j))))
      (fun j x ↦ sub_nonneg.mpr (hr.zeroExtension_lt_one (T j • x)).le) hΩ ?_ ?_ hK hKΩ
    · intro L hL hLΩ
      simpa only [Pi.sub_apply, Function.comp_apply, norm_sub_rev] using hphase L hL hLΩ
    · intro L hL hLΩ α hα
      filter_upwards [hr.eventually_no_interior_levels_of_energy_vanishes
        h hT hTt hΩ henergy hL hLΩ (a := 1 - α) (b := 1 - α)
        (by linarith [hα.2]) (by linarith [hα.1])] with j hj
      intro x hx he
      simp only [Pi.sub_apply, Function.comp_apply] at he
      have heq : zeroExtension g u (T j • x) = 1 - α := by linarith
      exact hj x hx (by rw [heq]; exact ⟨le_rfl, le_rfl⟩)
  rw [Metric.tendstoUniformlyOn_iff] at hz ⊢
  intro ε hε
  filter_upwards [hz ε hε] with j hj
  intro x hx
  simpa only [Pi.zero_apply, Real.dist_eq, zero_sub, abs_neg] using hj x hx

/-- Uniform convergence to the zero phase improves to exact eventual vanishing
on compact sets, by applying physical clearing at radius R₀. -/
theorem RigidityHypotheses.eventually_eq_zero_of_locally_uniform_zero
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {T : ℕ → ℝ} (hT : ∀ j, 0 < T j) (hTt : Tendsto T atTop atTop)
    {Ω : Set (Space (m + 1))} (hΩ : IsOpen Ω)
    (huniform : ∀ L : Set (Space (m + 1)), IsCompact L → L ⊆ Ω →
      TendstoUniformlyOn (fun j x ↦ zeroExtension g u (T j • x)) 0 atTop L)
    {K : Set (Space (m + 1))} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∀ᶠ j in atTop, EqOn (fun x ↦ zeroExtension g u (T j • x)) 0 K := by
  obtain ⟨a, R₀, ha, hR₀, hclear⟩ := hr.exists_rescaled_phase_clearing_constants h
  obtain ⟨r, hradius, hthick⟩ := hK.exists_cthickening_subset_open hΩ hKΩ
  let L := cthickening r K
  have hL : IsCompact L := hK.cthickening
  have hsmall := Metric.tendstoUniformlyOn_iff.mp (huniform L hL hthick)
    (a * R₀) (mul_pos ha hR₀)
  have hlarge : ∀ᶠ j in atTop, R₀ / T j ≤ r := by
    filter_upwards [hTt.eventually (eventually_ge_atTop (R₀ / r))] with j hj
    apply (div_le_iff₀ (hT j)).mpr
    have hh := (div_le_iff₀ hradius).mp hj
    linarith
  filter_upwards [hsmall, hlarge] with j hj hjlarge
  intro x hx
  have hrad : 0 < R₀ / T j := div_pos hR₀ (hT j)
  have hscale : T j * (R₀ / T j) = R₀ := by field_simp [(hT j).ne']
  have hz := hclear (T j) (hT j) x (R₀ / T j) hrad hscale.le (by
    intro y hy
    have hyL : y ∈ L := closedBall_subset_cthickening hx r
      (ball_subset_closedBall (ball_subset_ball hjlarge hy))
    have hb := hj y hyL
    rw [hscale]
    have hnorm : ‖zeroExtension g u (T j • y)‖ < a * R₀ := by
      simpa only [Pi.zero_apply, dist_zero_left] using hb
    exact (le_abs_self _).trans hnorm.le)
  exact hz (mem_ball_self (half_pos hrad))

end SerrinEpigraph
