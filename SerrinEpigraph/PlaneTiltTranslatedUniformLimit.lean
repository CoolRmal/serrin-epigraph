module

public import SerrinEpigraph.PlaneTiltTranslatedClearing

/-!
# Locally uniform phase convergence for moving centers
-/

public section
noncomputable section

open Set Metric Filter MeasureTheory InnerProductSpace
open scoped Topology

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ : ℝ}

/-- Vanishing phase and energy integrals imply uniform convergence to zero locally. -/
theorem RigidityHypotheses.translated_tendstoUniformlyOn_zero_of_energy_and_phase_vanishes
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (c : ℕ → Space (m + 1)) {T : ℕ → ℝ} (hT : ∀ j, 0 < T j) (hTt : Tendsto T atTop atTop)
    {Ω : Set (Space (m + 1))} (hΩ : IsOpen Ω)
    (henergy : ∀ L : Set (Space (m + 1)), IsCompact L → L ⊆ Ω →
      Tendsto (fun j ↦ ∫ x in L, rescaledPhaseEnergyDensity f (T j)
        (fun y ↦ zeroExtension g u (c j + T j • y)) x) atTop (𝓝 0))
    (hphase : ∀ L : Set (Space (m + 1)), IsCompact L → L ⊆ Ω →
      Tendsto (fun j ↦ ∫ x in L, ‖zeroExtension g u (c j + T j • x)‖) atTop (𝓝 0))
    {K : Set (Space (m + 1))} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    TendstoUniformlyOn (fun j x ↦ zeroExtension g u (c j + T j • x)) 0 atTop K := by
  apply tendstoUniformlyOn_zero_of_local_integral_and_level_exclusion
    (fun j ↦ h.zeroExtension_continuous.comp (continuous_const.add (continuous_const_smul (T j))))
    (fun _ _ ↦ h.zeroExtension_nonneg _) hΩ hphase ?_ hK hKΩ
  intro L hL hLΩ α hα
  filter_upwards [hr.translated_eventually_no_interior_levels_of_energy_vanishes
    h c hT hTt hΩ henergy hL hLΩ hα.1 hα.2] with j hj
  intro x hx he
  simp only [Function.comp_apply, Pi.add_apply] at he
  exact hj x hx (by rw [he]; exact ⟨le_rfl, le_rfl⟩)

/-- Vanishing energy and local integral convergence to one imply locally uniform
convergence to the positive well. -/
theorem RigidityHypotheses.translated_tendstoUniformlyOn_one_of_energy_and_phase_converges
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (c : ℕ → Space (m + 1)) {T : ℕ → ℝ} (hT : ∀ j, 0 < T j) (hTt : Tendsto T atTop atTop)
    {Ω : Set (Space (m + 1))} (hΩ : IsOpen Ω)
    (henergy : ∀ L : Set (Space (m + 1)), IsCompact L → L ⊆ Ω →
      Tendsto (fun j ↦ ∫ x in L, rescaledPhaseEnergyDensity f (T j)
        (fun y ↦ zeroExtension g u (c j + T j • y)) x) atTop (𝓝 0))
    (hphase : ∀ L : Set (Space (m + 1)), IsCompact L → L ⊆ Ω →
      Tendsto (fun j ↦ ∫ x in L, ‖zeroExtension g u (c j + T j • x) - 1‖) atTop (𝓝 0))
    {K : Set (Space (m + 1))} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    TendstoUniformlyOn (fun j x ↦ zeroExtension g u (c j + T j • x)) (fun _ ↦ 1) atTop K := by
  have hz : TendstoUniformlyOn (fun j x ↦ 1 - zeroExtension g u (c j + T j • x)) 0 atTop K := by
    apply tendstoUniformlyOn_zero_of_local_integral_and_level_exclusion
      (fun j ↦ continuous_const.sub
        (h.zeroExtension_continuous.comp (continuous_const.add (continuous_const_smul (T j)))))
      (fun j x ↦ sub_nonneg.mpr (hr.zeroExtension_lt_one (c j + T j • x)).le) hΩ ?_ ?_ hK hKΩ
    · intro L hL hLΩ
      simpa only [Pi.sub_apply, Function.comp_apply, Pi.add_apply, norm_sub_rev] using hphase L hL hLΩ
    · intro L hL hLΩ α hα
      filter_upwards [hr.translated_eventually_no_interior_levels_of_energy_vanishes
        h c hT hTt hΩ henergy hL hLΩ (a := 1 - α) (b := 1 - α)
        (by linarith [hα.2]) (by linarith [hα.1])] with j hj
      intro x hx he
      simp only [Pi.sub_apply, Function.comp_apply, Pi.add_apply] at he
      have heq : zeroExtension g u (c j + T j • x) = 1 - α := by linarith
      exact hj x hx (by rw [heq]; exact ⟨le_rfl, le_rfl⟩)
  rw [Metric.tendstoUniformlyOn_iff] at hz ⊢
  intro ε hε
  filter_upwards [hz ε hε] with j hj
  intro x hx
  simpa only [Pi.zero_apply, Real.dist_eq, zero_sub, abs_neg] using hj x hx

/-- Uniform convergence to the zero phase improves to exact eventual vanishing
on compact sets, by applying physical clearing at radius R₀. -/
theorem RigidityHypotheses.translated_eventually_eq_zero_of_locally_uniform_zero
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (c : ℕ → Space (m + 1)) {T : ℕ → ℝ} (hT : ∀ j, 0 < T j) (hTt : Tendsto T atTop atTop)
    {Ω : Set (Space (m + 1))} (hΩ : IsOpen Ω)
    (huniform : ∀ L : Set (Space (m + 1)), IsCompact L → L ⊆ Ω →
      TendstoUniformlyOn (fun j x ↦ zeroExtension g u (c j + T j • x)) 0 atTop L)
    {K : Set (Space (m + 1))} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∀ᶠ j in atTop, EqOn (fun x ↦ zeroExtension g u (c j + T j • x)) 0 K := by
  obtain ⟨a, R₀, ha, hR₀, hclear⟩ := hr.exists_translated_phase_clearing_constants h
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
  have hz := hclear (c j) (T j) (hT j) x (R₀ / T j) hrad hscale.le (by
    intro y hy
    have hyL : y ∈ L := closedBall_subset_cthickening hx r
      (ball_subset_closedBall (ball_subset_ball hjlarge hy))
    have hb := hj y hyL
    rw [hscale]
    have hnorm : ‖zeroExtension g u (c j + T j • y)‖ < a * R₀ := by
      simpa only [Pi.zero_apply, dist_zero_left] using hb
    exact (le_abs_self _).trans hnorm.le)
  exact hz (mem_ball_self (half_pos hrad))

end SerrinEpigraph
