module

public import SerrinEpigraph.QuadraticPotential

/-!
# Two-sided quadratic comparison for the normalized potential
-/

public section

noncomputable section

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ : ℝ}

/-- The reaction is at most linear in the distance to equilibrium on the upper half interval. -/
theorem RigidityHypotheses.reaction_equilibrium_upper_bound
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ s ∈ Set.Icc ((1 : ℝ) / 2) 1, f s ≤ C * (1 - s) := by
  have hdcont : ContinuousOn (fun t ↦ |deriv f t|) (Set.Icc ((1 : ℝ) / 2) 1) := by
    apply ContinuousOn.abs
    apply ((h.reaction_contDiffOn.mono Set.Ioi_subset_Ici_self).continuousOn_deriv_of_isOpen
      isOpen_Ioi (by simp)).mono
    intro t ht
    exact lt_of_lt_of_le (by norm_num) ht.1
  obtain ⟨a, ha, hmax⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr (by norm_num))
    hdcont
  refine ⟨|deriv f a| + 1, by positivity, ?_⟩
  intro s hs
  rcases lt_or_eq_of_le hs.2 with hslt | rfl
  · have hspos : 0 < s := lt_of_lt_of_le (by norm_num) hs.1
    have hcont : ContinuousOn f (Set.Icc s 1) :=
      h.reaction_contDiffOn.continuousOn.mono (fun t ht ↦ hspos.le.trans ht.1)
    have hdiff : DifferentiableOn ℝ f (Set.Ioo s 1) := by
      intro t ht
      exact ((h.reaction_contDiffOn.differentiableOn_one t
        (hspos.le.trans ht.1.le)).differentiableAt
        (Ici_mem_nhds (hspos.trans ht.1))).differentiableWithinAt
    obtain ⟨t, ht, heq⟩ := exists_deriv_eq_slope f hslt hcont hdiff
    have htb := hmax (show t ∈ Set.Icc ((1 : ℝ) / 2) 1 from
      ⟨hs.1.trans ht.1.le, ht.2.le⟩)
    change |deriv f t| ≤ |deriv f a| at htb
    have hdle : -deriv f t ≤ |deriv f a| + 1 := by
      linarith [neg_le_abs (deriv f t)]
    have hmul := (eq_div_iff (sub_pos.mpr hslt).ne').mp heq
    rw [hr.reaction_one, zero_sub] at hmul
    have := mul_le_mul_of_nonneg_right hdle (sub_pos.mpr hslt).le
    nlinarith
  · simp [hr.reaction_one]

/-- A quadratic upper bound valid throughout the upper half of the solution interval. -/
theorem RigidityHypotheses.potential_quadratic_upper_bound_near_one
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ s ∈ Set.Icc ((1 : ℝ) / 2) 1,
      normalizedPotential f s ≤ C * (1 - s) ^ 2 := by
  obtain ⟨C, hC, hb⟩ := hr.reaction_equilibrium_upper_bound h
  refine ⟨C / 2, by positivity, ?_⟩
  intro s hs
  rw [← integral_linear_equilibrium, normalizedPotential]
  have hcont : Continuous (fun t : ℝ ↦ C * (1 - t)) := by fun_prop
  apply intervalIntegral.integral_mono_on hs.2
    (h.reaction_intervalIntegrable (by linarith [hs.1])) (hcont.intervalIntegrable _ _)
  intro t ht
  exact hb t ⟨hs.1.trans ht.1, ht.2⟩

/-- A uniform quadratic upper bound holds on the entire normalized solution interval. -/
theorem RigidityHypotheses.potential_quadratic_upper_bound
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ s ∈ Set.Icc (0 : ℝ) 1,
      normalizedPotential f s ≤ C * (1 - s) ^ 2 := by
  obtain ⟨C, hC, hb⟩ := hr.potential_quadratic_upper_bound_near_one h
  obtain ⟨a, ha, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr zero_le_one) h.normalizedPotential_continuousOn
  let D := 4 * (normalizedPotential f a + 1)
  have hWa := hr.normalizedPotential_nonneg h ha
  have hD : 0 < D := by dsimp [D]; linarith
  refine ⟨max C D, hC.trans_le (le_max_left _ _), ?_⟩
  intro s hs
  by_cases hhalf : 1 / 2 ≤ s
  · exact (hb s ⟨hhalf, hs.2⟩).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))
  · have hsq : (1 : ℝ) / 4 ≤ (1 - s) ^ 2 := by
      have hslt := lt_of_not_ge hhalf
      nlinarith [sq_nonneg (s - 1 / 2)]
    have hsm : normalizedPotential f s ≤ normalizedPotential f a := hmax hs
    have hprod := mul_le_mul_of_nonneg_left hsq hD.le
    have hmid : normalizedPotential f s ≤ D * (1 - s) ^ 2 := by
      dsimp [D] at hprod ⊢
      nlinarith
    exact hmid.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _))

/-- The normalized potential is comparable to squared distance to equilibrium on the full range. -/
theorem RigidityHypotheses.potential_quadratic_comparison
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ s ∈ Set.Icc (0 : ℝ) 1,
      c * (1 - s) ^ 2 ≤ normalizedPotential f s ∧
      normalizedPotential f s ≤ C * (1 - s) ^ 2 := by
  obtain ⟨c, hc, hlo⟩ := hr.potential_quadratic_lower_bound h
  obtain ⟨C, hC, hhi⟩ := hr.potential_quadratic_upper_bound h
  exact ⟨c, C, hc, hC, fun s hs ↦ ⟨hlo s hs, hhi s hs⟩⟩

end SerrinEpigraph
