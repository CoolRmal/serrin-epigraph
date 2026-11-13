module

public import SerrinEpigraph.NormalizedPotential
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Uniform coercivity near the positive equilibrium
-/

public section

open scoped Topology

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ : ℝ}

/-- The negative equilibrium slope gives a uniform positive bound in a full neighborhood. -/
theorem RigidityHypotheses.exists_reaction_deriv_bound
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) :
    ∃ c δ : ℝ, 0 < c ∧ 0 < δ ∧ ∀ s : ℝ, |s - 1| < δ →
      0 < s ∧ c ≤ -deriv f s := by
  have hc : ContinuousAt (deriv f) 1 :=
    ((h.reaction_contDiffOn.mono Set.Ioi_subset_Ici_self).continuousOn_deriv_of_isOpen
      isOpen_Ioi (by simp)).continuousAt (Ioi_mem_nhds (by norm_num))
  have he : ∀ᶠ s in 𝓝 (1 : ℝ), deriv f s < deriv f 1 / 2 :=
    hc.eventually (gt_mem_nhds (by linarith [hr.reaction_deriv_one_neg]))
  obtain ⟨ε, hε, hb⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨-deriv f 1 / 2, min ε (1 / 2), by linarith [hr.reaction_deriv_one_neg],
    lt_min hε (by norm_num), ?_⟩
  intro s hs
  have hse : dist s 1 < ε := by
    rw [Real.dist_eq]
    exact lt_of_lt_of_le hs (min_le_left _ _)
  have hspos : 0 < s := by
    have := (abs_lt.mp (lt_of_lt_of_le hs (min_le_right ε ((1 : ℝ) / 2)))).1
    linarith
  exact ⟨hspos, by linarith [hb hse]⟩

/-- The normalized potential has a uniformly positive second derivative near one. -/
theorem RigidityHypotheses.exists_potential_second_deriv_bound
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) :
    ∃ c δ : ℝ, 0 < c ∧ 0 < δ ∧ ∀ s : ℝ, |s - 1| < δ →
      c ≤ deriv (deriv (normalizedPotential f)) s := by
  obtain ⟨c, δ, hc, hδ, hb⟩ := hr.exists_reaction_deriv_bound h
  refine ⟨c, δ, hc, hδ, fun s hs ↦ ?_⟩
  obtain ⟨hspos, hsbound⟩ := hb s hs
  rw [(h.normalizedPotential_deriv_hasDerivAt hspos).deriv]
  exact hsbound

/-- Below one, the reaction dominates the distance to equilibrium in a fixed neighborhood. -/
theorem RigidityHypotheses.exists_reaction_equilibrium_lower_bound
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) :
    ∃ c δ : ℝ, 0 < c ∧ 0 < δ ∧ ∀ s : ℝ, 1 - δ < s → s ≤ 1 →
      c * (1 - s) ≤ f s := by
  obtain ⟨c, δ, hc, hδ, hb⟩ := hr.exists_reaction_deriv_bound h
  refine ⟨c, δ, hc, hδ, ?_⟩
  intro s hs hsone
  rcases lt_or_eq_of_le hsone with hslt | rfl
  · have hsabs : |s - 1| < δ := by rw [abs_of_neg (sub_neg.mpr hslt)]; linarith
    have hspos := (hb s hsabs).1
    have hcont : ContinuousOn f (Set.Icc s 1) :=
      h.reaction_contDiffOn.continuousOn.mono (fun t ht ↦ hspos.le.trans ht.1)
    have hdiff : DifferentiableOn ℝ f (Set.Ioo s 1) := by
      intro t ht
      exact ((h.reaction_contDiffOn.differentiableOn_one t
        (hspos.le.trans ht.1.le)).differentiableAt
        (Ici_mem_nhds (hspos.trans ht.1))).differentiableWithinAt
    obtain ⟨t, ht, heq⟩ := exists_deriv_eq_slope f hslt hcont hdiff
    have htbound := (hb t (by rw [abs_of_neg (sub_neg.mpr ht.2)]; linarith [ht.1])).2
    have hmul := (eq_div_iff (sub_pos.mpr hslt).ne').mp heq
    rw [hr.reaction_one, zero_sub] at hmul
    have := mul_le_mul_of_nonneg_right htbound (sub_pos.mpr hslt).le
    nlinarith
  · simp [hr.reaction_one]

end SerrinEpigraph
