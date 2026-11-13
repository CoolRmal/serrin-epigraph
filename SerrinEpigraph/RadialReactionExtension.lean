module

public import SerrinEpigraph.RadialFixedPoint
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Local radial solutions for reactions smooth on a value interval
-/

public section
noncomputable section
open Set
open scoped NNReal Topology

namespace SerrinEpigraph

/-- Constant endpoint extension of a reaction on a closed value interval. -/
@[expose] def intervalReaction (f : ℝ → ℝ) {b c : ℝ} (hbc : b ≤ c) (s : ℝ) : ℝ :=
  f (projIcc b c hbc s)

/-- The extended reaction agrees with the original on its value interval. -/
theorem intervalReaction_eq {f : ℝ → ℝ} {b c s : ℝ} (hbc : b ≤ c)
    (hs : s ∈ Icc b c) : intervalReaction f hbc s = f s := by
  simp only [intervalReaction, projIcc_of_mem hbc hs]

/-- Endpoint extension preserves a Lipschitz bound on a closed interval. -/
theorem intervalReaction_lipschitz {f : ℝ → ℝ} {b c : ℝ} (hbc : b ≤ c)
    {L : ℝ≥0} (hf : LipschitzOnWith L f (Icc b c)) :
    LipschitzWith L (intervalReaction f hbc) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have he := hf.dist_le_mul _ (projIcc b c hbc x).property
    _ (projIcc b c hbc y).property
  have hp := (LipschitzWith.projIcc hbc).dist_le_mul x y
  simp only [NNReal.coe_one, one_mul, Subtype.dist_eq] at hp
  exact he.trans (mul_le_mul_of_nonneg_left hp L.coe_nonneg)

/-- A continuously differentiable reaction on a compact interval has a Lipschitz extension. -/
theorem intervalReaction_exists_lipschitz {f : ℝ → ℝ} {b c : ℝ} (hbc : b ≤ c)
    (hf : ContDiffOn ℝ 1 f (Icc b c)) :
    ∃ L : ℝ≥0, LipschitzWith L (intervalReaction f hbc) := by
  obtain ⟨L, hL⟩ := hf.exists_lipschitzOnWith one_ne_zero (convex_Icc b c) isCompact_Icc
  exact ⟨L, intervalReaction_lipschitz hbc hL⟩

/-- There is always a positive radius on which the Picard factor is less than one. -/
theorem exists_radial_contraction_radius (m : ℕ) (L : ℝ≥0) :
    ∃ R : ℝ, 0 < R ∧ R ^ 2 / 2 * ((L : ℝ) / (m + 1 : ℝ)) < 1 := by
  have hc : Continuous (fun R : ℝ ↦ R ^ 2 / 2 * ((L : ℝ) / (m + 1 : ℝ))) := by
    fun_prop
  have hn : {R : ℝ | R ^ 2 / 2 * ((L : ℝ) / (m + 1 : ℝ)) < 1} ∈ 𝓝 (0 : ℝ) :=
    hc.continuousAt.preimage_mem_nhds (Iio_mem_nhds (by norm_num))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨ε / 2, by positivity, hball ?_⟩
  rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos (by positivity)]
  linarith

/-- An interior initial value admits a local averaged radial solution for the original reaction. -/
theorem exists_radial_solution_in_value_interval (m : ℕ) {f : ℝ → ℝ} {b a c : ℝ}
    (ha : a ∈ Ioo b c) (hf : ContDiffOn ℝ 1 f (Icc b c)) :
    ∃ R : ℝ, 0 < R ∧ ∃ Q : ℝ → ℝ,
      Continuous Q ∧ Q 0 = a ∧ HasDerivAt Q 0 0 ∧
      (∀ r ∈ Icc (0 : ℝ) R, Q r ∈ Ioo b c) ∧
      ∀ r ∈ Icc (0 : ℝ) R, HasDerivAt Q (-r * radialAverage m (f ∘ Q) r) r := by
  have hbc : b ≤ c := (ha.1.trans ha.2).le
  obtain ⟨L, hL⟩ := intervalReaction_exists_lipschitz hbc hf
  obtain ⟨T, hT, hsmall⟩ := exists_radial_contraction_radius m L
  obtain ⟨Q, hQ, hQ0, hd0, hd⟩ := exists_radial_averaged_solution m hT.le hL a hsmall
  have hn : Q ⁻¹' Ioo b c ∈ 𝓝 (0 : ℝ) :=
    hQ.continuousAt.preimage_mem_nhds (Ioo_mem_nhds (by simpa [hQ0] using ha.1)
      (by simpa [hQ0] using ha.2))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hn
  let R := min T (ε / 2)
  have hR : 0 < R := lt_min hT (by positivity)
  have hrange : ∀ r ∈ Icc (0 : ℝ) R, Q r ∈ Ioo b c := by
    intro r hr
    apply hball
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_nonneg hr.1]
    have := hr.2.trans (min_le_right T (ε / 2))
    linarith
  refine ⟨R, hR, Q, hQ, hQ0, hd0, hrange, ?_⟩
  intro r hr
  have havg : radialAverage m (intervalReaction f hbc ∘ Q) r =
      radialAverage m (f ∘ Q) r := by
    apply intervalIntegral.integral_congr
    intro s hs
    have hs' : s ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using hs
    have ht : r * s ∈ Icc (0 : ℝ) R :=
      ⟨mul_nonneg hr.1 hs'.1, (mul_le_of_le_one_right hr.1 hs'.2).trans hr.2⟩
    have hval := hrange (r * s) ht
    simp only [Function.comp_apply, intervalReaction_eq hbc ⟨hval.1.le, hval.2.le⟩]
  have he := hd r ⟨hr.1, hr.2.trans (min_le_left T (ε / 2))⟩
  rw [havg] at he
  exact he

/-- The project's reaction hypotheses give local profiles with values strictly between zero and one. -/
theorem Hypotheses.exists_local_radial_averaged_solution
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (h : Hypotheses g u f κ) {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    ∃ R : ℝ, 0 < R ∧ ∃ Q : ℝ → ℝ,
      Continuous Q ∧ Q 0 = a ∧ HasDerivAt Q 0 0 ∧
      (∀ r ∈ Icc (0 : ℝ) R, Q r ∈ Ioo (0 : ℝ) 1) ∧
      ∀ r ∈ Icc (0 : ℝ) R, HasDerivAt Q (-r * radialAverage m (f ∘ Q) r) r := by
  exact exists_radial_solution_in_value_interval m ha
    (h.reaction_contDiffOn.mono (fun _ hx ↦ hx.1))

end SerrinEpigraph
