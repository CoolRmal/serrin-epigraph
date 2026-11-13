module

public import SerrinEpigraph.TransitionLayerSelection

/-!
# Smooth cutoffs selected by their transition cost
-/

public section

open Set MeasureTheory Metric

namespace SerrinEpigraph

/-- A smooth cutoff can be chosen to transition in a low-cost radial layer, with a
dimension-independent gradient constant. -/
theorem exists_cutoff_with_small_transition_cost :
    ∃ C : ℝ, 0 < C ∧ ∀ (d N : ℕ) (r L : ℝ), 0 < N → 0 < r → 0 < L →
      ∀ F : Space d → ℝ, IntegrableOn F (closedBall 0 (r + N * L)) →
      (∀ x ∈ closedBall 0 (r + N * L), 0 ≤ F x) →
      ∃ η : Space d → ℝ, ContDiff ℝ 1 η ∧ HasCompactSupport η ∧
        tsupport η ⊆ ball 0 (r + N * L) ∧
        (∀ x ∈ ball 0 r, η x = 1) ∧
        (∀ x, η x ∈ Icc (0 : ℝ) 1) ∧
        (∀ x, ‖gradient η x‖ ≤ C / L) ∧
        (∫ x in {x | 0 < η x ∧ η x < 1}, F x) ≤
          (∫ x in closedBall 0 (r + N * L), F x) / N := by
  obtain ⟨C, hC, hcut⟩ := exists_fixedWidth_ball_cutoffs
  refine ⟨C, hC, fun d N r L hN hr hL F hF hpos ↦ ?_⟩
  obtain ⟨i, hi⟩ := exists_radial_layer_integral_le hN r hL.le hF hpos
  have hia : r ≤ r + (i.val : ℝ) * L :=
    le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hL.le)
  have hib : r + (i.val : ℝ) * L + L ≤ r + N * L := by
    have hh : (i.val : ℝ) + 1 ≤ N := by exact_mod_cast Nat.succ_le_of_lt i.isLt
    nlinarith [mul_le_mul_of_nonneg_right hh hL.le]
  obtain ⟨η, hη, hc, hs, hone, hval, hgrad⟩ :=
    hcut d (r + (i.val : ℝ) * L) L (hr.trans_le hia) hL
  refine ⟨η, hη, hc, hs.trans (ball_subset_ball hib),
    fun x hx ↦ hone x (ball_subset_ball hia hx), hval, hgrad, ?_⟩
  let S : Set (Space d) := {x | r + (i.val : ℝ) * L ≤ ‖x‖ ∧
    ‖x‖ < r + (i.val + 1 : ℝ) * L}
  have hS : MeasurableSet S :=
    (measurableSet_le measurable_const continuous_norm.measurable).inter
      (measurableSet_lt continuous_norm.measurable measurable_const)
  have hSK : S ⊆ closedBall 0 (r + N * L) := by
    intro x hx
    simp only [mem_closedBall, dist_zero_right]
    have he : r + (i.val + 1 : ℝ) * L = r + (i.val : ℝ) * L + L := by ring
    exact hx.2.le.trans (he ▸ hib)
  have hTS : {x | 0 < η x ∧ η x < 1} ⊆ S := by
    intro x hx
    have hh := cutoff_transition_subset_annulus hs hone hx
    refine ⟨hh.1, ?_⟩
    convert hh.2 using 1
    ring
  apply le_trans _ hi
  apply setIntegral_mono_set (hF.mono_set hSK)
  · exact ae_restrict_of_forall_mem hS (fun x hx ↦ hpos x (hSK hx))
  · exact Filter.Eventually.of_forall hTS

/-- In a fixed annulus, selection reduces the transition cost by the layer count,
while increasing the gradient bound linearly in that count. -/
theorem exists_cutoff_in_fixed_annulus_with_small_cost :
    ∃ C : ℝ, 0 < C ∧ ∀ (d N : ℕ) (r t : ℝ), 0 < N → 0 < r → 0 < t →
      ∀ F : Space d → ℝ, IntegrableOn F (closedBall 0 (r + t)) →
      (∀ x ∈ closedBall 0 (r + t), 0 ≤ F x) →
      ∃ η : Space d → ℝ, ContDiff ℝ 1 η ∧ HasCompactSupport η ∧
        tsupport η ⊆ ball 0 (r + t) ∧
        (∀ x ∈ ball 0 r, η x = 1) ∧
        (∀ x, η x ∈ Icc (0 : ℝ) 1) ∧
        (∀ x, ‖gradient η x‖ ≤ C * N / t) ∧
        (∫ x in {x | 0 < η x ∧ η x < 1}, F x) ≤
          (∫ x in closedBall 0 (r + t), F x) / N := by
  obtain ⟨C, hC, hcut⟩ := exists_cutoff_with_small_transition_cost
  refine ⟨C, hC, fun d N r t hN hr ht F hF hpos ↦ ?_⟩
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have he : (N : ℝ) * (t / N) = t := by field_simp
  have hg : C / (t / N) = C * N / t := by field_simp
  have hh := hcut d N r (t / N) hN hr (div_pos ht hNr) F
    (by simpa only [he] using hF) (by simpa only [he] using hpos)
  simpa only [he, hg] using hh

end SerrinEpigraph
