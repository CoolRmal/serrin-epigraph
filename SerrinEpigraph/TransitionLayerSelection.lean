module

public import SerrinEpigraph.FixedWidthCutoff
public import SerrinEpigraph.GluingTransition

/-!
# Selecting a transition layer with small integral cost
-/

public section

open Set MeasureTheory Metric

namespace SerrinEpigraph

/-- The strict transition region lies between a cutoff's inner and outer radii. -/
theorem cutoff_transition_subset_annulus {d : ℕ} {η : Space d → ℝ} {r L : ℝ}
    (hs : tsupport η ⊆ ball 0 (r + L))
    (hi : ∀ x ∈ ball 0 r, η x = 1) :
    {x | 0 < η x ∧ η x < 1} ⊆ {x | r ≤ ‖x‖ ∧ ‖x‖ < r + L} := by
  intro x hx
  refine ⟨?_, ?_⟩
  · by_contra hn
    have he := hi x (by simpa only [mem_ball, dist_zero_right] using lt_of_not_ge hn)
    linarith [hx.2]
  · have hm : x ∈ tsupport η := subset_closure (by exact ne_of_gt hx.1)
    simpa only [mem_ball, dist_zero_right] using hs hm

/-- Among disjoint measurable layers, one costs at most the ambient integral divided
by the number of layers. The integrand may combine energy and mismatch penalties. -/
theorem exists_layer_integral_le_average {d N : ℕ} (hN : 0 < N)
    {S : Fin N → Set (Space d)} {K : Set (Space d)} {F : Space d → ℝ}
    (hS : ∀ i, MeasurableSet (S i)) (hdis : Pairwise (fun i j ↦ Disjoint (S i) (S j)))
    (hSK : ∀ i, S i ⊆ K) (hK : MeasurableSet K) (hF : IntegrableOn F K)
    (hnonneg : ∀ x ∈ K, 0 ≤ F x) :
    ∃ i, (∫ x in S i, F x) ≤ (∫ x in K, F x) / N := by
  have hi : ∀ i, IntegrableOn F (S i) := fun i ↦ hF.mono_set (hSK i)
  have hsum : (∑ i, ∫ x in S i, F x) ≤ ∫ x in K, F x := by
    rw [← integral_iUnion_fintype hS hdis hi]
    apply setIntegral_mono_set hF
    · exact ae_restrict_of_forall_mem hK hnonneg
    · exact Filter.Eventually.of_forall (iUnion_subset hSK)
  by_contra hn
  push Not at hn
  have hlt : (∑ _i : Fin N, (∫ x in K, F x) / N) < ∑ i, ∫ x in S i, F x := by
    apply Finset.sum_lt_sum
    · intro i _
      exact (hn i).le
    · exact ⟨⟨0, hN⟩, Finset.mem_univ _, hn _⟩
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hlt
  have he : (N : ℝ) * ((∫ x in K, F x) / N) = ∫ x in K, F x := by field_simp
  rw [he] at hlt
  exact (not_lt_of_ge hsum) hlt

/-- Consecutive half-open radial layers are disjoint, including their boundary spheres. -/
theorem radial_layers_pairwise_disjoint {d N : ℕ} (r : ℝ) {L : ℝ} (hL : 0 ≤ L) :
    Pairwise (fun i j : Fin N ↦ Disjoint
      {x : Space d | r + (i.val : ℝ) * L ≤ ‖x‖ ∧ ‖x‖ < r + (i.val + 1 : ℝ) * L}
      {x : Space d | r + (j.val : ℝ) * L ≤ ‖x‖ ∧ ‖x‖ < r + (j.val + 1 : ℝ) * L}) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  rcases lt_or_gt_of_ne hij with hij | hij
  · have hh : (i.val : ℝ) + 1 ≤ j.val := by exact_mod_cast Nat.succ_le_of_lt hij
    nlinarith [mul_le_mul_of_nonneg_right hh hL, hxi.2, hxj.1]
  · have hh : (j.val : ℝ) + 1 ≤ i.val := by exact_mod_cast Nat.succ_le_of_lt hij
    nlinarith [mul_le_mul_of_nonneg_right hh hL, hxj.2, hxi.1]

/-- One of finitely many equal-width radial layers has at most the average ambient cost. -/
theorem exists_radial_layer_integral_le {d N : ℕ} (hN : 0 < N) (r : ℝ)
    {L : ℝ} (hL : 0 ≤ L) {F : Space d → ℝ}
    (hF : IntegrableOn F (closedBall 0 (r + N * L)))
    (hpos : ∀ x ∈ closedBall 0 (r + N * L), 0 ≤ F x) :
    ∃ i : Fin N,
      (∫ x in {x : Space d | r + (i.val : ℝ) * L ≤ ‖x‖ ∧
        ‖x‖ < r + (i.val + 1 : ℝ) * L}, F x) ≤
          (∫ x in closedBall 0 (r + N * L), F x) / N := by
  apply exists_layer_integral_le_average hN
    (fun i ↦ (measurableSet_le measurable_const continuous_norm.measurable).inter
      (measurableSet_lt continuous_norm.measurable measurable_const))
    (radial_layers_pairwise_disjoint r hL) _ measurableSet_closedBall hF hpos
  intro i x hx
  have hi : (i.val : ℝ) + 1 ≤ N := by exact_mod_cast Nat.succ_le_of_lt i.isLt
  simp only [mem_closedBall, dist_zero_right]
  exact hx.2.le.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right hi hL))

end SerrinEpigraph
