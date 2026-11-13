module

public import SerrinEpigraph.RadialNormalizedContinuation

/-!
# Completing a zero endpoint as a radial Dirichlet ball profile
-/

public section
noncomputable section
open Set
open scoped Topology

namespace SerrinEpigraph

/-- A completed left derivative supplies continuity on the closed radius interval. -/
theorem continuousOn_update_endpoint {F : ℝ → ℝ} {R b d : ℝ}
    (hF : ContinuousOn F (Ico 0 R))
    (hend : HasDerivWithinAt (Function.update F R b) d (Iic R) R) :
    ContinuousOn (Function.update F R b) (Icc 0 R) := by
  have hc : ContinuousOn (Function.update F R b) (Ico 0 R) := by
    apply hF.congr
    intro t ht
    exact Function.update_of_ne ht.2.ne b F
  intro t ht
  rcases lt_or_eq_of_le ht.2 with hlt | rfl
  · apply (hc t ⟨ht.1, hlt⟩).mono_of_mem_nhdsWithin
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hlt)] with s hs hsR
    exact ⟨hs.1, hsR⟩
  · exact hend.continuousWithinAt.mono (fun _ hs ↦ hs.2)

/-- A normalized central solution with zero endpoint limit gives a genuine Dirichlet ball profile. -/
theorem Hypotheses.exists_ballProfile_of_zero_limit
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (h : Hypotheses g u f κ) {Q P : ℝ → ℝ} {R : ℝ} (hR : 0 < R)
    (hQc : ContinuousOn Q (Ico 0 R)) (hPc : ContinuousOn P (Ico 0 R))
    (hQP : IsRadialSystemOn m f Q P (Ioo 0 R))
    (hval : ∀ t ∈ Ico (0 : ℝ) R, Q t ∈ Ioo (0 : ℝ) 1) (hP0 : P 0 = 0)
    (hzero : Filter.Tendsto Q (𝓝[<] R) (𝓝 0)) :
    ∃ v : RadialBallProfile f m R,
      EqOn v.value Q (Ico 0 R) ∧ EqOn v.slope P (Ico 0 R) := by
  obtain ⟨b, p, _, hQlim, _, hQend, hPend⟩ := h.exists_completed_radial_endpoint
    (a := 0) (δ := R / 2) le_rfl ⟨by positivity, by linarith⟩ hQP
    (fun t ht ↦ hval t ⟨ht.1.le, ht.2⟩)
  have hb : b = 0 := tendsto_nhds_unique hQlim hzero
  subst b
  let W := Function.update Q R 0
  let Z := Function.update P R p
  have hW : EqOn W Q (Ico 0 R) := fun t ht ↦ Function.update_of_ne ht.2.ne _ _
  have hZ : EqOn Z P (Ico 0 R) := fun t ht ↦ Function.update_of_ne ht.2.ne _ _
  refine ⟨{
    value := W
    slope := Z
    radius_pos := hR
    value_continuous := continuousOn_update_endpoint hQc hQend
    slope_continuous := continuousOn_update_endpoint hPc hPend
    value_range := ?_
    value_pos := ?_
    value_derivative := ?_
    slope_derivative := ?_
    slope_zero := ?_
    boundary_zero := by simp [W]
  }, hW, hZ⟩
  · intro t ht
    rcases lt_or_eq_of_le ht.2 with hlt | rfl
    · rw [hW ⟨ht.1, hlt⟩]
      exact ⟨(hval t ⟨ht.1, hlt⟩).1.le, (hval t ⟨ht.1, hlt⟩).2.le⟩
    · simp [W]
  · intro t ht
    rw [hW ⟨ht.1.le, ht.2⟩]
    exact (hval t ⟨ht.1.le, ht.2⟩).1
  · intro t ht
    rw [hZ ⟨ht.1.le, ht.2⟩]
    exact hasDerivAt_update_endpoint ht.2.ne (hQP t ht).1
  · intro t ht
    rw [hW ⟨ht.1.le, ht.2⟩, hZ ⟨ht.1.le, ht.2⟩]
    exact hasDerivAt_update_endpoint ht.2.ne (hQP t ht).2
  · rw [hZ ⟨le_rfl, hR⟩]
    exact hP0

/-- A regular positive central profile either completes to a ball solution or extends normalized. -/
theorem RigidityHypotheses.radial_ballProfile_or_extension
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {Q P : ℝ → ℝ} {R : ℝ} (hR : 0 < R)
    (hQc : ContinuousOn Q (Ico 0 R)) (hPc : ContinuousOn P (Ico 0 R))
    (hQP : IsRadialSystemOn m f Q P (Ioo 0 R))
    (hval : ∀ t ∈ Ico (0 : ℝ) R, Q t ∈ Ioo (0 : ℝ) 1) (hP0 : P 0 = 0) :
    (∃ v : RadialBallProfile f m R,
      EqOn v.value Q (Ico 0 R) ∧ EqOn v.slope P (Ico 0 R) ∧
      v.slope R < 0 ∧ v.slope R ^ 2 < 2 * normalizedPotential f 0) ∨
    (∃ ε : ℝ, 0 < ε ∧ ∃ W Z : ℝ → ℝ,
      IsRadialSystemOn m f W Z (Ioo 0 (R + ε)) ∧
      ContinuousOn W (Ico 0 (R + ε)) ∧ ContinuousOn Z (Ico 0 (R + ε)) ∧
      EqOn W Q (Ico 0 R) ∧ EqOn Z P (Ico 0 R) ∧
      (∀ t ∈ Ioo (0 : ℝ) (R + ε), W t ∈ Ioo (0 : ℝ) 1)) := by
  have hQ0 := (hval 0 ⟨le_rfl, hR⟩).2
  rcases hr.radial_zero_limit_or_normalized_continuation h hR hQc hPc hQP
    (fun t ht ↦ hval t ⟨ht.1.le, ht.2⟩) hQ0 hP0 with hz | hext
  · obtain ⟨v, hvQ, hvP⟩ := h.exists_ballProfile_of_zero_limit hR hQc hPc hQP hval hP0 hz
    refine Or.inl ⟨v, hvQ, hvP, v.boundary_slope_neg hr h, ?_⟩
    apply v.boundary_slope_sq_lt hr h
    rw [hvQ ⟨le_rfl, hR⟩]
    exact hQ0
  · exact Or.inr hext

end SerrinEpigraph
