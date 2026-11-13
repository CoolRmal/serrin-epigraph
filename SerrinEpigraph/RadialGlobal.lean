module

public import SerrinEpigraph.RadialBranches

/-!
# The unbounded-radius alternative for radial extensions
-/

public section
noncomputable section
open Set

namespace SerrinEpigraph

/-- Unbounded branch radii cover every nonnegative radius. -/
theorem radialUnion_domain_eq_Ici {ι : Type*} {R : ι → ℝ}
    (hR : ¬BddAbove (range R)) : (⋃ i, Ico (0 : ℝ) (R i)) = Ici 0 := by
  ext t
  constructor
  · intro ht
    obtain ⟨i, hi⟩ := mem_iUnion.mp ht
    exact hi.1
  · intro ht
    obtain ⟨r, ⟨i, rfl⟩, hi⟩ := not_bddAbove_iff.mp hR t
    exact mem_iUnion.mpr ⟨i, ht, hi⟩

/-- Unbounded branch radii cover every positive radius. -/
theorem radialUnion_positive_domain_eq_Ioi {ι : Type*} {R : ι → ℝ}
    (hR : ¬BddAbove (range R)) : (⋃ i, Ioo (0 : ℝ) (R i)) = Ioi 0 := by
  ext t
  constructor
  · intro ht
    obtain ⟨i, hi⟩ := mem_iUnion.mp ht
    exact hi.1
  · intro ht
    obtain ⟨r, ⟨i, rfl⟩, hi⟩ := not_bddAbove_iff.mp hR t
    exact mem_iUnion.mpr ⟨i, ht, hi⟩

/-- If extension radii are unbounded, their union is a normalized solution on the whole half-line. -/
theorem RadialBranch.exists_global_of_unbounded_extensions
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ a : ℝ}
    (h : Hypotheses g u f κ) (seed : RadialBranch f m a)
    (hb : ¬BddAbove (range (fun v : RadialExtension seed ↦ v.branch.radius))) :
    ∃ Q P : ℝ → ℝ, ContinuousOn Q (Ici 0) ∧ ContinuousOn P (Ici 0) ∧
      Q 0 = a ∧ P 0 = 0 ∧ (∀ t ∈ Ici (0 : ℝ), Q t ∈ Ioo (0 : ℝ) 1) ∧
      IsRadialSystemOn m f Q P (Ioi 0) ∧
      EqOn Q seed.value (Ico 0 seed.radius) ∧ EqOn P seed.slope (Ico 0 seed.radius) := by
  let R := fun v : RadialExtension seed ↦ v.branch.radius
  let Q := fun v : RadialExtension seed ↦ v.branch.value
  let P := fun v : RadialExtension seed ↦ v.branch.slope
  have hQ := fun v w : RadialExtension seed ↦ (v.compatible h w).1
  have hP := fun v w : RadialExtension seed ↦ (v.compatible h w).2
  have hd := radialUnion_domain_eq_Ici hb
  have hdi := radialUnion_positive_domain_eq_Ioi hb
  refine ⟨radialUnion R Q, radialUnion R P, ?_, ?_,
    radialUnion_center hQ seed.selfExtension seed.radius_pos seed.value_zero,
    radialUnion_center hP seed.selfExtension seed.radius_pos seed.slope_zero, ?_, ?_,
    radialUnion_eqOn hQ seed.selfExtension, radialUnion_eqOn hP seed.selfExtension⟩
  · rw [← hd]
    exact radialUnion_continuousOn hQ (fun v ↦ v.branch.value_continuous)
  · rw [← hd]
    exact radialUnion_continuousOn hP (fun v ↦ v.branch.slope_continuous)
  · intro t ht
    apply radialUnion_mem_Ioo hQ (fun v ↦ v.branch.value_range)
    rwa [hd]
  · rw [← hdi]
    exact radialUnion_isRadialSystemOn hQ hP (fun v ↦ v.branch.system)

/-- Each normalized central value produces either a ball profile or a global positive radial system. -/
theorem RigidityHypotheses.radial_ball_or_global
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ a : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (ha : a ∈ Ioo (0 : ℝ) 1) :
    (∃ R : ℝ, ∃ v : RadialBallProfile f m R, v.value 0 = a) ∨
    (∃ Q P : ℝ → ℝ, ContinuousOn Q (Ici 0) ∧ ContinuousOn P (Ici 0) ∧
      Q 0 = a ∧ P 0 = 0 ∧ (∀ t ∈ Ici (0 : ℝ), Q t ∈ Ioo (0 : ℝ) 1) ∧
      IsRadialSystemOn m f Q P (Ioi 0)) := by
  obtain ⟨seed⟩ := h.nonempty_radialBranch ha
  by_cases hb : BddAbove (range (fun v : RadialExtension seed ↦ v.branch.radius))
  · obtain ⟨R, _, v, hQ, _⟩ := seed.exists_ballProfile_of_bdd_extensions hr h hb
    exact Or.inl ⟨R, v, (hQ ⟨le_rfl, seed.radius_pos⟩).trans seed.value_zero⟩
  · obtain ⟨Q, P, hQc, hPc, hQ0, hP0, hval, hsys, _, _⟩ :=
      seed.exists_global_of_unbounded_extensions h hb
    exact Or.inr ⟨Q, P, hQc, hPc, hQ0, hP0, hval, hsys⟩

end SerrinEpigraph
