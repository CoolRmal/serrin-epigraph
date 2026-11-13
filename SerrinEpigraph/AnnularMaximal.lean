module

public import SerrinEpigraph.AnnularLimits

/-!
# Attainment of the maximal annular radius
-/

public section
noncomputable section

open Set

namespace SerrinEpigraph

/-- Completing the compatible union gives an extension at the supremum of all extension radii. -/
theorem IncreasingRadialSegment.exists_supExtension
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ a b : ℝ}
    (seed : IncreasingRadialSegment f m a b) (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ)
    (hb : BddAbove (range (fun v : AnnularExtension seed ↦ v.radius))) :
    ∃ v : AnnularExtension seed,
      v.radius = sSup (range (fun w : AnnularExtension seed ↦ w.radius)) := by
  let R := fun v : AnnularExtension seed ↦ v.radius
  let Q := annularUnion a R (fun v ↦ v.segment.value)
  let P := annularUnion a R (fun v ↦ v.segment.slope)
  let S := sSup (range R)
  have hbS : b ≤ S := le_csSup hb (mem_range_self seed.selfExtension)
  have haS : a < S := seed.radii_lt.trans_le hbS
  have hQ := fun v w : AnnularExtension seed ↦ (v.compatible h w).1
  have hP := fun v w : AnnularExtension seed ↦ (v.compatible h w).2
  have hdom := annularUnion_domain_eq_Ico (a := a) hb
  have hdomi := annularUnion_domain_eq_Ioo (a := a) hb
  have hQc : ContinuousOn Q (Ico a S) := by
    rw [← hdom]
    exact annularUnion_continuousOn hQ
      (fun v ↦ v.segment.value_continuous.mono Ico_subset_Icc_self)
  have hPc : ContinuousOn P (Ico a S) := by
    rw [← hdom]
    exact annularUnion_continuousOn hP
      (fun v ↦ v.segment.slope_continuous.mono Ico_subset_Icc_self)
  have hsys : IsRadialSystemOn m f Q P (Ioo a S) := by
    rw [← hdomi]
    exact annularUnion_isRadialSystemOn hQ hP
      (fun v t ht ↦ ⟨v.segment.value_derivative t ht, v.segment.slope_derivative t ht⟩)
  have hbounds : ∀ t ∈ Ico a S, Q t ∈ Icc (0 : ℝ) 1 ∧ 0 ≤ P t := by
    intro t ht
    rw [← hdom] at ht
    obtain ⟨v, hv⟩ := mem_iUnion.mp ht
    rw [show Q t = v.segment.value t from annularUnion_eqOn hQ v hv,
      show P t = v.segment.slope t from annularUnion_eqOn hP v hv]
    exact ⟨v.segment.value_range t ⟨hv.1, hv.2.le⟩,
      v.segment.slope_nonneg t ⟨hv.1, hv.2.le⟩⟩
  have hpos : ∀ t ∈ Ioo a S, 0 < Q t := by
    intro t ht
    rw [← hdomi] at ht
    obtain ⟨v, hv⟩ := mem_iUnion.mp ht
    rw [show Q t = v.segment.value t from annularUnion_eqOn hQ v ⟨hv.1.le, hv.2⟩]
    exact v.segment.value_pos t hv
  have hQseed : EqOn Q seed.value (Ico a b) := annularUnion_eqOn hQ seed.selfExtension
  have hPseed : EqOn P seed.slope (Ico a b) := annularUnion_eqOn hP seed.selfExtension
  have hzero : Q a = 0 := (hQseed ⟨le_rfl, seed.radii_lt⟩).trans seed.inner_zero
  obtain ⟨q, p, hqr, hp0, hqlim, hplim⟩ := seed.annularUnion_endpoint_limits hr h hb
  obtain ⟨v, hvQ, hvP⟩ := increasingRadialSegment_of_endpoint_limits seed.inner_pos haS
    hQc hPc hsys hbounds hpos hzero hqlim hplim hqr hp0
  have hsub : Icc a b ⊆ Icc a S := fun _ ht ↦ ⟨ht.1, ht.2.trans hbS⟩
  have hval : EqOn v.value seed.value (Ioo a b) := fun t ht ↦
    (hvQ ⟨ht.1.le, ht.2.trans_le hbS⟩).trans (hQseed ⟨ht.1.le, ht.2⟩)
  have hslope : EqOn v.slope seed.slope (Ioo a b) := fun t ht ↦
    (hvP ⟨ht.1.le, ht.2.trans_le hbS⟩).trans (hPseed ⟨ht.1.le, ht.2⟩)
  have hcl : closure (Ioo a b) = Icc a b := closure_Ioo seed.radii_lt.ne
  refine ⟨{
    radius := S
    segment := v
    radius_ge := hbS
    value_eq := hval.of_subset_closure (v.value_continuous.mono hsub)
      seed.value_continuous Ioo_subset_Icc_self (by rw [hcl])
    slope_eq := hslope.of_subset_closure (v.slope_continuous.mono hsub)
      seed.slope_continuous Ioo_subset_Icc_self (by rw [hcl]) }, rfl⟩

/-- A positive initial energy margin forces an increasing radial segment to reach one. -/
theorem IncreasingRadialSegment.exists_extension_reaching_one
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ a b δ : ℝ}
    (seed : IncreasingRadialSegment f m a b) (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) (hδ : 0 < δ)
    (hmargin : δ ^ 2 ≤ seed.slope a ^ 2 - 2 * normalizedPotential f 0 -
      2 * ((m : ℝ) / a * seed.slope a)) :
    ∃ v : AnnularExtension seed, v.segment.value v.radius = 1 := by
  obtain ⟨v, hv⟩ := seed.exists_supExtension hr h
    (seed.extension_radii_bddAbove hr h hδ hmargin)
  exact ⟨v, v.value_eq_one_of_radius_eq_sup hr h hδ hmargin hv⟩

/-- For any initial slope above the potential energy threshold, every sufficiently large
inner radius admits an increasing radial solution from zero to one with that initial slope. -/
theorem RigidityHypotheses.exists_increasing_annular_profile
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ p : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (hp : 0 < p)
    (henergy : 2 * normalizedPotential f 0 < p ^ 2) :
    ∃ A : ℝ, 0 < A ∧ ∀ a : ℝ, A ≤ a →
      ∃ b : ℝ, ∃ v : IncreasingRadialSegment f m a b,
        v.slope a = p ∧ v.value b = 1 ∧ ∀ r ∈ Icc a b, 0 < v.slope r := by
  obtain ⟨A, δ, hA, hδ, hmargin⟩ := exists_annular_energy_margin m hp henergy
  refine ⟨A, hA, ?_⟩
  intro a ha
  obtain ⟨b, seed, hseed, _⟩ := exists_increasingRadialSegment h.reaction_contDiffOn m
    (hA.trans_le ha) hp
  have hm : δ ^ 2 ≤ seed.slope a ^ 2 - 2 * normalizedPotential f 0 -
      2 * ((m : ℝ) / a * seed.slope a) := by rw [hseed]; exact hmargin a ha
  obtain ⟨v, hv⟩ := seed.exists_extension_reaching_one hr h hδ hm
  have hpa : v.segment.slope a = p :=
    (v.slope_eq ⟨le_rfl, seed.radii_lt.le⟩).trans hseed
  refine ⟨v.radius, v.segment, hpa, hv, ?_⟩
  intro r hri
  have he := v.segment.slope_sq_lower_bound hr h hri
  rw [hpa] at he
  have hs := (hmargin a ha).trans he
  have hn := v.segment.slope_nonneg r hri
  nlinarith [sq_pos_of_pos hδ]

end SerrinEpigraph
